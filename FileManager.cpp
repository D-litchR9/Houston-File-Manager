#include <algorithm>
#include <atomic>
#include <chrono>
#include <climits>
#include <cstring>
#include <cstdlib>
#include <deque>
#include <dirent.h>
#include <fcntl.h>
#include <functional>
#include <grp.h>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <poll.h>
#include <pthread.h>
#include <pwd.h>
#include <signal.h>
#include <sstream>
#include <string>
#include <sys/inotify.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <thread>
#include <unistd.h>
#include <vector>

#include <curses.h>

// ==============================
//  Definiciones y globales
// ==============================

// Estructura para cada entrada del directorio
struct FileEntry {
    std::string name;          // nombre del archivo/directorio
    ino_t inode;               // número de i-nodo
    off_t size;                // tamaño en bytes
    mode_t mode;               // permisos y tipo
    time_t mtime;              // última modificación
    std::string perms;         // cadena de permisos estilo "ls -l"
    std::string type_str;      // categoría inferida
    bool is_dir;               // si es directorio
    bool is_exec;              // si es ejecutable
    bool is_symlink;           // si es enlace simbólico
};

// Modos del panel derecho
enum class RightView { TEXT, HEX, PROPERTIES, TREE };

// Variables globales de ncurses
WINDOW *left_win = nullptr;
WINDOW *right_win = nullptr;
WINDOW *bottom_win = nullptr;
int left_rows, left_cols, right_rows, right_cols;

// Variables del gestor
std::string current_path;                // ruta actual del panel izquierdo
std::vector<FileEntry> files;            // listado actual
int selected_idx = 0;                    // índice seleccionado
int left_scroll = 0;                     // desplazamiento vertical del panel izq.

// Opciones de visualización
bool show_hidden = false;
bool show_inode = false;

// Ordenamiento
int sort_column = 0;   // 0:nombre, 1:tamaño, 2:fecha, 3:tipo
bool sort_asc = true;

// Panel derecho
RightView right_view_mode = RightView::TEXT;
std::string exec_output;                 // salida capturada de ejecución
int right_scroll_offset = 0;             // desplazamiento vertical del panel der.
bool right_focus = false;                // foco en panel derecho (para scroll)

// Reloj
std::mutex clock_mtx;
std::string clock_str = "0000-00-00 00:00:00";
std::atomic<bool> quit_flag(false);

// Hilo de refresco (inotify -> pipe)
std::atomic<bool> refresh_active(false);
std::thread refresh_thread_obj;
int refresh_pipe[2] = {-1, -1};          // pipe para notificar cambios
std::string watched_path;

// Mutex para actualización de path en el hilo de refresco
std::mutex path_mtx;

// Flag de redimension
volatile sig_atomic_t resize_flag = 0;

// ==============================
//  Funciones auxiliares
// ==============================

// Manejador de SIGWINCH
void handle_winch(int sig) {
    resize_flag = 1;
}

// Convertir tamaño a notación de ingeniería
std::string format_size(off_t bytes) {
    const char* units[] = {"B", "KiB", "MiB", "GiB", "TiB"};
    int unit_idx = 0;
    double size = static_cast<double>(bytes);
    while (size >= 1024.0 && unit_idx < 4) {
        size /= 1024.0;
        ++unit_idx;
    }
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(1) << size << " " << units[unit_idx];
    return oss.str();
}

// Obtener cadena de permisos tipo "ls -l"
std::string get_perms_string(mode_t mode) {
    std::string perms(10, '-');
    // tipo
    if (S_ISDIR(mode)) perms[0] = 'd';
    else if (S_ISLNK(mode)) perms[0] = 'l';
    else if (S_ISCHR(mode)) perms[0] = 'c';
    else if (S_ISBLK(mode)) perms[0] = 'b';
    else if (S_ISFIFO(mode)) perms[0] = 'p';
    else if (S_ISSOCK(mode)) perms[0] = 's';
    // permisos
    perms[1] = (mode & S_IRUSR) ? 'r' : '-';
    perms[2] = (mode & S_IWUSR) ? 'w' : '-';
    perms[3] = (mode & S_IXUSR) ? 'x' : '-';
    perms[4] = (mode & S_IRGRP) ? 'r' : '-';
    perms[5] = (mode & S_IWGRP) ? 'w' : '-';
    perms[6] = (mode & S_IXGRP) ? 'x' : '-';
    perms[7] = (mode & S_IROTH) ? 'r' : '-';
    perms[8] = (mode & S_IWOTH) ? 'w' : '-';
    perms[9] = (mode & S_IXOTH) ? 'x' : '-';
    // sticky / setuid / setgid se omiten por simplicidad
    return perms;
}

// Inferir tipo de archivo por extensión y magic number básico
std::string get_file_type(const std::string& name, mode_t mode, bool is_reg) {
    if (S_ISDIR(mode)) return "directorio";
    if (!is_reg) return "especial";
    // extensión
    size_t dot = name.rfind('.');
    std::string ext;
    if (dot != std::string::npos) ext = name.substr(dot);
    if (ext == ".pdf") return "PDF";
    if (ext == ".png" || ext == ".gif" || ext == ".jpg" || ext == ".jpeg" || ext == ".bmp")
        return "imagen";
    if (ext == ".sh" || ext == ".py" || ext == ".pl" || ext == ".rb") return "script";
    if (mode & (S_IXUSR | S_IXGRP | S_IXOTH)) return "ejecutable";
    if (ext == ".txt" || ext == ".md" || ext == ".cpp" || ext == ".h" || ext == ".c") return "texto";
    // magic: leer primeros bytes
    FILE* fp = fopen(name.c_str(), "rb");
    if (fp) {
        unsigned char buf[4];
        size_t n = fread(buf, 1, 4, fp);
        fclose(fp);
        if (n >= 4 && buf[0]==0x7f && buf[1]=='E' && buf[2]=='L' && buf[3]=='F') return "ELF";
        if (n >= 2 && buf[0]=='P' && buf[1]=='K') return "ZIP/archivo";
    }
    return "binario";
}

// ==============================
//  Lectura de directorio
// ==============================
std::vector<FileEntry> read_directory(const std::string& path) {
    std::vector<FileEntry> result;
    DIR* dir = opendir(path.c_str());
    if (!dir) return result;

    struct dirent* entry;
    while ((entry = readdir(dir)) != nullptr) {
        // omitir "." y ".." temporalmente; se añadirán después
        std::string name = entry->d_name;
        if (name == "." || name == "..") continue;
        if (!show_hidden && name[0] == '.') continue;

        std::string full = path + "/" + name;
        struct stat st;
        if (lstat(full.c_str(), &st) == -1) continue;

        FileEntry fe;
        fe.name = name;
        fe.inode = st.st_ino;
        fe.size = st.st_size;
        fe.mode = st.st_mode;
        fe.mtime = st.st_mtime;
        fe.perms = get_perms_string(st.st_mode);
        fe.is_dir = S_ISDIR(st.st_mode);
        fe.is_exec = (st.st_mode & (S_IXUSR|S_IXGRP|S_IXOTH)) != 0;
        fe.is_symlink = S_ISLNK(st.st_mode);
        fe.type_str = get_file_type(name, st.st_mode, S_ISREG(st.st_mode));
        result.push_back(fe);
    }
    closedir(dir);

    // Añadir entrada ".." al principio si no estamos en la raíz
    if (path != "/") {
        FileEntry parent;
        parent.name = "..";
        struct stat st;
        if (lstat((path + "/..").c_str(), &st) == 0) {
            parent.inode = st.st_ino;
            parent.size = st.st_size;
            parent.mode = st.st_mode;
            parent.mtime = st.st_mtime;
            parent.perms = get_perms_string(st.st_mode);
            parent.is_dir = true;
            parent.is_exec = false;
            parent.is_symlink = false;
            parent.type_str = "directorio";
        }
        result.insert(result.begin(), parent);
    }

    return result;
}

// Ordenar listado según columna y dirección
void sort_files(std::vector<FileEntry>& vec) {
    // mantener ".." siempre arriba
    auto it_dotdot = std::find_if(vec.begin(), vec.end(),
                                  [](const FileEntry& f){ return f.name == ".."; });
    FileEntry dotdot;
    bool has_dotdot = false;
    if (it_dotdot != vec.end()) {
        dotdot = *it_dotdot;
        vec.erase(it_dotdot);
        has_dotdot = true;
    }

    std::sort(vec.begin(), vec.end(),
        [&](const FileEntry& a, const FileEntry& b) {
            // directorios primero
            if (a.is_dir != b.is_dir) return a.is_dir > b.is_dir; // dirs primero
            int cmp = 0;
            switch (sort_column) {
                case 0: // nombre
                    cmp = a.name.compare(b.name);
                    break;
                case 1: // tamaño
                    cmp = (a.size < b.size) ? -1 : (a.size > b.size ? 1 : 0);
                    break;
                case 2: // fecha modificación
                    cmp = (a.mtime < b.mtime) ? -1 : (a.mtime > b.mtime ? 1 : 0);
                    break;
                case 3: // tipo
                    cmp = a.type_str.compare(b.type_str);
                    break;
            }
            if (cmp == 0) cmp = a.name.compare(b.name); // desempate
            return sort_asc ? cmp < 0 : cmp > 0;
        });

    if (has_dotdot) vec.insert(vec.begin(), dotdot);
}

// ==============================
//  Funciones de dibujo
// ==============================

void draw_left_panel() {
    werase(left_win);
    box(left_win, 0, 0);
    // Cabecera
    int header_y = 0;
    wattron(left_win, A_BOLD);
    std::string header;
    if (show_inode) header += " Inode    ";
    header += " Nombre                    Tamaño      Permisos        Fecha mod.    Tipo";
    mvwaddstr(left_win, header_y, 2, header.c_str());
    wattroff(left_win, A_BOLD);
    // Línea separadora
    mvwaddch(left_win, header_y + 1, 1, ACS_HLINE);
    for (int x = 2; x < left_cols - 1; ++x)
        mvwaddch(left_win, header_y + 1, x, ACS_HLINE);

    int y = header_y + 2;
    int max_lines = left_rows - (header_y + 2) - 1; // una línea libre abajo para scroll?
    // Ajustar scroll
    if (selected_idx < left_scroll) left_scroll = selected_idx;
    if (selected_idx >= left_scroll + max_lines) left_scroll = selected_idx - max_lines + 1;
    if (left_scroll < 0) left_scroll = 0;

    for (int i = left_scroll; i < static_cast<int>(files.size()) && y < left_rows - 1; ++i) {
        const auto& fe = files[i];
        if (i == selected_idx) wattron(left_win, A_REVERSE);
        // Color según tipo
        int color_pair = 1;
        if (fe.is_dir) color_pair = 2;
        else if (fe.is_exec) color_pair = 3;
        else if (fe.is_symlink) color_pair = 4;
        wattron(left_win, COLOR_PAIR(color_pair));
        std::ostringstream line;
        if (show_inode) {
            line << std::setw(8) << fe.inode << " ";
        }
        line << std::left << std::setw(24) << fe.name.substr(0,23) << " "
             << std::right << std::setw(10) << format_size(fe.size) << " "
             << std::left << std::setw(13) << fe.perms << " "
             << std::setw(14);
        char timebuf[20];
        strftime(timebuf, sizeof(timebuf), "%b %d %H:%M", localtime(&fe.mtime));
        line << timebuf << " "
             << fe.type_str;
        mvwaddnstr(left_win, y, 2, line.str().c_str(), left_cols - 4);
        wattroff(left_win, COLOR_PAIR(color_pair));
        if (i == selected_idx) wattroff(left_win, A_REVERSE);
        ++y;
    }
    wrefresh(left_win);
}

void draw_right_panel(const std::string& selected_path) {
    werase(right_win);
    box(right_win, 0, 0);
    int y = 1;

    switch (right_view_mode) {
        case RightView::TEXT: {
            mvwaddstr(right_win, y++, 2, "Vista de texto");

            // Salida de ejecución capturada (flag especial)
            if (!exec_output.empty() && selected_path.find("/tmp/exec_output") != std::string::npos) {
                std::istringstream iss(exec_output);
                std::string line;
                int line_no = 0;
                int max_lines = right_rows - y - 1;
                while (std::getline(iss, line) && y < right_rows - 1) {
                    if (line_no >= right_scroll_offset)
                        mvwaddnstr(right_win, y++, 2, line.c_str(), right_cols - 4);
                    ++line_no;
                }
                exec_output.clear();
                break;
            }

            // Obtener información siguiendo enlaces simbólicos (stat, no lstat)
            struct stat st;
            if (stat(selected_path.c_str(), &st) == -1) {
                mvwaddstr(right_win, y++, 2, "No se puede acceder al archivo.");
                break;
            }

            // Si es directorio, no se previsualiza como texto
            if (S_ISDIR(st.st_mode)) {
                mvwaddstr(right_win, y++, 2, "Es un directorio.");
                break;
            }

            // Si no es archivo regular, podría ser enlace roto, dispositivo, etc.
            if (!S_ISREG(st.st_mode)) {
                struct stat lst;
                if (lstat(selected_path.c_str(), &lst) == 0 && S_ISLNK(lst.st_mode))
                    mvwaddstr(right_win, y++, 2, "Enlace simbólico (roto o especial).");
                else
                    mvwaddstr(right_win, y++, 2, "Tipo de archivo no regular.");
                break;
            }

            // Intentar abrir y leer los primeros 4096 bytes
            FILE* fp = fopen(selected_path.c_str(), "r");
            if (!fp) {
                mvwaddstr(right_win, y++, 2, "No se puede abrir el archivo.");
                break;
            }

            char buf[4096];
            size_t n = fread(buf, 1, sizeof(buf), fp);
            fclose(fp);

            if (n == 0) {
                mvwaddstr(right_win, y++, 2, "(archivo vacío)");
                break;
            }

            // Heurística de texto mejorada: permite tab, nueva línea, retorno de carro, avance de página.
            bool is_text = true;
            for (size_t i = 0; i < n; ++i) {
                unsigned char c = buf[i];
                if (c == 0) { is_text = false; break; }   // byte nulo → binario
                if (c < 32 && c != '\t' && c != '\n' && c != '\r' && c != 12) {
                    is_text = false;                     // otro carácter de control
                    break;
                }
            }

            if (!is_text) {
                mvwaddstr(right_win, y++, 2, "Archivo binario, sin vista previa.");
                break;
            }

            // Mostrar contenido con scroll
            std::string content(buf, n);
            std::istringstream iss(content);
            std::string line;
            int line_num = 0;
            int max_lines = right_rows - y - 1;
            while (std::getline(iss, line) && y < right_rows - 1) {
                if (line_num >= right_scroll_offset) {
                    mvwaddnstr(right_win, y++, 2, line.c_str(), right_cols - 4);
                }
                ++line_num;
            }
            // Si hay más contenido del que cabe, indicar
            if (line_num > right_scroll_offset + max_lines)
                mvwaddstr(right_win, y, 2, "[...]");
            break;
        }

        case RightView::HEX: {
            mvwaddstr(right_win, y++, 2, "Vista hexadecimal");
            struct stat st;
            if (stat(selected_path.c_str(), &st) == 0 && S_ISREG(st.st_mode)) {
                FILE* fp = fopen(selected_path.c_str(), "rb");
                if (fp) {
                    unsigned char buf[16];
                    size_t offset = 0;
                    size_t skip_lines = right_scroll_offset;
                    size_t skip_bytes = skip_lines * 16;
                    if (skip_bytes > 0) fseek(fp, skip_bytes, SEEK_SET);
                    int max_lines = right_rows - y - 1;
                    while (y < right_rows - 1 && max_lines-- > 0) {
                        size_t n = fread(buf, 1, 16, fp);
                        if (n == 0) break;
                        std::ostringstream hex_line, ascii_line;
                        hex_line << std::hex << std::setfill('0') << std::setw(8) << offset << "  ";
                        for (size_t i = 0; i < 16; ++i) {
                            if (i < n) hex_line << std::setw(2) << (int)buf[i] << " ";
                            else hex_line << "   ";
                        }
                        hex_line << " |";
                        for (size_t i = 0; i < n; ++i)
                            ascii_line << (isprint(buf[i]) ? (char)buf[i] : '.');
                        hex_line << ascii_line.str();
                        mvwaddnstr(right_win, y++, 2, hex_line.str().c_str(), right_cols - 4);
                        offset += n;
                    }
                    fclose(fp);
                }
            } else {
                mvwaddstr(right_win, y++, 2, "No es archivo regular o no accesible.");
            }
            break;
        }

        case RightView::PROPERTIES: {
            mvwaddstr(right_win, y++, 2, "Propiedades");
            struct stat st;
            if (lstat(selected_path.c_str(), &st) == 0) {
                mvwprintw(right_win, y++, 2, "Nombre: %s", selected_path.c_str());
                mvwprintw(right_win, y++, 2, "Tamaño: %ld bytes", st.st_size);
                mvwprintw(right_win, y++, 2, "Permisos (octal): %o", st.st_mode & 0777);
                mvwprintw(right_win, y++, 2, "Permisos (simb): %s", get_perms_string(st.st_mode).c_str());
                struct passwd *pw = getpwuid(st.st_uid);
                mvwprintw(right_win, y++, 2, "Propietario: %s (%d)", pw ? pw->pw_name : "?", st.st_uid);
                struct group *gr = getgrgid(st.st_gid);
                mvwprintw(right_win, y++, 2, "Grupo: %s (%d)", gr ? gr->gr_name : "?", st.st_gid);
                char timebuf[30];
                strftime(timebuf, sizeof(timebuf), "%Y-%m-%d %H:%M:%S", localtime(&st.st_atime));
                mvwprintw(right_win, y++, 2, "Acceso: %s", timebuf);
                strftime(timebuf, sizeof(timebuf), "%Y-%m-%d %H:%M:%S", localtime(&st.st_mtime));
                mvwprintw(right_win, y++, 2, "Modificación: %s", timebuf);
                strftime(timebuf, sizeof(timebuf), "%Y-%m-%d %H:%M:%S", localtime(&st.st_ctime));
                mvwprintw(right_win, y++, 2, "Cambio: %s", timebuf);
                mvwprintw(right_win, y++, 2, "Enlaces duros: %lu", st.st_nlink);
                mvwprintw(right_win, y++, 2, "i-nodo: %lu", st.st_ino);
            } else {
                mvwaddstr(right_win, y++, 2, "No se pudo obtener información.");
            }
            break;
        }

        case RightView::TREE: {
            mvwaddstr(right_win, y++, 2, "Árbol de directorios");
            struct stat st;
            if (lstat(selected_path.c_str(), &st) == 0 && S_ISDIR(st.st_mode)) {
                std::function<void(const std::string&, int, std::string&)> build_tree =
                    [&](const std::string& dir, int depth, std::string& out) {
                        if (depth > 3) return;
                        DIR* d = opendir(dir.c_str());
                        if (!d) return;
                        struct dirent* ent;
                        while ((ent = readdir(d)) != nullptr) {
                            if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
                                continue;
                            std::string full = dir + "/" + ent->d_name;
                            struct stat st2;
                            if (lstat(full.c_str(), &st2) != 0) continue;
                            out += std::string(depth*2, ' ') + ent->d_name + "\n";
                            if (S_ISDIR(st2.st_mode))
                                build_tree(full, depth+1, out);
                        }
                        closedir(d);
                    };
                std::string tree_text;
                build_tree(selected_path, 0, tree_text);
                std::istringstream iss(tree_text);
                std::string line;
                int line_no = 0;
                int max_lines = right_rows - y - 1;
                while (std::getline(iss, line) && y < right_rows - 1) {
                    if (line_no >= right_scroll_offset)
                        mvwaddnstr(right_win, y++, 2, line.c_str(), right_cols - 4);
                    ++line_no;
                }
                if (line_no > right_scroll_offset + max_lines)
                    mvwaddstr(right_win, y, 2, "[...]");
            } else {
                mvwaddstr(right_win, y++, 2, "Seleccione un directorio.");
            }
            break;
        }
    }
    wrefresh(right_win);
}

void draw_bottom_bar() {
    werase(bottom_win);
    std::string user = getenv("USER") ? getenv("USER") : "unknown";
    std::string clock;
    {
        std::lock_guard<std::mutex> lk(clock_mtx);
        clock = clock_str;
    }
    std::string shortcuts = "F1:Texto F2:Hex F3:Prop F4:Arbol F5:Copiar F6:Mover F7:Chmod F8:Borrar F9:Mkdir F10:Nuevo F11:Exec F12:Salir i:inodo h:ocultos s:orden";
    std::string bar = user + " | " + shortcuts + " | " + clock;
    mvwaddnstr(bottom_win, 0, 0, bar.c_str(), getmaxx(bottom_win));
    wrefresh(bottom_win);
}

// Recrear ventanas tras redimension
void resize_windows() {
    endwin();
    refresh();
    clear();
    int max_y, max_x;
    getmaxyx(stdscr, max_y, max_x);
    left_rows = max_y - 2;
    left_cols = max_x / 2;
    right_rows = max_y - 2;
    right_cols = max_x - left_cols;
    left_win = newwin(left_rows, left_cols, 1, 0);
    right_win = newwin(right_rows, right_cols, 1, left_cols);
    bottom_win = newwin(1, max_x, max_y - 1, 0);
    keypad(left_win, TRUE);
    keypad(right_win, TRUE);
    resize_flag = 0;
}

// ==============================
//  Operaciones con fork/exec
// ==============================
int run_command(const std::vector<std::string>& args, bool capture_stdout = false, std::string* output = nullptr) {
    int pipefd[2] = {-1, -1};
    if (capture_stdout) {
        if (pipe(pipefd) == -1) return -1;
    }

    pid_t pid = fork();
    if (pid == 0) {
        // Hijo
        if (capture_stdout) {
            close(pipefd[0]);
            dup2(pipefd[1], STDOUT_FILENO);
            close(pipefd[1]);
        }
        endwin(); // restablecer terminal antes de exec
        std::vector<char*> argv;
        for (const auto& a : args) argv.push_back(const_cast<char*>(a.c_str()));
        argv.push_back(nullptr);
        execvp(argv[0], argv.data());
        perror("execvp");
        _exit(EXIT_FAILURE);
    } else if (pid > 0) {
        // Padre
        if (capture_stdout) {
            close(pipefd[1]);
            char buf[256];
            ssize_t n;
            while ((n = read(pipefd[0], buf, sizeof(buf)-1)) > 0) {
                buf[n] = '\0';
                if (output) *output += buf;
            }
            close(pipefd[0]);
        }
        int status;
        waitpid(pid, &status, 0);
        // Tras restaurar, refrescar pantalla
        refresh();
        return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
    }
    return -1;
}

// Popup para ingresar texto en barra inferior
std::string popup_input(const std::string& prompt) {
    echo();
    curs_set(1);
    char input[256] = {0};
    mvwprintw(bottom_win, 0, 0, "%s", prompt.c_str());
    wrefresh(bottom_win);
    wgetnstr(bottom_win, input, 255);
    noecho();
    curs_set(0);
    return std::string(input);
}

// Confirmación sí/no
bool popup_confirm(const std::string& msg) {
    std::string answer = popup_input(msg + " (s/n): ");
    return answer == "s" || answer == "S";
}

// ==============================
//  Hilo del reloj
// ==============================
void clock_thread_func() {
    while (!quit_flag) {
        time_t now = time(nullptr);
        struct tm tm;
        localtime_r(&now, &tm);
        char buf[64];
        strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", &tm);
        {
            std::lock_guard<std::mutex> lk(clock_mtx);
            clock_str = buf;
        }
        std::this_thread::sleep_for(std::chrono::seconds(1));
    }
}

// ==============================
//  Hilo de refresco con inotify + pipe (IPC)
// ==============================
void refresh_thread_func(std::string path) {
    int inot_fd = inotify_init1(IN_NONBLOCK);
    if (inot_fd < 0) return;
    int wd = inotify_add_watch(inot_fd, path.c_str(),
                               IN_CREATE | IN_DELETE | IN_MODIFY |
                               IN_MOVED_FROM | IN_MOVED_TO);
    while (refresh_active) {
        struct pollfd pfd;
        pfd.fd = inot_fd;
        pfd.events = POLLIN;
        int ret = poll(&pfd, 1, 500); // 500 ms
        if (ret > 0 && (pfd.revents & POLLIN)) {
            char buf[4096] __attribute__((aligned(__alignof__(struct inotify_event))));
            ssize_t len = read(inot_fd, buf, sizeof(buf));
            if (len > 0) {
                // Notificar al principal mediante pipe
                if (refresh_pipe[1] != -1) {
                    char c = '1';
                    write(refresh_pipe[1], &c, 1);
                }
            }
        }
        // Si cambió el path observado, cerrar y reabrir
        std::string new_path;
        {
            std::lock_guard<std::mutex> lk(path_mtx);
            new_path = watched_path;
        }
        if (new_path != path) {
            inotify_rm_watch(inot_fd, wd);
            path = new_path;
            wd = inotify_add_watch(inot_fd, path.c_str(),
                                   IN_CREATE | IN_DELETE | IN_MODIFY |
                                   IN_MOVED_FROM | IN_MOVED_TO);
        }
    }
    if (wd >= 0) inotify_rm_watch(inot_fd, wd);
    close(inot_fd);
}

void start_refresh_thread(const std::string& path) {
    // Detener hilo anterior si existe
    if (refresh_active) {
        refresh_active = false;
        if (refresh_thread_obj.joinable())
            refresh_thread_obj.join();
    }
    // Cerrar extremos de pipe antiguos
    if (refresh_pipe[0] != -1) { close(refresh_pipe[0]); close(refresh_pipe[1]); }
    // Crear nueva pipe
    if (pipe(refresh_pipe) == -1) return;
    // Hacer el extremo de lectura no bloqueante
    int flags = fcntl(refresh_pipe[0], F_GETFL, 0);
    fcntl(refresh_pipe[0], F_SETFL, flags | O_NONBLOCK);

    {
        std::lock_guard<std::mutex> lk(path_mtx);
        watched_path = path;
    }
    refresh_active = true;
    refresh_thread_obj = std::thread(refresh_thread_func, path);
}

// ==============================
//  Lógica principal
// ==============================

void navigate_to(const std::string& path) {
    std::string new_path = path;
    // Resolver ruta real para normalizar
    char* real = realpath(new_path.c_str(), nullptr);
    if (real) {
        new_path = real;
        free(real);
    }
    current_path = new_path;
    files = read_directory(current_path);
    sort_files(files);
    selected_idx = 0;
    left_scroll = 0;
    // Reiniciar observador de cambios
    start_refresh_thread(current_path);
}

int main() {
    // Inicializar ncurses
    setlocale(LC_ALL, "");
    initscr();
    cbreak();
    noecho();
    keypad(stdscr, TRUE);
    curs_set(0);
    start_color();
    init_pair(1, COLOR_WHITE, COLOR_BLACK);   // normal
    init_pair(2, COLOR_BLUE, COLOR_BLACK);    // directorio
    init_pair(3, COLOR_GREEN, COLOR_BLACK);   // ejecutable
    init_pair(4, COLOR_CYAN, COLOR_BLACK);    // symlink
    init_pair(5, COLOR_BLACK, COLOR_WHITE);   // selección (usado con A_REVERSE)

    // Señal de redimension
    signal(SIGWINCH, handle_winch);

    // Ventanas iniciales
    resize_windows();

    // Path actual
    char cwd[PATH_MAX];
    getcwd(cwd, sizeof(cwd));
    current_path = cwd;
    navigate_to(current_path);

    // Lanzar hilo del reloj
    std::thread clock_th(clock_thread_func);

    // Bucle principal
    bool running = true;
    while (running) {
        // Procesar redimensión
        if (resize_flag) {
            resize_windows();
            navigate_to(current_path); // recargar
        }

        // Leer pipe de refresco sin bloquear
        char pipe_buf;
        if (refresh_pipe[0] != -1) {
            ssize_t n = read(refresh_pipe[0], &pipe_buf, 1);
            if (n > 0) {
                // Cambio detectado, recargar directorio
                files = read_directory(current_path);
                sort_files(files);
                if (selected_idx >= static_cast<int>(files.size()))
                    selected_idx = files.size() - 1;
            }
        }

        // Dibujar todo
        draw_left_panel();
        // Obtener ruta del elemento seleccionado
        std::string selected_path;
        if (!files.empty() && selected_idx < static_cast<int>(files.size())) {
            if (files[selected_idx].name == "..")
                selected_path = current_path + "/..";
            else
                selected_path = current_path + "/" + files[selected_idx].name;
        } else {
            selected_path = current_path;
        }
        // Si estamos mostrando salida de ejecución, se usa un path ficticio
        if (!exec_output.empty()) {
            selected_path = "/tmp/exec_output"; // bandera
        }
        draw_right_panel(selected_path);
        draw_bottom_bar();

        // Entrada de teclado con timeout para refresco del reloj
        timeout(100); // ms
        int ch = getch();
        if (ch == ERR) continue; // timeout, volver a dibujar

        // Navegación básica
        if (right_focus) {
            // Foco en panel derecho para scroll
            switch (ch) {
                case KEY_UP:
                    if (right_scroll_offset > 0) right_scroll_offset--;
                    break;
                case KEY_DOWN:
                    right_scroll_offset++;
                    break;
                case KEY_PPAGE:
                    right_scroll_offset -= (right_rows - 4);
                    if (right_scroll_offset < 0) right_scroll_offset = 0;
                    break;
                case KEY_NPAGE:
                    right_scroll_offset += (right_rows - 4);
                    break;
                case '\t': // Tab -> volver a panel izquierdo
                    right_focus = false;
                    break;
            }
            continue;
        }

        // Panel izquierdo activo
        switch (ch) {
            case KEY_UP:
                if (selected_idx > 0) selected_idx--;
                break;
            case KEY_DOWN:
                if (selected_idx < static_cast<int>(files.size()) - 1) selected_idx++;
                break;
            case KEY_PPAGE:
                selected_idx -= (left_rows - 4);
                if (selected_idx < 0) selected_idx = 0;
                break;
            case KEY_NPAGE:
                selected_idx += (left_rows - 4);
                if (selected_idx >= static_cast<int>(files.size()))
                    selected_idx = files.size() - 1;
                break;
            case KEY_HOME:
                selected_idx = 0;
                break;
            case KEY_END:
                selected_idx = files.size() - 1;
                break;
            case '\n': // Enter -> abrir directorio o archivo de texto con nano
                if (!files.empty()) {
                    if (files[selected_idx].name == ".." || files[selected_idx].is_dir) {
                        // Cambiar directorio
                        std::string new_dir = selected_path;
                        navigate_to(new_dir);
                    } else {
                        // Abrir con nano
                        run_command({"nano", selected_path});
                    }
                }
                break;
            case KEY_BACKSPACE: // Retroceder al directorio padre
            case 127: // otro backspace
                if (current_path != "/") {
                    navigate_to(current_path + "/..");
                }
                break;
            case '\t': // Tab -> enfocar panel derecho
                if (!files.empty() && !files[selected_idx].is_dir && files[selected_idx].name != "..") {
                    right_focus = true;
                    right_scroll_offset = 0;
                }
                break;
            // Vistas del panel derecho
            case KEY_F(1): right_view_mode = RightView::TEXT; right_scroll_offset=0; exec_output.clear(); break;
            case KEY_F(2): right_view_mode = RightView::HEX; right_scroll_offset=0; break;
            case KEY_F(3): right_view_mode = RightView::PROPERTIES; right_scroll_offset=0; break;
            case KEY_F(4): right_view_mode = RightView::TREE; right_scroll_offset=0; break;
            // Operaciones
            case KEY_F(5): { // Copiar
                if (!files.empty() && files[selected_idx].name != "..") {
                    std::string dest = popup_input("Destino para copiar: ");
                    if (!dest.empty()) {
                        std::vector<std::string> args = {"cp", "-r", selected_path, dest};
                        run_command(args);
                    }
                }
                break;
            }
            case KEY_F(6): { // Mover/renombrar
                if (!files.empty() && files[selected_idx].name != "..") {
                    std::string dest = popup_input("Nuevo nombre/ubicación: ");
                    if (!dest.empty()) {
                        run_command({"mv", selected_path, dest});
                        navigate_to(current_path);
                    }
                }
                break;
            }
            case KEY_F(7): { // chmod
                if (!files.empty() && files[selected_idx].name != "..") {
                    std::string mode_str = popup_input("Nuevos permisos (octal): ");
                    if (!mode_str.empty()) {
                        run_command({"chmod", mode_str, selected_path});
                    }
                }
                break;
            }
            case KEY_F(8): { // Eliminar
                if (!files.empty() && files[selected_idx].name != "..") {
                    if (popup_confirm("¿Eliminar " + files[selected_idx].name + "?")) {
                        struct stat st;
                        if (lstat(selected_path.c_str(), &st) == 0 && S_ISDIR(st.st_mode))
                            run_command({"rm", "-rf", selected_path});
                        else
                            run_command({"rm", "-f", selected_path});
                        navigate_to(current_path);
                    }
                }
                break;
            }
            case KEY_F(9): { // Crear directorio
                std::string dirname = popup_input("Nombre del nuevo directorio: ");
                if (!dirname.empty()) {
                    std::string new_dir = current_path + "/" + dirname;
                    run_command({"mkdir", new_dir});
                    navigate_to(current_path);
                }
                break;
            }
            case KEY_F(10): { // Crear archivo y abrir nano
                std::string filename = popup_input("Nombre del nuevo archivo: ");
                if (!filename.empty()) {
                    std::string new_file = current_path + "/" + filename;
                    run_command({"touch", new_file});
                    run_command({"nano", new_file});
                    navigate_to(current_path);
                }
                break;
            }
            case KEY_F(11): { // Ejecutar archivo
                if (!files.empty() && files[selected_idx].name != "..") {
                    struct stat st;
                    if (lstat(selected_path.c_str(), &st) == 0 && (st.st_mode & S_IXUSR)) {
                        std::string captured;
                        run_command({selected_path}, true, &captured);
                        exec_output = captured;
                        right_view_mode = RightView::TEXT;
                        right_scroll_offset = 0;
                    }
                }
                break;
            }
            case KEY_F(12): // Salir
            case 'q':
                running = false;
                break;
            case 'i': // Toggle i-nodos
                show_inode = !show_inode;
                navigate_to(current_path);
                break;
            case 'h': // Toggle ocultos
                show_hidden = !show_hidden;
                navigate_to(current_path);
                break;
            case 's': // Cambiar columna de orden
                sort_column = (sort_column + 1) % 4;
                sort_asc = true;
                sort_files(files);
                break;
            case 'S': // Invertir orden
                sort_asc = !sort_asc;
                sort_files(files);
                break;
            // Teclas de columna (1-4) para orden
            case '1': sort_column=0; sort_asc=!sort_asc; sort_files(files); break;
            case '2': sort_column=1; sort_asc=!sort_asc; sort_files(files); break;
            case '3': sort_column=2; sort_asc=!sort_asc; sort_files(files); break;
            case '4': sort_column=3; sort_asc=!sort_asc; sort_files(files); break;
        }
    }

    // Limpieza final
    quit_flag = true;
    if (clock_th.joinable()) clock_th.join();

    refresh_active = false;
    if (refresh_thread_obj.joinable()) refresh_thread_obj.join();
    if (refresh_pipe[0] != -1) { close(refresh_pipe[0]); close(refresh_pipe[1]); }

    delwin(left_win);
    delwin(right_win);
    delwin(bottom_win);
    endwin();
    return 0;
}

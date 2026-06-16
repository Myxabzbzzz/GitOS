typedef unsigned char  u8;
typedef unsigned short u16;
typedef unsigned int   u32;

extern "C" void* memset(void* s, int c, unsigned long n) {
    u8* p = (u8*)s;
    while (n--) *p++ = (u8)c;
    return s;
}

#define VGA ((u16*)0xB8000)
#define W 80
#define H 50

u16 TERM_BG = 0x0000;
u16 TERM_FG = 0x0F00;
u16 TERM_ROOT = 0x0F00;
u16 TERM_ERR = 0x0C00;
u16 TERM_SYS = 0x0B00;

static inline u8  inb(u16 p) { u8 v; __asm__ volatile("inb %1,%0":"=a"(v):"dN"(p)); return v; }
static inline void outb(u16 p, u8 v) { __asm__ volatile("outb %0,%1"::"a"(v),"dN"(p)); }
static inline u16 inw(u16 p) { u16 v; __asm__ volatile("inw %1,%0":"=a"(v):"dN"(p)); return v; }
static inline void outw(u16 p, u16 v) { __asm__ volatile("outw %0,%1"::"a"(v),"dN"(p)); }

static void cls() { for(int i=0; i<W*H; i++) VGA[i] = TERM_BG | ' '; }
static void putc_at(int x, int y, char c, u16 col) { if(x<W && y<H) VGA[y*W+x]=(TERM_BG<<4)|col|(u8)c; }
static void puts_at(int x, int y, const char* s, u16 col) { for(; *s; s++, x++) putc_at(x, y, *s, col); }
static void fill_row(int y, u16 col) { for(int x=0; x<W; x++) VGA[y*W+x]=col|' '; }

static int slen(const char* s) { int n=0; while(s[n]) n++; return n; }
static void scpy(char* d, const char* s) { while((*d++ = *s++)); }
static void sncpy(char* d, const char* s, int n) { int i=0; while(i<n-1 && s[i]) { d[i]=s[i]; i++; } d[i]=0; }
static int scmp(const char* a, const char* b) { while(*a && *a==*b) { a++; b++; } return *a-*b; }
static void scat(char* d, const char* s) { while(*d) d++; while((*d++ = *s++)); }
static int starts(const char* s, const char* p) { while(*p) if(*s++ != *p++) return 0; return 1; }

static void sint(char* b, int n) {
    if(!n) { b[0]='0'; b[1]=0; return; }
    char t[12]; int i=0;
    int neg = n < 0; if(neg) n = -n;
    while(n>0) { t[i++]='0'+(n%10); n/=10; }
    int j=0; if(neg) b[j++]='-';
    while(i>0) b[j++]=t[--i]; b[j]=0;
}

static int atoi(const char* s) {
    int neg = 0;
    if(*s == '-') { neg = 1; s++; }
    int res = 0;
    while(*s >= '0' && *s <= '9') { res = res * 10 + (*s - '0'); s++; }
    return neg ? -res : res;
}

static void delay(int loops) {
    for(volatile int i=0; i<loops*10000; i++);
}

static int ata_wait_drq() {
    for(int i=0; i<100000; i++) {
        u8 status = inb(0x1F7);
        if(status & 0x80) continue; 
        if(status & 0x01) return 0; 
        if(status & 0x08) return 1; 
    }
    return 0;
}

static void ata_read_sector(u32 lba, u16* buf) {
    outb(0x1F6, 0xE0 | ((lba >> 24) & 0x0F));
    outb(0x1F2, 1); outb(0x1F3, (u8)lba); outb(0x1F4, (u8)(lba >> 8)); outb(0x1F5, (u8)(lba >> 16));
    outb(0x1F7, 0x20); 
    if(!ata_wait_drq()) { for(int i=0; i<256; i++) buf[i] = 0; return; }
    for(int i=0; i<256; i++) buf[i] = inw(0x1F0);
}

static void ata_write_sector(u32 lba, const u16* buf) {
    outb(0x1F6, 0xE0 | ((lba >> 24) & 0x0F));
    outb(0x1F2, 1); outb(0x1F3, (u8)lba); outb(0x1F4, (u8)(lba >> 8)); outb(0x1F5, (u8)(lba >> 16));
    outb(0x1F7, 0x30);
    if(!ata_wait_drq()) return;
    for(int i=0; i<256; i++) outw(0x1F0, buf[i]);
    outb(0x1F7, 0xE7);
    for(int i=0; i<100000; i++) { if(!(inb(0x1F7) & 0x80)) break; }
}

#define NFILES 32
#define FSIZE  2048
typedef struct { char name[32]; char data[FSIZE]; int sz; int sys; } __attribute__((packed)) File;
static File fs[NFILES];
static int fscnt = 0;
static int shell_row;
static u32 uptime_ticks = 0;
static bool shift_pressed = false;

#define VIM_MAXLINES 64
#define VIM_COLS     78

static char vim_lines[VIM_MAXLINES][VIM_COLS];
static char vim_yank[VIM_COLS];
static int  vim_nlines;
static int  vim_cx, vim_cy;
static int  vim_top;
static int  vim_mode;
static bool vim_modified;
static char vim_cmd[80];
static char vim_pending;

static void disk_sync_write() {
    u8* ptr = (u8*)fs;
    const int SECTORS = (sizeof(fs) + 511) / 512;
    for (int s = 0; s < SECTORS; s++) {
        u16 sector_buf[256];
        for (int i = 0; i < 512; i++) ((u8*)sector_buf)[i] = ptr[s * 512 + i];
        ata_write_sector(100 + s, sector_buf);
    }
}

static void disk_sync_read() {
    u8* ptr = (u8*)fs;
    const int SECTORS = (sizeof(fs) + 511) / 512;
    for (int s = 0; s < SECTORS; s++) {
        u16 sector_buf[256];
        ata_read_sector(100 + s, sector_buf);
        for (int i = 0; i < 512; i++) ptr[s * 512 + i] = ((u8*)sector_buf)[i];
    }
    fscnt = 0;
    for(int i=0; i<NFILES; i++) if(fs[i].name[0] != 0) fscnt = i + 1;
}

static File* fs_find(const char* n) { for(int i=0; i<NFILES; i++) if(fs[i].name[0] && !scmp(fs[i].name, n)) return &fs[i]; return 0; }

static File* fs_new(const char* n, int sys) {
    for(int i=0; i<NFILES; i++) {
        if(fs[i].name[0] == 0) {
            sncpy(fs[i].name, n, 32); fs[i].data[0]=0; fs[i].sz=0; fs[i].sys=sys;
            if(i >= fscnt) fscnt = i + 1;
            return &fs[i];
        }
    }
    return 0;
}

static File* fs_open(const char* n) {
    File* f = fs_find(n);
    return f ? f : fs_new(n, 0);
}

static void vim_load(File* f) {
    for(int i = 0; i < VIM_MAXLINES; i++) vim_lines[i][0] = 0;
    vim_nlines = 0; vim_cx = 0; vim_cy = 0; vim_top = 0;
    vim_mode = 0; vim_modified = false; vim_pending = 0;
    vim_cmd[0] = 0; vim_yank[0] = 0;

    if(f->sz == 0) { vim_nlines = 1; return; }

    char* p = f->data;
    int row = 0;
    while(*p && row < VIM_MAXLINES) {
        int col = 0;
        while(*p && *p != '\n' && col < VIM_COLS - 1) vim_lines[row][col++] = *p++;
        vim_lines[row][col] = 0;
        if(*p == '\n') p++;
        row++;
    }
    vim_nlines = row > 0 ? row : 1;
}

static void vim_save(File* f) {
    char* p = f->data;
    for(int i = 0; i < vim_nlines; i++) {
        char* line = vim_lines[i];
        while(*line) *p++ = *line++;
        if(i < vim_nlines - 1) *p++ = '\n';
    }
    *p = 0;
    f->sz = (int)(p - f->data);
    disk_sync_write();
    vim_modified = false;
}

static void vim_render(File* f) {
    // Row 0: header
    fill_row(0, 0xF000);
    char hdr[82] = "";
    if(vim_mode == 0)      scat(hdr, "[NORMAL]  ");
    else if(vim_mode == 1) scat(hdr, "[INSERT]  ");
    else                   scat(hdr, "[COMMAND] ");
    scat(hdr, f->name);
    if(vim_modified) scat(hdr, "  [Modified]");
    puts_at(1, 0, hdr, 0xF000);

    // Rows 1..H-2: file content
    int view_rows = H - 2;
    for(int i = 0; i < view_rows; i++) {
        int file_row = vim_top + i;
        int screen_row = i + 1;
        for(int x = 0; x < W; x++) VGA[screen_row * W + x] = TERM_BG | ' ';
        if(file_row < vim_nlines) {
            char* line = vim_lines[file_row];
            int len = slen(line);
            for(int x = 0; x < len && x < W; x++) {
                u8 ch = (u8)line[x];
                if(file_row == vim_cy && x == vim_cx && vim_mode != 2)
                    VGA[screen_row * W + x] = 0xF000 | ch;
                else
                    VGA[screen_row * W + x] = TERM_FG | ch;
            }
            if(file_row == vim_cy && vim_cx >= len && vim_mode != 2)
                VGA[screen_row * W + (vim_cx < W ? vim_cx : W-1)] = 0xF000 | ' ';
        } else {
            VGA[screen_row * W] = TERM_FG | '~';
        }
    }

    // Row H-1: status bar
    fill_row(H-1, 0xF000);
    if(vim_mode == 2) {
        char cmdline[82] = ":";
        scat(cmdline, vim_cmd);
        puts_at(0, H-1, cmdline, 0xF000);
    } else {
        char pos[48] = "Ln "; char n[12];
        sint(n, vim_cy + 1); scat(pos, n);
        scat(pos, ", Col "); sint(n, vim_cx + 1); scat(pos, n);
        puts_at(1, H-1, pos, 0xF000);
    }
}

static void vim_x() {
    char* line = vim_lines[vim_cy];
    int len = slen(line);
    if(vim_cx >= len) return;
    for(int i = vim_cx; i < len; i++) line[i] = line[i+1];
    int newlen = slen(line);
    if(vim_cx > 0 && vim_cx >= newlen) vim_cx = newlen > 0 ? newlen - 1 : 0;
    vim_modified = true;
}

static void vim_dd() {
    sncpy(vim_yank, vim_lines[vim_cy], VIM_COLS);
    if(vim_nlines > 1) {
        for(int i = vim_cy; i < vim_nlines - 1; i++)
            sncpy(vim_lines[i], vim_lines[i+1], VIM_COLS);
        vim_lines[vim_nlines-1][0] = 0;
        vim_nlines--;
        if(vim_cy >= vim_nlines) vim_cy = vim_nlines - 1;
    } else {
        vim_lines[0][0] = 0;
    }
    vim_cx = 0;
    vim_modified = true;
}

static void vim_yy() {
    sncpy(vim_yank, vim_lines[vim_cy], VIM_COLS);
}

static void vim_p() {
    if(vim_nlines >= VIM_MAXLINES) return;
    for(int i = vim_nlines; i > vim_cy + 1; i--)
        sncpy(vim_lines[i], vim_lines[i-1], VIM_COLS);
    sncpy(vim_lines[vim_cy + 1], vim_yank, VIM_COLS);
    vim_nlines++;
    vim_cy++;
    vim_cx = 0;
    vim_modified = true;
}

static void vim_o() {
    if(vim_nlines >= VIM_MAXLINES) return;
    for(int i = vim_nlines; i > vim_cy + 1; i--)
        sncpy(vim_lines[i], vim_lines[i-1], VIM_COLS);
    vim_lines[vim_cy + 1][0] = 0;
    vim_nlines++;
    vim_cy++;
    vim_cx = 0;
    vim_mode = 1;
    vim_modified = true;
}

#define KEY_UP    0x80
#define KEY_DOWN  0x81
#define KEY_LEFT  0x82
#define KEY_RIGHT 0x83

static u8 kbd_scan_raw() {
    while(!(inb(0x64) & 1)) uptime_ticks++;
    return inb(0x60);
}

static u8 get_key() {
    while(1) {
        u8 sc = kbd_scan_raw();
        if(sc == 0xE0) {
            u8 ext = kbd_scan_raw();
            if(ext == 0x48) return KEY_UP;
            if(ext == 0x50) return KEY_DOWN;
            if(ext == 0x4B) return KEY_LEFT;
            if(ext == 0x4D) return KEY_RIGHT;
            continue;
        }
        if(sc == 0x2A || sc == 0x36) { shift_pressed = true;  continue; }
        if(sc == 0xAA || sc == 0xB6) { shift_pressed = false; continue; }
        if(sc >= 0x80) continue;
        return sc;
    }
}

static char sc2ch(u8 sc) {
    static const char t[128] = {
        0,  0, '1','2','3','4','5','6','7','8','9','0','-','=', 0,
        0, 'q','w','e','r','t','y','u','i','o','p','[',']','\n',
        0, 'a','s','d','f','g','h','j','k','l',';','\'','`',  0,
       '\\','z','x','c','v','b','n','m',',','.','/', 0, '*', 0, ' '
    };
    static const char ts[128] = {
        0,  0, '!','@','#','$','%','^','&','*','(',')','_','+', 0,
        0, 'Q','W','E','R','T','Y','U','I','O','P','{','}','\n',
        0, 'A','S','D','F','G','H','J','K','L',':','"','~',  0,
       '|','Z','X','C','V','B','N','M','<','>','?', 0, '*', 0, ' '
    };
    if(sc >= 128) return 0;
    return shift_pressed ? ts[sc] : t[sc];
}

static int readline(char* buf, int max, int row, u16 prompt_len, u16 col) {
    int i=0; buf[0]=0;
    while(1){
        puts_at(prompt_len, row, buf, col);
        putc_at(prompt_len+i, row, '_', 0x0F00); 
        u8 sc=get_key();
        if(sc==0x1C) { buf[i]=0; putc_at(prompt_len+i, row, ' ', col); return i; } 
        if(sc==0x0E && i>0) { 
            buf[--i]=0; 
            putc_at(prompt_len+i, row, ' ', col);   
            putc_at(prompt_len+i+1, row, ' ', col); 
            continue;
        }
        if(sc==0x01) return -1; 
        char c=sc2ch(sc);
        if(c && i<max-1) { buf[i++]=c; buf[i]=0; }
    }
}

static void vim_editor(File* f) {
    vim_load(f);
    vim_render(f);

    while(1) {
        u8 sc = get_key();
        bool quit = false;

        if(vim_mode == 0) {
            // NORMAL mode
            char nch = sc2ch(sc);
            if(nch == 'h' || sc == KEY_LEFT)  { if(vim_cx > 0) vim_cx--; vim_pending = 0; }
            else if(nch == 'l' || sc == KEY_RIGHT) { if(vim_cx < slen(vim_lines[vim_cy])) vim_cx++; vim_pending = 0; }
            else if(nch == 'k' || sc == KEY_UP)    { if(vim_cy > 0) vim_cy--; vim_pending = 0; }
            else if(nch == 'j' || sc == KEY_DOWN)  { if(vim_cy < vim_nlines-1) vim_cy++; vim_pending = 0; }
            else if(nch == 'i') { vim_mode = 1; vim_pending = 0; }
            else if(nch == 'a') {
                int len = slen(vim_lines[vim_cy]);
                if(vim_cx < len) vim_cx++;
                vim_mode = 1; vim_pending = 0;
            }
            else if(nch == 'o') { vim_o(); vim_pending = 0; }
            else if(nch == 'x') { vim_x(); vim_pending = 0; }
            else if(nch == 'p') { vim_p(); vim_pending = 0; }
            else if(nch == ':') { vim_mode = 2; vim_cmd[0] = 0; vim_pending = 0; }
            else if(nch == 'd' || nch == 'y') {
                char ch = nch;
                if(vim_pending == ch) {
                    if(ch == 'd') vim_dd();
                    else          vim_yy();
                    vim_pending = 0;
                } else {
                    vim_pending = ch;
                }
            }
            else { vim_pending = 0; }

        } else if(vim_mode == 1) {
            // INSERT mode
            if(sc == 0x01) {
                // Esc → NORMAL
                vim_mode = 0;
                if(vim_cx > 0) vim_cx--;
            }
            else if(sc == 0x1C) {
                // Enter → split line at cursor
                char* cur = vim_lines[vim_cy];
                char right[VIM_COLS] = "";
                sncpy(right, cur + vim_cx, VIM_COLS);
                cur[vim_cx] = 0;
                if(vim_nlines < VIM_MAXLINES) {
                    for(int i = vim_nlines; i > vim_cy + 1; i--)
                        sncpy(vim_lines[i], vim_lines[i-1], VIM_COLS);
                    sncpy(vim_lines[vim_cy + 1], right, VIM_COLS);
                    vim_nlines++;
                    vim_cy++;
                    vim_cx = 0;
                    vim_modified = true;
                }
            }
            else if(sc == 0x0E) {
                // Backspace
                if(vim_cx > 0) {
                    char* line = vim_lines[vim_cy];
                    int len = slen(line);
                    for(int i = vim_cx - 1; i < len; i++) line[i] = line[i+1];
                    vim_cx--;
                    vim_modified = true;
                } else if(vim_cy > 0) {
                    // join current line onto previous
                    char* prev = vim_lines[vim_cy - 1];
                    int prev_len = slen(prev);
                    char* cur = vim_lines[vim_cy];
                    if(prev_len + slen(cur) < VIM_COLS - 1) {
                        scat(prev, cur);
                        for(int i = vim_cy; i < vim_nlines - 1; i++)
                            sncpy(vim_lines[i], vim_lines[i+1], VIM_COLS);
                        vim_lines[vim_nlines-1][0] = 0;
                        vim_nlines--;
                        vim_cy--;
                        vim_cx = prev_len;
                        vim_modified = true;
                    }
                }
            }
            else if(sc == KEY_UP)    { if(vim_cy > 0) vim_cy--; }
            else if(sc == KEY_DOWN)  { if(vim_cy < vim_nlines-1) vim_cy++; }
            else if(sc == KEY_LEFT)  { if(vim_cx > 0) vim_cx--; }
            else if(sc == KEY_RIGHT) { if(vim_cx < slen(vim_lines[vim_cy])) vim_cx++; }
            else {
                char c = sc2ch(sc);
                if(c) {
                    char* line = vim_lines[vim_cy];
                    int len = slen(line);
                    if(len < VIM_COLS - 1) {
                        for(int i = len; i >= vim_cx; i--) line[i+1] = line[i];
                        line[vim_cx] = c;
                        vim_cx++;
                        vim_modified = true;
                    }
                }
            }

        } else {
            // COMMAND mode
            if(sc == 0x01) {
                // Esc → cancel command
                vim_mode = 0; vim_cmd[0] = 0;
            }
            else if(sc == 0x1C) {
                // Enter → execute command
                if(!scmp(vim_cmd, "w"))   { vim_save(f); }
                else if(!scmp(vim_cmd, "q"))  {
                    if(!vim_modified) quit = true;
                    else { fill_row(H-1, 0xF000); puts_at(0, H-1, "E: unsaved changes -- use :q! to force", 0x0C00); }
                }
                else if(!scmp(vim_cmd, "wq")) { vim_save(f); quit = true; }
                else if(!scmp(vim_cmd, "q!")) { quit = true; }
                else {
                    fill_row(H-1, 0xF000);
                    char err[82] = "E: unknown command: "; scat(err, vim_cmd);
                    puts_at(0, H-1, err, 0x0C00);
                }
                if(!quit) { vim_mode = 0; vim_cmd[0] = 0; }
            }
            else if(sc == 0x0E) {
                // Backspace in command line
                int len = slen(vim_cmd);
                if(len > 0) vim_cmd[len-1] = 0;
            }
            else {
                char c = sc2ch(sc);
                if(c) {
                    int len = slen(vim_cmd);
                    if(len < 78) { vim_cmd[len] = c; vim_cmd[len+1] = 0; }
                }
            }
        }

        if(quit) break;

        // Scroll adjustment
        if(vim_cy < vim_top) vim_top = vim_cy;
        if(vim_cy >= vim_top + (H - 2)) vim_top = vim_cy - (H - 3);

        // Clamp cursor column — always clamp to line length, then apply NORMAL-mode stricter clamp
        int line_len = slen(vim_lines[vim_cy]);
        if(vim_cx > line_len) vim_cx = line_len;
        if(vim_mode == 0 && vim_cx >= line_len)
            vim_cx = line_len > 0 ? line_len - 1 : 0;

        vim_render(f);
    }

    cls(); shell_row = 1;
}

static void text_editor(File* f) {
    cls(); fill_row(0, 0xF000); fill_row(H-1, 0xF000);
    puts_at(2, 0, " GitOS Code Editor v1.0 ", 0xF000);
    puts_at(2, H-1, "^ESC Save & Exit   |   File: ", 0xF000); puts_at(31, H-1, f->name, 0xF000);

    char buf[2048]="";
    if(f->sz > 0) sncpy(buf, f->data, 2048);

    int cursor_y = 2;
    char line_buf[64]="";
    char* ptr = buf;

    int max_lines = H - 4;
    while(cursor_y < 2 + max_lines) {
        if(ptr - buf >= FSIZE - 64) break;
        if(readline(line_buf, 62, cursor_y, 2, 0x0F00) < 0) break;
        scpy(ptr, line_buf);
        ptr += slen(line_buf);
        *ptr++ = '\n';
        *ptr = 0;
        cursor_y++;
    }

    scpy(f->data, buf);
    f->sz = slen(buf);
    disk_sync_write();
    cls(); shell_row = 1;
}

static void run_matrix() {
    cls(); u32 rnd = 0xACE1u;
    for(int t=0; t<120; t++) {
        int x = rnd % W; rnd = (rnd >> 1) ^ (-(rnd & 1u) & 0xB400u); int y = rnd % H;
        putc_at(x, y, '0' + (rnd % 10), 0x0F00); delay(1000);
    }
    cls(); shell_row = 2;
}

static void sh_print(const char* s, u16 col) {
    puts_at(2, shell_row, s, col);
    shell_row++;
    if(shell_row >= H-2) { 
        cls(); shell_row=1; 
        fill_row(0, 0xF000); puts_at(2, 0, " GitOS Shell | admin ", 0xF000);
    }
}

static void execute_script(const char* filename) {
    File* f = fs_find(filename);
    if(!f) { sh_print("run: file not found", TERM_ERR); return; }
    
    sh_print("--- Executing Script ---", 0x0F00);
    char* ptr = f->data;
    char line[64];
    
    while(*ptr) {
        int i=0;
        while(*ptr && *ptr != '\n' && i<62) line[i++] = *ptr++;
        line[i] = 0;
        if(*ptr == '\n') ptr++;
        
        if(starts(line, "print ")) {
            sh_print(line + 6, TERM_FG);
        } 
        else if(!scmp(line, "clear")) {
            cls(); shell_row=1;
        } 
        else if(!scmp(line, "delay")) {
            delay(10000);
        }
        else if(starts(line, "color ")) {
            if(line[6] == '0') TERM_FG = 0x0F00;
            else if(line[6] == '1') TERM_FG = 0x0A00;
            else if(line[6] == '2') TERM_FG = 0x0900;
            else if(line[6] == '3') TERM_FG = 0x0400;
            cls(); shell_row=1;
        }
        else if(!scmp(line, "matrix")) {
            run_matrix();
        }
    }
    sh_print("--- Program Finished ---", 0x0F00);
}

static void run_sysinfo() {
    if(shell_row >= H-10) { cls(); shell_row=1; }
    const char* logo[] = {
        "  /\\_/\\  ",
        " ( o.o ) ",
        "  > ^ <  "
    };
    for(int i=0; i<3; i++) puts_at(2, shell_row+i, logo[i], 0x0F00); 
    
    puts_at(20, shell_row++, "admin@gitos", 0x0F00);
    puts_at(20, shell_row++, "----------------", TERM_FG);
    puts_at(20, shell_row++, "OS: GitOS Core 4.0", TERM_FG);
    puts_at(20, shell_row++, "Kernel: C++17 Monolithic Custom", TERM_FG);
    puts_at(20, shell_row++, "Graphics: VGA Text Mode", TERM_FG);
    puts_at(20, shell_row++, "Storage: ATA PIO (Persistent)", TERM_FG);
    shell_row++;
}

static void shell_core() {
    cls(); fill_row(0, 0xF000); fill_row(H-1, 0xF000);
    puts_at(2, 0, " GitOS Shell | admin ", 0xF000);
    puts_at(2, H-1, " F1 Help | F2 Setup | System Ready ", 0xF000);
    shell_row=2; 
    
    run_sysinfo();
    
    char cmd[128];
    while(1){
        puts_at(0, shell_row, "admin@gitos:~# ", TERM_ROOT);
        if(readline(cmd, 100, shell_row, 15, TERM_FG)<0) continue;
        shell_row++;

        if(!scmp(cmd, "help")) {
            sh_print("=== GitOS Command Reference ===", TERM_SYS);
            sh_print("FILES : ls, cat <file>, touch <file>, rm <file>, edit <file>, vim <file>", TERM_FG);
            sh_print("SYSTEM: clear, color <1/2/3>, res <WxH>, reboot, shutdown", TERM_FG);
            sh_print("APPS  : sysinfo, calc <expr>, time, uptime, whoami, ascii", TERM_FG);
            sh_print("DEV   : run <file.gs> (Execute GitScript programs)", 0x0F00);
        }
        else if(starts(cmd, "res ")) {
            sh_print("ERROR: VBE (VESA BIOS Extensions) driver is not loaded.", TERM_ERR);
            sh_print("System running in Ring-0. Hardware locked to 80x25 VGA Text Mode.", TERM_ERR);
        }
        else if(starts(cmd, "run ")) {
            execute_script(cmd+4);
        }
        else if(!scmp(cmd, "sysinfo")) run_sysinfo();
        else if(!scmp(cmd, "whoami")) sh_print("admin (Ring 0 Superuser)", TERM_FG);
        else if(!scmp(cmd, "uptime")) {
            char b[32]="Uptime Ticks: "; char n[12]; sint(n, uptime_ticks); scat(b, n);
            sh_print(b, TERM_FG);
        }
        else if(!scmp(cmd, "clear") || !scmp(cmd, "cls")) { cls(); shell_row=1; }
        else if(starts(cmd, "color ")) {
            if(cmd[6] == '0') TERM_FG = 0x0F00;
            else if(cmd[6] == '1') TERM_FG = 0x0A00;
            else if(cmd[6] == '2') TERM_FG = 0x0900;
            else if(cmd[6] == '3') TERM_FG = 0x0400;
            cls(); shell_row=1;
        }
        else if(!scmp(cmd, "reboot")) { outb(0x64, 0xFE); while(1); }
        else if(!scmp(cmd, "shutdown")) { outw(0x604, 0x2000); outw(0xB004, 0x2000); while(1); }
        else if(!scmp(cmd, "ascii")) {
            sh_print("  /\\_/\\  ", 0x0F00);
            sh_print(" ( o.o ) ", 0x0F00);
            sh_print("  > ^ <  ", 0x0F00);
        }
        else if(starts(cmd, "echo ")) { sh_print(cmd+5, TERM_FG); }
        else if(starts(cmd, "calc ")) {
            char* p = cmd + 5; int n1 = atoi(p);
            while(*p == '-' || (*p >= '0' && *p <= '9')) p++; while(*p == ' ') p++;
            char op = *p; if(op) p++; while(*p == ' ') p++;
            int n2 = atoi(p); int res = 0; int ok = 1;
            if(op == '+') res = n1 + n2;
            else if(op == '-') res = n1 - n2;
            else if(op == '*') res = n1 * n2;
            else if(op == '/') {
                if(!n2) { sh_print("Error: division by zero", TERM_ERR); ok = 0; }
                else res = n1 / n2;
            }
            if(ok) { char b[32]="Result: "; char n[12]; sint(n, res); scat(b, n); sh_print(b, 0x0F00); }
        }
        else if(!scmp(cmd, "ls")) {
            for(int i=0; i<NFILES; i++){
                if(!fs[i].name[0]) continue;
                char line[64] = "";
                if(fs[i].sys) scat(line, "-rw-r--r-- admin root  ");
                else scat(line, "-rw-rw-rw- admin user  ");
                char sz[8]; sint(sz, fs[i].sz); scat(line, sz); scat(line, " B  "); scat(line, fs[i].name);
                sh_print(line, fs[i].sys ? 0x0F00 : 0x0F00); 
            }
        }
        else if(starts(cmd, "cat ")) {
            File* f=fs_find(cmd+4);
            sh_print(f ? f->data : "cat: file not found", f ? TERM_FG : TERM_ERR);
        }
        else if(starts(cmd, "touch ")) { fs_open(cmd+6); disk_sync_write(); }
        else if(starts(cmd, "rm ")) {
            File* f=fs_find(cmd+3);
            if(f && !f->sys) { f->name[0]=0; disk_sync_write(); }
            else sh_print("rm: Permission denied or file not found", TERM_ERR);
        }
        else if(starts(cmd, "vim ")) {
            File* f=fs_open(cmd+4);
            if(f) vim_editor(f);
            else sh_print("vim: cannot open file", TERM_ERR);
        }
        else if(starts(cmd, "edit ")) {
            File* f=fs_open(cmd+5);
            if(f) text_editor(f);
        }
        else if(cmd[0] != 0) {
            char err[64] = ""; scat(err, cmd); scat(err, ": command not found");
            sh_print(err, TERM_ERR);
        }
    }
}

extern "C" __attribute__((section(".text.boot"))) void kmain() {
    cls();
    fill_row(0, 0xF000); puts_at(2, 0, "GitOS GRUB Bootloader...", 0xF000);
    delay(50);
    puts_at(2, 2, "[ OK ] Loading GitOS Core...", 0x0F00); delay(40);
    puts_at(2, 3, "[ OK ] Mounting Root VFS...", 0x0F00);
    
    disk_sync_read();

    if(fs_find("system.log") == 0) {
        for(int i=0; i<NFILES; i++) { fs[i].name[0] = 0; fs[i].sys = 0; }
        
        File* f = fs_new("readme.txt", 0); 
        scpy(f->data, "Welcome to GitOS! You are running as Admin."); f->sz=slen(f->data);
        
        File* g = fs_new("system.log", 1); 
        scpy(g->data, "[BOOT]: Core loaded successfully. Subsystems green."); g->sz=slen(g->data);
        
        File* prog = fs_new("test.gs", 0);
        scpy(prog->data, "print Hello from GitScript!\ndelay\ncolor 1\nprint Changed background!\n");
        prog->sz=slen(prog->data);

        disk_sync_write();
    }

    delay(50);
    shell_core();
    
    while(1) __asm__("hlt");
}

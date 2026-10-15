/* Backtracking regex engine (BitState-style memoisation: each (pc,pos) visited once per search,
   so no exponential blow-up and no infinite loops on empty iterations).
   Syntax: . * + ? *? +? ?? {n} {n,} {n,m} (lazy with ?)  [...] [^...] ranges, \d \w \s \D \W \S,
   ( ) (?: ) | ^ $ \b \B, escapes \t \n \r \f \v \xHH \uHHHH \\ \. etc. */
#include <stdlib.h>
#include <string.h>
#include "regex.h"
#ifdef _WIN32
#include <windows.h>
#endif

enum { I_CHAR, I_ANY, I_CLASS, I_SPLIT, I_JMP, I_SAVE, I_BOL, I_EOL, I_WORDB, I_NWORDB, I_MATCH };
typedef struct { int op, x, y; } Inst;
typedef struct { int neg, n, cls; rechar *lo, *hi; } Class;   /* cls bits: 1 d,2 w,4 s,8 D,16 W,32 S */
enum { N_CHAR, N_ANY, N_CLASS, N_BOL, N_EOL, N_WB, N_NWB, N_CAT, N_ALT, N_REP, N_GROUP, N_EMPTY };
typedef struct Node { int t, c, min, max, greedy, idx; struct Node *a, *b; struct Node **kids; int nk; } Node;

struct Regex {
    Inst *prog; int np, capp;
    Class *cls; int ncls;
    int icase;
    int firstch;          /* literal first char for fast scan, or -1 */
    unsigned char *vis; size_t viscap;
    int *stk; size_t stkcap;
};

/* ---------- character helpers ---------- */
static rechar fold1(rechar c) {
    if (c >= 'A' && c <= 'Z') return (rechar)(c + 32);
    if (c < 0x80) return c;
    if (c >= 0xFF21 && c <= 0xFF3A) return (rechar)(c + 32);
#ifdef _WIN32
    WCHAR w = c; CharLowerBuffW(&w, 1); return w;
#else
    if (c >= 0xC0 && c <= 0xDE && c != 0xD7) return (rechar)(c + 32);
    if (c >= 0x391 && c <= 0x3A9) return (rechar)(c + 32);
    if (c >= 0x410 && c <= 0x42F) return (rechar)(c + 32);
    return c;
#endif
}
static rechar g_fold[65536]; static int g_foldInit;   /* fold1 of every UTF-16 unit (built once) */
static rechar fold(rechar c) {
    if (!g_foldInit) { for (unsigned i = 0; i < 65536; i++) g_fold[i] = fold1((rechar)i); g_foldInit = 1; }
    return g_fold[(unsigned short)c];
}
static int isword(rechar c) {
    if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_') return 1;
    if (c < 0x80) return 0;
    if (c >= 0xD800 && c <= 0xDFFF) return 1;          /* astral letters/ideographs */
    if (c >= 0x3041 && c <= 0x30FF) return c != 0x30FB; /* kana (except ・) */
    if (c >= 0x3400 && c <= 0x9FFF) return 1;
    if (c >= 0xF900 && c <= 0xFAFF) return 1;
    if (c >= 0xFF10 && c <= 0xFF19) return 1;
    if ((c >= 0xFF21 && c <= 0xFF3A) || (c >= 0xFF41 && c <= 0xFF5A) || (c >= 0xFF66 && c <= 0xFF9F)) return 1;
    if (c == 0x3005 || c == 0x30FC) return 1;
#ifdef _WIN32
    return IsCharAlphaNumericW(c) ? 1 : 0;
#else
    return (c >= 0xC0 && c <= 0x24F && c != 0xD7 && c != 0xF7);
#endif
}
static int isdig(rechar c) { return (c >= '0' && c <= '9') || (c >= 0xFF10 && c <= 0xFF19); }
static int isspc(rechar c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v' || c == 0x3000 || c == 0xA0 || c == 0xFEFF; }
static int clsmatch1(const Class *k, rechar c) {
    if ((k->cls & 1) && isdig(c)) return 1;
    if ((k->cls & 2) && isword(c)) return 1;
    if ((k->cls & 4) && isspc(c)) return 1;
    if ((k->cls & 8) && !isdig(c)) return 1;
    if ((k->cls & 16) && !isword(c)) return 1;
    if ((k->cls & 32) && !isspc(c)) return 1;
    for (int i = 0; i < k->n; i++) if (c >= k->lo[i] && c <= k->hi[i]) return 1;
    return 0;
}
static int clsmatch(const Regex *re, const Class *k, rechar c) {
    int m = clsmatch1(k, c);
    if (!m && re->icase) {
        rechar l = fold(c);
        m = clsmatch1(k, l);
        if (!m) {  /* try upper case of ASCII/fullwidth */
            rechar u = c;
            if (c >= 'a' && c <= 'z') u = (rechar)(c - 32);
            else if (c >= 0xFF41 && c <= 0xFF5A) u = (rechar)(c - 32);
            if (u != c) m = clsmatch1(k, u);
        }
    }
    return k->neg ? !m : m;
}

/* ---------- parser ---------- */
typedef struct { const rechar *p; int len, i, err, ngroup; Regex *re; Node **all; int nall, capall; } P;
static Node *mk(P *ps, int t) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) { ps->err = 1; return NULL; }
    n->t = t;
    if (ps->nall == ps->capall) { ps->capall = ps->capall ? ps->capall * 2 : 32; ps->all = realloc(ps->all, (size_t)ps->capall * sizeof(Node *)); }
    ps->all[ps->nall++] = n;
    return n;
}
static void addkid(Node *cat, Node *k) {
    cat->kids = realloc(cat->kids, (size_t)(cat->nk + 1) * sizeof(Node *));
    cat->kids[cat->nk++] = k;
}
static int hexv(rechar c) { if (c >= '0' && c <= '9') return c - '0'; if (c >= 'a' && c <= 'f') return c - 'a' + 10; if (c >= 'A' && c <= 'F') return c - 'A' + 10; return -1; }
/* parse escape after '\'; returns char or -1..-6 for class escapes (d w s D W S), -7 \b, -8 \B */
static int parse_escape(P *ps) {
    if (ps->i >= ps->len) { ps->err = 1; return 0; }
    rechar c = ps->p[ps->i++];
    switch (c) {
    case 'd': return -1; case 'w': return -2; case 's': return -3;
    case 'D': return -4; case 'W': return -5; case 'S': return -6;
    case 'b': return -7; case 'B': return -8;
    case 't': return '\t'; case 'n': return '\n'; case 'r': return '\r'; case 'f': return '\f'; case 'v': return '\v';
    case '0': return 0;
    case 'x': case 'u': {
        int nd = c == 'x' ? 2 : 4, v = 0;
        for (int k = 0; k < nd; k++) {
            int h = ps->i < ps->len ? hexv(ps->p[ps->i]) : -1;
            if (h < 0) { ps->err = 1; return 0; }
            v = v * 16 + h; ps->i++;
        }
        return v;
    }
    default: return c;   /* \. \\ \( etc, and any other char literally */
    }
}
static int clsbit(int e) { static const int b[] = { 1, 2, 4, 8, 16, 32 }; return b[-e - 1]; }
static Node *parse_class(P *ps) {
    Regex *re = ps->re;
    re->cls = realloc(re->cls, (size_t)(re->ncls + 1) * sizeof(Class));
    Class *k = &re->cls[re->ncls]; memset(k, 0, sizeof *k);
    int idx = re->ncls++;
    if (ps->i < ps->len && ps->p[ps->i] == '^') { k->neg = 1; ps->i++; }
    int first = 1;
    while (ps->i < ps->len && (ps->p[ps->i] != ']' || first)) {
        first = 0;
        int lo;
        rechar c = ps->p[ps->i++];
        if (c == '\\') { lo = parse_escape(ps); if (lo <= -7) lo = lo == -7 ? 8 : 'B'; if (lo < 0) { k->cls |= clsbit(lo); continue; } }
        else lo = c;
        int hi = lo;
        if (ps->i + 1 < ps->len && ps->p[ps->i] == '-' && ps->p[ps->i + 1] != ']') {
            ps->i++;
            rechar d = ps->p[ps->i++];
            if (d == '\\') { hi = parse_escape(ps); if (hi < 0) { ps->err = 1; return NULL; } }
            else hi = d;
            if (hi < lo) { ps->err = 1; return NULL; }
        }
        k = &re->cls[idx];
        k->lo = realloc(k->lo, (size_t)(k->n + 1) * sizeof(rechar));
        k->hi = realloc(k->hi, (size_t)(k->n + 1) * sizeof(rechar));
        k->lo[k->n] = (rechar)lo; k->hi[k->n] = (rechar)hi; k->n++;
    }
    if (ps->i >= ps->len) { ps->err = 1; return NULL; }
    ps->i++; /* ']' */
    Node *n = mk(ps, N_CLASS); if (n) n->c = idx;
    return n;
}
static Node *parse_alt(P *ps);
static Node *parse_atom(P *ps) {
    rechar c = ps->p[ps->i++];
    Node *n;
    switch (c) {
    case '.': return mk(ps, N_ANY);
    case '^': return mk(ps, N_BOL);
    case '$': return mk(ps, N_EOL);
    case '[': return parse_class(ps);
    case '(': {
        int cap = 1;
        if (ps->i + 1 < ps->len && ps->p[ps->i] == '?' && ps->p[ps->i + 1] == ':') { cap = 0; ps->i += 2; }
        int gi = cap ? ++ps->ngroup : 0;
        Node *in = parse_alt(ps);
        if (ps->err) return NULL;
        if (ps->i >= ps->len || ps->p[ps->i] != ')') { ps->err = 1; return NULL; }
        ps->i++;
        if (!cap) return in;
        n = mk(ps, N_GROUP); if (n) { n->a = in; n->idx = gi; }
        return n;
    }
    case '\\': {
        int e = parse_escape(ps);
        if (e == -7) return mk(ps, N_WB);
        if (e == -8) return mk(ps, N_NWB);
        if (e < 0) {
            Regex *re = ps->re;
            re->cls = realloc(re->cls, (size_t)(re->ncls + 1) * sizeof(Class));
            Class *k = &re->cls[re->ncls]; memset(k, 0, sizeof *k);
            k->cls = clsbit(e);
            n = mk(ps, N_CLASS); if (n) n->c = re->ncls;
            re->ncls++;
            return n;
        }
        n = mk(ps, N_CHAR); if (n) n->c = e;
        return n;
    }
    case '*': case '+': case '?': case ')': case '|':
        ps->err = 1; return NULL;
    default:
        n = mk(ps, N_CHAR); if (n) n->c = c;
        return n;
    }
}
static int parse_int(P *ps, int *v) {
    int s = ps->i, x = 0;
    while (ps->i < ps->len && ps->p[ps->i] >= '0' && ps->p[ps->i] <= '9') { x = x * 10 + (ps->p[ps->i] - '0'); if (x > 1000) x = 1000; ps->i++; }
    *v = x; return ps->i > s;
}
static Node *parse_repeat(P *ps) {
    Node *a = parse_atom(ps);
    if (ps->err) return NULL;
    while (ps->i < ps->len) {
        rechar c = ps->p[ps->i];
        int mn, mx;
        if (c == '*') { mn = 0; mx = -1; ps->i++; }
        else if (c == '+') { mn = 1; mx = -1; ps->i++; }
        else if (c == '?') { mn = 0; mx = 1; ps->i++; }
        else if (c == '{') {
            int save = ps->i; ps->i++;
            if (!parse_int(ps, &mn)) { ps->i = save; break; }   /* literal '{' */
            mx = mn;
            if (ps->i < ps->len && ps->p[ps->i] == ',') { ps->i++; if (!parse_int(ps, &mx)) mx = -1; }
            if (ps->i >= ps->len || ps->p[ps->i] != '}' || (mx >= 0 && mx < mn)) { ps->i = save; break; }
            ps->i++;
        } else break;
        if (a->t == N_BOL || a->t == N_EOL || a->t == N_WB || a->t == N_NWB) { ps->err = 1; return NULL; }
        Node *r = mk(ps, N_REP); if (!r) return NULL;
        r->a = a; r->min = mn; r->max = mx; r->greedy = 1;
        if (ps->i < ps->len && ps->p[ps->i] == '?') { r->greedy = 0; ps->i++; }
        a = r;
    }
    if (ps->i < ps->len && a->t == N_CHAR && ps->p[ps->i] == '{') { /* literal brace handled as next atom */ }
    return a;
}
static Node *parse_cat(P *ps) {
    Node *cat = mk(ps, N_CAT);
    while (!ps->err && ps->i < ps->len && ps->p[ps->i] != '|' && ps->p[ps->i] != ')') {
        if (ps->p[ps->i] == '{') {   /* '{' that is not a quantifier: literal */
            Node *n = mk(ps, N_CHAR); if (!n) break; n->c = '{'; ps->i++;
            addkid(cat, n); continue;
        }
        Node *r = parse_repeat(ps);
        if (r) addkid(cat, r);
    }
    return cat;
}
static Node *parse_alt(P *ps) {
    Node *l = parse_cat(ps);
    while (!ps->err && ps->i < ps->len && ps->p[ps->i] == '|') {
        ps->i++;
        Node *r = parse_cat(ps);
        Node *a = mk(ps, N_ALT); if (!a) return NULL;
        a->a = l; a->b = r; l = a;
    }
    return l;
}

/* ---------- code generation ---------- */
static int emit(Regex *re, int op, int x, int y) {
    if (re->np == re->capp) { re->capp = re->capp ? re->capp * 2 : 64; re->prog = realloc(re->prog, (size_t)re->capp * sizeof(Inst)); }
    re->prog[re->np].op = op; re->prog[re->np].x = x; re->prog[re->np].y = y;
    return re->np++;
}
static void gen(Regex *re, Node *n, int *err) {
    if (*err) return;
    if (re->np > 200000) { *err = 1; return; }
    switch (n->t) {
    case N_CHAR: emit(re, I_CHAR, re->icase ? fold((rechar)n->c) : n->c, 0); break;
    case N_ANY: emit(re, I_ANY, 0, 0); break;
    case N_CLASS: emit(re, I_CLASS, n->c, 0); break;
    case N_BOL: emit(re, I_BOL, 0, 0); break;
    case N_EOL: emit(re, I_EOL, 0, 0); break;
    case N_WB: emit(re, I_WORDB, 0, 0); break;
    case N_NWB: emit(re, I_NWORDB, 0, 0); break;
    case N_EMPTY: break;
    case N_CAT: for (int i = 0; i < n->nk; i++) gen(re, n->kids[i], err); break;
    case N_GROUP:
        emit(re, I_SAVE, 2 * n->idx, 0); gen(re, n->a, err); emit(re, I_SAVE, 2 * n->idx + 1, 0);
        break;
    case N_ALT: {
        int sp = emit(re, I_SPLIT, 0, 0);
        re->prog[sp].x = re->np; gen(re, n->a, err);
        int j = emit(re, I_JMP, 0, 0);
        re->prog[sp].y = re->np; gen(re, n->b, err);
        re->prog[j].x = re->np;
        break;
    }
    case N_REP: {
        for (int i = 0; i < n->min; i++) gen(re, n->a, err);
        if (n->max < 0) {
            int sp = emit(re, I_SPLIT, 0, 0);
            int body = re->np; gen(re, n->a, err);
            emit(re, I_JMP, sp, 0);
            if (n->greedy) { re->prog[sp].x = body; re->prog[sp].y = re->np; }
            else { re->prog[sp].x = re->np; re->prog[sp].y = body; }
        } else {
            int k = n->max - n->min, *fix = malloc(sizeof(int) * (size_t)(k + 1)), nf = 0;
            for (int i = 0; i < k; i++) {
                int sp = emit(re, I_SPLIT, 0, 0);
                fix[nf++] = sp;
                int body = re->np; gen(re, n->a, err);
                if (n->greedy) re->prog[sp].x = body; else re->prog[sp].y = body;
            }
            for (int i = 0; i < nf; i++) { if (n->greedy) re->prog[fix[i]].y = re->np; else re->prog[fix[i]].x = re->np; }
            free(fix);
        }
        break;
    }
    }
}

Regex *re_compile(const rechar *pat, int len, int flags, int *errpos) {
    Regex *re = calloc(1, sizeof(Regex));
    if (!re) return NULL;
    re->icase = (flags & RE_ICASE) != 0;
    P ps; memset(&ps, 0, sizeof ps);
    ps.p = pat; ps.len = len; ps.re = re;
    Node *root;
    if (flags & RE_LITERAL) {
        root = mk(&ps, N_CAT);
        for (int i = 0; i < len && root; i++) { Node *c = mk(&ps, N_CHAR); if (!c) break; c->c = pat[i]; addkid(root, c); }
    } else {
        root = parse_alt(&ps);
        if (!ps.err && ps.i < ps.len) ps.err = 1;   /* stray ')' */
    }
    int err = ps.err;
    if (!err) {
        emit(re, I_SAVE, 0, 0);
        gen(re, root, &err);
        emit(re, I_SAVE, 1, 0);
        emit(re, I_MATCH, 0, 0);
    }
    for (int i = 0; i < ps.nall; i++) { free(ps.all[i]->kids); free(ps.all[i]); }
    free(ps.all);
    if (err) { if (errpos) *errpos = ps.i; re_free(re); return NULL; }
    re->firstch = (re->np > 1 && re->prog[1].op == I_CHAR) ? re->prog[1].x : -1;   /* folded when icase */
    return re;
}
void re_free(Regex *re) {
    if (!re) return;
    for (int i = 0; i < re->ncls; i++) { free(re->cls[i].lo); free(re->cls[i].hi); }
    free(re->cls); free(re->prog); free(re->vis); free(re->stk); free(re);
}

/* ---------- matcher ---------- */
static int push(Regex *re, size_t *sp, int a, int b) {
    if (*sp + 2 > re->stkcap) {
        size_t nc = re->stkcap ? re->stkcap * 2 : 1024;
        int *ns = realloc(re->stk, nc * sizeof(int)); if (!ns) return 0;
        re->stk = ns; re->stkcap = nc;
    }
    re->stk[(*sp)++] = a; re->stk[(*sp)++] = b;
    return 1;
}
static int try_at(Regex *re, const rechar *t, int len, int start, int *caps, int usevis) {
    size_t sp = 0;
    if (!push(re, &sp, 0, start)) return 0;
    long budget = 20000000;   /* safety net when no memo table */
    while (sp) {
        int pos = re->stk[--sp], pc = re->stk[--sp];
        if (pc < 0) { caps[-pc - 1] = pos; continue; }   /* capture restore */
        for (;;) {
            if (--budget < 0) return 0;
            if (usevis) {
                size_t bit = (size_t)pc * (size_t)(len + 1) + (size_t)pos;
                if (re->vis[bit >> 3] & (1u << (bit & 7))) break;
                re->vis[bit >> 3] |= (unsigned char)(1u << (bit & 7));
            }
            const Inst *in = &re->prog[pc];
            if (in->op == I_CHAR) {
                if (pos < len && (re->icase ? fold(t[pos]) : t[pos]) == in->x) { pc++; pos++; continue; }
                break;
            } else if (in->op == I_ANY) {
                if (pos >= len || t[pos] == '\n') break;
                pos += (t[pos] >= 0xD800 && t[pos] <= 0xDBFF && pos + 1 < len && t[pos + 1] >= 0xDC00 && t[pos + 1] <= 0xDFFF) ? 2 : 1;
                pc++; continue;
            } else if (in->op == I_CLASS) {
                if (pos < len && clsmatch(re, &re->cls[in->x], t[pos])) { pc++; pos++; continue; }
                break;
            } else if (in->op == I_SPLIT) {
                if (!push(re, &sp, in->y, pos)) return 0;
                pc = in->x; continue;
            } else if (in->op == I_JMP) { pc = in->x; continue; }
            else if (in->op == I_SAVE) {
                if (!push(re, &sp, -(in->x + 1), caps[in->x])) return 0;
                caps[in->x] = pos; pc++; continue;
            } else if (in->op == I_BOL) { if (pos == 0) { pc++; continue; } break; }
            else if (in->op == I_EOL) { if (pos == len) { pc++; continue; } break; }
            else if (in->op == I_WORDB || in->op == I_NWORDB) {
                int a = pos > 0 && isword(t[pos - 1]), b = pos < len && isword(t[pos]);
                if ((a != b) == (in->op == I_WORDB)) { pc++; continue; }
                break;
            } else if (in->op == I_MATCH) return 1;
            break;
        }
    }
    return 0;
}
int re_search(Regex *re, const rechar *text, int len, int start, int *caps) {
    if (!re || start > len) return 0;
    int usevis = -1;                        /* memo table: prepared at the first real attempt */
    for (int s = start; s <= len; s++) {
        if (re->firstch >= 0) {             /* skip to the next possible first character */
            if (re->icase) while (s < len && fold(text[s]) != re->firstch) s++;
            else while (s < len && text[s] != re->firstch) s++;
            if (s >= len) return 0;
        }
        if (usevis < 0) {
            size_t bits = (size_t)re->np * (size_t)(len + 1);
            usevis = bits <= (size_t)256 * 1024 * 1024;     /* <= 32 MB table */
            if (usevis) {
                size_t bytes = (bits + 7) / 8;
                if (bytes > re->viscap) { unsigned char *v = realloc(re->vis, bytes); if (!v) usevis = 0; else { re->vis = v; re->viscap = bytes; } }
                if (usevis) memset(re->vis, 0, bytes);
            }
        }
        for (int i = 0; i < 2 * RE_NCAP; i++) caps[i] = -1;
        if (try_at(re, text, len, s, caps, usevis)) return 1;
        /* do not start inside a surrogate pair */
        if (s + 1 < len && text[s] >= 0xD800 && text[s] <= 0xDBFF && text[s + 1] >= 0xDC00 && text[s + 1] <= 0xDFFF) s++;
    }
    return 0;
}
int re_expand(const rechar *r, int rl, const rechar *t, const int *caps, rechar *out, int oc) {
    int n = 0;
#define PUT(ch) do { if (out && n < oc) out[n] = (ch); n++; } while (0)
    for (int i = 0; i < rl; i++) {
        rechar c = r[i];
        int g = -1;
        if (c == '$' && i + 1 < rl) {
            rechar d = r[i + 1];
            if (d >= '0' && d <= '9') { g = d - '0'; i++; }
            else if (d == '&') { g = 0; i++; }
            else if (d == '$') { PUT('$'); i++; continue; }
        } else if (c == '\\' && i + 1 < rl) {
            rechar d = r[i + 1]; i++;
            if (d >= '0' && d <= '9') g = d - '0';
            else if (d == 'n') { PUT('\n'); continue; }
            else if (d == 't') { PUT('\t'); continue; }
            else { PUT(d); continue; }
        }
        if (g >= 0) {
            if (caps[2 * g] >= 0 && caps[2 * g + 1] >= caps[2 * g])
                for (int k = caps[2 * g]; k < caps[2 * g + 1]; k++) PUT(t[k]);
            continue;
        }
        PUT(c);
    }
#undef PUT
    return n;
}

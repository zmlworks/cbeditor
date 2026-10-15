/*
 * CEditor 1.3 - custom-drawn Win32 text editor with EDIT-compatible inline Japanese IME,
 * custom title bar, find/replace (own regex engine), word wrap, large files, Markdown view.
 * Plain C / Win32 / GDI / IMM32 / DWM. No EDIT/RichEdit for the document itself.
 */
#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0A00
#endif
#define WINVER 0x0A00
#include <windows.h>
#include <windowsx.h>
#include <imm.h>
#include <commdlg.h>
#include <shellapi.h>
#include <dwmapi.h>
#include <uxtheme.h>
#include <commctrl.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <stdio.h>
#include <stdarg.h>
#include <limits.h>
#include <psapi.h>
#include "regex.h"

#define APPNAME   L"CEditor"
#define APPVER    L"1.3.0"
#define CLS_FRAME L"CEditorFrame"
#define CLS_TEXT  L"CEditorText"
#define CLS_FIND  L"CEditorFind"

/* colours (spec) */
#define C_FRAME     RGB(0x3D, 0x01, 0x05)
#define C_FRAME_MD  RGB(0x7B, 0x5E, 0x86)
#define C_BG        RGB(0x00, 0x22, 0x18)
#define C_TEXT      RGB(0xC6, 0xCF, 0xC6)
#define C_SEL       RGB(0x2A, 0x5B, 0x7E)
#define C_SEL_NF    RGB(0x1E, 0x40, 0x48)
#define C_MATCH     RGB(0x4E, 0x46, 0x16)
#define C_CURMATCH  RGB(0x9A, 0x62, 0x12)
#define C_WS        RGB(0x1E, 0x4A, 0x3F)
#define C_DOT       RGB(0x00, 0xA2, 0xE8)
#define C_CAPTEXT   RGB(0xEE, 0xE0, 0xE0)
#define C_CAPTEXT_I RGB(0xA8, 0x90, 0x90)
#define C_INPUT_BG  RGB(0x00, 0x22, 0x18)
#define C_INPUT_TX  RGB(0xC0, 0x5E, 0x40)
#define C_QUOTE     RGB(0x8B, 0x91, 0x8B)
#define C_LINK      RGB(0x6E, 0x9E, 0xB2)
#define C_CODEBG    RGB(0x0B, 0x33, 0x27)
#define C_GRID      RGB(0x2E, 0x5A, 0x4E)
#define C_THEAD     RGB(0x08, 0x30, 0x24)

#ifndef DWMWA_WINDOW_CORNER_PREFERENCE
#define DWMWA_WINDOW_CORNER_PREFERENCE 33
#endif
#ifndef DWMWA_BORDER_COLOR
#define DWMWA_BORDER_COLOR 34
#endif
#ifndef DWMWA_CAPTION_COLOR
#define DWMWA_CAPTION_COLOR 35
#endif
#ifndef DWMWA_USE_IMMERSIVE_DARK_MODE
#define DWMWA_USE_IMMERSIVE_DARK_MODE 20
#endif
#define CED_DWMWCP_ROUND 2

enum { IDM_NEWWIN = 100, IDM_OPEN, IDM_SAVE, IDM_SAVEAS, IDM_SAVEINC, IDM_EXIT,
       IDM_UNDO = 200, IDM_REDO, IDM_CUT, IDM_COPY, IDM_PASTE, IDM_DELETE, IDM_SELALL,
       IDM_RECONV, IDM_FIND, IDM_REPLACE, IDM_FINDNEXT, IDM_FINDPREV,
       IDM_WRAP = 250, IDM_WS, IDM_MD,
       IDM_FONT0 = 300,
       IDM_ZOOMIN = 400, IDM_ZOOMOUT, IDM_ZOOMRESET, IDM_ABOUT };

static const WCHAR *const kFonts[] = { L"MS Gothic", L"BIZ UDGothic", L"Meiryo", L"Yu Gothic UI", L"Consolas" };
static const WCHAR *const kFontLabels[] = { L"MS ゴシック (等幅)", L"BIZ UDゴシック (等幅)", L"メイリオ", L"Yu Gothic UI", L"Consolas" };
#define NFONTS ((int)(sizeof(kFonts) / sizeof(kFonts[0])))

static void NoMem(void) { MessageBoxW(NULL, L"メモリ不足です。", APPNAME, MB_ICONERROR); ExitProcess(1); }
static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) NoMem();
    return q;
}
static void *xmalloc(size_t n) { return xrealloc(NULL, n); }
#define IS_HI(c) ((c) >= 0xD800 && (c) <= 0xDBFF)
#define IS_LO(c) ((c) >= 0xDC00 && (c) <= 0xDFFF)

/* ================================================================== */
/* text storage: piece table (UTF-16) + incremental line index         */
/* ================================================================== */
/* The loaded text (g_org) is never modified. Inserted text is appended to add blocks (append-only,
   never moved), and the document is the concatenation of the pieces in g_pc. Deleting only edits the
   piece list. Typing extends the last piece in place, so it does not create new pieces.
   In idle time, runs of small pieces are copied into line-aligned contiguous chunks (a very long line
   is stored as several chunks), so that nearly every line is one contiguous range that search and save
   read in place. Afterwards memory that no piece refers to any more is given back (see Compaction). */
typedef struct { const WCHAR *p; size_t pos, len; } Piece;   /* pos = document offset of the piece */
static WCHAR *g_org; static size_t g_orgCap;   /* original text (immutable, VirtualAlloc'ed, g_orgCap + 1 units) */
typedef struct { WCHAR *p; size_t cap; } Block;
static Block *g_blk; static size_t g_nblk;  /* all add blocks */
static WCHAR *g_add; static size_t g_addN, g_addCap;   /* current add block */
static Piece *g_pc; static size_t g_npc, g_pccap, g_pcHint;
static size_t g_len;
#define PIECES_COMPACT 50000                /* piece count that makes an edit run compaction at once */
static size_t g_cpk, g_syncAt = PIECES_COMPACT; /* compaction cursor (piece index) */
static BOOL g_cdone = TRUE, g_cclean, g_gcDue;  /* compaction finished / no work in this pass / release due */
static size_t *g_ls; static size_t g_nl, g_lscap;
/* lazy shift: entries with index >= g_dIdx must be adjusted by g_delta (typing = O(1)) */
static size_t g_dIdx = (size_t)-1; static ptrdiff_t g_delta;
static unsigned g_docVer = 1;

/* original-text buffer: committed on demand, so untouched pages cost no RAM; parts can be released */
static WCHAR *OrgAlloc(size_t n) { return VirtualAlloc(NULL, (n + 1) * sizeof(WCHAR), MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE); }
static void OrgFree(WCHAR *p) { if (p) VirtualFree(p, 0, MEM_RELEASE); }
static void Decommit(const WCHAR *a, const WCHAR *b) {   /* gives the whole pages inside [a, b) back */
    uintptr_t s = ((uintptr_t)a + 4095) & ~(uintptr_t)4095, e = (uintptr_t)b & ~(uintptr_t)4095;
    if (e > s) VirtualFree((void *)s, e - s, MEM_DECOMMIT);
}
static size_t DocLen(void) { return g_len; }
static size_t PieceAt(size_t i) {           /* piece containing offset i (< g_len); sequential access is O(1) */
    size_t k = g_pcHint;
    if (k < g_npc && i - g_pc[k].pos < g_pc[k].len) return k;
    if (++k < g_npc && i - g_pc[k].pos < g_pc[k].len) return g_pcHint = k;
    size_t lo = 0, hi = g_npc - 1;
    while (lo < hi) { size_t m = (lo + hi + 1) / 2; if (g_pc[m].pos <= i) lo = m; else hi = m - 1; }
    return g_pcHint = lo;
}
static WCHAR DocAt(size_t i) { if (i >= g_len) return 0; const Piece *c = &g_pc[PieceAt(i)]; return c->p[i - c->pos]; }
static void DocGet(size_t p, size_t n, WCHAR *d) {
    for (size_t k = n ? PieceAt(p) : 0; n; k++) {
        size_t o = p - g_pc[k].pos, a = g_pc[k].len - o; if (a > n) a = n;
        memcpy(d, g_pc[k].p + o, a * sizeof(WCHAR)); d += a; p += a; n -= a;
    }
}
/* [p, p + n) in place if it lies inside one piece, else NULL */
static const WCHAR *DocPtr(size_t p, size_t n) {
    if (!n || p >= g_len) return NULL;
    const Piece *c = &g_pc[PieceAt(p)];
    return p + n <= c->pos + c->len ? c->p + (p - c->pos) : NULL;
}
static void PcInsert(size_t k, Piece pc) {
    if (g_npc == g_pccap) { g_pccap = g_pccap * 2 + 16; g_pc = xrealloc(g_pc, g_pccap * sizeof(Piece)); }
    memmove(g_pc + k + 1, g_pc + k, (g_npc - k) * sizeof(Piece));
    g_pc[k] = pc; g_npc++;
}
static void PcShift(size_t k, ptrdiff_t d) { for (; k < g_npc; k++) g_pc[k].pos += (size_t)d; }
static size_t SplitAt(size_t p) {           /* makes p a piece boundary; returns the index of the piece starting at p */
    if (p >= g_len) return g_npc;
    size_t k = PieceAt(p); Piece *c = &g_pc[k];
    if (c->pos == p) return k;
    Piece r = { c->p + (p - c->pos), p, c->len - (p - c->pos) };
    c->len = p - c->pos;
    PcInsert(k + 1, r);
    return k + 1;
}
static WCHAR *AddAlloc(size_t n) {
    if (g_addCap - g_addN < n) {
        g_addCap = n > (1u << 20) ? n : (1u << 20); g_addN = 0;
        g_add = xmalloc(g_addCap * sizeof(WCHAR));
        g_blk = xrealloc(g_blk, (g_nblk + 1) * sizeof *g_blk); g_blk[g_nblk].p = g_add; g_blk[g_nblk++].cap = g_addCap;
    }
    WCHAR *d = g_add + g_addN; g_addN += n;
    return d;
}
static void PtInsert(size_t p, const WCHAR *s, size_t n) {
    WCHAR *t = AddAlloc(n); memcpy(t, s, n * sizeof(WCHAR));
    size_t k = SplitAt(p);
    if (k > 0 && t > g_add && g_pc[k - 1].p + g_pc[k - 1].len == t) g_pc[k - 1].len += n;   /* typing */
    else { Piece pc = { t, p, n }; PcInsert(k++, pc); }
    PcShift(k, (ptrdiff_t)n); g_len += n;
    g_cdone = g_cclean = FALSE;
}
static void PtDelete(size_t p, size_t n) {
    size_t a = SplitAt(p), b = SplitAt(p + n);
    memmove(g_pc + a, g_pc + b, (g_npc - b) * sizeof(Piece)); g_npc -= b - a;
    PcShift(a, -(ptrdiff_t)n); g_len -= n;
    g_cdone = g_cclean = FALSE;
}
/* t (n units, from OrgAlloc(cap)) becomes the whole document as one piece; old buffers are freed */
static void PtAdopt(WCHAR *t, size_t n, size_t cap) {
    if (g_org != t) OrgFree(g_org);
    for (size_t i = 0; i < g_nblk; i++) free(g_blk[i].p);
    free(g_blk); g_blk = NULL; g_nblk = 0; g_add = NULL; g_addN = g_addCap = 0;
    g_org = t; g_orgCap = cap; g_len = n; g_npc = 0; g_pcHint = 0;
    g_cpk = 0; g_cdone = TRUE; g_gcDue = FALSE; g_syncAt = PIECES_COMPACT;
    if (n) { Piece pc = { t, 0, n }; PcInsert(0, pc); }
}

/* ---- per-line metadata (kept parallel to the line index) ---- */
#define CK 128                              /* checkpoint spacing (units) */
typedef struct { int i, x; } Mark;
typedef struct {                            /* measurement progress of one display line */
    unsigned id;                            /* changes whenever the content below is invalidated */
    int mi, mx;                             /* measured prefix [0, mi) (cluster boundary), x at mi */
    Mark *ck; int nck, cck;                 /* checkpoints (i, x): ck[0] = {0, 0}, then about every CK units */
    int *rows; int nr, cr, rw;              /* wrap row starts found so far (rows[0] = 0) for wrap width rw */
    BOOL rdone;                             /* all rows found */
} LineInfo;
typedef struct { unsigned li; int rows; } LineMeta;   /* li: index into g_info (0 = none); rows: wrapped rows, 0 = not known */
static LineMeta *g_lm;
static LineInfo **g_info; static unsigned *g_ifree; static size_t g_infoCap, g_infoTop, g_nifree;   /* pool */
#define LI(L) (g_lm[L].li ? g_info[g_lm[L].li] : NULL)
static unsigned g_infoSeq; static size_t g_ninfo;
static long long g_rowsSum;                 /* wrap: sum over lines of (rows known ? rows : 1) */
static int g_rowsW = -1;                    /* wrap width the known row counts belong to */
static size_t g_bgL;                        /* idle row counting: lines below this are known */
static size_t g_tcL; static long long g_tcS; /* cache: rows above line g_tcL */

static void InfoReset(LineInfo *li) {
    li->id = ++g_infoSeq; li->mi = li->mx = 0; li->nr = 0; li->rw = -1; li->rdone = FALSE;
    if (!li->cck) { li->cck = 16; li->ck = xmalloc(16 * sizeof(Mark)); }
    li->ck[0].i = li->ck[0].x = 0; li->nck = 1;
}
static unsigned InfoNew(void) {
    unsigned i;
    if (g_nifree) i = g_ifree[--g_nifree];
    else {
        if (g_infoTop + 1 >= g_infoCap) {
            g_infoCap = g_infoCap * 2 + 64;
            g_info = xrealloc(g_info, g_infoCap * sizeof *g_info); g_ifree = xrealloc(g_ifree, g_infoCap * sizeof *g_ifree);
        }
        i = (unsigned)++g_infoTop;
    }
    LineInfo *li = calloc(1, sizeof(LineInfo)); if (!li) NoMem();
    InfoReset(li); g_info[i] = li; g_ninfo++;
    return i;
}
static void InfoFree(size_t L) {
    LineInfo *li = LI(L);
    if (li) { free(li->ck); free(li->rows); free(li); g_ifree[g_nifree++] = g_lm[L].li; g_lm[L].li = 0; g_ninfo--; }
}
static int RowsK(size_t L) { return g_lm[L].rows ? g_lm[L].rows : 1; }
static void SetRowCount(size_t L, int n) {
    int d = (n ? n : 1) - RowsK(L);
    g_rowsSum += d; if (L < g_tcL) g_tcS += d;
    g_lm[L].rows = n;
    if (!n && g_bgL > L) g_bgL = L;
}
/* text of line L changed from offset off on: keep what was measured safely before it */
static void LineEdited(size_t L, size_t off) {
    SetRowCount(L, 0);
    LineInfo *li = LI(L);
    if (!li) return;
    int keep = off > 64 ? (int)off - 64 : 0;  /* clusters and break rules look a little around a position */
    li->id = ++g_infoSeq;
    while (li->nck > 1 && li->ck[li->nck - 1].i > keep) li->nck--;
    li->mi = li->ck[li->nck - 1].i; li->mx = li->ck[li->nck - 1].x;
    /* rows[m] is still valid if rows[m + 1] <= keep (the scan that found rows[m] ended before rows[m + 1]) */
    int j = 0; while (j + 1 < li->nr && li->rows[j + 1] <= keep) j++;
    if (li->nr) li->nr = j > 1 ? j : 1;
    li->rdone = FALSE;
}

static size_t LS(size_t j) { return j >= g_dIdx ? (size_t)((ptrdiff_t)g_ls[j] + g_delta) : g_ls[j]; }
/* entries from 'from' on move by d: only the entries between the old and the new lazy start are touched */
static void ShiftFrom(size_t from, ptrdiff_t d) {
    if (from >= g_nl || d == 0) return;
    if (g_dIdx == (size_t)-1) { g_dIdx = from; g_delta = d; return; }
    if (from < g_dIdx) for (size_t j = from; j < g_dIdx && j < g_nl; j++) g_ls[j] = (size_t)((ptrdiff_t)g_ls[j] - g_delta);
    else for (size_t j = g_dIdx; j < from; j++) g_ls[j] = (size_t)((ptrdiff_t)g_ls[j] + g_delta);
    g_dIdx = from; g_delta += d;
}
static void ExactBelow(size_t j0) {         /* entries below j0 hold exact values (lazy range starts at j0 or later) */
    if (g_dIdx == (size_t)-1 || g_dIdx >= j0) return;
    for (size_t j = g_dIdx; j < j0 && j < g_nl; j++) g_ls[j] = (size_t)((ptrdiff_t)g_ls[j] + g_delta);
    g_dIdx = j0;
}
static void LsReserve(size_t n) {
    if (n <= g_lscap) return;
    g_lscap = n + n / 2 + 64;
    g_ls = xrealloc(g_ls, g_lscap * sizeof(size_t));
    g_lm = xrealloc(g_lm, g_lscap * sizeof(LineMeta));
}
static void RebuildLines(void) {  /* full scan; used only on load */
    for (size_t L = 0; L < g_nl; L++) InfoFree(L);
    g_dIdx = (size_t)-1; g_delta = 0;
    g_nl = 0; LsReserve(64);
    g_ls[g_nl++] = 0;
    for (size_t k = 0; k < g_npc; k++) {
        const WCHAR *b = g_pc[k].p, *p = b, *e = b + g_pc[k].len;
        while (p < e) {
            const WCHAR *q = wmemchr(p, L'\n', (size_t)(e - p));
            if (!q) break;
            if (g_nl == g_lscap) LsReserve(g_lscap * 2);
            g_ls[g_nl++] = g_pc[k].pos + (size_t)(q - b) + 1;
            p = q + 1;
        }
    }
    memset(g_lm, 0, g_nl * sizeof(LineMeta));
    g_rowsSum = (long long)g_nl; g_bgL = 0; g_tcL = 0; g_tcS = 0;
}
static size_t LineOf(size_t pos) {
    size_t lo = 0, hi = g_nl - 1;
    while (lo < hi) { size_t m = (lo + hi + 1) / 2; if (LS(m) <= pos) lo = m; else hi = m - 1; }
    return lo;
}
static size_t LineStart(size_t L) { return LS(L); }
static size_t LineEnd(size_t L) { return L + 1 < g_nl ? LS(L + 1) - 1 : DocLen(); }

static void CompactNow(void);
static void RawInsert(size_t p, const WCHAR *s, size_t n) {
    if (!n) return;
    size_t L = LineOf(p), k = 0;
    for (size_t i = 0; i < n; i++) if (s[i] == L'\n') k++;
    LineEdited(L, p - LineStart(L));
    PtInsert(p, s, n);
    if (k == 0) ShiftFrom(L + 1, (ptrdiff_t)n);
    else {
        ExactBelow(L + 1);
        LsReserve(g_nl + k);
        memmove(g_ls + L + 1 + k, g_ls + L + 1, (g_nl - L - 1) * sizeof(size_t));
        if (g_dIdx != (size_t)-1) g_dIdx += k;
        memmove(g_lm + L + 1 + k, g_lm + L + 1, (g_nl - L - 1) * sizeof(LineMeta));
        memset(g_lm + L + 1, 0, k * sizeof(LineMeta));
        size_t w = L + 1;
        for (size_t i = 0; i < n; i++) if (s[i] == L'\n') g_ls[w++] = p + i + 1;
        g_nl += k; g_rowsSum += (long long)k; g_tcL = 0; g_tcS = 0;
        ShiftFrom(L + 1 + k, (ptrdiff_t)n);
    }
    if (g_npc > g_syncAt) CompactNow();
    g_docVer++;
}
static void RawDelete(size_t p, size_t n) {
    if (!n) return;
    size_t L = LineOf(p), Le = LineOf(p + n);
    LineEdited(L, p - LineStart(L));
    PtDelete(p, n);
    size_t k = Le - L;
    if (k == 0) ShiftFrom(L + 1, -(ptrdiff_t)n);
    else {
        ExactBelow(L + 1);
        for (size_t j = L + 1; j <= Le; j++) { g_rowsSum -= RowsK(j); InfoFree(j); }
        memmove(g_ls + L + 1, g_ls + Le + 1, (g_nl - Le - 1) * sizeof(size_t));
        if (g_dIdx != (size_t)-1) g_dIdx = g_dIdx > Le ? g_dIdx - k : L + 1;
        memmove(g_lm + L + 1, g_lm + Le + 1, (g_nl - Le - 1) * sizeof(LineMeta));
        g_nl -= k;
        ShiftFrom(L + 1, -(ptrdiff_t)n);
        g_tcL = 0; g_tcS = 0;
    }
    if (g_bgL > g_nl) g_bgL = g_nl;
    if (g_npc > g_syncAt) CompactNow();
    g_docVer++;
}
/* ---- compaction (idle time) ----
   Copies runs of small pieces into new contiguous pieces that start and end at line boundaries; inside
   a very long line the pieces are cut into chunks of a few thousand units instead. The text does not
   change, so undo records (positions + text), the line index and the layout caches stay valid. */
#define CHUNK 16384                         /* merged pieces grow up to about this size (units) */
#define SMALL 2048                          /* pieces shorter than this are merged */
static BOOL AtLineStart(size_t p) { return p == 0 || DocAt(p - 1) == L'\n'; }
static BOOL AtLineEnd(size_t e) { return e >= g_len || DocAt(e - 1) == L'\n'; }
static BOOL PieceGood(size_t k) {
    const Piece *c = &g_pc[k];
    if (c->len >= SMALL) return TRUE;
    if (!AtLineStart(c->pos) || !AtLineEnd(c->pos + c->len)) return FALSE;
    return !(k + 1 < g_npc && g_pc[k + 1].len < SMALL && c->len + g_pc[k + 1].len <= CHUNK);
}
static size_t Materialize(size_t a, size_t b) {   /* document [a, b) becomes one new piece; returns its index */
    WCHAR *t = AddAlloc(b - a); DocGet(a, b - a, t);
    size_t i = SplitAt(a), j = SplitAt(b);
    Piece pc = { t, a, b - a };
    memmove(g_pc + i + 1, g_pc + j, (g_npc - j) * sizeof(Piece)); g_npc -= j - i - 1;
    g_pc[i] = pc; g_pcHint = i;
    return i;
}
static size_t CompactAt(size_t k) {         /* piece k is not good: merge it with its surroundings */
    size_t p = g_pc[k].pos, e = p + g_pc[k].len, a = p, b = e;
    if (AtLineStart(p) && AtLineEnd(e)) b = e + g_pc[k + 1].len;          /* two small whole-line pieces */
    else {
        size_t ls = LineStart(LineOf(p)), L2 = LineOf(e - 1), le = L2 + 1 < g_nl ? LineStart(L2 + 1) : g_len;
        if (!AtLineStart(p)) a = p - ls <= CHUNK / 2 ? ls : p - (g_pc[k - 1].len <= 2 * SMALL ? g_pc[k - 1].len : SMALL);
        if (!AtLineEnd(e)) b = le - e <= CHUNK / 2 ? le : e + (g_pc[k + 1].len <= 2 * SMALL ? g_pc[k + 1].len : SMALL);
    }
    return Materialize(a, b);
}
/* gives back add blocks no piece points into, and the pages of the original text no piece uses */
static void ReleaseUnused(void) {
    g_gcDue = FALSE;
    BYTE *live = calloc(g_nblk + 1, 1); if (!live) return;
    uintptr_t o0 = (uintptr_t)g_org, o1 = o0 + (g_orgCap + 1) * sizeof(WCHAR), last = o0;
    BOOL mono = TRUE; size_t j = 0;
    for (size_t k = 0; k < g_npc; k++) {
        uintptr_t p = (uintptr_t)g_pc[k].p;
        if (g_org && p >= o0 && p < o1) { if (p < last) mono = FALSE; last = p + g_pc[k].len * sizeof(WCHAR); continue; }
        for (size_t n = 0; n < g_nblk; n++, j = (j + 1) % g_nblk)
            if (p >= (uintptr_t)g_blk[j].p && p < (uintptr_t)(g_blk[j].p + g_blk[j].cap)) { live[j] = 1; break; }
    }
    size_t w = 0;
    for (size_t i = 0; i < g_nblk; i++) {
        if (live[i] || g_blk[i].p == g_add) g_blk[w++] = g_blk[i]; else free(g_blk[i].p);
    }
    g_nblk = w; free(live);
    if (!g_org || !mono) return;            /* original pieces always stay in text order (they are never moved) */
    const WCHAR *gap = g_org;
    for (size_t k = 0; k < g_npc; k++) {
        const WCHAR *p = g_pc[k].p;
        if ((uintptr_t)p < o0 || (uintptr_t)p >= o1) continue;
        Decommit(gap, p); gap = p + g_pc[k].len;
    }
    Decommit(gap, g_org + g_orgCap + 1);
}
/* about budget units of compaction work; returns TRUE when everything is compact */
static BOOL CompactStep(int budget) {
    while (!g_cdone && budget-- > 0) {
        if (g_cpk >= g_npc) { g_cpk = 0; if (g_cclean) g_cdone = g_gcDue = TRUE; g_cclean = TRUE; continue; }
        if (PieceGood(g_cpk)) { g_cpk++; continue; }
        g_cpk = CompactAt(g_cpk); g_cclean = FALSE; budget -= 8;
    }
    return g_cdone;
}
static void CompactNow(void) {              /* too many pieces: compact everything (memory is released in idle) */
    for (int g = 0; g < 4096 && !CompactStep(1 << 16); g++) {}
    g_syncAt = g_npc * 2 > PIECES_COMPACT ? g_npc * 2 : PIECES_COMPACT;
}
static BOOL LineContiguous(size_t L) { size_t s = LineStart(L), e = LineEnd(L); return e == s || DocPtr(s, e - s) != NULL; }


/* ================================================================== */
/* state                                                               */
/* ================================================================== */
static HINSTANCE g_inst;
static HWND g_frame, g_hwnd, g_find;       /* top-level frame, text view (child), find popup */
static HWND g_lastFocus;
static HFONT g_font; static LOGFONTW g_lf;
static HFONT g_uiFont, g_capFont;
static HDC g_hdcM;                          /* measuring DC with g_font */
static int g_fontIdx = 0, g_fontPt10 = 110;
static UINT g_dpi = 96;
static int g_lineH = 16, g_ascent = 12, g_tabW = 32, g_margin = 4, g_avgW = 8, g_caretW = 2;
static unsigned g_layoutVer = 1;            /* bump on font / wrap width change */
static size_t g_caret, g_anchor;
static BOOL g_aff;                          /* caret at a wrap boundary drawn at end of previous row */
static int g_wantX = -1;
static size_t g_top; static int g_topRow;   /* first visible (line, wrapped row) */
static int g_sx;                            /* horizontal scroll (no-wrap) */
static int g_maxW;
static int g_cw, g_ch;
static BOOL g_focus, g_caretMade;
static BOOL g_modified;
static WCHAR g_path[MAX_PATH * 4];
static int g_enc;                           /* 0 UTF-8 1 UTF-8 BOM 2 Shift_JIS 3 UTF-16LE */
static BOOL g_wrap, g_showWs, g_mdView;
static BOOL g_dragging; static int g_dragMode; /* 0 char 1 word 2 line */
static size_t g_wordA, g_wordB;
static DWORD g_lastDblTime; static POINT g_lastDblPt;
static int g_wheelAcc, g_hwheelAcc;
static int g_lastMouseX, g_lastMouseY;
static int g_selftest; static WCHAR g_stlog[MAX_PATH * 4];
static WCHAR g_demo[32]; static int g_bench; static WCHAR g_benchFile[MAX_PATH * 4];
static WCHAR g_iniPath[MAX_PATH * 4];

/* IME composition state */
static BOOL g_comp;
static WCHAR *g_cstr; static int g_clen;
static BYTE *g_cattr;
static DWORD *g_ccl; static int g_nccl;
static int g_ccur;
static size_t g_cpos;
static unsigned g_compVer = 1;
static size_t g_reconvBase, g_reconvLen; static BOOL g_reconvValid;

/* find state */
static Regex *g_re; static BOOL g_reLiteral; static BOOL g_matchCase; static BOOL g_findOpen, g_findExpanded;
static unsigned g_findVer = 1;
static WCHAR g_findStatus[64];

/* forward declarations */
static void Refresh(BOOL ensure);
static void UpdateTitle(void);
static void UpdateScrollBars(void);
static void ClampScroll(void);
static void EnsureVisible(void);
static void FrameLayout(void);
static void FindShow(BOOL expanded);
static void FindHide(void);
static BOOL FindNext(BOOL forward);
static void MdInvalidate(void);
static void CompleteComposition(void);
static void UpdateImeWindows(void);
static void OnKeyDown(WPARAM vk);
static void SetupFont(void);
static void Invalidate(void);
static int Sc(int v);
static BOOL g_dirty = TRUE;                 /* back buffer must be fully re-rendered */
static BOOL IdleWork(void);

/* ================================================================== */
/* undo / redo                                                         */
/* ================================================================== */
typedef struct { BOOL ins; size_t pos; WCHAR *s; size_t n; int grp; size_t cb, ab, cap; } Op;
typedef struct { Op *v; size_t n, cap; } OpStack;
static OpStack g_undo, g_redo;
static int g_grp = 1;
enum { K_NONE, K_TYPE, K_IME, K_DEL, K_BS, K_OTHER };
static int g_lastKind = K_NONE; static size_t g_lastEnd;

static void OpPush(OpStack *st, Op o) {
    if (st->n == st->cap) { st->cap = st->cap ? st->cap * 2 : 64; st->v = xrealloc(st->v, st->cap * sizeof(Op)); }
    st->v[st->n++] = o;
}
static void OpClear(OpStack *st) { for (size_t i = 0; i < st->n; i++) free(st->v[i].s); st->n = 0; }
static void NewGroup(void) { g_grp++; }
static void BreakUndoMerge(void) { g_lastKind = K_NONE; }
/* the last undo record of the current group, if it can take n more units */
static Op *OpTail(BOOL ins, size_t n) {
    Op *t = g_undo.n ? &g_undo.v[g_undo.n - 1] : NULL;
    if (!t || t->ins != ins || t->grp != g_grp) return NULL;
    if (t->n + n > t->cap) { t->cap = (t->n + n) * 2; t->s = xrealloc(t->s, t->cap * sizeof(WCHAR)); }
    return t;
}
static void EditInsert(size_t p, const WCHAR *s, size_t n) {
    if (!n) return;
    Op *t = g_undo.n && g_undo.v[g_undo.n - 1].pos + g_undo.v[g_undo.n - 1].n == p ? OpTail(TRUE, n) : NULL;
    if (t) { memcpy(t->s + t->n, s, n * sizeof(WCHAR)); t->n += n; }      /* typing: "ab" at p == "a" at p, "b" at p+1 */
    else {
        Op o = { TRUE, p, xmalloc(n * sizeof(WCHAR)), n, g_grp, g_caret, g_anchor, n };
        memcpy(o.s, s, n * sizeof(WCHAR));
        OpPush(&g_undo, o);
    }
    OpClear(&g_redo);
    RawInsert(p, s, n);
    g_modified = TRUE;
}
static void EditDelete(size_t p, size_t n) {
    if (!n) return;
    Op *t = NULL;
    if (g_undo.n) { const Op *l = &g_undo.v[g_undo.n - 1]; if (l->pos == p || p + n == l->pos) t = OpTail(FALSE, n); }
    if (t && t->pos == p) { DocGet(p, n, t->s + t->n); t->n += n; }                   /* Delete key */
    else if (t) { memmove(t->s + n, t->s, t->n * sizeof(WCHAR)); DocGet(p, n, t->s); t->n += n; t->pos = p; }   /* Backspace */
    else {
        Op o = { FALSE, p, xmalloc(n * sizeof(WCHAR)), n, g_grp, g_caret, g_anchor, n };
        DocGet(p, n, o.s);
        OpPush(&g_undo, o);
    }
    OpClear(&g_redo);
    RawDelete(p, n);
    g_modified = TRUE;
}

/* ================================================================== */
/* character helpers                                                   */
/* ================================================================== */
static UINT CpAt(size_t p, int *units) {
    size_t len = DocLen(); WCHAR c = DocAt(p);
    if (IS_HI(c) && p + 1 < len && IS_LO(DocAt(p + 1))) {
        *units = 2; return 0x10000 + (((UINT)c - 0xD800) << 10) + ((UINT)DocAt(p + 1) - 0xDC00);
    }
    *units = 1; return c;
}
static BOOL IsExtender(UINT cp) {
    return (cp >= 0xFE00 && cp <= 0xFE0F) || (cp >= 0xE0100 && cp <= 0xE01EF) ||
           cp == 0x3099 || cp == 0x309A || cp == 0x200D || (cp >= 0x0300 && cp <= 0x036F) ||
           (cp >= 0x1F3FB && cp <= 0x1F3FF);
}
static size_t NextPos(size_t p) {
    size_t len = DocLen(); int u;
    if (p >= len) return len;
    if (DocAt(p) == L'\n') return p + 1;
    CpAt(p, &u); p += u;
    while (p < len) {
        UINT c2 = CpAt(p, &u);
        if (!IsExtender(c2)) break;
        p += u;
        if (c2 == 0x200D && p < len && DocAt(p) != L'\n') { CpAt(p, &u); p += u; }
    }
    return p;
}
static size_t PrevPos(size_t p) {
    if (p == 0) return 0;
    size_t L = LineOf(p - 1);
    size_t s = LineStart(L);
    if (s == p) return p - 1;
    if (p - s > 4096) s = p - 64;
    if (s > LineStart(L) && IS_LO(DocAt(s))) s--;
    size_t q = s, prev = s;
    while (q < p) { prev = q; q = NextPos(q); }
    return prev;
}
/* same cluster rule on an in-memory buffer (display line) */
static int BufCp(const WCHAR *b, int n, int i, int *u) {
    if (IS_HI(b[i]) && i + 1 < n && IS_LO(b[i + 1])) { *u = 2; return 0x10000 + ((b[i] - 0xD800) << 10) + (b[i + 1] - 0xDC00); }
    *u = 1; return b[i];
}
static int BufNext(const WCHAR *b, int n, int i) {
    int u;
    if (i >= n) return n;
    BufCp(b, n, i, &u); i += u;
    while (i < n) {
        UINT c2 = (UINT)BufCp(b, n, i, &u);
        if (!IsExtender(c2)) break;
        i += u;
        if (c2 == 0x200D && i < n) { BufCp(b, n, i, &u); i += u; }
    }
    return i;
}
static int CharClass(UINT c) {
    if (c == L'\n') return 9;
    if (c == L' ' || c == L'\t' || c == 0x3000) return 0;
    if ((c >= L'0' && c <= L'9') || (c >= L'A' && c <= L'Z') || (c >= L'a' && c <= L'z') || c == L'_' ||
        (c >= 0xFF10 && c <= 0xFF19) || (c >= 0xFF21 && c <= 0xFF3A) || (c >= 0xFF41 && c <= 0xFF5A) ||
        (c >= 0xC0 && c <= 0x24F && c != 0xD7 && c != 0xF7)) return 1;
    if (c >= 0x3041 && c <= 0x309F) return 2;
    if ((c >= 0x30A0 && c <= 0x30FF) || (c >= 0xFF66 && c <= 0xFF9F) || (c >= 0x31F0 && c <= 0x31FF)) return 3;
    if ((c >= 0x4E00 && c <= 0x9FFF) || (c >= 0x3400 && c <= 0x4DBF) || (c >= 0xF900 && c <= 0xFAFF) ||
        (c >= 0x20000 && c <= 0x3FFFF) || c == 0x3005 || c == 0x3006 || c == 0x303B) return 4;
    if (c >= 0x1F000) return 6;
    if (c < 0x10000 && IsCharAlphaNumericW((WCHAR)c)) return 1;
    return 5;
}
static int ClassAt(size_t p) { int u; return CharClass(CpAt(p, &u)); }
static size_t WordRight(size_t p) {
    size_t len = DocLen();
    if (p >= len) return len;
    int c = ClassAt(p);
    if (c == 9) return p + 1;
    if (c != 0) { while (p < len && ClassAt(p) == c) p = NextPos(p); }
    while (p < len && ClassAt(p) == 0) p = NextPos(p);
    return p;
}
static size_t WordLeft(size_t p) {
    if (p == 0) return 0;
    size_t q = PrevPos(p);
    if (ClassAt(q) == 9) return q;
    while (q > 0 && ClassAt(q) == 0) { size_t r = PrevPos(q); if (ClassAt(r) == 9) return q; q = r; }
    int c = ClassAt(q);
    if (c == 0) return q;
    while (q > 0) { size_t r = PrevPos(q); if (ClassAt(r) != c) break; q = r; }
    return q;
}
static void WordAt(size_t p, size_t *a, size_t *b) {
    size_t len = DocLen();
    if (p >= len || DocAt(p) == L'\n') {
        if (p > 0 && DocAt(p - 1) != L'\n') p = PrevPos(p); else { *a = *b = p; return; }
    }
    int c = ClassAt(p);
    size_t s = p, e = NextPos(p);
    while (s > 0) { size_t r = PrevPos(s); if (ClassAt(r) != c) break; s = r; }
    while (e < len && ClassAt(e) == c) e = NextPos(e);
    *a = s; *b = e;
}

/* ================================================================== */
/* measurement and layout. ONE source of x positions (MeasureRun with  */
/* the width dictionary) used by drawing (as ExtTextOut lpDx), caret,  */
/* hit testing, composition, IME positions, wrapping and extents       */
/* ================================================================== */
/* ---- width dictionary: advance width per character for the current font (font / zoom / DPI) ---- */
static unsigned short *g_wbmp;              /* BMP: 0xFFFF = not measured yet */
typedef struct { UINT cp; int w; } WEnt;
static WEnt *g_wsup; static size_t g_wsupN, g_wsupCap;   /* supplementary planes (open addressing) */
static unsigned g_gdiCalls;                 /* number of GDI measurements (statistics) */
static void DictReset(void) {
    if (!g_wbmp) g_wbmp = xmalloc(65536 * sizeof *g_wbmp);
    memset(g_wbmp, 0xFF, 65536 * sizeof *g_wbmp);
    free(g_wsup); g_wsup = NULL; g_wsupN = g_wsupCap = 0;
}
static int GdiW(const WCHAR *s, int n) { SIZE z = { 0, 0 }; GetTextExtentPoint32W(g_hdcM, s, n, &z); g_gdiCalls++; return z.cx; }
static BOOL ZeroWidthCp(UINT c) {
    return c < 0x20 || IsExtender(c) || (c >= 0x200B && c <= 0x200F) || (c >= 0x2060 && c <= 0x2064) || c == 0xFEFF;
}
static BOOL WideCp(UINT c) {
    return (c >= 0x1100 && c <= 0x115F) || (c >= 0x2E80 && c <= 0xA4CF) || (c >= 0xAC00 && c <= 0xD7A3) ||
           (c >= 0xF900 && c <= 0xFAFF) || (c >= 0xFE30 && c <= 0xFE4F) || (c >= 0xFF00 && c <= 0xFF60) ||
           (c >= 0xFFE0 && c <= 0xFFE6) || (c >= 0x1F300 && c <= 0x1FAFF) || (c >= 0x20000 && c <= 0x3FFFD);
}
/* a visible character that measures 0 (no glyph even through font linking) still gets a cell,
   so the caret and the mouse can reach it; drawing uses the same width */
static int FixW(UINT c, int w) { return (w > 0 || ZeroWidthCp(c)) ? w : (WideCp(c) ? 2 : 1) * g_avgW; }
static int CharW(UINT c) {
    if (c < 0x10000) {
        if (g_wbmp[c] == 0xFFFF) { WCHAR s = (WCHAR)c; int w = FixW(c, GdiW(&s, 1)); g_wbmp[c] = (unsigned short)(w < 0xFFFE ? w : 0xFFFE); }
        return g_wbmp[c];
    }
    if (g_wsupN * 2 >= g_wsupCap) {         /* grow + rehash */
        WEnt *o = g_wsup; size_t oc = g_wsupCap;
        g_wsupCap = oc ? oc * 2 : 256; g_wsup = calloc(g_wsupCap, sizeof(WEnt)); if (!g_wsup) NoMem();
        for (size_t i = 0; i < oc; i++) if (o[i].cp) {
            size_t h = (o[i].cp * 2654435761u) & (g_wsupCap - 1);
            while (g_wsup[h].cp) h = (h + 1) & (g_wsupCap - 1);
            g_wsup[h] = o[i];
        }
        free(o);
    }
    size_t h = (c * 2654435761u) & (g_wsupCap - 1);
    while (g_wsup[h].cp && g_wsup[h].cp != c) h = (h + 1) & (g_wsupCap - 1);
    if (!g_wsup[h].cp) {
        WCHAR s[2] = { (WCHAR)(0xD800 + ((c - 0x10000) >> 10)), (WCHAR)(0xDC00 + ((c - 0x10000) & 0x3FF)) };
        g_wsup[h].cp = c; g_wsup[h].w = FixW(c, GdiW(s, 2)); g_wsupN++;
    }
    return g_wsup[h].w;
}
/* width of the cluster t[i, j): one character from the dictionary; a cluster with combining marks,
   variation selectors or ZWJ is measured as a whole (rare) */
static int ClusterW(const WCHAR *t, int i, int j) {
    int u; UINT c = (UINT)BufCp(t, j, i, &u);
    return i + u >= j ? CharW(c) : FixW(c, GdiW(t + i, j - i));
}
/* x positions of t[0, m) starting at line x: xs[k] = x before unit k (units inside a cluster get the
   x after it, so xs[k + 1] - xs[k] is the ExtTextOut lpDx). Stops at the first cluster boundary >= lim,
   or before a cluster that may continue past the buffer (!atEnd). ck: record checkpoints (base = index of t[0]). */
static int MeasureRun(const WCHAR *t, int m, BOOL atEnd, int lim, int x, int *xs, LineInfo *ck, int base) {
    int i = 0;
    while (i < lim && i < m) {
        if (ck && base + i >= ck->ck[ck->nck - 1].i + CK) {
            if (ck->nck == ck->cck) { ck->cck *= 2; ck->ck = xrealloc(ck->ck, (size_t)ck->cck * sizeof(Mark)); }
            ck->ck[ck->nck].i = base + i; ck->ck[ck->nck++].x = x;
        }
        if (t[i] == L'\t') { xs[i++] = x; x = (x / g_tabW + 1) * g_tabW; continue; }
        int j = BufNext(t, m, i);
        if (j >= m && !atEnd) break;
        xs[i] = x; x += ClusterW(t, i, j);
        for (int k = i + 1; k < j; k++) xs[k] = x;
        i = j;
    }
    xs[i] = x;
    return i;
}

/* ---- a display line: document line L with the composition string inserted at co ---- */
typedef struct { size_t L; int co, n; LineInfo *li; } Ln;
static LineInfo g_ci; static size_t g_ciL = (size_t)-1; static unsigned g_ciDV, g_ciCV;   /* composition line */
static Ln LnOf(size_t L, BOOL withComp) {
    Ln ln; size_t s = LineStart(L);
    ln.L = L; ln.co = -1; ln.n = (int)(LineEnd(L) - s);
    if (withComp && g_comp && g_clen > 0 && LineOf(g_cpos) == L) {
        ln.co = (int)(g_cpos - s); ln.n += g_clen; ln.li = &g_ci;
        if (g_ciL != L || g_ciDV != g_docVer || g_ciCV != g_compVer) { InfoReset(&g_ci); g_ciL = L; g_ciDV = g_docVer; g_ciCV = g_compVer; }
    } else {
        if (!g_lm[L].li) g_lm[L].li = InfoNew();
        ln.li = g_info[g_lm[L].li];
    }
    return ln;
}
static void LnGet(const Ln *ln, int a, int n, WCHAR *d) {
    size_t s = LineStart(ln->L);
    if (ln->co >= 0 && a < ln->co + g_clen) {
        if (a < ln->co) { int k = n < ln->co - a ? n : ln->co - a; DocGet(s + (size_t)a, (size_t)k, d); d += k; a += k; n -= k; }
        int k = n < ln->co + g_clen - a ? n : ln->co + g_clen - a;
        if (k > 0) { memcpy(d, g_cstr + (a - ln->co), (size_t)k * sizeof(WCHAR)); d += k; a += k; n -= k; }
    }
    if (n > 0) DocGet(s + (size_t)a - (size_t)(ln->co >= 0 ? g_clen : 0), (size_t)n, d);
}
/* text + positions buffers: g_scr is scratch, g_win holds the window the caller is drawing / hit testing */
typedef struct { WCHAR *t; int *x; int cap; } TBuf;
static TBuf g_scr, g_win;
static unsigned g_winId; static int g_lo, g_hi;          /* g_win covers display units [g_lo, g_hi] */
#define LB(i) g_win.t[(i) - g_lo]
#define LX(i) g_win.x[(i) - g_lo]
/* measures ln from unit a (a cluster boundary at line x) up to the first boundary >= lim into b
   (b->t[k - a], b->x[k - a]); returns that boundary */
static int ScanFrom(TBuf *b, const Ln *ln, int a, int x, int lim, LineInfo *ck) {
    for (int pad = 32;; pad *= 8) {
        int m = lim - a + pad; if (m > ln->n - a) m = ln->n - a;
        if (m + 2 > b->cap) { b->cap = m + 1024; b->t = xrealloc(b->t, (size_t)b->cap * sizeof(WCHAR)); b->x = xrealloc(b->x, (size_t)b->cap * sizeof(int)); }
        LnGet(ln, a, m, b->t);
        int r = MeasureRun(b->t, m, a + m == ln->n, lim - a, x, b->x, ck, a);
        if (a + r >= lim || a + m == ln->n) return a + r;
        ck = NULL;                          /* a huge cluster at the buffer end: read more and retry */
    }
}
/* extends the measured prefix of ln to at least unit upto (in bounded steps, recording checkpoints) */
static void Measure(const Ln *ln, int upto) {
    LineInfo *li = ln->li;
    if (upto > ln->n) upto = ln->n;
    while (li->mi < upto) {
        int lim = upto - li->mi > 16384 ? li->mi + 16384 : upto;
        int r = ScanFrom(&g_scr, ln, li->mi, li->mx, lim, li);
        li->mx = g_scr.x[r - li->mi]; li->mi = r;
    }
}
static BOOL Measured(const Ln *ln) { return ln->li->mi >= ln->n; }
/* line width: exact when measured to the end, otherwise extrapolated (provisional, for the scrollbar) */
static int LineWidth(const Ln *ln) {
    const LineInfo *li = ln->li;
    if (li->mi >= ln->n || li->mi <= 0) return li->mx;
    long long w = (long long)li->mx * ln->n / li->mi;
    return w > INT_MAX / 2 ? INT_MAX / 2 : (int)w;
}
static const Mark *CkAt(const LineInfo *li, int i) {     /* last checkpoint at or before unit i */
    int lo = 0, hi = li->nck - 1;
    while (lo < hi) { int m = (lo + hi + 1) / 2; if (li->ck[m].i <= i) lo = m; else hi = m - 1; }
    return &li->ck[lo];
}
static int XOf(const Ln *ln, int i) {       /* line x of unit i */
    if (i <= 0) return 0;
    if (i > ln->n) i = ln->n;
    Measure(ln, i);
    if (i == ln->li->mi) return ln->li->mx;
    const Mark *c = CkAt(ln->li, i);
    ScanFrom(&g_scr, ln, c->i, c->x, i, NULL);
    return g_scr.x[i - c->i];
}
static int IdxAtX(const Ln *ln, int x) {    /* last cluster boundary whose line x is <= x */
    LineInfo *li = ln->li;
    if (x <= 0) return 0;
    while (li->mi < ln->n && li->mx <= x) Measure(ln, li->mi + 4096);
    int lo = 0, hi = li->nck - 1;           /* last checkpoint with x <= x */
    while (lo < hi) { int m = (lo + hi + 1) / 2; if (li->ck[m].x <= x) lo = m; else hi = m - 1; }
    const Mark *c = &li->ck[lo];
    int end = lo + 1 < li->nck ? li->ck[lo + 1].i : li->mi;
    int r = ScanFrom(&g_scr, ln, c->i, c->x, end, NULL), k = 0;
    while (k < r - c->i && g_scr.x[k + 1] <= x) k++;
    return c->i + k;
}
/* makes LB / LX valid for display units [a, b] of ln */
static void Win(const Ln *ln, int a, int b) {
    if (b > ln->n) b = ln->n;
    if (a > b) a = b;
    if (g_winId == ln->li->id && a >= g_lo && b <= g_hi) return;
    Measure(ln, a);
    const Mark *c = CkAt(ln->li, a);
    g_lo = c->i; g_hi = ScanFrom(&g_win, ln, c->i, c->x, b, NULL); g_winId = ln->li->id;
}

/* ---- wrapping ---- */
static int WrapW(void) { int w = g_cw - 2 * g_margin - g_caretW; return w < g_avgW * 2 ? g_avgW * 2 : w; }
static BOOL IsCJK(WCHAR c) { return c >= 0x2E80; }
static BOOL NoLineStart(WCHAR c) { return c && wcschr(L"、。，．・：；？！゛゜ヽヾゝゞ々ー）］｝」』】〕〉》’”ぁぃぅぇぉっゃゅょゎァィゥェォッャュョヮヵヶ!),.:;?]}", c) != NULL; }
/* start of the row after the row starting at s (ln->n if the rest fits): break at a space / CJK
   boundary, simple kinsoku (no closing punctuation at a row start) */
static int NextBreak(const Ln *ln, int s, int W) {
    int x0 = XOf(ln, s);
    for (int span = 256 + 4 * W / (g_avgW > 0 ? g_avgW : 1);; span *= 4) {
        int r = ScanFrom(&g_scr, ln, s, x0, s + span < ln->n ? s + span : ln->n, NULL) - s;
        const WCHAR *t = g_scr.t; const int *xs = g_scr.x;
        int opp = -1, i = 0;
        while (i < r) {
            int j = BufNext(t, r, i);
            if (i > 0 && (t[i - 1] == L' ' || t[i - 1] == L'\t' || t[i - 1] == 0x3000 || IsCJK(t[i]) || IsCJK(t[i - 1]))) opp = i;
            if (xs[j] - xs[0] > W && i > 0) {
                int brk = opp > 0 ? opp : i;
                if (brk == i && NoLineStart(t[brk]) && opp <= 0) {
                    int q = 0, prev = 0;
                    while (q < brk) { prev = q; q = BufNext(t, r, q); }
                    if (prev > 0) brk = prev;
                }
                return s + brk;
            }
            i = j;
        }
        if (s + r >= ln->n) return ln->n;
    }
}
/* finds rows of ln until at least want rows are known or all are; returns the number known */
static int EnsureRows(const Ln *ln, int want) {
    LineInfo *li = ln->li; int W = g_wrap ? WrapW() : 0;
    if (li->rw != W || !li->nr || !W) {     /* no wrap: one row */
        if (!li->cr) { li->cr = 4; li->rows = xmalloc(4 * sizeof(int)); }
        li->nr = 1; li->rows[0] = 0; li->rw = W; li->rdone = !W || !ln->n;
    }
    while (!li->rdone && li->nr < want) {
        int b = NextBreak(ln, li->rows[li->nr - 1], W);
        if (b >= ln->n) { li->rdone = TRUE; break; }
        if (li->nr == li->cr) { li->cr *= 2; li->rows = xrealloc(li->rows, (size_t)li->cr * sizeof(int)); }
        li->rows[li->nr++] = b;
    }
    if (li->rdone && W && ln->co < 0 && W == g_rowsW && g_lm[ln->L].rows != li->nr) SetRowCount(ln->L, li->nr);
    return li->nr;
}
static void RowCountsCheck(void) {          /* known row counts belong to one wrap width */
    int W = g_wrap ? WrapW() : -1;
    if (W == g_rowsW) return;
    for (size_t L = 0; L < g_nl; L++) g_lm[L].rows = 0;
    g_rowsSum = (long long)g_nl; g_rowsW = W; g_bgL = 0; g_tcL = 0; g_tcS = 0;
}
/* rows of line L (with composition); stops early once at least want rows are known */
static int RowsAtLeast(size_t L, int want) {
    if (!g_wrap) return 1;
    RowCountsCheck();
    if (g_lm[L].rows && !(g_comp && g_clen > 0 && LineOf(g_cpos) == L)) return g_lm[L].rows;
    Ln ln = LnOf(L, TRUE);
    return EnsureRows(&ln, want);
}
static int RowsOf(size_t L) { return RowsAtLeast(L, INT_MAX); }
/* font / zoom / DPI changed: all widths are invalid */
static void LayoutReset(void) {
    for (size_t L = 0; L < g_nl; L++) InfoFree(L);
    DictReset();
    g_ciL = (size_t)-1; g_winId = 0; g_rowsW = -2;
}

/* ---- the current line (LayoutLine) and its rows ---- */
static Ln g_ln;
static int LayoutLine(size_t L, BOOL withComp) { g_ln = LnOf(L, withComp); return g_ln.n; }
static BOOL HasRow(int r) { return EnsureRows(&g_ln, r + 1) > r; }
static int RowStart(int r) { int nr = EnsureRows(&g_ln, r + 1); return g_ln.li->rows[r < nr ? r : nr - 1]; }
static int RowEnd(int r) { return EnsureRows(&g_ln, r + 2) > r + 1 ? g_ln.li->rows[r + 1] : g_ln.n; }
static int RowOf(int idx) {
    LineInfo *li = g_ln.li;
    EnsureRows(&g_ln, 1);
    while (!li->rdone && li->rows[li->nr - 1] <= idx) EnsureRows(&g_ln, li->nr + 1);
    int lo = 0, hi = li->nr - 1;
    while (lo < hi) { int m = (lo + hi + 1) / 2; if (li->rows[m] <= idx) lo = m; else hi = m - 1; }
    return lo;
}
static int RowX(int idx, int r) { return XOf(&g_ln, idx) - XOf(&g_ln, RowStart(r)); }
static int XClient(int x) { return x + g_margin - (g_wrap ? 0 : g_sx); }
static int VisLines(void) { int v = g_ch / g_lineH; return v < 1 ? 1 : v; }
static int CmpLR(size_t L1, int r1, size_t L2, int r2) { if (L1 != L2) return L1 < L2 ? -1 : 1; return r1 < r2 ? -1 : (r1 > r2); }
/* rows from (L1,r1) to (L2,r2); |result| capped at limit+1 */
static long long RowDelta(size_t L1, int r1, size_t L2, int r2, long long limit) {
    if (!g_wrap) return (long long)L2 - (long long)L1;
    int c = CmpLR(L1, r1, L2, r2);
    if (c == 0) return 0;
    if (c > 0) return -RowDelta(L2, r2, L1, r1, limit);
    if (L1 == L2) return r2 - r1;
    int lim = limit > INT_MAX / 4 ? INT_MAX / 4 : (int)limit;
    long long cnt = RowsAtLeast(L1, r1 + lim + 2) - r1;
    for (size_t L = L1 + 1; L < L2; L++) { if (cnt > limit) return limit + 1; cnt += RowsAtLeast(L, lim + 2); }
    cnt += r2;
    return cnt > limit ? limit + 1 : cnt;
}
/* move (L,r) by d rows; returns the number of rows actually moved (signed) */
static long long StepRows(size_t *L, int *r, long long d) {
    if (!g_wrap) {
        long long t = (long long)*L + d;
        if (t < 0) t = 0;
        if (t > (long long)g_nl - 1) t = (long long)g_nl - 1;
        long long moved = t - (long long)*L;
        *L = (size_t)t; *r = 0;
        return moved;
    }
    long long moved = 0;
    if (d > 0) {
        while (d > 0) {
            int nr = RowsAtLeast(*L, d > INT_MAX / 4 ? INT_MAX / 4 : *r + (int)d + 1);
            if (*r + d < nr) { *r += (int)d; moved += d; break; }
            if (*L + 1 >= g_nl) { moved += nr - 1 - *r; *r = nr - 1; break; }
            d -= nr - *r; moved += nr - *r; (*L)++; *r = 0;
        }
    } else {
        while (d < 0) {
            if (*r + d >= 0) { *r += (int)d; moved += d; break; }
            if (*L == 0) { moved -= *r; *r = 0; break; }
            d += *r + 1; moved -= *r + 1; (*L)--; *r = RowsOf(*L) - 1;
        }
    }
    return moved;
}
static int RowY(size_t L, int r) {
    long long d = RowDelta(g_top, g_topRow, L, r, VisLines() + 2);
    if (d > 100000) d = 100000;
    if (d < -100000) d = -100000;
    return (int)d * g_lineH;
}
/* caret client point (inside composition at GCS_CURSORPOS while composing) */
static void CaretInfo(POINT *pt, size_t *pL, int *pr) {
    size_t L; int idx, r, x;
    if (g_comp && g_clen > 0) {
        L = LineOf(g_cpos); LayoutLine(L, TRUE);
        idx = g_ln.co + g_ccur; r = RowOf(idx); x = RowX(idx, r);
    } else {
        L = LineOf(g_caret); LayoutLine(L, FALSE);
        idx = (int)(g_caret - LineStart(L)); r = RowOf(idx);
        if (g_aff && r > 0 && RowStart(r) == idx) r--;
        x = RowX(idx, r);
    }
    pt->x = XClient(x); pt->y = RowY(L, r);
    if (pL) *pL = L;
    if (pr) *pr = r;
}
static void CaretPoint(POINT *pt, size_t *pL) { CaretInfo(pt, pL, NULL); }
/* client point of display index idx on line L (layout with composition) */
static void IdxPoint(size_t L, int idx, POINT *pt) {
    LayoutLine(L, TRUE);
    int r = RowOf(idx), x = RowX(idx, r);
    pt->x = XClient(x); pt->y = RowY(L, r);
}
static size_t PosAtRowX(size_t L, int r, int px, BOOL *aff) {
    LayoutLine(L, FALSE);
    int nr = EnsureRows(&g_ln, r + 2);
    if (r >= nr) r = nr - 1;
    BOOL more = r + 1 < nr;
    int a = RowStart(r), b = RowEnd(r), base = XOf(&g_ln, a);
    size_t s = LineStart(L);
    if (aff) *aff = FALSE;
    if (px <= 0) return s + (size_t)a;
    int q = IdxAtX(&g_ln, base + px);
    if (q < a) q = a;
    while (q < b) {
        Win(&g_ln, q, q + 1);
        int nq = q + BufNext(&LB(q), g_hi - q, 0); if (nq > b) nq = b;
        int x0 = LX(q) - base, x1 = LX(nq) - base;
        if (px < x1) {
            int res = (px - x0 < x1 - px) ? q : nq;
            if (aff && res == b && more) *aff = TRUE;
            return s + (size_t)res;
        }
        q = nq;
    }
    if (aff && more) *aff = TRUE;
    return s + (size_t)b;
}
static size_t PosFromPointEx(int x, int y, BOOL *aff) {
    long long k = y >= 0 ? y / g_lineH : -((-(long long)y + g_lineH - 1) / g_lineH);
    size_t L = g_top; int r = g_topRow;
    StepRows(&L, &r, k);
    return PosAtRowX(L, r, x - g_margin + (g_wrap ? 0 : g_sx), aff);
}
static size_t PosFromPoint(int x, int y) { return PosFromPointEx(x, y, NULL); }

/* ================================================================== */
/* scrolling                                                           */
/* ================================================================== */
static int g_mdTop, g_mdH;                  /* markdown view scroll (px) */
static int ContentW(void) { return g_maxW + g_margin * 2 + g_caretW; }
static void ClampScroll(void) {
    if (g_mdView) {
        int mx = g_mdH - g_ch; if (mx < 0) mx = 0;
        if (g_mdTop > mx) g_mdTop = mx;
        if (g_mdTop < 0) g_mdTop = 0;
        return;
    }
    if (g_top >= g_nl) { g_top = g_nl - 1; g_topRow = 0; }
    if (g_topRow < 0) g_topRow = 0;
    if (g_wrap) { int nr = RowsAtLeast(g_top, g_topRow + 1); if (g_topRow >= nr) g_topRow = nr - 1; }
    else g_topRow = 0;
    /* keep the last row at the bottom: look vis-1 rows ahead (only rows that are needed get laid out) */
    long long want = VisLines() - 1;
    size_t L = g_top; int r = g_topRow;
    long long moved = StepRows(&L, &r, want);
    if (moved < want) StepRows(&g_top, &g_topRow, moved - want);
    if (g_wrap) g_sx = 0;
    else {
        int maxSx = ContentW() - g_cw; if (maxSx < 0) maxSx = 0;
        if (g_sx > maxSx) g_sx = maxSx;
        if (g_sx < 0) g_sx = 0;
    }
}
/* wrap mode scrollbar unit = rows. Lines whose row count is not known yet count as one row; idle
   time fills the counts in, so the bar becomes exact. Small documents are counted at once. */
#define WRAP_EXACT_LINES 400
static long long TopRowIndex(void) {
    while (g_tcL < g_top) g_tcS += RowsK(g_tcL++);
    while (g_tcL > g_top) g_tcS -= RowsK(--g_tcL);
    return g_tcS + g_topRow;
}
static void TopFromRowIndex(long long t) {
    size_t L = 0;
    while (L + 1 < g_nl && t >= RowsK(L)) t -= RowsK(L++);
    g_top = L; g_topRow = (int)t;
}
static void UpdateScrollBars(void) {
    static BOOL busy;
    if (busy || !g_hwnd) return;
    busy = TRUE;
    for (int pass = 0; pass < 3; pass++) {
        int cw0 = g_cw, ch0 = g_ch;
        ClampScroll();
        SCROLLINFO si = { sizeof si, SIF_RANGE | SIF_PAGE | SIF_POS, 0, 0, 0, 0, 0 };
        if (g_mdView) { si.nMax = g_mdH - 1; si.nPage = (UINT)(g_ch > 0 ? g_ch : 1); si.nPos = g_mdTop; }
        else if (g_wrap) {
            RowCountsCheck();
            if (g_nl <= WRAP_EXACT_LINES) for (size_t L = 0; L < g_nl; L++) RowsOf(L);
            long long t = g_rowsSum - 1, p = TopRowIndex();
            if (t > 0x7FFFFFF) t = 0x7FFFFFF;
            if (p > t) p = t;
            si.nMax = (int)t; si.nPage = (UINT)VisLines(); si.nPos = (int)p;
        } else {
            si.nMax = g_nl - 1 > 0x7FFFFFF ? 0x7FFFFFF : (int)(g_nl - 1);
            si.nPage = (UINT)VisLines(); si.nPos = (int)g_top;
        }
        SetScrollInfo(g_hwnd, SB_VERT, &si, TRUE);
        SCROLLINFO hi = { sizeof hi, SIF_RANGE | SIF_PAGE | SIF_POS, 0, 0, 0, 0, 0 };
        if (g_wrap || g_mdView) { hi.nMax = 0; hi.nPage = 1; hi.nPos = 0; }
        else { hi.nMax = ContentW() - 1; hi.nPage = (UINT)(g_cw > 0 ? g_cw : 1); hi.nPos = g_sx; }
        SetScrollInfo(g_hwnd, SB_HORZ, &hi, TRUE);
        if (cw0 == g_cw && ch0 == g_ch) break;
        g_layoutVer++;   /* client width changed -> wrap width changed */
    }
    busy = FALSE;
}
static void EnsureVisible(void) {
    if (g_mdView) return;
    POINT pt; size_t L; int r;
    CaretInfo(&pt, &L, &r);
    int vis = VisLines();
    if (CmpLR(L, r, g_top, g_topRow) < 0) { g_top = L; g_topRow = r; }
    else if (RowDelta(g_top, g_topRow, L, r, vis) >= vis) {
        size_t nL = L; int nr = r;
        StepRows(&nL, &nr, -(long long)(vis - 1));
        g_top = nL; g_topRow = nr;
    }
    if (g_wrap) { g_sx = 0; return; }
    CaretInfo(&pt, &L, &r);
    int x = pt.x + g_sx - g_margin;
    int w = g_cw - g_margin * 2; if (w < 20) w = 20;
    if (x + g_caretW > g_maxW) g_maxW = x + g_caretW;
    if (x < g_sx) g_sx = x - w / 4;
    else if (x + g_caretW > g_sx + w) { g_sx = x + g_caretW - w + w / 4; if (g_sx + w > g_maxW) g_maxW = g_sx + w; }
    if (g_sx < 0) g_sx = 0;
}
static void ScrollRows(long long d) {
    if (g_mdView) { g_mdTop += (int)d * g_lineH; ClampScroll(); Refresh(FALSE); return; }
    StepRows(&g_top, &g_topRow, d);
    ClampScroll();
    Refresh(FALSE);
}

/* ================================================================== */
/* editing                                                             */
/* ================================================================== */
static BOOL HasSel(void) { return g_caret != g_anchor; }
static size_t SelA(void) { return g_caret < g_anchor ? g_caret : g_anchor; }
static size_t SelB(void) { return g_caret < g_anchor ? g_anchor : g_caret; }
static void DeleteSelection(void) {
    if (!HasSel()) return;
    size_t a = SelA(), b = SelB();
    EditDelete(a, b - a);
    g_caret = g_anchor = a;
}
static void InsertText(const WCHAR *s, size_t n, int kind) {
    BOOL nl = (n == 1 && s[0] == L'\n');
    BOOL merge = (kind == K_TYPE && g_lastKind == K_TYPE && g_lastEnd == g_caret && !HasSel() && !nl);
    if (kind == K_IME) merge = TRUE;
    if (!merge) NewGroup();
    DeleteSelection();
    EditInsert(g_caret, s, n);
    g_caret += n; g_anchor = g_caret; g_aff = FALSE;
    g_lastKind = (kind == K_TYPE && nl) ? K_NONE : kind;
    g_lastEnd = g_caret;
    g_wantX = -1;
}
static void Undo(void) {
    if (!g_undo.n) return;
    int grp = g_undo.v[g_undo.n - 1].grp;
    size_t cb = 0, ab = 0;
    while (g_undo.n && g_undo.v[g_undo.n - 1].grp == grp) {
        Op o = g_undo.v[--g_undo.n];
        if (o.ins) RawDelete(o.pos, o.n); else RawInsert(o.pos, o.s, o.n);
        cb = o.cb; ab = o.ab;
        OpPush(&g_redo, o);
    }
    size_t len = DocLen();
    g_caret = cb > len ? len : cb; g_anchor = ab > len ? len : ab; g_aff = FALSE;
    g_modified = TRUE; BreakUndoMerge(); NewGroup(); g_wantX = -1;
}
static void Redo(void) {
    if (!g_redo.n) return;
    int grp = g_redo.v[g_redo.n - 1].grp;
    size_t cp = g_caret;
    while (g_redo.n && g_redo.v[g_redo.n - 1].grp == grp) {
        Op o = g_redo.v[--g_redo.n];
        if (o.ins) { RawInsert(o.pos, o.s, o.n); cp = o.pos + o.n; } else { RawDelete(o.pos, o.n); cp = o.pos; }
        OpPush(&g_undo, o);
    }
    g_caret = g_anchor = cp; g_aff = FALSE;
    g_modified = TRUE; BreakUndoMerge(); NewGroup(); g_wantX = -1;
}
static void CopySel(void) {
    if (!HasSel()) return;
    size_t a = SelA(), n = SelB() - a, lf = 0;
    WCHAR *t = xmalloc((n + 1) * sizeof(WCHAR)); DocGet(a, n, t);
    for (size_t i = 0; i < n; i++) if (t[i] == L'\n') lf++;
    HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE, (n + lf + 1) * sizeof(WCHAR));
    if (h) {
        WCHAR *d = GlobalLock(h); size_t k = 0;
        for (size_t i = 0; i < n; i++) { if (t[i] == L'\n') d[k++] = L'\r'; d[k++] = t[i]; }
        d[k] = 0; GlobalUnlock(h);
        if (OpenClipboard(g_hwnd)) { EmptyClipboard(); if (!SetClipboardData(CF_UNICODETEXT, h)) GlobalFree(h); CloseClipboard(); }
        else GlobalFree(h);
    }
    free(t);
}
static size_t NormalizeNewlines(WCHAR *t, size_t n) {
    size_t k = 0;
    for (size_t i = 0; i < n; i++) {
        WCHAR c = t[i];
        if (c == L'\r') { if (i + 1 < n && t[i + 1] == L'\n') i++; c = L'\n'; }
        if (c == 0) continue;
        t[k++] = c;
    }
    return k;
}
static void Paste(void) {
    if (!OpenClipboard(g_hwnd)) return;
    HANDLE h = GetClipboardData(CF_UNICODETEXT);
    if (h) {
        const WCHAR *s = GlobalLock(h);
        if (s) {
            size_t n = wcslen(s);
            WCHAR *t = xmalloc((n + 1) * sizeof(WCHAR)); memcpy(t, s, n * sizeof(WCHAR));
            GlobalUnlock(h);
            n = NormalizeNewlines(t, n);
            InsertText(t, n, K_OTHER);
            BreakUndoMerge();
            free(t);
        }
    }
    CloseClipboard();
}
static void CutSel(void) {
    if (!HasSel()) return;
    CopySel(); NewGroup(); DeleteSelection(); BreakUndoMerge(); UpdateTitle(); Refresh(TRUE);
}

/* ================================================================== */
/* file I/O (large-file aware: decoded chunk by chunk straight into the original text) */
/* ================================================================== */
static void ResetDoc(void) {
    OpClear(&g_undo); OpClear(&g_redo);
    g_caret = g_anchor = 0; g_top = 0; g_topRow = 0; g_sx = 0; g_maxW = 0; g_wantX = -1; g_aff = FALSE;
    g_modified = FALSE; BreakUndoMerge(); g_docVer++;
}
/* takes ownership of buf (text length n, from OrgAlloc(cap)): it becomes the immutable original text */
static void AdoptDoc(WCHAR *buf, size_t n, size_t cap) {
    PtAdopt(buf, n, cap);
    RebuildLines(); g_docVer++;
}
static void SetDocText(const WCHAR *t, size_t n) {
    WCHAR *b = OrgAlloc(n);
    if (!b) NoMem();
    if (n) memcpy(b, t, n * sizeof(WCHAR));
    AdoptDoc(b, n, n);
}
#define LOAD_CHUNK (1u << 22)               /* bytes read and decoded at a time */
static DWORD CharCut(const BYTE *b, DWORD m, UINT cp) {   /* start of the last character in b[0, m) */
    if (cp == CP_UTF8) { DWORD j = m - 1; while (j > 0 && m - j < 4 && (b[j] & 0xC0) == 0x80) j--; return j; }
    static BYTE lead[256]; static BOOL init;
    if (!init) { for (int c = 0; c < 256; c++) lead[c] = IsDBCSLeadByteEx(932, (BYTE)c) ? 1 : 0; init = TRUE; }
    DWORD i = 0, last = 0;
    while (i < m) { last = i; i += lead[b[i]] ? 2u : 1u; }
    return last;
}
static BOOL g_loadQuiet;
/* The file is read in chunks and each chunk is decoded straight into the original-text buffer, so the
   raw bytes are never held as a whole. UTF-8 BOM / UTF-16LE BOM / strict UTF-8, else Shift_JIS (CP932). */
static BOOL LoadFile(const WCHAR *path) {
    HANDLE f = CreateFileW(path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    if (f == INVALID_HANDLE_VALUE) { if (!g_loadQuiet) MessageBoxW(g_frame, L"ファイルを開けません。", APPNAME, MB_ICONERROR); return FALSE; }
    LARGE_INTEGER sz; GetFileSizeEx(f, &sz);
    if (sz.QuadPart > 0x7FFFFFF0LL) { CloseHandle(f); MessageBoxW(g_frame, L"ファイルが大きすぎます (2GB 以上)。", APPNAME, MB_ICONERROR); return FALSE; }
    HCURSOR oc = SetCursor(LoadCursorW(NULL, IDC_WAIT));
    DWORD n = (DWORD)sz.QuadPart, rd = 0, skip = 0;
    BYTE h[3] = { 0, 0, 0 };
    BOOL ok = ReadFile(f, h, n < 3 ? n : 3, &rd, NULL);
    int enc = 0;
    if (n >= 3 && h[0] == 0xEF && h[1] == 0xBB && h[2] == 0xBF) { enc = 1; skip = 3; }
    else if (n >= 2 && h[0] == 0xFF && h[1] == 0xFE) { enc = 3; skip = 2; }
    size_t cap = enc == 3 ? (n - 2) / 2 : n, wn = 0;   /* UTF-8 / CP932: at most one unit per byte */
    WCHAR *w = OrgAlloc(cap); BYTE *b = malloc(LOAD_CHUNK + 8);
    if (!w || !b) { free(b); OrgFree(w); CloseHandle(f); SetCursor(oc); MessageBoxW(g_frame, L"メモリ不足です。", APPNAME, MB_ICONERROR); return FALSE; }
    UINT cp = CP_UTF8; DWORD flags = enc == 0 ? MB_ERR_INVALID_CHARS : 0;
    for (BOOL again = TRUE; ok && again; ) {    /* one decoding pass; repeated as CP932 if strict UTF-8 fails */
        again = FALSE;
        LARGE_INTEGER z; z.QuadPart = skip; ok = SetFilePointerEx(f, z, NULL, FILE_BEGIN);
        DWORD left = n - skip, carry = 0; wn = 0;
        while (ok && (left || carry)) {
            DWORD want = left > LOAD_CHUNK ? LOAD_CHUNK : left;
            if (enc == 3) {                 /* UTF-16LE: read straight into the text */
                if (want > (cap - wn) * 2) want = (DWORD)((cap - wn) * 2);
                ok = want && ReadFile(f, (BYTE *)(w + wn), want, &rd, NULL) && rd == want; wn += want / 2; left -= want;
                if ((cap - wn) == 0) left = 0;
                continue;
            }
            if (want) { ok = ReadFile(f, b + carry, want, &rd, NULL) && rd == want; if (!ok) break; left -= want; }
            DWORD m = carry + want, c = left ? CharCut(b, m, cp) : m;
            if (c) {
                int r = MultiByteToWideChar(cp, flags, (const char *)b, (int)c, w + wn, (int)(cap - wn));
                if (r <= 0) { if (cp == CP_UTF8 && enc == 0) { cp = 932; flags = 0; enc = 2; again = TRUE; } else ok = FALSE; break; }
                wn += (size_t)r;
            }
            carry = m - c; memmove(b, b + c, carry);
        }
    }
    CloseHandle(f); free(b);
    if (!ok) { OrgFree(w); SetCursor(oc); MessageBoxW(g_frame, L"読み込みに失敗しました。", APPNAME, MB_ICONERROR); return FALSE; }
    wn = NormalizeNewlines(w, wn); w[wn] = 0;
    Decommit(w + wn + 1, w + cap + 1);      /* the part the text did not need (CRLF, multi-byte) */
    AdoptDoc(w, wn, cap);
    ResetDoc(); g_enc = enc;
    wcsncpy(g_path, path, sizeof g_path / sizeof g_path[0] - 1);
    g_maxW = 0; g_layoutVer++;
    if (g_mdView) MdInvalidate();
    SetCursor(oc);
    UpdateTitle(); Refresh(TRUE);
    return TRUE;
}
static BOOL SaveFile(const WCHAR *path) {
    HANDLE f = CreateFileW(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) { MessageBoxW(g_frame, L"保存できません (書き込み不可)。", APPNAME, MB_ICONERROR); return FALSE; }
    int enc = (g_enc == 1) ? 1 : 0;
    BOOL ok = TRUE; DWORD wr;
    if (enc == 1) { static const BYTE bom[3] = { 0xEF, 0xBB, 0xBF }; ok = WriteFile(f, bom, 3, &wr, NULL) && wr == 3; }
    const size_t CH = 1 << 20;
    WCHAR *t = xmalloc(CH * sizeof(WCHAR)), *c = xmalloc((CH * 2 + 2) * sizeof(WCHAR));
    char *u = xmalloc(CH * 2 * 3 + 16);
    size_t len = DocLen(), p = 0;
    while (ok && p < len) {
        size_t n = len - p > CH ? CH : len - p;
        if (p + n < len && IS_HI(DocAt(p + n - 1))) n--;   /* keep surrogate pairs together */
        DocGet(p, n, t);
        size_t k = 0;
        for (size_t i = 0; i < n; i++) { if (t[i] == L'\n') c[k++] = L'\r'; c[k++] = t[i]; }
        int bn = WideCharToMultiByte(CP_UTF8, 0, c, (int)k, u, (int)(CH * 6 + 16), NULL, NULL);
        ok = bn > 0 && WriteFile(f, u, (DWORD)bn, &wr, NULL) && wr == (DWORD)bn;
        p += n;
    }
    free(t); free(c); free(u);
    CloseHandle(f);
    if (!ok) { MessageBoxW(g_frame, L"保存に失敗しました。", APPNAME, MB_ICONERROR); return FALSE; }
    g_enc = enc; g_modified = FALSE;
    if (path != g_path) wcsncpy(g_path, path, sizeof g_path / sizeof g_path[0] - 1);
    UpdateTitle();
    return TRUE;
}
static const WCHAR kFilter[] = L"テキスト ファイル (*.txt;*.md)\0*.txt;*.md;*.markdown\0すべてのファイル (*.*)\0*.*\0";
static BOOL DoSaveAs(void) {
    WCHAR p[MAX_PATH * 4]; wcsncpy(p, g_path, sizeof p / sizeof p[0] - 1); p[sizeof p / sizeof p[0] - 1] = 0;
    OPENFILENAMEW of; memset(&of, 0, sizeof of);
    of.lStructSize = sizeof of; of.hwndOwner = g_frame; of.lpstrFilter = kFilter;
    of.lpstrFile = p; of.nMaxFile = sizeof p / sizeof p[0]; of.lpstrDefExt = L"txt";
    of.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetSaveFileNameW(&of)) return FALSE;
    return SaveFile(p);
}
/* Ctrl+S: confirm every time (spec) */
static BOOL DoSave(void) {
    if (!g_path[0]) return DoSaveAs();
    WCHAR msg[MAX_PATH * 4 + 64];
    _snwprintf(msg, sizeof msg / sizeof msg[0], L"上書き保存しますか?\n\n%ls", g_path); msg[sizeof msg / sizeof msg[0] - 1] = 0;
    if (MessageBoxW(g_frame, msg, APPNAME, MB_YESNO | MB_ICONQUESTION | MB_DEFBUTTON1) != IDYES) return FALSE;
    return SaveFile(g_path);
}
static BOOL ConfirmDiscard(void) {
    if (!g_modified) return TRUE;
    int r = MessageBoxW(g_frame, L"変更内容を保存しますか?", APPNAME, MB_YESNOCANCEL | MB_ICONQUESTION);
    if (r == IDCANCEL) return FALSE;
    if (r == IDYES) return g_path[0] ? SaveFile(g_path) : DoSaveAs();
    return TRUE;
}
static void DoOpen(void) {
    if (!ConfirmDiscard()) return;
    WCHAR p[MAX_PATH * 4]; p[0] = 0;
    OPENFILENAMEW of; memset(&of, 0, sizeof of);
    of.lStructSize = sizeof of; of.hwndOwner = g_frame; of.lpstrFilter = kFilter;
    of.lpstrFile = p; of.nMaxFile = sizeof p / sizeof p[0];
    of.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (GetOpenFileNameW(&of)) LoadFile(p);
}
/* "memo3.txt" -> "memo4.txt", "memo.txt" -> "memo1.txt", "memo009.txt" -> "memo010.txt" */
static void IncrementName(const WCHAR *path, WCHAR *out, size_t cap) {
    const WCHAR *name = wcsrchr(path, L'\\'); name = name ? name + 1 : path;
    const WCHAR *dot = wcsrchr(name, L'.');
    if (!dot || dot == name) dot = name + wcslen(name);
    const WCHAR *d = dot;
    while (d > name && d[-1] >= L'0' && d[-1] <= L'9') d--;
    size_t pre = (size_t)(d - path), nd = (size_t)(dot - d);
    WCHAR num[64];
    if (nd == 0 || nd > 30) wcscpy(num, L"1");
    else {
        /* decimal increment on the digit string, keeping zero padding */
        wcsncpy(num, d, nd); num[nd] = 0;
        int i = (int)nd - 1;
        while (i >= 0) { if (num[i] == L'9') { num[i] = L'0'; i--; } else { num[i]++; break; } }
        if (i < 0) { memmove(num + 1, num, (nd + 1) * sizeof(WCHAR)); num[0] = L'1'; }
    }
    _snwprintf(out, cap, L"%.*ls%ls%ls", (int)pre, path, num, dot);
    out[cap - 1] = 0;
}
static void DoSaveIncrement(void) {
    if (!g_path[0]) { DoSaveAs(); return; }
    WCHAR np[MAX_PATH * 4], cur[MAX_PATH * 4];
    wcsncpy(cur, g_path, sizeof cur / sizeof cur[0] - 1); cur[sizeof cur / sizeof cur[0] - 1] = 0;
    for (int guard = 0; guard < 10000; guard++) {
        IncrementName(cur, np, sizeof np / sizeof np[0]);
        if (GetFileAttributesW(np) == INVALID_FILE_ATTRIBUTES) break;
        WCHAR msg[MAX_PATH * 4 + 160];
        _snwprintf(msg, sizeof msg / sizeof msg[0], L"%ls は既に存在します。\n\nはい: 上書きする\nいいえ: さらに番号を進める\nキャンセル: 中止", np);
        msg[sizeof msg / sizeof msg[0] - 1] = 0;
        int r = MessageBoxW(g_frame, msg, APPNAME, MB_YESNOCANCEL | MB_ICONWARNING | MB_DEFBUTTON2);
        if (r == IDCANCEL) return;
        if (r == IDYES) break;
        wcscpy(cur, np);
    }
    size_t L = LineOf(g_caret), col = g_caret - LineStart(L);
    size_t top = g_top; int topRow = g_topRow, sx = g_sx;
    if (!SaveFile(np)) return;
    /* close the current file and open the saved one at the same place */
    if (!LoadFile(np)) return;
    if (L >= g_nl) L = g_nl - 1;
    size_t p = LineStart(L) + col; if (p > LineEnd(L)) p = LineEnd(L);
    g_caret = g_anchor = p;
    g_top = top; g_topRow = topRow; g_sx = sx;
    ClampScroll();
    Refresh(FALSE);
}

/* ================================================================== */
/* title / font / DPI                                                  */
/* ================================================================== */
static int Sc(int v) { return MulDiv(v, (int)g_dpi, 96); }
static void UpdateTitle(void) {
    const WCHAR *name = g_path[0] ? wcsrchr(g_path, L'\\') : NULL;
    name = name ? name + 1 : (g_path[0] ? g_path : L"無題");
    if (g_frame) {
        SetWindowTextW(g_frame, name);          /* taskbar shows the file name */
        RECT rc; GetClientRect(g_frame, &rc); rc.bottom = Sc(32);
        InvalidateRect(g_frame, &rc, FALSE);
    }
}
static void CreateCaretNow(void) {
    if (!g_focus || g_mdView) return;
    if (g_caretMade) DestroyCaret();
    CreateCaret(g_hwnd, NULL, g_caretW, g_lineH);
    g_caretMade = TRUE;
    ShowCaret(g_hwnd);
}
static void SetImeFont(void) {
    HIMC imc = ImmGetContext(g_hwnd);
    if (imc) { ImmSetCompositionFontW(imc, &g_lf); ImmReleaseContext(g_hwnd, imc); }
}
static void SetupFont(void) {
    if (!g_hdcM) g_hdcM = CreateCompatibleDC(NULL);
    memset(&g_lf, 0, sizeof g_lf);
    g_lf.lfHeight = -MulDiv(g_fontPt10, (int)g_dpi, 720);
    g_lf.lfWeight = FW_NORMAL;
    g_lf.lfCharSet = DEFAULT_CHARSET;
    g_lf.lfOutPrecision = OUT_TT_PRECIS;
    g_lf.lfQuality = CLEARTYPE_QUALITY;
    g_lf.lfPitchAndFamily = (g_fontIdx <= 1 || g_fontIdx == 4) ? (FIXED_PITCH | FF_MODERN) : (VARIABLE_PITCH | FF_SWISS);
    wcsncpy(g_lf.lfFaceName, kFonts[g_fontIdx], LF_FACESIZE - 1);
    HFONT nf = CreateFontIndirectW(&g_lf);
    SelectObject(g_hdcM, nf);
    if (g_font) DeleteObject(g_font);
    g_font = nf;
    TEXTMETRICW tm; GetTextMetricsW(g_hdcM, &tm);
    g_lineH = tm.tmHeight + tm.tmExternalLeading; if (g_lineH < 4) g_lineH = 4;
    g_ascent = tm.tmAscent;
    SIZE sz; GetTextExtentPoint32W(g_hdcM, L"        ", 8, &sz);
    g_avgW = sz.cx / 8; if (g_avgW < 1) g_avgW = 1;
    g_tabW = g_avgW * 4;
    g_margin = Sc(6);
    DWORD cw = 1; SystemParametersInfoW(SPI_GETCARETWIDTH, 0, &cw, 0);
    g_caretW = MulDiv((int)(cw < 1 ? 1 : cw), (int)g_dpi, 96); if (g_caretW < 1) g_caretW = 1;
    g_maxW = 0; g_layoutVer++;
    LayoutReset(); g_dirty = TRUE;          /* widths depend on font / zoom / DPI */
    /* UI fonts */
    if (g_uiFont) DeleteObject(g_uiFont);
    if (g_capFont) DeleteObject(g_capFont);
    LOGFONTW u; memset(&u, 0, sizeof u);
    u.lfHeight = -MulDiv(9, (int)g_dpi, 72); u.lfCharSet = DEFAULT_CHARSET; u.lfQuality = CLEARTYPE_QUALITY;
    wcscpy(u.lfFaceName, L"Yu Gothic UI");
    g_uiFont = CreateFontIndirectW(&u);
    u.lfHeight = -MulDiv(10, (int)g_dpi, 72);
    g_capFont = CreateFontIndirectW(&u);
    if (g_hwnd) { SetImeFont(); CreateCaretNow(); }
    MdInvalidate();
}

/* ================================================================== */
/* IME helpers                                                         */
/* ================================================================== */
static void CompTarget(int *a, int *b) {
    int s = -1, e = -1;
    for (int i = 0; i < g_clen; i++) {
        BYTE at = g_cattr[i];
        if (at == ATTR_TARGET_CONVERTED || at == ATTR_TARGET_NOTCONVERTED) { if (s < 0) s = i; e = i + 1; }
        else if (s >= 0) break;
    }
    if (s < 0) s = e = g_ccur;
    *a = s; *b = e;
}
/* composition start point and target-clause rectangle (client coords) */
static void ImeGeometry(POINT *compPt, int *tx0, int *tx1, int *ty) {
    if (g_comp && g_clen > 0) {
        size_t L = LineOf(g_cpos);
        LayoutLine(L, TRUE);
        int co = g_ln.co, ta, tb; CompTarget(&ta, &tb);
        int r = RowOf(co + ta), e = co + tb; if (e > RowEnd(r)) e = RowEnd(r);
        int x0 = RowX(co + ta, r), x1 = RowX(e, r);
        int rc = RowOf(co), xc = RowX(co, rc);
        int yt = RowY(L, r);
        LayoutLine(L, TRUE);
        int yc = RowY(L, rc);
        *ty = yt; *tx0 = XClient(x0); *tx1 = XClient(x1);
        compPt->x = XClient(xc); compPt->y = yc;
    } else {
        CaretPoint(compPt, NULL);
        *ty = compPt->y; *tx0 = compPt->x; *tx1 = compPt->x + g_caretW;
    }
    if (*tx1 <= *tx0) *tx1 = *tx0 + 1;
}
static void UpdateImeWindows(void) {
    HIMC imc = ImmGetContext(g_hwnd);
    if (!imc) return;
    POINT cp; int x0, x1, y;
    ImeGeometry(&cp, &x0, &x1, &y);
    COMPOSITIONFORM cf; memset(&cf, 0, sizeof cf);
    cf.dwStyle = CFS_POINT; cf.ptCurrentPos = cp;
    ImmSetCompositionWindow(imc, &cf);
    CANDIDATEFORM cand; memset(&cand, 0, sizeof cand);
    cand.dwIndex = 0; cand.dwStyle = CFS_EXCLUDE;
    cand.ptCurrentPos.x = x0; cand.ptCurrentPos.y = y;
    SetRect(&cand.rcArea, x0, y, x1, y + g_lineH);
    ImmSetCandidateWindow(imc, &cand);
    ImmReleaseContext(g_hwnd, imc);
}
static void CompleteComposition(void) {
    if (!g_comp) return;
    HIMC imc = ImmGetContext(g_hwnd);
    if (imc) { ImmNotifyIME(imc, NI_COMPOSITIONSTR, CPS_COMPLETE, 0); ImmReleaseContext(g_hwnd, imc); }
}
static void ClearComp(void) { g_clen = 0; g_nccl = 0; g_ccur = 0; g_compVer++; }
static void PlaceCaret(void) {
    if (g_focus && g_caretMade && !g_mdView) { POINT pt; CaretPoint(&pt, NULL); SetCaretPos(pt.x, pt.y); }
    if (g_focus && !g_mdView) UpdateImeWindows();
}
/* ================================================================== */
/* find matches for painting                                           */
/* ================================================================== */
static WCHAR *g_fbuf; static size_t g_fbcap;
static int g_fm[1024]; static int g_nfm;
static size_t g_curMA = (size_t)-1, g_curMB;
/* text of line L: in place when it is contiguous (almost always after compaction), else copied */
static const WCHAR *LineText(size_t L, int *n) {
    size_t s = LineStart(L), len = LineEnd(L) - s;
    *n = (int)len;
    const WCHAR *d = DocPtr(s, len);
    if (d) return d;
    if (len + 1 > g_fbcap) { g_fbcap = len + 256; g_fbuf = xrealloc(g_fbuf, g_fbcap * sizeof(WCHAR)); }
    DocGet(s, len, g_fbuf); g_fbuf[len] = 0;
    *n = (int)len;
    return g_fbuf;
}
static void LineMatches(size_t L) {
    g_nfm = 0;
    if (!g_findOpen || !g_re) return;
    int n; const WCHAR *t = LineText(L, &n);
    if (n > 200000) return;
    int caps[2 * RE_NCAP], s = 0;
    while (s <= n && g_nfm < 1022 && re_search(g_re, (const rechar *)t, n, s, caps)) {
        if (caps[1] > caps[0]) { g_fm[g_nfm++] = caps[0]; g_fm[g_nfm++] = caps[1]; s = caps[1]; }
        else s = caps[0] + 1;
    }
}

/* ================================================================== */
/* painting: persistent back buffer. A pure scroll shifts it (and the  */
/* window, ScrollWindowEx) and draws only the newly exposed rows       */
/* ================================================================== */
static void FillR(HDC dc, int l, int t, int r, int b, COLORREF c) {
    RECT rc = { l, t, r, b }; SetBkColor(dc, c); ExtTextOutW(dc, 0, 0, ETO_OPAQUE, &rc, NULL, 0, NULL);
}
static void DrawUnderline(HDC dc, int x0, int x1, int y, BYTE attr, COLORREF col) {
    int thin = Sc(1); if (thin < 1) thin = 1;
    if (x1 <= x0) return;
    switch (attr) {
    case ATTR_TARGET_CONVERTED: case ATTR_TARGET_NOTCONVERTED:
        FillR(dc, x0, y - thin, x1, y + thin, col); break;
    case ATTR_CONVERTED: case ATTR_FIXEDCONVERTED:
        FillR(dc, x0, y, x1, y + thin, col); break;
    default:
        for (int x = x0; x < x1; x += thin * 2) FillR(dc, x, y, x + thin < x1 ? x + thin : x1, y + thin, col);
        break;
    }
}
static void DrawWsMarks(HDC dc, int a, int b, int ox, int y) {
    int u = Sc(1); if (u < 1) u = 1;
    int mid = y + g_lineH / 2;
    for (int i = a; i < b; i++) {
        WCHAR c = LB(i);
        int x0 = LX(i) + ox, x1 = LX(i + 1) + ox;
        if (c == L' ') {
            int cx = (x0 + x1) / 2, d = u + (u + 1) / 2;
            FillR(dc, cx - d / 2, mid - d / 2, cx - d / 2 + d, mid - d / 2 + d, C_WS);
        } else if (c == 0x3000) {
            int l = x0 + 2 * u, r = x1 - 2 * u, t = y + (g_lineH - (r - l)) / 2, bt = t + (r - l);
            if (t < y + u) t = y + u;
            if (bt > y + g_lineH - u) bt = y + g_lineH - u;
            FillR(dc, l, t, r, t + u, C_WS); FillR(dc, l, bt - u, r, bt, C_WS);
            FillR(dc, l, t, l + u, bt, C_WS); FillR(dc, r - u, t, r, bt, C_WS);
        } else if (c == L'\t') {
            int l = x0 + 2 * u, r = x1 - 2 * u; if (r - l < 4 * u) r = l + 4 * u;
            FillR(dc, l, mid, r, mid + u, C_WS);
            for (int k = 1; k <= 3 * u; k++) { FillR(dc, r - k, mid - k, r - k + u, mid - k + u, C_WS); FillR(dc, r - k, mid + k, r - k + u, mid + k + u, C_WS); }
        }
    }
}
static void DrawNewlineMark(HDC dc, int x, int y) {
    int u = Sc(1); if (u < 1) u = 1;
    int h = g_lineH / 3, w = g_avgW;
    int bx = x + w, top = y + g_lineH / 2 - h / 2, by = top + h;
    FillR(dc, bx - u, top, bx, by + u, C_WS);            /* vertical */
    FillR(dc, x + u, by, bx, by + u, C_WS);              /* horizontal */
    for (int k = 1; k <= 3 * u; k++) { FillR(dc, x + u + k, by - k, x + 2 * u + k, by - k + u, C_WS); FillR(dc, x + u + k, by + k, x + 2 * u + k, by + k + u, C_WS); }
}
/* text of display units [i, j) at x0 with the measured advances, so the glyphs land exactly where the
   caret, hit testing and underlines put them */
static int *g_dxb; static int g_dxcap;
/* lpDx for window units [i,j): the measured advances.  A surrogate pair's advance is split over its
   two code units: GDI sums them when the pair is one glyph, and Wine draws a missing pair as two boxes. */
static void RunDx(int i, int j, int *dx) {
    for (int k = i; k < j; k++) dx[k - i] = LX(k + 1) - LX(k);
    for (int k = i; k + 1 < j; k++)
        if (IS_HI(LB(k)) && IS_LO(LB(k + 1)) && dx[k - i + 1] == 0) { dx[k - i + 1] = dx[k - i] / 2; dx[k - i] -= dx[k - i + 1]; k++; }
}
static void DrawRun(HDC dc, int x0, int y, int i, int j) {
    if (j - i > g_dxcap) { g_dxcap = j - i + 256; g_dxb = xrealloc(g_dxb, (size_t)g_dxcap * sizeof(int)); }
    RunDx(i, j, g_dxb);
    ExtTextOutW(dc, x0, y, 0, NULL, &LB(i), (UINT)(j - i), g_dxb);
}
static void MdPaint(HDC dc, int w, int h);
/* draws the text rows whose top lies in [y0, y1) (the caller clips and fills the background) */
static void PaintRows(HDC dc, int w, int y0, int y1) {
    COLORREF sbg = (g_focus || GetFocus() == NULL) ? C_SEL : C_SEL_NF;
    size_t sa = SelA(), sb = SelB();
    if (HasSel() && sa == g_curMA && sb == g_curMB && g_findOpen) sbg = C_CURMATCH;
    size_t L = g_top; int r = g_topRow, y = 0;
    int thin = Sc(1); if (thin < 1) thin = 1;
    if (y0 >= g_lineH) y = (int)StepRows(&L, &r, y0 / g_lineH) * g_lineH;
    while (y < y1 && L < g_nl) {
        LineMatches(L);
        int n = LayoutLine(L, TRUE), co = g_ln.co;
        size_t s = LineStart(L), e = s + (size_t)n;
        for (; y < y1 && HasRow(r); r++, y += g_lineH) {
            int a = RowStart(r), b = RowEnd(r);
            BOOL lastRow = !HasRow(r + 1);
            int ox = XClient(0) - XOf(&g_ln, a), va = a, vb = b;
            /* no wrap: only the part inside the window is measured and drawn */
            if (!g_wrap) { va = IdxAtX(&g_ln, -ox); vb = IdxAtX(&g_ln, w - ox); if (vb < b) vb++; }
            Win(&g_ln, va, vb);
            if (vb > g_hi) vb = g_hi;
            /* find highlights */
            if (co < 0)
                for (int k = 0; k < g_nfm; k += 2) {
                    int ms = g_fm[k] > va ? g_fm[k] : va, me = g_fm[k + 1] < vb ? g_fm[k + 1] : vb;
                    if (me > ms) FillR(dc, LX(ms) + ox, y, LX(me) + ox, y + g_lineH, C_MATCH);
                }
            /* selection */
            if (sa != sb && co < 0 && sb > s + (size_t)a && sa <= s + (size_t)b) {
                int ss = (int)((sa > s ? sa : s) - s), se = (int)((sb < e ? sb : e) - s);
                if (ss < va) ss = va;
                if (ss > vb) ss = vb;
                if (se > vb) se = vb;
                if (se < ss) se = ss;
                int x0 = LX(ss) + ox, x1 = LX(se) + ox;
                if (lastRow && sb > e && vb == n) x1 += g_avgW;
                if (x1 > x0) FillR(dc, x0, y, x1, y + g_lineH, sbg);
            }
            /* text */
            SetTextColor(dc, C_TEXT);
            for (int i = va; i < vb;) {
                if (LB(i) == L'\t') { i++; continue; }
                int j = i + 1;
                while (j < vb && LB(j) != L'\t' && j - i < 2048) j++;
                if (j < vb && IS_LO(LB(j))) j++;
                int x0 = LX(i) + ox, x1 = LX(j) + ox;
                if (x1 >= 0 && x0 <= w) DrawRun(dc, x0, y, i, j);
                i = j;
            }
            if (g_showWs) {
                DrawWsMarks(dc, va, vb, ox, y);
                if (lastRow && vb == n) {
                    int xe = LX(n) + ox + Sc(2);
                    if (L + 1 < g_nl) DrawNewlineMark(dc, xe, y);
                    else { SetTextColor(dc, C_WS); ExtTextOutW(dc, xe, y, 0, NULL, L"[EOF]", 5, NULL); }
                }
            }
            /* composition underlines (per clause x attribute, clipped to this row) */
            if (co >= 0) {
                int gap = thin, uy = y + g_lineH - 2 * gap;
                if (uy < y + g_ascent + gap) uy = y + g_ascent + gap;
                int ci = 0, k = 0;
                while (k < g_clen) {
                    while (ci + 1 < g_nccl && (int)g_ccl[ci + 1] <= k) ci++;
                    int cend = (ci + 1 < g_nccl) ? (int)g_ccl[ci + 1] : g_clen;
                    if (cend > g_clen || cend <= k) cend = g_clen;
                    BYTE at = g_cattr[k];
                    int m = k + 1;
                    while (m < cend && g_cattr[m] == at) m++;
                    int ua = co + k, ub = co + m;
                    if (ua < va) ua = va;
                    if (ub > vb) ub = vb;
                    if (ub > ua) {
                        int x0 = LX(ua) + ox + (ua == co + k ? gap : 0), x1 = LX(ub) + ox - (ub == co + m ? gap : 0);
                        if (x1 <= x0) x1 = x0 + 1;
                        DrawUnderline(dc, x0, x1, uy, at, at == ATTR_INPUT_ERROR ? RGB(255, 80, 80) : C_TEXT);
                    }
                    k = m;
                }
            }
        }
        L++; r = 0;
    }
}
/* everything the picture depends on, except what Invalidate() reports */
typedef struct {
    size_t top, sa, sb, ma, mb; int topRow, sx, cw, ch, mdTop;
    BOOL wrap, ws, md, findOpen, comp, focus;
    unsigned docVer, compVer, layoutVer, findVer; const void *re;
} ViewKey;
static HDC g_bb; static HBITMAP g_bbBmp; static int g_bbW, g_bbH;
static ViewKey g_vk;   /* the back buffer shows g_vk unless dirty */
static void ViewKeyNow(ViewKey *k) {
    memset(k, 0, sizeof *k);
    k->top = g_top; k->topRow = g_topRow; k->sx = g_sx; k->cw = g_cw; k->ch = g_ch; k->mdTop = g_mdTop;
    if (HasSel()) { k->sa = SelA(); k->sb = SelB(); }
    k->ma = g_curMA; k->mb = g_curMB; k->wrap = g_wrap; k->ws = g_showWs; k->md = g_mdView;
    k->findOpen = g_findOpen; k->comp = g_comp; k->focus = g_focus || GetFocus() == NULL;
    k->docVer = g_docVer; k->compVer = g_compVer; k->layoutVer = g_layoutVer; k->findVer = g_findVer; k->re = g_re;
}
static void Invalidate(void) { g_dirty = TRUE; if (g_hwnd) InvalidateRect(g_hwnd, NULL, FALSE); }
/* no wrap: content width of the visible lines (provisional while a line is not measured to its end) */
static void UpdateMaxW(void) {
    if (g_wrap || g_mdView) return;
    int m = g_sx > 0 ? g_sx + g_cw - g_margin * 2 - g_caretW : 0;
    size_t L = g_top;
    for (int k = 0; k <= VisLines() && L < g_nl; k++, L++) {
        Ln ln = LnOf(L, TRUE);
        IdxAtX(&ln, g_sx + g_cw);
        int w = LineWidth(&ln); if (w > m) m = w;
    }
    g_maxW = m;
}
static void RenderStrip(int y0, int y1) {
    int sv = SaveDC(g_bb);
    IntersectClipRect(g_bb, 0, y0, g_bbW, y1);
    SelectObject(g_bb, g_font);
    FillR(g_bb, 0, y0, g_bbW, y1, C_BG);
    SetBkMode(g_bb, TRANSPARENT);
    SetTextAlign(g_bb, TA_TOP | TA_LEFT);
    if (g_mdView) MdPaint(g_bb, g_bbW, g_bbH); else PaintRows(g_bb, g_bbW, y0, y1);
    RestoreDC(g_bb, sv);
}
static void Paint(HDC hdc, const RECT *pr) {
    RECT rc; GetClientRect(g_hwnd, &rc);
    int w = rc.right, h = rc.bottom;
    if (w <= 0 || h <= 0) return;
    if (!g_bb || g_bbW != w || g_bbH != h) {   /* (re)create on resize */
        if (!g_bb) g_bb = CreateCompatibleDC(hdc);
        HBITMAP nb = CreateCompatibleBitmap(hdc, w, h);
        SelectObject(g_bb, nb);
        if (g_bbBmp) DeleteObject(g_bbBmp);
        g_bbBmp = nb; g_bbW = w; g_bbH = h; g_dirty = TRUE;
    }
    ViewKey k; ViewKeyNow(&k);
    if (g_dirty || memcmp(&k, &g_vk, sizeof k)) {
        UpdateMaxW();
        RenderStrip(0, h);
        g_vk = k; g_dirty = FALSE;
    }
    BitBlt(hdc, pr->left, pr->top, pr->right - pr->left, pr->bottom - pr->top, g_bb, pr->left, pr->top, SRCCOPY);
}
/* the view moved by d rows and nothing else changed */
static unsigned g_scrollPaths;
static void ScrollView(int d, const ViewKey *k) {
    g_scrollPaths++;
    int dy = -d * g_lineH, full = g_ch / g_lineH;
    int y0 = d > 0 ? (full - d) * g_lineH : 0, y1 = d > 0 ? g_ch : dy;
    ScrollDC(g_bb, 0, dy, NULL, NULL, NULL, NULL);
    g_vk = *k;
    int oldMax = g_maxW;
    UpdateMaxW();
    RenderStrip(y0, y1);
    ScrollWindowEx(g_hwnd, 0, dy, NULL, NULL, NULL, NULL, SW_INVALIDATE);
    RECT r = { 0, y0, g_cw, y1 }; InvalidateRect(g_hwnd, &r, FALSE);
    if (g_maxW != oldMax) UpdateScrollBars();
}
static void Refresh(BOOL ensure) {
    if (!g_hwnd) return;
    if (ensure) EnsureVisible();
    UpdateScrollBars();
    ViewKey k; ViewKeyNow(&k);
    if (g_dirty || !g_bb || g_mdView || g_bbW != g_cw || g_bbH != g_ch) InvalidateRect(g_hwnd, NULL, FALSE);
    else if (memcmp(&k, &g_vk, sizeof k)) {
        ViewKey o = g_vk; o.top = k.top; o.topRow = k.topRow;
        int vis = VisLines();
        long long d = memcmp(&o, &k, sizeof k) ? vis : RowDelta(g_vk.top, g_vk.topRow, g_top, g_topRow, vis);
        if (d > -vis && d < vis) ScrollView((int)d, &k);
        else InvalidateRect(g_hwnd, NULL, FALSE);
    }
    PlaceCaret();
}

/* ================================================================== */
/* IME messages (EDIT-compatible inline composition)                   */
/* ================================================================== */
static void ReadCompString(HIMC imc, LPARAM lp) {
    ClearComp();
    if (lp & GCS_COMPSTR) {
        LONG nb = ImmGetCompositionStringW(imc, GCS_COMPSTR, NULL, 0);
        if (nb > 0) {
            g_cstr = xrealloc(g_cstr, (size_t)nb + sizeof(WCHAR));
            nb = ImmGetCompositionStringW(imc, GCS_COMPSTR, g_cstr, (DWORD)nb);
            g_clen = nb > 0 ? (int)(nb / (LONG)sizeof(WCHAR)) : 0;
        }
    }
    g_cattr = xrealloc(g_cattr, (size_t)g_clen + 1);
    memset(g_cattr, ATTR_INPUT, (size_t)g_clen + 1);
    if ((lp & GCS_COMPATTR) && g_clen > 0) {
        LONG na = ImmGetCompositionStringW(imc, GCS_COMPATTR, NULL, 0);
        if (na > 0) {
            BYTE *t = xmalloc((size_t)na);
            na = ImmGetCompositionStringW(imc, GCS_COMPATTR, t, (DWORD)na);
            if (na > 0) memcpy(g_cattr, t, (size_t)(na < g_clen ? na : g_clen));
            free(t);
        }
    }
    if ((lp & GCS_COMPCLAUSE) && g_clen > 0) {
        LONG nc = ImmGetCompositionStringW(imc, GCS_COMPCLAUSE, NULL, 0);
        if (nc >= (LONG)(2 * sizeof(DWORD))) {
            g_ccl = xrealloc(g_ccl, (size_t)nc);
            nc = ImmGetCompositionStringW(imc, GCS_COMPCLAUSE, g_ccl, (DWORD)nc);
            g_nccl = nc > 0 ? (int)(nc / (LONG)sizeof(DWORD)) : 0;
        }
    }
    if (g_nccl < 2) { g_ccl = xrealloc(g_ccl, 2 * sizeof(DWORD)); g_ccl[0] = 0; g_ccl[1] = (DWORD)g_clen; g_nccl = 2; }
    if (lp & GCS_CURSORPOS) {
        LONG c = ImmGetCompositionStringW(imc, GCS_CURSORPOS, NULL, 0);
        g_ccur = (c < 0) ? g_clen : (int)c;
    } else g_ccur = g_clen;
    if (g_ccur > g_clen) g_ccur = g_clen;
    if (g_ccur < 0) g_ccur = 0;
    if (g_ccur > 0 && g_ccur < g_clen && IS_LO(g_cstr[g_ccur]) && IS_HI(g_cstr[g_ccur - 1])) g_ccur--;
    g_compVer++;
}
static void BeginComp(void) {
    if (g_dragging) { g_dragging = FALSE; ReleaseCapture(); }
    NewGroup(); BreakUndoMerge();
    if (HasSel()) DeleteSelection();
    g_comp = TRUE; ClearComp(); g_cpos = g_caret; g_aff = FALSE;
    UpdateTitle();
}
static void OnStartComposition(void) {
    if (g_mdView) return;
    BeginComp();
    SetImeFont();
    Refresh(TRUE);
}
static void OnComposition(LPARAM lp) {
    if (g_mdView) return;
    HIMC imc = ImmGetContext(g_hwnd);
    if (!imc) return;
    if (!g_comp) BeginComp();
    if (lp & GCS_RESULTSTR) {
        LONG nb = ImmGetCompositionStringW(imc, GCS_RESULTSTR, NULL, 0);
        if (nb > 0) {
            WCHAR *r = xmalloc((size_t)nb + sizeof(WCHAR));
            nb = ImmGetCompositionStringW(imc, GCS_RESULTSTR, r, (DWORD)nb);
            if (nb > 0) {
                size_t n = NormalizeNewlines(r, (size_t)nb / sizeof(WCHAR));
                InsertText(r, n, K_IME);
            }
            free(r);
        }
    }
    ReadCompString(imc, lp);
    g_cpos = g_caret;
    ImmReleaseContext(g_hwnd, imc);
    UpdateTitle();
    Refresh(TRUE);
}
static void OnEndComposition(void) {
    g_comp = FALSE; ClearComp();
    BreakUndoMerge(); NewGroup();
    Refresh(TRUE);
}
static LRESULT BuildReconvert(RECONVERTSTRING *rs, BOOL docfeed) {
    size_t base, slen, coff, clen;
    WCHAR *tmp; BOOL own = FALSE;
    if (docfeed && g_comp && g_clen > 0) {
        size_t L = LineOf(g_cpos);
        int n = LayoutLine(L, TRUE);
        slen = (size_t)n; coff = (size_t)g_ln.co; clen = (size_t)g_clen; base = LineStart(L);
        tmp = xmalloc((slen + 1) * sizeof(WCHAR)); own = TRUE;
        LnGet(&g_ln, 0, n, tmp);
    } else {
        BOOL sel = HasSel() && !docfeed;
        size_t a = sel ? SelA() : g_caret, b = sel ? SelB() : g_caret;
        size_t La = LineOf(a), Lb = LineOf(b);
        if (La == Lb) { base = LineStart(La); slen = LineEnd(La) - base; }
        else { base = a; slen = b - a; }
        const size_t WIN = 512;
        if (slen > 2 * WIN + (b - a)) {
            size_t ns = a > base + WIN ? a - WIN : base;
            size_t ne = b + WIN < base + slen ? b + WIN : base + slen;
            if (ns > base && IS_LO(DocAt(ns))) ns--;
            if (ne < base + slen && IS_LO(DocAt(ne))) ne++;
            slen = ne - ns; base = ns;
        }
        coff = a - base; clen = b - a;
        tmp = xmalloc((slen + 1) * sizeof(WCHAR)); own = TRUE;
        DocGet(base, slen, tmp);
    }
    DWORD need = (DWORD)(sizeof(RECONVERTSTRING) + (slen + 1) * sizeof(WCHAR));
    if (rs) {
        if (rs->dwSize < need) { if (own) free(tmp); return 0; }
        rs->dwSize = need; rs->dwVersion = 0;
        rs->dwStrLen = (DWORD)slen; rs->dwStrOffset = sizeof(RECONVERTSTRING);
        rs->dwCompStrLen = (DWORD)clen; rs->dwCompStrOffset = (DWORD)(coff * sizeof(WCHAR));
        rs->dwTargetStrLen = (DWORD)clen; rs->dwTargetStrOffset = (DWORD)(coff * sizeof(WCHAR));
        WCHAR *d = (WCHAR *)((BYTE *)rs + sizeof(RECONVERTSTRING));
        memcpy(d, tmp, slen * sizeof(WCHAR)); d[slen] = 0;
        if (!docfeed) { g_reconvBase = base; g_reconvLen = slen; g_reconvValid = TRUE; }
    }
    if (own) free(tmp);
    return (LRESULT)need;
}
static LRESULT OnImeRequest(WPARAM wp, LPARAM lp) {
    if (g_mdView) return 0;
    switch (wp) {
    case IMR_COMPOSITIONWINDOW: {
        COMPOSITIONFORM *cf = (COMPOSITIONFORM *)lp;
        POINT cp; int x0, x1, y; ImeGeometry(&cp, &x0, &x1, &y);
        cf->dwStyle = CFS_POINT; cf->ptCurrentPos = cp; SetRect(&cf->rcArea, 0, 0, g_cw, g_ch);
        return 1;
    }
    case IMR_CANDIDATEWINDOW: {
        CANDIDATEFORM *cd = (CANDIDATEFORM *)lp;
        if (cd->dwIndex != 0) return 0;
        POINT cp; int x0, x1, y; ImeGeometry(&cp, &x0, &x1, &y);
        cd->dwStyle = CFS_EXCLUDE; cd->ptCurrentPos.x = x0; cd->ptCurrentPos.y = y;
        SetRect(&cd->rcArea, x0, y, x1, y + g_lineH);
        return 1;
    }
    case IMR_COMPOSITIONFONT:
        *(LOGFONTW *)lp = g_lf; return 1;
    case IMR_QUERYCHARPOSITION: {
        IMECHARPOSITION *cp = (IMECHARPOSITION *)lp;
        if (cp->dwSize < sizeof(IMECHARPOSITION)) return 0;
        size_t L; int idx;
        if (g_comp && g_clen > 0) {
            L = LineOf(g_cpos); LayoutLine(L, TRUE);
            DWORD k = cp->dwCharPos; if (k > (DWORD)g_clen) k = (DWORD)g_clen;
            idx = g_ln.co + (int)k;
        } else {
            size_t base = HasSel() ? SelA() : g_caret;
            L = LineOf(base);
            size_t p = base + cp->dwCharPos, e = LineEnd(L); if (p > e) p = e;
            idx = (int)(p - LineStart(L));
        }
        POINT pt; IdxPoint(L, idx, &pt);
        ClientToScreen(g_hwnd, &pt);
        cp->pt = pt; cp->cLineHeight = (UINT)g_lineH;
        RECT r; GetClientRect(g_hwnd, &r);
        MapWindowPoints(g_hwnd, NULL, (POINT *)&r, 2);
        cp->rcDocument = r;
        return 1;
    }
    case IMR_RECONVERTSTRING:
        if (g_comp) return 0;
        return BuildReconvert((RECONVERTSTRING *)lp, FALSE);
    case IMR_CONFIRMRECONVERTSTRING: {
        RECONVERTSTRING *rs = (RECONVERTSTRING *)lp;
        if (!rs || !g_reconvValid || g_comp) return 0;
        if (rs->dwStrLen != g_reconvLen) return 0;
        size_t off = rs->dwCompStrOffset / sizeof(WCHAR), n = rs->dwCompStrLen;
        if (off > g_reconvLen || n > g_reconvLen - off) return 0;
        size_t a = g_reconvBase + off, b = a + n;
        if (b > DocLen()) return 0;
        g_anchor = a; g_caret = b; g_wantX = -1; g_aff = FALSE;
        Refresh(TRUE);
        return 1;
    }
    case IMR_DOCUMENTFEED:
        return BuildReconvert((RECONVERTSTRING *)lp, TRUE);
    }
    return 0;
}
static void StartReconversion(void) {
    HIMC imc = ImmGetContext(g_hwnd);
    if (!imc) return;
    LRESULT sz = BuildReconvert(NULL, FALSE);
    RECONVERTSTRING *rs = calloc(1, (size_t)sz);
    if (rs) {
        rs->dwSize = (DWORD)sz;
        if (BuildReconvert(rs, FALSE) &&
            ImmSetCompositionStringW(imc, SCS_QUERYRECONVERTSTRING, rs, (DWORD)sz, NULL, 0)) {
            OnImeRequest(IMR_CONFIRMRECONVERTSTRING, (LPARAM)rs);
            ImmSetCompositionStringW(imc, SCS_SETRECONVERTSTRING, rs, (DWORD)sz, NULL, 0);
        }
        free(rs);
    }
    ImmReleaseContext(g_hwnd, imc);
}

/* ================================================================== */
/* find / replace on the document                                      */
/* ================================================================== */
static HWND g_edFind, g_edRepl;
static HBRUSH g_brInput;
static void SetFindStatus(const WCHAR *s) {
    wcsncpy(g_findStatus, s ? s : L"", sizeof g_findStatus / sizeof g_findStatus[0] - 1);
    if (g_find) { FrameLayout(); InvalidateRect(g_find, NULL, FALSE); }
}
static WCHAR *GetEditText(HWND e, int *n) {
    int len = GetWindowTextLengthW(e);
    WCHAR *t = xmalloc(((size_t)len + 1) * sizeof(WCHAR));
    GetWindowTextW(e, t, len + 1);
    *n = (int)wcslen(t);
    return t;
}
static void FindCompile(void) {
    re_free(g_re); g_re = NULL; g_reLiteral = FALSE;
    g_findVer++;
    if (!g_edFind) return;
    int n; WCHAR *t = GetEditText(g_edFind, &n);
    if (n > 0) {
        int flags = g_matchCase ? 0 : RE_ICASE, ep = 0;
        g_re = re_compile((const rechar *)t, n, flags, &ep);
        if (!g_re) { g_re = re_compile((const rechar *)t, n, flags | RE_LITERAL, &ep); g_reLiteral = TRUE; }
    }
    free(t);
    SetFindStatus(g_reLiteral ? L"正規表現として無効なため文字列として検索します" : L"");
    if (g_hwnd) Invalidate();
}
static void SelectMatch(size_t a, size_t b) {
    g_anchor = a; g_caret = b; g_aff = FALSE; g_wantX = -1;
    g_curMA = a; g_curMB = b;
    BreakUndoMerge();
    Refresh(TRUE);
}
/* finds next/previous non-empty match starting from the selection; wraps around */
static BOOL FindFrom(size_t start, BOOL forward, size_t *ma, size_t *mb) {
    if (!g_re || g_nl == 0) return FALSE;
    int caps[2 * RE_NCAP];
    size_t L0 = LineOf(start); int off0 = (int)(start - LineStart(L0));
    for (size_t i = 0; i <= g_nl; i++) {
        size_t L = forward ? (L0 + i) % g_nl : (L0 + g_nl - (i % g_nl)) % g_nl;
        int n; const WCHAR *t = LineText(L, &n);
        if (forward) {
            int s = (i == 0) ? off0 : 0;
            while (s <= n && re_search(g_re, (const rechar *)t, n, s, caps)) {
                if (i == g_nl && caps[0] >= off0) break;
                if (caps[1] > caps[0]) { *ma = LineStart(L) + (size_t)caps[0]; *mb = LineStart(L) + (size_t)caps[1]; return TRUE; }
                s = caps[0] + 1;
            }
        } else {
            int limit = (i == 0) ? off0 : INT_MAX, lo = (i == g_nl) ? off0 : -1, s = 0, fa = -1, fb = -1;
            while (s <= n && re_search(g_re, (const rechar *)t, n, s, caps)) {
                if (caps[0] >= limit) break;
                if (caps[1] > caps[0] && caps[0] >= lo) { fa = caps[0]; fb = caps[1]; }
                s = caps[1] > caps[0] ? caps[1] : caps[0] + 1;
            }
            if (fa >= 0) { *ma = LineStart(L) + (size_t)fa; *mb = LineStart(L) + (size_t)fb; return TRUE; }
        }
    }
    return FALSE;
}
static BOOL FindNext(BOOL forward) {
    if (!g_re) FindCompile();
    if (!g_re) { if (!g_findOpen) FindShow(FALSE); return FALSE; }
    size_t a, b;
    HCURSOR oc = SetCursor(LoadCursorW(NULL, IDC_WAIT));
    BOOL ok = FindFrom(forward ? SelB() : SelA(), forward, &a, &b);
    SetCursor(oc);
    if (ok) { SelectMatch(a, b); if (!g_reLiteral) SetFindStatus(L""); }
    else { MessageBeep(MB_ICONWARNING); SetFindStatus(L"見つかりません"); }
    return ok;
}
static WCHAR *ExpandReplacement(const WCHAR *t, const int *caps, int *outn) {
    int rn; WCHAR *rp = GetEditText(g_edRepl, &rn);
    int n = re_expand((const rechar *)rp, rn, (const rechar *)t, caps, NULL, 0);
    WCHAR *o = xmalloc(((size_t)n + 1) * sizeof(WCHAR));
    re_expand((const rechar *)rp, rn, (const rechar *)t, caps, (rechar *)o, n);
    free(rp);
    *outn = n;
    return o;
}
static void DoReplace(void) {
    if (!g_re) FindCompile();
    if (!g_re) return;
    if (HasSel() && LineOf(SelA()) == LineOf(SelB())) {
        size_t L = LineOf(SelA()), s = LineStart(L);
        int n; const WCHAR *t = LineText(L, &n);
        int caps[2 * RE_NCAP], off = (int)(SelA() - s);
        if (re_search(g_re, (const rechar *)t, n, off, caps) && caps[0] == off && (size_t)caps[1] == SelB() - s) {
            int rn; WCHAR *rep = ExpandReplacement(t, caps, &rn);
            NewGroup();
            size_t a = SelA();
            DeleteSelection();
            EditInsert(a, rep, (size_t)rn);
            free(rep);
            g_caret = g_anchor = a + (size_t)rn;
            BreakUndoMerge(); NewGroup();
            UpdateTitle();
        }
    }
    FindNext(TRUE);
}
static void DoReplaceAll(void) {
    if (!g_re) FindCompile();
    if (!g_re) return;
    HCURSOR oc = SetCursor(LoadCursorW(NULL, IDC_WAIT));
    WCHAR *out = NULL; size_t on = 0, ocap = 0, keep = 0;
    long long first = -1, count = 0;
    int caps[2 * RE_NCAP];
#define OUTAPP(src, cnt) do { size_t c_ = (cnt); if (on + c_ + 1 > ocap) { ocap = (on + c_ + 1) * 2; out = xrealloc(out, ocap * sizeof(WCHAR)); } memcpy(out + on, (src), c_ * sizeof(WCHAR)); on += c_; } while (0)
    size_t lastL = 0;
    for (size_t L = 0; L < g_nl; L++) {
        int n; const WCHAR *t = LineText(L, &n);
        int s = 0, copied = 0; BOOL any = FALSE;
        while (s <= n && re_search(g_re, (const rechar *)t, n, s, caps)) {
            if (caps[1] == caps[0]) { s = caps[0] + 1; continue; }
            if (first < 0) { first = (long long)L; }
            any = TRUE;
            OUTAPP(t + copied, (size_t)(caps[0] - copied));
            int rn; WCHAR *rep = ExpandReplacement(t, caps, &rn);
            OUTAPP(rep, (size_t)rn); free(rep);
            copied = caps[1]; s = caps[1]; count++;
        }
        if (first < 0) continue;
        OUTAPP(t + copied, (size_t)(n - copied));
        if (any) { keep = on; lastL = L; }
        if (L + 1 < g_nl) OUTAPP(L"\n", 1);
    }
#undef OUTAPP
    SetCursor(oc);
    if (count == 0) { free(out); MessageBeep(MB_ICONWARNING); SetFindStatus(L"見つかりません"); return; }
    size_t a = LineStart((size_t)first), b = LineEnd(lastL);
    NewGroup();
    EditDelete(a, b - a);
    EditInsert(a, out, keep);
    BreakUndoMerge(); NewGroup();
    free(out);
    g_caret = g_anchor = a; g_aff = FALSE;
    WCHAR msg[64]; _snwprintf(msg, 64, L"%lld 件置換しました", count); msg[63] = 0;
    SetFindStatus(msg);
    UpdateTitle(); Refresh(TRUE);
}

/* ================================================================== */
/* find popup window                                                   */
/* ================================================================== */
enum { H_NONE, H_FOLD, H_MAG, H_CASE, H_NEXT, H_PREV, H_CLOSE, H_REP, H_REPALL };
static int g_fHover, g_fPress;
#define FP_W 440
static void FindRects(RECT *r) {   /* r[H_*] in popup client coords */
    int pad = Sc(5), rowH = Sc(30), fold = Sc(22), btn = Sc(26), ck = Sc(32), W = Sc(FP_W);
    int y1 = pad, y2 = pad + rowH + pad;
    for (int i = 0; i <= H_REPALL; i++) SetRectEmpty(&r[i]);
    SetRect(&r[H_FOLD], pad, y1, pad + fold, g_findExpanded ? y2 + rowH : y1 + rowH);
    int xr = W - pad;
    SetRect(&r[H_CLOSE], xr - btn, y1, xr, y1 + rowH); xr -= btn + Sc(2);
    SetRect(&r[H_PREV], xr - btn, y1, xr, y1 + rowH); xr -= btn + Sc(2);
    SetRect(&r[H_NEXT], xr - btn, y1, xr, y1 + rowH); xr -= btn + Sc(4);
    SetRect(&r[H_CASE], xr - ck, y1 + Sc(2), xr, y1 + rowH - Sc(2)); xr -= ck + Sc(4);
    int x1 = pad + fold + Sc(4);
    SetRect(&r[H_MAG], xr - Sc(26), y1, xr, y1 + rowH);   /* inside the find box, right end */
    r[0].left = x1; r[0].right = xr; r[0].top = y1; r[0].bottom = y1 + rowH;   /* find box */
    if (g_findExpanded) {
        int xr2 = W - pad;
        SetRect(&r[H_REPALL], xr2 - Sc(76), y2 + Sc(2), xr2, y2 + rowH - Sc(2)); xr2 -= Sc(76) + Sc(4);
        SetRect(&r[H_REP], xr2 - Sc(50), y2 + Sc(2), xr2, y2 + rowH - Sc(2));
    }
}
static int FindPopupH(void) {
    int pad = Sc(5), rowH = Sc(30);
    int h = pad + rowH + pad;
    if (g_findExpanded) h += rowH + pad;
    if (g_findStatus[0]) h += Sc(18);
    return h;
}
static void FindLayoutChildren(void) {
    RECT r[H_REPALL + 1]; FindRects(r);
    int eh = Sc(20);
    RECT fb = r[0];
    MoveWindow(g_edFind, fb.left + Sc(6), fb.top + (fb.bottom - fb.top - eh) / 2, r[H_MAG].left - fb.left - Sc(8), eh, TRUE);
    if (g_findExpanded) {
        int pad = Sc(5), rowH = Sc(30), y2 = pad + rowH + pad;
        int right = r[H_REP].left - Sc(4);
        MoveWindow(g_edRepl, fb.left + Sc(6), y2 + (rowH - eh) / 2, right - fb.left - Sc(12), eh, TRUE);
        ShowWindow(g_edRepl, SW_SHOW);
    } else ShowWindow(g_edRepl, SW_HIDE);
    SendMessageW(g_edFind, EM_SETCUEBANNER, TRUE, (LPARAM)(g_findExpanded ? L"置換前" : L"検索"));
    SendMessageW(g_edRepl, EM_SETCUEBANNER, TRUE, (LPARAM)L"置換後");
}
static void DrawChevron(HDC dc, int cx, int cy, int s, int dir, COLORREF c) {  /* dir 0 down 1 up 2 right */
    int u = Sc(1) > 0 ? Sc(1) : 1;
    for (int k = 0; k <= s; k++) {
        int a = k, b = s - k;
        if (dir == 0) { FillR(dc, cx - s + a, cy - s / 2 + a, cx - s + a + u + 1, cy - s / 2 + a + u + 1, c); FillR(dc, cx + b - 1, cy - s / 2 + a, cx + b + u, cy - s / 2 + a + u + 1, c); }
        else if (dir == 1) { FillR(dc, cx - s + a, cy + s / 2 - a, cx - s + a + u + 1, cy + s / 2 - a + u + 1, c); FillR(dc, cx + b - 1, cy + s / 2 - a, cx + b + u, cy + s / 2 - a + u + 1, c); }
        else { FillR(dc, cx - s / 2 + a, cy - s + a, cx - s / 2 + a + u + 1, cy - s + a + u + 1, c); FillR(dc, cx - s / 2 + a, cy + b - 1, cx - s / 2 + a + u + 1, cy + b + u, c); }
    }
}
static void DrawX(HDC dc, int cx, int cy, int s, COLORREF c) {
    int u = Sc(1) > 0 ? Sc(1) : 1;
    for (int k = -s; k <= s; k++) { FillR(dc, cx + k, cy + k, cx + k + u + 1, cy + k + u + 1, c); FillR(dc, cx + k, cy - k, cx + k + u + 1, cy - k + u + 1, c); }
}
static void DrawMagnifier(HDC dc, int cx, int cy, COLORREF c) {
    int rr = Sc(5), u = Sc(1) > 0 ? Sc(1) : 1;
    HPEN pen = CreatePen(PS_SOLID, u + (u > 1), c); HGDIOBJ op = SelectObject(dc, pen);
    HGDIOBJ obr = SelectObject(dc, GetStockObject(NULL_BRUSH));
    Ellipse(dc, cx - rr - Sc(2), cy - rr - Sc(2), cx + rr - Sc(2), cy + rr - Sc(2));
    MoveToEx(dc, cx + rr / 2, cy + rr / 2, NULL); LineTo(dc, cx + rr + Sc(1), cy + rr + Sc(1));
    SelectObject(dc, obr); SelectObject(dc, op); DeleteObject(pen);
}
static void FindPaint(HWND h) {
    PAINTSTRUCT ps; HDC hdc = BeginPaint(h, &ps);
    RECT rc; GetClientRect(h, &rc);
    HDC dc = CreateCompatibleDC(hdc);
    HBITMAP bmp = CreateCompatibleBitmap(hdc, rc.right, rc.bottom);
    HGDIOBJ ob = SelectObject(dc, bmp), of = SelectObject(dc, g_uiFont);
    SetBkMode(dc, TRANSPARENT);
    COLORREF bg = g_mdView ? C_FRAME_MD : C_FRAME, hov = RGB(0x60, 0x1C, 0x22), prs = RGB(0x80, 0x2C, 0x34), bord = RGB(0x7A, 0x3A, 0x3E);
    FillR(dc, 0, 0, rc.right, rc.bottom, bord);
    FillR(dc, 1, 1, rc.right - 1, rc.bottom - 1, bg);
    RECT r[H_REPALL + 1]; FindRects(r);
    /* input boxes */
    FillR(dc, r[0].left, r[0].top, r[0].right, r[0].bottom, bord);
    FillR(dc, r[0].left + 1, r[0].top + 1, r[0].right - 1, r[0].bottom - 1, C_INPUT_BG);
    if (g_findExpanded) {
        int pad = Sc(5), rowH = Sc(30), y2 = pad + rowH + pad, right = r[H_REP].left - Sc(4);
        FillR(dc, r[0].left, y2, right, y2 + rowH, bord);
        FillR(dc, r[0].left + 1, y2 + 1, right - 1, y2 + rowH - 1, C_INPUT_BG);
    }
    for (int i = H_FOLD; i <= H_REPALL; i++) {
        if (IsRectEmpty(&r[i])) continue;
        RECT b = r[i];
        BOOL on = (i == H_CASE && g_matchCase);
        COLORREF c = (g_fPress == i) ? prs : (g_fHover == i ? hov : (i == H_MAG ? C_INPUT_BG : bg));
        if (on) c = RGB(0x8A, 0x3A, 0x40);
        if (i == H_REP || i == H_REPALL) { FillR(dc, b.left, b.top, b.right, b.bottom, bord); FillR(dc, b.left + 1, b.top + 1, b.right - 1, b.bottom - 1, g_fPress == i ? prs : (g_fHover == i ? hov : RGB(0x52, 0x10, 0x16))); }
        else if (i == H_MAG) FillR(dc, b.left + 1, b.top + 1, b.right - 1, b.bottom - 1, c);
        else FillR(dc, b.left, b.top, b.right, b.bottom, c);
        if (on) { FillR(dc, b.left, b.bottom - Sc(2), b.right, b.bottom, C_DOT); }
        int cx = (b.left + b.right) / 2, cy = (b.top + b.bottom) / 2, s = Sc(4);
        SetTextColor(dc, C_CAPTEXT);
        switch (i) {
        case H_FOLD: DrawChevron(dc, cx, Sc(5) + Sc(15), s, g_findExpanded ? 0 : 2, C_CAPTEXT); break;
        case H_NEXT: DrawChevron(dc, cx, cy, s, 0, C_CAPTEXT); break;
        case H_PREV: DrawChevron(dc, cx, cy, s, 1, C_CAPTEXT); break;
        case H_CLOSE: DrawX(dc, cx, cy, s, C_CAPTEXT); break;
        case H_MAG: DrawMagnifier(dc, cx, cy, C_INPUT_TX); break;
        default: {
            const WCHAR *t = i == H_CASE ? L"Aa" : (i == H_REP ? L"置換" : L"全て置換");
            DrawTextW(dc, t, -1, &b, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        }
        }
    }
    if (g_findStatus[0]) {
        RECT sr = { r[0].left, rc.bottom - Sc(19), rc.right - Sc(6), rc.bottom - Sc(2) };
        SetTextColor(dc, RGB(0xE8, 0xB0, 0x90));
        DrawTextW(dc, g_findStatus, -1, &sr, DT_LEFT | DT_VCENTER | DT_SINGLELINE | DT_END_ELLIPSIS);
    }
    BitBlt(hdc, 0, 0, rc.right, rc.bottom, dc, 0, 0, SRCCOPY);
    SelectObject(dc, of); SelectObject(dc, ob); DeleteObject(bmp); DeleteDC(dc);
    EndPaint(h, &ps);
}
static int FindHit(int x, int y) {
    RECT r[H_REPALL + 1]; FindRects(r); POINT p = { x, y };
    for (int i = H_FOLD; i <= H_REPALL; i++) if (!IsRectEmpty(&r[i]) && PtInRect(&r[i], p)) return i;
    return H_NONE;
}
static void FindAction(int hit) {
    switch (hit) {
    case H_FOLD: g_findExpanded = !g_findExpanded; FrameLayout(); FindLayoutChildren(); InvalidateRect(g_find, NULL, FALSE);
        SetFocus(g_findExpanded ? g_edRepl : g_edFind); break;
    case H_MAG: case H_NEXT: FindNext(TRUE); break;
    case H_PREV: FindNext(FALSE); break;
    case H_CASE: g_matchCase = !g_matchCase; FindCompile(); InvalidateRect(g_find, NULL, FALSE); break;
    case H_CLOSE: FindHide(); break;
    case H_REP: DoReplace(); break;
    case H_REPALL: DoReplaceAll(); break;
    }
}
static LRESULT CALLBACK EditSubProc(HWND h, UINT m, WPARAM wp, LPARAM lp, UINT_PTR id, DWORD_PTR ref) {
    (void)ref;
    BOOL ctrl = GetKeyState(VK_CONTROL) < 0, shift = GetKeyState(VK_SHIFT) < 0, alt = GetKeyState(VK_MENU) < 0;
    switch (m) {
    case WM_SETFOCUS: g_lastFocus = h; break;
    case WM_KEYDOWN:
        if (wp == VK_RETURN) { if (id == 2) DoReplace(); else FindNext(!shift); return 0; }
        if (wp == VK_ESCAPE) { FindHide(); return 0; }
        if (wp == VK_F3) { FindNext(!shift); return 0; }
        if (wp == VK_TAB) { if (g_findExpanded) SetFocus(h == g_edFind ? g_edRepl : g_edFind); return 0; }
        if (ctrl && !alt) {
            if (wp == 'F') { FindShow(FALSE); return 0; }
            if (wp == 'H') { FindShow(TRUE); return 0; }
            if (wp == 'A') { SendMessageW(h, EM_SETSEL, 0, -1); return 0; }
        }
        break;
    case WM_CHAR:
        if (wp == L'\r' || wp == 0x1B || wp == L'\t') return 0;
        if (ctrl && !alt && (wp < 0x20 || wp == 0x7F)) return 0;
        break;
    case WM_NCDESTROY: RemoveWindowSubclass(h, EditSubProc, id); break;
    }
    return DefSubclassProc(h, m, wp, lp);
}
static LRESULT CALLBACK FindProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CREATE: {
        g_edFind = CreateWindowExW(0, L"EDIT", L"", WS_CHILD | WS_VISIBLE | ES_AUTOHSCROLL, 0, 0, 10, 10, h, (HMENU)1, g_inst, NULL);
        g_edRepl = CreateWindowExW(0, L"EDIT", L"", WS_CHILD | ES_AUTOHSCROLL, 0, 0, 10, 10, h, (HMENU)2, g_inst, NULL);
        SetWindowSubclass(g_edFind, EditSubProc, 1, 0);
        SetWindowSubclass(g_edRepl, EditSubProc, 2, 0);
        return 0;
    }
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: FindPaint(h); return 0;
    case WM_CTLCOLOREDIT:
        SetTextColor((HDC)wp, C_INPUT_TX); SetBkColor((HDC)wp, C_INPUT_BG);
        return (LRESULT)g_brInput;
    case WM_COMMAND:
        if (LOWORD(wp) == 1 && HIWORD(wp) == EN_CHANGE) FindCompile();
        return 0;
    case WM_MOUSEMOVE: {
        int hit = FindHit(GET_X_LPARAM(lp), GET_Y_LPARAM(lp));
        if (hit != g_fHover) { g_fHover = hit; InvalidateRect(h, NULL, FALSE); }
        TRACKMOUSEEVENT t = { sizeof t, TME_LEAVE, h, 0 }; TrackMouseEvent(&t);
        return 0;
    }
    case WM_MOUSELEAVE: g_fHover = H_NONE; g_fPress = H_NONE; InvalidateRect(h, NULL, FALSE); return 0;
    case WM_LBUTTONDOWN: g_fPress = FindHit(GET_X_LPARAM(lp), GET_Y_LPARAM(lp)); SetCapture(h); InvalidateRect(h, NULL, FALSE); return 0;
    case WM_LBUTTONUP: {
        int hit = FindHit(GET_X_LPARAM(lp), GET_Y_LPARAM(lp)), p = g_fPress;
        g_fPress = H_NONE; ReleaseCapture(); InvalidateRect(h, NULL, FALSE);
        if (hit == p && hit != H_NONE) FindAction(hit);
        return 0;
    }
    case WM_SETCURSOR:
        if (LOWORD(lp) == HTCLIENT && (HWND)wp == h) { SetCursor(LoadCursorW(NULL, IDC_ARROW)); return TRUE; }
        break;
    }
    return DefWindowProcW(h, m, wp, lp);
}
static void FindShow(BOOL expanded) {
    CompleteComposition();
    g_findOpen = TRUE; g_findExpanded = expanded;
    if (HasSel() && LineOf(SelA()) == LineOf(SelB()) && SelB() - SelA() < 256) {
        size_t n = SelB() - SelA(); WCHAR *t = xmalloc((n + 1) * sizeof(WCHAR));
        DocGet(SelA(), n, t); t[n] = 0;
        SetWindowTextW(g_edFind, t); free(t);
    }
    FrameLayout(); FindLayoutChildren();
    ShowWindow(g_find, SW_SHOW);
    InvalidateRect(g_find, NULL, FALSE);
    SetFocus(expanded && GetWindowTextLengthW(g_edFind) > 0 ? g_edRepl : g_edFind);
    SendMessageW(GetFocus(), EM_SETSEL, 0, -1);
    FindCompile();
}
static void FindHide(void) {
    g_findOpen = FALSE;
    ShowWindow(g_find, SW_HIDE);
    SetFindStatus(L"");
    SetFocus(g_hwnd);
    Invalidate();
}

/* ================================================================== */
/* Markdown view (read-only; newlines are kept as-is, no soft-break    */
/* joining). Layout = display list of items, built once per            */
/* (document version, width, font) and painted for the visible part.   */
/* ================================================================== */
enum { MI_TEXT, MI_FILL, MI_BULLET };
typedef struct { int x, y, w, h; BYTE type, font, kind; COLORREF col; int ts, tl; } MdItem;
static MdItem *g_mi; static int g_nmi, g_micap;
static WCHAR *g_mpool; static size_t g_mpn, g_mpcap;
static BOOL g_mdValid; static unsigned g_mdDV, g_mdLV; static int g_mdW;
static HFONT g_mdFonts[7 * 32]; static int g_mdAsc[7 * 32], g_mdDesc[7 * 32];
static int *g_mdx; static size_t g_mdxcap;
enum { S_B = 1, S_I = 2, S_U = 4, S_S = 8, S_CODE = 16, S_LINK = 32, S_HIDE = 64 };

static void MdInvalidate(void) { g_mdValid = FALSE; }
static void MdFreeFonts(void) { for (int i = 0; i < 7 * 32; i++) if (g_mdFonts[i]) { DeleteObject(g_mdFonts[i]); g_mdFonts[i] = NULL; } }
static int MdFontIdx(int size, int fl) { return size * 32 + (fl & 31); }
static HFONT MdFont(int idx) {
    if (g_mdFonts[idx]) return g_mdFonts[idx];
    static const int mul[7] = { 100, 200, 160, 135, 120, 105, 95 };
    int size = idx / 32, fl = idx % 32;
    LOGFONTW lf = g_lf;
    lf.lfHeight = -MulDiv(-g_lf.lfHeight, mul[size], 100);
    lf.lfWeight = (fl & 1) || size > 0 ? FW_BOLD : FW_NORMAL;
    lf.lfItalic = (fl & 2) ? TRUE : FALSE;
    lf.lfUnderline = (fl & 4) ? TRUE : FALSE;
    lf.lfStrikeOut = (fl & 8) ? TRUE : FALSE;
    if (fl & 16) { wcscpy(lf.lfFaceName, L"MS Gothic"); lf.lfPitchAndFamily = FIXED_PITCH | FF_MODERN; }
    else if (g_fontIdx <= 1 || g_fontIdx == 4) { wcscpy(lf.lfFaceName, L"Yu Gothic UI"); lf.lfPitchAndFamily = VARIABLE_PITCH | FF_SWISS; }
    g_mdFonts[idx] = CreateFontIndirectW(&lf);
    HGDIOBJ o = SelectObject(g_hdcM, g_mdFonts[idx]);
    TEXTMETRICW tm; GetTextMetricsW(g_hdcM, &tm);
    g_mdAsc[idx] = tm.tmAscent; g_mdDesc[idx] = tm.tmDescent + tm.tmExternalLeading;
    SelectObject(g_hdcM, o);
    return g_mdFonts[idx];
}
static int MdAddItem(int type, int x, int y, int w, int h, int font, COLORREF col, const WCHAR *t, int tl) {
    if (g_nmi == g_micap) { g_micap = g_micap ? g_micap * 2 : 1024; g_mi = xrealloc(g_mi, (size_t)g_micap * sizeof(MdItem)); }
    MdItem *it = &g_mi[g_nmi];
    it->type = (BYTE)type; it->x = x; it->y = y; it->w = w; it->h = h; it->font = 0; it->kind = 0; it->col = col; it->ts = 0; it->tl = 0;
    if (type == MI_TEXT) {
        if (g_mpn + (size_t)tl > g_mpcap) { g_mpcap = (g_mpn + (size_t)tl) * 2 + 1024; g_mpool = xrealloc(g_mpool, g_mpcap * sizeof(WCHAR)); }
        memcpy(g_mpool + g_mpn, t, (size_t)tl * sizeof(WCHAR));
        it->ts = (int)g_mpn; it->tl = tl; g_mpn += (size_t)tl;
    }
    it->font = (BYTE)(font & 0xFF);
    /* font index can exceed 255: store high bits in kind for text */
    if (type == MI_TEXT) it->kind = (BYTE)(font >> 8);
    return g_nmi++;
}
static int MdItemFont(const MdItem *it) { return it->font | (it->kind << 8); }

/* ---------- inline parsing ---------- */
typedef struct { int pos, cnt; WCHAR ch; BYTE open, close; } MdDelim;
static BOOL MdPunct(WCHAR c) { return c < 0x80 && c > 0x20 && !((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')); }
static BOOL MdSpace(WCHAR c) { return c == ' ' || c == '\t' || c == 0 || c == 0x3000; }
static BOOL MdAlnum(WCHAR c) { return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c >= 0x80; }
typedef struct { WCHAR *t; WORD *s; int n, cap; } MdOut;
static void MdEmit(MdOut *o, WCHAR c, WORD st) {
    if (c == L'\t') { for (int i = 0; i < 3; i++) MdEmit(o, L' ', st); c = L' '; }   /* no tab glyphs */
    if (o->n == o->cap) { o->cap = o->cap ? o->cap * 2 : 256; o->t = xrealloc(o->t, (size_t)o->cap * sizeof(WCHAR)); o->s = xrealloc(o->s, (size_t)o->cap * sizeof(WORD)); }
    o->t[o->n] = c; o->s[o->n] = st; o->n++;
}
static void MdInline(const WCHAR *s, int n, WORD base, MdOut *o) {
    MdDelim *d = NULL; int nd = 0, dcap = 0;
    int i = 0;
    while (i < n) {
        WCHAR c = s[i];
        if (c == '\\' && i + 1 < n && MdPunct(s[i + 1])) { MdEmit(o, s[i + 1], base); i += 2; continue; }
        if (c == '`') {
            int k = 0; while (i + k < n && s[i + k] == '`') k++;
            int j = i + k, found = -1;
            while (j < n) {
                if (s[j] == '`') { int m = 0; while (j + m < n && s[j + m] == '`') m++; if (m == k) { found = j; break; } j += m; }
                else j++;
            }
            if (found >= 0) {
                int a = i + k, b = found;
                if (b - a >= 2 && s[a] == ' ' && s[b - 1] == ' ') { a++; b--; }
                for (int q = a; q < b; q++) MdEmit(o, s[q], (WORD)(base | S_CODE));
                i = found + k; continue;
            }
            for (int q = 0; q < k; q++) MdEmit(o, '`', base);
            i += k; continue;
        }
        if (c == '<') {
            int j = i + 1; BOOL ok = TRUE, sch = FALSE;
            while (j < n && s[j] != '>') { if (s[j] == ' ' || s[j] == '<') { ok = FALSE; break; } if (s[j] == ':' || s[j] == '@') sch = TRUE; j++; }
            if (ok && j < n && sch && j > i + 1) {
                for (int q = i + 1; q < j; q++) MdEmit(o, s[q], (WORD)(base | S_LINK | S_U));
                i = j + 1; continue;
            }
        }
        if (c == '[' || (c == '!' && i + 1 < n && s[i + 1] == '[')) {
            int st = c == '!' ? i + 1 : i, j = st + 1, depth = 0;
            while (j < n) { if (s[j] == '\\') { j += 2; continue; } if (s[j] == '[') depth++; else if (s[j] == ']') { if (depth == 0) break; depth--; } j++; }
            if (j + 1 < n && s[j] == ']' && s[j + 1] == '(') {
                int k = j + 2, pd = 0;
                while (k < n) { if (s[k] == '(') pd++; else if (s[k] == ')') { if (pd == 0) break; pd--; } k++; }
                if (k < n) {
                    MdInline(s + st + 1, j - st - 1, (WORD)(base | S_LINK), o);
                    int ua = j + 2, ub = k;
                    while (ua < ub && s[ua] == ' ') ua++;
                    int ue = ua; while (ue < ub && s[ue] != ' ') ue++;      /* drop "title" */
                    if (ue - ua >= 2 && s[ua] == '<' && s[ue - 1] == '>') { ua++; ue--; }
                    MdEmit(o, '(', (WORD)(base | S_LINK));
                    for (int q = ua; q < ue; q++) MdEmit(o, s[q], (WORD)(base | S_LINK));
                    MdEmit(o, ')', (WORD)(base | S_LINK));
                    i = k + 1; continue;
                }
            }
        }
        if (c == '*' || c == '_' || c == '~') {
            int k = 0; while (i + k < n && s[i + k] == c) k++;
            WCHAR prev = i > 0 ? s[i - 1] : 0, next = i + k < n ? s[i + k] : 0;
            BOOL open = !MdSpace(next) && (!MdPunct(next) || MdSpace(prev) || MdPunct(prev));
            BOOL close = !MdSpace(prev) && (!MdPunct(prev) || MdSpace(next) || MdPunct(next));
            if (c == '_' && MdAlnum(prev) && MdAlnum(next)) open = close = FALSE;
            if (c == '~' && k != 2) open = close = FALSE;
            if (open || close) {
                if (nd == dcap) { dcap = dcap ? dcap * 2 : 16; d = xrealloc(d, (size_t)dcap * sizeof(MdDelim)); }
                d[nd].pos = o->n; d[nd].cnt = k; d[nd].ch = c; d[nd].open = (BYTE)open; d[nd].close = (BYTE)close; nd++;
            }
            for (int q = 0; q < k; q++) MdEmit(o, c, base);
            i += k; continue;
        }
        MdEmit(o, c, base); i++;
    }
    /* process emphasis (CommonMark-like) */
    for (int di = 0; di < nd; di++) {
        while (d[di].close && d[di].cnt > 0) {
            int oi = -1;
            for (int q = di - 1; q >= 0; q--)
                if (d[q].ch == d[di].ch && d[q].open && d[q].cnt > 0 && (d[q].ch != '~' || (d[q].cnt >= 2 && d[di].cnt >= 2))) { oi = q; break; }
            if (oi < 0) break;
            int use = d[di].ch == '~' ? 2 : (d[di].cnt >= 2 && d[oi].cnt >= 2 ? 2 : 1);
            WORD bit = d[di].ch == '~' ? S_S : (use == 2 ? S_B : S_I);
            int oEnd = d[oi].pos + d[oi].cnt;
            for (int q = oEnd - use; q < oEnd; q++) o->s[q] |= S_HIDE;
            for (int q = d[di].pos; q < d[di].pos + use; q++) o->s[q] |= S_HIDE;
            for (int q = oEnd; q < d[di].pos; q++) o->s[q] |= bit;
            d[oi].cnt -= use; d[di].pos += use; d[di].cnt -= use;
            for (int q = oi + 1; q < di; q++) d[q].cnt = 0;
        }
    }
    free(d);
}

/* ---------- flow layout ---------- */
static int g_rowY, g_rowAsc, g_rowDesc, g_rowFirst, g_bodyH;
static void MdRowBegin(void) { g_rowAsc = 0; g_rowDesc = 0; g_rowFirst = g_nmi; }
static void MdRowEnd(int minH) {
    int h = g_rowAsc + g_rowDesc;
    if (h < minH) h = minH;
    if (g_rowAsc == 0) g_rowAsc = h - h / 5;
    for (int i = g_rowFirst; i < g_nmi; i++) {
        MdItem *it = &g_mi[i];
        if (it->type == MI_TEXT) it->y = g_rowY + g_rowAsc - g_mdAsc[MdItemFont(it)];
        else if (it->type == MI_FILL && it->h < 0) { it->y = g_rowY; it->h = h; }       /* code bg */
        else if (it->type == MI_BULLET) it->y = g_rowY + g_rowAsc - it->h - (g_rowAsc - it->h) / 3;
    }
    g_rowY += h;
    MdRowBegin();
}
static int MdMeasure(int font, const WCHAR *t, int n, int **dx) {
    if ((size_t)n + 1 > g_mdxcap) { g_mdxcap = (size_t)n + 256; g_mdx = xrealloc(g_mdx, g_mdxcap * sizeof(int)); }
    HGDIOBJ o = SelectObject(g_hdcM, MdFont(font));
    SIZE sz = { 0, 0 }; int fit = 0;
    if (n) GetTextExtentExPointW(g_hdcM, t, n, INT_MAX, &fit, g_mdx, &sz);
    SelectObject(g_hdcM, o);
    *dx = g_mdx;
    return sz.cx;
}
static void MdRowFont(int font) {
    MdFont(font);
    if (g_mdAsc[font] > g_rowAsc) g_rowAsc = g_mdAsc[font];
    if (g_mdDesc[font] > g_rowDesc) g_rowDesc = g_mdDesc[font];
}
/* flows styled text into rows starting at x0, wrapping to xh */
static void MdFlow(const MdOut *o, int size, COLORREF base, int x0, int xh, int maxX, BOOL forceBold) {
    int x = x0, i = 0, rowStartX = x0;
    MdRowBegin();
    if (o->n == 0) MdRowFont(MdFontIdx(size, forceBold ? S_B : 0));
    while (i < o->n) {
        if (o->s[i] & S_HIDE) { i++; continue; }
        WORD st = o->s[i];
        int j = i; while (j < o->n && o->s[j] == st) j++;
        int fl = (st & (S_B | S_I | S_U | S_S)) | ((st & S_CODE) ? 16 : 0) | (forceBold ? S_B : 0);
        int font = MdFontIdx(size, fl);
        COLORREF col = (st & S_LINK) ? C_LINK : base;
        int start = i;
        while (start < j) {
            int *dx; MdMeasure(font, o->t + start, j - start, &dx);
            int avail = maxX - x, k = 0;
            while (k < j - start && dx[k] <= avail) k++;
            if (k < j - start) {
                if (k == 0 && x > rowStartX) { MdRowEnd(g_bodyH); x = rowStartX = xh; continue; }
                if (k == 0) k = 1;
                int sp = -1;
                for (int q = k; q > 0; q--) if (o->t[start + q - 1] == ' ' && q < j - start) { sp = q; break; }
                if (sp > 0 && o->t[start + k] != ' ' && o->t[start + k] < 0x2E80) k = sp;
                if (k < j - start && IS_LO(o->t[start + k])) k++;
            }
            int wpx = k ? dx[k - 1] : 0;
            MdRowFont(font);
            if (st & S_CODE) { int f = MdAddItem(MI_FILL, x - Sc(2), 0, wpx + Sc(4), -1, 0, C_CODEBG, NULL, 0); (void)f; }
            MdAddItem(MI_TEXT, x, 0, wpx, 0, font, col, o->t + start, k);
            x += wpx; start += k;
            if (start < j) { MdRowEnd(g_bodyH); x = rowStartX = xh; while (start < j && o->t[start] == ' ') start++; }
        }
        i = j;
    }
    MdRowEnd(g_bodyH);
}
static int MdIndentCols(const WCHAR *t, int n, int *ofs) {
    int col = 0, i = 0;
    while (i < n && (t[i] == ' ' || t[i] == '\t')) { col = t[i] == '\t' ? (col / 4 + 1) * 4 : col + 1; i++; }
    *ofs = i; return col;
}
static BOOL MdIsHr(const WCHAR *t, int n) {
    int i = 0; while (i < n && t[i] == ' ') i++;
    if (i > 3 || i >= n) return FALSE;
    WCHAR c = t[i]; if (c != '*' && c != '-' && c != '_') return FALSE;
    int cnt = 0;
    for (; i < n; i++) { if (t[i] == c) cnt++; else if (t[i] != ' ' && t[i] != '\t') return FALSE; }
    return cnt >= 3;
}
/* split a table row into cells; returns count, cells as [start,end) pairs */
static int MdSplitRow(const WCHAR *t, int n, int *cs, int maxc) {
    int a = 0, b = n;
    while (a < b && (t[a] == ' ' || t[a] == '\t')) a++;
    while (b > a && (t[b - 1] == ' ' || t[b - 1] == '\t')) b--;
    if (a < b && t[a] == '|') a++;
    if (b > a && t[b - 1] == '|' && (b - 2 < a || t[b - 2] != '\\')) b--;
    int nc = 0, st = a; BOOL code = FALSE;
    for (int i = a; i <= b && nc < maxc; i++) {
        if (i < b && t[i] == '\\') { i++; continue; }
        if (i < b && t[i] == '`') code = !code;
        if (i == b || (t[i] == '|' && !code)) {
            int x = st, y = i;
            while (x < y && t[x] == ' ') x++;
            while (y > x && t[y - 1] == ' ') y--;
            cs[2 * nc] = x; cs[2 * nc + 1] = y; nc++; st = i + 1;
        }
    }
    return nc;
}
static int MdDelimRow(const WCHAR *t, int n, int *align, int maxc) {   /* returns columns or 0 */
    int cs[128]; int nc = MdSplitRow(t, n, cs, maxc < 64 ? maxc : 64);
    if (nc == 0) return 0;
    BOOL pipe = FALSE; for (int i = 0; i < n; i++) if (t[i] == '|') pipe = TRUE;
    for (int c = 0; c < nc; c++) {
        int a = cs[2 * c], b = cs[2 * c + 1];
        if (b <= a) return 0;
        BOOL l = t[a] == ':', r = t[b - 1] == ':';
        int dash = 0;
        for (int i = a + l; i < b - r; i++) { if (t[i] != '-') return 0; dash++; }
        if (dash < 1) return 0;
        align[c] = l && r ? 1 : (r ? 2 : 0);
    }
    return (pipe || nc > 1) ? nc : 0;
}
typedef struct { int markerCol, contentCol, ordered, counter; WCHAR delim; } MdList;

static void MdLayout(void) {
    int width = g_cw;
    if (g_mdValid && g_mdDV == g_docVer && g_mdLV == g_layoutVer && g_mdW == width) return;
    MdFreeFonts();
    g_nmi = 0; g_mpn = 0;
    g_mdDV = g_docVer; g_mdLV = g_layoutVer; g_mdW = width; g_mdValid = TRUE;
    int left = Sc(16), maxX = width - Sc(16);
    if (maxX < left + Sc(80)) maxX = left + Sc(80);
    MdFont(0);
    g_bodyH = g_mdAsc[0] + g_mdDesc[0] + Sc(3);
    g_rowY = Sc(10);
    BOOL inCmt = FALSE, inFence = FALSE; WCHAR fenceCh = 0; int fenceLen = 0;
    MdList stk[16]; int sp = 0;
    WCHAR *ln = NULL; size_t lncap = 0;
    MdOut o; memset(&o, 0, sizeof o);
    for (size_t L = 0; L < g_nl; L++) {
        int rn; const WCHAR *raw = LineText(L, &rn);
        /* strip <!-- comments --> (may span lines) */
        if ((size_t)rn + 1 > lncap) { lncap = (size_t)rn + 256; ln = xrealloc(ln, lncap * sizeof(WCHAR)); }
        int n = 0; BOOL hadCmt = inCmt;
        if (!inFence) {
            for (int i = 0; i < rn; ) {
                if (inCmt) { if (i + 2 < rn && raw[i] == '-' && raw[i + 1] == '-' && raw[i + 2] == '>') { inCmt = FALSE; i += 3; } else i++; continue; }
                if (i + 3 < rn && raw[i] == '<' && raw[i + 1] == '!' && raw[i + 2] == '-' && raw[i + 3] == '-') { inCmt = TRUE; hadCmt = TRUE; i += 4; continue; }
                ln[n++] = raw[i++];
            }
        } else { memcpy(ln, raw, (size_t)rn * sizeof(WCHAR)); n = rn; }
        ln[n] = 0;
        int ofs, ind = MdIndentCols(ln, n, &ofs);
        BOOL blank = (ofs == n);
        if (hadCmt && blank && !inFence) continue;            /* line consisting of a comment: hidden */
        /* fenced code */
        if (inFence) {
            int k = 0; while (ofs + k < n && ln[ofs + k] == fenceCh) k++;
            if (ind < 4 && k >= fenceLen) { BOOL rest = TRUE; for (int i = ofs + k; i < n; i++) if (ln[i] != ' ') rest = FALSE; if (rest) { inFence = FALSE; continue; } }
            goto code_row;
        }
        if (ind < 4 && ofs + 2 < n && (ln[ofs] == '`' || ln[ofs] == '~') && ln[ofs + 1] == ln[ofs] && ln[ofs + 2] == ln[ofs]) {
            fenceCh = ln[ofs]; fenceLen = 0; while (ofs + fenceLen < n && ln[ofs + fenceLen] == fenceCh) fenceLen++;
            inFence = TRUE; continue;
        }
        if (blank) { g_rowY += g_bodyH * 2 / 3; continue; }
        /* block quote */
        int ql = 0, p = ofs;
        while (p < n && ind < 4 && ln[p] == '>') { ql++; p++; if (p < n && ln[p] == ' ') p++; while (p < n && ln[p] == ' ') p++; }
        COLORREF col = ql ? C_QUOTE : C_TEXT;
        int base = left + ql * Sc(16);
        const WCHAR *t = ln + p; int tn = n - p;
        int qy0 = g_rowY;
        if (ql) { int o2; ind = MdIndentCols(t, tn, &o2); ofs = o2; } else { ofs = p; t = ln; tn = n; }
        const WCHAR *c0 = t + (ql ? ofs : ofs);
        int cn = tn - ofs;
        if (ql) { c0 = t + ofs; cn = tn - ofs; }
        else { c0 = ln + ofs; cn = n - ofs; }
        if (MdIsHr(c0, cn)) {
            sp = 0;
            MdAddItem(MI_FILL, base, g_rowY + g_bodyH / 2, maxX - base, Sc(1) > 0 ? Sc(1) : 1, 0, C_GRID, NULL, 0);
            g_rowY += g_bodyH;
        } else if (cn > 0 && c0[0] == '#') {
            int k = 0; while (k < cn && c0[k] == '#') k++;
            if (k <= 6 && (k == cn || c0[k] == ' ' || c0[k] == '\t')) {
                sp = 0;
                int a = k, b = cn;
                while (a < b && (c0[a] == ' ' || c0[a] == '\t')) a++;
                while (b > a && c0[b - 1] == ' ') b--;
                int e = b; while (e > a && c0[e - 1] == '#') e--;
                if (e < b && (e == a || c0[e - 1] == ' ')) { b = e; while (b > a && c0[b - 1] == ' ') b--; }
                o.n = 0; MdInline(c0 + a, b - a, 0, &o);
                g_rowY += Sc(k <= 2 ? 8 : 4);
                MdFlow(&o, k, col, base, base, maxX, TRUE);
                if (k <= 2) { MdAddItem(MI_FILL, base, g_rowY + Sc(1), maxX - base, Sc(1) > 0 ? Sc(1) : 1, 0, C_GRID, NULL, 0); g_rowY += Sc(6); }
                else g_rowY += Sc(2);
            } else goto paragraph;
        } else {
            /* table? */
            int align[64];
            if (!ql && L + 1 < g_nl && wmemchr(c0, L'|', (size_t)cn)) {
                int dn; const WCHAR *dl = LineText(L + 1, &dn);
                WCHAR *dcopy = xmalloc(((size_t)dn + 1) * sizeof(WCHAR)); memcpy(dcopy, dl, (size_t)dn * sizeof(WCHAR));
                int ncol = MdDelimRow(dcopy, dn, align, 64);
                free(dcopy);
                int hc[128]; WCHAR *hdr = xmalloc(((size_t)n + 1) * sizeof(WCHAR)); memcpy(hdr, ln, (size_t)n * sizeof(WCHAR));
                int hn = MdSplitRow(hdr, n, hc, 64);
                if (ncol > 0 && hn == ncol) {
                    sp = 0;
                    /* gather rows */
                    size_t L2 = L + 2;
                    while (L2 < g_nl) { int tn2; const WCHAR *t2 = LineText(L2, &tn2); int o3; MdIndentCols(t2, tn2, &o3); if (o3 == tn2 || !wmemchr(t2, L'|', (size_t)tn2)) break; L2++; }
                    int nrow = (int)(L2 - L) - 1;    /* header + body rows */
                    int *colW = calloc((size_t)ncol, sizeof(int));
                    int pad = Sc(8), rowH = g_bodyH + Sc(6);
                    /* pass 1: widths */
                    for (int pass = 0; pass < 2; pass++) {
                        int y0 = g_rowY;
                        for (int ri = 0; ri < nrow; ri++) {
                            size_t LL = ri == 0 ? L : L + 1 + (size_t)ri;
                            int tn3; const WCHAR *t3 = LineText(LL, &tn3);
                            WCHAR *cp = xmalloc(((size_t)tn3 + 1) * sizeof(WCHAR)); memcpy(cp, t3, (size_t)tn3 * sizeof(WCHAR));
                            int cs[128]; int nc = MdSplitRow(cp, tn3, cs, 64);
                            int x = left;
                            if (pass == 1 && ri == 0) {
                                int tw = 0; for (int c = 0; c < ncol; c++) tw += colW[c];
                                MdAddItem(MI_FILL, left, y0, tw, rowH, 0, C_THEAD, NULL, 0);
                            }
                            for (int c = 0; c < ncol; c++) {
                                o.n = 0;
                                if (c < nc) MdInline(cp + cs[2 * c], cs[2 * c + 1] - cs[2 * c], 0, &o);
                                int wsum = 0;
                                for (int i2 = 0; i2 < o.n; ) {
                                    if (o.s[i2] & S_HIDE) { i2++; continue; }
                                    int j2 = i2; while (j2 < o.n && o.s[j2] == o.s[i2]) j2++;
                                    WORD st = o.s[i2];
                                    int fl = (st & (S_B | S_I | S_U | S_S)) | ((st & S_CODE) ? 16 : 0) | (ri == 0 ? S_B : 0);
                                    int font = MdFontIdx(0, fl); int *dx;
                                    int wpx = MdMeasure(font, o.t + i2, j2 - i2, &dx);
                                    wsum += wpx; i2 = j2;
                                }
                                if (pass == 0) { if (wsum + 2 * pad > colW[c]) colW[c] = wsum + 2 * pad; }
                                else {
                                    int cx = align[c] == 1 ? x + (colW[c] - wsum) / 2 : (align[c] == 2 ? x + colW[c] - pad - wsum : x + pad);
                                    for (int i2 = 0; i2 < o.n; ) {
                                        if (o.s[i2] & S_HIDE) { i2++; continue; }
                                        int j2 = i2; while (j2 < o.n && o.s[j2] == o.s[i2]) j2++;
                                        WORD st = o.s[i2];
                                        int fl = (st & (S_B | S_I | S_U | S_S)) | ((st & S_CODE) ? 16 : 0) | (ri == 0 ? S_B : 0);
                                        int font = MdFontIdx(0, fl); int *dx;
                                        int wpx = MdMeasure(font, o.t + i2, j2 - i2, &dx);
                                        int ty = y0 + (rowH - (g_mdAsc[font] + g_mdDesc[font])) / 2;
                                        MdAddItem(MI_TEXT, cx, ty, wpx, 0, font, (st & S_LINK) ? C_LINK : C_TEXT, o.t + i2, j2 - i2);
                                        cx += wpx; i2 = j2;
                                    }
                                    MdAddItem(MI_FILL, x, y0, 1, rowH, 0, C_GRID, NULL, 0);
                                }
                                x += colW[c];
                            }
                            if (pass == 1) {
                                MdAddItem(MI_FILL, x, y0, 1, rowH, 0, C_GRID, NULL, 0);
                                MdAddItem(MI_FILL, left, y0, x - left + 1, 1, 0, C_GRID, NULL, 0);
                            }
                            y0 += rowH;
                            free(cp);
                        }
                        if (pass == 1) {
                            int tw = 0; for (int c = 0; c < ncol; c++) tw += colW[c];
                            MdAddItem(MI_FILL, left, y0, tw + 1, 1, 0, C_GRID, NULL, 0);
                            g_rowY = y0 + Sc(4);
                        }
                    }
                    free(colW); free(hdr);
                    L = L2 - 1;
                    continue;
                }
                free(hdr);
            }
            /* list item? */
            int mlen = 0, ordered = 0, num = 0; WCHAR dch = 0;
            if (cn >= 1 && (c0[0] == '-' || c0[0] == '*' || c0[0] == '+') && (cn == 1 || c0[1] == ' ' || c0[1] == '\t')) { mlen = 1; dch = c0[0]; }
            else {
                int k = 0; while (k < cn && k < 9 && c0[k] >= '0' && c0[k] <= '9') { num = num * 10 + (c0[k] - '0'); k++; }
                if (k > 0 && k < cn && (c0[k] == '.' || c0[k] == ')') && (k + 1 == cn || c0[k + 1] == ' ' || c0[k + 1] == '\t')) { mlen = k + 1; ordered = 1; dch = c0[k]; }
            }
            if (mlen > 0) {
                int sps = 0; while (mlen + sps < cn && c0[mlen + sps] == ' ') sps++;
                if (sps > 4) sps = 1;
                int mcol = ind, ccol = ind + mlen + (sps ? sps : 1);
                while (sp > 0 && mcol < stk[sp - 1].markerCol) sp--;
                if (sp > 0 && mcol < stk[sp - 1].contentCol) {             /* sibling */
                    MdList *top = &stk[sp - 1];
                    if (top->ordered == ordered && top->delim == dch) top->counter++;
                    else { top->ordered = ordered; top->delim = dch; top->counter = num; }
                    top->markerCol = mcol; top->contentCol = ccol;
                } else if (sp < 16) {
                    stk[sp].markerCol = mcol; stk[sp].contentCol = ccol; stk[sp].ordered = ordered; stk[sp].counter = num; stk[sp].delim = dch; sp++;
                }
                int lvl = sp - 1;
                int mx = base + lvl * Sc(22);
                int cx = mx + Sc(18);
                WCHAR mk[16]; int mkn = 0;
                if (stk[lvl].ordered) { mkn = _snwprintf(mk, 16, L"%d%lc", stk[lvl].counter, stk[lvl].delim); if (mkn < 0) mkn = 0; }
                int mw = 0;
                if (mkn) { int *dx; mw = MdMeasure(MdFontIdx(0, 0), mk, mkn, &dx); if (mx + mw + Sc(6) > cx) cx = mx + mw + Sc(6); }
                o.n = 0; MdInline(c0 + mlen + sps, cn - mlen - sps, 0, &o);
                int firstItem = g_nmi;
                MdFlow(&o, 0, col, cx, cx, maxX, FALSE);
                /* marker on the first row */
                if (g_nmi > firstItem || 1) {
                    int ry = 0; int asc = g_mdAsc[0];
                    for (int i = firstItem; i < g_nmi; i++) if (g_mi[i].type == MI_TEXT) { ry = g_mi[i].y + g_mdAsc[MdItemFont(&g_mi[i])] - asc; break; }
                    if (ry == 0) ry = g_rowY - g_bodyH;
                    if (mkn) MdAddItem(MI_TEXT, mx, ry, mw, 0, MdFontIdx(0, 0), col, mk, mkn);
                    else {
                        int d = Sc(6); if (d < 4) d = 4;
                        int it = MdAddItem(MI_BULLET, mx + Sc(4), ry + asc - asc / 2 - d / 2, d, d, 0, col, NULL, 0);
                        g_mi[it].kind = (BYTE)(lvl % 3);
                    }
                }
            } else {
            paragraph:
                if (sp > 0 && ind >= stk[sp - 1].contentCol) {        /* continuation inside list item */
                    int cx = base + (sp - 1) * Sc(22) + Sc(18);
                    o.n = 0; MdInline(c0, cn, 0, &o);
                    MdFlow(&o, 0, col, cx, cx, maxX, FALSE);
                } else if (!ql && sp == 0 && ind >= 4) {
                    goto code_row;
                } else {
                    sp = 0;
                    o.n = 0; MdInline(c0, cn, 0, &o);
                    MdFlow(&o, 0, col, base, base, maxX, FALSE);
                }
            }
        }
        if (ql) for (int k = 0; k < ql; k++) MdAddItem(MI_FILL, left + k * Sc(16), qy0, Sc(3), g_rowY - qy0, 0, C_QUOTE, NULL, 0);
        continue;
    code_row: {
            /* fenced / indented code: monospace, background, no wrap */
            WCHAR *cb = xmalloc(((size_t)n * 4 + 2) * sizeof(WCHAR)); int k = 0, colx = 0;
            int startc = inFence ? 0 : (ofs > 4 ? 4 : ofs);
            for (int i = startc; i < n; i++) { if (ln[i] == '\t') { int nx = (colx / 4 + 1) * 4; while (colx < nx) { cb[k++] = ' '; colx++; } } else { cb[k++] = ln[i]; colx++; } }
            int font = MdFontIdx(0, 16);
            MdFont(font);
            int h = g_mdAsc[font] + g_mdDesc[font] + Sc(2);
            MdAddItem(MI_FILL, left, g_rowY, maxX - left, h, 0, C_CODEBG, NULL, 0);
            int *dx; int wpx = MdMeasure(font, cb, k, &dx);
            MdAddItem(MI_TEXT, left + Sc(8), g_rowY + Sc(1), wpx, 0, font, C_TEXT, cb, k);
            g_rowY += h;
            free(cb);
        }
    }
    free(ln); free(o.t); free(o.s);
    g_mdH = g_rowY + Sc(16);
}
static void MdPaint(HDC dc, int w, int h) {
    MdLayout();
    (void)w;
    HGDIOBJ of = GetCurrentObject(dc, OBJ_FONT);
    for (int i = 0; i < g_nmi; i++) {
        const MdItem *it = &g_mi[i];
        int y = it->y - g_mdTop;
        int ih = it->type == MI_TEXT ? g_mdAsc[MdItemFont(it)] + g_mdDesc[MdItemFont(it)] : it->h;
        if (y + ih < 0 || y > h) continue;
        if (it->type == MI_FILL) FillR(dc, it->x, y, it->x + it->w, y + it->h, it->col);
        else if (it->type == MI_TEXT) {
            SelectObject(dc, MdFont(MdItemFont(it)));
            SetTextColor(dc, it->col);
            ExtTextOutW(dc, it->x, y, 0, NULL, g_mpool + it->ts, (UINT)it->tl, NULL);
        } else if (it->type == MI_BULLET) {
            HBRUSH br = CreateSolidBrush(it->col); HPEN pen = CreatePen(PS_SOLID, 1, it->col);
            HGDIOBJ ob = SelectObject(dc, it->kind == 1 ? GetStockObject(NULL_BRUSH) : (HGDIOBJ)br), op = SelectObject(dc, pen);
            if (it->kind == 2) Rectangle(dc, it->x, y, it->x + it->w, y + it->h);
            else Ellipse(dc, it->x, y, it->x + it->w, y + it->h);
            SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(br); DeleteObject(pen);
        }
    }
    SelectObject(dc, of);
}

/* ================================================================== */
/* commands / keyboard / mouse for the text view                       */
/* ================================================================== */
static void SetMdView(BOOL on);
static void NewWindow(void);
static void ShowMainMenu(void);
static void ZoomSet(int pt10) {
    if (pt10 < 60) pt10 = 60;
    if (pt10 > 720) pt10 = 720;
    if (pt10 == g_fontPt10) return;
    /* keep the first visible line in place */
    g_fontPt10 = pt10; SetupFont(); g_topRow = 0;
    Refresh(FALSE);
}
static void DoCommand(int id) {
    CompleteComposition();
    BOOL ro = g_mdView;
    if (id >= IDM_FONT0 && id < IDM_FONT0 + NFONTS) { g_fontIdx = id - IDM_FONT0; SetupFont(); Refresh(TRUE); return; }
    switch (id) {
    case IDM_NEWWIN: NewWindow(); break;
    case IDM_OPEN: DoOpen(); break;
    case IDM_SAVE: DoSave(); break;
    case IDM_SAVEAS: DoSaveAs(); break;
    case IDM_SAVEINC: DoSaveIncrement(); break;
    case IDM_EXIT: PostMessageW(g_frame, WM_CLOSE, 0, 0); break;
    case IDM_UNDO: if (!ro) { Undo(); Refresh(TRUE); } break;
    case IDM_REDO: if (!ro) { Redo(); Refresh(TRUE); } break;
    case IDM_CUT: if (!ro) CutSel(); break;
    case IDM_COPY: CopySel(); break;
    case IDM_PASTE: if (!ro) { Paste(); Refresh(TRUE); } break;
    case IDM_DELETE: if (!ro && HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); Refresh(TRUE); } break;
    case IDM_SELALL: g_anchor = 0; g_caret = DocLen(); g_aff = FALSE; Refresh(!ro); break;
    case IDM_RECONV: if (!ro) { SetFocus(g_hwnd); StartReconversion(); } break;
    case IDM_FIND: if (ro) SetMdView(FALSE); FindShow(FALSE); break;
    case IDM_REPLACE: if (ro) SetMdView(FALSE); FindShow(TRUE); break;
    case IDM_FINDNEXT: case IDM_FINDPREV:
        if (ro) SetMdView(FALSE);
        if (g_re) FindNext(id == IDM_FINDNEXT); else FindShow(FALSE);
        break;
    case IDM_WRAP:
        g_wrap = !g_wrap; g_layoutVer++; g_topRow = 0; g_sx = 0; g_aff = FALSE; g_maxW = 0;
        Refresh(TRUE); break;
    case IDM_WS: g_showWs = !g_showWs; Refresh(FALSE); break;
    case IDM_MD: SetMdView(!g_mdView); break;
    case IDM_ZOOMIN: ZoomSet(g_fontPt10 + 10); break;
    case IDM_ZOOMOUT: ZoomSet(g_fontPt10 - 10); break;
    case IDM_ZOOMRESET: ZoomSet(110); break;
    case IDM_ABOUT:
        MessageBoxW(g_frame, APPNAME L" " APPVER L"\n\nWin32 / GDI / IMM32 のみで描画するテキストエディタ\n(インライン IME 変換、独自タイトルバー、正規表現検索、Markdown 表示)", APPNAME, MB_ICONINFORMATION);
        break;
    }
    UpdateTitle();
}
static void MoveTo(size_t p, BOOL extend, BOOL keepX, BOOL aff) {
    size_t len = DocLen(); if (p > len) p = len;
    g_caret = p; if (!extend) g_anchor = p;
    g_aff = aff;
    if (!keepX) g_wantX = -1;
    BreakUndoMerge();
    Refresh(TRUE);
}
static void MoveVert(long long d, BOOL extend) {
    POINT pt; size_t L; int r;
    CaretInfo(&pt, &L, &r);
    if (g_wantX < 0) g_wantX = pt.x - XClient(0);
    long long moved = StepRows(&L, &r, d);
    size_t p; BOOL aff = FALSE;
    if (moved == 0 && d < 0) p = 0;
    else if (moved == 0 && d > 0) p = DocLen();
    else p = PosAtRowX(L, r, g_wantX, &aff);
    MoveTo(p, extend, TRUE, aff);
}
static BOOL CtrlChar(WPARAM vk, WCHAR want) {
    UINT ch = MapVirtualKeyW((UINT)vk, MAPVK_VK_TO_CHAR) & 0x7FFF;
    return ch == want;
}
static void MdKey(WPARAM vk, BOOL ctrl) {
    switch (vk) {
    case VK_UP: ScrollRows(-1); break;
    case VK_DOWN: ScrollRows(1); break;
    case VK_PRIOR: g_mdTop -= g_ch - g_lineH; ClampScroll(); Refresh(FALSE); break;
    case VK_NEXT: case VK_SPACE: g_mdTop += g_ch - g_lineH; ClampScroll(); Refresh(FALSE); break;
    case VK_HOME: if (ctrl || 1) { g_mdTop = 0; Refresh(FALSE); } break;
    case VK_END: g_mdTop = g_mdH; ClampScroll(); Refresh(FALSE); break;
    case VK_ESCAPE: SetMdView(FALSE); break;
    }
}
static void OnKeyDown(WPARAM vk) {
    BOOL ctrl = GetKeyState(VK_CONTROL) < 0, shift = GetKeyState(VK_SHIFT) < 0, alt = GetKeyState(VK_MENU) < 0;
    size_t len = DocLen();
    if (vk == VK_F3) { DoCommand(shift ? IDM_FINDPREV : IDM_FINDNEXT); return; }
    if (ctrl && !alt) {
        int cmd = 0;
        if (CtrlChar(vk, L';') || CtrlChar(vk, L'+') || CtrlChar(vk, L'=') || vk == VK_ADD) cmd = IDM_ZOOMIN;
        else if (CtrlChar(vk, L'-') || vk == VK_SUBTRACT) cmd = IDM_ZOOMOUT;
        else if (vk == '0' || vk == VK_NUMPAD0) cmd = IDM_ZOOMRESET;
        else switch (vk) {
        case 'N': cmd = IDM_NEWWIN; break;
        case 'O': cmd = IDM_OPEN; break;
        case 'S': cmd = shift ? IDM_SAVEAS : IDM_SAVE; break;
        case 'I': cmd = IDM_SAVEINC; break;
        case 'F': cmd = IDM_FIND; break;
        case 'H': cmd = IDM_REPLACE; break;
        case 'M': cmd = IDM_MD; break;
        case 'T': cmd = IDM_WRAP; break;
        case 'W': cmd = IDM_WS; break;
        case 'A': cmd = IDM_SELALL; break;
        case 'C': cmd = IDM_COPY; break;
        case 'X': cmd = IDM_CUT; break;
        case 'V': cmd = IDM_PASTE; break;
        case 'Z': cmd = shift ? IDM_REDO : IDM_UNDO; break;
        case 'Y': cmd = IDM_REDO; break;
        }
        if (cmd) { DoCommand(cmd); return; }
    }
    if (g_mdView) { MdKey(vk, ctrl); return; }
    if (vk == VK_ESCAPE) { if (g_findOpen) FindHide(); return; }
    switch (vk) {
    case VK_LEFT:
        if (HasSel() && !shift && !ctrl) { MoveTo(SelA(), FALSE, FALSE, FALSE); break; }
        MoveTo(ctrl ? WordLeft(g_caret) : PrevPos(g_caret), shift, FALSE, FALSE); break;
    case VK_RIGHT:
        if (HasSel() && !shift && !ctrl) { MoveTo(SelB(), FALSE, FALSE, FALSE); break; }
        MoveTo(ctrl ? WordRight(g_caret) : NextPos(g_caret), shift, FALSE, FALSE); break;
    case VK_UP:   if (ctrl) ScrollRows(-1); else MoveVert(-1, shift); break;
    case VK_DOWN: if (ctrl) ScrollRows(1); else MoveVert(1, shift); break;
    case VK_PRIOR: case VK_NEXT: {
        long long v = VisLines() - 1; if (v < 1) v = 1;
        if (vk == VK_PRIOR) v = -v;
        StepRows(&g_top, &g_topRow, v); ClampScroll();
        MoveVert(v, shift); break;
    }
    case VK_HOME:
        if (ctrl) MoveTo(0, shift, FALSE, FALSE);
        else {
            POINT pt; size_t L; int r; CaretInfo(&pt, &L, &r);
            LayoutLine(L, FALSE);
            size_t s = LineStart(L), rs = s + (size_t)RowStart(r);
            if (r > 0) { MoveTo(rs, shift, FALSE, FALSE); break; }
            size_t e = LineEnd(L), q = s;      /* smart home: first non-blank, then column 0 */
            while (q < e && (DocAt(q) == L' ' || DocAt(q) == L'\t' || DocAt(q) == 0x3000)) q++;
            MoveTo(g_caret == q ? s : q, shift, FALSE, FALSE);
        }
        break;
    case VK_END:
        if (ctrl) MoveTo(len, shift, FALSE, FALSE);
        else {
            POINT pt; size_t L; int r; CaretInfo(&pt, &L, &r);
            LayoutLine(L, FALSE);
            if (HasRow(r + 1)) MoveTo(LineStart(L) + (size_t)RowStart(r + 1), shift, FALSE, TRUE);
            else MoveTo(LineEnd(L), shift, FALSE, FALSE);
        }
        break;
    case VK_DELETE:
        if (shift && !ctrl) { CutSel(); break; }
        if (HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); }
        else if (g_caret < len) {
            size_t e = ctrl ? WordRight(g_caret) : NextPos(g_caret);
            if (!(g_lastKind == K_DEL && g_lastEnd == g_caret)) NewGroup();
            EditDelete(g_caret, e - g_caret);
            g_anchor = g_caret; g_lastKind = K_DEL; g_lastEnd = g_caret;
        }
        g_wantX = -1; g_aff = FALSE; UpdateTitle(); Refresh(TRUE); break;
    case VK_BACK:
        if (HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); }
        else if (g_caret > 0) {
            size_t s;
            if (ctrl) s = WordLeft(g_caret);
            else { s = g_caret - 1; if (s > 0 && IS_LO(DocAt(s)) && IS_HI(DocAt(s - 1))) s--; }
            if (!(g_lastKind == K_BS && g_lastEnd == g_caret)) NewGroup();
            EditDelete(s, g_caret - s);
            g_caret = g_anchor = s; g_lastKind = K_BS; g_lastEnd = s;
        }
        g_wantX = -1; g_aff = FALSE; UpdateTitle(); Refresh(TRUE); break;
    case VK_INSERT:
        if (ctrl && !shift) DoCommand(IDM_COPY);
        else if (shift && !ctrl) DoCommand(IDM_PASTE);
        break;
    case VK_APPS: break;
    }
}
static void OnChar(WPARAM ch) {
    WCHAR c = (WCHAR)ch;
    if (g_mdView) return;
    BOOL ctrl = GetKeyState(VK_CONTROL) < 0, alt = GetKeyState(VK_MENU) < 0;
    if (ctrl && !alt && c < 0x20) return;          /* Ctrl+I/M/J etc. would produce TAB/CR/LF */
    if (c == L'\r') c = L'\n';
    if ((c < 0x20 && c != L'\n' && c != L'\t') || c == 0x7F) return;
    if (IS_LO(c) && g_caret > 0 && !HasSel() && IS_HI(DocAt(g_caret - 1)) && g_lastEnd == g_caret) {
        EditInsert(g_caret, &c, 1); g_caret++; g_anchor = g_caret; g_lastEnd = g_caret;
    } else InsertText(&c, 1, K_TYPE);
    UpdateTitle(); Refresh(TRUE);
}
static void OnScroll(int bar, int code) {
    SCROLLINFO si = { sizeof si, SIF_ALL, 0, 0, 0, 0, 0 };
    GetScrollInfo(g_hwnd, bar, &si);
    if (bar == SB_VERT && g_mdView) {
        int t = g_mdTop;
        switch (code) {
        case SB_LINEUP: t -= g_lineH; break; case SB_LINEDOWN: t += g_lineH; break;
        case SB_PAGEUP: t -= g_ch; break; case SB_PAGEDOWN: t += g_ch; break;
        case SB_THUMBTRACK: case SB_THUMBPOSITION: t = si.nTrackPos; break;
        case SB_TOP: t = 0; break; case SB_BOTTOM: t = g_mdH; break;
        default: return;
        }
        g_mdTop = t;
    } else if (bar == SB_VERT) {
        long long v = VisLines() - 1; if (v < 1) v = 1;
        switch (code) {
        case SB_LINEUP: StepRows(&g_top, &g_topRow, -1); break;
        case SB_LINEDOWN: StepRows(&g_top, &g_topRow, 1); break;
        case SB_PAGEUP: StepRows(&g_top, &g_topRow, -v); break;
        case SB_PAGEDOWN: StepRows(&g_top, &g_topRow, v); break;
        case SB_THUMBTRACK: case SB_THUMBPOSITION:
            if (g_wrap) TopFromRowIndex(si.nTrackPos);
            else { g_top = (size_t)(si.nTrackPos < 0 ? 0 : si.nTrackPos); g_topRow = 0; }
            break;
        case SB_TOP: g_top = 0; g_topRow = 0; break;
        case SB_BOTTOM: g_top = g_nl - 1; g_topRow = 1 << 30; break;
        default: return;
        }
    } else {
        int x = g_sx;
        switch (code) {
        case SB_LINELEFT: x -= g_avgW * 4; break; case SB_LINERIGHT: x += g_avgW * 4; break;
        case SB_PAGELEFT: x -= g_cw; break; case SB_PAGERIGHT: x += g_cw; break;
        case SB_THUMBTRACK: case SB_THUMBPOSITION: x = si.nTrackPos; break;
        case SB_LEFT: x = 0; break; case SB_RIGHT: x = g_maxW; break;
        default: return;
        }
        g_sx = x;
    }
    ClampScroll(); Refresh(FALSE);
}
static void LineSpan(size_t p, size_t *a, size_t *b) {
    size_t L = LineOf(p);
    *a = LineStart(L);
    *b = L + 1 < g_nl ? LineStart(L + 1) : LineEnd(L);
}
static void DragTo(int x, int y) {
    BOOL aff = FALSE;
    size_t p = PosFromPointEx(x, y, &aff);
    if (g_dragMode == 1 || g_dragMode == 2) {
        size_t a, b;
        if (g_dragMode == 1) WordAt(p, &a, &b); else LineSpan(p, &a, &b);
        if (p < g_wordA) { g_anchor = g_wordB; g_caret = a; }
        else { g_anchor = g_wordA; g_caret = b > g_wordB ? b : g_wordB; }
        aff = FALSE;
    } else g_caret = p;
    g_aff = aff;
    Refresh(TRUE);
}
static void ShowContextMenu(int sx, int sy) {
    CompleteComposition();
    if (sx == -1 && sy == -1) { POINT pt; CaretPoint(&pt, NULL); pt.y += g_lineH; ClientToScreen(g_hwnd, &pt); sx = pt.x; sy = pt.y; }
    HMENU m = CreatePopupMenu();
    BOOL ro = g_mdView, sel = HasSel(), clip = IsClipboardFormatAvailable(CF_UNICODETEXT);
    AppendMenuW(m, MF_STRING | ((g_undo.n && !ro) ? 0 : MF_GRAYED), IDM_UNDO, L"元に戻す(&U)\tCtrl+Z");
    AppendMenuW(m, MF_STRING | ((g_redo.n && !ro) ? 0 : MF_GRAYED), IDM_REDO, L"やり直し(&R)\tCtrl+Y");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING | ((sel && !ro) ? 0 : MF_GRAYED), IDM_CUT, L"切り取り(&T)\tCtrl+X");
    AppendMenuW(m, MF_STRING | (sel ? 0 : MF_GRAYED), IDM_COPY, L"コピー(&C)\tCtrl+C");
    AppendMenuW(m, MF_STRING | ((clip && !ro) ? 0 : MF_GRAYED), IDM_PASTE, L"貼り付け(&P)\tCtrl+V");
    AppendMenuW(m, MF_STRING | ((sel && !ro) ? 0 : MF_GRAYED), IDM_DELETE, L"削除(&D)\tDel");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, IDM_SELALL, L"すべて選択(&A)\tCtrl+A");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING | (ro ? MF_GRAYED : 0), IDM_RECONV, L"再変換(&V)");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, IDM_FIND, L"検索(&F)...\tCtrl+F");
    AppendMenuW(m, MF_STRING, IDM_REPLACE, L"置換(&H)...\tCtrl+H");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING | (g_wrap ? MF_CHECKED : 0), IDM_WRAP, L"右端で折り返す(&W)\tCtrl+T");
    AppendMenuW(m, MF_STRING | (g_showWs ? MF_CHECKED : 0), IDM_WS, L"空白文字を表示(&S)\tCtrl+W");
    AppendMenuW(m, MF_STRING | (g_mdView ? MF_CHECKED : 0), IDM_MD, L"Markdown 表示(&M)\tCtrl+M");
    int cmd = (int)TrackPopupMenu(m, TPM_RETURNCMD | TPM_RIGHTBUTTON, sx, sy, 0, g_frame, NULL);
    DestroyMenu(m);
    if (cmd) DoCommand(cmd);
}

static LRESULT CALLBACK TextProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CREATE:
        g_hwnd = h;
        SetupFont();
        return 0;
    case WM_SIZE:
        if (g_cw != LOWORD(lp)) g_layoutVer++;
        g_cw = LOWORD(lp); g_ch = HIWORD(lp);
        ClampScroll(); Refresh(FALSE);
        return 0;
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps);
        int oldMax = g_maxW, oldMdH = g_mdH;
        Paint(dc, &ps.rcPaint);
        EndPaint(h, &ps);
        if (g_maxW != oldMax || g_mdH != oldMdH) UpdateScrollBars();
        if (g_selftest == 1) { g_selftest = 2; PostMessageW(g_frame, WM_APP + 1, 0, 0); }
        return 0;
    }
    case WM_SETFOCUS:
        g_focus = TRUE; g_lastFocus = h; CreateCaretNow(); PlaceCaret(); Invalidate();
        return 0;
    case WM_KILLFOCUS:
        CompleteComposition();              /* EDIT commits the composition on focus loss */
        g_focus = FALSE;
        if (g_caretMade) { DestroyCaret(); g_caretMade = FALSE; }
        if (g_dragging) { g_dragging = FALSE; ReleaseCapture(); }
        Invalidate();
        return 0;
    case WM_ENTERMENULOOP:
        CompleteComposition();
        break;
    case WM_SETCURSOR:
        if (LOWORD(lp) == HTCLIENT) { SetCursor(LoadCursorW(NULL, g_mdView ? IDC_ARROW : IDC_IBEAM)); return TRUE; }
        break;
    case WM_KEYDOWN:
        if (wp == VK_PROCESSKEY) break;     /* consumed by the IME */
        OnKeyDown(wp);
        return 0;
    case WM_SYSKEYDOWN:
        if (wp == VK_F4) { PostMessageW(g_frame, WM_SYSCOMMAND, SC_CLOSE, 0); return 0; }
        break;
    case WM_SYSCHAR:
        if (wp == L' ') { PostMessageW(g_frame, WM_SYSCOMMAND, SC_KEYMENU, L' '); return 0; }
        break;
    case WM_CHAR:
        OnChar(wp);
        return 0;
    case WM_UNICHAR:
        if (wp == UNICODE_NOCHAR) return TRUE;
        if (g_mdView) return 0;
        if (wp >= 0x10000 && wp <= 0x10FFFF) {
            WCHAR s[2] = { (WCHAR)(0xD800 + ((wp - 0x10000) >> 10)), (WCHAR)(0xDC00 + ((wp - 0x10000) & 0x3FF)) };
            InsertText(s, 2, K_TYPE); UpdateTitle(); Refresh(TRUE);
        } else if (wp < 0x10000) OnChar(wp);
        return 0;

    /* ---- IME (inline composition, EDIT-compatible) ---- */
    case WM_IME_SETCONTEXT:
        if (wp) lp &= ~(LPARAM)ISC_SHOWUICOMPOSITIONWINDOW;  /* we draw composition; keep candidate UI */
        return DefWindowProcW(h, m, wp, lp);
    case WM_IME_STARTCOMPOSITION:
        OnStartComposition();
        return 0;                           /* not to DefWindowProc: no floating composition window */
    case WM_IME_COMPOSITION:
        OnComposition(lp);
        return 0;                           /* not to DefWindowProc: no WM_IME_CHAR duplicates */
    case WM_IME_ENDCOMPOSITION:
        OnEndComposition();
        return 0;
    case WM_IME_CHAR:
        return 0;                           /* results come from GCS_RESULTSTR */
    case WM_IME_NOTIFY:
        if (wp == IMN_OPENCANDIDATE || wp == IMN_CHANGECANDIDATE || wp == IMN_SETOPENSTATUS)
            UpdateImeWindows();
        break;
    case WM_IME_REQUEST:
        return OnImeRequest(wp, lp);
    case WM_INPUTLANGCHANGE:
        SetImeFont(); UpdateImeWindows();
        break;

    /* ---- mouse ---- */
    case WM_LBUTTONDOWN:
    case WM_LBUTTONDBLCLK: {
        CompleteComposition();              /* EDIT commits the composition on click */
        if (GetFocus() != h) SetFocus(h);
        if (g_mdView) return 0;
        int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
        BOOL aff = FALSE;
        size_t p = PosFromPointEx(x, y, &aff);
        g_wantX = -1; BreakUndoMerge();
        DWORD now = (DWORD)GetMessageTime();
        if (m == WM_LBUTTONDBLCLK) {
            WordAt(p, &g_wordA, &g_wordB);
            g_anchor = g_wordA; g_caret = g_wordB; g_dragMode = 1; g_aff = FALSE;
            g_lastDblTime = now; g_lastDblPt.x = x; g_lastDblPt.y = y;
        } else if (g_lastDblTime && now - g_lastDblTime <= GetDoubleClickTime() &&
                   abs(x - g_lastDblPt.x) <= GetSystemMetrics(SM_CXDOUBLECLK) &&
                   abs(y - g_lastDblPt.y) <= GetSystemMetrics(SM_CYDOUBLECLK)) {
            /* triple click: select the whole line (including its newline) */
            LineSpan(p, &g_wordA, &g_wordB);
            g_anchor = g_wordA; g_caret = g_wordB; g_dragMode = 2; g_aff = FALSE;
            g_lastDblTime = 0;
        } else {
            g_dragMode = 0; g_lastDblTime = 0;
            g_caret = p; g_aff = aff; if (!(wp & MK_SHIFT)) g_anchor = p;
        }
        g_dragging = TRUE; SetCapture(h); SetTimer(h, 1, 50, NULL);
        g_lastMouseX = x; g_lastMouseY = y;
        Refresh(TRUE);
        return 0;
    }
    case WM_MOUSEMOVE:
        if (g_dragging) { g_lastMouseX = GET_X_LPARAM(lp); g_lastMouseY = GET_Y_LPARAM(lp); DragTo(g_lastMouseX, g_lastMouseY); }
        return 0;
    case WM_TIMER:
        if (wp == 1 && g_dragging) {    /* auto-scroll while dragging outside */
            if (g_lastMouseY < 0) { StepRows(&g_top, &g_topRow, -1); ClampScroll(); DragTo(g_lastMouseX, g_lastMouseY); }
            else if (g_lastMouseY >= g_ch) { StepRows(&g_top, &g_topRow, 1); ClampScroll(); DragTo(g_lastMouseX, g_lastMouseY); }
            else if (g_lastMouseX < 0 || g_lastMouseX >= g_cw) DragTo(g_lastMouseX, g_lastMouseY);
        }
        return 0;
    case WM_LBUTTONUP:
        if (g_dragging) { g_dragging = FALSE; ReleaseCapture(); }
        KillTimer(h, 1);
        return 0;
    case WM_CAPTURECHANGED:
        g_dragging = FALSE; KillTimer(h, 1);
        return 0;
    case WM_RBUTTONDOWN:
        CompleteComposition();
        if (GetFocus() != h) SetFocus(h);
        return 0;
    case WM_CONTEXTMENU:
        ShowContextMenu(GET_X_LPARAM(lp), GET_Y_LPARAM(lp));
        return 0;
    case WM_MOUSEWHEEL: {
        if (GET_KEYSTATE_WPARAM(wp) & MK_CONTROL) {
            DoCommand(GET_WHEEL_DELTA_WPARAM(wp) > 0 ? IDM_ZOOMIN : IDM_ZOOMOUT);
            return 0;
        }
        UINT lines = 3; SystemParametersInfoW(SPI_GETWHEELSCROLLLINES, 0, &lines, 0);
        if (lines == 0) return 0;
        if (lines == WHEEL_PAGESCROLL) lines = (UINT)VisLines();
        g_wheelAcc += GET_WHEEL_DELTA_WPARAM(wp);
        int steps = g_wheelAcc * (int)lines / WHEEL_DELTA;
        if (steps) { g_wheelAcc -= steps * WHEEL_DELTA / (int)lines; ScrollRows(-steps); }
        return 0;
    }
    case WM_MOUSEHWHEEL: {
        if (g_wrap || g_mdView) return 0;
        g_hwheelAcc += GET_WHEEL_DELTA_WPARAM(wp);
        int steps = g_hwheelAcc / (WHEEL_DELTA / 4);
        if (steps) { g_hwheelAcc -= steps * (WHEEL_DELTA / 4); g_sx += steps * g_avgW * 2; ClampScroll(); Refresh(FALSE); }
        return 0;
    }
    case WM_VSCROLL: OnScroll(SB_VERT, LOWORD(wp)); return 0;
    case WM_HSCROLL: OnScroll(SB_HORZ, LOWORD(wp)); return 0;
    case WM_COMMAND: DoCommand(LOWORD(wp)); return 0;
    }
    return DefWindowProcW(h, m, wp, lp);
}

/* ================================================================== */
/* settings (.ini next to the exe; falls back to %APPDATA%\CEditor)    */
/* ================================================================== */
static BOOL g_noIni;
static BOOL g_iniHaveRect; static RECT g_iniRect; static BOOL g_iniMax;
static void IniPaths(WCHAR *exeIni, WCHAR *appIni) {
    GetModuleFileNameW(NULL, exeIni, MAX_PATH * 4);
    WCHAR *s = wcsrchr(exeIni, L'\\'); if (s) s[1] = 0; else exeIni[0] = 0;
    wcscat(exeIni, L"editor.ini");
    appIni[0] = 0;
    DWORD n = GetEnvironmentVariableW(L"APPDATA", appIni, MAX_PATH * 3);
    if (n == 0 || n >= MAX_PATH * 3) appIni[0] = 0;
    else wcscat(appIni, L"\\CEditor\\editor.ini");
}
static void IniReadFrom(const WCHAR *p) {
    WCHAR b[32];
    g_fontIdx = (int)GetPrivateProfileIntW(L"Editor", L"Font", g_fontIdx, p);
    if (g_fontIdx < 0 || g_fontIdx >= NFONTS) g_fontIdx = 0;
    g_fontPt10 = (int)GetPrivateProfileIntW(L"Editor", L"Zoom", g_fontPt10, p);
    if (g_fontPt10 < 60 || g_fontPt10 > 720) g_fontPt10 = 110;
    g_wrap = GetPrivateProfileIntW(L"Editor", L"Wrap", g_wrap, p) != 0;
    g_showWs = GetPrivateProfileIntW(L"Editor", L"Whitespace", g_showWs, p) != 0;
    g_matchCase = GetPrivateProfileIntW(L"Find", L"MatchCase", g_matchCase, p) != 0;
    if (GetPrivateProfileStringW(L"Window", L"W", L"", b, 32, p) > 0) {
        int x = (int)GetPrivateProfileIntW(L"Window", L"X", 0, p), y = (int)GetPrivateProfileIntW(L"Window", L"Y", 0, p);
        int w = (int)GetPrivateProfileIntW(L"Window", L"W", 0, p), h = (int)GetPrivateProfileIntW(L"Window", L"H", 0, p);
        /* GetPrivateProfileInt returns UINT: negative coordinates come back as large values */
        if (GetPrivateProfileStringW(L"Window", L"X", L"0", b, 32, p) > 0) x = _wtoi(b);
        if (GetPrivateProfileStringW(L"Window", L"Y", L"0", b, 32, p) > 0) y = _wtoi(b);
        if (w >= 200 && h >= 120 && w < 20000 && h < 20000) {
            SetRect(&g_iniRect, x, y, x + w, y + h);
            g_iniHaveRect = MonitorFromRect(&g_iniRect, MONITOR_DEFAULTTONULL) != NULL;
        }
        g_iniMax = GetPrivateProfileIntW(L"Window", L"Max", 0, p) != 0;
    }
}
static void LoadIni(void) {
    WCHAR a[MAX_PATH * 4], b[MAX_PATH * 4];
    IniPaths(a, b);
    if (GetFileAttributesW(a) != INVALID_FILE_ATTRIBUTES) { wcscpy(g_iniPath, a); IniReadFrom(a); }
    else if (b[0] && GetFileAttributesW(b) != INVALID_FILE_ATTRIBUTES) { wcscpy(g_iniPath, b); IniReadFrom(b); }
}
static BOOL IniPut(const WCHAR *sec, const WCHAR *key, int v, const WCHAR *p) {
    WCHAR b[32]; _snwprintf(b, 32, L"%d", v); b[31] = 0;
    return WritePrivateProfileStringW(sec, key, b, p);
}
static BOOL IniWriteTo(const WCHAR *p) {
    if (!IniPut(L"Editor", L"Font", g_fontIdx, p)) return FALSE;     /* first write tells if it is writable */
    IniPut(L"Editor", L"Zoom", g_fontPt10, p);
    IniPut(L"Editor", L"Wrap", g_wrap, p);
    IniPut(L"Editor", L"Whitespace", g_showWs, p);
    IniPut(L"Find", L"MatchCase", g_matchCase, p);
    if (g_frame) {
        WINDOWPLACEMENT wp = { sizeof wp, 0, 0, { 0, 0 }, { 0, 0 }, { 0, 0, 0, 0 } };
        if (GetWindowPlacement(g_frame, &wp)) {
            RECT r = wp.rcNormalPosition;
            IniPut(L"Window", L"X", r.left, p); IniPut(L"Window", L"Y", r.top, p);
            IniPut(L"Window", L"W", r.right - r.left, p); IniPut(L"Window", L"H", r.bottom - r.top, p);
            IniPut(L"Window", L"Max", IsZoomed(g_frame) ? 1 : 0, p);
        }
    }
    WritePrivateProfileStringW(NULL, NULL, NULL, p);   /* flush */
    return TRUE;
}
static void SaveIni(void) {
    if (g_noIni) return;
    WCHAR a[MAX_PATH * 4], b[MAX_PATH * 4];
    IniPaths(a, b);
    /* prefer the exe directory; if it is not writable (Program Files, read-only media) use %APPDATA% */
    DWORD at = GetFileAttributesW(a);
    if (!(at != INVALID_FILE_ATTRIBUTES && (at & FILE_ATTRIBUTE_READONLY)) && IniWriteTo(a)) { wcscpy(g_iniPath, a); return; }
    if (!b[0]) return;
    WCHAR dir[MAX_PATH * 4]; wcscpy(dir, b);
    WCHAR *s = wcsrchr(dir, L'\\'); if (s) *s = 0;
    CreateDirectoryW(dir, NULL);
    if (IniWriteTo(b)) wcscpy(g_iniPath, b);
}

/* ================================================================== */
/* frame window: custom caption                                        */
/* ================================================================== */
static BOOL g_active = TRUE;
static int g_capHot, g_capDown;             /* HTMINBUTTON / HTMAXBUTTON / HTCLOSE / CAP_MENU */
#define CAP_MENU 1000
static int CapH(void) { return Sc(32); }
static COLORREF FrameColor(void) { return g_mdView ? C_FRAME_MD : C_FRAME; }
static void CapRects(RECT *rmin, RECT *rmax, RECT *rclose, RECT *rmenu) {
    RECT rc; GetClientRect(g_frame, &rc);
    int bw = Sc(46), h = CapH(), w = rc.right;
    SetRect(rclose, w - bw, 0, w, h);
    SetRect(rmax, w - 2 * bw, 0, w - bw, h);
    SetRect(rmin, w - 3 * bw, 0, w - 2 * bw, h);
    SetRect(rmenu, w - 3 * bw - Sc(40), 0, w - 3 * bw, h);
}
static int FrameFx(void) { return GetSystemMetricsForDpi(SM_CXSIZEFRAME, g_dpi) + GetSystemMetricsForDpi(SM_CXPADDEDBORDER, g_dpi); }
static int FrameFy(void) { return GetSystemMetricsForDpi(SM_CYSIZEFRAME, g_dpi) + GetSystemMetricsForDpi(SM_CXPADDEDBORDER, g_dpi); }
static void ApplyDwm(void) {
    int pref = CED_DWMWCP_ROUND;
    DwmSetWindowAttribute(g_frame, DWMWA_WINDOW_CORNER_PREFERENCE, &pref, sizeof pref);
    BOOL dark = TRUE;
    DwmSetWindowAttribute(g_frame, DWMWA_USE_IMMERSIVE_DARK_MODE, &dark, sizeof dark);
    COLORREF bc = FrameColor();
    DwmSetWindowAttribute(g_frame, DWMWA_BORDER_COLOR, &bc, sizeof bc);
}
static void InvalidateCaption(void) {
    if (!g_frame) return;
    RECT rc; GetClientRect(g_frame, &rc); rc.bottom = CapH();
    InvalidateRect(g_frame, &rc, FALSE);
}
static void Glyph(HDC dc, int kind, RECT r, COLORREF c) {
    int cx = (r.left + r.right) / 2, cy = (r.top + r.bottom) / 2, s = Sc(5);
    int pw = Sc(1) > 0 ? Sc(1) : 1;
    HPEN pen = CreatePen(PS_SOLID, pw, c); HGDIOBJ op = SelectObject(dc, pen), ob = SelectObject(dc, GetStockObject(NULL_BRUSH));
    if (kind == HTMINBUTTON) { MoveToEx(dc, cx - s, cy, NULL); LineTo(dc, cx + s + 1, cy); }
    else if (kind == HTMAXBUTTON) {
        if (IsZoomed(g_frame)) {
            int d = Sc(2);
            Rectangle(dc, cx - s, cy - s + d, cx + s - d + 1, cy + s + 1);
            MoveToEx(dc, cx - s + d, cy - s + d, NULL); LineTo(dc, cx - s + d, cy - s); LineTo(dc, cx + s, cy - s);
            LineTo(dc, cx + s, cy + s - d); LineTo(dc, cx + s - d, cy + s - d);
        } else Rectangle(dc, cx - s, cy - s, cx + s + 1, cy + s + 1);
    } else if (kind == HTCLOSE) {
        MoveToEx(dc, cx - s, cy - s, NULL); LineTo(dc, cx + s + 1, cy + s + 1);
        MoveToEx(dc, cx + s, cy - s, NULL); LineTo(dc, cx - s - 1, cy + s + 1);
    } else {   /* menu: three bars */
        for (int i = -1; i <= 1; i++) { MoveToEx(dc, cx - s - 1, cy + i * Sc(4), NULL); LineTo(dc, cx + s + 2, cy + i * Sc(4)); }
    }
    SelectObject(dc, op); SelectObject(dc, ob); DeleteObject(pen);
}
static void FramePaint(HWND h) {
    PAINTSTRUCT ps; HDC hdc = BeginPaint(h, &ps);
    RECT rc; GetClientRect(h, &rc);
    int w = rc.right, ch = CapH();
    if (w > 0) {
        HDC dc = CreateCompatibleDC(hdc);
        HBITMAP bmp = CreateCompatibleBitmap(hdc, w, ch);
        HGDIOBJ ob = SelectObject(dc, bmp);
        COLORREF bg = FrameColor();
        FillR(dc, 0, 0, w, ch, bg);
        RECT rmin, rmax, rclose, rmenu; CapRects(&rmin, &rmax, &rclose, &rmenu);
        COLORREF fg = g_active ? C_CAPTEXT : C_CAPTEXT_I;
        COLORREF hov = RGB(GetRValue(bg) + (255 - GetRValue(bg)) / 6, GetGValue(bg) + (255 - GetGValue(bg)) / 6, GetBValue(bg) + (255 - GetBValue(bg)) / 6);
        COLORREF prs = RGB(GetRValue(bg) + (255 - GetRValue(bg)) / 4, GetGValue(bg) + (255 - GetGValue(bg)) / 4, GetBValue(bg) + (255 - GetBValue(bg)) / 4);
        const int ids[4] = { CAP_MENU, HTMINBUTTON, HTMAXBUTTON, HTCLOSE };
        RECT rs[4] = { rmenu, rmin, rmax, rclose };
        for (int i = 0; i < 4; i++) {
            BOOL hot = g_capHot == ids[i], down = g_capDown == ids[i] && hot;
            COLORREF gc = fg;
            if (hot) {
                COLORREF c = ids[i] == HTCLOSE ? (down ? RGB(0x94, 0x1E, 0x13) : RGB(0xC4, 0x2B, 0x1C)) : (down ? prs : hov);
                FillR(dc, rs[i].left, rs[i].top, rs[i].right, rs[i].bottom, c);
                if (ids[i] == HTCLOSE) gc = RGB(255, 255, 255);
            }
            Glyph(dc, ids[i], rs[i], gc);
        }
        /* blank space with the unsaved-changes dot, then the file name */
        if (g_modified) {
            int d = Sc(8), cx = Sc(15), cy = ch / 2;
            HBRUSH br = CreateSolidBrush(C_DOT); HPEN pn = CreatePen(PS_SOLID, 1, C_DOT);
            HGDIOBJ o1 = SelectObject(dc, br), o2 = SelectObject(dc, pn);
            Ellipse(dc, cx - d / 2, cy - d / 2, cx - d / 2 + d, cy - d / 2 + d);
            SelectObject(dc, o1); SelectObject(dc, o2); DeleteObject(br); DeleteObject(pn);
        }
        WCHAR title[MAX_PATH * 4 + 32]; GetWindowTextW(h, title, sizeof title / sizeof title[0]);
        if (g_mdView) wcscat(title, L"  [Markdown]");
        HGDIOBJ of = SelectObject(dc, g_capFont);
        SetBkMode(dc, TRANSPARENT); SetTextColor(dc, fg);
        RECT tr = { Sc(30), 0, rmenu.left - Sc(8), ch };
        DrawTextW(dc, title, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_END_ELLIPSIS | DT_NOPREFIX);
        SelectObject(dc, of);
        BitBlt(hdc, 0, 0, w, ch, dc, 0, 0, SRCCOPY);
        SelectObject(dc, ob); DeleteObject(bmp); DeleteDC(dc);
    }
    if (rc.bottom > ch && !g_hwnd) FillR(hdc, 0, ch, w, rc.bottom, C_BG);
    EndPaint(h, &ps);
}
static HFONT g_findFontSet;
static void FrameLayout(void) {
    if (!g_frame || !g_hwnd) return;
    RECT rc; GetClientRect(g_frame, &rc);
    int ch = CapH();
    int h = rc.bottom - ch; if (h < 0) h = 0;
    SetWindowPos(g_hwnd, NULL, 0, ch, rc.right, h, SWP_NOZORDER | SWP_NOACTIVATE);
    if (g_find) {
        if (g_findFontSet != g_uiFont) {
            SendMessageW(g_edFind, WM_SETFONT, (WPARAM)g_uiFont, TRUE);
            SendMessageW(g_edRepl, WM_SETFONT, (WPARAM)g_uiFont, TRUE);
            g_findFontSet = g_uiFont;
        }
        int fw = Sc(FP_W), fh = FindPopupH();
        int sb = GetSystemMetricsForDpi(SM_CXVSCROLL, g_dpi);
        int x = rc.right - fw - sb - Sc(8); if (x < 0) x = 0;
        SetWindowPos(g_find, HWND_TOP, x, ch + Sc(2), fw, fh, SWP_NOACTIVATE | (g_findOpen ? SWP_SHOWWINDOW : 0));
        FindLayoutChildren();
    }
}
static void SetMdView(BOOL on) {
    CompleteComposition();
    if (on == g_mdView) return;
    if (on && DocLen() > 20u * 1024 * 1024) {
        MessageBoxW(g_frame, L"文書が大きすぎるため Markdown 表示はできません (2000万文字まで)。", APPNAME, MB_ICONINFORMATION);
        return;
    }
    if (on && g_findOpen) FindHide();
    g_mdView = on;
    if (on) {
        if (g_caretMade) { DestroyCaret(); g_caretMade = FALSE; }
        MdInvalidate(); MdLayout();
        g_mdTop = g_nl > 1 ? (int)((double)g_mdH * (double)g_top / (double)g_nl) : 0;
    } else CreateCaretNow();
    ApplyDwm(); InvalidateCaption();
    ClampScroll();
    Refresh(!on);
}
static void NewWindow(void) {
    WCHAR exe[MAX_PATH * 4]; GetModuleFileNameW(NULL, exe, MAX_PATH * 4);
    WINDOWPLACEMENT wp = { sizeof wp, 0, 0, { 0, 0 }, { 0, 0 }, { 0, 0, 0, 0 } };
    GetWindowPlacement(g_frame, &wp);
    RECT r = wp.rcNormalPosition; int d = Sc(32);
    WCHAR cmd[MAX_PATH * 4 + 128];
    _snwprintf(cmd, sizeof cmd / sizeof cmd[0], L"\"%ls\" --pos %ld %ld %ld %ld", exe, r.left + d, r.top + d, r.right - r.left, r.bottom - r.top);
    cmd[sizeof cmd / sizeof cmd[0] - 1] = 0;
    STARTUPINFOW si; memset(&si, 0, sizeof si); si.cb = sizeof si;
    PROCESS_INFORMATION pi;
    if (CreateProcessW(exe, cmd, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) { CloseHandle(pi.hThread); CloseHandle(pi.hProcess); }
    else MessageBoxW(g_frame, L"新しいウィンドウを起動できませんでした。", APPNAME, MB_ICONERROR);
}
static void ShowMainMenu(void) {
    CompleteComposition();
    HMENU m = CreatePopupMenu(), f = CreatePopupMenu(), e = CreatePopupMenu(), v = CreatePopupMenu(), fo = CreatePopupMenu();
    AppendMenuW(f, MF_STRING, IDM_NEWWIN, L"新しいウィンドウ(&N)\tCtrl+N");
    AppendMenuW(f, MF_STRING, IDM_OPEN, L"開く(&O)...\tCtrl+O");
    AppendMenuW(f, MF_STRING, IDM_SAVE, L"上書き保存(&S)\tCtrl+S");
    AppendMenuW(f, MF_STRING, IDM_SAVEAS, L"名前を付けて保存(&A)...\tCtrl+Shift+S");
    AppendMenuW(f, MF_STRING, IDM_SAVEINC, L"番号を進めて保存(&I)\tCtrl+I");
    AppendMenuW(f, MF_SEPARATOR, 0, NULL);
    AppendMenuW(f, MF_STRING, IDM_EXIT, L"終了(&X)\tAlt+F4");
    BOOL ro = g_mdView;
    AppendMenuW(e, MF_STRING | ((g_undo.n && !ro) ? 0 : MF_GRAYED), IDM_UNDO, L"元に戻す(&U)\tCtrl+Z");
    AppendMenuW(e, MF_STRING | ((g_redo.n && !ro) ? 0 : MF_GRAYED), IDM_REDO, L"やり直し(&R)\tCtrl+Y");
    AppendMenuW(e, MF_SEPARATOR, 0, NULL);
    AppendMenuW(e, MF_STRING | ((HasSel() && !ro) ? 0 : MF_GRAYED), IDM_CUT, L"切り取り(&T)\tCtrl+X");
    AppendMenuW(e, MF_STRING | (HasSel() ? 0 : MF_GRAYED), IDM_COPY, L"コピー(&C)\tCtrl+C");
    AppendMenuW(e, MF_STRING | ro * MF_GRAYED, IDM_PASTE, L"貼り付け(&P)\tCtrl+V");
    AppendMenuW(e, MF_STRING | ((HasSel() && !ro) ? 0 : MF_GRAYED), IDM_DELETE, L"削除(&L)\tDel");
    AppendMenuW(e, MF_SEPARATOR, 0, NULL);
    AppendMenuW(e, MF_STRING, IDM_SELALL, L"すべて選択(&A)\tCtrl+A");
    AppendMenuW(e, MF_STRING | ro * MF_GRAYED, IDM_RECONV, L"再変換(&V)");
    AppendMenuW(e, MF_SEPARATOR, 0, NULL);
    AppendMenuW(e, MF_STRING, IDM_FIND, L"検索(&F)...\tCtrl+F");
    AppendMenuW(e, MF_STRING, IDM_REPLACE, L"置換(&H)...\tCtrl+H");
    AppendMenuW(e, MF_STRING, IDM_FINDNEXT, L"次を検索(&N)\tF3");
    AppendMenuW(e, MF_STRING, IDM_FINDPREV, L"前を検索(&B)\tShift+F3");
    AppendMenuW(v, MF_STRING | (g_wrap ? MF_CHECKED : 0), IDM_WRAP, L"右端で折り返す(&W)\tCtrl+T");
    AppendMenuW(v, MF_STRING | (g_showWs ? MF_CHECKED : 0), IDM_WS, L"空白文字を表示(&S)\tCtrl+W");
    AppendMenuW(v, MF_STRING | (g_mdView ? MF_CHECKED : 0), IDM_MD, L"Markdown 表示(&M)\tCtrl+M");
    AppendMenuW(v, MF_SEPARATOR, 0, NULL);
    AppendMenuW(v, MF_STRING, IDM_ZOOMIN, L"拡大(&I)\tCtrl+;");
    AppendMenuW(v, MF_STRING, IDM_ZOOMOUT, L"縮小(&O)\tCtrl+-");
    AppendMenuW(v, MF_STRING, IDM_ZOOMRESET, L"標準サイズ(&R)\tCtrl+0");
    for (int i = 0; i < NFONTS; i++) AppendMenuW(fo, MF_STRING | (i == g_fontIdx ? MF_CHECKED : 0), (UINT_PTR)(IDM_FONT0 + i), kFontLabels[i]);
    AppendMenuW(v, MF_SEPARATOR, 0, NULL);
    AppendMenuW(v, MF_POPUP, (UINT_PTR)fo, L"フォント(&F)");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)f, L"ファイル(&F)");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)e, L"編集(&E)");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)v, L"表示(&V)");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, IDM_ABOUT, L"バージョン情報(&A)");
    RECT rmin, rmax, rclose, rmenu; CapRects(&rmin, &rmax, &rclose, &rmenu);
    POINT pt = { rmenu.left, rmenu.bottom }; ClientToScreen(g_frame, &pt);
    g_capHot = CAP_MENU; g_capDown = 0; InvalidateCaption(); UpdateWindow(g_frame);
    int cmd = (int)TrackPopupMenu(m, TPM_RETURNCMD | TPM_LEFTALIGN | TPM_TOPALIGN, pt.x, pt.y, 0, g_frame, NULL);
    DestroyMenu(m);
    g_capHot = 0; InvalidateCaption();
    if (cmd) DoCommand(cmd);
    if (IsWindow(g_hwnd) && !g_findOpen) SetFocus(g_hwnd);
}
static void RunSelfTest(void);
static void RunDemo(void);
static void RunBench(void);
static LRESULT CALLBACK FrameProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CREATE: {
        g_frame = h;
        g_dpi = GetDpiForWindow(h); if (!g_dpi) g_dpi = 96;
        ApplyDwm();
        g_brInput = CreateSolidBrush(C_INPUT_BG);
        CreateWindowExW(0, CLS_TEXT, L"", WS_CHILD | WS_VISIBLE | WS_VSCROLL | WS_HSCROLL | WS_CLIPSIBLINGS,
                        0, 0, 10, 10, h, (HMENU)1, g_inst, NULL);
        SetWindowTheme(g_hwnd, L"DarkMode_Explorer", NULL);
        g_find = CreateWindowExW(0, CLS_FIND, L"", WS_CHILD | WS_CLIPSIBLINGS | WS_CLIPCHILDREN, 0, 0, 10, 10, h, (HMENU)2, g_inst, NULL);
        g_lastFocus = g_hwnd;
        /* force WM_NCCALCSIZE with the new frame */
        SetWindowPos(h, NULL, 0, 0, 0, 0, SWP_FRAMECHANGED | SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
        return 0;
    }
    case WM_NCCALCSIZE:
        if (wp) {
            NCCALCSIZE_PARAMS *p = (NCCALCSIZE_PARAMS *)lp;
            int fx = FrameFx(), fy = FrameFy();
            p->rgrc[0].left += fx; p->rgrc[0].right -= fx; p->rgrc[0].bottom -= fy;
            if (IsZoomed(h)) p->rgrc[0].top += fy;          /* maximized: the frame is off-screen */
            return 0;
        }
        break;
    case WM_NCHITTEST: {
        LRESULT hit = DefWindowProcW(h, m, wp, lp);
        if (hit != HTCLIENT && hit != HTCAPTION && hit != HTNOWHERE && hit != HTSYSMENU &&
            hit != HTMINBUTTON && hit != HTMAXBUTTON && hit != HTCLOSE) return hit;
        POINT pt = { GET_X_LPARAM(lp), GET_Y_LPARAM(lp) }; ScreenToClient(h, &pt);
        RECT rc; GetClientRect(h, &rc);
        if (!IsZoomed(h) && pt.y >= 0 && pt.y < FrameFy() - Sc(2) + 1) {
            if (pt.x < Sc(16)) return HTTOPLEFT;
            if (pt.x >= rc.right - Sc(16)) return HTTOPRIGHT;
            return HTTOP;
        }
        if (pt.y >= 0 && pt.y < CapH()) {
            RECT rmin, rmax, rclose, rmenu; CapRects(&rmin, &rmax, &rclose, &rmenu);
            if (PtInRect(&rclose, pt)) return HTCLOSE;
            if (PtInRect(&rmax, pt)) return HTMAXBUTTON;      /* Win11 snap layouts flyout */
            if (PtInRect(&rmin, pt)) return HTMINBUTTON;
            if (PtInRect(&rmenu, pt)) return HTCLIENT;
            return HTCAPTION;
        }
        return HTCLIENT;
    }
    case WM_NCACTIVATE:
        g_active = wp != 0; InvalidateCaption();
        return DefWindowProcW(h, m, wp, -1);       /* -1: do not repaint the (non-existent) classic frame */
    case WM_NCMOUSEMOVE: {
        int hot = (wp == HTMINBUTTON || wp == HTMAXBUTTON || wp == HTCLOSE) ? (int)wp : 0;
        if (hot != g_capHot) { g_capHot = hot; InvalidateCaption(); }
        TRACKMOUSEEVENT t = { sizeof t, TME_LEAVE | TME_NONCLIENT, h, 0 }; TrackMouseEvent(&t);
        if (hot) return 0;
        break;
    }
    case WM_NCMOUSELEAVE:
        if (g_capHot != CAP_MENU || !g_capDown) { g_capHot = 0; g_capDown = 0; InvalidateCaption(); }
        break;
    case WM_NCLBUTTONDOWN:
        if (wp == HTMINBUTTON || wp == HTMAXBUTTON || wp == HTCLOSE) { CompleteComposition(); g_capDown = (int)wp; g_capHot = (int)wp; InvalidateCaption(); return 0; }
        CompleteComposition();
        break;
    case WM_NCLBUTTONDBLCLK:
        if (wp == HTMINBUTTON || wp == HTMAXBUTTON || wp == HTCLOSE) return 0;
        break;
    case WM_NCLBUTTONUP:
        if (wp == HTMINBUTTON || wp == HTMAXBUTTON || wp == HTCLOSE) {
            int d = g_capDown; g_capDown = 0; InvalidateCaption();
            if (d == (int)wp) {
                if (wp == HTMINBUTTON) ShowWindow(h, SW_MINIMIZE);
                else if (wp == HTMAXBUTTON) ShowWindow(h, IsZoomed(h) ? SW_RESTORE : SW_MAXIMIZE);
                else PostMessageW(h, WM_SYSCOMMAND, SC_CLOSE, 0);
            }
            return 0;
        }
        break;
    case WM_MOUSEMOVE: {
        RECT rmin, rmax, rclose, rmenu; CapRects(&rmin, &rmax, &rclose, &rmenu);
        POINT pt = { GET_X_LPARAM(lp), GET_Y_LPARAM(lp) };
        int hot = PtInRect(&rmenu, pt) ? CAP_MENU : 0;
        if (hot != g_capHot) { g_capHot = hot; InvalidateCaption(); }
        TRACKMOUSEEVENT t = { sizeof t, TME_LEAVE, h, 0 }; TrackMouseEvent(&t);
        return 0;
    }
    case WM_MOUSELEAVE:
        if (g_capHot == CAP_MENU) { g_capHot = 0; InvalidateCaption(); }
        return 0;
    case WM_LBUTTONDOWN: {
        RECT rmin, rmax, rclose, rmenu; CapRects(&rmin, &rmax, &rclose, &rmenu);
        POINT pt = { GET_X_LPARAM(lp), GET_Y_LPARAM(lp) };
        if (PtInRect(&rmenu, pt)) ShowMainMenu();
        return 0;
    }
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: FramePaint(h); return 0;
    case WM_SIZE:
        FrameLayout();
        InvalidateCaption();
        return 0;
    case WM_SETTEXT: {
        LRESULT r = DefWindowProcW(h, m, wp, lp);
        InvalidateCaption();
        return r;
    }
    case WM_GETMINMAXINFO: {
        MINMAXINFO *mi = (MINMAXINFO *)lp;
        mi->ptMinTrackSize.x = Sc(360); mi->ptMinTrackSize.y = Sc(200);
        return 0;
    }
    case WM_DPICHANGED: {
        g_dpi = HIWORD(wp);
        SetupFont(); g_findFontSet = NULL;
        const RECT *r = (const RECT *)lp;
        SetWindowPos(h, NULL, r->left, r->top, r->right - r->left, r->bottom - r->top, SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED);
        FrameLayout();
        Refresh(TRUE);
        InvalidateRect(h, NULL, FALSE);
        if (g_find) InvalidateRect(g_find, NULL, FALSE);
        return 0;
    }
    case WM_ACTIVATE:
        if (LOWORD(wp) != WA_INACTIVE) {
            HWND f = (g_lastFocus && IsWindowVisible(g_lastFocus)) ? g_lastFocus : g_hwnd;
            SetFocus(f);
        }
        return 0;
    case WM_SETFOCUS:
        SetFocus((g_lastFocus && IsWindowVisible(g_lastFocus)) ? g_lastFocus : g_hwnd);
        return 0;
    case WM_ENTERMENULOOP: case WM_ENTERSIZEMOVE:
        CompleteComposition();
        break;
    case WM_COMMAND:
        DoCommand(LOWORD(wp));
        return 0;
    case WM_DROPFILES: {
        WCHAR p[MAX_PATH * 4];
        if (DragQueryFileW((HDROP)wp, 0, p, sizeof p / sizeof p[0]) && ConfirmDiscard()) { if (g_mdView) SetMdView(FALSE); LoadFile(p); }
        DragFinish((HDROP)wp);
        return 0;
    }
    case WM_CLOSE:
        CompleteComposition();
        if (ConfirmDiscard()) { SaveIni(); DestroyWindow(h); }
        return 0;
    case WM_APP + 1:
        if (g_bench) RunBench(); else if (g_demo[0]) RunDemo(); else RunSelfTest();
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(h, m, wp, lp);
}

/* ================================================================== */
/* self test (editor.exe --selftest log.txt)                           */
/* ================================================================== */
static FILE *g_stf; static int g_stfail, g_stcount;
static void STLog(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    if (g_stf) { vfprintf(g_stf, fmt, ap); fflush(g_stf); }
    va_end(ap);
}
static void STCheck(int ok, const char *what) { g_stcount++; STLog("[%s] %s\n", ok ? "OK" : "NG", what); if (!ok) g_stfail++; }
static int PrefixW(const WCHAR *s, int n) {   /* independent reference: GetTextExtentPoint32 on a fresh DC */
    HDC dc = GetDC(g_hwnd); HGDIOBJ o = SelectObject(dc, g_font);
    SIZE z = { 0, 0 }; if (n) GetTextExtentPoint32W(dc, s, n, &z);
    SelectObject(dc, o); ReleaseDC(g_hwnd, dc); return z.cx;
}
static const char *W2U(const WCHAR *w) {   /* UTF-8 for the log (rotating buffers) */
    static char b[4][1024]; static int k;
    k = (k + 1) & 3;
    if (!WideCharToMultiByte(CP_UTF8, 0, w, -1, b[k], 1024, NULL, NULL)) b[k][0] = 0;
    return b[k];
}
static BOOL HasStyle(DWORD st) { return (GetWindowLongW(g_hwnd, GWL_STYLE) & st) != 0; }
static void SetTextForTest(const WCHAR *t) {
    SetDocText(t, wcslen(t)); ResetDoc(); g_comp = FALSE; ClearComp();
    UpdateScrollBars(); Invalidate(); UpdateWindow(g_hwnd); UpdateScrollBars();
}
static BOOL DocEquals(const WCHAR *t) {
    size_t n = wcslen(t);
    if (DocLen() != n) return FALSE;
    for (size_t i = 0; i < n; i++) if (DocAt(i) != t[i]) return FALSE;
    return TRUE;
}
static BOOL IndexConsistent(void) {        /* incremental line index vs full recount */
    size_t len = DocLen(), L = 0;
    if (LineStart(0) != 0) return FALSE;
    for (size_t i = 0; i < len; i++)
        if (DocAt(i) == L'\n') { L++; if (L >= g_nl || LineStart(L) != i + 1) return FALSE; }
    return L + 1 == g_nl;
}
static int CompactAll(void) { int g = 0; while (!CompactStep(1 << 16) && g < 100000) g++; ReleaseUnused(); return g; }
static int CollectMatches(size_t *out, int max) {   /* all matches by repeated FindFrom (stops when it wraps) */
    size_t a, b, pos = 0; int k = 0;
    while (k + 2 <= max && FindFrom(pos, TRUE, &a, &b)) {
        if (k && a <= out[k - 2]) break;
        out[k++] = a; out[k++] = b; pos = b;
    }
    return k;
}
static int RefMatches(Regex *re, const WCHAR *ref, size_t rn, size_t *out, int max) {
    int k = 0, caps[2 * RE_NCAP];
    for (size_t s0 = 0; s0 <= rn; ) {
        size_t e = s0; while (e < rn && ref[e] != L'\n') e++;
        int n = (int)(e - s0), s = 0;
        while (s <= n && k + 2 <= max && re_search(re, (const rechar *)ref + s0, n, s, caps)) {
            if (caps[1] > caps[0]) { out[k++] = s0 + (size_t)caps[0]; out[k++] = s0 + (size_t)caps[1]; s = caps[1]; } else s = caps[0] + 1;
        }
        s0 = e + 1;
    }
    return k;
}
static char *ReadAll(const WCHAR *p, size_t *n) {
    HANDLE f = CreateFileW(p, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (f == INVALID_HANDLE_VALUE) return NULL;
    DWORD sz = GetFileSize(f, NULL), rd = 0; char *b = xmalloc((size_t)sz + 1);
    ReadFile(f, b, sz, &rd, NULL); CloseHandle(f); *n = rd; return b;
}
static double NowMs(void);
static void SetComp(const WCHAR *comp) {
    BeginComp();
    g_clen = (int)wcslen(comp);
    g_cstr = xrealloc(g_cstr, (size_t)(g_clen + 1) * sizeof(WCHAR)); memcpy(g_cstr, comp, (size_t)g_clen * sizeof(WCHAR));
    g_cattr = xrealloc(g_cattr, (size_t)g_clen + 1);
    for (int i = 0; i < g_clen; i++) g_cattr[i] = i < 2 ? ATTR_TARGET_CONVERTED : (i < 5 ? ATTR_CONVERTED : ATTR_INPUT);
    g_ccl = xrealloc(g_ccl, 4 * sizeof(DWORD)); g_ccl[0] = 0; g_ccl[1] = 2; g_ccl[2] = 5; g_ccl[3] = (DWORD)g_clen; g_nccl = 4;
    g_ccur = 2; g_cpos = g_caret; g_compVer++;
}
static int MdVisible(const WCHAR *src, WCHAR *vis, WORD *st, int cap) {
    MdOut o; memset(&o, 0, sizeof o);
    MdInline(src, (int)wcslen(src), 0, &o);
    int k = 0;
    for (int i = 0; i < o.n && k < cap - 1; i++) if (!(o.s[i] & S_HIDE)) { vis[k] = o.t[i]; if (st) st[k] = o.s[i]; k++; }
    vis[k] = 0;
    free(o.t); free(o.s);
    return k;
}
static int LineCopy(size_t L, BOOL comp, WCHAR *t, int cap) {   /* display text of line L */
    LayoutLine(L, comp);
    int n = g_ln.n < cap - 1 ? g_ln.n : cap - 1;
    LnGet(&g_ln, 0, n, t); t[n] = 0;
    return n;
}
static int LineX(size_t L, BOOL comp, int i) { LayoutLine(L, comp); return XOf(&g_ln, i); }
/* draws t[0, n) of line 0 into a DIB twice: GDI's own layout (no lpDx) and the editor's lpDx; returns differing pixels */
static int DrawCompare(const WCHAR *t, int n) {
    LayoutLine(0, FALSE); Win(&g_ln, 0, n);
    int w = LX(n) + 64, h = g_lineH, diff = 0;
    BITMAPINFO bi; memset(&bi, 0, sizeof bi);
    bi.bmiHeader.biSize = sizeof bi.bmiHeader; bi.bmiHeader.biWidth = w; bi.bmiHeader.biHeight = -h;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32;
    DWORD *px[2]; HBITMAP bm[2]; HDC dc = CreateCompatibleDC(NULL);
    int *dx = xmalloc(((size_t)n + 1) * sizeof(int));
    RunDx(0, n, dx);
    for (int v = 0; v < 2; v++) {
        bm[v] = CreateDIBSection(dc, &bi, DIB_RGB_COLORS, (void **)&px[v], NULL, 0);
        HGDIOBJ ob = SelectObject(dc, bm[v]), of = SelectObject(dc, g_font);
        FillR(dc, 0, 0, w, h, C_BG); SetBkMode(dc, TRANSPARENT); SetTextColor(dc, C_TEXT);
        ExtTextOutW(dc, 8, 0, 0, NULL, t, (UINT)n, v ? dx : NULL);
        GdiFlush(); SelectObject(dc, of); SelectObject(dc, ob);
    }
    for (int k = 0; k < w * h; k++) diff += px[0][k] != px[1][k];
    DeleteObject(bm[0]); DeleteObject(bm[1]); DeleteDC(dc); free(dx);
    return diff;
}
/* copies the client area (screen = 1) or the back buffer into a malloc'ed 32 bpp pixel array */
static DWORD *Grab(BOOL screen) {
    int w = g_cw, h = g_ch;
    BITMAPINFO bi; memset(&bi, 0, sizeof bi);
    bi.bmiHeader.biSize = sizeof bi.bmiHeader; bi.bmiHeader.biWidth = w; bi.bmiHeader.biHeight = -h;
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32;
    DWORD *px; HDC dc = CreateCompatibleDC(NULL);
    HBITMAP bm = CreateDIBSection(dc, &bi, DIB_RGB_COLORS, (void **)&px, NULL, 0);
    HGDIOBJ ob = SelectObject(dc, bm);
    HDC src = screen ? GetDC(g_hwnd) : g_bb;
    BitBlt(dc, 0, 0, w, h, src, 0, 0, SRCCOPY); GdiFlush();
    if (screen) ReleaseDC(g_hwnd, src);
    DWORD *out = xmalloc((size_t)w * h * sizeof(DWORD)); memcpy(out, px, (size_t)w * h * sizeof(DWORD));
    SelectObject(dc, ob); DeleteObject(bm); DeleteDC(dc);
    return out;
}
static int PixDiff(const DWORD *a, const DWORD *b) { int d = 0; for (int k = 0; k < g_cw * g_ch; k++) d += (a[k] & 0xFFFFFF) != (b[k] & 0xFFFFFF); return d; }
/* composition geometry checks (v1.0.1): underline end, caret, IMR_QUERYCHARPOSITION, candidate rect */
static void STComp(const char *tag) {
    char buf[512];
    SetTextForTest(L"前置き");
    g_caret = g_anchor = 3;
    SetComp(L"長井文章をへんかんすると");
    Refresh(TRUE); UpdateWindow(g_hwnd);
    WCHAR t[256]; int n = LineCopy(0, TRUE, t, 256), co = g_ln.co;
    int full = PrefixW(t, n), endx = LineX(0, TRUE, co + g_clen);
    snprintf(buf, sizeof buf, "%scomposition end x=%d vs reference width=%d (underline ends here)", tag, endx, full);
    STCheck(abs(endx - full) <= 1, buf);
    POINT cp; GetCaretPos(&cp);
    int expect = g_margin + PrefixW(t, co + 2);
    snprintf(buf, sizeof buf, "%scaret in composition (GCS_CURSORPOS=2): x=%ld expected=%d", tag, cp.x, expect);
    STCheck(labs(cp.x - expect) <= 1, buf);
    int maxd = 0;
    for (int k = 0; k <= g_clen; k++) {
        IMECHARPOSITION ip; memset(&ip, 0, sizeof ip); ip.dwSize = sizeof ip; ip.dwCharPos = (DWORD)k;
        OnImeRequest(IMR_QUERYCHARPOSITION, (LPARAM)&ip);
        POINT p = ip.pt; ScreenToClient(g_hwnd, &p);
        int e = g_margin + PrefixW(t, co + k);
        int d = abs(p.x - e); if (d > maxd) maxd = d;
    }
    snprintf(buf, sizeof buf, "%sIMR_QUERYCHARPOSITION max diff=%dpx", tag, maxd);
    STCheck(maxd <= 1, buf);
    CANDIDATEFORM cf; memset(&cf, 0, sizeof cf);
    OnImeRequest(IMR_CANDIDATEWINDOW, (LPARAM)&cf);
    expect = g_margin + PrefixW(t, co);
    snprintf(buf, sizeof buf, "%scandidate CFS_EXCLUDE rect=(%ld,%ld)-(%ld,%ld), target clause starts at x=%d", tag,
             cf.rcArea.left, cf.rcArea.top, cf.rcArea.right, cf.rcArea.bottom, expect);
    STCheck(labs(cf.rcArea.left - expect) <= 1 && labs(cf.rcArea.right - (g_margin + PrefixW(t, co + 2))) <= 1, buf);
    g_comp = FALSE; ClearComp();
}
static void RunSelfTest(void) {
    char buf[512];
    g_stf = _wfopen(g_stlog, L"w");
    if (!g_stf) {
        WCHAR msg[MAX_PATH * 4 + 128];
        _snwprintf(msg, sizeof msg / sizeof msg[0], L"セルフテストのログファイルを開けません:\n%ls\n\nフォルダーが存在し、書き込み可能か確認してください。\n(テストは続行し、結果をこの後メッセージで表示します)", g_stlog);
        msg[sizeof msg / sizeof msg[0] - 1] = 0;
        MessageBoxW(g_frame, msg, APPNAME L" セルフテスト", MB_ICONERROR);
    }
    SetFocus(g_hwnd);
    g_wrap = FALSE; g_showWs = FALSE; g_layoutVer++;
    RECT rc; GetClientRect(g_hwnd, &rc);
    STLog("CEditor %s selftest\ndpi=%u client=%ldx%ld lineH=%d font=%s\n", W2U(APPVER), g_dpi, rc.right, rc.bottom, g_lineH, W2U(g_lf.lfFaceName));
    /* ---- 1. one measurement path (v1.0.1 checks) ---- */
    static const WCHAR *const lines[] = { L"テスト", L"abc def_ghi XYZ", L"長井文章をへんかんすると下線が長くなります",
                                          L"𠮷野家😀と絵文字", L"ｱｲｳ半角ｶﾅ ﾃｽﾄ mixed 全角ＡＢＣ" };
    for (int li = 0; li < 5; li++) {
        SetTextForTest(lines[li]);
        WCHAR t[256]; int n = LineCopy(0, FALSE, t, 256), maxd = 0;
        for (int i = 0; i <= n; i++) {
            if (i < n && IS_LO(t[i])) continue;
            int d = abs(LineX(0, FALSE, i) - PrefixW(t, i)); if (d > maxd) maxd = d;
        }
        snprintf(buf, sizeof buf, "line %d: positions (width dictionary) vs GetTextExtentPoint32 prefix, max diff=%dpx (width=%d)", li, maxd, LineX(0, FALSE, n));
        STCheck(maxd <= 1, buf);
    }
    SetTextForTest(L"テスト");
    g_caret = g_anchor = 3; OnKeyDown(VK_LEFT);
    POINT cp; GetCaretPos(&cp);
    int expect = g_margin + PrefixW(L"テスト", 2);
    snprintf(buf, sizeof buf, "caret after Left: GetCaretPos.x=%ld expected=%d (caret index %u)", cp.x, expect, (unsigned)g_caret);
    STCheck(labs(cp.x - expect) <= 1 && g_caret == 2, buf);
    size_t hp = PosFromPoint(expect + 1, g_lineH / 2);
    snprintf(buf, sizeof buf, "hit test at x=%d -> pos %u (expected 2)", expect + 1, (unsigned)hp);
    STCheck(hp == 2, buf);
    SetTextForTest(L"a\tb");
    snprintf(buf, sizeof buf, "tab: x(b)=%d expected=%d", LineX(0, FALSE, 2), g_tabW);
    STCheck(LineX(0, FALSE, 2) == g_tabW, buf);
    /* ---- 2. composition ---- */
    STComp("");
    /* ---- 3. scrollbars only when needed ---- */
    SetTextForTest(L"1行目\n2行目\n3行目");
    snprintf(buf, sizeof buf, "3 lines: VSCROLL visible=%d HSCROLL visible=%d (expect 0 0)", HasStyle(WS_VSCROLL), HasStyle(WS_HSCROLL));
    STCheck(!HasStyle(WS_VSCROLL) && !HasStyle(WS_HSCROLL), buf);
    {
        int vis = VisLines(); size_t n = (size_t)vis;
        WCHAR *t = xmalloc((n * 2 + 2) * sizeof(WCHAR));
        for (size_t i = 0; i < n; i++) { t[i * 2] = L'x'; t[i * 2 + 1] = L'\n'; }
        t[n * 2 - 1] = 0;
        SetTextForTest(t);
        snprintf(buf, sizeof buf, "%d lines (= visible lines): VSCROLL visible=%d (expect 0)", vis, HasStyle(WS_VSCROLL));
        STCheck(!HasStyle(WS_VSCROLL), buf);
        t[n * 2 - 1] = L'\n'; t[n * 2] = 0;
        SetTextForTest(t);
        snprintf(buf, sizeof buf, "%d lines: VSCROLL visible=%d (expect 1)", vis + 1, HasStyle(WS_VSCROLL));
        STCheck(HasStyle(WS_VSCROLL), buf);
        free(t);
    }
    WCHAR longl[401]; for (int i = 0; i < 400; i++) longl[i] = (i % 7 == 6) ? L' ' : L'あ'; longl[400] = 0;
    SetTextForTest(longl);
    snprintf(buf, sizeof buf, "long line: HSCROLL visible=%d (expect 1)", HasStyle(WS_HSCROLL));
    STCheck(HasStyle(WS_HSCROLL), buf);
    SetTextForTest(L"短い");
    snprintf(buf, sizeof buf, "back to short text: VSCROLL=%d HSCROLL=%d (expect 0 0)", HasStyle(WS_VSCROLL), HasStyle(WS_HSCROLL));
    STCheck(!HasStyle(WS_VSCROLL) && !HasStyle(WS_HSCROLL), buf);

    /* ---- 4. word wrap ---- */
    g_wrap = TRUE; g_layoutVer++;
    SetTextForTest(longl);
    {
        LayoutLine(0, FALSE);
        int W = WrapW(), worst = 0, rows = EnsureRows(&g_ln, INT_MAX);
        for (int r = 0; r < rows; r++) { int w = XOf(&g_ln, RowEnd(r)) - XOf(&g_ln, RowStart(r)); if (w > worst) worst = w; }
        snprintf(buf, sizeof buf, "wrap: 400-char line -> %d rows, widest row %dpx <= wrap width %dpx, HSCROLL=%d (expect 0)", rows, worst, W, HasStyle(WS_HSCROLL));
        STCheck(rows > 1 && worst <= W && !HasStyle(WS_HSCROLL), buf);
        int bad = 0;
        for (size_t p = 0; p <= 400; p += 3) {
            g_caret = g_anchor = p; g_aff = FALSE; EnsureVisible();
            POINT pt; CaretPoint(&pt, NULL);
            BOOL aff; size_t q = PosFromPointEx(pt.x, pt.y + g_lineH / 2, &aff);
            if (q != p) { if (bad < 3) STLog("   wrap round trip mismatch: pos %u -> (%ld,%ld) -> %u\n", (unsigned)p, pt.x, pt.y, (unsigned)q); bad++; }
        }
        snprintf(buf, sizeof buf, "wrap: caret point -> hit test round trip, mismatches=%d", bad);
        STCheck(bad == 0, buf);
        /* End on a wrapped row stays on that row (affinity) */
        g_caret = g_anchor = 0; g_aff = FALSE; g_top = 0; g_topRow = 0;
        OnKeyDown(VK_END);
        POINT pe; CaretPoint(&pe, NULL);
        LayoutLine(0, FALSE);
        snprintf(buf, sizeof buf, "wrap: End -> pos %u (row 1 starts at %d), caret y=%ld (expect 0)", (unsigned)g_caret, RowStart(1), pe.y);
        STCheck(g_caret == (size_t)RowStart(1) && pe.y == 0, buf);
        OnKeyDown(VK_DOWN);
        snprintf(buf, sizeof buf, "wrap: Down moves one visual row (pos %u, row %d)", (unsigned)g_caret, RowOf((int)g_caret));
        LayoutLine(0, FALSE);
        STCheck(RowOf((int)g_caret) == 1 || (g_aff && RowOf((int)g_caret) == 2), buf);
    }
    SetTextForTest(L"a\nb\nc");
    snprintf(buf, sizeof buf, "wrap: 3 short lines VSCROLL=%d HSCROLL=%d (expect 0 0)", HasStyle(WS_VSCROLL), HasStyle(WS_HSCROLL));
    STCheck(!HasStyle(WS_VSCROLL) && !HasStyle(WS_HSCROLL), buf);
    g_wrap = FALSE; g_layoutVer++;

    /* ---- 5. incremental line index ---- */
    {
        SetTextForTest(L"");
        unsigned seed = 12345; int bad = 0;
        static const WCHAR *const ins[] = { L"abc", L"\n", L"あ\nい\n", L"\n\n", L"xyz\n", L"😀" };
        for (int it = 0; it < 3000; it++) {
            seed = seed * 1103515245u + 12345u;
            size_t len = DocLen(), p = len ? (seed >> 8) % (len + 1) : 0;
            if ((seed >> 4) % 3 == 0 && len > 0) {
                size_t n = 1 + (seed >> 12) % 5; if (p + n > len) n = len - p;
                RawDelete(p, n);
            } else { const WCHAR *s = ins[(seed >> 16) % 6]; RawInsert(p, s, wcslen(s)); }
            if (it % 97 == 0 && !IndexConsistent()) bad++;
        }
        if (!IndexConsistent()) bad++;
        snprintf(buf, sizeof buf, "line index: 3000 random edits, inconsistencies=%d (len=%u lines=%u)", bad, (unsigned)DocLen(), (unsigned)g_nl);
        STCheck(bad == 0, buf);
        /* cost of typing in the middle of a big document */
        size_t N = 300000; WCHAR *big = xmalloc((N * 4 + 1) * sizeof(WCHAR));
        for (size_t i = 0; i < N; i++) { big[i * 4] = L'a'; big[i * 4 + 1] = L'b'; big[i * 4 + 2] = L'c'; big[i * 4 + 3] = L'\n'; }
        big[N * 4] = 0;
        SetDocText(big, N * 4); ResetDoc(); free(big);
        double t0 = NowMs();
        size_t mid = LineStart(N / 2);
        for (int i = 0; i < 2000; i++) { RawInsert(mid + (size_t)i, (i % 10 == 9) ? L"\n" : L"x", 1); }
        double t1 = NowMs();
        snprintf(buf, sizeof buf, "line index: 2000 inserts in the middle of %u lines took %.1f ms, consistent=%d", (unsigned)N, t1 - t0, IndexConsistent());
        STCheck(IndexConsistent() && t1 - t0 < 2000, buf);
    }
    /* ---- 5b. piece table: random edits against a plain reference string ---- */
    {
        static const WCHAR *const ins[] = { L"a", L"bc", L"\n", L"あい\nう", L"😀", L"\t", L"xyz\n\n", L"漢字かな交じり文" };
        SetTextForTest(L"初期テキスト\n二行目\n😀end");
        size_t rn = DocLen(), rcap = 1 << 16, last = 0;
        WCHAR *ref = xmalloc(rcap * sizeof(WCHAR)), *tmp = xmalloc(rcap * sizeof(WCHAR));
        DocGet(0, rn, ref);
        unsigned seed = 4242; int bad = 0;
        for (int it = 0; it < 6000; it++) {
            seed = seed * 1103515245u + 12345u;
            size_t len = DocLen(), p = (seed >> 3) % 4 == 0 ? last : (len ? (seed >> 8) % (len + 1) : 0);
            if (p > len) p = len;
            if ((seed >> 5) % 3 == 0 && len > 0) {
                size_t n = 1 + (seed >> 12) % 9; if (p + n > len) n = len - p;
                RawDelete(p, n); memmove(ref + p, ref + p + n, (rn - p - n) * sizeof(WCHAR)); rn -= n; last = p;
            } else {
                const WCHAR *t = ins[(seed >> 16) % 8]; size_t n = wcslen(t);
                if (rn + n >= rcap) break;
                memmove(ref + p + n, ref + p, (rn - p) * sizeof(WCHAR)); memcpy(ref + p, t, n * sizeof(WCHAR)); rn += n;
                RawInsert(p, t, n); last = p + n;
            }
            if (it % 250 == 0 || it == 5999) {
                DocGet(0, DocLen(), tmp);
                if (DocLen() != rn || memcmp(tmp, ref, rn * sizeof(WCHAR)) || !IndexConsistent()) bad++;
                for (int k = 0; k < 50 && rn; k++) { size_t q = (seed + (unsigned)k * 7919u) % rn; if (DocAt(q) != ref[q]) { bad++; break; } }
            }
        }
        size_t pieces = g_npc;
        snprintf(buf, sizeof buf, "piece table: 6000 random edits vs reference string, mismatches=%d (len=%u pieces=%u lines=%u)", bad, (unsigned)rn, (unsigned)pieces, (unsigned)g_nl);
        STCheck(bad == 0 && pieces > 1, buf);
        CompactAll();
        DocGet(0, DocLen(), tmp);
        BOOL ok = g_npc < pieces && DocLen() == rn && !memcmp(tmp, ref, rn * sizeof(WCHAR)) && IndexConsistent();
        snprintf(buf, sizeof buf, "piece table: compaction %u pieces -> %u, text and line index unchanged=%d", (unsigned)pieces, (unsigned)g_npc, ok);
        STCheck(ok, buf);
        free(ref); free(tmp);
    }
    {
        static const WCHAR *const ins[] = { L"x", L"かな", L"\n", L"😀", L"ab\ncd" };
        SetTextForTest(L"undo の元テキスト\n2行目\n3行目");
        size_t n0 = DocLen(); WCHAR *orig = xmalloc((n0 + 1) * sizeof(WCHAR)); DocGet(0, n0, orig); orig[n0] = 0;
        unsigned seed = 99;
        for (int it = 0; it < 400; it++) {
            seed = seed * 1103515245u + 12345u;
            size_t len = DocLen(), p = len ? (seed >> 8) % (len + 1) : 0;
            NewGroup();
            if ((seed >> 4) % 3 == 0 && len) { size_t n = 1 + (seed >> 12) % 4; if (p + n > len) n = len - p; EditDelete(p, n); }
            else { const WCHAR *t = ins[(seed >> 16) % 5]; EditInsert(p, t, wcslen(t)); }
        }
        size_t n1 = DocLen(); WCHAR *fin = xmalloc((n1 + 1) * sizeof(WCHAR)); DocGet(0, n1, fin); fin[n1] = 0;
        int undos = 0; while (g_undo.n) { Undo(); undos++; }
        BOOL u = DocEquals(orig) && IndexConsistent();
        while (g_redo.n) Redo();
        BOOL rr = DocEquals(fin) && IndexConsistent();
        snprintf(buf, sizeof buf, "undo/redo: 400 random edits, %d undo steps restore the original=%d, redo restores the result=%d", undos, u, rr);
        STCheck(u && rr, buf);
        free(orig); free(fin);
    }
    /* ---- 5j. v1.3: background compaction, in-place search, long-line chunks, save, released memory, loading ---- */
    {   /* random edits interleaved with idle compaction steps vs a reference string; undo / redo across compaction */
        size_t cap = 1 << 20, n = 0; WCHAR *t = xmalloc(cap * sizeof(WCHAR));
        for (int L = 0; L < 3000; L++) {
            if (L == 1500) { for (int i = 0; i < 60000; i++) t[n++] = L"長い行の中身abcdefg "[i % 13]; t[n++] = L'\n'; }
            n += (size_t)swprintf(t + n, 80, L"%04d: 行のテキスト line text %d\n", L, L * 7);
        }
        t[n] = 0; SetTextForTest(t);
        WCHAR *ref = xmalloc(cap * sizeof(WCHAR)); memcpy(ref, t, n * sizeof(WCHAR)); size_t rn = n;
        static const WCHAR *const ins[] = { L"x", L"かな", L"\n", L"😀", L"ab\ncd", L"挿入テキスト挿入テキスト" };
        unsigned seed = 777; int bad = 0, steps = 0;
        for (int it = 0; it < 3000; it++) {
            seed = seed * 1103515245u + 12345u;
            size_t len = DocLen(), p = (seed >> 8) % (len + 1);
            NewGroup();
            if ((seed >> 4) % 3 == 0 && len) {
                size_t k = 1 + (seed >> 12) % 40; if (p + k > len) k = len - p;
                EditDelete(p, k); memmove(ref + p, ref + p + k, (rn - p - k) * sizeof(WCHAR)); rn -= k;
            } else {
                const WCHAR *s = ins[(seed >> 16) % 6]; size_t m = wcslen(s);
                if (rn + m >= cap) break;
                EditInsert(p, s, m); memmove(ref + p + m, ref + p, (rn - p) * sizeof(WCHAR)); memcpy(ref + p, s, m * sizeof(WCHAR)); rn += m;
            }
            if ((seed >> 20) % 4 == 0) { CompactStep((int)((seed >> 22) % 300)); steps++; }
            if ((seed >> 24) % 64 == 0) ReleaseUnused();
            if (it % 300 == 299) { DocGet(0, DocLen(), t); if (DocLen() != rn || memcmp(t, ref, rn * sizeof(WCHAR)) || !IndexConsistent()) bad++; }
        }
        size_t pc0 = g_npc; int g = CompactAll();
        DocGet(0, DocLen(), t);
        BOOL same = DocLen() == rn && !memcmp(t, ref, rn * sizeof(WCHAR)) && IndexConsistent();
        size_t split = 0; for (size_t L = 0; L < g_nl; L++) if (LineEnd(L) - LineStart(L) <= CHUNK / 2 && !LineContiguous(L)) split++;
        snprintf(buf, sizeof buf, "compaction: 3000 random edits with %d idle compaction steps vs reference, mismatches=%d; full compaction (%d slices) %u -> %u pieces, text same=%d, short lines not contiguous=%u",
                 steps, bad, g, (unsigned)pc0, (unsigned)g_npc, same, (unsigned)split);
        STCheck(bad == 0 && same && g_cdone && split == 0 && g_npc < pc0, buf);
        WCHAR *fin = ref; ref = xmalloc(cap * sizeof(WCHAR));
        int u = 0; while (g_undo.n) { Undo(); if (++u % 37 == 0) { CompactStep(400); ReleaseUnused(); } }
        DocGet(0, DocLen(), ref);
        size_t n2 = 0;                      /* t was overwritten above: rebuild the original */
        for (int L = 0; L < 3000; L++) {
            if (L == 1500) { for (int i = 0; i < 60000; i++) t[n2++] = L"長い行の中身abcdefg "[i % 13]; t[n2++] = L'\n'; }
            n2 += (size_t)swprintf(t + n2, 80, L"%04d: 行のテキスト line text %d\n", L, L * 7);
        }
        BOOL uo = DocLen() == n2 && !memcmp(ref, t, n2 * sizeof(WCHAR)) && IndexConsistent();
        int r = 0; while (g_redo.n) { Redo(); if (++r % 41 == 0) { CompactStep(400); ReleaseUnused(); } }
        CompactAll(); DocGet(0, DocLen(), ref);
        BOOL ro = DocLen() == rn && !memcmp(ref, fin, rn * sizeof(WCHAR)) && IndexConsistent();
        snprintf(buf, sizeof buf, "compaction: %d undo steps interleaved with compaction restore the original=%d, %d redo steps restore the result=%d", u, uo, r, ro);
        STCheck(uo && ro, buf);
        free(t); free(ref); free(fin);
    }
    {   /* search on in-place (compacted) and copied (not yet compacted) lines == reference search */
        static const WCHAR *const words[] = { L"foo12", L"bar", L"fooo7", L"ばー", L"バー", L"x", L"foo", L"f0o9", L" ", L"漢字" };
        size_t cap = 1 << 19, n = 0; WCHAR *t = xmalloc(cap * sizeof(WCHAR)); unsigned seed = 31337;
        for (int L = 0; L < 2000; L++) {
            seed = seed * 1103515245u + 12345u;
            for (int w = (int)((seed >> 8) % 12); w > 0; w--) { seed = seed * 1103515245u + 12345u; const WCHAR *s = words[(seed >> 10) % 10]; size_t m = wcslen(s); memcpy(t + n, s, m * sizeof(WCHAR)); n += m; }
            t[n++] = L'\n';
        }
        t[n] = 0; SetTextForTest(t);
        int ep; Regex *re = re_compile((const rechar *)L"fo+\\d+|バー", 10, 0, &ep), *sv = g_re; g_re = re;
        int bad = 0; size_t *got = xmalloc(40000 * sizeof(size_t)), *exp = xmalloc(40000 * sizeof(size_t));
        size_t inplace = 0, copied = 0;
        for (int round = 0; round < 2; round++) {
            for (int it = 0; it < 1500; it++) {
                seed = seed * 1103515245u + 12345u;
                size_t len = DocLen(), p = (seed >> 8) % (len + 1);
                NewGroup();
                if ((seed >> 4) % 4 == 0 && len) { size_t k = 1 + (seed >> 12) % 5; if (p + k > len) k = len - p; EditDelete(p, k); }
                else { const WCHAR *s = words[(seed >> 16) % 10]; EditInsert(p, s, wcslen(s)); }
                if ((seed >> 22) % 8 == 0) CompactStep(64);
            }
            for (size_t L = 0; L < g_nl; L++) { if (LineContiguous(L)) inplace++; else copied++; }
            size_t rn = DocLen(); WCHAR *ref = xmalloc((rn + 1) * sizeof(WCHAR)); DocGet(0, rn, ref);
            int k1 = CollectMatches(got, 40000), k2 = RefMatches(re, ref, rn, exp, 40000);
            if (k1 != k2 || memcmp(got, exp, (size_t)k1 * sizeof(size_t))) bad++;
            CompactAll();
            int k3 = CollectMatches(got, 40000);
            if (k3 != k2 || memcmp(got, exp, (size_t)k3 * sizeof(size_t))) bad++;
            snprintf(buf, sizeof buf, "  round %d: %d matches", round, k2 / 2); STLog("%s\n", buf);
            free(ref);
        }
        snprintf(buf, sizeof buf, "search: in-place lines (%u) and copied lines (%u) vs reference search, 2 rounds before/after compaction: mismatching rounds=%d",
                 (unsigned)inplace, (unsigned)copied, bad);
        STCheck(bad == 0 && inplace > 0 && copied > 0, buf);
        g_re = sv; re_free(re); free(got); free(exp); free(t);
    }
    {   /* a very long line is stored in chunks; matches across chunk borders, caret and End treat it as one line */
        size_t N = 300000; WCHAR *t = xmalloc((N + 16) * sizeof(WCHAR)); unsigned seed = 4711;
        for (size_t i = 0; i < N; i++) { seed = seed * 1103515245u + 12345u; t[i] = (WCHAR)(L'a' + (seed >> 16) % 26); }
        wcscpy(t + N, L"\n二行目"); SetTextForTest(t);
        size_t rn = N + 4; WCHAR *ref = xmalloc((rn + 400) * sizeof(WCHAR)); memcpy(ref, t, rn * sizeof(WCHAR));
        for (int k = 0; k < 200; k++) {
            seed = seed * 1103515245u + 12345u; size_t p = (seed >> 4) % LineEnd(0);
            NewGroup(); EditInsert(p, L"Q", 1); memmove(ref + p + 1, ref + p, (rn - p) * sizeof(WCHAR)); ref[p] = L'Q'; rn++;
        }
        CompactAll(); ref[rn] = 0;
        size_t e0 = LineEnd(0), pcs = 0; int tried = 0, bad = 0;
        for (size_t k = 0; k < g_npc && g_pc[k].pos < e0; k++) {
            pcs++;
            size_t q = g_pc[k].pos;
            if (q < 8 || q + 8 > e0 || tried >= 40) continue;
            WCHAR nd[16]; memcpy(nd, ref + q - 5, 10 * sizeof(WCHAR)); nd[10] = 0;
            const WCHAR *f = wcsstr(ref, nd); size_t want = (size_t)(f - ref);
            int ep; Regex *re = re_compile((const rechar *)nd, 10, 0, &ep), *sv = g_re; g_re = re;
            size_t a = 0, b = 0; BOOL ok = FindFrom(0, TRUE, &a, &b);
            g_re = sv; re_free(re); tried++;
            if (!ok || a != want || b != want + 10) bad++;
        }
        int n; const WCHAR *lt = LineText(0, &n);
        BOOL one = g_nl == 2 && (size_t)n == e0 && !memcmp(lt, ref, e0 * sizeof(WCHAR)) && !LineContiguous(0);
        g_caret = g_anchor = 0; OnKeyDown(VK_END); BOOL end = g_caret == e0;
        snprintf(buf, sizeof buf, "long line: 300000 chars + 200 edits stored as %u pieces; matches across %d chunk borders found=%d/%d, one logical line=%d, End -> line end=%d",
                 (unsigned)pcs, tried, tried - bad, tried, one, end);
        STCheck(pcs > 10 && tried > 10 && bad == 0 && one && end, buf);
        free(t); free(ref);
    }
    {   /* save output: uncompacted == compacted == reference */
        size_t cap = 200000, n = 0; WCHAR *t = xmalloc(cap * sizeof(WCHAR));
        for (int L = 0; L < 2000; L++) n += (size_t)swprintf(t + n, 64, L"保存テスト %d 😀\tend\n", L);
        t[n] = 0; SetTextForTest(t); int e0 = g_enc; g_enc = 0;
        unsigned seed = 5; static const WCHAR *const ins[] = { L"y", L"\n", L"日本", L"😀" };
        for (int it = 0; it < 500; it++) {
            seed = seed * 1103515245u + 12345u; size_t len = DocLen(), p = (seed >> 8) % (len + 1);
            if (p < len && IS_LO(DocAt(p))) p--;
            NewGroup();
            if ((seed >> 4) % 3 == 0 && p + 2 <= len && !IS_HI(DocAt(p + 1)) && !IS_LO(DocAt(p))) EditDelete(p, 1);
            else { const WCHAR *s = ins[(seed >> 16) % 4]; EditInsert(p, s, wcslen(s)); }
        }
        size_t rn = DocLen(); WCHAR *ref = xmalloc((rn * 2 + 1) * sizeof(WCHAR)); DocGet(0, rn, ref);
        WCHAR *crlf = xmalloc((rn * 2 + 1) * sizeof(WCHAR)); size_t cn = 0;
        for (size_t i = 0; i < rn; i++) { if (ref[i] == L'\n') crlf[cn++] = L'\r'; crlf[cn++] = ref[i]; }
        int en = WideCharToMultiByte(CP_UTF8, 0, crlf, (int)cn, NULL, 0, NULL, NULL); char *exp = xmalloc((size_t)en + 1);
        WideCharToMultiByte(CP_UTF8, 0, crlf, (int)cn, exp, en, NULL, NULL);
        WCHAR tmp[MAX_PATH], p1[MAX_PATH], p2[MAX_PATH], keep[MAX_PATH * 4]; GetTempPathW(MAX_PATH, tmp); wcscpy(keep, g_path);
        _snwprintf(p1, MAX_PATH, L"%lsced_st_save1.txt", tmp); _snwprintf(p2, MAX_PATH, L"%lsced_st_save2.txt", tmp);
        size_t pc0 = g_npc; BOOL s1 = SaveFile(p1); size_t pc1 = g_npc; CompactAll(); BOOL s2 = SaveFile(p2);
        size_t l1, l2; char *b1 = ReadAll(p1, &l1), *b2 = ReadAll(p2, &l2);
        BOOL ok = s1 && s2 && b1 && b2 && l1 == (size_t)en && l2 == (size_t)en && !memcmp(b1, exp, (size_t)en) && !memcmp(b2, exp, (size_t)en);
        snprintf(buf, sizeof buf, "save: %u pieces (save keeps them: %u) and after compaction (%u): both files == reference UTF-8/CRLF (%d bytes) = %d",
                 (unsigned)pc0, (unsigned)pc1, (unsigned)g_npc, en, ok);
        STCheck(ok && pc1 == pc0 && pc0 > 100, buf);
        DeleteFileW(p1); DeleteFileW(p2); wcscpy(g_path, keep); g_enc = e0; g_modified = FALSE;
        free(b1); free(b2); free(exp); free(crlf); free(ref); free(t);
    }
    {   /* deleted original text: its pages are given back; undo still restores it */
        size_t N = 2000000; WCHAR *t = xmalloc((N + 1) * sizeof(WCHAR));
        for (size_t i = 0; i < N; i++) t[i] = i % 100 == 99 ? L'\n' : (WCHAR)(L'あ' + i % 50);
        t[N] = 0; SetTextForTest(t);
        PROCESS_MEMORY_COUNTERS m0, m1; GetProcessMemoryInfo(GetCurrentProcess(), &m0, sizeof m0);
        NewGroup(); EditDelete(200000, 1500000); CompactAll();
        GetProcessMemoryInfo(GetCurrentProcess(), &m1, sizeof m1);
        MEMORY_BASIC_INFORMATION mi; VirtualQuery(g_org + 1000000, &mi, sizeof mi);
        BOOL rel = mi.State == MEM_RESERVE, text = DocLen() == N - 1500000 && DocAt(199999) == t[199999] && DocAt(200000) == t[1700000];
        Undo(); BOOL back = DocEquals(t) && IndexConsistent();
        snprintf(buf, sizeof buf, "release: 1.5M deleted chars -> original pages decommitted=%d (private %.1f -> %.1f MB), text ok=%d, undo restores=%d",
                 rel, m0.PagefileUsage / 1048576.0, m1.PagefileUsage / 1048576.0, text, back);
        STCheck(rel && text && back, buf);
        free(t);
    }
    {   /* chunked loading: chunk borders inside multi-byte characters, all encodings */
        WCHAR tmp[MAX_PATH], fp[MAX_PATH], keep[MAX_PATH * 4]; GetTempPathW(MAX_PATH, tmp); wcscpy(keep, g_path);
        _snwprintf(fp, MAX_PATH, L"%lsced_st_load.txt", tmp);
        static const WCHAR *const unit[] = { L"日本語テキスト😀abc\r\n", L"ﾃｽﾄ日本語abc\r\n" };
        int fails = 0; char what[160] = "";
        for (int v = 0; v < 4; v++) {           /* 0 = UTF-8 (9 MB), 1 = CP932 (9 MB), 2 = UTF-8 BOM, 3 = UTF-16LE BOM */
            const WCHAR *u = unit[v == 1]; size_t ul = wcslen(u), reps = v < 2 ? 9000000 / (ul * 2) : 1000, wn = ul * reps;
            WCHAR *w = xmalloc((wn + 1) * sizeof(WCHAR)); for (size_t i = 0; i < reps; i++) memcpy(w + i * ul, u, ul * sizeof(WCHAR));
            size_t bn = 0; char *bytes = xmalloc(wn * 4 + 8);
            if (v == 2) { memcpy(bytes, "\xEF\xBB\xBF", 3); bn = 3; }
            if (v == 3) { memcpy(bytes, "\xFF\xFE", 2); memcpy(bytes + 2, w, wn * 2); bn = 2 + wn * 2; }
            else bn += (size_t)WideCharToMultiByte(v == 1 ? 932 : CP_UTF8, 0, w, (int)wn, bytes + bn, (int)(wn * 4), NULL, NULL);
            HANDLE f = CreateFileW(fp, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL); DWORD wr;
            WriteFile(f, bytes, (DWORD)bn, &wr, NULL); CloseHandle(f);
            wn = NormalizeNewlines(w, wn); w[wn] = 0;
            g_loadQuiet = TRUE; BOOL ok = LoadFile(fp); g_loadQuiet = FALSE;
            static const int encs[] = { 0, 2, 1, 3 };
            ok = ok && g_enc == encs[v] && DocEquals(w) && IndexConsistent();
            if (!ok) { fails++; snprintf(what + strlen(what), sizeof what - strlen(what), " v%d(enc=%d len=%u/%u)", v, g_enc, (unsigned)DocLen(), (unsigned)wn); }
            free(w); free(bytes);
        }
        DeleteFileW(fp); wcscpy(g_path, keep); g_enc = 0;
        snprintf(buf, sizeof buf, "load: chunked decoding of 9 MB UTF-8 / 9 MB Shift_JIS / UTF-8 BOM / UTF-16LE files == expected text, failures=%d%s", fails, what);
        STCheck(fails == 0, buf);
    }
    {   /* undo records: typing / Backspace extend the last record of their group; undo steps unchanged */
        SetTextForTest(L"abc"); g_caret = g_anchor = 3;
        for (int i = 0; i < 30; i++) OnChar(L'x');
        size_t r1 = g_undo.n;
        for (int i = 0; i < 10; i++) OnKeyDown(VK_BACK);
        size_t r2 = g_undo.n;
        BOOL a = DocLen() == 23; Undo(); BOOL b = DocLen() == 33; Undo(); BOOL c = DocEquals(L"abc");
        Redo(); Redo(); BOOL d = DocLen() == 23 && g_caret == 23;
        snprintf(buf, sizeof buf, "undo records: 30 typed chars -> %u record, +10 Backspace -> %u records; undo steps restore 33 / 3 chars=%d, redo=%d", (unsigned)r1, (unsigned)r2, a && b && c, d);
        STCheck(r1 == 1 && r2 == 2 && a && b && c && d, buf);
    }
    /* ---- 5c. width dictionary == direct measurement, and lpDx drawing == GDI's own glyph placement ---- */
    {
        static const WCHAR *const wl[] = { L"abc def_ghi XYZ ;:,.!?()[]{}<>@#$%^&*~|", L"長井文章をへんかんすると下線が長くなります。、「」『』",
            L"𠮷野家😀と絵文字 ✓★→①", L"ｱｲｳ半角ｶﾅ ﾃｽﾄ mixed 全角ＡＢＣ　x", L"The quick brown fox jumps over the lazy dog 0123456789",
            L"AVAWATAYToTaFaLTPAVAyWaWe ffi fl Ta.Yo" };
        int f0 = g_fontIdx; UINT d0 = g_dpi; int worstD = 0, worstPix = 0, combos = 0;
        char wd[128] = "-", wp[128] = "-";
        for (int f = 0; f < NFONTS; f++) for (int di = 0; di < 2; di++) {
            g_fontIdx = f; g_dpi = di ? 144 : 96; SetupFont(); combos++;
            for (int li = 0; li < 6; li++) {
                SetDocText(wl[li], wcslen(wl[li])); ResetDoc();
                WCHAR t[256]; int n = LineCopy(0, FALSE, t, 256), md = 0;
                for (int i = 0; i <= n; i++) {
                    if (i < n && IS_LO(t[i])) continue;
                    int d = abs(LineX(0, FALSE, i) - PrefixW(t, i)); if (d > md) md = d;
                }
                int pix = DrawCompare(t, n);
                if (md > worstD) { worstD = md; snprintf(wd, sizeof wd, "%s %udpi line %d", W2U(kFonts[f]), g_dpi, li); }
                if (pix > worstPix) { worstPix = pix; snprintf(wp, sizeof wp, "%s %udpi line %d", W2U(kFonts[f]), g_dpi, li); }
            }
        }
        snprintf(buf, sizeof buf, "width dictionary vs GetTextExtentPoint32 of the run: %d fonts x 96/144 dpi x 6 lines, worst diff=%dpx (%s)", NFONTS, worstD, wd);
        STCheck(worstD == 0, buf);
        snprintf(buf, sizeof buf, "drawing with measured lpDx vs ExtTextOut's own layout: differing pixels worst=%d (%s)", worstPix, wp);
        STCheck(worstPix == 0, buf);
        g_fontIdx = f0; g_dpi = d0; SetupFont();
        WCHAR *t = xmalloc(20001 * sizeof(WCHAR));
        for (int i = 0; i < 20000; i++) t[i] = L"あいうえおabcdeカキクケコ漢字 \t。"[i % 20];
        t[20000] = 0;
        SetDocText(t, 20000); ResetDoc(); free(t);
        unsigned c0 = g_gdiCalls; int wfull = LineX(0, FALSE, 20000); unsigned c1 = g_gdiCalls;
        LayoutReset(); LineX(0, FALSE, 20000); unsigned c2 = g_gdiCalls;
        snprintf(buf, sizeof buf, "width dictionary: 20000-char line (19 distinct chars) measured with %u GDI calls (fresh dictionary: %u), width=%d",
                 c1 - c0, c2 - c1, wfull);
        STCheck(c2 - c1 <= 19, buf);
    }
    /* ---- 5d. IME geometry with the font size of 144 DPI (caret drift / long underline history) ---- */
    { UINT d0 = g_dpi; g_dpi = 144; SetupFont(); STComp("[144dpi font] "); g_dpi = d0; SetupFont(); }
    /* ---- 5e. caret / hit test on a long line with horizontal scrolling ---- */
    {
        WCHAR *t = xmalloc(3001 * sizeof(WCHAR));
        for (int i = 0; i < 3000; i++) { int k = i % 13; t[i] = k == 3 ? L'\t' : k == 7 ? L'あ' : k == 9 ? L'ｶ' : k == 11 ? L'　' : (WCHAR)(L'a' + i % 26); }
        t[3000] = 0;
        SetTextForTest(t); free(t);
        int bad = 0, badc = 0, maxsx = 0;
        for (size_t p = 0; p <= 3000; p += 37) {
            g_caret = g_anchor = p; g_aff = FALSE; Refresh(TRUE); UpdateWindow(g_hwnd);
            POINT pt, gp; CaretPoint(&pt, NULL); GetCaretPos(&gp);
            if (gp.x != pt.x || gp.y != pt.y || pt.x < 0 || pt.x > g_cw) badc++;
            if (PosFromPoint(pt.x, pt.y + g_lineH / 2) != p) bad++;
            if (g_sx > maxsx) maxsx = g_sx;
        }
        snprintf(buf, sizeof buf, "no wrap: caret -> hit test round trip on a 3000-char line, horizontal scroll up to %dpx: mismatches=%d, caret placement errors=%d", maxsx, bad, badc);
        STCheck(bad == 0 && badc == 0 && maxsx > 1000, buf);
    }
    /* ---- 5f. per-line cache: partial measurement + invalidation on edits == fresh layout ---- */
    {
        static const WCHAR *const ins[] = { L"x", L"あ", L" ", L"\n", L"。", L"」", L"\t", L"word ", L"長い日本語の文章", L"😀" };
        g_wrap = TRUE; g_layoutVer++;
        WCHAR *t = xmalloc(40000 * sizeof(WCHAR)); size_t n = 0;
        for (int L = 0; L < 60; L++) {
            int len = (L * 37) % 700;
            for (int i = 0; i < len; i++) t[n++] = L"日本語の文章、そして English words; 「括弧」。\t"[(i + L) % 29];
            t[n++] = L'\n';
        }
        t[n - 1] = 0;
        SetTextForTest(t); free(t);
        unsigned seed = 31337; int bad = 0, checks = 0;
        for (int it = 0; it < 400; it++) {
            seed = seed * 1103515245u + 12345u;
            size_t len = DocLen(), p = len ? (seed >> 8) % (len + 1) : 0;
            if ((seed >> 4) % 3 == 0 && len) { size_t k = 1 + (seed >> 12) % 6; if (p + k > len) k = len - p; RawDelete(p, k); }
            else { const WCHAR *s = ins[(seed >> 16) % 10]; RawInsert(p, s, wcslen(s)); }
            for (int k = 0; k < 3; k++) {
                seed = seed * 1103515245u + 12345u;
                Ln ln = LnOf((seed >> 8) % g_nl, FALSE);
                EnsureRows(&ln, 1 + (int)((seed >> 4) % 6)); XOf(&ln, (int)((seed >> 12) % (unsigned)(ln.n + 1)));
            }
            if (it % 25 != 24) continue;
            for (size_t L = 0; L < g_nl; L++) {
                Ln ln = LnOf(L, FALSE);
                int nr = EnsureRows(&ln, INT_MAX), w = XOf(&ln, ln.n), mid = XOf(&ln, ln.n / 3);
                int *rows = xmalloc(((size_t)nr + 1) * sizeof(int)); memcpy(rows, ln.li->rows, (size_t)nr * sizeof(int));
                InfoFree(L);
                Ln f = LnOf(L, FALSE);
                int fr = EnsureRows(&f, INT_MAX);
                if (fr != nr || memcmp(rows, f.li->rows, (size_t)nr * sizeof(int)) || XOf(&f, f.n) != w || XOf(&f, f.n / 3) != mid) bad++;
                checks++; free(rows);
            }
        }
        long long sum = 0; RowCountsCheck();
        for (size_t L = 0; L < g_nl; L++) sum += RowsOf(L);
        snprintf(buf, sizeof buf, "line cache: 400 random edits with partial measurement, cached rows/widths vs fresh layout: %d mismatches in %d lines, row sum %lld == %lld",
                 bad, checks, g_rowsSum, sum);
        STCheck(bad == 0 && sum == g_rowsSum, buf);
        g_wrap = FALSE; g_layoutVer++;
    }
    /* ---- 5g. scrolling shifts the back buffer and draws only new rows; result == full repaint ---- */
    {
        WCHAR *t = xmalloc(200000 * sizeof(WCHAR)); size_t n = 0;
        for (int L = 0; L < 300; L++) {
            n += (size_t)swprintf(t + n, 64, L"%03d 行目: ", L);
            for (int i = 0; i < (L * 53) % 260; i++) t[n++] = L"折り返しの確認 wrap test。\t"[i % 18];
            t[n++] = L'\n';
        }
        t[n - 1] = 0;
        int dn[2] = { 0, 0 }, ds[2] = { 0, 0 }; unsigned sp0 = g_scrollPaths;
        for (int wm = 0; wm < 2; wm++) {
            g_wrap = wm; g_layoutVer++;
            SetTextForTest(t);
            g_anchor = LineStart(3) + 2; g_caret = LineStart(12) + 5; g_showWs = TRUE;   /* selection + marks in view */
            Refresh(FALSE); UpdateWindow(g_hwnd);
            static const int steps[] = { 3, 5, -2, 1, 7, -4, 2, 2, -1, 9 };
            for (int k = 0; k < 10; k++) { ScrollRows(steps[k]); UpdateWindow(g_hwnd); }
            HideCaret(g_hwnd); DWORD *a = Grab(FALSE), *sc = Grab(TRUE); ShowCaret(g_hwnd);
            Invalidate(); UpdateWindow(g_hwnd);
            DWORD *b = Grab(FALSE);
            dn[wm] = PixDiff(a, b); ds[wm] = PixDiff(sc, b);
            free(a); free(b); free(sc);
            g_showWs = FALSE;
        }
        free(t);
        snprintf(buf, sizeof buf, "back buffer: %u scroll steps drew only the exposed rows; vs full repaint: differing pixels no-wrap=%d wrap=%d, screen=%d/%d",
                 g_scrollPaths - sp0, dn[0], dn[1], ds[0], ds[1]);
        STCheck(g_scrollPaths - sp0 >= 18 && !dn[0] && !dn[1] && !ds[0] && !ds[1], buf);
        g_wrap = FALSE; g_layoutVer++;
    }
    /* ---- 5h. very long line: measured only as far as needed, completed in idle time ---- */
    {
        size_t N = 1000000; WCHAR *t = xmalloc((N + 1) * sizeof(WCHAR));
        for (size_t i = 0; i < N; i++) t[i] = i % 11 == 10 ? L' ' : (i % 5 ? (WCHAR)(L'a' + i % 26) : L'漢');
        t[N] = 0;
        double t0 = NowMs(); SetTextForTest(t); double t1 = NowMs();
        free(t);
        Ln ln = LnOf(0, FALSE); int mi0 = ln.li->mi;
        double t2 = NowMs(); OnKeyDown(VK_END); UpdateWindow(g_hwnd); double t3 = NowMs();
        POINT pt; CaretPoint(&pt, NULL);
        double t4 = NowMs(); for (int i = 0; i < 20; i++) { OnChar(L'x'); UpdateWindow(g_hwnd); } double t5 = NowMs();
        ln = LnOf(0, FALSE);
        snprintf(buf, sizeof buf, "long line: 1M chars, open+paint %.1f ms measured %d units only; End %.1f ms (caret x=%ld); typing at the end %.2f ms/char",
                 t1 - t0, mi0, t3 - t2, pt.x, (t5 - t4) / 20);
        STCheck(mi0 < 20000 && pt.x > 0 && pt.x < g_cw && EnsureRows(&ln, INT_MAX) == 1 && (t5 - t4) / 20 < 50, buf);
        g_caret = g_anchor = 0; Refresh(TRUE); UpdateWindow(g_hwnd);
        int guard = 0; double t6 = NowMs(); while (IdleWork() && guard < 200000) guard++; double t7 = NowMs();
        ln = LnOf(0, FALSE);
        SCROLLINFO si = { sizeof si, SIF_RANGE, 0, 0, 0, 0, 0 }; GetScrollInfo(g_hwnd, SB_HORZ, &si);
        snprintf(buf, sizeof buf, "long line: idle prefetch completed the width in %.0f ms (%d slices): %d px exact=%d, horizontal range %d == content %d",
                 t7 - t6, guard, LineWidth(&ln), Measured(&ln), si.nMax + 1, ContentW());
        STCheck(Measured(&ln) && g_maxW == LineWidth(&ln) && si.nMax + 1 == ContentW(), buf);
    }
    /* ---- 5i. wrap: idle row counting makes the vertical scrollbar exact for big documents ---- */
    {
        g_wrap = TRUE; g_layoutVer++;
        size_t n = 0; WCHAR *t = xmalloc(800000 * sizeof(WCHAR));
        for (int L = 0; L < 3000; L++) {
            int len = L % 3 == 0 ? 150 + L % 97 : 10 + L % 20;
            for (int i = 0; i < len; i++) t[n++] = L"あいうえお かきくけこ abc。"[i % 16];
            t[n++] = L'\n';
        }
        t[n - 1] = 0;
        SetTextForTest(t); free(t);
        SCROLLINFO s0 = { sizeof s0, SIF_ALL, 0, 0, 0, 0, 0 }; GetScrollInfo(g_hwnd, SB_VERT, &s0);
        int guard = 0; while (IdleWork() && guard < 200000) guard++;
        long long sum = 0, above = 0;
        for (size_t L = 0; L < g_nl; L++) { int r = RowsOf(L); sum += r; if (L < 1500) above += r; }
        g_top = 1500; g_topRow = 0; Refresh(FALSE); UpdateWindow(g_hwnd);
        SCROLLINFO s1 = { sizeof s1, SIF_ALL, 0, 0, 0, 0, 0 }; GetScrollInfo(g_hwnd, SB_VERT, &s1);
        snprintf(buf, sizeof buf, "wrap scrollbar, 3000 lines (> %d): range before idle %d, after idle %d == exact rows %lld; position at line 1500 %d == %lld",
                 WRAP_EXACT_LINES, s0.nMax + 1, s1.nMax + 1, sum, s1.nPos, above);
        STCheck(s1.nMax + 1 == sum && s1.nPos == above, buf);
        g_wrap = FALSE; g_layoutVer++;
    }
    /* ---- 6. Ctrl+I name increment ---- */
    {
        static const WCHAR *const in[] = { L"C:\\d\\memo3.txt", L"C:\\d\\memo.txt", L"C:\\d\\memo009.txt", L"C:\\d\\memo99.md", L"C:\\d\\memo", L"C:\\d.x\\a.b.txt", L"C:\\d\\v1.2" };
        static const WCHAR *const ex[] = { L"C:\\d\\memo4.txt", L"C:\\d\\memo1.txt", L"C:\\d\\memo010.txt", L"C:\\d\\memo100.md", L"C:\\d\\memo1", L"C:\\d.x\\a.b1.txt", L"C:\\d\\v2.2" };
        for (int i = 0; i < 7; i++) {
            WCHAR o[MAX_PATH]; IncrementName(in[i], o, MAX_PATH);
            snprintf(buf, sizeof buf, "IncrementName %s -> %s (expect %s)", W2U(in[i]), W2U(o), W2U(ex[i]));
            STCheck(wcscmp(o, ex[i]) == 0, buf);
        }
    }
    /* ---- 7. regex engine in the exe ---- */
    {
        struct { const WCHAR *p, *t; int flags, a, b; } rt[] = {
            { L"a.c", L"xxabcxx", 0, 2, 5 }, { L"\\d+", L"abc 1234 x", 0, 4, 8 }, { L"(foo|bar)+?x", L"barfoox", 0, 0, 7 },
            { L"^\\s*$", L"   ", 0, 0, 3 }, { L"[^あ-ん]+", L"ひらがなカタカナ", 0, 4, 8 }, { L"ＡＢＣ", L"xａｂｃ", RE_ICASE, 1, 4 },
            { L"colou?r", L"COLOR", RE_ICASE, 0, 5 }, { L"a{2,3}", L"aaaa", 0, 0, 3 }, { L"(a*)*b", L"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac", 0, -1, -1 },
            { L"\\bword\\b", L"a word.", 0, 2, 6 }, { L"x.y", L"x😀y", 0, 0, 4 } };
        int nrt = (int)(sizeof rt / sizeof rt[0]);
        for (int i = 0; i < nrt; i++) {
            int ep; Regex *re = re_compile((const rechar *)rt[i].p, (int)wcslen(rt[i].p), rt[i].flags, &ep);
            int caps[2 * RE_NCAP]; int f = re ? re_search(re, (const rechar *)rt[i].t, (int)wcslen(rt[i].t), 0, caps) : 0;
            int a = f ? caps[0] : -1, b = f ? caps[1] : -1;
            snprintf(buf, sizeof buf, "regex /%s/ on \"%s\" -> [%d,%d) expect [%d,%d)", W2U(rt[i].p), W2U(rt[i].t), a, b, rt[i].a, rt[i].b);
            STCheck(re && a == rt[i].a && b == rt[i].b, buf);
            re_free(re);
        }
    }
    /* ---- 8. replace / replace all (single undo step) ---- */
    {
        static const WCHAR orig[] = L"foo1 bar foo22\nnothing\nfoo3 end";
        SetTextForTest(orig);
        g_findOpen = TRUE;
        SetWindowTextW(g_edFind, L"foo(\\d+)"); SetWindowTextW(g_edRepl, L"[$1]"); FindCompile();
        DoReplaceAll();
        BOOL ok1 = DocEquals(L"[1] bar [22]\nnothing\n[3] end");
        snprintf(buf, sizeof buf, "replace all foo(\\d+) -> [$1]: %s", ok1 ? "ok" : "wrong result");
        STCheck(ok1, buf);
        Undo();
        snprintf(buf, sizeof buf, "replace all is one undo step: %s", DocEquals(orig) ? "restored" : "not restored");
        STCheck(DocEquals(orig), buf);
        SetTextForTest(L"aXbXc");
        SetWindowTextW(g_edFind, L"x"); SetWindowTextW(g_edRepl, L""); g_matchCase = FALSE; FindCompile();
        g_caret = g_anchor = 0; FindNext(TRUE); DoReplace();
        snprintf(buf, sizeof buf, "replace with empty string deletes the match and selects the next (sel=[%u,%u))", (unsigned)SelA(), (unsigned)SelB());
        STCheck(DocEquals(L"abXc") && SelA() == 2 && SelB() == 3, buf);
        g_matchCase = TRUE; FindCompile();
        snprintf(buf, sizeof buf, "match case: 'x' not found in 'abXc' -> %d", FindNext(TRUE));
        STCheck(!FindNext(TRUE), buf);
        g_matchCase = FALSE;
        SetWindowTextW(g_edFind, L"([a-z]+)@(\\w+)"); SetWindowTextW(g_edRepl, L"\\2 at $1");
        SetTextForTest(L"mail: user@example");
        FindCompile(); DoReplaceAll();
        STCheck(DocEquals(L"mail: example at user"), "replacement \\2 and $1 group references");
        SetWindowTextW(g_edFind, L""); SetWindowTextW(g_edRepl, L""); FindCompile();
        FindHide();
    }
    /* ---- 9. Markdown ---- */
    {
        WCHAR v[256]; WORD st[256];
        MdVisible(L"**太字** *斜体* ***両方*** ~~取消~~ \\*esc\\* `co*de*` [リンク](http://x.jp \"title\") <https://u.jp>", v, st, 256);
        snprintf(buf, sizeof buf, "md inline visible text: \"%s\"", W2U(v));
        STCheck(wcscmp(v, L"太字 斜体 両方 取消 *esc* co*de* リンク(http://x.jp) https://u.jp") == 0, buf);
        STCheck((st[0] & S_B) && !(st[0] & S_I) && (st[3] & S_I) && !(st[3] & S_B) && (st[6] & S_B) && (st[6] & S_I) && (st[9] & S_S),
                "md inline styles: bold / italic / bold+italic / strike");
        MdVisible(L"__a__ _b_ snake_case_word", v, st, 256);
        snprintf(buf, sizeof buf, "md underscore emphasis, intraword '_' kept: \"%s\"", W2U(v));
        STCheck(wcscmp(v, L"a b snake_case_word") == 0 && (st[0] & S_B) && (st[2] & S_I), buf);
        SetTextForTest(L"# 見出し\n本文<!-- 隠す\n複数行 -->表示\n\n| a | b |\n|:--|--:|\n| 1 | 2 |\n\n- 項目\n  - 入れ子\n1. 番号\n---\n> 引用");
        g_mdView = TRUE; MdInvalidate(); MdLayout();
        BOOL hidden = TRUE, haveHead = FALSE, haveCell = FALSE, haveNest = FALSE;
        int bullets = 0, num = 0;
        for (int i = 0; i < g_nmi; i++) {
            if (g_mi[i].type == MI_BULLET) bullets++;
            if (g_mi[i].type != MI_TEXT) continue;
            const WCHAR *s = g_mpool + g_mi[i].ts; int n = g_mi[i].tl;
            for (int k = 0; k < n; k++) if (s[k] == L'隠' || s[k] == L'複' || s[k] == L'|') hidden = FALSE;
            if (n >= 3 && wcsncmp(s, L"見出し", 3) == 0 && g_mi[i].font / 32 == 1) haveHead = TRUE;
            if (n == 1 && s[0] == L'2') haveCell = TRUE;
            if (n >= 3 && wcsncmp(s, L"入れ子", 3) == 0 && g_mi[i].x > Sc(30)) haveNest = TRUE;
            if (n == 2 && wcsncmp(s, L"1.", 2) == 0) num++;
        }
        snprintf(buf, sizeof buf, "md layout: comment hidden=%d heading=%d table cell=%d nested list=%d bullets=%d ordered=%d items=%d height=%d",
                 hidden, haveHead, haveCell, haveNest, bullets, num, g_nmi, g_mdH);
        STCheck(hidden && haveHead && haveCell && haveNest && bullets == 2 && num == 1, buf);
        SetTextForTest(L"```\nint main(void) { return 0; }\n```\nThe quick brown fox jumps over the lazy dog. とても長い一行の文章は、右端で折り返す設定にすると、ウィンドウの幅に合わせて複数の表示行に分かれます。とても長い一行の文章は、右端で折り返す設定にすると、ウィンドウの幅に合わせて複数の表示行に分かれます。");
        MdInvalidate(); MdLayout();
        int maxR = 0, rowsY[64], nrow = 0;
        for (int i = 0; i < g_nmi; i++) if (g_mi[i].type == MI_TEXT) {
            if (g_mi[i].x + g_mi[i].w > maxR) maxR = g_mi[i].x + g_mi[i].w;
            BOOL seen = FALSE; for (int r = 0; r < nrow; r++) if (rowsY[r] == g_mi[i].y) seen = TRUE;
            if (!seen && nrow < 64) rowsY[nrow++] = g_mi[i].y;
        }
        snprintf(buf, sizeof buf, "md paragraph wraps: rightmost text edge %d <= %d, text rows=%d", maxR, g_cw - Sc(16), nrow);
        STCheck(maxR <= g_cw - Sc(16) && nrow >= 3, buf);
        g_mdView = FALSE;
    }
    /* ---- 10. title / ini ---- */
    {
        WCHAR old[MAX_PATH * 4]; wcscpy(old, g_path);
        wcscpy(g_path, L"C:\\work\\memo3.txt"); UpdateTitle();
        WCHAR t[256]; GetWindowTextW(g_frame, t, 256);
        snprintf(buf, sizeof buf, "window (taskbar) title = file name: \"%s\"", W2U(t));
        STCheck(wcscmp(t, L"memo3.txt") == 0, buf);
        wcscpy(g_path, old); UpdateTitle();
        WCHAR tmp[MAX_PATH], ip[MAX_PATH]; GetTempPathW(MAX_PATH, tmp); _snwprintf(ip, MAX_PATH, L"%lsced_selftest.ini", tmp); ip[MAX_PATH - 1] = 0;
        int f0 = g_fontIdx, z0 = g_fontPt10; BOOL w0 = g_wrap, s0 = g_showWs;
        g_fontIdx = 2; g_fontPt10 = 150; g_wrap = TRUE; g_showWs = TRUE;
        BOOL wr = IniWriteTo(ip);
        g_fontIdx = 0; g_fontPt10 = 110; g_wrap = FALSE; g_showWs = FALSE;
        IniReadFrom(ip);
        snprintf(buf, sizeof buf, "ini round trip (%s): write=%d font=%d zoom=%d wrap=%d ws=%d", W2U(ip), wr, g_fontIdx, g_fontPt10, g_wrap, g_showWs);
        STCheck(wr && g_fontIdx == 2 && g_fontPt10 == 150 && g_wrap && g_showWs, buf);
        DeleteFileW(ip);
        g_fontIdx = f0; g_fontPt10 = z0; g_wrap = w0; g_showWs = s0; g_iniHaveRect = FALSE;
        BOOL bad = IniWriteTo(L"Z:\\no\\such\\dir\\x.ini");
        snprintf(buf, sizeof buf, "ini: unwritable path reports failure (-> %%APPDATA%% fallback): %d", !bad);
        STCheck(!bad, buf);
        SetupFont(); g_layoutVer++;
    }
    /* ---- 11. keyboard shortcut mapping is layout independent ---- */
    {
        UINT vk = VkKeyScanW(L';') & 0xFF;
        snprintf(buf, sizeof buf, "zoom-in key: VkKeyScan(';')=0x%02X maps back to ';' = %d", vk, vk != 0xFF && CtrlChar(vk, L';'));
        STCheck(vk != 0xFF && CtrlChar(vk, L';'), buf);
        SetTextForTest(L"abc");
        g_caret = g_anchor = 3;
        BYTE ks[256]; GetKeyboardState(ks); BYTE oc = ks[VK_CONTROL]; ks[VK_CONTROL] = 0x80; SetKeyboardState(ks);
        OnChar(0x09); OnChar(0x0D); OnChar(0x0A);       /* what Ctrl+I / Ctrl+M / Ctrl+J produce */
        ks[VK_CONTROL] = oc; SetKeyboardState(ks);
        STCheck(DocEquals(L"abc"), "Ctrl+I/M/J control characters are not inserted");
        int z = g_fontPt10; DoCommand(IDM_ZOOMIN); int z1 = g_fontPt10; DoCommand(IDM_ZOOMRESET);
        snprintf(buf, sizeof buf, "zoom in %d -> %d, reset -> %d", z, z1, g_fontPt10);
        STCheck(z1 == z + 10 && g_fontPt10 == 110, buf);
    }
    snprintf(buf, sizeof buf, "RESULT: %s (%d checks, %d failures)\n", g_stfail ? "FAIL" : "PASS", g_stcount, g_stfail);
    STLog("%s", buf);
    if (g_stf) fclose(g_stf);
    else {
        WCHAR wb[512]; MultiByteToWideChar(CP_UTF8, 0, buf, -1, wb, 512);
        MessageBoxW(g_frame, wb, APPNAME L" セルフテスト", g_stfail ? MB_ICONWARNING : MB_ICONINFORMATION);
    }
    g_stf = NULL;
    /* leave a demo composition on screen */
    SetTextForTest(L"テスト\n長井文章をへんかんすると下線が長くなります\nタブ\tの後\n𠮷野家😀");
    g_caret = g_anchor = LineEnd(1);
    SetComp(L"長井文章を変換");
    Refresh(TRUE);
}

/* ================================================================== */
/* demo (screenshots) and benchmark modes                              */
/* ================================================================== */
static const WCHAR kDemoText[] =
    L"# CEditor 1.3 デモ\n"
    L"\n"
    L"カスタム描画のテキストエディタです。**太字**、*斜体*、***太字斜体***、~~取り消し線~~、`コード`。\n"
    L"全角スペース「　」と半角スペース「 」とタブ「\t」を含む行。\n"
    L"> 引用ブロックの例です。\\*エスケープ\\* も使えます。\n"
    L"> > 入れ子の引用\n"
    L"\n"
    L"- 箇条書き 1\n"
    L"- 箇条書き 2\n"
    L"  - 入れ子の項目。長い行は折り返したときにぶら下げインデントになります。長い行は折り返したときにぶら下げインデントになります。\n"
    L"1. 番号付き\n"
    L"2. 二番目\n"
    L"\n"
    L"| 機能 | 状態 | 備考 |\n"
    L"|:-----|:----:|-----:|\n"
    L"| 検索 | ✓ | 正規表現 |\n"
    L"| 置換 | ✓ | $1 参照 |\n"
    L"\n"
    L"リンク: [CEditor](https://example.com/ \"タイトル\") と <https://example.jp>\n"
    L"<!-- このコメントは表示されません -->\n"
    L"***\n"
    L"```\n"
    L"int main(void) { return 0; }\n"
    L"```\n"
    L"The quick brown fox jumps over the lazy dog. とても長い一行の文章は、右端で折り返す設定にすると、ウィンドウの幅に合わせて複数の表示行に分かれます。";
static void RunDemo(void) {
    SetDocText(kDemoText, wcslen(kDemoText)); ResetDoc();
    wcscpy(g_path, L"C:\\Users\\demo\\メモ3.md");
    g_modified = TRUE;
    g_caret = LineStart(2) + 9; g_anchor = LineStart(2) + 4;     /* a visible selection */
    if (!wcscmp(g_demo, L"find")) {
        g_caret = g_anchor = 0;
        FindShow(FALSE); SetWindowTextW(g_edFind, L"折り返"); FindCompile(); FindNext(TRUE);
    } else if (!wcscmp(g_demo, L"replace")) {
        g_caret = g_anchor = 0;
        FindShow(TRUE); SetWindowTextW(g_edFind, L"箇条書き (\\d)"); SetWindowTextW(g_edRepl, L"項目$1"); FindCompile(); FindNext(TRUE);
    } else if (!wcscmp(g_demo, L"ws")) {
        g_showWs = TRUE; g_caret = g_anchor = LineEnd(3);
    } else if (!wcscmp(g_demo, L"md")) {
        SetMdView(TRUE);
    } else if (!wcscmp(g_demo, L"wrap")) {
        g_wrap = TRUE; g_layoutVer++; g_caret = g_anchor = DocLen();
    } else if (!wcscmp(g_demo, L"comp")) {
        g_caret = g_anchor = LineEnd(3);
        SetComp(L"長井文章を変換");
    }
    UpdateTitle(); InvalidateCaption();
    Refresh(TRUE);
    if (g_findOpen) SetFocus(g_edFind);
}
static void BenchPaint(void) { Invalidate(); UpdateWindow(g_hwnd); }
static void RunBench(void) {
    FILE *f = _wfopen(g_stlog, L"w");
    if (!f) { MessageBoxW(g_frame, L"ベンチマークのログファイルを開けません。", APPNAME, MB_ICONERROR); }
#define BLOG(...) do { if (f) { fprintf(f, __VA_ARGS__); fflush(f); } } while (0)
#define BT(label, n, code) do { double t0_ = NowMs(); for (int i_ = 0; i_ < (n); i_++) { code; } double t1_ = NowMs(); \
        BLOG("%-44s %9.2f ms total %8.3f ms each\n", label, t1_ - t0_, (t1_ - t0_) / (n)); } while (0)
    PROCESS_MEMORY_COUNTERS pm0; memset(&pm0, 0, sizeof pm0); GetProcessMemoryInfo(GetCurrentProcess(), &pm0, sizeof pm0);
    BLOG("%s bench\n", W2U(APPNAME L" " APPVER));
    double t0 = NowMs();
    g_loadQuiet = TRUE;
    BOOL ok = LoadFile(g_benchFile);
    double t1 = NowMs();
    PROCESS_MEMORY_COUNTERS pm1; memset(&pm1, 0, sizeof pm1); GetProcessMemoryInfo(GetCurrentProcess(), &pm1, sizeof pm1);
    BLOG("file: %s\nload: %s, %.0f ms, %u chars, %u lines\n", W2U(g_benchFile), ok ? "ok" : "FAILED", t1 - t0, (unsigned)DocLen(), (unsigned)g_nl);
    BLOG("memory after load: working set %.1f MB, peak %.1f MB (before load %.1f MB)\n", pm1.WorkingSetSize / 1048576.0, pm1.PeakWorkingSetSize / 1048576.0, pm0.WorkingSetSize / 1048576.0);
    BT("first paint", 1, BenchPaint());
    BT("no-wrap: PageDown (caret+scroll+paint)", 100, (OnKeyDown(VK_NEXT), UpdateWindow(g_hwnd)));
    BT("no-wrap: wheel scroll 3 rows", 300, (ScrollRows(3), UpdateWindow(g_hwnd)));
    BT("no-wrap: wheel scroll 1 row up", 100, (ScrollRows(-1), UpdateWindow(g_hwnd)));
    BT("no-wrap: scroll right (SB_LINERIGHT)", 100, (OnScroll(SB_HORZ, SB_LINERIGHT), UpdateWindow(g_hwnd)));
    BT("no-wrap: scroll back to the left edge", 1, (OnScroll(SB_HORZ, SB_LEFT), UpdateWindow(g_hwnd)));
    size_t mid = DocLen() / 2; if (mid && IS_LO(DocAt(mid))) mid--;
    BT("jump to the middle character", 1, (g_caret = g_anchor = mid, Refresh(TRUE), UpdateWindow(g_hwnd)));
    BT("typing in the middle (200 chars)", 200, (OnChar(L'x'), UpdateWindow(g_hwnd)));
    BT("typing in the middle (20 newlines)", 20, (OnChar(L'\r'), UpdateWindow(g_hwnd)));
    BT("End (end of the line) + paint", 1, (OnKeyDown(VK_END), UpdateWindow(g_hwnd)));
    BT("typing at the line end (50 chars)", 50, (OnChar(L'y'), UpdateWindow(g_hwnd)));
    BT("Home + paint", 1, (OnKeyDown(VK_HOME), UpdateWindow(g_hwnd)));
    BT("Ctrl+End", 1, (g_caret = g_anchor = DocLen(), Refresh(TRUE), UpdateWindow(g_hwnd)));
    BT("20 undo (+ one paint)", 1, { for (int k = 0; k < 20; k++) Undo(); Refresh(TRUE); UpdateWindow(g_hwnd); });
    g_wrap = TRUE; g_layoutVer++; g_caret = g_anchor = 0; g_top = 0; g_topRow = 0;
    BT("wrap on (top of file)", 1, (Refresh(TRUE), UpdateWindow(g_hwnd)));
    BT("wrap: PageDown", 100, (OnKeyDown(VK_NEXT), UpdateWindow(g_hwnd)));
    BT("wrap: wheel scroll 3 rows", 300, (ScrollRows(3), UpdateWindow(g_hwnd)));
    BT("wrap: wheel scroll 1 row up", 100, (ScrollRows(-1), UpdateWindow(g_hwnd)));
    BT("wrap: jump to the middle + typing 20 chars", 1, { g_caret = g_anchor = mid; Refresh(TRUE); UpdateWindow(g_hwnd); for (int k = 0; k < 20; k++) { OnChar(L'z'); UpdateWindow(g_hwnd); } });
    BT("wrap: Ctrl+End", 1, (g_caret = g_anchor = DocLen(), Refresh(TRUE), UpdateWindow(g_hwnd)));
    g_wrap = FALSE; g_layoutVer++; g_caret = g_anchor = 0; Refresh(TRUE); UpdateWindow(g_hwnd);
    {
        int ep; Regex *re = re_compile((const rechar *)L"ZQX_NOT_PRESENT\\d", 17, RE_ICASE, &ep);
        Regex *sv = g_re; g_re = re; size_t a, b; BOOL found = FALSE;
        BT("full-document regex search (no match)", 1, found = FindFrom(0, TRUE, &a, &b));
        g_re = sv; re_free(re);
        if (found) BLOG("  (unexpected match)\n");
    }
    WCHAR tmp[MAX_PATH], sp[MAX_PATH]; GetTempPathW(MAX_PATH, tmp); _snwprintf(sp, MAX_PATH, L"%lsced_bench_save.txt", tmp); sp[MAX_PATH - 1] = 0;
    WCHAR keep[MAX_PATH * 4]; wcscpy(keep, g_path);
    BOOL sok = FALSE;
    BT("save (UTF-8)", 1, sok = SaveFile(sp));
    if (!sok) BLOG("  save FAILED\n");
    DeleteFileW(sp); wcscpy(g_path, keep);
    PROCESS_MEMORY_COUNTERS pm2; memset(&pm2, 0, sizeof pm2); GetProcessMemoryInfo(GetCurrentProcess(), &pm2, sizeof pm2);
    BLOG("memory at the end: working set %.1f MB, peak working set %.1f MB, private %.1f MB\n", pm2.WorkingSetSize / 1048576.0, pm2.PeakWorkingSetSize / 1048576.0, pm2.PagefileUsage / 1048576.0);
    BLOG("done\n");
#undef BT
#undef BLOG
    if (f) fclose(f);
    g_modified = FALSE;
    PostMessageW(g_frame, WM_CLOSE, 0, 0);
}

/* ================================================================== */
/* idle time (message loop has nothing to do): measure / wrap the lines */
/* around the viewport, count wrapped rows of the whole document       */
/* ================================================================== */
#define INFO_MAX 20000                      /* cached line infos kept (far ones are dropped) */
static double NowMs(void) {
    static LARGE_INTEGER f; LARGE_INTEGER c;
    if (!f.QuadPart) QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return (double)c.QuadPart * 1000.0 / (double)f.QuadPart;
}
static LineInfo g_bgi; static size_t g_bgiL = (size_t)-1; static unsigned g_bgiDV;
static BOOL IdleBusy(double t0) { return NowMs() - t0 > 4.0 || HIWORD(GetQueueStatus(QS_ALLINPUT)); }
/* does a few ms of work; returns TRUE if there is more */
static BOOL IdleWork(void) {
    static double lastSB;
    if (!g_hwnd || g_mdView || IsIconic(g_frame)) return FALSE;
    double t0 = NowMs();
    int vis = VisLines(), W = g_wrap ? WrapW() : 0;
    size_t lo = g_top > (size_t)vis * 3 ? g_top - (size_t)vis * 3 : 0, hi = g_top + (size_t)vis * 4;
    BOOL busy = FALSE, visible = FALSE;
    long long sum0 = g_rowsSum;
    RowCountsCheck();
    /* 1) the viewport, then three screens below and three above */
    for (int pass = 0; pass < 3 && !busy; pass++) {
        size_t a = pass == 0 ? g_top : pass == 1 ? g_top + (size_t)vis + 1 : lo;
        size_t b = pass == 0 ? g_top + (size_t)vis + 1 : pass == 1 ? hi : g_top;
        for (size_t L = a; L < b && L < g_nl && !busy; L++) {
            Ln ln = LnOf(L, TRUE);
            while (!busy && !(g_wrap ? ln.li->rw == W && ln.li->rdone : Measured(&ln))) {
                if (g_wrap) EnsureRows(&ln, (ln.li->rw == W ? ln.li->nr : 0) + 64);
                else Measure(&ln, ln.li->mi + 65536);
                visible |= pass == 0; busy = IdleBusy(t0);
            }
        }
    }
    /* 2) wrap: row count of every line, so the vertical scrollbar becomes exact */
    while (g_wrap && !busy && g_bgL < g_nl) {
        if (g_lm[g_bgL].rows) { g_bgL++; continue; }
        if (g_bgiL != g_bgL || g_bgiDV != g_docVer) { InfoReset(&g_bgi); g_bgiL = g_bgL; g_bgiDV = g_docVer; }
        Ln ln = { g_bgL, -1, (int)(LineEnd(g_bgL) - LineStart(g_bgL)), g_lm[g_bgL].li ? LI(g_bgL) : &g_bgi };
        EnsureRows(&ln, (ln.li->rw == W ? ln.li->nr : 0) + 256);
        if (ln.li->rdone && !g_lm[g_bgL].rows) SetRowCount(g_bgL, ln.li->nr);
        busy = IdleBusy(t0);
    }
    /* 3) compaction of the piece table, then give back memory no longer used */
    while (!busy && !CompactStep(256)) busy = IdleBusy(t0);
    if (!busy && g_gcDue) { ReleaseUnused(); busy = IdleBusy(t0); }
    /* 4) bound the memory of the line cache */
    if (g_ninfo > INFO_MAX) {
        size_t a = g_top > INFO_MAX / 4 ? g_top - INFO_MAX / 4 : 0, b = g_top + INFO_MAX / 4;
        for (size_t L = 0; L < g_nl; L++) if (g_lm[L].li && (L < a || L > b) && L != g_ln.L) InfoFree(L);
    }
    int om = g_maxW;
    if (visible) UpdateMaxW();
    if (om != g_maxW || (g_rowsSum != sum0 && (NowMs() - lastSB > 150 || !busy))) { UpdateScrollBars(); lastSB = NowMs(); }
    return busy;
}

/* ================================================================== */
/* entry point                                                         */
/* ================================================================== */
int WINAPI wWinMain(HINSTANCE hi, HINSTANCE hp, LPWSTR cmdl, int show) {
    (void)hp; (void)cmdl;
    g_inst = hi;
    SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
    INITCOMMONCONTROLSEX icc = { sizeof icc, ICC_STANDARD_CLASSES };
    InitCommonControlsEx(&icc);
    SetDocText(NULL, 0);
    int argc = 0; LPWSTR *argv = CommandLineToArgvW(GetCommandLineW(), &argc);
    const WCHAR *file = NULL; BOOL havePos = FALSE; RECT pos = { 0, 0, 0, 0 };
    for (int i = 1; argv && i < argc; i++) {
        if (!wcscmp(argv[i], L"--selftest") && i + 1 < argc) { wcsncpy(g_stlog, argv[++i], MAX_PATH * 4 - 1); g_selftest = 1; }
        else if (!wcscmp(argv[i], L"--demo") && i + 1 < argc) { wcsncpy(g_demo, argv[++i], 31); g_selftest = 1; }
        else if (!wcscmp(argv[i], L"--bench") && i + 2 < argc) { wcsncpy(g_benchFile, argv[++i], MAX_PATH * 4 - 1); wcsncpy(g_stlog, argv[++i], MAX_PATH * 4 - 1); g_bench = 1; g_selftest = 1; }
        else if (!wcscmp(argv[i], L"--pos") && i + 4 < argc) {
            int x = _wtoi(argv[i + 1]), y = _wtoi(argv[i + 2]), w = _wtoi(argv[i + 3]), h = _wtoi(argv[i + 4]);
            i += 4;
            if (w > 100 && h > 100) { SetRect(&pos, x, y, x + w, y + h); havePos = TRUE; }
        } else file = argv[i];
    }
    g_noIni = g_selftest != 0;
    if (!g_noIni) LoadIni();
    WNDCLASSEXW wc; memset(&wc, 0, sizeof wc);
    wc.cbSize = sizeof wc; wc.hInstance = hi; wc.hCursor = LoadCursorW(NULL, IDC_ARROW);
    wc.hIcon = LoadIconW(NULL, IDI_APPLICATION);
    wc.lpfnWndProc = FrameProc; wc.lpszClassName = CLS_FRAME; wc.style = CS_DBLCLKS;
    RegisterClassExW(&wc);
    wc.lpfnWndProc = TextProc; wc.lpszClassName = CLS_TEXT; wc.style = CS_DBLCLKS; wc.hCursor = LoadCursorW(NULL, IDC_IBEAM);
    RegisterClassExW(&wc);
    wc.lpfnWndProc = FindProc; wc.lpszClassName = CLS_FIND; wc.style = 0; wc.hCursor = LoadCursorW(NULL, IDC_ARROW);
    RegisterClassExW(&wc);
    UINT sdpi = GetDpiForSystem(); if (!sdpi) sdpi = 96;
    int W = MulDiv(g_selftest ? 820 : 900, (int)sdpi, 96), H = MulDiv(g_selftest ? 600 : 640, (int)sdpi, 96);
    HWND h = CreateWindowExW(WS_EX_ACCEPTFILES, CLS_FRAME, APPNAME, WS_OVERLAPPEDWINDOW | WS_CLIPCHILDREN,
                             CW_USEDEFAULT, CW_USEDEFAULT, W, H, NULL, NULL, hi, NULL);
    if (!h) return 1;
    UpdateTitle();
    if (g_selftest) { SetWindowPos(h, NULL, 0, 0, W, H, SWP_NOZORDER); ShowWindow(h, SW_SHOWNORMAL); }
    else if (havePos || g_iniHaveRect) {
        WINDOWPLACEMENT wp = { sizeof wp, 0, 0, { 0, 0 }, { 0, 0 }, { 0, 0, 0, 0 } };
        GetWindowPlacement(h, &wp);
        wp.rcNormalPosition = havePos ? pos : g_iniRect;
        if (havePos && !MonitorFromRect(&pos, MONITOR_DEFAULTTONULL)) OffsetRect(&wp.rcNormalPosition, -pos.left + 40, -pos.top + 40);
        wp.showCmd = (!havePos && g_iniMax) ? SW_SHOWMAXIMIZED : (show == SW_SHOWMINNOACTIVE || show == SW_SHOWMINIMIZED ? (UINT)show : SW_SHOWNORMAL);
        wp.flags = 0;
        SetWindowPlacement(h, &wp);
    } else ShowWindow(h, show);
    UpdateWindow(h);
    if (file && !g_selftest) { LoadFile(file); Refresh(FALSE); }
    if (argv) LocalFree(argv);
    MSG msg;
    for (;;) {                              /* input first; layout work only when the queue is empty */
        if (PeekMessageW(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) break;
            TranslateMessage(&msg); DispatchMessageW(&msg);
        } else if (!IdleWork()) WaitMessage();
    }
    return (int)msg.wParam;
}

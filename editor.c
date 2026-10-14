/*
 * CEditor - custom-drawn Win32 text editor with inline Japanese IME composition.
 * Plain C / Win32 / GDI / IMM32. Own gap buffer, own rendering (no EDIT/RichEdit).
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
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#define APPNAME L"CEditor"
#define CLS     L"CEditorMainWnd"

enum { IDM_NEW = 100, IDM_OPEN, IDM_SAVE, IDM_SAVEAS, IDM_EXIT,
       IDM_UNDO = 200, IDM_REDO, IDM_CUT, IDM_COPY, IDM_PASTE, IDM_DELETE, IDM_SELALL,
       IDM_RECONV,
       IDM_FONT0 = 300, /* +index */
       IDM_ZOOMIN = 400, IDM_ZOOMOUT, IDM_ZOOMRESET };

static const WCHAR *const kFonts[] = { L"MS Gothic", L"BIZ UDGothic", L"Meiryo", L"Yu Gothic UI", L"Consolas" };
static const WCHAR *const kFontLabels[] = { L"MS ゴシック (等幅)", L"BIZ UDゴシック (等幅)", L"メイリオ", L"Yu Gothic UI", L"Consolas" };
#define NFONTS ((int)(sizeof(kFonts)/sizeof(kFonts[0])))

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) { MessageBoxW(NULL, L"メモリ不足です。", APPNAME, MB_ICONERROR); ExitProcess(1); }
    return q;
}
static void *xmalloc(size_t n) { return xrealloc(NULL, n); }
#define IS_HI(c) ((c) >= 0xD800 && (c) <= 0xDBFF)
#define IS_LO(c) ((c) >= 0xDC00 && (c) <= 0xDFFF)

/* ---------------- gap buffer (UTF-16) + line index ---------------- */
static WCHAR *g_buf;
static size_t g_cap, g_gs, g_ge;          /* gap = [g_gs, g_ge) */
static size_t *g_ls; static size_t g_nl, g_lscap; /* line starts */

static size_t DocLen(void) { return g_cap - (g_ge - g_gs); }
static WCHAR DocAt(size_t i) { return i < g_gs ? g_buf[i] : g_buf[i + (g_ge - g_gs)]; }
static void DocGet(size_t p, size_t n, WCHAR *d) {
    if (p < g_gs) {
        size_t a = g_gs - p; if (a > n) a = n;
        memcpy(d, g_buf + p, a * sizeof(WCHAR)); d += a; p += a; n -= a;
    }
    if (n) memcpy(d, g_buf + p + (g_ge - g_gs), n * sizeof(WCHAR));
}
static void GapMove(size_t p) {
    if (p < g_gs) {
        size_t n = g_gs - p;
        memmove(g_buf + g_ge - n, g_buf + p, n * sizeof(WCHAR));
        g_gs -= n; g_ge -= n;
    } else if (p > g_gs) {
        size_t n = p - g_gs;
        memmove(g_buf + g_gs, g_buf + g_ge, n * sizeof(WCHAR));
        g_gs += n; g_ge += n;
    }
}
static void GapReserve(size_t n) {
    if (g_ge - g_gs >= n) return;
    size_t len = DocLen();
    size_t ncap = (len + n) * 2 + 256;
    WCHAR *nb = xmalloc(ncap * sizeof(WCHAR));
    size_t tail = g_cap - g_ge;
    if (g_gs) memcpy(nb, g_buf, g_gs * sizeof(WCHAR));
    if (tail) memcpy(nb + ncap - tail, g_buf + g_ge, tail * sizeof(WCHAR));
    free(g_buf);
    g_buf = nb; g_ge = ncap - tail; g_cap = ncap;
}
static void RebuildLines(void) {
    g_nl = 0;
    if (g_lscap < 64) { g_lscap = 64; g_ls = xrealloc(g_ls, g_lscap * sizeof(size_t)); }
    g_ls[g_nl++] = 0;
    for (int seg = 0; seg < 2; seg++) {
        const WCHAR *b = seg ? g_buf + g_ge : g_buf;
        size_t n = seg ? g_cap - g_ge : g_gs, base = seg ? g_gs : 0;
        for (size_t i = 0; i < n; i++) if (b[i] == L'\n') {
            if (g_nl == g_lscap) { g_lscap *= 2; g_ls = xrealloc(g_ls, g_lscap * sizeof(size_t)); }
            g_ls[g_nl++] = base + i + 1;
        }
    }
}
static size_t LineOf(size_t pos) {
    size_t lo = 0, hi = g_nl - 1;
    while (lo < hi) { size_t m = (lo + hi + 1) / 2; if (g_ls[m] <= pos) lo = m; else hi = m - 1; }
    return lo;
}
static size_t LineStart(size_t L) { return g_ls[L]; }
static size_t LineEnd(size_t L) { return L + 1 < g_nl ? g_ls[L + 1] - 1 : DocLen(); }

static void RawInsert(size_t p, const WCHAR *s, size_t n) {
    if (!n) return;
    GapMove(p); GapReserve(n);
    memcpy(g_buf + g_gs, s, n * sizeof(WCHAR)); g_gs += n;
    RebuildLines();
}
static void RawDelete(size_t p, size_t n) {
    if (!n) return;
    GapMove(p); g_ge += n;
    RebuildLines();
}

/* ---------------- editor state ---------------- */
static HWND g_hwnd;
static HFONT g_font; static LOGFONTW g_lf;
static HDC g_hdcM;                  /* measuring DC with g_font */
static int g_fontIdx = 0, g_fontPt10 = 110; /* size in 1/10 pt */
static UINT g_dpi = 96;
static int g_lineH = 16, g_ascent = 12, g_tabW = 32, g_margin = 4, g_avgW = 8;
static int g_caretW = 2;
static size_t g_caret, g_anchor;    /* doc positions */
static int g_wantX = -1;            /* preferred x for vertical moves */
static size_t g_top;                /* first visible line */
static int g_sx;                    /* horizontal scroll (px) */
static int g_maxW;                  /* widest line seen (px) */
static int g_cw, g_ch;              /* client size */
static BOOL g_focus, g_caretMade;
static BOOL g_modified;
static WCHAR g_path[MAX_PATH * 4];
static int g_enc;                   /* 0=UTF-8 1=UTF-8 BOM 2=Shift_JIS 3=UTF-16LE */
static BOOL g_dragging; static int g_dragMode; /* 0 char, 1 word */
static size_t g_wordA, g_wordB;
static int g_wheelAcc, g_hwheelAcc;
static int g_lastMouseX, g_lastMouseY;

/* IME composition state */
static BOOL g_comp;                 /* between START/ENDCOMPOSITION */
static WCHAR *g_cstr; static int g_clen;
static BYTE *g_cattr;
static DWORD *g_ccl; static int g_nccl; /* clause boundaries */
static int g_ccur;                  /* cursor within comp */
static size_t g_cpos;               /* doc position where comp is shown */
static size_t g_reconvBase, g_reconvLen; static BOOL g_reconvValid;

/* line display buffers */
static WCHAR *g_lb; static int *g_lx; static int *g_dx; static size_t g_lcap;

/* ---------------- undo / redo ---------------- */
typedef struct { BOOL ins; size_t pos; WCHAR *s; size_t n; int grp; size_t cb, ab; } Op;
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

static void EditInsert(size_t p, const WCHAR *s, size_t n) {
    if (!n) return;
    Op o = { TRUE, p, xmalloc(n * sizeof(WCHAR)), n, g_grp, g_caret, g_anchor };
    memcpy(o.s, s, n * sizeof(WCHAR));
    OpPush(&g_undo, o); OpClear(&g_redo);
    RawInsert(p, s, n);
    g_modified = TRUE;
}
static void EditDelete(size_t p, size_t n) {
    if (!n) return;
    Op o = { FALSE, p, xmalloc(n * sizeof(WCHAR)), n, g_grp, g_caret, g_anchor };
    DocGet(p, n, o.s);
    OpPush(&g_undo, o); OpClear(&g_redo);
    RawDelete(p, n);
    g_modified = TRUE;
}

/* ---------------- character helpers ---------------- */
static UINT CpAt(size_t p, int *units) {
    size_t len = DocLen(); WCHAR c = DocAt(p);
    if (IS_HI(c) && p + 1 < len && IS_LO(DocAt(p + 1))) {
        *units = 2; return 0x10000 + (((UINT)c - 0xD800) << 10) + ((UINT)DocAt(p + 1) - 0xDC00);
    }
    *units = 1; return c;
}
static BOOL IsExtender(UINT cp) {   /* code points that stick to the previous one */
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
        if (c2 == 0x200D && p < len && DocAt(p) != L'\n') { CpAt(p, &u); p += u; } /* ZWJ sequence */
    }
    return p;
}
static size_t PrevPos(size_t p) {
    if (p == 0) return 0;
    size_t L = LineOf(p - 1);
    size_t s = LineStart(L);
    if (s == p) return p - 1;                 /* previous char is '\n' */
    if (p - s > 4096) s = p - 64;             /* very long line: approximate start */
    if (s > LineStart(L) && IS_LO(DocAt(s))) s--;
    size_t q = s, prev = s;
    while (q < p) { prev = q; q = NextPos(q); }
    return prev;
}
static int CharClass(UINT c) {
    if (c == L'\n') return 9;
    if (c == L' ' || c == L'\t' || c == 0x3000) return 0;
    if ((c >= L'0' && c <= L'9') || (c >= L'A' && c <= L'Z') || (c >= L'a' && c <= L'z') || c == L'_' ||
        (c >= 0xFF10 && c <= 0xFF19) || (c >= 0xFF21 && c <= 0xFF3A) || (c >= 0xFF41 && c <= 0xFF5A) ||
        (c >= 0xC0 && c <= 0x24F && c != 0xD7 && c != 0xF7)) return 1;
    if (c >= 0x3041 && c <= 0x309F) return 2;                                   /* hiragana */
    if ((c >= 0x30A0 && c <= 0x30FF) || (c >= 0xFF66 && c <= 0xFF9F) || (c >= 0x31F0 && c <= 0x31FF)) return 3; /* katakana */
    if ((c >= 0x4E00 && c <= 0x9FFF) || (c >= 0x3400 && c <= 0x4DBF) || (c >= 0xF900 && c <= 0xFAFF) ||
        (c >= 0x20000 && c <= 0x3FFFF) || c == 0x3005 || c == 0x3006 || c == 0x303B) return 4; /* kanji */
    if (c >= 0x1F000) return 6;                                                 /* emoji */
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

/* ---------------- layout / measuring ---------------- */
static void LineCap(size_t n) {
    if (n + 2 <= g_lcap) return;
    g_lcap = n + 256;
    g_lb = xrealloc(g_lb, g_lcap * sizeof(WCHAR));
    g_lx = xrealloc(g_lx, g_lcap * sizeof(int));
    g_dx = xrealloc(g_dx, g_lcap * sizeof(int));
}
/* Displayed text of line L into g_lb (composition inserted at g_cpos when
   withComp). Returns length; *co = composition offset in the line or -1. */
static int BuildLine(size_t L, BOOL withComp, int *co) {
    size_t s = LineStart(L), e = LineEnd(L), n = e - s;
    int off = -1;
    if (withComp && g_comp && g_clen > 0 && LineOf(g_cpos) == L) off = (int)(g_cpos - s);
    size_t tot = n + (off >= 0 ? (size_t)g_clen : 0);
    LineCap(tot);
    if (off >= 0) {
        DocGet(s, (size_t)off, g_lb);
        memcpy(g_lb + off, g_cstr, (size_t)g_clen * sizeof(WCHAR));
        DocGet(g_cpos, e - g_cpos, g_lb + off + g_clen);
    } else DocGet(s, n, g_lb);
    if (co) *co = off;
    return (int)tot;
}
/* g_lx[i] = x (px, line-relative) of the boundary before unit i; g_lx[n] = width */
static void MeasureLine(int n) {
    int x = 0, i = 0;
    while (i < n) {
        if (g_lb[i] == L'\t') { g_lx[i] = x; x = (x / g_tabW + 1) * g_tabW; i++; continue; }
        int j = i; while (j < n && g_lb[j] != L'\t') j++;
        int k = 0;
        while (k < j - i) {          /* chunk huge runs */
            int cn = j - i - k;
            if (cn > 8192) { cn = 8192; if (IS_HI(g_lb[i + k + cn - 1])) cn--; }
            SIZE sz; int fit = 0;
            GetTextExtentExPointW(g_hdcM, g_lb + i + k, cn, 0, &fit, g_dx, &sz);
            g_lx[i + k] = x;
            for (int t = 1; t < cn; t++) g_lx[i + k + t] = x + g_dx[t - 1];
            x += sz.cx; k += cn;
        }
        i = j;
    }
    g_lx[n] = x;
    for (int t = 1; t < n; t++) if (IS_LO(g_lb[t]) && IS_HI(g_lb[t - 1])) g_lx[t] = g_lx[t - 1];
    if (x > g_maxW) g_maxW = x;
}
static int LineTopY(size_t L) { return (int)((long long)L - (long long)g_top) * g_lineH; }
static int VisLines(void) { int v = g_ch / g_lineH; return v < 1 ? 1 : v; }
static int XOfPos(size_t p) {
    size_t L = LineOf(p);
    int n = BuildLine(L, FALSE, NULL); MeasureLine(n);
    return g_lx[p - LineStart(L)];
}
/* client point of caret; during composition the caret is at GCS_CURSORPOS */
static void CaretPoint(POINT *pt, size_t *pline) {
    size_t L; int idx;
    if (g_comp && g_clen > 0) {
        int co; L = LineOf(g_cpos);
        int n = BuildLine(L, TRUE, &co); MeasureLine(n);
        idx = co + g_ccur;
    } else {
        L = LineOf(g_caret);
        int n = BuildLine(L, FALSE, NULL); MeasureLine(n);
        idx = (int)(g_caret - LineStart(L));
    }
    pt->x = g_lx[idx] - g_sx + g_margin; pt->y = LineTopY(L);
    if (pline) *pline = L;
}
static size_t PosAtX(size_t L, int px) {
    int n = BuildLine(L, FALSE, NULL); MeasureLine(n);
    size_t s = LineStart(L), e = s + (size_t)n, q = s;
    if (px <= 0) return s;
    while (q < e) {
        size_t r = NextPos(q); if (r > e) r = e;
        int x0 = g_lx[q - s], x1 = g_lx[r - s];
        if (px < x1) return (px - x0 < x1 - px) ? q : r;
        q = r;
    }
    return e;
}
static size_t PosFromPoint(int x, int y) {
    long long l = (long long)g_top + (y >= 0 ? y / g_lineH : -((-y + g_lineH - 1) / g_lineH));
    if (l < 0) return 0;
    if ((size_t)l >= g_nl) return DocLen();
    return PosAtX((size_t)l, x + g_sx - g_margin);
}

/* ---------------- scrolling / caret ---------------- */
static void UpdateScrollBars(void) {
    SCROLLINFO si = { sizeof si, SIF_RANGE | SIF_PAGE | SIF_POS | SIF_DISABLENOSCROLL, 0, 0, 0, 0, 0 };
    size_t mx = g_nl - 1 + (size_t)VisLines() - 1;
    si.nMax = mx > 0x7FFFFFF ? 0x7FFFFFF : (int)mx; si.nPage = (UINT)VisLines(); si.nPos = (int)g_top;
    SetScrollInfo(g_hwnd, SB_VERT, &si, TRUE);
    SCROLLINFO hi = { sizeof hi, SIF_RANGE | SIF_PAGE | SIF_POS | SIF_DISABLENOSCROLL, 0, 0, 0, 0, 0 };
    int w = g_cw > 0 ? g_cw : 1;
    hi.nMax = g_maxW + g_margin * 2 + w / 3; hi.nPage = (UINT)w; hi.nPos = g_sx;
    SetScrollInfo(g_hwnd, SB_HORZ, &hi, TRUE);
}
static void UpdateImeWindows(void);
static void PlaceCaret(void) {
    if (g_focus && g_caretMade) { POINT pt; CaretPoint(&pt, NULL); SetCaretPos(pt.x, pt.y); }
    if (g_focus) UpdateImeWindows();
}
static void ClampScroll(void) {
    size_t maxTop = g_nl > 1 ? g_nl - 1 : 0;
    if (g_top > maxTop) g_top = maxTop;
    int maxSx = g_maxW + g_margin * 2 + g_cw / 3 - g_cw; if (maxSx < 0) maxSx = 0;
    if (g_sx > maxSx) g_sx = maxSx;
    if (g_sx < 0) g_sx = 0;
}
static void EnsureVisible(void) {
    POINT pt; size_t L;
    CaretPoint(&pt, &L);
    int vis = VisLines();
    if (L < g_top) g_top = L;
    else if (L >= g_top + (size_t)vis) g_top = L - (size_t)vis + 1;
    int x = pt.x + g_sx - g_margin;
    int w = g_cw - g_margin * 2; if (w < 20) w = 20;
    /* during composition keep the whole target visible if possible */
    if (x < g_sx) { g_sx = x - w / 4; }
    else if (x + g_caretW > g_sx + w) g_sx = x + g_caretW - w + w / 4;
    if (g_sx < 0) g_sx = 0;
}
static void Refresh(BOOL ensure) {
    if (ensure) EnsureVisible();
    UpdateScrollBars();
    InvalidateRect(g_hwnd, NULL, FALSE);
    PlaceCaret();
}
static void UpdateTitle(void) {
    static const WCHAR *const encs[] = { L"UTF-8", L"UTF-8 BOM", L"Shift_JIS", L"UTF-16LE" };
    WCHAR t[MAX_PATH * 4 + 64];
    const WCHAR *name = g_path[0] ? wcsrchr(g_path, L'\\') : NULL;
    name = name ? name + 1 : (g_path[0] ? g_path : L"無題");
    _snwprintf(t, sizeof t / sizeof t[0], L"%ls%ls - %ls [%ls]", g_modified ? L"*" : L"", name, APPNAME, encs[g_enc]);
    t[sizeof t / sizeof t[0] - 1] = 0;
    SetWindowTextW(g_hwnd, t);
}

/* ---------------- font / DPI ---------------- */
static void CreateCaretNow(void) {
    if (!g_focus) return;
    if (g_caretMade) DestroyCaret();
    CreateCaret(g_hwnd, NULL, g_caretW, g_lineH);
    g_caretMade = TRUE;
    PlaceCaret();
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
    SIZE sz; GetTextExtentPoint32W(g_hdcM, L"        ", 8, &sz);  /* tab = 4 half-width spaces */
    g_avgW = sz.cx / 8; if (g_avgW < 1) g_avgW = 1;
    g_tabW = g_avgW * 4;
    g_margin = MulDiv(4, (int)g_dpi, 96);
    DWORD cw = 1; SystemParametersInfoW(SPI_GETCARETWIDTH, 0, &cw, 0);
    g_caretW = MulDiv((int)(cw < 1 ? 1 : cw), (int)g_dpi, 96); if (g_caretW < 1) g_caretW = 1;
    g_maxW = 0;
    if (g_hwnd) {
        SetImeFont();
        CreateCaretNow();
        HMENU m = GetMenu(g_hwnd);
        for (int i = 0; i < NFONTS; i++)
            CheckMenuItem(m, (UINT)(IDM_FONT0 + i), MF_BYCOMMAND | (i == g_fontIdx ? MF_CHECKED : MF_UNCHECKED));
    }
}

/* ---------------- IME helpers ---------------- */
/* target clause [a,b) inside the composition; falls back to the cursor */
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
/* geometry used for composition/candidate placement (client coords) */
static void ImeGeometry(POINT *compPt, int *tx0, int *tx1, int *ty) {
    if (g_comp && g_clen > 0) {
        int co; size_t L = LineOf(g_cpos);
        int n = BuildLine(L, TRUE, &co); MeasureLine(n);
        int ta, tb; CompTarget(&ta, &tb);
        *ty = LineTopY(L);
        compPt->x = g_lx[co] - g_sx + g_margin; compPt->y = *ty;
        *tx0 = g_lx[co + ta] - g_sx + g_margin; *tx1 = g_lx[co + tb] - g_sx + g_margin;
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
static void ClearComp(void) { g_clen = 0; g_nccl = 0; g_ccur = 0; }

/* ---------------- editing ---------------- */
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
    if (kind == K_IME) merge = TRUE;          /* group was opened at WM_IME_STARTCOMPOSITION */
    if (!merge) NewGroup();
    DeleteSelection();
    EditInsert(g_caret, s, n);
    g_caret += n; g_anchor = g_caret;
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
    g_caret = cb > len ? len : cb; g_anchor = ab > len ? len : ab;
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
    g_caret = g_anchor = cp;
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
static size_t NormalizeNewlines(WCHAR *t, size_t n) { /* CRLF/CR -> LF, drop NUL */
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

/* ---------------- file I/O ---------------- */
static void ResetDoc(void) {
    OpClear(&g_undo); OpClear(&g_redo);
    g_caret = g_anchor = 0; g_top = 0; g_sx = 0; g_maxW = 0; g_wantX = -1;
    g_modified = FALSE; BreakUndoMerge();
}
static void SetDocText(const WCHAR *t, size_t n) {
    free(g_buf);
    g_cap = n + 1024; g_buf = xmalloc(g_cap * sizeof(WCHAR));
    if (n) memcpy(g_buf, t, n * sizeof(WCHAR));
    g_gs = n; g_ge = g_cap;
    RebuildLines();
}
static BOOL LoadFile(const WCHAR *path) {
    HANDLE f = CreateFileW(path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
    if (f == INVALID_HANDLE_VALUE) { MessageBoxW(g_hwnd, L"ファイルを開けません。", APPNAME, MB_ICONERROR); return FALSE; }
    LARGE_INTEGER sz; GetFileSizeEx(f, &sz);
    if (sz.QuadPart > 0x3FFFFFFF) { CloseHandle(f); MessageBoxW(g_hwnd, L"ファイルが大きすぎます。", APPNAME, MB_ICONERROR); return FALSE; }
    DWORD n = (DWORD)sz.QuadPart, rd = 0;
    BYTE *b = xmalloc(n + 2);
    BOOL ok = ReadFile(f, b, n, &rd, NULL); CloseHandle(f);
    if (!ok) { free(b); MessageBoxW(g_hwnd, L"読み込みに失敗しました。", APPNAME, MB_ICONERROR); return FALSE; }
    n = rd;
    WCHAR *w; int wn = 0, enc;
    if (n >= 3 && b[0] == 0xEF && b[1] == 0xBB && b[2] == 0xBF) {
        enc = 1;
        wn = MultiByteToWideChar(CP_UTF8, 0, (char *)b + 3, (int)n - 3, NULL, 0);
        w = xmalloc(((size_t)wn + 1) * sizeof(WCHAR));
        if (wn) MultiByteToWideChar(CP_UTF8, 0, (char *)b + 3, (int)n - 3, w, wn);
    } else if (n >= 2 && b[0] == 0xFF && b[1] == 0xFE) {
        enc = 3; wn = (int)(n - 2) / 2;
        w = xmalloc(((size_t)wn + 1) * sizeof(WCHAR)); memcpy(w, b + 2, (size_t)wn * 2);
    } else {
        enc = 0;
        wn = n ? MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, (char *)b, (int)n, NULL, 0) : 0;
        if (n && wn == 0) {           /* invalid UTF-8 -> Shift_JIS (CP932) */
            enc = 2;
            wn = MultiByteToWideChar(932, 0, (char *)b, (int)n, NULL, 0);
            w = xmalloc(((size_t)wn + 1) * sizeof(WCHAR));
            MultiByteToWideChar(932, 0, (char *)b, (int)n, w, wn);
        } else {
            w = xmalloc(((size_t)wn + 1) * sizeof(WCHAR));
            if (n) MultiByteToWideChar(CP_UTF8, 0, (char *)b, (int)n, w, wn);
        }
    }
    free(b);
    size_t len = NormalizeNewlines(w, (size_t)wn);
    SetDocText(w, len); free(w);
    ResetDoc(); g_enc = enc;
    wcsncpy(g_path, path, sizeof g_path / sizeof g_path[0] - 1);
    UpdateTitle(); Refresh(TRUE);
    return TRUE;
}
static BOOL SaveFile(const WCHAR *path) {
    size_t n = DocLen(), lf = 0;
    WCHAR *t = xmalloc((n + 1) * sizeof(WCHAR)); DocGet(0, n, t);
    for (size_t i = 0; i < n; i++) if (t[i] == L'\n') lf++;
    WCHAR *c = xmalloc((n + lf + 1) * sizeof(WCHAR)); size_t k = 0;
    for (size_t i = 0; i < n; i++) { if (t[i] == L'\n') c[k++] = L'\r'; c[k++] = t[i]; }
    free(t);
    int enc = (g_enc == 1) ? 1 : 0;   /* always UTF-8; keep BOM if the file had one */
    int bn = k ? WideCharToMultiByte(CP_UTF8, 0, c, (int)k, NULL, 0, NULL, NULL) : 0;
    BYTE *b = xmalloc((size_t)bn + 3); int off = 0;
    if (enc == 1) { b[0] = 0xEF; b[1] = 0xBB; b[2] = 0xBF; off = 3; }
    if (k) WideCharToMultiByte(CP_UTF8, 0, c, (int)k, (char *)b + off, bn, NULL, NULL);
    free(c);
    HANDLE f = CreateFileW(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    DWORD wr = 0; BOOL ok = FALSE;
    if (f != INVALID_HANDLE_VALUE) { ok = WriteFile(f, b, (DWORD)(bn + off), &wr, NULL) && wr == (DWORD)(bn + off); CloseHandle(f); }
    free(b);
    if (!ok) { MessageBoxW(g_hwnd, L"保存に失敗しました。", APPNAME, MB_ICONERROR); return FALSE; }
    g_enc = enc; g_modified = FALSE;
    if (path != g_path) wcsncpy(g_path, path, sizeof g_path / sizeof g_path[0] - 1);
    UpdateTitle();
    return TRUE;
}
static const WCHAR kFilter[] = L"テキスト ファイル (*.txt)\0*.txt\0すべてのファイル (*.*)\0*.*\0";
static BOOL DoSaveAs(void) {
    WCHAR p[MAX_PATH * 4]; wcsncpy(p, g_path, sizeof p / sizeof p[0] - 1); p[sizeof p / sizeof p[0] - 1] = 0;
    OPENFILENAMEW of; memset(&of, 0, sizeof of);
    of.lStructSize = sizeof of; of.hwndOwner = g_hwnd; of.lpstrFilter = kFilter;
    of.lpstrFile = p; of.nMaxFile = sizeof p / sizeof p[0]; of.lpstrDefExt = L"txt";
    of.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetSaveFileNameW(&of)) return FALSE;
    return SaveFile(p);
}
static BOOL DoSave(void) { return g_path[0] ? SaveFile(g_path) : DoSaveAs(); }
static BOOL ConfirmDiscard(void) {
    if (!g_modified) return TRUE;
    int r = MessageBoxW(g_hwnd, L"変更内容を保存しますか?", APPNAME, MB_YESNOCANCEL | MB_ICONQUESTION);
    if (r == IDCANCEL) return FALSE;
    if (r == IDYES) return DoSave();
    return TRUE;
}
static void DoOpen(void) {
    if (!ConfirmDiscard()) return;
    WCHAR p[MAX_PATH * 4]; p[0] = 0;
    OPENFILENAMEW of; memset(&of, 0, sizeof of);
    of.lStructSize = sizeof of; of.hwndOwner = g_hwnd; of.lpstrFilter = kFilter;
    of.lpstrFile = p; of.nMaxFile = sizeof p / sizeof p[0];
    of.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (GetOpenFileNameW(&of)) LoadFile(p);
}

/* ---------------- painting ---------------- */
static void FillR(HDC dc, int l, int t, int r, int b, COLORREF c) {
    RECT rc = { l, t, r, b }; SetBkColor(dc, c); ExtTextOutW(dc, 0, 0, ETO_OPAQUE, &rc, NULL, 0, NULL);
}
/* EDIT-like composition underline: dotted = input, thin = converted, thick = target */
static void DrawUnderline(HDC dc, int x0, int x1, int y, BYTE attr, COLORREF col) {
    int thin = MulDiv(1, (int)g_dpi, 96); if (thin < 1) thin = 1;
    if (x1 <= x0) return;
    switch (attr) {
    case ATTR_TARGET_CONVERTED:
    case ATTR_TARGET_NOTCONVERTED:
        FillR(dc, x0, y - thin, x1, y + thin, col); break;
    case ATTR_CONVERTED:
    case ATTR_FIXEDCONVERTED:
        FillR(dc, x0, y, x1, y + thin, col); break;
    default:
        for (int x = x0; x < x1; x += thin * 2) FillR(dc, x, y, x + thin < x1 ? x + thin : x1, y + thin, col);
        break;
    }
}
static void Paint(HDC hdc) {
    RECT rc; GetClientRect(g_hwnd, &rc);
    int w = rc.right, h = rc.bottom;
    if (w <= 0 || h <= 0) return;
    HDC dc = CreateCompatibleDC(hdc);
    HBITMAP bmp = CreateCompatibleBitmap(hdc, w, h);
    HGDIOBJ ob = SelectObject(dc, bmp);
    HGDIOBJ of = SelectObject(dc, g_font);
    COLORREF bg = GetSysColor(COLOR_WINDOW), fg = GetSysColor(COLOR_WINDOWTEXT);
    COLORREF sbg = g_focus ? GetSysColor(COLOR_HIGHLIGHT) : GetSysColor(COLOR_BTNFACE);
    COLORREF sfg = g_focus ? GetSysColor(COLOR_HIGHLIGHTTEXT) : fg;
    FillR(dc, 0, 0, w, h, bg);
    SetBkMode(dc, TRANSPARENT);
    SetTextAlign(dc, TA_TOP | TA_LEFT);
    size_t sa = SelA(), sb = SelB();
    int vis = VisLines() + 1;
    int ox = g_margin - g_sx;
    for (int r = 0; r < vis; r++) {
        size_t L = g_top + (size_t)r;
        if (L >= g_nl) break;
        int y = r * g_lineH, co;
        int n = BuildLine(L, TRUE, &co);
        MeasureLine(n);
        size_t s = LineStart(L), e = s + (size_t)n;
        int ss = -1, se = -1;
        if (sa != sb && co < 0 && sb > s && sa <= e) {
            ss = (int)((sa > s ? sa : s) - s);
            se = (int)((sb < e ? sb : e) - s);
            int x0 = g_lx[ss] + ox, x1 = g_lx[se] + ox;
            if (sb > e) x1 += g_avgW;               /* line break is selected */
            if (x1 > x0) FillR(dc, x0, y, x1, y + g_lineH, sbg);
        }
        int i = 0;
        while (i < n) {
            if (g_lb[i] == L'\t') { i++; continue; }
            BOOL insel = (ss >= 0 && i >= ss && i < se);
            int j = i + 1;
            while (j < n && g_lb[j] != L'\t' && ((ss >= 0 && j >= ss && j < se) == insel) && j - i < 2048) j++;
            if (j < n && IS_LO(g_lb[j])) j++;
            int x0 = g_lx[i] + ox, x1 = g_lx[j] + ox;
            if (x1 >= 0 && x0 <= w) {
                SetTextColor(dc, insel ? sfg : fg);
                ExtTextOutW(dc, x0, y, 0, NULL, g_lb + i, (UINT)(j - i), NULL);
            }
            i = j;
        }
        if (co >= 0) {   /* underline per (clause x attribute) run with small gaps between clauses */
            int gap = MulDiv(1, (int)g_dpi, 96); if (gap < 1) gap = 1;
            int uy = y + g_lineH - 2 * gap;
            if (uy < y + g_ascent + gap) uy = y + g_ascent + gap;
            int ci = 0, k = 0;
            while (k < g_clen) {
                while (ci + 1 < g_nccl && (int)g_ccl[ci + 1] <= k) ci++;
                int cend = (ci + 1 < g_nccl) ? (int)g_ccl[ci + 1] : g_clen;
                if (cend > g_clen || cend <= k) cend = g_clen;
                BYTE at = g_cattr[k];
                int m = k + 1;
                while (m < cend && g_cattr[m] == at) m++;
                int x0 = g_lx[co + k] + ox + gap, x1 = g_lx[co + m] + ox - gap;
                if (x1 <= x0) x1 = x0 + 1;
                DrawUnderline(dc, x0, x1, uy, at, at == ATTR_INPUT_ERROR ? RGB(255, 0, 0) : fg);
                k = m;
            }
        }
    }
    BitBlt(hdc, 0, 0, w, h, dc, 0, 0, SRCCOPY);
    SelectObject(dc, of); SelectObject(dc, ob);
    DeleteObject(bmp); DeleteDC(dc);
}

/* ---------------- IME messages ---------------- */
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
}
static void BeginComp(void) {
    if (g_dragging) { g_dragging = FALSE; ReleaseCapture(); }
    NewGroup(); BreakUndoMerge();       /* selection deletion + all results share one undo group */
    if (HasSel()) DeleteSelection();    /* typing over a selection replaces it (like EDIT) */
    g_comp = TRUE; ClearComp(); g_cpos = g_caret;
    UpdateTitle();
}
static void OnStartComposition(void) {
    BeginComp();
    SetImeFont();
    Refresh(TRUE);
}
static void OnComposition(LPARAM lp) {
    HIMC imc = ImmGetContext(g_hwnd);
    if (!imc) return;
    if (!g_comp) BeginComp();           /* some IMEs omit STARTCOMPOSITION for result-only */
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
    ReadCompString(imc, lp);            /* new composition after the result (same message) */
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

/* RECONVERTSTRING for IMR_RECONVERTSTRING / IMR_DOCUMENTFEED. Returns byte size (0 = fail). */
static LRESULT BuildReconvert(RECONVERTSTRING *rs, BOOL docfeed) {
    size_t base, slen, coff, clen;
    WCHAR *tmp; BOOL own = FALSE;
    if (docfeed && g_comp && g_clen > 0) {
        size_t L = LineOf(g_cpos); int co;
        int n = BuildLine(L, TRUE, &co);
        tmp = g_lb; slen = (size_t)n; coff = (size_t)co; clen = (size_t)g_clen; base = LineStart(L);
    } else {
        BOOL sel = HasSel() && !docfeed;
        size_t a = sel ? SelA() : g_caret, b = sel ? SelB() : g_caret;
        size_t La = LineOf(a), Lb = LineOf(b);
        if (La == Lb) { base = LineStart(La); slen = LineEnd(La) - base; }
        else { base = a; slen = b - a; }
        const size_t WIN = 512;           /* limit context on very long lines */
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
        if (g_comp && g_clen > 0) {     /* dwCharPos = offset inside the composition string */
            int co; L = LineOf(g_cpos); int n = BuildLine(L, TRUE, &co); MeasureLine(n);
            DWORD k = cp->dwCharPos; if (k > (DWORD)g_clen) k = (DWORD)g_clen;
            idx = co + (int)k;
        } else {                        /* no composition: relative to caret / selection start */
            size_t base = HasSel() ? SelA() : g_caret;
            L = LineOf(base); int n = BuildLine(L, FALSE, NULL); MeasureLine(n);
            size_t p = base + cp->dwCharPos, e = LineEnd(L); if (p > e) p = e;
            idx = (int)(p - LineStart(L));
        }
        POINT pt = { g_lx[idx] - g_sx + g_margin, LineTopY(L) };
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
    case IMR_CONFIRMRECONVERTSTRING: {  /* IME may have adjusted the range: select exactly that */
        RECONVERTSTRING *rs = (RECONVERTSTRING *)lp;
        if (!rs || !g_reconvValid || g_comp) return 0;
        if (rs->dwStrLen != g_reconvLen) return 0;
        size_t off = rs->dwCompStrOffset / sizeof(WCHAR), n = rs->dwCompStrLen;
        if (off > g_reconvLen || n > g_reconvLen - off) return 0;
        size_t a = g_reconvBase + off, b = a + n;
        if (b > DocLen()) return 0;
        g_anchor = a; g_caret = b; g_wantX = -1;
        Refresh(TRUE);
        return 1;
    }
    case IMR_DOCUMENTFEED:
        return BuildReconvert((RECONVERTSTRING *)lp, TRUE);
    }
    return 0;
}
/* Edit menu 再変換: same handshake EDIT/RichEdit use via SCS_SETRECONVERTSTRING */
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

/* ---------------- caret movement / keyboard ---------------- */
static void MoveTo(size_t p, BOOL extend, BOOL keepX) {
    size_t len = DocLen(); if (p > len) p = len;
    g_caret = p; if (!extend) g_anchor = p;
    if (!keepX) g_wantX = -1;
    BreakUndoMerge();
    Refresh(TRUE);
}
static void MoveVert(long long dl, BOOL extend) {
    size_t L = LineOf(g_caret);
    if (g_wantX < 0) g_wantX = XOfPos(g_caret);
    long long nl = (long long)L + dl;
    size_t p;
    if (nl < 0) p = 0;
    else if (nl >= (long long)g_nl) p = DocLen();
    else p = PosAtX((size_t)nl, g_wantX);
    MoveTo(p, extend, TRUE);
}
static void ScrollLines(long long d) {
    long long t = (long long)g_top + d;
    if (t < 0) t = 0;
    g_top = (size_t)t; ClampScroll();
    Refresh(FALSE);
}
static void CutSel(void) {
    if (!HasSel()) return;
    CopySel(); NewGroup(); DeleteSelection(); BreakUndoMerge(); UpdateTitle(); Refresh(TRUE);
}
static void OnKeyDown(WPARAM vk) {
    BOOL ctrl = GetKeyState(VK_CONTROL) < 0, shift = GetKeyState(VK_SHIFT) < 0;
    size_t len = DocLen();
    switch (vk) {
    case VK_LEFT:
        if (HasSel() && !shift && !ctrl) { MoveTo(SelA(), FALSE, FALSE); break; }
        MoveTo(ctrl ? WordLeft(g_caret) : PrevPos(g_caret), shift, FALSE); break;
    case VK_RIGHT:
        if (HasSel() && !shift && !ctrl) { MoveTo(SelB(), FALSE, FALSE); break; }
        MoveTo(ctrl ? WordRight(g_caret) : NextPos(g_caret), shift, FALSE); break;
    case VK_UP:   if (ctrl) ScrollLines(-1); else MoveVert(-1, shift); break;
    case VK_DOWN: if (ctrl) ScrollLines(1); else MoveVert(1, shift); break;
    case VK_PRIOR: {
        long long v = VisLines() - 1; if (v < 1) v = 1;
        g_top = (long long)g_top > v ? g_top - (size_t)v : 0;
        MoveVert(-v, shift); break;
    }
    case VK_NEXT: {
        long long v = VisLines() - 1; if (v < 1) v = 1;
        g_top += (size_t)v; ClampScroll();
        MoveVert(v, shift); break;
    }
    case VK_HOME:
        if (ctrl) MoveTo(0, shift, FALSE);
        else {  /* smart home: first non-blank, then column 0 */
            size_t L = LineOf(g_caret), s = LineStart(L), e = LineEnd(L), q = s;
            while (q < e && (DocAt(q) == L' ' || DocAt(q) == L'\t' || DocAt(q) == 0x3000)) q++;
            MoveTo(g_caret == q ? s : q, shift, FALSE);
        }
        break;
    case VK_END: MoveTo(ctrl ? len : LineEnd(LineOf(g_caret)), shift, FALSE); break;
    case VK_DELETE:
        if (shift && !ctrl) { CutSel(); break; }
        if (HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); }
        else if (g_caret < len) {
            size_t e = ctrl ? WordRight(g_caret) : NextPos(g_caret);
            if (!(g_lastKind == K_DEL && g_lastEnd == g_caret)) NewGroup();
            EditDelete(g_caret, e - g_caret);
            g_anchor = g_caret; g_lastKind = K_DEL; g_lastEnd = g_caret;
        }
        g_wantX = -1; UpdateTitle(); Refresh(TRUE); break;
    case VK_BACK:
        if (HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); }
        else if (g_caret > 0) {
            size_t s;
            if (ctrl) s = WordLeft(g_caret);
            else {  /* one code point (surrogate pair as a unit), like EDIT */
                s = g_caret - 1;
                if (s > 0 && IS_LO(DocAt(s)) && IS_HI(DocAt(s - 1))) s--;
            }
            if (!(g_lastKind == K_BS && g_lastEnd == g_caret)) NewGroup();
            EditDelete(s, g_caret - s);
            g_caret = g_anchor = s; g_lastKind = K_BS; g_lastEnd = s;
        }
        g_wantX = -1; UpdateTitle(); Refresh(TRUE); break;
    case VK_INSERT:
        if (ctrl && !shift) CopySel();
        else if (shift && !ctrl) { Paste(); UpdateTitle(); Refresh(TRUE); }
        break;
    default:
        if (!ctrl || GetKeyState(VK_MENU) < 0) break;
        switch (vk) {
        case 'A': g_anchor = 0; g_caret = len; Refresh(TRUE); break;
        case 'C': CopySel(); break;
        case 'X': CutSel(); break;
        case 'V': Paste(); UpdateTitle(); Refresh(TRUE); break;
        case 'Z': if (shift) Redo(); else Undo(); UpdateTitle(); Refresh(TRUE); break;
        case 'Y': Redo(); UpdateTitle(); Refresh(TRUE); break;
        case 'O': DoOpen(); break;
        case 'S': if (shift) DoSaveAs(); else DoSave(); break;
        case 'N': SendMessageW(g_hwnd, WM_COMMAND, IDM_NEW, 0); break;
        case VK_OEM_PLUS: case VK_ADD: SendMessageW(g_hwnd, WM_COMMAND, IDM_ZOOMIN, 0); break;
        case VK_OEM_MINUS: case VK_SUBTRACT: SendMessageW(g_hwnd, WM_COMMAND, IDM_ZOOMOUT, 0); break;
        case '0': case VK_NUMPAD0: SendMessageW(g_hwnd, WM_COMMAND, IDM_ZOOMRESET, 0); break;
        }
    }
}
static void OnChar(WPARAM ch) {
    WCHAR c = (WCHAR)ch;
    if (c == L'\r') c = L'\n';
    if ((c < 0x20 && c != L'\n' && c != L'\t') || c == 0x7F) return;  /* Ctrl+letters, BS, ESC */
    /* a surrogate pair arrives as two WM_CHARs: keep the pair in one undo step */
    if (IS_LO(c) && g_caret > 0 && !HasSel() && IS_HI(DocAt(g_caret - 1)) && g_lastEnd == g_caret) {
        EditInsert(g_caret, &c, 1); g_caret++; g_anchor = g_caret; g_lastEnd = g_caret;
    } else InsertText(&c, 1, K_TYPE);
    UpdateTitle(); Refresh(TRUE);
}

/* ---------------- window ---------------- */
static HMENU BuildMenu(void) {
    HMENU bar = CreateMenu(), f = CreatePopupMenu(), e = CreatePopupMenu(), v = CreatePopupMenu();
    AppendMenuW(f, MF_STRING, IDM_NEW, L"新規(&N)\tCtrl+N");
    AppendMenuW(f, MF_STRING, IDM_OPEN, L"開く(&O)...\tCtrl+O");
    AppendMenuW(f, MF_STRING, IDM_SAVE, L"上書き保存(&S)\tCtrl+S");
    AppendMenuW(f, MF_STRING, IDM_SAVEAS, L"名前を付けて保存(&A)...\tCtrl+Shift+S");
    AppendMenuW(f, MF_SEPARATOR, 0, NULL);
    AppendMenuW(f, MF_STRING, IDM_EXIT, L"終了(&X)");
    AppendMenuW(e, MF_STRING, IDM_UNDO, L"元に戻す(&U)\tCtrl+Z");
    AppendMenuW(e, MF_STRING, IDM_REDO, L"やり直し(&R)\tCtrl+Y");
    AppendMenuW(e, MF_SEPARATOR, 0, NULL);
    AppendMenuW(e, MF_STRING, IDM_CUT, L"切り取り(&T)\tCtrl+X");
    AppendMenuW(e, MF_STRING, IDM_COPY, L"コピー(&C)\tCtrl+C");
    AppendMenuW(e, MF_STRING, IDM_PASTE, L"貼り付け(&P)\tCtrl+V");
    AppendMenuW(e, MF_STRING, IDM_DELETE, L"削除(&L)\tDel");
    AppendMenuW(e, MF_SEPARATOR, 0, NULL);
    AppendMenuW(e, MF_STRING, IDM_SELALL, L"すべて選択(&A)\tCtrl+A");
    AppendMenuW(e, MF_STRING, IDM_RECONV, L"再変換(&V)");
    for (int i = 0; i < NFONTS; i++) AppendMenuW(v, MF_STRING, (UINT_PTR)(IDM_FONT0 + i), kFontLabels[i]);
    AppendMenuW(v, MF_SEPARATOR, 0, NULL);
    AppendMenuW(v, MF_STRING, IDM_ZOOMIN, L"拡大(&I)\tCtrl++");
    AppendMenuW(v, MF_STRING, IDM_ZOOMOUT, L"縮小(&O)\tCtrl+-");
    AppendMenuW(v, MF_STRING, IDM_ZOOMRESET, L"標準サイズ(&R)\tCtrl+0");
    AppendMenuW(bar, MF_POPUP, (UINT_PTR)f, L"ファイル(&F)");
    AppendMenuW(bar, MF_POPUP, (UINT_PTR)e, L"編集(&E)");
    AppendMenuW(bar, MF_POPUP, (UINT_PTR)v, L"フォント(&O)");
    return bar;
}
static void OnScroll(int bar, int code) {
    SCROLLINFO si = { sizeof si, SIF_ALL, 0, 0, 0, 0, 0 };
    GetScrollInfo(g_hwnd, bar, &si);
    if (bar == SB_VERT) {
        long long t = (long long)g_top;
        switch (code) {
        case SB_LINEUP: t--; break; case SB_LINEDOWN: t++; break;
        case SB_PAGEUP: t -= VisLines(); break; case SB_PAGEDOWN: t += VisLines(); break;
        case SB_THUMBTRACK: case SB_THUMBPOSITION: t = si.nTrackPos; break;
        case SB_TOP: t = 0; break; case SB_BOTTOM: t = (long long)g_nl; break;
        default: return;
        }
        g_top = t < 0 ? 0 : (size_t)t;
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
static void DragTo(int x, int y) {
    size_t p = PosFromPoint(x, y);
    if (g_dragMode == 1) {
        size_t a, b; WordAt(p, &a, &b);
        if (p < g_wordA) { g_anchor = g_wordB; g_caret = a; }
        else { g_anchor = g_wordA; g_caret = b > g_wordB ? b : g_wordB; }
    } else g_caret = p;
    Refresh(TRUE);
}

static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CREATE:
        g_hwnd = h;
        g_dpi = GetDpiForWindow(h); if (!g_dpi) g_dpi = 96;
        SetupFont();
        return 0;
    case WM_SIZE:
        g_cw = LOWORD(lp); g_ch = HIWORD(lp);
        ClampScroll(); Refresh(FALSE);
        return 0;
    case WM_DPICHANGED: {
        g_dpi = HIWORD(wp);
        SetupFont();
        const RECT *r = (const RECT *)lp;
        SetWindowPos(h, NULL, r->left, r->top, r->right - r->left, r->bottom - r->top, SWP_NOZORDER | SWP_NOACTIVATE);
        Refresh(TRUE);
        return 0;
    }
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps);
        int oldMax = g_maxW;
        Paint(dc);
        EndPaint(h, &ps);
        if (g_maxW != oldMax) UpdateScrollBars();
        return 0;
    }
    case WM_SETFOCUS:
        g_focus = TRUE; CreateCaretNow(); InvalidateRect(h, NULL, FALSE);
        return 0;
    case WM_KILLFOCUS:
        CompleteComposition();              /* EDIT commits the composition on focus loss */
        g_focus = FALSE;
        if (g_caretMade) { DestroyCaret(); g_caretMade = FALSE; }
        if (g_dragging) { g_dragging = FALSE; ReleaseCapture(); }
        InvalidateRect(h, NULL, FALSE);
        return 0;
    case WM_ENTERMENULOOP:
        CompleteComposition();
        break;
    case WM_SETCURSOR:
        if (LOWORD(lp) == HTCLIENT) { SetCursor(LoadCursorW(NULL, IDC_IBEAM)); return TRUE; }
        break;
    case WM_KEYDOWN:
        if (wp == VK_PROCESSKEY) break;     /* consumed by the IME */
        OnKeyDown(wp);
        return 0;
    case WM_CHAR:
        OnChar(wp);
        return 0;
    case WM_UNICHAR:
        if (wp == UNICODE_NOCHAR) return TRUE;
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
        int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
        size_t p = PosFromPoint(x, y);
        g_wantX = -1; BreakUndoMerge();
        if (m == WM_LBUTTONDBLCLK) {
            WordAt(p, &g_wordA, &g_wordB);
            g_anchor = g_wordA; g_caret = g_wordB; g_dragMode = 1;
        } else {
            g_dragMode = 0;
            g_caret = p; if (!(wp & MK_SHIFT)) g_anchor = p;
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
            if (g_lastMouseY < 0) { if (g_top > 0) g_top--; DragTo(g_lastMouseX, g_lastMouseY); }
            else if (g_lastMouseY >= g_ch) { g_top++; ClampScroll(); DragTo(g_lastMouseX, g_lastMouseY); }
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
    case WM_MOUSEWHEEL: {
        if (GET_KEYSTATE_WPARAM(wp) & MK_CONTROL) {
            SendMessageW(h, WM_COMMAND, GET_WHEEL_DELTA_WPARAM(wp) > 0 ? IDM_ZOOMIN : IDM_ZOOMOUT, 0);
            return 0;
        }
        UINT lines = 3; SystemParametersInfoW(SPI_GETWHEELSCROLLLINES, 0, &lines, 0);
        if (lines == 0) return 0;
        if (lines == WHEEL_PAGESCROLL) lines = (UINT)VisLines();
        g_wheelAcc += GET_WHEEL_DELTA_WPARAM(wp);
        int steps = g_wheelAcc * (int)lines / WHEEL_DELTA;
        if (steps) { g_wheelAcc -= steps * WHEEL_DELTA / (int)lines; ScrollLines(-steps); }
        return 0;
    }
    case WM_MOUSEHWHEEL: {
        g_hwheelAcc += GET_WHEEL_DELTA_WPARAM(wp);
        int steps = g_hwheelAcc / (WHEEL_DELTA / 4);
        if (steps) { g_hwheelAcc -= steps * (WHEEL_DELTA / 4); g_sx += steps * g_avgW * 2; ClampScroll(); Refresh(FALSE); }
        return 0;
    }
    case WM_VSCROLL: OnScroll(SB_VERT, LOWORD(wp)); return 0;
    case WM_HSCROLL: OnScroll(SB_HORZ, LOWORD(wp)); return 0;
    case WM_INITMENUPOPUP: {
        HMENU mm = (HMENU)wp;
        EnableMenuItem(mm, IDM_UNDO, MF_BYCOMMAND | (g_undo.n ? MF_ENABLED : MF_GRAYED));
        EnableMenuItem(mm, IDM_REDO, MF_BYCOMMAND | (g_redo.n ? MF_ENABLED : MF_GRAYED));
        UINT s = HasSel() ? MF_ENABLED : MF_GRAYED;
        EnableMenuItem(mm, IDM_CUT, MF_BYCOMMAND | s); EnableMenuItem(mm, IDM_COPY, MF_BYCOMMAND | s);
        EnableMenuItem(mm, IDM_DELETE, MF_BYCOMMAND | s);
        EnableMenuItem(mm, IDM_PASTE, MF_BYCOMMAND | (IsClipboardFormatAvailable(CF_UNICODETEXT) ? MF_ENABLED : MF_GRAYED));
        break;
    }
    case WM_COMMAND: {
        int id = LOWORD(wp);
        CompleteComposition();
        if (id >= IDM_FONT0 && id < IDM_FONT0 + NFONTS) { g_fontIdx = id - IDM_FONT0; SetupFont(); Refresh(TRUE); return 0; }
        switch (id) {
        case IDM_NEW:
            if (ConfirmDiscard()) { SetDocText(NULL, 0); ResetDoc(); g_path[0] = 0; g_enc = 0; UpdateTitle(); Refresh(TRUE); }
            break;
        case IDM_OPEN: DoOpen(); break;
        case IDM_SAVE: DoSave(); break;
        case IDM_SAVEAS: DoSaveAs(); break;
        case IDM_EXIT: SendMessageW(h, WM_CLOSE, 0, 0); break;
        case IDM_UNDO: Undo(); UpdateTitle(); Refresh(TRUE); break;
        case IDM_REDO: Redo(); UpdateTitle(); Refresh(TRUE); break;
        case IDM_CUT: CutSel(); break;
        case IDM_COPY: CopySel(); break;
        case IDM_PASTE: Paste(); UpdateTitle(); Refresh(TRUE); break;
        case IDM_DELETE: if (HasSel()) { NewGroup(); DeleteSelection(); BreakUndoMerge(); UpdateTitle(); Refresh(TRUE); } break;
        case IDM_SELALL: g_anchor = 0; g_caret = DocLen(); Refresh(TRUE); break;
        case IDM_RECONV: SetFocus(h); StartReconversion(); break;
        case IDM_ZOOMIN: if (g_fontPt10 < 720) { g_fontPt10 += 10; SetupFont(); Refresh(TRUE); } break;
        case IDM_ZOOMOUT: if (g_fontPt10 > 60) { g_fontPt10 -= 10; SetupFont(); Refresh(TRUE); } break;
        case IDM_ZOOMRESET: g_fontPt10 = 110; SetupFont(); Refresh(TRUE); break;
        }
        return 0;
    }
    case WM_DROPFILES: {
        WCHAR p[MAX_PATH * 4];
        if (DragQueryFileW((HDROP)wp, 0, p, sizeof p / sizeof p[0]) && ConfirmDiscard()) LoadFile(p);
        DragFinish((HDROP)wp);
        return 0;
    }
    case WM_CLOSE:
        CompleteComposition();
        if (ConfirmDiscard()) DestroyWindow(h);
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(h, m, wp, lp);
}

int WINAPI wWinMain(HINSTANCE hi, HINSTANCE hp, LPWSTR cmd, int show) {
    (void)hp; (void)cmd;
    /* manifest declares PerMonitorV2; this call is a no-op fallback if it is already set */
    SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
    SetDocText(NULL, 0);
    WNDCLASSEXW wc; memset(&wc, 0, sizeof wc);
    wc.cbSize = sizeof wc; wc.style = CS_DBLCLKS; wc.lpfnWndProc = WndProc; wc.hInstance = hi;
    wc.hCursor = LoadCursorW(NULL, IDC_IBEAM);
    wc.hIcon = LoadIconW(NULL, IDI_APPLICATION);
    wc.lpszClassName = CLS;
    RegisterClassExW(&wc);
    HWND h = CreateWindowExW(WS_EX_ACCEPTFILES, CLS, APPNAME, WS_OVERLAPPEDWINDOW | WS_VSCROLL | WS_HSCROLL,
                             CW_USEDEFAULT, CW_USEDEFAULT, 900, 640, NULL, BuildMenu(), hi, NULL);
    if (!h) return 1;
    SetWindowPos(h, NULL, 0, 0, MulDiv(900, (int)g_dpi, 96), MulDiv(640, (int)g_dpi, 96), SWP_NOMOVE | SWP_NOZORDER);
    SetupFont();
    UpdateTitle();
    int argc = 0; LPWSTR *argv = CommandLineToArgvW(GetCommandLineW(), &argc);
    if (argv && argc > 1) LoadFile(argv[1]);
    if (argv) LocalFree(argv);
    ShowWindow(h, show); UpdateWindow(h);
    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0) > 0) { TranslateMessage(&msg); DispatchMessageW(&msg); }
    return (int)msg.wParam;
}

/* native unit tests for regex.c:  gcc -O1 -o retest retest.c regex.c && ./retest */
#include <stdio.h>
#include <string.h>
#include <uchar.h>
#include "regex.h"
static int fails, total;
static int ulen(const char16_t *s) { int n = 0; while (s[n]) n++; return n; }
static void T(const char16_t *pat, int flags, const char16_t *txt, int ms, int me, int g1s, int g1e) {
    int err = -1; total++;
    Regex *re = re_compile((const rechar *)pat, ulen(pat), flags, &err);
    int caps[20]; int ok;
    if (ms == -2) { ok = (re == NULL); }
    else if (!re) ok = 0;
    else {
        int f = re_search(re, (const rechar *)txt, ulen(txt), 0, caps);
        if (ms < 0) ok = !f;
        else ok = f && caps[0] == ms && caps[1] == me && (g1s == -9 || (caps[2] == g1s && caps[3] == g1e));
        if (!ok) printf("   got f=%d %d-%d g1=%d-%d\n", f, caps[0], caps[1], caps[2], caps[3]);
    }
    if (!ok) { fails++; printf("FAIL #%d\n", total); }
    re_free(re);
}
static void R(const char16_t *pat, const char16_t *txt, const char16_t *rep, const char16_t *expect) {
    total++;
    Regex *re = re_compile((const rechar *)pat, ulen(pat), 0, NULL);
    int caps[20]; rechar out[256];
    int ok = 0;
    if (re && re_search(re, (const rechar *)txt, ulen(txt), 0, caps)) {
        int n = re_expand((const rechar *)rep, ulen(rep), (const rechar *)txt, caps, out, 256);
        ok = n == ulen(expect) && memcmp(out, expect, (size_t)n * 2) == 0;
    }
    if (!ok) { fails++; printf("FAIL R #%d\n", total); }
    re_free(re);
}
int main(void) {
    T(u"abc", 0, u"xxabcxx", 2, 5, -9, 0);
    T(u"a.c", 0, u"zabc", 1, 4, -9, 0);
    T(u"ab*c", 0, u"ac abbbc", 0, 2, -9, 0);
    T(u"ab+c", 0, u"ac abbbc", 3, 8, -9, 0);
    T(u"colou?r", 0, u"color colour", 0, 5, -9, 0);
    T(u"a.*b", 0, u"a1b2b", 0, 5, -9, 0);
    T(u"a.*?b", 0, u"a1b2b", 0, 3, -9, 0);
    T(u"a+?", 0, u"aaa", 0, 1, -9, 0);
    T(u"(ab)+", 0, u"xababab", 1, 7, 5, 7);
    T(u"(a|bc)d", 0, u"bcd", 0, 3, 0, 2);
    T(u"^abc", 0, u"xabc", -1, 0, 0, 0);
    T(u"^abc$", 0, u"abc", 0, 3, -9, 0);
    T(u"c$", 0, u"abc", 2, 3, -9, 0);
    T(u"[a-c]+", 0, u"xxbcaz", 2, 5, -9, 0);
    T(u"[^a-c]+", 0, u"abxyc", 2, 4, -9, 0);
    T(u"\\d+", 0, u"memo009.txt", 4, 7, -9, 0);
    T(u"\\w+", 0, u"  日本語テキスト abc", 2, 9, -9, 0);
    T(u"\\s+", 0, u"a \u3000b", 1, 3, -9, 0);
    T(u"\\bcat\\b", 0, u"concat cat", 7, 10, -9, 0);
    T(u"ABC", RE_ICASE, u"xxabc", 2, 5, -9, 0);
    T(u"[A-Z]+", RE_ICASE, u"123abc", 3, 6, -9, 0);
    T(u"ＡＢ", RE_ICASE, u"ａｂ", 0, 2, -9, 0);
    T(u"a{3}", 0, u"aaaa", 0, 3, -9, 0);
    T(u"a{2,3}", 0, u"aaaa", 0, 3, -9, 0);
    T(u"a{2,}", 0, u"a aaaaa", 2, 7, -9, 0);
    T(u"x{a", 0, u"x{a", 0, 3, -9, 0);
    T(u"(a*)*b", 0, u"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac", -1, 0, 0, 0);   /* no blow-up */
    T(u"(a|a)*b", 0, u"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac", -1, 0, 0, 0);
    T(u"(", 0, u"", -2, 0, 0, 0);
    T(u"a)", 0, u"", -2, 0, 0, 0);
    T(u"[abc", 0, u"", -2, 0, 0, 0);
    T(u"*a", 0, u"", -2, 0, 0, 0);
    T(u"(", RE_LITERAL, u"f(x)", 1, 2, -9, 0);
    T(u"\\.", 0, u"a.b", 1, 2, -9, 0);
    T(u"\\u3042", 0, u"xあ", 1, 2, -9, 0);
    T(u".", 0, u"😀a", 0, 2, -9, 0);              /* surrogate pair as one char */
    T(u"(?:ab)+c", 0, u"ababc", 0, 5, -1, -1);
    T(u"x*", 0, u"abc", 0, 0, -9, 0);              /* empty match */
    T(u"テスト", 0, u"これはテストです", 3, 6, -9, 0);
    R(u"(\\w+)@(\\w+)", u"me@host", u"$2 at $1", u"host at me");
    R(u"(\\d+)", u"n=42", u"[\\1]", u"[42]");
    R(u"b", u"abc", u"$&$&$$", u"bb$");
    R(u"b", u"abc", u"", u"");
    printf("%d/%d passed\n", total - fails, total);
    return fails != 0;
}

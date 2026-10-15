/* Small backtracking regex engine for CEditor (UTF-16, line oriented). */
#ifndef CED_REGEX_H
#define CED_REGEX_H
typedef unsigned short rechar;          /* UTF-16 code unit (== WCHAR on Windows) */
#define RE_NCAP 10                      /* groups 0..9 */
typedef struct Regex Regex;
/* flags */
#define RE_ICASE   1
#define RE_LITERAL 2
/* Returns NULL on syntax error; *errpos receives the offending pattern offset. */
Regex *re_compile(const rechar *pat, int len, int flags, int *errpos);
void   re_free(Regex *re);
/* Search text[start..len). ^/$ match at text start/end (text = one line).
   caps[2*i], caps[2*i+1] = group i span (-1 if unset). Returns 1 if found. */
int    re_search(Regex *re, const rechar *text, int len, int start, int *caps);
/* Expand replacement ($0-$9, $&, $$, \1-\9, \n, \t, \\). Returns length; writes up to outcap units if out. */
int    re_expand(const rechar *repl, int rlen, const rechar *text, const int *caps, rechar *out, int outcap);
#endif

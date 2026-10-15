#!/bin/sh
# CEditor - Windows x64 build with MinGW-w64 cross toolchain (Debian/Ubuntu: gcc-mingw-w64-x86-64)
set -eu
cd "$(dirname "$0")"
CC=${CC:-x86_64-w64-mingw32-gcc}
WINDRES=${WINDRES:-x86_64-w64-mingw32-windres}
$WINDRES -O coff -i app.rc -o app.res.o
$CC -O2 -Wall -Wextra -std=c11 -municode -mwindows -static -s \
    -Wl,--dynamicbase -Wl,--nxcompat -Wl,--high-entropy-va \
    -o editor.exe editor.c regex.c app.res.o \
    -limm32 -ldwmapi -luxtheme -lcomctl32 -lcomdlg32 -lshell32 -lgdi32 -luser32 -lkernel32
rm -f app.res.o
echo "built editor.exe ($(stat -c %s editor.exe) bytes)"

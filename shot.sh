#!/bin/sh
# usage: shot.sh mode out.png
export WINEPREFIX=${WINEPREFIX:-$HOME/.wine-cb} WINEDEBUG=-all
cd "$(dirname "$0")"
timeout 60 xvfb-run -a -s "-screen 0 1280x900x24" sh -c "wine cbeditor.exe --demo $1 & sleep 9; xwd -root -silent | convert xwd:- -crop 820x600+0+0 +repage $2; kill %1 2>/dev/null; wineserver -k"

# CEditor — IME インライン変換対応の自前描画テキストエディタ (Win32 / C)

EDIT / RichEdit コントロールを一切使わず、テキストバッファ (UTF-16 ギャップバッファ) と
描画 (GDI, ダブルバッファ) を自前で実装したエディタです。日本語 IME の未確定文字列
(変換中文字列) の振る舞いを、OS 標準 EDIT コントロールに合わせることを主目的にしています。

- 対象: Windows 10/11 x64 (PerMonitorV2 DPI 対応マニフェスト)
- 単体 exe (MinGW-w64 静的リンク。依存はシステム DLL のみ: kernel32/user32/gdi32/imm32/comdlg32/shell32/msvcrt)

## ビルド (Linux)
    sudo apt install gcc-mingw-w64-x86-64 binutils-mingw-w64-x86-64
    ./build.sh      # または make
`-Wall -Wextra` で警告ゼロ。

## ファイル
- `editor.c` 本体 / `app.rc` リソース (マニフェスト・バージョン) / `app.manifest` / `build.sh` / `Makefile`

## 機能
- 複数行、折り返しなし + 横スクロール、タブ (半角4文字幅)
- 矢印 / Home(スマートHome) / End / Ctrl+←→ (単語: 英数・ひらがな・カタカナ・漢字で区切り) / PgUp/PgDn / Ctrl+Home/End / Ctrl+↑↓ (スクロール)
- Shift 選択、マウスクリック・ドラッグ選択 (外へドラッグで自動スクロール)、ダブルクリックで単語選択 (ドラッグで単語単位拡張)
- Ctrl+A/C/X/V (CF_UNICODETEXT, 改行は CRLF でやり取り)、Shift+Del / Ctrl+Ins / Shift+Ins
- Undo/Redo (Ctrl+Z / Ctrl+Y / Ctrl+Shift+Z)。連続入力はまとめ、1 回の変換 (選択削除 + 確定文字列) は 1 ステップ
- サロゲートペア (絵文字・𠮷 など)、異体字セレクタ (IVS)、結合濁点、ZWJ 絵文字はカーソル移動・Delete で1文字扱い。BackSpace は1コードポイント単位
- 開く/保存 (Ctrl+O / Ctrl+S / Ctrl+Shift+S)、ドラッグ&ドロップ、コマンドライン引数
  - 読込: UTF-8 BOM / UTF-16LE BOM / BOM なし UTF-8 (厳密検証) → 不正なら Shift_JIS (CP932)
  - 保存: UTF-8 (元が BOM 付きなら BOM 付き)、改行 CRLF
- フォント: MS ゴシック / BIZ UDゴシック / メイリオ / Yu Gothic UI / Consolas、Ctrl+ホイール・Ctrl +/-/0 で拡大縮小
- DPI 変更 (WM_DPICHANGED) でフォント・キャレット幅・余白を再計算

## IME 処理の要点
| メッセージ | 処理 |
|---|---|
| WM_IME_SETCONTEXT | `ISC_SHOWUICOMPOSITIONWINDOW` を落として DefWindowProc へ (候補ウィンドウ UI は残す) |
| WM_IME_STARTCOMPOSITION | 選択範囲があれば削除 (Undo グループ開始)、合成フォント設定。**DefWindowProc に渡さない** |
| WM_IME_COMPOSITION | 先に `GCS_RESULTSTR` を確定挿入 → 続けて `GCS_COMPSTR/COMPATTR/COMPCLAUSE/CURSORPOS` を読む (同一メッセージで確定+新規未確定に対応)。lParam に GCS_COMPSTR が無ければ未確定は空 (ESC キャンセル)。**DefWindowProc に渡さない** (WM_IME_CHAR の二重入力防止) |
| WM_IME_ENDCOMPOSITION | 未確定状態を破棄 |
| 描画 | 未確定文字列をキャレット位置にインライン描画。下線: ATTR_INPUT=点線、ATTR_CONVERTED=細い実線、ATTR_TARGET_CONVERTED / TARGET_NOTCONVERTED=太線、ATTR_INPUT_ERROR=赤点線。文節 (GCS_COMPCLAUSE) ごとに左右 1px(DPI換算) の隙間 |
| キャレット | 変換中は GCS_CURSORPOS の位置に SetCaretPos |
| 候補窓 | `ImmSetCandidateWindow(CFS_EXCLUDE)`: 注目文節の矩形 (行の上端〜下端) を除外領域に → 注目文節の直下に出る。`ImmSetCompositionWindow(CFS_POINT)` は未確定文字列の先頭。毎回の再描画・スクロール・IMN_OPENCANDIDATE/CHANGECANDIDATE で更新 |
| フォント | `ImmSetCompositionFontW` にエディタの LOGFONT (DPI 込み) |
| WM_IME_REQUEST | IMR_QUERYCHARPOSITION (未確定文字列内の各文字のスクリーン座標・行高・文書矩形)、IMR_COMPOSITIONWINDOW、IMR_CANDIDATEWINDOW、IMR_COMPOSITIONFONT、IMR_RECONVERTSTRING (選択範囲 or キャレット行。長い行は ±512 文字に制限)、IMR_CONFIRMRECONVERTSTRING (IME が調整した範囲を選択)、IMR_DOCUMENTFEED (現在行 + 未確定文字列) |
| 確定 | フォーカス喪失・マウスクリック・メニュー操作・終了時に `ImmNotifyIME(NI_COMPOSITIONSTR, CPS_COMPLETE)` |
| 再変換 | 変換キー (IME 側) のほか、編集メニュー「再変換」で SCS_QUERYRECONVERTSTRING → SCS_SETRECONVERTSTRING |

TSF ベースの新しい MS-IME も、Windows が提供する IMM32 互換レイヤ経由で上記メッセージを送ってくるため、この経路で動作します (TSF の ITextStoreACP は未実装)。

## 手動テスト チェックリスト (Windows 11 + Microsoft IME で実施してください)
比較対象の標準 EDIT として「ファイル名を指定して実行」(Win+R) の入力欄などを横に並べると分かりやすいです (Windows 11 の新メモ帳は EDIT ではありません)。

1. **変換中下線**: 「きょうはいいてんきです」と入力 → 点線下線、キャレットは末尾。システムの浮いた未確定ウィンドウが出ないこと
2. **変換**: Space → 文節ごとに下線が分かれ、注目文節が太線、他は細線。文節間に隙間があること
3. **文節移動**: ←/→ で注目文節 (太線) が移動。Shift+←/→ で文節区切り伸縮、表示が追従すること
4. **候補窓位置**: Space 2回で候補一覧 → 注目文節の **直下・左端揃え**。文節移動で候補窓も移動。ウィンドウ右端/画面下端付近でも行を隠さないこと (下端なら上に出る)
5. **予測候補**: 入力中の予測候補ポップアップがキャレット付近に出ること (IMR_QUERYCHARPOSITION)
6. **確定**: Enter で確定、下線が消え文字が本文に入る。Ctrl+Z 1回で変換1回分が消えること
7. **キャンセル**: ESC (1回目は変換取消し、2回目で全取消し) で本文が変わらないこと
8. **確定+継続**: 長文を変換中に次の文字を打ち始める (自動確定) → 確定分と新しい未確定が正しく並ぶこと
9. **選択置換**: 文字列を選択して IME 入力 → 入力開始時に選択が消え、その位置に未確定文字列。Ctrl+Z で元の選択文字列が戻ること
10. **再変換**: 確定済み「今日」を選択して変換キー → 「きょう」の候補が出る。選択なしでキャレットを単語上に置いて変換キーでも再変換できること。編集メニュー「再変換」も
11. **フォーカス喪失**: 変換中に別ウィンドウをクリック / Alt+Tab → 確定されること (EDIT と同じ)
12. **クリック**: 変換中に本文の別位置をクリック → 確定後、クリック位置へキャレット移動
13. **スクロール**: 変換中にホイールスクロール → 未確定文字列と候補窓が一緒に動く。横スクロールが必要な長い行の右端で変換しても見えること
14. **フォント/DPI**: フォント切替・Ctrl+ホイール後に変換 → 下線・候補位置がずれないこと。DPI の違うモニター間でウィンドウ移動後も同様
15. **サロゲート**: 「𠮷」「😀」を入力 (IME/絵文字パネル Win+.) → ←→ で1文字単位、Delete/BS で半分だけ消えないこと。未確定中に含まれても表示崩れなし
16. **IME オフ直接入力**: 半角英数・Tab・Enter、Ctrl+各キーが文字として入らないこと
17. **ファイル**: Shift_JIS ファイル・UTF-8 BOM 有無を開いてタイトル表示を確認、保存後に再度開いて一致

## 既知の制限・リスク
- 実機 Windows での IME 動作は未検証 (ビルド環境は Linux。Wine で起動・描画・キー入力・選択のみ確認)。上記チェックリストでの確認が必要です
- GDI の GetTextExtentExPoint / ExtTextOut を使用。絵文字はフォントリンクによるモノクロ表示。合字・複雑なスクリプト (アラビア語等) の整形は非対応
- 長大な1行 (数十万文字) は描画・計測が遅くなる可能性 (行単位で毎回計測、キャッシュなし)
- 行インデックスは編集毎に全再構築 (数 MB 程度までは実用範囲)
- 選択中の改行は行末に半角1文字幅の選択色で表示
- 保存は常に UTF-8 (Shift_JIS で開いたファイルも UTF-8 で保存されます)
- 候補窓位置は CFS_EXCLUDE と IMR_QUERYCHARPOSITION の両方で返していますが、最終的な配置は IME 実装依存
- 検索/置換・折り返し・印刷は未実装

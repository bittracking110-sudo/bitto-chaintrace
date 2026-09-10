#!/bin/sh
# 控えたファイルを日付入りの名前にして、コミットまで行う。
# 使い方：管理画面から落とした label-cache.json をこのフォルダに置いて実行。
cd "$(dirname "$0")/.."
SRC="backup/label-cache.json"
[ -f "$SRC" ] || { echo "backup/label-cache.json がありません。管理画面から保存して置いてください"; exit 1; }

# 中身の確認。壊れたファイルをコミットしない。
node -e "
const j=require('./$SRC');
const n=j.labels?Object.keys(j.labels).length:Object.keys(j).length;
if(!n) { console.error('中身が空です。コミットしません'); process.exit(1); }
console.log('件数:', n, j._meta? '（名前あり '+j._meta.named+' ／ 名前なし '+j._meta.unnamed+'）':'');
" || exit 1

DEST="backup/label-cache-$(date +%Y-%m-%d).json"
mv "$SRC" "$DEST"
git add "$DEST"
git commit -q -m "照会済みの名前の控え（$(date +%Y-%m-%d)）" && echo "コミットしました: $DEST"
echo "プッシュする場合： git push origin main"

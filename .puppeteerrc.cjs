/* puppeteer 同梱Chromiumのダウンロードを止める。
   このコンテナには unzip が無く、ダウンロードした zip を展開できずビルドが落ちる。
   代わりに OS 側の chromium（nixpacks.toml の aptPkgs でインストール）を使う。
   実行ファイルの場所は server.js の findChromium() が解決する。

   nixpacks.toml の [variables] でも同じ指定をしているが、
   ビルドの install フェーズに環境変数が渡らない場合に備えて両方に置いている。
   ビルドの失敗は1回あたり10分以上を失うため、確実側に倒す。 */
module.exports = {
  skipDownload: true,
};

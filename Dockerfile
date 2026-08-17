# 報告書のPDF生成に Chromium が必要なため、Nixpacks ではなく Dockerfile で構築する。
#
# Nixpacks では2回失敗した：
#   ・puppeteer 同梱Chromiumを zip で取得するが、コンテナに unzip が無く展開できない
#   ・nixpacks.toml の aptPkgs が Nix パッケージとして解釈され
#     「undefined variable 'chromium'」で停止。さらにベースが Ubuntu で
#     apt の chromium は snap 経由になりコンテナ内で動かない
#
# Debian(bookworm) なら chromium が通常の deb パッケージとして入る。
# 日本語フォントも必須。入れないとPDFの日本語がすべて豆腐（□）になる。
# 報告書は警察や取引所へ相談する際の資料なので、文字化けは許容できない。

FROM node:22-bookworm-slim

ENV NODE_ENV=production \
    PUPPETEER_SKIP_DOWNLOAD=true \
    PUPPETEER_EXECUTABLE_PATH=/usr/bin/chromium

# chromium 本体と、日本語・絵文字フォント。
# ca-certificates は外部API（Blockchair等）のHTTPS通信に必要。
RUN apt-get update && apt-get install -y --no-install-recommends \
      chromium \
      fonts-noto-cjk \
      fonts-noto-color-emoji \
      ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 依存だけ先に入れる。server.js を変えただけの再デプロイでこの層を再利用でき、
# ビルド時間を短縮できる。
# .puppeteerrc.cjs も一緒に入れる。npm ci の時点で無いと puppeteer の
# インストールスクリプトが同梱Chromiumを取りに行く（上の ENV でも止まるが二重に効かせる）。
COPY package.json package-lock.json .puppeteerrc.cjs ./
RUN npm ci --omit=dev

COPY . .

EXPOSE 3000
CMD ["node", "server.js"]

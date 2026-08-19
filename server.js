// ============================================================
// BitTo — LINE ブロックチェーン自動調査サーバー
// BTC / ETH / XRP 対応 | LINE Messaging API + Stripe 決済
// ============================================================
require('dotenv').config();
const express      = require('express');
const crypto       = require('crypto');
const fetch        = require('node-fetch');
const fs           = require('fs');
const fsp          = require('fs').promises;
const cors         = require('cors');
const path         = require('path');
const line         = require('@line/bot-sdk');
const { google }   = require('googleapis');
const nodemailer   = require('nodemailer');

const app  = express();
const PORT = process.env.PORT || 3000;

// ── APIキー ────────────────────────────────────────────────
const BLOCKCHAIR_KEY            = process.env.BLOCKCHAIR_API_KEY;
const ETHERSCAN_KEY             = process.env.ETHERSCAN_API_KEY;
const GEMINI_KEY                = process.env.GEMINI_API_KEY;
// gemini-2.5-flash は新規プロジェクトでは提供終了。既定を現行の別名モデルにし、env で上書き可能に。
const GEMINI_MODEL              = process.env.GEMINI_MODEL || 'gemini-flash-latest';
// モデルの提供終了・パラメータ非対応で全AI機能が止まるのを防ぐため、順に切り替えて試すフォールバック。
// 使えないモデルを候補に残すと、報告書生成のたびに必ず失敗する呼び出しを重ねる。
// 本番ログで次の2つは毎回同じ理由で失敗していたため外した。
//   gemini-2.5-flash : 新規プロジェクトでは提供終了
//   gemini-1.5-flash : v1beta に存在しない
// gemini-2.0-flash は無料枠が0だが、課金を有効にすれば使えるので残す。
const GEMINI_FALLBACK_MODELS    = [GEMINI_MODEL, 'gemini-flash-latest', 'gemini-2.0-flash'];
// 価格定数（トップレベルの文字列テンプレートでも使うため、ファイル冒頭で定義）
const BITTO_PRICE              = 6600;  // BitToの報告書価格（Web/LINEのStripe用。IAP価格はストア側で設定）
const BITTO_PRODUCT_ID         = process.env.BITTO_PRODUCT_ID || 'bitto_report';  // BitToアプリIAPの商品ID
// 1回の申込で受け付けるTXIDの上限。
const BITTO_MAX_TXID = 15;
// 商品IDと付与件数の対応。被害者はTXIDを2〜6件持つことが多く、1件ずつしか
// 買えないと手続きを繰り返させることになるため、件数ごとの商品を用意している。
// アプリ内課金は数量を指定できないため、この対応表が件数の唯一の根拠になる。
//   bitto_report(=1件) / bitto_report_2 … bitto_report_15
// ストアに未作成の商品があっても害はない（アプリは存在する商品だけを選択肢に出す）。
const BITTO_PRODUCT_UNITS = { [BITTO_PRODUCT_ID]: 1 };
for (let i = 2; i <= BITTO_MAX_TXID; i++) BITTO_PRODUCT_UNITS[`${BITTO_PRODUCT_ID}_${i}`] = i;
// Google Play の新方式は `商品ID:購入オプション` の複合IDになるため `:` より前で判定する。
// 対象外の商品なら 0 を返す（＝受け付けない）。
const bittoUnitsOf = pid => BITTO_PRODUCT_UNITS[String(pid || '').split(':')[0]] || 0;
const LINE_CHANNEL_ACCESS_TOKEN = process.env.LINE_CHANNEL_ACCESS_TOKEN;
const LINE_CHANNEL_SECRET       = process.env.LINE_CHANNEL_SECRET;
const STRIPE_SECRET_KEY         = process.env.STRIPE_SECRET_KEY;
const STRIPE_WEBHOOK_SECRET     = process.env.STRIPE_WEBHOOK_SECRET;
const GOOGLE_SHEET_ID           = process.env.GOOGLE_SHEET_ID;
const SMTP_USER                 = process.env.SMTP_USER;
const SMTP_PASS                 = process.env.SMTP_PASS;
// Resend（HTTP APIメール配信：Railwayのポートブロック回避）
const RESEND_API_KEY            = process.env.RESEND_API_KEY;
const MAIL_FROM                 = process.env.MAIL_FROM || 'Connection <onboarding@resend.dev>';
// Railway は RAILWAY_PUBLIC_DOMAIN を自動設定する → https:// を付けて使用
const BASE_URL = process.env.BASE_URL
  || (process.env.RAILWAY_PUBLIC_DOMAIN
      ? `https://${process.env.RAILWAY_PUBLIC_DOMAIN}`
      : `http://localhost:${PORT}`);

// ── RevenueCat（App内課金レシート検証用・秘密キー） ──────────
// RevenueCat ダッシュボード → Project settings → API keys → Secret key（sk_ で始まる）
// 検証対象の商品ID（任意・カンマ区切り）。未設定なら商品ID一致チェックをスキップ。
const REVENUECAT_SECRET_KEY = process.env.REVENUECAT_SECRET_KEY || '';
const RC_PRODUCT_IDS = (process.env.RC_PRODUCT_IDS || '')
  .split(',').map(s => s.trim()).filter(Boolean);
const consumedIapTx = new Set();   // 二重利用防止：検証済みトランザクションID

// ── Stripe（任意） ─────────────────────────────────────────
let stripe = null;
if (STRIPE_SECRET_KEY && !STRIPE_SECRET_KEY.includes('ここに')) {
  stripe = require('stripe')(STRIPE_SECRET_KEY);
}

// ── LINE クライアント ──────────────────────────────────────
const lineConfig = {
  channelAccessToken: LINE_CHANNEL_ACCESS_TOKEN,
  channelSecret:      LINE_CHANNEL_SECRET,
};
const lineClient = new line.Client(lineConfig);

// ══ セッション管理 ════════════════════════════════════════════
// state: idle → waiting_txid → investigating → done
const userSessions    = new Map(); // userId → session
const txidCache       = new Map(); // txid（小文字）→ { result, investigatedAt }
// ── Gemini 呼び出し（モデル終了・パラメータ非対応に強い版）──────────────
// thinkingConfig 非対応やモデルの提供終了で全AI機能が止まらないよう、
// 「モデル × thinkingConfigあり/なし」を順に試し、最初に成功したものを返す。
// すべて失敗した場合のみ null を返し、原因をログに残す。
// Gemini 1回あたりの上限と、全モデルを試し切るまでの総上限。
// AIの本文が無くても報告書自体は出せる（呼び出し側でフォールバックする）ので、
// 待ち続けるより打ち切って納品する方がよい。
const GEMINI_TIMEOUT_MS       = 30000;
const GEMINI_TOTAL_TIMEOUT_MS = 90000;
async function geminiGenerate(prompt, { temperature = 0.4, maxOutputTokens = 1000 } = {}) {
  if (!GEMINI_KEY) return null;
  const deadline = Date.now() + GEMINI_TOTAL_TIMEOUT_MS;
  const tried = [];
  for (const model of [...new Set(GEMINI_FALLBACK_MODELS)]) {
    for (const useThinking of [true, false]) {
      // 総上限を超えたら残りの組み合わせは試さない（全体が長引くのを防ぐ）
      if (Date.now() >= deadline) { tried.push('総時間の上限に到達'); break; }
      const generationConfig = { temperature, maxOutputTokens };
      if (useThinking) generationConfig.thinkingConfig = { thinkingBudget: 0 };
      try {
        // 上限を設けないと応答が返らないときに永久に待ち続け、報告書の生成が
        // 「調査中」のまま止まる（有料の納品物なので致命的）。1回ごとに打ち切る。
        const r = await fetch(`https://generativelanguage.googleapis.com/v1beta/models/${model}:generateContent?key=${GEMINI_KEY}`, {
          method: 'POST', headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ contents: [{ parts: [{ text: prompt }] }], generationConfig }),
          signal: AbortSignal.timeout(GEMINI_TIMEOUT_MS),
        });
        const j = await r.json();
        const text = j.candidates?.[0]?.content?.parts?.[0]?.text;
        if (text) {
          if (tried.length) console.warn(`[Gemini] 復旧 model=${model} thinking=${useThinking} ／ 失敗した組み合わせ: ${tried.join(' | ')}`);
          return text.trim();
        }
        tried.push(`${model}${useThinking ? '+think' : ''}: ${j.error?.message || j.candidates?.[0]?.finishReason || 'empty'}`);
      } catch (e) {
        tried.push(`${model}${useThinking ? '+think' : ''}: ${e.message}`);
      }
    }
  }
  console.error('[Gemini] 全ての組み合わせで失敗:', tried.join(' | '));
  return null;
}

const pendingSessions = new Map(); // sessionId → { userId, txidCount, stripeId }
const reportCache     = new Map(); // reportId  → { html }（メモリキャッシュ）
const txidFormTokens  = new Map();

// ── データ永続化 ───────────────────────────────────────────────
// ⚠️ Railwayのファイルシステムは揮発性（再デプロイで消える）。
//   本番では Railwayの永続ボリュームをマウントし、環境変数 DATA_DIR=/data を設定すること。
//   未設定時はローカル（開発用・揮発）にフォールバック。
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'public', 'reports');
const REPORTS_DIR = DATA_DIR;
if (!fs.existsSync(REPORTS_DIR)) fs.mkdirSync(REPORTS_DIR, { recursive: true });
// 起動時に保存先を明示ログ（Railwayログで永続化の有効/無効を確認できる）
// ⚠️ DATA_DIR が設定されていても、その先にボリュームがマウントされていなければ
//   ただのコンテナ内ディレクトリで再デプロイのたびに消える。環境変数の有無だけでは
//   永続しているか判定できないため、起動をまたいで残る目印ファイルで実測する。
const STORAGE_CHECK_FILE = path.join(REPORTS_DIR, '.storage-check.json');
let storageState = { dataDir: !!process.env.DATA_DIR, persistent: null, since: null, boots: 1 };
try {
  if (fs.existsSync(STORAGE_CHECK_FILE)) {
    const prev = JSON.parse(fs.readFileSync(STORAGE_CHECK_FILE, 'utf8'));
    // 前回の起動で書いた目印が残っている＝再デプロイをまたいでファイルが生き残った
    storageState = { ...storageState, persistent: true, since: prev.since, boots: (prev.boots || 1) + 1 };
  } else {
    storageState.since = new Date().toISOString();
  }
  fs.writeFileSync(STORAGE_CHECK_FILE, JSON.stringify(storageState), 'utf8');
} catch (e) {
  console.error('[Storage] 永続判定に失敗:', e.message);
}
if (!storageState.dataDir) {
  console.log(`[Storage] ⚠️ 揮発モード（DATA_DIR未設定）: ${REPORTS_DIR}（再デプロイで消えます）`);
} else if (storageState.persistent) {
  console.log(`[Storage] ✅ 永続を実測で確認: DATA_DIR=${REPORTS_DIR}（${storageState.since} から ${storageState.boots} 回目の起動）`);
} else {
  console.log(`[Storage] ❓ DATA_DIR=${REPORTS_DIR} は設定済みだが永続かは未確定。` +
    `目印ファイルを作成したので、次回デプロイ後の起動ログで「✅ 永続を実測で確認」が出れば本物。` +
    `出なければボリュームが未マウント＝注文・報告書が毎回消えている。`);
}

// 申込（TXIDフォームトークン）の永続化：再デプロイで注文が消えないように
const TXID_FORMS_FILE = path.join(REPORTS_DIR, 'txid-forms.json');
try {
  if (fs.existsSync(TXID_FORMS_FILE)) {
    const saved = JSON.parse(fs.readFileSync(TXID_FORMS_FILE, 'utf8'));
    for (const [k, v] of Object.entries(saved)) txidFormTokens.set(k, v);
    console.log(`[Forms] 申込 ${txidFormTokens.size}件を復元`);
    // 調査はメモリ上で走っているため、再起動をまたぐと処理が消える。
    // 「調査中」のまま復元された申込は永久に完了しないので、放置せずエラーにして
    // 気づけるようにする（利用者は支払い済みなので、取り残しが最も避けたい）。
    let orphaned = 0;
    for (const v of txidFormTokens.values()) {
      if (v.status === 'investigating') {
        v.status = 'error';
        v.errorMsg = 'サーバー更新により調査が中断されました。サポートより折り返しご連絡いたします。';
        orphaned++;
      }
    }
    if (orphaned) console.warn(`[Forms] ⚠️ 再起動で中断された調査 ${orphaned}件をエラーに変更しました（要フォロー）`);
  }
} catch (e) { console.error('[Forms] 復元失敗:', e.message); }
/* ══ ヒアリング（被害時系列パック）の回答 ══════════════════════
   購入者が答えた内容。氏名・口座・連絡先を含むため、報告書と同じ
   永続ボリュームに置き、外から読めるルートは作らない。
   下書きも保存する。設問数が多く、一度で書き切れないため。 */
const HEARINGS_FILE = path.join(REPORTS_DIR, 'hearings.json');
const hearings = new Map();   // hearingId → { token, answers, status, ... }
try {
  if (fs.existsSync(HEARINGS_FILE)) {
    const saved = JSON.parse(fs.readFileSync(HEARINGS_FILE, 'utf8'));
    for (const [k, v] of Object.entries(saved)) hearings.set(k, v);
    console.log(`[Hearing] ${hearings.size}件を復元`);
  }
} catch (e) { console.error('[Hearing] 復元失敗:', e.message); }

function saveHearings() {
  fsp.writeFile(HEARINGS_FILE, JSON.stringify(Object.fromEntries(hearings)), 'utf8')
    .catch(e => console.error('[Hearing] 保存失敗:', e.message));
}

function saveTxidForms() {
  fsp.writeFile(TXID_FORMS_FILE, JSON.stringify(Object.fromEntries(txidFormTokens)), 'utf8').catch(() => {});
}
// 申込状態（作成・調査中・完了）を定期的に永続化（個別呼び出し漏れを防ぐ）
setInterval(saveTxidForms, 8000);

async function saveReport(reportId, html) {
  reportCache.set(reportId, { html });
  try {
    await fsp.writeFile(path.join(REPORTS_DIR, `${reportId}.html`), html, 'utf8');
  } catch (e) { console.error('[Report] ファイル保存失敗:', e.message); }
  // HTMLを置いた直後にPDFも作る。ここで失敗しても報告書の納品は止めない。
  generateReportPdf(reportId).catch(e => console.error('[PDF] 生成失敗:', e.message));
}

/* ── 報告書のPDF化 ────────────────────────────────────────────
   ブラウザの印刷機能に頼ると、Chrome(iOS) では window.print() から
   システムの印刷画面を開けず、PDF保存ができない（Appleの制約で回避不能）。
   Androidでもアプリ内ブラウザからは印刷メニューに届かない。
   利用者に「ブラウザで開き直してから印刷」を強いることになるため、
   サーバー側でPDFを作って1タップでダウンロードできるようにする。

   報告書は警察や取引所に出す書類なので、端末によって体裁が変わらない
   利点もある。価格グラフ（Chart.js + CoinGecko）は描画を待ってから出力する。 */
const PDF_TIMEOUT_MS = 60000;
let pdfBrowser = null;

/* Chromiumの場所を決める。
   本番はOS側（apt）のchromiumを使う（同梱版はunzipが無く展開できないため）。
   開発機ではpuppeteer同梱版が入っているのでそちらに任せる。 */
function findChromium() {
  const cands = [
    process.env.PUPPETEER_EXECUTABLE_PATH,
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
    '/usr/bin/google-chrome',
  ].filter(Boolean);
  for (const p of cands) {
    try { if (fs.existsSync(p)) return p; } catch { /* 次の候補へ */ }
  }
  return undefined;   // undefined なら puppeteer 同梱版が使われる
}

async function getPdfBrowser() {
  if (pdfBrowser && pdfBrowser.connected) return pdfBrowser;
  const puppeteer = require('puppeteer');
  const executablePath = findChromium();
  console.log('[PDF] Chromium:', executablePath || '同梱版');
  // コンテナ内ではsandboxが使えない。共有メモリも小さいので /tmp を使わせる。
  pdfBrowser = await puppeteer.launch({
    headless: 'new',
    executablePath,
    args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-dev-shm-usage', '--font-render-hinting=none'],
  });
  return pdfBrowser;
}

async function generateReportPdf(reportId) {
  const out = path.join(REPORTS_DIR, `${reportId}.pdf`);
  const browser = await getPdfBrowser();
  const page = await browser.newPage();
  try {
    // 自分自身のHTTPで開く。相対パスやfetchが本番と同じ条件で動く。
    await page.goto(`http://127.0.0.1:${PORT}/report/${reportId}`,
      { waitUntil: 'networkidle0', timeout: PDF_TIMEOUT_MS });
    // 価格グラフはCoinGecko取得後に描画される。canvasが描かれるまで待つ。
    await page.waitForFunction(() => {
      const c = document.querySelector('canvas[data-coin]');
      if (!c) return true;                       // グラフが無い報告書もある
      if (document.querySelector('.chart-error')) return true;  // 取得失敗も確定状態
      return typeof Chart !== 'undefined' && !!Chart.getChart(c);
    }, { timeout: 20000 }).catch(() => { /* 待てなければグラフ無しで出す */ });
    await page.pdf({
      path: out,
      format: 'A4',
      printBackground: true,
      margin: { top: '12mm', right: '10mm', bottom: '12mm', left: '10mm' },
    });
    console.log(`[PDF] 生成: ${reportId}.pdf`);
  } finally {
    await page.close().catch(() => {});
  }
}

/* 被害時系列パックのPDF。報告書と同じChromiumを使い回す。
   パックは表組みが主で待つ要素が無いので、描画完了だけ待てばよい。 */
async function generatePackPdf(hearingId, outPath) {
  const browser = await getPdfBrowser();
  const page = await browser.newPage();
  try {
    await page.goto(`http://127.0.0.1:${PORT}/api/hearing/${hearingId}/pack`,
      { waitUntil: 'networkidle0', timeout: PDF_TIMEOUT_MS });
    await page.pdf({
      path: outPath, format: 'A4', printBackground: true,
      margin: { top: '12mm', right: '10mm', bottom: '12mm', left: '10mm' },
    });
    console.log(`[Pack] PDF生成: ${hearingId}`);
  } finally {
    await page.close().catch(() => {});
  }
}

async function loadReport(reportId) {
  if (reportCache.has(reportId)) return reportCache.get(reportId).html;
  try {
    const html = await fsp.readFile(path.join(REPORTS_DIR, `${reportId}.html`), 'utf8');
    reportCache.set(reportId, { html }); // メモリにも載せる
    return html;
  } catch { return null; }
} // token → { sessionId, userId, count, customerName, email, used, createdAt }

function getSession(userId) {
  if (!userSessions.has(userId)) {
    userSessions.set(userId, { state: 'idle', investigatedList: [] });
  }
  return userSessions.get(userId);
}

function resetSession(userId) {
  userSessions.set(userId, { state: 'idle', investigatedList: [] });
}

// ══ 取引所ラベルDB ═══════════════════════════════════════════
const LABEL_DB = {
  // ─── BTC ───
  '1ndyjtntjmwk5xpnhjgamu4hdhigtobu1s': 'Binance Cold Wallet',
  '34xp4vrocgjym3xr7ycvpfhocnxv4twseo': 'Binance Hot Wallet',
  '3lyjfcfhkxykfqmkgw4beta69jzne8ueyl': 'Coinbase',
  '3cbq7at1ty8kmxwlbkcqfku5y74outz9mv': 'Coinbase 2',
  '385cr5dm96n1hvbdmnlt6xwtimfbkh8c8v': 'Kraken',
  '3bmexqgpg4fxba1kwhRfufxfstrgzfdbhj': 'bitFlyer',
  '3fhnblobjnbcpujbdkzotkhms3kxmg4eee': 'Coincheck',
  '3m219kq8nt418t1zjxtq3y9ghu5nxu5zdnr': 'Bitbank',
  // ─── ETH ───
  '0x3f5ce5fbfe3e9af3971dd833d26ba9b5c936f0be': 'Binance Hot Wallet',
  '0x28c6c06298d514db089934071355e5743bf21d60': 'Binance Hot Wallet 2',
  '0xdfd5293d8e347dfe59e90efd55b2956a1343963d': 'Binance',
  '0x56eddb7aa87536c09ccc2793473599fd21a8b17f': 'Binance',
  '0xa9d1e08c7793af67e9d92fe308d5697fb81d3e43': 'Coinbase',
  '0x71660c4005ba85c37ccec55d0c4493e66fe775d3': 'Coinbase 2',
  '0x503828976d22510aad0201ac7ec88293211d23da': 'Coinbase',
  '0x236f9f97e0e62388479bf9e5ba4889e46b0273c3': 'Coinbase',
  '0xb62132e35a6c13ee1ee0f84dc5d40bad8d815206': 'Coinbase',
  '0x2910543af39aba0cd09dbb2d50200b3e800a63d2': 'Kraken',
  '0x0a869d79a7052c7f1b55a8ebabbea3420f0d1e13': 'Kraken',
  '0xe853c56864a2ebe4576a807d26fdc4a0ada51919': 'Bybit',
  '0xf89d7b9c864f589bbf53a82105107622b35eaa40': 'OKX',
  '0x6cc5f688a315f3dc28a7781717a9a798a59fda7b': 'OKX Hot',
  '0xd551234ae421e3bcba99a0da6d736074f22192ff': 'Binance',
  '0xbe0eb53f46cd790cd13851d5eff43d12404d33e8': 'Binance Cold',
  '0x4976a4a02f38326660d17bf34b431dc6e2eb2327': 'Binance',
  '0x0681d8db095565fe8a346fa0277bffd65d716b4': 'Binance',
  '0xfe9e8709d3215310075d67e3ed32a380ccf451c8': 'Binance',
  '0x85b931a32a0725be14285b66f1a22178c672d69b': 'Binance',
  '0x708396f17127c42383e3b9014072679b2f60b82f': 'OKX',
  '0x69b9f9b28f4fdd3b8b9b52a4b4f3a0b7f26e3f6e': 'OKX',
  '0x2b5634c42055806a59e9107ed44d43c426e58258': 'KuCoin',
  '0x689c56aef474df92d44a1b70850f808488f9769c': 'KuCoin',
  '0xa7efae728d2936e78bda97dc267687568dd593f3': 'Kraken',
  '0x267be1c1d684f78cb4f6a176c4911b741e4ffdc0': 'Kraken',
  '0xcdc195b84cbadbb4f76beab0bd28e95ebf0f1b03': 'Bybit',
  '0xf89d7b9c864f589bbf53a82105107622b35eaa40': 'OKX',
  '0x9c19b0497997fe9e75862688a295168070456951': 'Binance Hot Wallet',
  // ─── OKX 追加 ───
  '0x461249076b88189f8ac9418de28f45859fe67da3': 'OKX',
  '0x8b99f3660622e21f2910ecca7fbe51d654a1517d': 'OKX',
  '0xadb2b42f6bd96f5c65920b9ac88619dce4166f94': 'OKX',
  // ─── Bybit 追加 ───
  '0x1db92e2eebc8e0c075a02bea49a2935bcd2dfcf4': 'Bybit',
  '0xf3b0073e3a7f747c7a38b36b805247b222c302a3': 'Bybit',
  // ─── MEXC ───
  '0x75e89d5979e4f6fba9f97c104c2f0afb3f1dcb88': 'MEXC',
  '0x0211f3cedbef3143223d3acf0e589747933e8527': 'MEXC',
  // ─── Gate.io ───
  '0x0d0707963952f2fba59dd06f2b425ace40b492fe': 'Gate.io',
  '0x7793cd85c11a924478d358d49b05b37e91b5810f': 'Gate.io',
  // ─── Bitget ───
  '0x1ab4973a48dc892cd9971ece8e01dcc7688f8f23': 'Bitget',
  '0x5bdf85216ec1e38d6458c870992a69e38e03f7ef': 'Bitget',
  // ─── 日本取引所 ───
  '0x4b9ea49f4de5b35c8d92c5f9b3e70bea3b3bef5f': 'Coincheck',
  '0x3fbcaaff0f0e2f7b6034e23df7ffe9462e5c52b7': 'Coincheck',
  '0x3d7b3ea634e29e8a5b7ae28e8266d9ab9a53f07b': 'bitFlyer',
  '0x1f857e89c6e40e57c4f2a6d43fa4f1d58ac2aba1': 'bitFlyer',
  '0x5c6f5e8c14d4c9e29e0b4e5c6f5e8c14d4c9e29e': 'Zaif',
  '0x6098d3ab1bcfce4a48e87d6b65e8a8cfeebcd7': 'Bitbank',
  // ─── HitBTC ───
  '0x1c4b70a3968436b9a0a9cf5205c787eb81bb558c': 'HitBTC',
  '0x0a98fb70939162725ae863267f8b056e9d890906': 'HitBTC',
  '0xf259869dfc3f3de5e1b2292882e3d59c8f2d1b01': 'HitBTC',
  '0x3d28a7c8d8f4f06b5f60d5855e5a1f6b5f59f95c': 'HitBTC',
  '1KAt6STtisWMMVo63xFER7NnGBBBBMHTNK': 'HitBTC BTC',
  '1GZEgEoAOcMKoqz93MPpFfQpFPDyKi41jh': 'HitBTC BTC',
  // ─── ブリッジ・DEX（主要） ───
  '0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2': 'Wrapped Ether（WETH）',
  '0xdef1c0ded9bec7f1a1670819833240f027b25eff': '0x Protocol（DEX）',
  '0xe66b31678d6c16e9ebf358268a790b763c133750': '0x Protocol（DEX）',
  '0x1111111254eeb25477b68fb85ed929f73a960582': '1inch v5（DEX）',
  '0x1111111254fb6c44bac0bed2854e76f90643097d': '1inch v4（DEX）',
  '0x111111125421ca6dc452d289314280a0f8842a65': '1inch v6（DEX）',
  '0x7a250d5630b4cf539739df2c5dacb4c659f2488d': 'Uniswap V2 Router',
  '0xe592427a0aece92de3edee1f18e0157c05861564': 'Uniswap V3 Router',
  '0x68b3465833fb72a70ecdf485e0e4c7bd8665fc45': 'Uniswap V3 Router 2',
  '0x3fc91a3afd70395cd496c647d5a6cc9d4b2b7fad': 'Uniswap Universal Router',
  '0xd9e1ce17f2641f24ae83637ab66a2cca9c378b9f': 'SushiSwap Router',
  // Near Protocol Rainbow Bridge
  '0x23ddd3e3692d1861ed57ede224608875809e127f': 'Near Rainbow Bridge（NEARブリッジ）',
  '0x6bfad42cfc4efc96f529d786d643ff4a8b89fa52': 'Near Rainbow Bridge（NEARブリッジ）',
  // Across Protocol Bridge
  '0x5c7bcd6e7de5423a257d81b442095a1a6ced35c5': 'Across Bridge',
  '0xe35e9842fceaca96570b734083f4a58e8f7c5f2a': 'Across Bridge',
  // Stargate Finance
  '0x8731d54e9d02c286767d56ac03e8037c07e01e98': 'Stargate Finance Bridge',
  '0x296f55f8fb28e498b858d0bcda06d955b2cb3f97': 'Stargate Finance Bridge',
  // ─── その他グローバル ───
  '0x4e9ce36e442e55ecd9025b759ce187c9aa80a4b': 'Bitfinex',
  '0x742d35cc6634c0532925a3b844bc454e4438f44e': 'Bitfinex Hot',
  '0x876eabf441b2ee5b5b0554fd502a8e0600950cfa': 'Bitfinex',
  '0xd24400ae8bfebb18ca49be86258a3c749cf46853': 'Gemini',
  '0x07ee55aa48bb72dcc6e9d78256648910de513eca': 'Gemini',
  '0x6fc82a5fe25a5cdb58bc74600a40a69c065263f8': 'Huobi',
  '0xadb2b42f6bd96f5c65920b9ac88619dce4166f94': 'Huobi',
  // ─── XRP ───
  'rpvmhwbsff9imxyj3aazjvkpdtfnsywdky': 'Binance XRP',
  'rlnapokeebj ze2qs6x52yvpzpz8td4dc6w': 'Kraken XRP',
  'rhub8vrugtv4pmoxfrp4rp4svnfxe3j7vy': 'Gatehub',
  'razqnbmgaqrknxcvntxfwpsecmz39aagg':  'Bitstamp XRP',
};

// 自前ラベルDB：Etherscan由来のCEXプリセット + 手動照会(MistTrack/Arkham等)分を読み込み。
// address-labels.json を後に読むことで、手動の確認済みラベルがプリセットを上書きする。
// 使い方：address-labels.json に "小文字アドレス": "取引所名" を追記 → commit&push で自動反映。
for (const labelFile of ['exchange-labels-eth.json', 'address-labels.json']) {
  try {
    const extra = JSON.parse(fs.readFileSync(path.join(__dirname, labelFile), 'utf8'));
    let n = 0;
    for (const [addr, name] of Object.entries(extra)) {
      if (addr.startsWith('_') || !name) continue;   // _note / _source 等のメタは無視
      LABEL_DB[addr.toLowerCase()] = name;
      n++;
    }
    console.log(`[LABEL_DB] ${labelFile} から ${n}件を読み込み`);
  } catch (e) {
    if (e.code !== 'ENOENT') console.error(`[LABEL_DB] ${labelFile} 読み込み失敗:`, e.message);
  }
}

// ══ 取引所連絡先DB ════════════════════════════════════════════
const EXCHANGE_CONTACTS = {
  binance: {
    name: 'Binance', url: 'https://www.binance.com',
    support: 'https://www.binance.com/en/chat',
    leo: 'https://www.binance.com/en/support/law-enforcement',
    email: 'support@binance.com',
    note: '法執行機関ポータルから凍結申請が可能',
  },
  coinbase: {
    name: 'Coinbase', url: 'https://www.coinbase.com',
    support: 'https://help.coinbase.com',
    leo: 'https://www.coinbase.com/legal/law_enforcement',
    email: 'legal@coinbase.com',
    note: '法執行機関向け専用フォームあり',
  },
  kraken: {
    name: 'Kraken', url: 'https://www.kraken.com',
    support: 'https://support.kraken.com',
    email: 'support@kraken.com',
    note: 'サポートチケット経由で法的要請を送付',
  },
  hitbtc: {
    name: 'HitBTC', url: 'https://hitbtc.com',
    support: 'https://support.hitbtc.com',
    email: 'support@hitbtc.com',
    note: 'サポートからフリーズ申請を行う',
  },
  bybit: {
    name: 'Bybit', url: 'https://www.bybit.com',
    support: 'https://www.bybit.com/en/help-center/',
    leo: 'https://www.bybit.com/en/legal/law-enforcement-request',
    email: 'support@bybit.com',
    note: '法執行機関向けガイドラインあり',
  },
  okx: {
    name: 'OKX', url: 'https://www.okx.com',
    support: 'https://www.okx.com/support-center',
    leo: 'https://www.okx.com/help/okxs-law-enforcement-response-guidelines',
    email: 'law_enforcement@okx.com',
    note: '法執行機関専用メールアドレスあり',
  },
  bitfinex: {
    name: 'Bitfinex', url: 'https://www.bitfinex.com',
    support: 'https://support.bitfinex.com',
    email: 'support@bitfinex.com',
    note: 'サポートチケット経由で申請',
  },
  huobi: {
    name: 'HTX (旧Huobi)', url: 'https://www.htx.com',
    support: 'https://www.htx.com/support',
    email: 'support@htx.com',
    note: 'サポートから法的要請フォームを申請',
  },
  kucoin: {
    name: 'KuCoin', url: 'https://www.kucoin.com',
    support: 'https://www.kucoin.com/support',
    leo: 'https://www.kucoin.com/legal/law-enforcement',
    email: 'law@kucoin.com',
    note: '法執行機関向け専用窓口あり',
  },
  gemini: {
    name: 'Gemini', url: 'https://www.gemini.com',
    support: 'https://support.gemini.com',
    email: 'support@gemini.com',
    note: 'コンプライアンスチームへ直接連絡',
  },
  // ─── 日本取引所 ───
  coincheck: {
    name: 'Coincheck', url: 'https://coincheck.com',
    support: 'https://coincheck.com/ja/support',
    email: 'info@coincheck.com',
    note: '日本語サポート対応。警察・弁護士からの書面要請が有効',
  },
  bitflyer: {
    name: 'bitFlyer', url: 'https://bitflyer.com/ja-jp/',
    support: 'https://bitflyer.com/ja-jp/support/',
    email: 'support@bitflyer.com',
    note: '日本語サポート対応。金融庁登録済み取引所',
  },
  zaif: {
    name: 'Zaif', url: 'https://zaif.jp',
    support: 'https://support.zaif.jp',
    email: 'support@zaif.jp',
    note: '日本語サポート対応',
  },
  bitbank: {
    name: 'Bitbank', url: 'https://bitbank.cc',
    support: 'https://support.bitbank.cc',
    email: 'support@bitbank.cc',
    note: '日本語サポート対応。金融庁登録済み取引所',
  },
  // ─── その他グローバル ───
  mexc: {
    name: 'MEXC', url: 'https://www.mexc.com',
    support: 'https://support.mexc.com',
    email: 'support@mexc.com',
    note: 'サポートチケット経由で申請',
  },
  gate: {
    name: 'Gate.io', url: 'https://www.gate.io',
    support: 'https://support.gate.io',
    email: 'support@mail.gate.io',
    note: 'サポートチケット経由で申請',
  },
  bitget: {
    name: 'Bitget', url: 'https://www.bitget.com',
    support: 'https://support.bitget.com',
    email: 'support@bitget.com',
    note: 'サポートから法的要請フォームを申請',
  },
};

function getExchangeContact(exchangeName) {
  if (!exchangeName) return null;
  const lower = exchangeName.toLowerCase();
  for (const [key, info] of Object.entries(EXCHANGE_CONTACTS)) {
    if (lower.includes(key)) return info;
  }
  return null;
}

const EX_KEYWORDS = [
  'binance','okx','okex','coinbase','kraken','bitfinex','huobi',
  'bybit','kucoin','gate','bitflyer','coincheck','zaif','liquid',
  'ftx','bittrex','bitstamp','upbit','bithumb','exchange','hot wallet',
  'cold wallet','bitbank','mexc','crypto.com','hot','cold',
  'hitbtc','hit btc','poloniex','gemini','bitget','lbank','whitebit',
  'phemex','bitmart','digifinex','xt.com','latoken','probit',
  // ブリッジ・スワップ・DEXアグリゲーター
  'bridgers','transit finance','transitswap','transitfinance',
  'changenow','fixedfloat','simpleswap',
  'sideshift','stealthex','exolix','lifi','socket','squid','rango',
  'thorchain','rubic','xy finance','paraswap','1inch','0x protocol',
  // DEX・ルーター・スワップ系コントラクト
  'uniswap','sushiswap','pancakeswap','router','swap router',
  'dex','aggregator','cross-chain','crosschain','bridge',
  // ブリッジ先チェーン・ラップトークン
  'near intents','near bridge','rainbow bridge','wrapped ether','weth',
  'wbtc','wrapped bitcoin','arbitrum bridge','optimism bridge',
  'polygon bridge','stargate','layerzero','hop protocol','across',
  'celer','multichain','anyswap','synapse','connext',
];

function getLabel(addr) {
  if (!addr) return { label: '', type: 'unknown' };
  const lo = addr.toLowerCase();
  const found = LABEL_DB[lo] || LABEL_DB[addr];
  if (found) return { label: found, type: 'exchange' };
  return { label: '', type: 'unknown' };
}

// ══ 取引所ラベルの外部API照会（APIキーがある時だけ動く） ══════
/* 自前DB（LABEL_DB＋JSON）に無いアドレスの取引所名を外部APIで引く。
   MISTTRACK_API_KEY 未設定なら何もしない＝これまで通り自前DBだけで動く。
   有料APIなので、名前が要るノード（到達先と、振る舞いで取引所候補と
   出たノード）に絞り、1調査あたり MISTTRACK_MAX_LOOKUPS 件までにする。
   照会結果は永続ボリュームに残す。再デプロイでコンテナが入れ替わっても
   同じアドレスを二度引かないため。名前が無かった場合も空で残す。 */
const MISTTRACK_KEY  = process.env.MISTTRACK_API_KEY || '';
const MISTTRACK_BASE = process.env.MISTTRACK_BASE_URL || 'https://openapi.misttrack.io/v1';
const MISTTRACK_MAX_LOOKUPS = 3;
const MISTTRACK_COIN = { btc: 'BTC', eth: 'ETH', xrp: 'XRP' };
const LABEL_CACHE_FILE = path.join(DATA_DIR, 'label-cache.json');
const labelCache = new Map();   // 小文字アドレス → 名前（''＝引いたが名前なし）

try {
  const cached = JSON.parse(fs.readFileSync(LABEL_CACHE_FILE, 'utf8'));
  for (const [addr, name] of Object.entries(cached)) labelCache.set(addr, name);
  console.log(`[LabelAPI] キャッシュ ${labelCache.size}件を読み込み`);
} catch (e) {
  if (e.code !== 'ENOENT') console.error('[LabelAPI] キャッシュ読み込み失敗:', e.message);
}

function saveLabelCache() {
  fsp.writeFile(LABEL_CACHE_FILE, JSON.stringify(Object.fromEntries(labelCache), null, 2), 'utf8')
    .catch(e => console.error('[LabelAPI] キャッシュ保存失敗:', e.message));
}

/* 応答の入れ物はプロバイダの仕様変更で変わりうる。
   ありがちな場所を順に見て、最初に見つかった名前を使う。 */
function pickLabelFromResponse(j) {
  const cands = [
    j && j.data && j.data.label, j && j.data && j.data.labels,
    j && j.data && j.data.entity, j && j.data && j.data.name,
    j && j.label, j && j.labels, j && j.entity, j && j.name,
  ];
  for (const c of cands) {
    if (typeof c === 'string' && c.trim()) return c.trim();
    if (Array.isArray(c) && c.length) {
      const first = c.find(v => typeof v === 'string' && v.trim());
      if (first) return first.trim();
    }
  }
  return '';
}

function scrubKey(msg) {
  const m = String(msg || '');
  return MISTTRACK_KEY ? m.split(MISTTRACK_KEY).join('***') : m;
}

function labelApiUrl(addr, chain) {
  const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
  return `${MISTTRACK_BASE}/address_labels?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`;
}

async function lookupLabelAPI(addr, chain) {
  if (!MISTTRACK_KEY) return '';
  const lo = addr.toLowerCase();
  if (labelCache.has(lo)) return labelCache.get(lo);
  try {
    const res = await fetchT(labelApiUrl(addr, chain));
    const j   = await res.json();
    const name = pickLabelFromResponse(j);
    labelCache.set(lo, name);
    saveLabelCache();
    if (name) console.log(`[LabelAPI] ${addr.slice(0, 10)}... → "${name}"`);
    else console.log('[LabelAPI] 名前なし:', addr.slice(0, 12), JSON.stringify(j).slice(0, 200));
    return name;
  } catch (e) {
    // 失敗はキャッシュしない（通信断・レート制限なら次の調査で拾える）
    console.error('[LabelAPI] 照会失敗:', addr.slice(0, 12), scrubKey(e.message));
    return '';
  }
}

function isExchange(label) {
  if (!label) return false;
  return EX_KEYWORDS.some(k => label.toLowerCase().includes(k));
}

// アドレスの「振る舞い」から取引所・ホットウォレットを推定
// txCount・balance・transferTime を使用（enrichPathWithAddressInfo 後に呼び出す）
function inferExchangeByBehavior(node) {
  const tx = node.txCount;
  if (tx == null) return null;
  // 1. TX件数が非常に多い → 大型取引所・サービスの可能性（残高の有無を問わない）
  //    取引所ホットウォレットは残高を持ったままTXが積み上がるため、残高0を条件にしない。
  if (tx >= 500000) return '大型取引所 Hot Wallet（推定）';
  if (tx >= 100000) return '主要取引所 Hot Wallet（推定）';
  if (tx >= 20000)  return '取引所・サービス系ウォレット（推定）';
  // 2. 残高ほぼゼロ かつ TX件数が多い → ホットウォレット / 使い捨て
  if (tx >= 500 && node.balance != null && node.balance < 0.001) {
    return 'ホットウォレット候補（残高0・TX多数）';
  }
  return null;
}

// ══ アドレス残高・TX件数取得 ══════════════════════════════════

const priceCache = new Map(); // chain → { price, ts }

async function getUSDPrice(chain) {
  const key = chain.toLowerCase();
  const cached = priceCache.get(key);
  if (cached && Date.now() - cached.ts < 300000) return cached.price; // 5分キャッシュ
  try {
    const ids = { btc: 'bitcoin', eth: 'ethereum', xrp: 'ripple' }[key];
    if (!ids) return 0;
    const r = await fetchT(`https://api.coingecko.com/api/v3/simple/price?ids=${ids}&vs_currencies=usd`);
    const j = await r.json();
    const price = j[ids]?.usd || 0;
    priceCache.set(key, { price, ts: Date.now() });
    return price;
  } catch { return 0; }
}

// 外部API（Etherscan / Blockchair 等）が応答しない場合に調査全体が停止しないよう、
// fetch に上限時間を付ける。時間切れは例外になり、各呼び出し側の try/catch で握られる。
const FETCH_TIMEOUT_MS = 6000;
async function fetchT(url, opts = {}, ms = FETCH_TIMEOUT_MS) {
  return fetch(url, { ...opts, signal: AbortSignal.timeout(ms) });
}
// 以下3つの時間予算は加算される（追跡→付帯情報→内部送金の順に直列実行）。
// 合計が長いと利用者が結果を待ちきれず「調査が出ない」と受け取られるため、
// 初回照会と合わせて約40秒で必ず返るよう配分する。超過分は部分結果で打ち切る。
const TRACE_BUDGET_MS = 18000;
// アドレス情報付与(enrich)の時間予算。USDT等の巨大コントラクトが混じっても全体を止めない。
const ENRICH_BUDGET_MS = 10000;
// investigateETH の内部呼び出し(calls)ラベル取得の時間予算。
const CALLS_BUDGET_MS = 6000;
// 上記の予算をすべてすり抜けた場合に調査ジョブを強制終了させる上限時間。
const INVESTIGATE_HARD_TIMEOUT_MS = 60000;

async function getAddressInfo(addr, chain) {
  try {
    if (chain === 'eth') {
      const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const r = await fetchT(url);
      const j = await r.json();
      const d = j.data?.[addr.toLowerCase()]?.address;
      if (!d) return null;
      const balNative = parseFloat(d.balance || 0) / 1e18;
      const price     = await getUSDPrice('eth');
      // Blockchairが持つアドレスラベル・コントラクト名を取得
      const bcLabel   = d.label || d.contract_name || '';
      return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price, bcLabel };
    }
    if (chain === 'btc') {
      const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const r = await fetchT(url);
      const j = await r.json();
      const d = j.data?.[addr]?.address;
      if (!d) return null;
      const balNative = parseFloat(d.balance || 0) / 1e8;
      const price     = await getUSDPrice('btc');
      const bcLabel   = d.label || '';
      return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price, bcLabel };
    }
    if (chain === 'xrp') {
      const r = await fetchT(`https://api.xrpscan.com/api/v1/account/${addr}`);
      const j = await r.json();
      const balNative = parseFloat(j.xrpBalance || 0);
      const price     = await getUSDPrice('xrp');
      // XRPScanのアカウント名（取引所名が入ることが多い）
      const bcLabel   = j.accountName?.name || j.username || '';
      return { balance: balNative, txCount: j.TxCount || 0, balanceUSD: balNative * price, bcLabel };
    }
  } catch (e) { console.error('[AddrInfo]', addr, e.message); }
  return null;
}

async function enrichPathWithAddressInfo(path, chain) {
  let exchangeCount = 0;                 // 判明＋推定を合わせた取引所ノード数
  let apiLookups    = 0;                 // 外部ラベルAPIを引いた回数（1調査あたりの上限あり）
  const deadline = Date.now() + ENRICH_BUDGET_MS;  // 巨大コントラクト混在でも全体を止めない
  for (let idx = 0; idx < path.length; idx++) {
    const node = path[idx];
    if (!node.address) continue;
    if (Date.now() > deadline) { console.log(`[enrich] 時間予算に達したため残りノードの情報付与を省略（index ${idx}）`); break; }
    await new Promise(res => setTimeout(res, 250)); // レート制限対策
    const info = await getAddressInfo(node.address, chain);
    if (info) {
      node.balance    = info.balance;
      node.txCount    = info.txCount;
      node.balanceUSD = info.balanceUSD;

      // ① Blockchairのラベルを優先適用（最も信頼性が高い）
      if (info.bcLabel && !node.label) {
        node.label      = info.bcLabel;
        const isEx      = isExchange(info.bcLabel);
        if (isEx) node.isExchange = true;
        console.log(`[Label] ${node.address.slice(0,10)}... → "${info.bcLabel}" (isExchange:${isEx})`);
      }
    }

    // ①' 自前DBにもBlockchairにも無ければ外部API（キー未設定なら何もしない）
    if (!node.label && MISTTRACK_KEY
        && (idx === path.length - 1 || inferExchangeByBehavior(node))) {
      const known = labelCache.has(node.address.toLowerCase());
      if (known || apiLookups < MISTTRACK_MAX_LOOKUPS) {
        if (!known) apiLookups++;
        const apiName = await lookupLabelAPI(node.address, chain);
        if (apiName) {
          node.label = apiName;
          if (isExchange(apiName)) node.isExchange = true;
        }
      }
    }

    // ② 振る舞いから取引所候補を推定（ラベルが付かなかった場合のみ）
    if (!node.label && !node.isExchange) {
      const inferred = inferExchangeByBehavior(node);
      if (inferred) {
        node.label      = inferred;
        node.isExchange = true;
        node.inferred   = true;
      }
    }

    // ③ 2個目の取引所で停止：以降は取引所内移動の可能性が高く意味が薄いため切り捨て
    if (node.isExchange) {
      exchangeCount++;
      if (exchangeCount >= 2) {
        path.splice(idx + 1);
        console.log(`[trace] 2個目の取引所で停止（index ${idx}、以降を切り捨て）`);
        break;
      }
    }
  }
}

// ══ チェーン自動判定 ══════════════════════════════════════════
function detectChain(input) {
  const s = input.trim();
  if (/^0x[0-9a-fA-F]{64}$/.test(s)) return 'eth';
  if (/^[0-9a-f]{64}$/.test(s))       return 'btc';
  if (/^[0-9A-F]{64}$/.test(s))       return 'xrp';
  if (/^[0-9a-fA-F]{64}$/.test(s))    return 'btc';
  return null;
}

// ══ 外部ラベル取得（Etherscan / Blockchair） ══════════════════

const labelFetchCache = new Map(); // addr → label（二重取得防止）

async function fetchAddressLabel(addr, chain) {
  const key = addr.toLowerCase();
  if (labelFetchCache.has(key)) return labelFetchCache.get(key);

  // ① ローカルDB（最速・最優先）
  const local = getLabel(addr);
  if (local.label) {
    labelFetchCache.set(key, local.label);
    return local.label;
  }

  let label = '';

  // ② Etherscan コントラクト名（ETH のみ）
  if (chain === 'eth' && ETHERSCAN_KEY) {
    try {
      const url = `https://api.etherscan.io/v2/api?chainid=1&module=contract&action=getsourcecode&address=${addr}&apikey=${ETHERSCAN_KEY}`;
      const r = await fetchT(url);
      const j = await r.json();
      const name = j.result?.[0]?.ContractName || '';
      // 意味のあるコントラクト名のみ採用（"Vyper_contract"などは除外）
      if (name && name.length > 2 && !['Vyper_contract','0x','_'].some(s => name.startsWith(s))) {
        label = name;
        console.log(`[ExLabel] Etherscan契約名: ${addr.slice(0,10)}... → "${name}"`);
      }
    } catch {}
  }

  // ③ Blockchair アドレスラベル（BTC / ETH）
  if (!label && (chain === 'btc' || chain === 'eth') && BLOCKCHAIR_KEY) {
    try {
      const chain2 = chain === 'btc' ? 'bitcoin' : 'ethereum';
      const addrKey = chain === 'eth' ? addr.toLowerCase() : addr;
      const url = `https://api.blockchair.com/${chain2}/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const r = await fetchT(url);
      const j = await r.json();
      const d = j.data?.[addrKey]?.address;
      const bcLbl = d?.label || d?.contract_name || '';
      if (bcLbl) {
        label = bcLbl;
        console.log(`[ExLabel] Blockchairラベル: ${addr.slice(0,10)}... → "${bcLbl}"`);
      }
    } catch {}
  }

  // ④ XRPScan アカウント名（XRP のみ）
  if (!label && chain === 'xrp') {
    try {
      const r = await fetchT(`https://api.xrpscan.com/api/v1/account/${addr}`);
      const j = await r.json();
      const xrpName = j.accountName?.name || j.username || '';
      if (xrpName) {
        label = xrpName;
        console.log(`[ExLabel] XRPScanラベル: ${addr.slice(0,10)}... → "${xrpName}"`);
      }
    } catch {}
  }

  labelFetchCache.set(key, label);
  return label;
}

// ══ マルチホップ追跡 ══════════════════════════════════════════

function normalizeTimeStr(t) {
  if (!t) return t;
  if (typeof t === 'string') return t.replace(' ', 'T').replace(/Z+$/, '') + 'Z';
  return t;
}

async function getNextTxBTC(addr, afterTime) {
  try {
    const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
    const r = await fetchT(url);
    const j = await r.json();
    const txHashes = j.data?.[addr]?.transactions || [];
    const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
    for (const txHash of txHashes.slice(0, 8)) {
      await new Promise(res => setTimeout(res, 250));
      try {
        const tr = await fetchT(`https://api.blockchair.com/bitcoin/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
        const tj = await tr.json();
        const tdata = tj.data?.[txHash];
        if (!tdata) continue;
        const inputs  = tdata.inputs  || [];
        const outputs = tdata.outputs || [];
        const isOutgoing = inputs.some(i => i.recipient === addr);
        if (!isOutgoing) continue;
        const txMs = new Date(normalizeTimeStr(tdata.transaction.time)).getTime();
        if (txMs < refMs - 3600000) continue;
        const target = outputs.filter(o => o.recipient !== addr).sort((a, b) => b.value - a.value)[0];
        if (!target) continue;
        return { addr: target.recipient, amount: target.value / 1e8, time: tdata.transaction.time, txHash };
      } catch { continue; }
    }
  } catch (e) { console.error('getNextTxBTC:', e.message); }
  return null;
}

async function getNextTxETH(addr, afterTime) {
  const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
  console.log(`[HOP] ETH追跡: ${addr} / 基準: ${isNaN(refMs) ? '不明' : new Date(refMs).toISOString()}`);

  // ① 通常TX（EOAからの送金）
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${addr}&startblock=0&endblock=latest&page=1&offset=1000&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetchT(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Etherscan TX: ${txs.length}件`);
    const candidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      if (!tx.to) continue;
      const db = getLabel(tx.to);
      const lbl = db.label || '';
      const isEx = db.type === 'exchange' || isExchange(lbl);
      candidates.push({ addr: tx.to, amount: parseFloat(tx.value)/1e18, time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, txMs });
    }
    if (candidates.length > 0) {
      const exCand = candidates.find(c => c.isExchange);
      // 取引所優先 → 次に金額最大（最も多くETHが流れた先を追う）
      const byAmount = [...candidates].sort((a, b) => b.amount - a.amount);
      const chosen = exCand || byAmount[0];
      chosen._siblings = candidates.filter(c => c.addr !== chosen.addr).slice(0, 4);
      console.log(`[HOP] ETH送金先: ${chosen.addr} label="${chosen.label}" amount=${chosen.amount} candidates=${candidates.length}`);
      return chosen;
    }
  } catch(e) { console.error('[HOP] Etherscan ETH:', e.message); }

  // ② 内部TX（スマートコントラクト・プロキシ経由の資金移動）
  // ※ sort=desc で最新TX から取得（古いコントラクトはascだと過去TXしか取れない問題を修正）
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlistinternal&address=${addr}&startblock=0&endblock=latest&page=1&offset=1000&sort=desc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetchT(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Internal TX: ${txs.length}件`);
    const intCandidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) break; // sort=desc なので以降は全て古い → 早期終了
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      if (!tx.to) continue;
      if (tx.type === 'delegatecall' || tx.type === 'staticcall') continue; // 実ETH移動なし
      const amt = parseFloat(tx.value) / 1e18;
      if (amt < 0.001) continue;
      const db  = getLabel(tx.to); // ローカルDBのみ（高速）
      const lbl = db.label || '';
      const isEx = db.type === 'exchange' || isExchange(lbl);
      intCandidates.push({ addr: tx.to, amount: amt, time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, txMs });
    }
    if (intCandidates.length > 0) {
      const exCand = intCandidates.find(c => c.isExchange);
      const byAmt  = [...intCandidates].sort((a, b) => b.amount - a.amount);
      const chosen = exCand || byAmt[0];
      chosen._siblings = intCandidates.filter(c => c.addr !== chosen.addr).slice(0, 4);
      console.log(`[HOP] 内部TX送金先: ${chosen.addr} label="${chosen.label}" amt=${chosen.amount} total=${intCandidates.length}`);
      return chosen;
    }
  } catch(e) { console.error('[HOP] Internal TX:', e.message); }

  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=tokentx&address=${addr}&startblock=0&endblock=latest&page=1&offset=1000&sort=desc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetchT(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    const tokenCandidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) break; // sort=desc なので以降は全て古い → 早期終了
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      const db  = getLabel(tx.to);
      const lbl = db.label || '';
      const isEx = db.type === 'exchange' || isExchange(lbl);
      const dec  = parseInt(tx.tokenDecimal) || 18;
      tokenCandidates.push({ addr: tx.to, amount: parseFloat(tx.value)/Math.pow(10,dec), time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, token: tx.tokenSymbol, txMs });
    }
    if (tokenCandidates.length > 0) {
      const exCand = tokenCandidates.find(c => c.isExchange);
      const chosen = exCand || tokenCandidates[0];
      console.log(`[HOP] ERC-20送金先: ${chosen.addr} token=${chosen.token} exchange=${chosen.isExchange}`);
      return chosen;
    }
  } catch(e) { console.error('[HOP] ERC20:', e.message); }

  try {
    const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}&limit=10`;
    const r = await fetchT(url);
    const j = await r.json();
    const txHashes = j.data?.[addr.toLowerCase()]?.transactions || [];
    for (const txHash of txHashes.slice(0, 4)) {
      await new Promise(res => setTimeout(res, 300));
      const tr = await fetchT(`https://api.blockchair.com/ethereum/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
      const tj = await tr.json();
      const txData = tj.data?.[txHash.toLowerCase()];
      if (!txData) continue;
      const tx = txData.transaction;
      if (tx.sender?.toLowerCase() !== addr.toLowerCase()) continue;
      if (new Date(normalizeTimeStr(tx.time)).getTime() < refMs) continue;
      const db  = getLabel(tx.recipient);
      const lbl = db.label || tx.recipient_label || '';
      return { addr: tx.recipient, amount: parseFloat(tx.value)/1e18, time: tx.time, txHash, label: lbl };
    }
  } catch(e) { console.error('[HOP] Blockchair ETH:', e.message); }

  console.log(`[HOP] ${addr} → 次TX見つからず`);
  return null;
}

async function getNextTxXRP(addr, afterTime) {
  try {
    const r = await fetchT(`https://api.xrpscan.com/api/v1/account/${addr}/transactions`);
    const j = await r.json();
    const txs = j.transactions || j || [];
    const refMs = new Date(afterTime).getTime();
    for (const tx of txs) {
      if (tx.Account !== addr) continue;
      if (new Date(tx.date).getTime() < refMs - 1000) continue;
      const db = getLabel(tx.Destination);
      return { addr: tx.Destination, amount: parseFloat(tx.Amount)/1e6, time: tx.date, txHash: tx.hash, label: db.label||'' };
    }
  } catch (e) { console.error('getNextTxXRP:', e.message); }
  return null;
}

async function traceHops(startAddr, startTime, chain, maxHops = 10, deadline = Date.now() + TRACE_BUDGET_MS) {
  const hops = [];
  let currentAddr = startAddr;
  let currentTime = startTime;
  const visited = new Set([startAddr.toLowerCase()]);
  let exCount = 0;                       // ラベルで判明した取引所の数
  for (let i = 0; i < maxHops; i++) {
    if (Date.now() > deadline) { console.log(`[traceHops] 時間予算に達したため打ち切り（${i}ホップで部分結果を返す）`); break; }
    let next = null;
    if (chain === 'btc') next = await getNextTxBTC(currentAddr, currentTime);
    else if (chain === 'eth') next = await getNextTxETH(currentAddr, currentTime);
    else if (chain === 'xrp') next = await getNextTxXRP(currentAddr, currentTime);
    if (!next) break;
    if (visited.has(next.addr.toLowerCase())) break; // ループ防止
    visited.add(next.addr.toLowerCase());
    const db  = getLabel(next.addr);
    const fetchedLabel = await fetchAddressLabel(next.addr, chain);
    const lbl = fetchedLabel || db.label || next.label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    // 同時送金先（siblings）を保存
    const siblings = (next._siblings || []).map(s => ({
      address: s.addr, label: s.label || '', amount: s.amount, token: s.token,
    }));
    console.log(`[traceHops] ホップ${i+1}: ${next.addr.slice(0,10)}... label="${lbl}" exchange=${isEx} siblings=${siblings.length}`);
    hops.push({ address: next.addr, label: lbl, amount: next.amount, token: next.token, isExchange: isEx, time: next.time, txHash: next.txHash, siblings });
    if (isEx) {
      exCount++;
      console.log(`[traceHops] 取引所到達(${exCount}件目): ${lbl}`);
      if (exCount >= 2) break;          // 2個目の取引所で停止
    }
    currentAddr = next.addr;
    currentTime = next.time;
  }
  return hops;
}

// ══ ブロックチェーン調査 ══════════════════════════════════════

async function investigateBTC(txid) {
  const url  = `https://api.blockchair.com/bitcoin/dashboards/transaction/${txid}?key=${BLOCKCHAIR_KEY}`;
  const r    = await fetchT(url);
  const j    = await r.json();
  const data = j.data?.[txid];
  if (!data) throw new Error('BTC TXが見つかりません');
  const tx = data.transaction;
  const inputs = data.inputs || [];
  const outputs = data.outputs || [];
  const senderAddr = inputs[0]?.recipient || '不明';
  const changeAddrs = new Set(inputs.map(i => i.recipient));
  const path = [];
  const exchanges = [];
  for (const out of outputs) {
    if (changeAddrs.has(out.recipient)) continue;
    const db = getLabel(out.recipient);
    const fetchedLabel = await fetchAddressLabel(out.recipient, 'btc');
    const lbl = fetchedLabel || db.label || out.recipient_label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    path.push({ address: out.recipient, label: lbl, amount: out.value/1e8, isExchange: isEx });
    if (isEx) exchanges.push({ name: lbl, address: out.recipient, amount: out.value/1e8 });
  }
  // 全ての送金先アドレスからホップ追跡（取引所が見つかっていない送金先のみ）
  // ※ 安全のため最大10件（一括送金TXでの過負荷防止）
  const nonExPaths = path.filter(p => !p.isExchange);
  const btcDeadline = Date.now() + TRACE_BUDGET_MS;   // 全送金先の追跡を合計でこの時間内に収める
  for (const startNode of nonExPaths.slice(0, 10)) {
    if (Date.now() > btcDeadline) break;
    const hops = await traceHops(startNode.address, tx.time, 'btc', 10, btcDeadline);
    for (const hop of hops) {
      if (!path.some(p => p.address === hop.address)) {
        path.push(hop);
        if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
      }
    }
  }
  return { chain: 'BTC', txid, blockTime: tx.time, blockHeight: tx.block_id,
    amount: tx.output_total/1e8, fee: tx.fee/1e8,
    sender: senderAddr, senderLabel: getLabel(senderAddr).label, path, exchanges };
}

async function investigateETH(hash) {
  const h   = hash.startsWith('0x') ? hash : '0x' + hash;
  const url = `https://api.blockchair.com/ethereum/dashboards/transaction/${h}?key=${BLOCKCHAIR_KEY}`;
  const r   = await fetchT(url);
  const j   = await r.json();
  const data = j.data?.[h.toLowerCase()];
  if (!data) throw new Error('ETH TXが見つかりません');
  const tx = data.transaction;
  const calls = data.calls || [];
  const senderDb = getLabel(tx.sender);
  const recipDb  = getLabel(tx.recipient);
  const recipFetchedLabel = await fetchAddressLabel(tx.recipient, 'eth');
  const recipLbl = recipFetchedLabel || recipDb.label || tx.recipient_label || '';
  const isRecipEx = recipDb.type === 'exchange' || isExchange(recipLbl);
  const path = [
    { address: tx.sender,    label: senderDb.label || tx.sender_label || '', role: 'sender' },
    { address: tx.recipient, label: recipLbl, role: 'recipient', isExchange: isRecipEx },
  ];
  const exchanges = [];
  if (isRecipEx) exchanges.push({ name: recipLbl, address: tx.recipient, amount: parseFloat(tx.value)/1e18 });

  // 内部呼び出し（calls）を全て追加 — 金額あり または 既知アドレス
  const callsDeadline = Date.now() + CALLS_BUDGET_MS;
  for (const call of calls) {
    if (Date.now() > callsDeadline) { console.log('[ETH] callsラベル取得が時間予算に達したため打ち切り'); break; }
    if (!call.recipient) continue;
    const callRecipLower = call.recipient.toLowerCase();
    if (callRecipLower === tx.sender?.toLowerCase()) continue; // 送信者へのコールはスキップ
    if (path.some(p => p.address?.toLowerCase() === callRecipLower)) continue; // 重複スキップ
    const db = getLabel(call.recipient);
    const fetchedLabel = await fetchAddressLabel(call.recipient, 'eth');
    const lbl = fetchedLabel || db.label || call.recipient_label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    const callAmt = parseFloat(call.value || '0') / 1e18;
    if (callAmt > 0.000001 || isEx) { // 実質送金額ありまたは既知取引所
      path.push({ address: call.recipient, label: lbl, role: 'internal', isExchange: isEx, amount: callAmt });
      if (isEx) exchanges.push({ name: lbl, address: call.recipient, amount: callAmt });
    }
  }

  // ERC-20トークン送金の検出（送金額0の場合）
  let tokenSymbol = null;
  let tokenAmount = 0;
  let tokenRecipient = null;
  if (parseFloat(tx.value) === 0 && tx.block_id) {
    try {
      const etUrl = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=tokentx&address=${tx.sender}&startblock=${tx.block_id}&endblock=${tx.block_id}&sort=asc&apikey=${ETHERSCAN_KEY}`;
      const etR = await fetchT(etUrl);
      const etJ = await etR.json();
      const tokenTxs = Array.isArray(etJ.result) ? etJ.result : [];
      const matchTx = tokenTxs.find(t => t.hash.toLowerCase() === h.toLowerCase());
      if (matchTx) {
        const dec = parseInt(matchTx.tokenDecimal) || 18;
        tokenSymbol = matchTx.tokenSymbol;
        tokenAmount = parseFloat(matchTx.value) / Math.pow(10, dec);
        tokenRecipient = matchTx.to;
        console.log(`[ETH] ERC-20検出: ${tokenAmount} ${tokenSymbol} → ${tokenRecipient}`);
        // トークン受取人がpath未登録なら追加
        if (tokenRecipient && !path.some(p => p.address?.toLowerCase() === tokenRecipient.toLowerCase())) {
          const trDb  = getLabel(tokenRecipient);
          const trLbl = await fetchAddressLabel(tokenRecipient, 'eth').catch(() => '') || trDb.label || '';
          const trIsEx = trDb.type === 'exchange' || isExchange(trLbl);
          path.push({ address: tokenRecipient, label: trLbl, role: 'token_recipient', isExchange: trIsEx, amount: tokenAmount, token: tokenSymbol });
          if (trIsEx) exchanges.push({ name: trLbl, address: tokenRecipient, amount: tokenAmount });
        }
      }
    } catch(e) { console.error('[ETH] ERC20検出エラー:', e.message); }
  }

  // 直接送金先が取引所でない場合 → 送金先からホップ追跡
  const traceFrom = tokenRecipient || tx.recipient;
  if (!isRecipEx && !exchanges.length) {
    const hops = await traceHops(traceFrom, tx.time, 'eth', 10, Date.now() + TRACE_BUDGET_MS);
    for (const hop of hops) {
      if (!path.some(p => p.address?.toLowerCase() === hop.address?.toLowerCase())) {
        path.push(hop);
        if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
      }
    }
  }
  return { chain: 'ETH', txid: h, blockTime: tx.time, blockHeight: tx.block_id,
    amount: parseFloat(tx.value)/1e18, fee: (tx.gas_used * tx.gas_price)/1e18,
    tokenSymbol, tokenAmount,
    sender: tx.sender, senderLabel: senderDb.label, recipient: tx.recipient, path, exchanges };
}

async function investigateXRP(txid) {
  const h = txid.toUpperCase();
  const r = await fetchT(`https://api.xrpscan.com/api/v1/tx/${h}`);
  const t = await r.text();
  if (t === 'Not found') throw new Error('XRP TXが見つかりません');
  const tx = JSON.parse(t);
  const senderDb = getLabel(tx.Account);
  const destDb   = getLabel(tx.Destination);
  const destFetchedLabel = await fetchAddressLabel(tx.Destination, 'xrp');
  const destLbl  = destFetchedLabel || destDb.label || tx.destinationName || '';
  const isDestEx = destDb.type === 'exchange' || isExchange(destLbl);
  const path = [
    { address: tx.Account,     label: senderDb.label, role: 'sender' },
    { address: tx.Destination, label: destLbl, role: 'recipient', isExchange: isDestEx },
  ];
  const exchanges = isDestEx ? [{ name: destLbl, address: tx.Destination, amount: parseFloat(tx.Amount)/1e6 }] : [];
  if (!isDestEx) {
    const hops = await traceHops(tx.Destination, tx.date, 'xrp', 10);
    for (const hop of hops) {
      if (!path.some(p => p.address === hop.address)) {
        path.push(hop);
        if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
      }
    }
  }
  return { chain: 'XRP', txid: h, blockTime: tx.date, blockHeight: tx.ledger_index,
    amount: parseFloat(tx.Amount)/1e6, sender: tx.Account, senderLabel: senderDb.label,
    recipient: tx.Destination, destTag: tx.DestinationTag, path, exchanges };
}

async function investigate(txid, chain) {
  let result;
  if (chain === 'btc') result = await investigateBTC(txid);
  else if (chain === 'eth') result = await investigateETH(txid);
  else if (chain === 'xrp') result = await investigateXRP(txid);
  else throw new Error('未対応チェーン');

  // 各アドレスノードに残高・TX件数を付加
  await enrichPathWithAddressInfo(result.path, chain);
  return result;
}

// ══ レポート生成 ══════════════════════════════════════════════

function fmtDate(d) {
  if (!d) return '不明';
  try {
    const s = typeof d === 'string'
      ? d.replace(' ', 'T').replace(/Z+$/, '') + 'Z' : d;
    const dt = new Date(s);
    if (isNaN(dt.getTime())) return '不明';
    return dt.toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  } catch { return '不明'; }
}

function buildReport(result) {
  const em      = { BTC: '₿', ETH: 'Ξ', XRP: '✕' }[result.chain] || '🔗';
  const txShort = result.txid.slice(0, 10) + '...' + result.txid.slice(-6);

  const pathLines = (result.path || []).map((p, i) => {
    const addrShort = p.address.slice(0, 10) + '...' + p.address.slice(-6);
    if (i === 0) return `🔴 被害者ウォレット\n   ${addrShort}`;
    const timeStr   = p.time ? `\n   📅 ${fmtDate(p.time)}` : '';
    const amountStr = (p.amount != null && !isNaN(p.amount) && p.amount > 0)
      ? `\n   💰 ${p.amount.toFixed(6)} ${p.token || result.chain}` : '';
    if (p.isExchange) {
      const nameTag = p.label ? `\n   🏷 取引所名：${p.label}` : '\n   🏷 取引所名：調査中';
      return `🏦 取引所到達（${i}次先）\n   ${addrShort}${nameTag}${timeStr}${amountStr}`;
    }
    const lbl = p.label ? ` [${p.label}]` : '';
    const siblingLines = (p.siblings || []).length > 0
      ? '\n' + p.siblings.map(s => {
          const sa = s.address.slice(0,10)+'...'+s.address.slice(-6);
          const sl = s.label ? ` [${s.label}]` : '';
          const sm = (s.amount != null && s.amount > 0) ? ` ${s.amount.toFixed(4)}${s.token||result.chain}` : '';
          return `   ┣ 同時送金先：${sa}${sl}${sm}`;
        }).join('\n')
      : '';
    return `🔵 中継アドレス（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}${siblingLines}`;
  });

  let exSection = '';
  let tplSection = '';
  if (result.exchanges && result.exchanges.length > 0) {
    const ex = result.exchanges[0];
    const exDisplayName = ex.name && ex.name.trim() ? ex.name : '未登録取引所';
    exSection = `\n🏦 判明した取引所\n━━━━━━━━━━━━━━━━━\n取引所名：${exDisplayName}\nアドレス：${ex.address.slice(0,12)}...${ex.address.slice(-6)}\n着金額　：${(ex.amount != null && !isNaN(ex.amount)) ? ex.amount.toFixed(8) : '不明'} ${result.chain}`;
    tplSection = `\n\n📝 取引所への要請テンプレート\n━━━━━━━━━━━━━━━━━\n【${exDisplayName} サポートチームへ】\n\n件名：不正送金に関する緊急凍結要請\n\n拝啓\n\n不正な仮想通貨送金について緊急のご対応をお願いいたします。\n\n■ トランザクションID\n${result.txid}\n\n■ チェーン：${result.chain}\n■ 送金日時（JST）：${fmtDate(result.blockTime)}\n■ 送金額：${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}\n■ 着金アドレス：${ex.address}\n\n上記は詐欺被害に起因する不正送金の疑いがあります。\n①上記アドレスの凍結措置\n②関連する取引情報の保全\nについて緊急のご対応をお願い申し上げます。\n\n敬具\n━━━━━━━━━━━━━━━━━`;
  } else {
    // 最後のノードのラベルを表示（DEX/ブリッジ等）
    const lastNode = (result.path || []).filter(p => p.role !== 'sender').slice(-1)[0];
    const lastLabel = lastNode?.label ? `\n最終到達先：${lastNode.label}` : '';
    const lastAddr  = lastNode?.address ? `\nアドレス：${lastNode.address.slice(0,12)}...${lastNode.address.slice(-6)}` : '';
    exSection = `\n⚠️ 取引所判定\n━━━━━━━━━━━━━━━━━\n送金先は既知の取引所DBに一致しませんでした。${lastLabel}${lastAddr}\n追加追跡が必要な場合はご連絡ください。`;
  }

  const amountDisplay = (result.tokenSymbol && result.tokenAmount > 0)
    ? `${result.tokenAmount.toFixed(6)} ${result.tokenSymbol}（ERC-20トークン）`
    : `${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}`;
  return `📊 BitTo 調査レポート\n━━━━━━━━━━━━━━━━━\n${em} チェーン：${result.chain}\n🔗 TXID：${txShort}\n📅 送金日時：${fmtDate(result.blockTime)}\n💰 送金額：${amountDisplay}${(result.fee != null && !isNaN(result.fee)) ? `\n⛽ 手数料：${result.fee.toFixed(8)} ${result.chain}` : ''}${result.destTag != null ? `\n🏷 宛先タグ：${result.destTag}` : ''}\n\n📍 送金経路\n━━━━━━━━━━━━━━━━━\n${pathLines.join('\n　↓\n')}\n${exSection}${tplSection}\n\n🔒 BitTo が自動生成したレポートです`;
}

/* ══ 管理用エンドポイントの関門 ═══════════════════════════════
   管理系は誰でも叩ける状態だった。実害は情報の流出ではなく
   「ただ乗り」と「なりすまし送信」で、とくにメール送信の口が開いていると
   第三者に踏み台にされてドメインの評判が落ちる（迷惑メール判定と戦っている最中で
   これは致命的）。ADMIN_TOKEN を1つ置き、合致しなければ触れないようにする。
   未設定なら従来どおり通す（設定漏れで自分が締め出されないため。ログで警告する）。 */
const ADMIN_TOKEN = process.env.ADMIN_TOKEN || '';
if (!ADMIN_TOKEN) {
  console.warn('[Admin] ⚠️ ADMIN_TOKEN が未設定です。管理用エンドポイントが誰でも叩ける状態です');
}
function adminOk(req) {
  if (!ADMIN_TOKEN) return true;
  const t = (req.query && req.query.t) || req.headers['x-admin-token'] || '';
  return String(t) === ADMIN_TOKEN;
}
function requireAdmin(req, res, next) {
  if (adminOk(req)) return next();
  // 存在自体を伏せる。総当たりの的にしない
  res.status(404).send('Not found');
}

// ══ Google Sheets 連携 ════════════════════════════════════════
// スプレッドシートの列構成（A〜J）:
// A:申込日時 B:お名前 C:電話番号 D:メールアドレス E:ご住所
// F:件数 G:合計金額(¥) H:セッションID I:レポートURL J:ステータス

function getSheets() {
  const keyJson = process.env.GOOGLE_SERVICE_ACCOUNT_KEY;
  if (!keyJson || !GOOGLE_SHEET_ID) return null;
  try {
    const credentials = JSON.parse(keyJson);
    const auth = new google.auth.GoogleAuth({
      credentials,
      scopes: ['https://www.googleapis.com/auth/spreadsheets'],
    });
    return google.sheets({ version: 'v4', auth });
  } catch (e) {
    console.error('[Sheets] 認証エラー:', e.message);
    return null;
  }
}

/* ══ ヒアリング（被害時系列パック）の保存先 ══════════════════
   申込用シートとは別のスプレッドシートに貯める。個人情報の密度が高く、
   運用で見る人も違うため、注文台帳と混ぜない。
   HEARING_SHEET_ID が未設定なら申込と同じブックの別タブに書く。
   列は HEARING_FIELDS が唯一の定義。見出し行も同じ配列から作る。 */
const HEARING_SHEET_ID  = process.env.HEARING_SHEET_ID || GOOGLE_SHEET_ID;
const HEARING_SHEET_TAB = process.env.HEARING_SHEET_TAB || 'ヒアリング';
const HEARING_FIELDS = [
  ['submittedAt',  '送信日時',              150],
  ['customerName', 'お名前',                120],
  ['email',        'メールアドレス',        210],
  ['reportUrl',    '報告書URL',             230],
  ['firstTime',    '最初の送金日時',        150],
  ['firstAmount',  '最初の送金数量',        140],
  ['firstChain',   'チェーン',               80],
  ['firstExchange','到達取引所（推定）',    160],
  ['a1',  'A1 名目',                        190],
  ['a2',  'A2 送金先のサイト・アプリ',      230],
  ['a3',  'A3 アドレスの渡され方',          160],
  ['a4',  'A4 送金直前に言われたこと',      280],
  ['b1',  'B1 相手の名乗り',                190],
  ['b2',  'B2 最初の接触経路',              150],
  ['b3',  'B3 連絡手段',                    170],
  ['b4',  'B4 相手のアカウント・電話',      190],
  ['b5',  'B5 やり取りの期間',              180],
  ['c1',  'C1 送金回数',                     95],
  ['c2',  'C2 総額（円）',                  120],
  ['c3',  'C3 送金の手段',                  190],
  ['c4',  'C4 他のTXID',                    230],
  ['c5',  'C5 銀行振込先',                  230],
  ['d1',  'D1 追加請求',                    110],
  ['d2',  'D2 出金を試みたか',              150],
  ['d3',  'D3 相手と連絡が取れるか',        160],
  ['d4',  'D4 サイト・アプリの状況',        170],
  ['e1',  'E1 警察への相談',                130],
  ['e2',  'E2 取引所への申告',              130],
  ['e3',  'E3 回収業者への連絡',            140],
  ['f1',  'F 保全している証拠',             250],
  ['story','経緯（ご本人の記述）',          420],
  ['note','自由記入',                       300],
  ['token','申込トークン',                  260],
];

/* シートは運用者が毎日見る場所なので、届いた時点で読める形にしておく。
   見出し固定・折り返し・列幅・フィルタまで入れる。何度呼んでも同じ状態になる。 */
async function formatHearingTab(sheets, sheetId) {
  const cols = HEARING_FIELDS.length;
  const reqs = [
    { updateSheetProperties: {
        properties: { sheetId, gridProperties: { frozenRowCount: 1 } },
        fields: 'gridProperties.frozenRowCount' } },
    // 見出し行
    { repeatCell: {
        range: { sheetId, startRowIndex: 0, endRowIndex: 1, startColumnIndex: 0, endColumnIndex: cols },
        cell: { userEnteredFormat: {
          backgroundColor: { red: 0.05, green: 0.16, blue: 0.25 },
          horizontalAlignment: 'LEFT', verticalAlignment: 'MIDDLE', wrapStrategy: 'WRAP',
          textFormat: { bold: true, fontSize: 10, foregroundColor: { red: 1, green: 1, blue: 1 } } } },
        fields: 'userEnteredFormat(backgroundColor,horizontalAlignment,verticalAlignment,wrapStrategy,textFormat)' } },
    // 本文：自由記入が長いので折り返して上揃え
    { repeatCell: {
        range: { sheetId, startRowIndex: 1, startColumnIndex: 0, endColumnIndex: cols },
        cell: { userEnteredFormat: { wrapStrategy: 'WRAP', verticalAlignment: 'TOP', textFormat: { fontSize: 10 } } },
        fields: 'userEnteredFormat(wrapStrategy,verticalAlignment,textFormat)' } },
  ];
  HEARING_FIELDS.forEach((f, i) => {
    reqs.push({ updateDimensionProperties: {
      range: { sheetId, dimension: 'COLUMNS', startIndex: i, endIndex: i + 1 },
      properties: { pixelSize: f[2] || 150 }, fields: 'pixelSize' } });
  });
  reqs.push({ setBasicFilter: { filter: { range: { sheetId, startRowIndex: 0, startColumnIndex: 0, endColumnIndex: cols } } } });
  await sheets.spreadsheets.batchUpdate({ spreadsheetId: HEARING_SHEET_ID, requestBody: { requests: reqs } });
}

/* タブが無ければ作る。運用者が手で用意しなくても書き込めるようにするため。
   既にあれば Google 側がエラーを返すので、その時は何もしない。 */
async function ensureHearingTab(sheets) {
  try {
    const meta = await sheets.spreadsheets.get({ spreadsheetId: HEARING_SHEET_ID });
    const found = (meta.data.sheets || []).find(sh => sh.properties && sh.properties.title === HEARING_SHEET_TAB);
    if (found) return true;
    await sheets.spreadsheets.batchUpdate({
      spreadsheetId: HEARING_SHEET_ID,
      requestBody: { requests: [{ addSheet: { properties: { title: HEARING_SHEET_TAB } } }] },
    });
    await sheets.spreadsheets.values.update({
      spreadsheetId: HEARING_SHEET_ID,
      range: `${HEARING_SHEET_TAB}!A1`,
      valueInputOption: 'RAW',
      requestBody: { values: [HEARING_FIELDS.map(f => f[1])] },
    });
    const meta2 = await sheets.spreadsheets.get({ spreadsheetId: HEARING_SHEET_ID });
    const made  = (meta2.data.sheets || []).find(sh => sh.properties && sh.properties.title === HEARING_SHEET_TAB);
    if (made) await formatHearingTab(sheets, made.properties.sheetId).catch(e => console.error('[Sheets] 整形に失敗:', e.message));
    console.log('[Sheets] ヒアリング用タブを作成しました');
    return true;
  } catch (e) {
    console.error('[Sheets] ヒアリングタブの準備に失敗:', e.message);
    return e.message;
  }
}

async function appendHearingToSheet(record) {
  try {
    const sheets = getSheets();
    if (!sheets || !HEARING_SHEET_ID) { console.log('[Sheets] ヒアリング未設定（スキップ）'); return { ok: false, reason: '未設定' }; }
    const tab = await ensureHearingTab(sheets);
    if (tab !== true) return { ok: false, reason: tab };
    const row = HEARING_FIELDS.map(([key]) => {
      const v = record[key];
      if (v == null) return '';
      return Array.isArray(v) ? v.join(' / ') : String(v);
    });
    await sheets.spreadsheets.values.append({
      spreadsheetId: HEARING_SHEET_ID,
      range: `${HEARING_SHEET_TAB}!A:AZ`,
      valueInputOption: 'USER_ENTERED',
      insertDataOption: 'INSERT_ROWS',
      requestBody: { values: [row] },
    });
    console.log('[Sheets] ヒアリングを追記しました');
    return { ok: true };
  } catch (e) {
    console.error('[Sheets] appendHearingToSheet エラー:', e.message);
    return { ok: false, reason: e.message };
  }
}

async function appendToSheet(rowData) {
  try {
    const sheets = getSheets();
    if (!sheets) { console.log('[Sheets] 未設定（スキップ）'); return; }
    await sheets.spreadsheets.values.append({
      spreadsheetId: GOOGLE_SHEET_ID,
      range: 'シート1!A:J',
      valueInputOption: 'USER_ENTERED',
      insertDataOption: 'INSERT_ROWS',
      requestBody: { values: [rowData] },
    });
    console.log('[Sheets] 行追記完了');
  } catch (e) {
    console.error('[Sheets] appendToSheet エラー:', e.message);
  }
}

async function updateSheetReportUrl(sessionId, reportUrl) {
  try {
    const sheets = getSheets();
    if (!sheets) return;
    // H列（セッションID）からマッチする行を検索
    const getRes = await sheets.spreadsheets.values.get({
      spreadsheetId: GOOGLE_SHEET_ID,
      range: 'シート1!H:H',
    });
    const rows = getRes.data.values || [];
    const rowIdx = rows.findIndex(row => row[0] === sessionId);
    if (rowIdx === -1) { console.log('[Sheets] sessionId 未検出:', sessionId); return; }
    const sheetRow = rowIdx + 1; // 1-indexed
    await sheets.spreadsheets.values.batchUpdate({
      spreadsheetId: GOOGLE_SHEET_ID,
      requestBody: {
        valueInputOption: 'USER_ENTERED',
        data: [
          { range: `シート1!I${sheetRow}`, values: [[reportUrl]] },
          { range: `シート1!J${sheetRow}`, values: [['支払い完了']] },
        ],
      },
    });
    console.log('[Sheets] レポートURL更新完了 row:', sheetRow);
  } catch (e) {
    console.error('[Sheets] updateSheetReportUrl エラー:', e.message);
  }
}

// ══ メール送信 ════════════════════════════════════════════════

function getMailer() {
  if (!SMTP_USER || !SMTP_PASS) return null;
  return nodemailer.createTransport({
    host: process.env.SMTP_HOST || 'smtp.gmail.com',
    port: parseInt(process.env.SMTP_PORT) || 587,
    secure: (process.env.SMTP_PORT === '465'), // 465ならSSL、それ以外はSTARTTLS
    auth: { user: SMTP_USER, pass: SMTP_PASS },
    tls: { rejectUnauthorized: false },
    connectionTimeout: 10000, // 10秒で接続を諦める（ハング防止）
    greetingTimeout: 10000,
    socketTimeout: 15000,
  });
}

// Resend（HTTP API）でメール送信。Railwayでもポートブロックを受けない
// 差出人の表示名だけブランド別に切替（アドレス部は MAIL_FROM と共通）。
// brand='bitto' 以外は従来どおり MAIL_FROM（Connection）。
function mailFromFor(brand) {
  if (String(brand || '').toLowerCase() !== 'bitto') return MAIL_FROM;
  const m = MAIL_FROM.match(/<([^>]+)>/);
  return `BitTo <${m ? m[1] : MAIL_FROM}>`;
}

async function sendViaResend(to, subject, html, brand) {
  // テストドメイン（onboarding@resend.dev）では本人以外・BCCに送れないため、
  // 独自ドメイン認証後（MAIL_FROMがresend.dev以外）のみ運営者控えBCCを付ける
  const from = mailFromFor(brand);
  const domainVerified = !/onboarding@resend\.dev/.test(from);
  const bccTarget = SMTP_USER && SMTP_USER !== to ? [SMTP_USER] : undefined;
  const bcc = domainVerified ? bccTarget : undefined;
  const r = await fetch('https://api.resend.com/emails', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${RESEND_API_KEY}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ from, to: [to], bcc, subject, html }),
  });
  const data = await r.json().catch(() => ({}));
  if (!r.ok) throw new Error(`Resend ${r.status}: ${data.message || JSON.stringify(data)}`);
  return data.id;
}

async function sendEmail(to, subject, html, brand) {
  // ① Resend（推奨：HTTP経由でRailway対応）
  if (RESEND_API_KEY) {
    try {
      const id = await sendViaResend(to, subject, html, brand);
      console.log('[Mail] Resend送信完了 → to:', to, '/ id:', id);
      return;
    } catch (e) {
      console.error('[Mail] Resend送信エラー:', e.message);
      // Resend失敗時はSMTPにフォールバック
    }
  }
  // ② SMTP（フォールバック）
  try {
    const mailer = getMailer();
    if (!mailer) { console.log('[Mail] メール未設定（スキップ）'); return; }
    const bcc = SMTP_USER && SMTP_USER !== to ? SMTP_USER : undefined;
    const info = await mailer.sendMail({
      from: `"${String(brand || '').toLowerCase() === 'bitto' ? 'BitTo' : 'Connection'} 調査サービス" <${SMTP_USER}>`,
      to, bcc, subject, html,
    });
    console.log('[Mail] SMTP送信完了 → to:', to, '/ bcc:', bcc || 'なし', '/ messageId:', info.messageId);
  } catch (e) {
    console.error('[Mail] SMTP送信エラー詳細:', e.message);
    console.error('[Mail] エラーコード:', e.code, '/ 応答:', e.response || '');
  }
}

function buildTOSEmailHTML(name, count, amount, submittedAt) {
  return `<!DOCTYPE html>
<html lang="ja">
<head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>ご利用規約同意の確認 — BitTo</title>
<style>
body{margin:0;background:#f4f5f7;font-family:-apple-system,BlinkMacSystemFont,'Hiragino Kaku Gothic Pro','Meiryo',sans-serif;color:#1a1a2e;font-size:14px}
.wrap{max-width:560px;margin:0 auto;padding:24px 16px}
.header{background:#1a1a2e;border-radius:12px;padding:24px 28px;margin-bottom:16px;color:#fff;text-align:center}
.header h1{font-size:1.2rem;margin:0 0 4px}
.header p{color:#94a3b8;font-size:0.83rem;margin:0}
.card{background:#fff;border-radius:12px;border:1px solid #e2e8f0;padding:28px;margin-bottom:16px}
h2{font-size:0.95rem;color:#1a1a2e;margin:0 0 14px;padding-bottom:8px;border-bottom:1px solid #e2e8f0}
table{width:100%;border-collapse:collapse}
th{width:130px;background:#f8fafc;padding:8px 10px;text-align:left;font-size:0.82rem;color:#64748b;border:1px solid #e2e8f0;white-space:nowrap}
td{padding:8px 10px;border:1px solid #e2e8f0;font-size:0.85rem}
.tos-box{background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:14px 16px;font-size:0.79rem;color:#64748b;line-height:1.8;white-space:pre-line;margin-top:10px}
.footer{text-align:center;color:#94a3b8;font-size:0.78rem;line-height:1.7;margin-top:16px}
</style>
</head>
<body>
<div class="wrap">
  <div class="header">
    <h1>🔗 BitTo 詳細調査レポート</h1>
    <p>ご利用規約同意の確認メール</p>
  </div>
  <div class="card">
    <h2>📋 お申し込み内容</h2>
    <table>
      <tr><th>お名前</th><td>${name} 様</td></tr>
      <tr><th>申し込み日時</th><td>${submittedAt}</td></tr>
      <tr><th>調査TXID件数</th><td>${count}件</td></tr>
      <tr><th>お支払い金額</th><td>¥${Number(amount).toLocaleString()}（税込）</td></tr>
    </table>
  </div>
  <div class="card">
    <h2>📄 ご同意いただいた利用規約</h2>
    <div class="tos-box">■ サービス内容
ブロックチェーン公開データを解析し送金先取引所を特定する調査サービスです。
公的機関へ相談する際の資料を作成します。

■ 料金
・送金経路・取引所特定：無料
・詳細調査レポート 1TXID：¥${BITTO_PRICE.toLocaleString()}（税込）
・複数TXIDは件数 × ¥${BITTO_PRICE.toLocaleString()}

■ 返金について
本サービスはデジタル調査コンテンツの提供のため、調査開始後の返金はいたしかねます。
・取引所への凍結・資金回収を保証しません
・調査結果に法的効力はありません
・結果に関わらず返金対応は行いません

■ 免責事項
・全追跡の成功を保証しません
・取引所の対応結果は当社管理外です
・本レポートは被害申告・警察相談の参考資料としてご活用ください

■ 個人情報の取扱い
収集情報は調査業務のみに使用し、第三者への提供はしません。</div>
  </div>
  <div class="footer">
    <p>このメールはお申し込み内容の確認として自動送信されました。</p>
    <p>ご不明な点はLINEにてお問い合わせください。</p>
    <p>© BitTo 詳細調査サービス</p>
  </div>
</div>
</body>
</html>`;
}

function buildReportEmailHTML(name, reportUrl, issuedAt, hearingUrl) {
  return `<!DOCTYPE html>
<html lang="ja">
<head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>詳細調査レポート完成のお知らせ — BitTo</title>
<style>
body{margin:0;background:#f4f5f7;font-family:-apple-system,BlinkMacSystemFont,'Hiragino Kaku Gothic Pro','Meiryo',sans-serif;color:#1a1a2e;font-size:14px}
.wrap{max-width:560px;margin:0 auto;padding:24px 16px}
.header{background:#1a1a2e;border-radius:12px;padding:24px 28px;margin-bottom:16px;color:#fff;text-align:center}
.header h1{font-size:1.2rem;margin:0 0 4px}
.header p{color:#94a3b8;font-size:0.83rem;margin:0}
.card{background:#fff;border-radius:12px;border:1px solid #e2e8f0;padding:28px;margin-bottom:16px}
h2{font-size:0.95rem;color:#1a1a2e;margin:0 0 14px;padding-bottom:8px;border-bottom:1px solid #e2e8f0}
.note{font-size:0.85rem;color:#374151;line-height:1.75}
.btn{display:block;background:#1a73e8;color:#fff;text-align:center;padding:14px 24px;border-radius:10px;font-size:1rem;font-weight:700;text-decoration:none;margin:18px 0}
.url-box{background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:12px 14px;font-size:0.82rem;word-break:break-all;color:#3b82f6}
.footer{text-align:center;color:#94a3b8;font-size:0.78rem;line-height:1.7;margin-top:16px}
</style>
</head>
<body>
<div class="wrap">
  <div class="header">
    <h1>🔗 BitTo 詳細調査レポート</h1>
    <p>レポート完成のお知らせ</p>
  </div>
  <div class="card">
    <h2>✅ 詳細調査レポートが完成しました</h2>
    <p class="note">${name} 様<br><br>
お支払いが確認され、ブロックチェーン詳細調査レポートの生成が完了しました。<br>
発行日時：${issuedAt}<br><br>
下記のボタンからレポートをご確認ください。</p>
    <a class="btn" href="${reportUrl}">📄 レポートを開く</a>
    <p class="note" style="font-size:0.82rem;color:#64748b">またはブラウザで以下のURLを開いてください：</p>
    <div class="url-box">${reportUrl}</div>
    ${hearingUrl ? `<p class="note" style="margin-top:20px">📑 <strong>被害時系列パック（任意・追加費用なし）</strong><br>
被害の経緯をうかがい、調査結果と合わせて時系列の資料にまとめます。警察・取引所へご相談の際にお使いいただけます。</p>
    <a class="btn" style="background:#0f766e" href="${hearingUrl}">📑 経緯を入力して資料を作る</a>
    <div class="url-box">${hearingUrl}</div>` : ''}
    <p class="note" style="margin-top:14px;font-size:0.82rem;color:#64748b">
💡 <strong>PDFとして保存するには</strong><br>
ブラウザの印刷メニュー（Ctrl+P / ⌘P）を開き、「PDFとして保存」を選択してください。</p>
  </div>
  <div class="footer">
    <p>このメールはお支払い確認後に自動送信されました。</p>
    <p>ご不明な点はLINEにてお問い合わせください。</p>
    <p>© BitTo 詳細調査サービス</p>
  </div>
</div>
</body>
</html>`;
}

function buildTxidFormEmailHTML(name, formUrl, count) {
  return `<!DOCTYPE html>
<html lang="ja">
<head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>TXID入力のお願い — BitTo</title>
<style>
body{margin:0;background:#f4f5f7;font-family:-apple-system,BlinkMacSystemFont,'Hiragino Kaku Gothic Pro','Meiryo',sans-serif;color:#1a1a2e;font-size:14px}
.wrap{max-width:560px;margin:0 auto;padding:24px 16px}
.header{background:#1a1a2e;border-radius:12px;padding:24px 28px;margin-bottom:16px;color:#fff;text-align:center}
.header h1{font-size:1.2rem;margin:0 0 4px}.header p{color:#94a3b8;font-size:0.83rem;margin:0}
.card{background:#fff;border-radius:12px;border:1px solid #e2e8f0;padding:28px;margin-bottom:16px}
h2{font-size:0.95rem;color:#1a1a2e;margin:0 0 14px;padding-bottom:8px;border-bottom:1px solid #e2e8f0}
.note{font-size:0.85rem;color:#374151;line-height:1.75}
.btn{display:block;background:#1a73e8;color:#fff;text-align:center;padding:14px 24px;border-radius:10px;font-size:1rem;font-weight:700;text-decoration:none;margin:18px 0}
.url-box{background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:12px 14px;font-size:0.82rem;word-break:break-all;color:#3b82f6}
.warn{background:#fff8e1;border:1px solid #fdd663;border-radius:8px;padding:10px 14px;font-size:0.82rem;color:#78600a;margin-top:12px}
.footer{text-align:center;color:#94a3b8;font-size:0.78rem;line-height:1.7;margin-top:16px}
</style></head>
<body><div class="wrap">
  <div class="header"><h1>🔗 BitTo 詳細調査レポート</h1><p>TXID入力フォームのご案内</p></div>
  <div class="card">
    <h2>📝 調査するTXIDを入力してください</h2>
    <p class="note">${name} 様<br><br>
お支払いが確認されました。<br>
以下のボタンから調査するTXIDを入力してください。<br><br>
入力できる件数：<strong>${count}件</strong></p>
    <a class="btn" href="${formUrl}">🔗 TXID入力フォームを開く</a>
    <p class="note" style="font-size:0.82rem;color:#64748b">またはブラウザで以下のURLを開いてください：</p>
    <div class="url-box">${formUrl}</div>
    <div class="warn">⚠️ このURLは1回のみ使用可能です。入力後は無効になります。</div>
  </div>
  <div class="footer"><p>ご不明な点はLINEにてお問い合わせください。</p><p>© BitTo 詳細調査サービス</p></div>
</div></body></html>`;
}

// ══ Mermaid フロー図生成 ══════════════════════════════════════

function buildMermaidDiagram(path, chain) {
  if (!path || path.length === 0) return 'graph LR\n  A["データなし"]';
  const lines = ['graph LR'];

  path.forEach((node, i) => {
    const id    = `N${i}`;
    const short = node.address.slice(0, 8) + '…' + node.address.slice(-4);
    const lbl   = node.label   ? `<br/>${node.label}` : '';
    const bal   = (node.balance != null && !isNaN(node.balance))
      ? `<br/>${node.isExchange ? '取引所内残高' : '残高'}: ${node.balance < 0.0001 ? node.balance.toFixed(6) : node.balance.toFixed(4)} ${chain}` : '';
    const txc   = node.txCount != null ? `<br/>TX: ${node.txCount.toLocaleString()}件` : '';

    if (i === 0) {
      lines.push(`  ${id}["🔴 被害者<br/>${short}${bal}${txc}"]`);
    } else if (node.isExchange) {
      lines.push(`  ${id}["🟢 ${node.label || '取引所'}<br/>${short}${bal}${txc}"]`);
    } else {
      lines.push(`  ${id}["🔵 中継${i}<br/>${short}${bal}${txc}"]`);
    }

    if (i > 0) {
      const amt = (node.amount != null && !isNaN(node.amount) && node.amount > 0)
        ? `${node.amount.toFixed(4)} ${node.token || chain}` : '→';
      lines.push(`  N${i - 1} -->|"${amt}"| ${id}`);
    }
  });

  // ノードスタイル
  path.forEach((node, i) => {
    const id = `N${i}`;
    if (i === 0)              lines.push(`  style ${id} fill:#fff5f5,stroke:#fca5a5,color:#dc2626`);
    else if (node.isExchange) lines.push(`  style ${id} fill:#f0fdf4,stroke:#86efac,color:#16a34a`);
    else                      lines.push(`  style ${id} fill:#eff6ff,stroke:#93c5fd,color:#2563eb`);
  });

  return lines.join('\n');
}

// ══ 有料HTMLレポート生成 ══════════════════════════════════════

function generateReportHTML(results, customerName, issuedAt, aiData = {}, reportUrl = '', brand = 'bitto', hearingUrl = '') {
  const chainFull = { BTC: 'Bitcoin', ETH: 'Ethereum', XRP: 'XRP Ledger' };

  // ── ブランド出し分け（未指定はBitTo＝従来どおり） ──
  const BRANDS = {
    bitto: {
      pageTitle: 'BitTo 詳細調査レポート',
      coverH1:   '🔗 BitTo 詳細調査レポート',
      coverH1Style: '',
      coverSub:  'ブロックチェーン送金経路・取引所特定 調査報告書',
      footer:    '本レポートは BitTo が自動生成した調査報告書です。参考資料としてご活用ください。',
    },
    connection: {
      pageTitle: 'Connection 正式調査報告書',
      coverH1:   'Connection',
      coverH1Style: "font-family:Georgia,'Times New Roman',serif;letter-spacing:3px;color:#b88a3e;font-weight:600",
      coverSub:  '正式調査報告書｜Blockchain Forensics &amp; Asset Tracing',
      footer:    '本報告書は Connection（Himesen株式会社）が作成した正式調査報告書です。',
    },
  };
  const BR = BRANDS[brand] || BRANDS.bitto;

  // ── ブランド別テーマ（配色・フォント）。報告書のCSSは var(--r-*) を参照する ──
  const THEME = {
    connection: {
      page:'#FBF8F1', ink:'#243349', ink2:'#6b7688', card:'#ffffff', border:'#E4D9C1', line:'#EAE1CE',
      softbg:'#FBF9F3', accent:'#B88A3E', accentink:'#9a7333', badgebg:'#243349', badgeink:'#ffffff',
      coverbg:'#FBF8F1', coverink:'#243349', coversub:'#6b7688', thbg:'#FAF6EC', addrbg:'#FCFAF4', addrink:'#3a4658',
      monoink:'#3a4658', aibg:'#243349', aititle:'#D8B877', aibody:'#D8DEE7', ailabelbg:'#B88A3E', tmplbg:'#FAF7F0',
      vbg:'#FBF5F2', vborder:'#E4B9A9', vink:'#B0553C', rbg:'#F7F3EB', rborder:'#DED0B2', rink:'#8A7A52',
      ebg:'#FBF6E9', eborder:'#D8C39A', eink:'#9A7333', usd:'#8A7A52', printbtnbg:'#243349', printbtnink:'#ffffff',
      openbtnbg:'#B88A3E', font:"Georgia,'Times New Roman','Yu Mincho',serif", mono:"'Courier New',monospace",
      tmplfont:"Georgia,'Times New Roman','Yu Mincho',serif",
    },
    bitto: {
      page:'#0C1728', ink:'#C7D6EC', ink2:'#8FA3C4', card:'#152741', border:'#2C4468', line:'#23385C',
      softbg:'#111F36', accent:'#34E1C8', accentink:'#34E1C8', badgebg:'#34E1C8', badgeink:'#0C1728',
      coverbg:'#0C1728', coverink:'#EAF6F3', coversub:'#5A7099', thbg:'#122038', addrbg:'#0E1C30', addrink:'#9FD9CD',
      monoink:'#9FD9CD', aibg:'#0F2033', aititle:'#34E1C8', aibody:'#B9C9DE', ailabelbg:'#0F6E56', tmplbg:'#122038',
      vbg:'#241826', vborder:'#7A3B3B', vink:'#E8897F', rbg:'#132038', rborder:'#3A557F', rink:'#8FB0E0',
      ebg:'#0F2B28', eborder:'#34E1C8', eink:'#34E1C8', usd:'#5DCAA5', printbtnbg:'#34E1C8', printbtnink:'#062018',
      openbtnbg:'#2F6FE8',
      font:"'Hiragino Sans','Hiragino Kaku Gothic ProN','Noto Sans JP','Noto Sans CJK JP','Yu Gothic UI','Yu Gothic',Meiryo,'Helvetica Neue',Arial,sans-serif",
      mono:"ui-monospace,'SF Mono',Menlo,Consolas,monospace",
      tmplfont:"ui-monospace,'SF Mono',Menlo,Consolas,monospace",
    },
  };
  const TH = THEME[brand] || THEME.bitto;
  const themeCSS = ':root{' + Object.entries(TH).map(([k,v]) => `--r-${k}:${v}`).join(';') + '}';

  const sectionsHTML = results.map((item, idx) => {
    const r  = item.result;
    const em = { BTC: '₿', ETH: 'Ξ', XRP: '✕' }[r.chain] || '🔗';

    // ── Mermaid・価格チャートデータ ──────────────────────
    const mermaidDef  = buildMermaidDiagram(r.path, r.chain);
    const coinId      = { BTC: 'bitcoin', ETH: 'ethereum', XRP: 'ripple' }[r.chain] || 'ethereum';
    const blockTimeMs = (() => {
      try {
        const s = typeof r.blockTime === 'string'
          ? r.blockTime.replace(' ', 'T').replace(/Z+$/, '') + 'Z' : r.blockTime;
        return new Date(s).getTime() || 0;
      } catch { return 0; }
    })();

    // ── フローマップ ──────────────────────────────────────
    const flowNodes = (r.path || []).map((p, i) => {
      let cls, icon, roleLabel;
      if (i === 0)           { cls = 'victim';   icon = '●'; roleLabel = '被害者ウォレット（起点）'; }
      else if (p.isExchange && p.inferred) { cls = 'exchange'; icon = '★'; roleLabel = `🏦 取引所候補（${i}次先・推定）`; }
      else if (p.isExchange) { cls = 'exchange'; icon = '★'; roleLabel = `🏦 取引所到達（${i}次先）`; }
      else if (p.role === 'internal') { cls = 'relay'; icon = '◆'; roleLabel = `内部コール（${i}次先）`; }
      else                   { cls = 'relay';    icon = '◆'; roleLabel = `中継アドレス（${i}次先）`; }

      const inferredBadge = p.inferred ? `<span class="badge" style="background:#d97706">推定</span>` : '';
      const exBadge  = p.label ? `<span class="badge">${p.label}</span>${inferredBadge}` : '';
      const timeTd   = p.time ? `<div class="node-meta">📅 ${fmtDate(p.time)}</div>` : '';
      const amtTd    = (p.amount != null && !isNaN(p.amount) && p.amount > 0)
        ? `<div class="node-meta">💸 送金額: ${p.amount.toFixed(8)} ${p.token || r.chain}</div>` : '';
      const usdStr   = (p.balanceUSD != null && !isNaN(p.balanceUSD))
        ? ` <span class="usd-val">≈ $${p.balanceUSD < 1 ? p.balanceUSD.toFixed(4) : p.balanceUSD.toLocaleString('en-US',{maximumFractionDigits:2})}</span>` : '';
      /* 残高＝そのアドレスに現在入っている総額。最終到達先が取引所の場合は
         取引所ウォレット全体の合算額（他の利用者の資産を含む）なので、
         被害額と読み違えられないよう見出しで区別する。 */
      const balLabel = p.isExchange ? '取引所ウォレット残高' : '残高';
      const balTd    = (p.balance != null && !isNaN(p.balance))
        ? `<div class="node-meta">💰 ${balLabel}: ${p.balance < 0.0001 ? p.balance.toFixed(8) : p.balance.toFixed(4)} ${r.chain}${usdStr}</div>` : '';
      const txCntTd  = (p.txCount != null)
        ? `<div class="node-meta">📊 TX件数: ${p.txCount.toLocaleString()}件</div>` : '';

      return `
        <div class="flow-node ${cls}">
          <div class="node-role"><span class="node-icon">${icon}</span>${roleLabel}${exBadge}</div>
          <div class="node-address">${p.address}</div>
          ${balTd}${txCntTd}${timeTd}${amtTd}
        </div>
        ${i < (r.path || []).length - 1 ? '<div class="flow-arrow">▼</div>' : ''}`;
    }).join('');

    // ── 取引所セクション ──────────────────────────────────
    const lastPathNode = (r.path || []).filter(p => p.role !== 'sender').slice(-1)[0];
    const lastLabelHtml = lastPathNode?.label
      ? `<br><span style="font-size:0.85em;color:#aaa">最終到達先：<strong>${lastPathNode.label}</strong>（${lastPathNode.address?.slice(0,12)}...${lastPathNode.address?.slice(-6)}）</span>`
      : '';
    // 名称未判明だが「取引所ホットウォレットの可能性が高い（推定）」アドレスに到達した場合
    const inferredEx = (r.path || []).filter(p => p.isExchange && p.inferred).slice(-1)[0];
    let exHTML;
    if (inferredEx) {
      exHTML = `
        <div style="background:rgba(201,169,110,.08);border:1px solid rgba(201,169,110,.3);border-radius:8px;padding:14px 16px">
          <p style="margin:0 0 10px"><strong>取引所のホットウォレットの可能性が高いアドレスに到達しました（推定）。</strong></p>
          <table class="info-table">
            <tr><th>到達アドレス</th><td class="mono">${inferredEx.address}</td></tr>
            <tr><th>判定根拠（推定）</th><td>${inferredEx.label || '残高ほぼ0・取引回数が非常に多い（取引所ホットウォレットの典型）'}${inferredEx.txCount != null ? `（TX ${Number(inferredEx.txCount).toLocaleString()}件）` : ''}</td></tr>
          </table>
          <p style="font-size:0.85em;color:#aaa;margin:10px 0 0">※ 取引所名（運営元）は公開情報からは特定できていません。凍結要請を行うには、弁護士・警察を通じた発信者情報開示請求や取引所への照会により運営元を特定する必要があります。本資料はその手続きの証拠資料としてご利用ください。</p>
        </div>`;
    } else {
      exHTML = `<p class="no-ex">送金先は既知の取引所DBに一致しませんでした。${lastLabelHtml}</p>`;
    }
    let tplHTML = '';
    if (r.exchanges && r.exchanges.length > 0) {
      const ex      = r.exchanges[0];
      const contact = getExchangeContact(ex.name);

      exHTML = `
        <table class="info-table">
          <tr><th>取引所名</th><td>${ex.name || '特定済み'}</td></tr>
          <tr><th>着金アドレス</th><td class="mono">${ex.address}</td></tr>
          <tr><th>着金額</th><td>${(ex.amount != null && !isNaN(ex.amount)) ? ex.amount.toFixed(8) : '不明'} ${r.chain}</td></tr>
        </table>
        ${contact ? `
        <h4 style="margin:18px 0 10px">📞 取引所連絡先・対応窓口</h4>
        <table class="info-table">
          <tr><th>公式サイト</th><td><a href="${contact.url}">${contact.url}</a></td></tr>
          ${contact.email ? `<tr><th>サポートメール</th><td>${contact.email}</td></tr>` : ''}
          <tr><th>サポートURL</th><td><a href="${contact.support}">${contact.support}</a></td></tr>
          ${contact.leo ? `<tr><th>法執行機関窓口</th><td><a href="${contact.leo}">${contact.leo}</a></td></tr>` : ''}
          ${contact.note ? `<tr><th>対応メモ</th><td>${contact.note}</td></tr>` : ''}
        </table>` : ''}`;

      tplHTML = `
        <h3>📝 取引所への要請テンプレート</h3>
        <p style="font-size:0.85em;color:#94a3b8;margin:0 0 8px">下記は、上記「申請アドバイス」に沿って取引所へそのまま送付できる要請文です。</p>
        <div class="template-box">【${ex.name || '取引所'} サポートチームへ】

件名：不正送金に関する緊急凍結要請

拝啓

不正な仮想通貨送金について、緊急のご対応をお願いいたします。

■ 依頼者情報
氏名：${customerName}
発行日：${issuedAt}

■ トランザクションID（TXID）
${r.txid}

■ チェーン：${r.chain}（${chainFull[r.chain] || r.chain}）
■ 送金日時（JST）：${fmtDate(r.blockTime)}
■ 送金額：${(r.tokenSymbol && r.tokenAmount > 0) ? `${r.tokenAmount.toFixed(6)} ${r.tokenSymbol}（ERC-20）` : `${(r.amount != null && !isNaN(r.amount)) ? r.amount.toFixed(8) : '不明'} ${r.chain}`}
■ 着金アドレス：${ex.address}

上記は詐欺被害に起因する不正送金の疑いがあります。
以下について緊急のご対応をお願い申し上げます。

① 上記アドレスの即時凍結措置
② 関連する取引情報・KYC情報の保全
③ 当局への情報提供へのご協力

敬具</div>`;

      // AI生成の要請文があれば上書き
      const aiReq = (aiData.requests || [])[idx];
      if (aiReq) {
        tplHTML = `
        <h3>📝 取引所への要請テンプレート</h3>
        <p style="font-size:0.85em;color:#94a3b8;margin:0 0 8px">下記は、上記「申請アドバイス」に沿って取引所へそのまま送付できる要請文です。</p>
        <div class="template-box">${aiReq}</div>`;
      }
    }

    // USDT（Tether発行）の場合：Tether社への凍結要請窓口を併記（Tetherはトークンを凍結可能）
    let tetherHTML = '';
    if (/usdt|tether/i.test(r.tokenSymbol || '')) {
      tetherHTML = `
        <h3>🪙 Tether社（USDT発行体）への凍結要請</h3>
        <div style="background:rgba(5,150,105,.08);border:1px solid rgba(5,150,105,.3);border-radius:8px;padding:14px 16px">
          <p style="margin:0 0 10px">本件は <strong>USDT（Tether社発行）</strong>です。Tether社は自社発行のUSDTトークンを<strong>凍結する権限</strong>を持つため、到達先取引所への要請に加え、<strong>発行体（Tether社）への凍結要請も有効</strong>です。</p>
          <table class="info-table">
            <tr><th>法執行機関向け窓口</th><td><a href="https://tether.to/en/legal/?tab=law-enforcement-requests">https://tether.to/en/legal/?tab=law-enforcement-requests</a></td></tr>
            <tr><th>連絡先メール</th><td>inforequests@tether.to</td></tr>
          </table>
          <p style="font-size:0.85em;color:#94a3b8;margin:10px 0 0">※ 通常、Tether社への要請は警察・弁護士等の法執行機関を通じて行います。本資料を添えてご相談ください。</p>
        </div>`;
    }

    return `
      <section class="tx-section${idx > 0 ? ' page-break' : ''}">
        <div class="tx-header">
          <span class="chain-badge">${em} ${r.chain}</span>
          <span class="tx-num">TXID ${idx + 1}</span>
        </div>

        <h3>基本情報</h3>
        <table class="info-table">
          <tr><th>チェーン</th><td>${r.chain}（${chainFull[r.chain] || r.chain}）</td></tr>
          <tr><th>TXID</th><td class="mono">${r.txid}</td></tr>
          <tr><th>送金日時（JST）</th><td>${fmtDate(r.blockTime)}</td></tr>
          <tr><th>送金額</th><td>${(r.tokenSymbol && r.tokenAmount > 0) ? `${r.tokenAmount.toFixed(6)} ${r.tokenSymbol} <span style="font-size:0.8em;color:#64748b">（ERC-20）</span>` : `${(r.amount != null && !isNaN(r.amount)) ? r.amount.toFixed(8) : '不明'} ${r.chain}`}</td></tr>
          ${(r.fee != null && !isNaN(r.fee)) ? `<tr><th>手数料</th><td>${r.fee.toFixed(8)} ${r.chain}</td></tr>` : ''}
          ${r.destTag != null ? `<tr><th>宛先タグ</th><td>${r.destTag}</td></tr>` : ''}
          ${r.blockHeight ? `<tr><th>ブロック高</th><td>${r.blockHeight}</td></tr>` : ''}
        </table>

        <h3>🔗 送金経路ビジュアルフロー</h3>
        <div class="mermaid-wrap">
          <pre class="mermaid">${mermaidDef}</pre>
        </div>

        <h3>📈 ${r.chain}価格推移（送金前後30日）</h3>
        <div class="chart-wrap">
          <p class="tx-price-label"></p>
          <canvas id="priceChart${idx}" data-coin="${coinId}" data-time="${blockTimeMs}"></canvas>
        </div>

        <h3>📍 送金経路詳細</h3>
        <div class="flow-map">${flowNodes}</div>
        <p class="flow-note">※「残高」は各アドレスに<strong>現在入っている総額</strong>（照会時点）です。最終到達先が取引所の場合、その残高は取引所ウォレット全体の合算額で、他の利用者の資産も含みます。<strong>お客様の被害額そのものではありません。</strong></p>

        <h3>🏦 取引所判定</h3>
        ${exHTML}
        ${tplHTML}
        ${tetherHTML}
      </section>`;
  }).join('');

  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>${BR.pageTitle}</title>
  <style>
    ${themeCSS}
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:var(--r-font);background:var(--r-page);color:var(--r-ink);padding:24px 16px 60px;font-size:14px;-webkit-print-color-adjust:exact;print-color-adjust:exact}
    .container{max-width:760px;margin:0 auto}
    /* カバー */
    .cover{background:var(--r-coverbg);color:var(--r-coverink);border:1px solid var(--r-border);border-radius:12px;padding:32px;margin-bottom:24px;display:flex;justify-content:space-between;align-items:flex-start;gap:16px}
    .cover-left h1{font-size:1.5rem;margin-bottom:4px}
    .cover-left p{color:var(--r-coversub);font-size:0.85rem}
    .cover-meta{text-align:right;font-size:0.82rem;color:var(--r-coversub);line-height:1.8}
    .cover-meta strong{color:var(--r-coverink);display:block}
    /* セクション */
    .tx-section{background:var(--r-card);border:1px solid var(--r-border);border-radius:10px;padding:24px;margin-bottom:20px}
    .tx-header{display:flex;align-items:center;gap:10px;margin-bottom:16px;padding-bottom:12px;border-bottom:2px solid var(--r-border)}
    .chain-badge{background:var(--r-badgebg);color:var(--r-badgeink);padding:4px 12px;border-radius:20px;font-weight:700;font-size:0.9rem}
    .tx-num{color:var(--r-ink2);font-size:0.85rem}
    h3{font-size:0.95rem;color:var(--r-ink);margin:20px 0 10px;padding-left:8px;border-left:3px solid var(--r-accent)}
    h4{font-size:0.88rem;color:var(--r-ink)}
    /* テーブル */
    .info-table{width:100%;border-collapse:collapse;margin-bottom:8px}
    .info-table th{width:140px;background:var(--r-thbg);padding:8px 10px;text-align:left;font-size:0.82rem;color:var(--r-ink2);border:1px solid var(--r-border);white-space:nowrap}
    .info-table td{padding:8px 10px;border:1px solid var(--r-border);font-size:0.85rem;word-break:break-all}
    .info-table a{color:var(--r-accentink);text-decoration:none}
    .mono{font-family:var(--r-mono);font-size:0.78rem;color:var(--r-monoink);word-break:break-all}
    /* フローマップ */
    .flow-map{display:flex;flex-direction:column;align-items:center;gap:0;margin:12px 0}
    .flow-node{width:100%;border-radius:10px;padding:14px 16px;border:2px solid}
    .flow-node.victim  {background:var(--r-vbg);border-color:var(--r-vborder)}
    .flow-node.relay   {background:var(--r-rbg);border-color:var(--r-rborder)}
    .flow-node.exchange{background:var(--r-ebg);border-color:var(--r-eborder)}
    .node-role{font-weight:700;font-size:0.85rem;margin-bottom:6px;display:flex;align-items:center;gap:6px}
    .node-icon{font-size:0.75rem}
    .flow-node.victim   .node-role{color:var(--r-vink)}
    .flow-node.relay    .node-role{color:var(--r-rink)}
    .flow-node.exchange .node-role{color:var(--r-eink)}
    .node-address{font-family:var(--r-mono);font-size:0.77rem;color:var(--r-addrink);word-break:break-all;background:var(--r-addrbg);border:1px solid var(--r-border);border-radius:6px;padding:6px 8px;margin-bottom:4px}
    .node-meta{font-size:0.78rem;color:var(--r-ink2);margin-top:3px}
    .usd-val{color:var(--r-usd);font-size:0.76rem;font-weight:600}
    .badge{background:var(--r-badgebg);color:var(--r-badgeink);font-size:0.72rem;padding:2px 8px;border-radius:10px;margin-left:6px;font-weight:400}
    .flow-arrow{font-size:1.4rem;color:var(--r-ink2);margin:4px 0;line-height:1}
    .no-ex{color:var(--r-ink2);font-size:0.85rem;padding:10px}
    .flow-note{color:var(--r-ink2);font-size:0.78rem;line-height:1.7;margin-top:10px}
    /* 要請テンプレート */
    .template-box{font-family:var(--r-tmplfont);background:var(--r-tmplbg);border:1px solid var(--r-border);border-radius:8px;padding:16px;font-size:0.82rem;white-space:pre-wrap;line-height:1.8;word-break:break-all;margin-top:10px;color:var(--r-ink)}
    /* 印刷ボタン */
    .print-bar{background:var(--r-card);border:1px solid var(--r-border);border-radius:10px;padding:16px 20px;margin-bottom:20px}
    .print-bar p{font-size:0.83rem;color:var(--r-ink2);margin:0 0 10px}
    .print-btn{background:var(--r-printbtnbg);color:var(--r-printbtnink);border:none;border-radius:8px;padding:10px 20px;font-size:0.9rem;font-weight:700;cursor:pointer;margin-right:8px}
    .print-btn:hover{opacity:0.85}
    .open-btn{background:var(--r-openbtnbg);color:#fff;border:none;border-radius:8px;padding:10px 16px;font-size:0.85rem;font-weight:700;cursor:pointer}
    .open-btn:hover{opacity:0.85}
    .print-hint{font-size:0.75rem;color:var(--r-ink2);margin-top:8px;display:none}
    @media(max-width:640px){.print-hint{display:block}}
    .mobile-open-section{display:none;margin-top:14px;padding-top:14px;border-top:2px dashed var(--r-border)}
    @media(max-width:640px){.mobile-open-section{display:block}}
    .qr-wrap{display:flex;gap:16px;align-items:flex-start;margin-bottom:14px}
    .qr-img{width:130px;height:130px;border:2px solid var(--r-border);border-radius:8px;flex-shrink:0;background:#fff}
    .qr-steps{margin:0;padding-left:18px;font-size:0.82rem;color:var(--r-ink);line-height:2}
    .qr-steps li{margin-bottom:2px}
    .qr-steps strong{color:var(--r-ink)}
    .url-box{display:flex;gap:6px;align-items:center;margin-top:8px}
    .url-input{flex:1;border:1px solid var(--r-border);border-radius:8px;padding:9px 10px;font-size:0.72rem;color:var(--r-ink2);background:var(--r-thbg);word-break:break-all;-webkit-user-select:all;user-select:all;outline:none}
    .copy-btn{background:var(--r-ink2);color:var(--r-card);border:none;border-radius:8px;padding:10px 14px;font-size:0.82rem;font-weight:700;cursor:pointer;white-space:nowrap}
    .copy-hint{font-size:0.72rem;color:var(--r-ink2);margin-top:6px;line-height:1.6}
    /* AI分析セクション */
    .ai-overall{background:var(--r-aibg);border:1px solid var(--r-border);border-radius:10px;padding:22px 24px;margin-bottom:20px;color:var(--r-aibody)}
    .ai-header{display:flex;align-items:center;gap:10px;margin-bottom:14px}
    .ai-title{font-size:1rem;font-weight:700;color:var(--r-aititle)}
    .ai-label{display:inline-flex;align-items:center;background:var(--r-ailabelbg);color:#fff;font-size:0.7rem;font-weight:700;padding:3px 10px;border-radius:12px}
    .ai-body{font-size:0.85rem;line-height:1.9;color:var(--r-aibody);white-space:pre-wrap;word-break:break-word}
    .ai-req-badge{background:var(--r-ailabelbg);color:#fff;font-size:0.68rem;padding:2px 8px;border-radius:10px;margin-left:8px;font-weight:700;vertical-align:middle}
    /* Mermaid フロー図 */
    .mermaid-wrap{background:var(--r-softbg);border:1px solid var(--r-border);border-radius:8px;padding:16px;margin-bottom:8px;overflow-x:auto;text-align:center}
    .mermaid-wrap pre{display:inline-block;text-align:left}
    /* 価格チャート */
    .chart-wrap{background:var(--r-card);border:1px solid var(--r-border);border-radius:8px;padding:16px;margin-bottom:8px}
    .tx-price-label{font-size:0.82rem;color:var(--r-accentink);font-weight:600;margin-bottom:8px;text-align:right}
    .chart-error{color:var(--r-ink2);font-size:0.82rem;text-align:center;padding:20px 0}
    .page-break{page-break-before:always}
    /* ── スマホ対応 ── */
    @media (max-width:640px){
      body{padding:8px 6px 40px;font-size:13px}
      .container{max-width:100%}
      .cover{flex-direction:column;gap:10px;padding:18px 14px}
      .cover-left h1{font-size:1.1rem}
      .cover-left p{font-size:0.78rem}
      .cover-meta{text-align:left;font-size:0.78rem}
      .print-bar{flex-direction:column;gap:8px;text-align:center;padding:12px 14px}
      .print-bar p{font-size:0.78rem}
      .print-btn{width:100%;padding:10px}
      .tx-section{padding:14px 10px}
      .tx-header{flex-wrap:wrap;gap:6px}
      .chain-badge{font-size:0.82rem;padding:3px 10px}
      h3{font-size:0.88rem;margin:14px 0 8px}
      h4{font-size:0.82rem}
      .info-table th{width:78px;font-size:0.73rem;padding:6px 7px;white-space:normal;word-break:keep-all}
      .info-table td{font-size:0.78rem;padding:6px 7px;word-break:break-all}
      .mono{font-size:0.68rem}
      .node-address{font-size:0.63rem;padding:5px 6px}
      .node-role{font-size:0.8rem}
      .node-meta{font-size:0.73rem}
      .badge{font-size:0.67rem;padding:2px 6px}
      .mermaid-wrap{padding:10px 8px;overflow-x:auto}
      .chart-wrap{padding:10px 8px}
      .template-box{font-size:0.75rem;padding:12px 10px}
      .ai-overall{padding:16px 14px}
      .ai-title{font-size:0.9rem}
      .ai-body{font-size:0.8rem}
      .flow-node{padding:10px 10px}
    }
    @media print{
      body{background:var(--r-page);padding:0}
      .print-bar{display:none}
      .tx-section{border:none;padding:0;margin-bottom:40px}
      .cover{border-radius:0}
    }
  </style>
</head>
<body>
<div class="container">
  ${hearingUrl ? `<div class="print-bar" style="border-color:var(--r-accent)">
    <p style="margin:0 0 10px"><strong style="color:var(--r-accent)">📑 被害時系列パック（任意・追加費用はかかりません）</strong><br>
    被害の経緯をうかがい、この調査結果と合わせて時系列の資料にまとめます。警察・取引所へご相談の際にお使いいただけます。</p>
    <a class="print-btn" href="${hearingUrl}" style="display:block;text-decoration:none;text-align:center">経緯を入力して資料を作る</a>
  </div>` : ''}
  <div class="print-bar">
    <!-- PDFはサーバー側で作ってあるので、端末やブラウザを問わず1タップで保存できる。
         印刷経由（下）は、Chrome(iOS)では機能せずAndroidのアプリ内ブラウザからも
         届かないため、こちらを主導線にする。 -->
    <a class="print-btn" id="pdfDlBtn" href="__REPORT_URL__.pdf"
       style="display:block;text-decoration:none;text-align:center">📄 PDFをダウンロード</a>
    <p style="margin:10px 0 0;font-size:0.78rem;color:var(--r-ink2)">
      うまく保存できない場合は、下の「印刷」からもPDF化できます</p>
    <details style="margin-top:14px">
      <summary style="cursor:pointer;font-size:0.82rem;color:var(--r-ink2)">🖨 印刷して保存する場合はこちら</summary>
    <button class="print-btn" onclick="doPrint()" id="pdfBtn" style="margin-top:10px">🖨 PDF保存 / 印刷</button>
    <div id="chromeGuide" style="display:none;margin-top:12px;background:#fff7ed;border:1px solid #fdba74;border-radius:8px;padding:14px;font-size:0.82rem;color:#334155;line-height:1.9">
      <p style="font-weight:700;margin:0 0 6px;color:#c2410c">📌 Chrome(iOS)でのPDF保存手順</p>
      <ol style="margin:0;padding-left:18px">
        <li>画面下部の <strong>共有ボタン（↑）</strong> をタップ</li>
        <li>下にスクロールして <strong>「印刷」</strong> を選択</li>
        <li>印刷プレビュー画面で <strong>2本指でピンチアウト</strong>（拡大）</li>
        <li>左上の <strong>「PDFとして保存」</strong> をタップ</li>
      </ol>
      <p style="margin:8px 0 0;color:#64748b;font-size:0.75rem">💡 QRコードでSafariから開くと、ボタン1つで保存できます</p>
    </div>
    <p class="print-hint">⚠️ アプリ内で開いている場合、PDF保存できないことがあります</p>
    <div class="mobile-open-section">
      <p style="font-size:0.83rem;font-weight:700;color:var(--r-ink);margin:0 0 10px">📸 QRコードを読み取ってブラウザで開く</p>
      <div class="qr-wrap">
        <img class="qr-img" src="https://api.qrserver.com/v1/create-qr-code/?size=260x260&data=__REPORT_URL__" alt="QRコード" />
        <ol class="qr-steps">
          <li><strong>カメラアプリ</strong>を開く</li>
          <li>QRコードに<strong>かざす</strong></li>
          <li>通知をタップして<strong>ブラウザで開く</strong></li>
          <li>上の<strong>「PDF保存 / 印刷」</strong>を押す</li>
          <li>「<strong>PDFとして保存</strong>」を選択</li>
        </ol>
      </div>
      <p style="font-size:0.78rem;color:var(--r-ink2);margin:4px 0 8px">▼ QRが読めない場合はURLをコピーしてブラウザに貼り付け</p>
      <div class="url-box">
        <input type="text" id="urlInput" class="url-input" readonly value="__REPORT_URL__" onclick="selectUrl(this)" />
        <button class="copy-btn" id="copyBtn" onclick="copyUrl()">📋 コピー</button>
      </div>
      <p class="copy-hint">コピー後、ブラウザのURLバーに貼り付けてください</p>
    </div>
    </details>
  </div>
  <script>
    var _url = '__REPORT_URL__';
    function doPrint(){
      var isChromeIOS = /CriOS/.test(navigator.userAgent);
      if(isChromeIOS){
        var g = document.getElementById('chromeGuide');
        var b = document.getElementById('pdfBtn');
        g.style.display = 'block';
        b.textContent = '📌 手順を確認してください';
        b.style.background = '#ea580c';
      } else {
        window.print();
      }
    }
    function selectUrl(inp){
      inp.removeAttribute('readonly'); inp.focus(); inp.select(); inp.setSelectionRange(0,99999); inp.setAttribute('readonly','');
    }
    function copyUrl(){
      var inp=document.getElementById('urlInput'); var btn=document.getElementById('copyBtn');
      inp.removeAttribute('readonly'); inp.focus(); inp.select(); inp.setSelectionRange(0,99999);
      var ok=false; try{ ok=document.execCommand('copy'); }catch(e){}
      inp.setAttribute('readonly','');
      if(ok){ btn.textContent='✅ コピー済み'; btn.style.background='#16a34a'; setTimeout(function(){btn.textContent='📋 コピー';btn.style.background='';},3000); return; }
      if(navigator.clipboard){ navigator.clipboard.writeText(_url).then(function(){ btn.textContent='✅ コピー済み'; btn.style.background='#16a34a'; setTimeout(function(){btn.textContent='📋 コピー';btn.style.background='';},3000); }).catch(function(){ prompt('URLをコピーしてください：',_url); }); return; }
      prompt('URLをコピーしてください：',_url);
    }
  </script>

  <div class="cover">
    <div class="cover-left">
      <h1${BR.coverH1Style ? ` style="${BR.coverH1Style}"` : ''}>${BR.coverH1}</h1>
      <p>${BR.coverSub}</p>
    </div>
    <div class="cover-meta">
      <strong>依頼者</strong>${customerName}
      <strong>発行日時</strong>${issuedAt}
      <strong>調査件数</strong>${results.length}件
    </div>
  </div>

  ${aiData.analysis ? `
  <div class="ai-overall">
    <div class="ai-header">
      <span class="ai-title">🔎 総合調査分析レポート</span>
    </div>
    <div class="ai-body">${aiData.analysis}</div>
  </div>` : ''}

  ${sectionsHTML}

  <p style="text-align:center;color:#94a3b8;font-size:0.78rem;margin-top:20px">
    ${BR.footer}
  </p>
</div>

<!-- Mermaid.js -->
<script type="module">
  import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs';
  mermaid.initialize({
    startOnLoad: true, theme: 'base',
    themeVariables: { fontSize: '13px', fontFamily: "${TH.font}" }
  });
</script>

<!-- Chart.js + 価格チャート描画 -->
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<script>
(async () => {
  for (const canvas of document.querySelectorAll('canvas[data-coin]')) {
    const coinId = canvas.dataset.coin;
    const txTime = parseInt(canvas.dataset.time);
    if (!txTime) { canvas.parentElement.innerHTML = '<p class="chart-error">送金日時データなし</p>'; continue; }
    const from = Math.floor(txTime / 1000) - 30 * 86400;
    const to   = Math.min(Math.floor(txTime / 1000) + 30 * 86400, Math.floor(Date.now() / 1000));

    /* CoinGeckoの無料APIは直近365日しか返さない（error_code 10012）。
       1年より前の送金でもグラフを出せるよう、Bitstampの日足に切り替える。
       どちらもブラウザから直接呼べる（CORS許可・APIキー不要）ので、
       サーバー側のPDF生成でも同じ経路で描画される。 */
    const PAIRS = { bitcoin: 'btcusd', ethereum: 'ethusd', ripple: 'xrpusd' };
    const loadPrices = async () => {
      try {
        const res = await fetch(
          'https://api.coingecko.com/api/v3/coins/' + coinId +
          '/market_chart/range?vs_currency=usd&from=' + from + '&to=' + to
        );
        const d = await res.json();
        if (d.prices && d.prices.length) return { points: d.prices, source: 'CoinGecko' };
      } catch (e) { /* Bitstampを試す */ }
      const pair = PAIRS[coinId];
      if (!pair) return null;
      const res2 = await fetch(
        'https://www.bitstamp.net/api/v2/ohlc/' + pair + '/?step=86400&limit=61&start=' + from
      );
      const d2 = await res2.json();
      const ohlc = (d2 && d2.data && d2.data.ohlc) || [];
      const points = ohlc
        .filter(o => Number(o.timestamp) <= to)
        .map(o => [Number(o.timestamp) * 1000, Number(o.close)]);
      return points.length ? { points, source: 'Bitstamp' } : null;
    };

    try {
      const loaded = await loadPrices();
      if (!loaded) throw new Error('データなし');
      const prices = loaded.points;

      const labels = prices.map(([ts]) => {
        const dt = new Date(ts);
        return (dt.getMonth() + 1) + '/' + dt.getDate();
      });
      const values = prices.map(([, p]) => p);

      // 送金時に最も近いインデックス
      let txIdx = prices.findIndex(([ts]) => ts >= txTime);
      if (txIdx < 0) txIdx = values.length - 1;
      const txPrice = values[txIdx];

      // 送金時価格をラベル表示
      const lbl = canvas.parentElement.querySelector('.tx-price-label');
      if (lbl && txPrice) {
        lbl.textContent = '● 送金時価格: $' + txPrice.toLocaleString('en-US', { maximumFractionDigits: 2 })
          + '（価格データ：' + loaded.source + '）';
      }

      new Chart(canvas, {
        type: 'line',
        data: {
          labels,
          datasets: [
            {
              label: coinId.toUpperCase() + ' (USD)',
              data: values,
              borderColor: '#3b82f6',
              backgroundColor: 'rgba(59,130,246,0.07)',
              borderWidth: 1.5,
              pointRadius: 0,
              tension: 0.3,
              fill: true,
            },
            {
              label: '送金時 $' + (txPrice ? txPrice.toLocaleString('en-US', { maximumFractionDigits: 2 }) : ''),
              data: values.map((v, i) => i === txIdx ? v : null),
              borderColor: 'transparent',
              pointBackgroundColor: '#dc2626',
              pointBorderColor: '#fff',
              pointBorderWidth: 2,
              pointRadius: 8,
              showLine: false,
            }
          ]
        },
        options: {
          responsive: true,
          // アニメーションはrequestAnimationFrameで進むため、描画が走り切る前に
          // 止まるとグラフが空のまま残る（実測で1画素も描かれていなかった）。
          // 報告書は印刷してPDF化する前提でもあり、アニメーション中に印刷されると
          // PDFも空になる。falseにすると生成と同時に同期で描画される。
          animation: false,
          plugins: {
            legend: { position: 'top', labels: { font: { size: 11 }, boxWidth: 12 } }
          },
          scales: {
            x: {
              ticks: { maxTicksLimit: 8, font: { size: 10 }, color: '#64748b' },
              grid: { display: false }
            },
            y: {
              ticks: {
                callback: v => '$' + v.toLocaleString('en-US', { maximumFractionDigits: 0 }),
                font: { size: 10 }, color: '#64748b'
              },
              grid: { color: '#f1f5f9' }
            }
          }
        }
      });
    } catch (e) {
      canvas.parentElement.innerHTML = '<p class="chart-error">価格データを取得できませんでした。時間をおいて再読み込みしてください。</p>';
    }
  }
})();
</script>
</body>
</html>`.replace(/__REPORT_URL__/g, reportUrl);
}

// ══ Gemini AI コンテンツ生成 ══════════════════════════════════

// AI生成に失敗すると、報告書から「総合調査分析レポート」と「凍結要請状」が
// 黙って欠落したまま有料顧客に届く。無言で劣化させないため運営に通知する。
async function notifyAIFailure(customerName, reason) {
  console.error(`[AI] ❌ 報告書のAI生成に失敗（AI分析・凍結要請状が欠落します）依頼者:${customerName} 理由:${reason}`);
  if (!SMTP_USER) return;
  await sendEmail(SMTP_USER, '【要対応】報告書のAI生成に失敗しました',
    `<p>依頼者：${customerName} 様</p>
     <p>理由：${reason}</p>
     <p><b>この報告書には「総合調査分析レポート」と「凍結要請状」が含まれていません。</b>
     内容を確認し、必要なら再生成のうえ改めてご案内してください。</p>
     <p>Geminiの無料枠を使い切っている場合は、APIキーの課金を有効化してください。</p>`
  ).catch(e => console.error('[AI] 失敗通知メールの送信に失敗:', e.message));
}

async function generateAIContent(results, customerName, opts = {}) {
  const notify = opts.notify !== false;
  const failed = async (reason) => {
    if (notify) await notifyAIFailure(customerName, reason);
    else console.error('[AI] Gemini生成失敗:', reason);
    return { analysis: null, requests: [], aiFailed: true };
  };
  if (!GEMINI_KEY) return failed('GEMINI_API_KEY が未設定');
  try {
    // 調査データをテキスト化
    const txData = results.map((item, idx) => {
      const r = item.result;
      const pathInfo = (r.path || []).map((p, i) => {
        const role = i === 0 ? '起点（被害者）' : p.isExchange ? (p.inferred ? '取引所?(推定)' : '★取引所到達') : `中継${i}`;
        const bal  = p.balance  != null ? `残高:${p.balance.toFixed(4)}${r.chain}` : '';
        const txc  = p.txCount  != null ? `TX:${p.txCount}件` : '';
        return `  [${role}] ${p.address}${p.label ? '('+p.label+')':''} ${bal} ${txc}`;
      }).join('\n');
      return `【TXID ${idx+1}】チェーン:${r.chain} 金額:${r.amount?.toFixed(6)||'?'}${r.chain} 日時:${r.blockTime}\n最終到達:${r.exchanges?.[0]?.name||'不明'} 着金アドレス:${r.exchanges?.[0]?.address||'不明'}\n送金経路:\n${pathInfo}`;
    }).join('\n---\n');

    // 取引所ごとの要請文プロンプト
    const requestBlocks = results.map((item, idx) => {
      const r  = item.result;
      const ex = r.exchanges?.[0];
      if (!ex || !ex.name) return '';   // 名称未判明は凍結要請状を生成しない（証拠資料で対応）
      return `[REQUEST_${idx}]（${ex.name}宛。依頼者:${customerName} TXID:${r.txid} チェーン:${r.chain} 日時:${r.blockTime} 金額:${r.amount?.toFixed(6)||'?'}${r.chain} 着金アドレス:${ex.address||'不明'} 送金経路の説明 凍結・保全・情報提供の3点を要請 取引所固有の申請窓口を明記した凍結要請メール全文）[/REQUEST_${idx}]`;
    }).filter(Boolean).join('\n');

    const prompt = `あなたはブロックチェーン調査の専門家です。仮想通貨詐欺被害の調査結果を分析し、被害者（${customerName}様）への報告書を作成してください。

${txData}

以下の形式で日本語で出力してください（区切りタグを正確に守ること）：

[ANALYSIS]
【結論】
（送金フロー全体の分析、2〜3文）

■ 特記事項①：（見出し）
（アドレスのTX件数・残高から使い捨てウォレット等を指摘）

■ 特記事項②：（見出し）
（送金時間・パターンから計画性等を分析）

■ 取引所への申請アドバイス
（特定取引所名と具体的な申請窓口・手順を記載）
[/ANALYSIS]

${requestBlocks}

分析ポイント：TX件数10件以下→専用ウォレット疑い、残高ほぼゼロ→使い捨て、短時間転送→計画的犯行、取引所ごとの窓口（法執行機関ポータル/メール/チケット）を明記

残高の扱い：上記の「残高」は各アドレスに現在入っている総額です。最終到達先が取引所の場合、その残高は取引所ウォレット全体の合算額で他の利用者の資産も含みます。被害者の資金が残っている額ではないため、残高を根拠に回収可能性や返金額を示唆しないでください。`;

    // 一時的なレート超過（RPM）は待てば通るので3回まで再試行する
    let lastErr = '不明';
    for (let attempt = 1; attempt <= 3; attempt++) {
      try {
        const text = await geminiGenerate(prompt, { temperature: 0.3, maxOutputTokens: 2500 });
        if (!text) throw new Error('Geminiが応答しませんでした（詳細は [Gemini] ログを参照）');

        const aMatch   = text.match(/\[ANALYSIS\]([\s\S]*?)\[\/ANALYSIS\]/);
        const analysis = aMatch ? aMatch[1].trim() : null;
        if (!analysis) throw new Error('ANALYSISタグが返らなかった');

        const requests = results.map((_, idx) => {
          const m = text.match(new RegExp(`\\[REQUEST_${idx}\\]([\\s\\S]*?)\\[/REQUEST_${idx}\\]`));
          return m ? m[1].trim() : null;
        });

        console.log('[AI] Gemini分析完了 analysis: true requests:', requests.map(r => !!r));
        return { analysis, requests, aiFailed: false };
      } catch (e) {
        lastErr = e.message;
        console.warn(`[AI] 生成失敗 (${attempt}/3): ${lastErr}`);
        if (attempt < 3) await new Promise(r => setTimeout(r, attempt * 5000));
      }
    }
    return failed(lastErr);
  } catch (e) {
    return failed(e.message);
  }
}

// 調査後に送るサービス案内メッセージ（調査結果に応じて文面を切り替え）
function buildServiceMsg(applyUrl, result = null) {
  const hasExchange = result?.exchanges?.length > 0;
  const exName      = result?.exchanges?.[0]?.name;
  const amountStr   = (result?.amount != null && !isNaN(result.amount) && result.amount > 0)
    ? `💰 被害額：${result.amount.toFixed(6)} ${result?.chain || ''}\n` : '';

  if (hasExchange) {
    // 取引所が特定できた場合 → 凍結要請の緊急性を強調
    const nameTag = exName ? `【${exName}】への着金が確認されました\n` : '';
    return `🏦 取引所が特定されました！
━━━━━━━━━━━━━━━━━
${nameTag}${amountStr}
詳細調査レポートでは
✅ 取引所への正式な凍結要請状
✅ KYC照会・警察への相談用の調査報告書
✅ AI による総合分析・証拠資料
✅ 複数TXIDもまとめて対応可能

早急な調査で被害回復に向けての
進展を目指してください！

📋 1件 ¥${BITTO_PRICE.toLocaleString()}（税込）
🔗 ${applyUrl}`;
  } else {
    // 取引所が見つからなかった場合 → さらなる追跡を訴求
    return `🔍 詳細調査で取引所を特定できる
可能性があります
━━━━━━━━━━━━━━━━━
${amountStr}
詳細調査レポートでは
✅ AIによるさらに深い追跡・分析
✅ DEX・ブリッジ経由の資金追跡
✅ 取引所特定後の凍結要請テンプレート
✅ 警察・弁護士への相談用の調査報告書

早急な調査で被害回復に向けての
進展を目指してください！

📋 1件 ¥${BITTO_PRICE.toLocaleString()}（税込）
🔗 ${applyUrl}`;
  }
}

// ══ 調査バックグラウンド実行 ══════════════════════════════════

async function runInvestigation(userId, txid, chain) {
  const session  = getSession(userId);
  const cacheKey = txid.toLowerCase();

  try {
    let result = txidCache.get(cacheKey)?.result;
    if (result) {
      console.log(`[CACHE] キャッシュ利用: ${txid}`);
    } else {
      result = await investigate(txid, chain);
      txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
    }

    // 調査結果をリストに追加（重複除外）
    if (!session.investigatedList) session.investigatedList = [];
    const alreadyIn = session.investigatedList.some(r => r.txid.toLowerCase() === txid.toLowerCase());
    if (!alreadyIn) session.investigatedList.push({ txid, chain, result });

    // 無料調査レポートを送信
    await lineClient.pushMessage(userId, { type: 'text', text: buildReport(result) });

    // サービス案内＋フォームURL（調査結果に応じて文面切り替え）
    const applyUrl = `${BASE_URL}/apply?uid=${encodeURIComponent(userId)}`;
    await lineClient.pushMessage(userId, { type: 'text', text: buildServiceMsg(applyUrl, result) });

    session.state = 'done';

  } catch (e) {
    console.error('[調査エラー]', e.message);
    session.state = 'waiting_txid';
    await lineClient.pushMessage(userId, {
      type: 'text',
      text: `⚠️ 調査中にエラーが発生しました\n\n${e.message}\n\nTXIDをご確認の上、再度送ってください`,
    });
  }
}

// ══ LINE 会話フロー ══════════════════════════════════════════

const HELP_TEXT = `📋 BitTo 使い方ガイド
━━━━━━━━━━━━━━━━━
詐欺被害に遭われた場合、TXIDを
もとに送金先取引所を自動追跡します

💬 ご利用方法
TXIDをそのまま送信してください

対応チェーン：
₿ Bitcoin (BTC)
Ξ Ethereum (ETH)
✕ XRP Ledger (XRP)

💴 料金
・送金経路・取引所特定：無料
・詳細レポート：¥${BITTO_PRICE.toLocaleString()}（税込）/ 件

「リセット」で最初からやり直し`;

async function handleLineEvent(event) {
  if (event.type !== 'message' || event.message.type !== 'text') return;

  const userId  = event.source.userId;
  const text    = event.message.text.trim();
  const session = getSession(userId);

  // ── グローバルコマンド ──────────────────────────────────
  if (['ヘルプ', 'help', '？', '?'].includes(text.toLowerCase())) {
    return lineClient.replyMessage(event.replyToken, { type: 'text', text: HELP_TEXT });
  }
  if (['リセット', 'reset', 'やり直し', 'やりなおし'].includes(text.toLowerCase())) {
    resetSession(userId);
    return lineClient.replyMessage(event.replyToken, {
      type: 'text',
      text: `🔄 リセットしました\n\nTXIDをお送りください\n対応：BTC / ETH / XRP`,
    });
  }

  const chain = detectChain(text);

  switch (session.state) {

    // ── 最初のメッセージ ──────────────────────────────────
    case 'idle': {
      session.state = 'waiting_txid';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `先ずは無料調査を開始しますので\nTXIDを1件ずつお送りください\n\n※ TXIDの取得方法はLINEプロフィールを\n　ご参照ください\n\n対応：BTC / ETH / XRP`,
      });
    }

    // ── TXID 待ち ─────────────────────────────────────────
    case 'waiting_txid': {
      if (!chain) {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `TXIDを認識できませんでした\n\nBTC / ETH / XRP のTXIDをお送りください\n（例：ETH は 0x から始まる66文字）`,
        });
      }
      session.txid  = text;
      session.chain = chain;
      session.state = 'investigating';

      const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger' }[chain];
      const txShort   = text.slice(0, 10) + '...' + text.slice(-6);
      const cached    = txidCache.get(text.toLowerCase());
      const waitMsg   = cached
        ? `🔍 TXIDを受け付けました\n\nチェーン：${chainName}\nTXID：${txShort}\n\n⚡ 過去の調査データを取得中...`
        : `🔍 TXIDを受け付けました\n\nチェーン：${chainName}\nTXID：${txShort}\n\n⚙️ 調査を実行中です...\n通常30秒〜2分かかります`;

      await lineClient.replyMessage(event.replyToken, { type: 'text', text: waitMsg });
      runInvestigation(userId, text, chain).catch(console.error);
      return;
    }

    // ── 調査実行中 ────────────────────────────────────────
    case 'investigating': {
      if (chain) {
        if (text.toLowerCase() === session.txid?.toLowerCase()) {
          return lineClient.replyMessage(event.replyToken, {
            type: 'text',
            text: `⚙️ このTXIDはただいま調査中です\nしばらくお待ちください`,
          });
        }
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `⚠️ 現在別のTXIDを調査中です\n\n調査完了後に新しいTXIDを送ってください`,
        });
      }
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `⚙️ 調査中です。しばらくお待ちください`,
      });
    }

    // ── 調査完了（次のTXID or 再送受付）──────────────────
    case 'done': {
      if (!chain) {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `次のTXIDをお送りください\n対応：BTC / ETH / XRP`,
        });
      }

      // 同じTXID → キャッシュから再表示
      if (text.toLowerCase() === session.txid?.toLowerCase()) {
        const cached = txidCache.get(text.toLowerCase());
        if (cached?.result) {
          await lineClient.replyMessage(event.replyToken, {
            type: 'text', text: `このTXIDは調査済みです\n調査結果を再表示します`,
          });
          await lineClient.pushMessage(userId, { type: 'text', text: buildReport(cached.result) });
          const applyUrl = `${BASE_URL}/apply?uid=${encodeURIComponent(userId)}`;
          await lineClient.pushMessage(userId, { type: 'text', text: buildServiceMsg(applyUrl, cached.result) });
        }
        return;
      }

      // 違うTXID → 新規調査
      session.txid  = text;
      session.chain = chain;
      session.state = 'investigating';
      const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger' }[chain];
      const txShort   = text.slice(0, 10) + '...' + text.slice(-6);
      const cached    = txidCache.get(text.toLowerCase());
      const waitMsg   = cached
        ? `🔍 新しいTXIDを受け付けました\n\nチェーン：${chainName}\nTXID：${txShort}\n\n⚡ 過去の調査データを取得中...`
        : `🔍 新しいTXIDを受け付けました\n\nチェーン：${chainName}\nTXID：${txShort}\n\n⚙️ 調査を実行中です...\n通常30秒〜2分かかります`;
      await lineClient.replyMessage(event.replyToken, { type: 'text', text: waitMsg });
      runInvestigation(userId, text, chain).catch(console.error);
      return;
    }

    default: {
      resetSession(userId);
      const ns = getSession(userId);
      ns.state = 'waiting_txid';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text', text: `TXIDをお送りください\n対応：BTC / ETH / XRP`,
      });
    }
  }
}

// ══ Express ══════════════════════════════════════════════════

// Stripe Webhook（raw body 必須 → 最初に登録）
app.post('/stripe-webhook',
  express.raw({ type: 'application/json' }),
  async (req, res) => {
    if (!stripe || !STRIPE_WEBHOOK_SECRET) return res.json({ ok: true });
    let event;
    try {
      event = stripe.webhooks.constructEvent(req.body, req.headers['stripe-signature'], STRIPE_WEBHOOK_SECRET);
    } catch (e) {
      return res.status(400).send(`Webhook Error: ${e.message}`);
    }

    if (event.type === 'checkout.session.completed') {
      const s = event.data.object;
      // ── Connection（Web版）の決済：決済後はTXID入力フォームで処理 ──
      if (s.metadata?.brand === 'connection') {
        const cEmail = s.customer_details?.email || s.customer_email || s.metadata.email || '';
        const formToken = s.metadata.formToken;
        // 念のためフォームトークンに最新メールを反映＋バックアップでフォームURLをメール
        if (formToken && txidFormTokens.has(formToken)) {
          const fd = txidFormTokens.get(formToken);
          if (cEmail) fd.email = cEmail;
          const formUrl = `${BASE_URL}/txid-form/${formToken}`;
          if (cEmail && !fd.used) {
            sendEmail(cEmail, '【Connection】調査するTXIDのご入力をお願いします',
              buildConnectionTxidFormEmailHTML(fd.customerName, formUrl, fd.count)).catch(console.error);
          }
        }
        return res.json({ received: true });
      }
      const { sessionId, userId, txidCount, customerName } = s.metadata;
      const count = parseInt(txidCount) || 1;
      const cName = customerName || '（お名前）';
      const customerEmail = s.customer_details?.email || s.customer_email || '';

      try {
        // ワンタイムTXID入力フォームのトークンを生成
        const formToken  = crypto.randomUUID();
        txidFormTokens.set(formToken, {
          sessionId, userId, count, customerName: cName,
          email: customerEmail, used: false, createdAt: Date.now(),
        });
        const txidFormUrl = `${BASE_URL}/txid-form/${formToken}`;

        // LINEにTXID入力リンクを送信（LINE経由の申込のみ。Web決済はuidが無いのでスキップ）
        if (userId) {
          try {
            await lineClient.pushMessage(userId, {
              type: 'text',
              text: `✅ お支払いありがとうございます！\n\n📝 以下のURLから調査するTXIDを入力してください\n（${count}件まで入力できます）\n\n${txidFormUrl}\n\n⚠️ このURLは1回のみ使用可能です`,
            });
          } catch (e) { console.error('[LINE push] TXIDフォーム送信失敗:', e.message); }
        }

        // Sheetsに支払い確認を記録
        updateSheetReportUrl(sessionId, `[TXID待ち] ${txidFormUrl}`).catch(console.error);

        // メールでもTXID入力フォームURLを送信
        if (customerEmail) {
          sendEmail(
            customerEmail,
            '【BitTo】TXIDの入力をお願いします',
            buildTxidFormEmailHTML(cName, txidFormUrl, count),
            'bitto'   // 渡さないと送信元が Connection 名義になる
          ).catch(console.error);
        }

        pendingSessions.delete(sessionId);
      } catch (e) {
        console.error('Stripe webhook エラー:', e);
        if (userId) {
          try {
            await lineClient.pushMessage(userId, {
              type: 'text', text: `⚠️ エラーが発生しました\n${e.message}\nサポートにご連絡ください`,
            });
          } catch (_) {}
        }
      }
    }
    res.json({ received: true });
  }
);

// 申し込みフォームからの決済セッション作成
app.post('/api/create-checkout', express.json(), async (req, res) => {
  try {
    const { uid, name, phone, email, address, txid_count, source } = req.body;
    const count  = Math.max(1, Math.min(BITTO_MAX_TXID, parseInt(txid_count) || 1));
    const amount = BITTO_PRICE * count;
    const sessionId = crypto.randomUUID();

    // Stripe未設定でも Sheets保存・確認メールだけ先に実行
    const submittedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    appendToSheet([
      submittedAt, name || '', phone || '', email || '', address || '',
      String(count), String(amount), sessionId, '', '申込済み',
    ]).catch(console.error);
    if (email) {
      sendEmail(
        email,
        '【BitTo】ご利用規約同意の確認',
        buildTOSEmailHTML(name || '', count, amount, submittedAt),
        'bitto'   // 渡さないと送信元が Connection 名義になる
      ).catch(console.error);
    }

    // LINEに申込確認メッセージを送信
    if (uid) {
      lineClient.pushMessage(uid, {
        type: 'text',
        text: `📋 申し込みを受け付けました\n━━━━━━━━━━━━━━━\n👤 お名前：${name || '不明'}\n📊 調査件数：${count}件\n💰 合計金額：¥${amount.toLocaleString()}（税込）\n📅 申込日時：${submittedAt}\n━━━━━━━━━━━━━━━\nこのままお支払い画面へお進みください。\n決済完了後にTXID入力フォームをお送りします。`,
      }).catch(e => console.error('[LINE] 申込確認送信エラー:', e.message));
    }

    // Stripe未設定の場合はテスト用成功ページへ
    if (!stripe) {
      return res.json({ url: `${BASE_URL}/payment/success?sid=${sessionId}&test=1` });
    }

    const session = await stripe.checkout.sessions.create({
      payment_method_types: ['card'],
      customer_email: email || undefined,
      line_items: [{
        price_data: {
          currency: 'jpy',
          product_data: {
            name:        `BitTo 詳細調査レポート（${count}件）`,
            description: `ブロックチェーン調査レポート ${count}件分`,
          },
          unit_amount: amount,
        },
        quantity: 1,
      }],
      mode: 'payment',
      success_url: `${BASE_URL}/payment/success?sid=${sessionId}`,
      cancel_url:  source === 'web' ? `${BASE_URL}/bitto` : `${BASE_URL}/apply?uid=${encodeURIComponent(uid || '')}`,
      metadata: {
        sessionId,
        userId:       uid || '',
        txidCount:    String(count),
        customerName: name || '',
        phone:        phone || '',
        address:      address || '',
      },
    });

    pendingSessions.set(sessionId, { userId: uid, txidCount: count, stripeId: session.id, createdAt: Date.now() });
    res.json({ url: session.url });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// 決済完了・キャンセルページ
app.get('/payment/success', (_req, res) => res.send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>決済完了 — BitTo</title>
<style>
body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:36px 28px;max-width:420px;width:100%;text-align:center}
h1{color:#34d399;font-size:1.4rem;margin:12px 0 8px}.icon{font-size:3rem;margin-bottom:4px}
.sub{color:#94a3b8;line-height:1.7;margin-bottom:24px;font-size:0.95rem}
.steps{text-align:left;background:#0d1117;border-radius:12px;padding:20px 20px;margin-bottom:20px}
.steps h2{font-size:0.85rem;color:#64748b;text-transform:uppercase;letter-spacing:0.05em;margin:0 0 14px}
.step{display:flex;align-items:flex-start;gap:12px;margin-bottom:14px;font-size:0.92rem;color:#cbd5e1;line-height:1.5}
.step:last-child{margin-bottom:0}
.badge{background:#1e3a5f;color:#60a5fa;border-radius:50%;width:24px;height:24px;display:flex;align-items:center;justify-content:center;font-size:0.78rem;font-weight:700;flex-shrink:0;margin-top:1px}
.check{color:#34d399;font-weight:700;font-size:1rem}
.note{background:#1a1f2e;border:1px solid #2d3748;border-radius:10px;padding:14px 16px;font-size:0.85rem;color:#94a3b8;line-height:1.6;text-align:left}
.note strong{color:#fbbf24}
</style></head>
<body><div class="card">
  <div class="icon">✅</div>
  <h1>決済が完了しました</h1>
  <p class="sub">お支払いありがとうございます。<br>以下の手順で調査をお進めください。</p>

  <div class="steps">
    <h2>📋 次のステップ</h2>
    <div class="step"><div class="badge">1</div><div>ご登録のメールアドレスに <strong>TXID入力フォームのURL</strong> をお送りします（LINE連携の場合はLINEにも届きます）。<br>数秒〜1分ほどお待ちください。迷惑メールフォルダもご確認ください。</div></div>
    <div class="step"><div class="badge">2</div><div>届いたURLを開き、<strong>調査対象のTXID</strong>（トランザクションID）を入力してください。</div></div>
    <div class="step"><div class="badge">3</div><div>調査完了後、<strong>レポートURLをメール</strong>（LINE連携の場合はLINEにも）にお送りします。</div></div>
  </div>

  <div class="note">
    <strong>⚠️ ご確認ください</strong><br>
    ✅ TXIDはブロックチェーン上の取引IDです（64文字の英数字）<br>
    ✅ 入力後の変更・キャンセルはできません<br>
    ✅ フォームURLは1回のみ使用可能です
  </div>
</div></body></html>`));

app.get('/payment/cancel', (_req, res) => res.send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>キャンセル — BitTo</title>
<style>body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:40px;max-width:380px}
h1{color:#f87171;font-size:1.5rem;margin-bottom:12px}.icon{font-size:3rem;margin-bottom:16px}p{color:#94a3b8;line-height:1.6}</style></head>
<body><div class="card"><div class="icon">❌</div><h1>キャンセルされました</h1>
<p>やり直す場合はLINEにて<br>フォームリンクをご確認ください。</p></div></body></html>`));

// LINE Webhook
app.post('/webhook', line.middleware(lineConfig), async (req, res) => {
  res.json({ ok: true });
  await Promise.all(req.body.events.map(handleLineEvent)).catch(console.error);
});

app.use(cors());
app.use(express.json());
/* 本文が大きすぎるとExpressがHTMLのエラーページを返し、画面側が「保存できません」
   としか出せない。JSONで理由を返し、利用者に短くしてもらう。 */
app.use((err, req, res, next) => {
  if (err && err.type === 'entity.too.large') {
    return res.status(413).json({ error: '入力が長すぎます。お手数ですが、経緯を短くしてから保存してください。' });
  }
  next(err);
});

// ── APIレスポンスをキャッシュさせない ──────────────────────────
// 調査の進捗確認（/api/connection/job/:id）は同じURLを数秒ごとに叩くため、
// Cache-Control が無いとiOSのWebViewが応答をキャッシュし、
// 調査が完了しても古い "running" を返し続けてアプリ側がタイムアウトしてしまう。
// さらに、ExpressはETagを付けて条件付きリクエスト(If-None-Match)に 304 Not Modified を返すため、
// no-store を無視するiOS WebViewだと 304 経由でキャッシュ済みの "running" を出し続けてしまう。
// 受信側の条件付きヘッダを削除して 304 を発生させず、毎回かならず完全な本文を返す。
app.use('/api', (req, res, next) => {
  delete req.headers['if-none-match'];
  delete req.headers['if-modified-since'];
  res.set('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0');
  res.set('Pragma', 'no-cache');
  res.set('Expires', '0');
  next();
});

app.use(express.static(path.join(__dirname, 'public')));

// ── REST API ────────────────────────────────────────────────
app.get('/api/status', (_req, res) => res.json({
  ok: true, mode: stripe ? 'production' : 'test（Stripeなし）',
  keys: { blockchair: !!BLOCKCHAIR_KEY, etherscan: !!ETHERSCAN_KEY, gemini: !!GEMINI_KEY, line: !!LINE_CHANNEL_ACCESS_TOKEN, stripe: !!stripe },
  // 注文と報告書が再デプロイで消えないか（Railwayのログを見なくても外から確認できるように）
  storage: storageState,
  webhook: `${BASE_URL}/webhook`,
}));
app.get('/api/btc/tx/:txid', async (req, res) => {
  try { res.json(await (await fetch(`https://api.blockchair.com/bitcoin/dashboards/transaction/${req.params.txid}?key=${BLOCKCHAIR_KEY}`)).json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/btc/address/:addr', async (req, res) => {
  try { res.json(await (await fetch(`https://api.blockchair.com/bitcoin/dashboards/address/${req.params.addr}?key=${BLOCKCHAIR_KEY}`)).json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/tx/:hash', async (req, res) => {
  try { const h = req.params.hash.startsWith('0x') ? req.params.hash : '0x' + req.params.hash;
    res.json(await (await fetch(`https://api.blockchair.com/ethereum/dashboards/transaction/${h}?key=${BLOCKCHAIR_KEY}`)).json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/address/:addr', async (req, res) => {
  try { res.json(await (await fetch(`https://api.blockchair.com/ethereum/dashboards/address/${req.params.addr}?key=${BLOCKCHAIR_KEY}`)).json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/txlist/:addr', async (req, res) => {
  try { const { page=1, offset=20, sort='desc' } = req.query;
    res.json(await (await fetch(`https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${req.params.addr}&startblock=0&endblock=latest&page=${page}&offset=${offset}&sort=${sort}&apikey=${ETHERSCAN_KEY}`)).json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/xrp/tx/:txid', async (req, res) => {
  try { const r = await fetch(`https://api.xrpscan.com/api/v1/tx/${req.params.txid.toUpperCase()}`);
    const t = await r.text(); if (t === 'Not found') return res.status(404).json({ error: 'Not found' }); res.json(JSON.parse(t)); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
/* /api/ai/analyze（任意のプロンプトをGeminiへ中継）は削除した。
   アプリもWebも使っておらず、誰でも叩ける状態のまま残すと、こちらの費用で
   好きな文章を生成させられる。相談は /api/connection/consult（レート制限つき）に一本化する。 */

// メール送信テスト（ブラウザで /api/test-email?to=xxx を開くと確認できる）
app.get('/api/test-email', requireAdmin, async (req, res) => {
  const to = req.query.to || SMTP_USER;
  if (!to) return res.status(400).json({ error: 'to パラメータが必要です' });
  const html = '<p>このメールが届いていればメール設定は正常です。</p>';
  // Resend優先
  if (RESEND_API_KEY) {
    try {
      const id = await sendViaResend(to, '【Connection】メール送信テスト', html);
      return res.json({ ok: true, via: 'resend', id, to, from: MAIL_FROM });
    } catch (e) {
      return res.status(500).json({ ok: false, via: 'resend', error: e.message });
    }
  }
  // SMTPフォールバック
  try {
    const mailer = getMailer();
    if (!mailer) return res.status(503).json({ error: 'メール未設定（RESEND_API_KEY または SMTP_USER/PASS）' });
    const info = await mailer.sendMail({ from: `"BitTo テスト" <${SMTP_USER}>`, to, subject: '【BitTo】メール送信テスト', html });
    res.json({ ok: true, via: 'smtp', messageId: info.messageId, to });
  } catch (e) {
    res.status(500).json({ ok: false, via: 'smtp', error: e.message, code: e.code, response: e.response });
  }
});

// 管理用レポート生成API（LINE・決済不要）
app.post('/api/admin/generate-report', requireAdmin, express.json(), async (req, res) => {
  try {
    const { customerName, txids } = req.body;
    if (!customerName) return res.status(400).json({ error: 'customerNameが必要です' });
    if (!Array.isArray(txids) || txids.length === 0) return res.status(400).json({ error: 'TXIDが必要です' });

    const list = [];
    const errors = [];

    for (const item of txids) {
      const txid  = (item.txid || '').trim();
      const chain = item.chain || detectChain(txid);
      if (!txid)  { errors.push('空のTXIDをスキップ'); continue; }
      if (!chain) { errors.push(`チェーン不明: ${txid.slice(0,16)}...`); continue; }
      try {
        console.log(`[Admin] 調査開始: ${txid} (${chain})`);
        const cacheKey = txid.toLowerCase();
        let result = txidCache.get(cacheKey)?.result;
        if (!result) {
          result = await investigate(txid, chain);
          txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
        }
        list.push({ txid, chain, result });
        console.log(`[Admin] 調査完了: ${txid}`);
      } catch (e) {
        errors.push(`${txid.slice(0,16)}...: ${e.message}`);
      }
    }

    if (list.length === 0) return res.status(400).json({ error: '調査できたTXIDが0件です', errors });

    const issuedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    console.log('[Admin] AI分析開始...');
    const aiData = await generateAIContent(list, customerName).catch(() => ({ analysis: null, requests: [] }));
    const reportId   = crypto.randomUUID();
    const reportUrl  = `${BASE_URL}/report/${reportId}`;
    const reportHtml = generateReportHTML(list, customerName, issuedAt, aiData, reportUrl);
    await saveReport(reportId, reportHtml);

    console.log('[Admin] レポート生成完了:', reportUrl);
    res.json({ ok: true, url: reportUrl, errors });
  } catch (e) {
    console.error('[Admin] エラー:', e);
    res.status(500).json({ error: e.message });
  }
});

/* ラベルAPIの疎通確認。キー投入後に応答の形をそのまま見るために置く。
   例: /api/admin/label-lookup?address=34xp4vRocGJym3xR7yCVpFHoCNxv4twsEo&chain=btc */
app.get('/api/admin/label-lookup', requireAdmin, async (req, res) => {
  const addr  = (req.query.address || '').trim();
  const chain = (req.query.chain || 'btc').toLowerCase();
  if (!addr) return res.status(400).json({ error: 'address が必要です' });
  if (!MISTTRACK_KEY) return res.json({ ok: false, reason: 'MISTTRACK_API_KEY が未設定です' });
  try {
    const r = await fetchT(labelApiUrl(addr, chain));
    const j = await r.json();
    res.json({ ok: r.ok, status: r.status, picked: pickLabelFromResponse(j), raw: j });
  } catch (e) {
    res.status(500).json({ error: scrubKey(e.message) });
  }
});

// /apply → apply.html（クエリパラメータ付きでも対応）
app.get('/apply', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'apply.html')));

// 管理ページ
app.get('/admin', requireAdmin, (_req, res) => res.sendFile(path.join(__dirname, 'public', 'admin.html')));

// テスト用：決済スキップでTXID入力フォームを生成
// 使い方: /api/test-txid-form?name=山田太郎&count=2&email=test@gmail.com
app.get('/api/test-txid-form', requireAdmin, (req, res) => {
  const customerName = req.query.name  || 'テストユーザー';
  const count        = parseInt(req.query.count) || 1;
  const email        = req.query.email || '';
  const brand        = req.query.brand || 'bitto';
  const formToken    = crypto.randomUUID();
  txidFormTokens.set(formToken, {
    sessionId: 'test-' + formToken,
    userId:    null,
    count, customerName, email, brand,
    status: 'paid_waiting_txid',
    used: false, createdAt: Date.now(),
  });
  const url = `${BASE_URL}/txid-form/${formToken}`;
  console.log('[Test] TXIDフォーム生成:', url);
  res.json({ ok: true, url, formToken });
});

/* ══ 被害時系列パック（ヒアリング＋解析結果の資料）══════════
   警察・取引所へ相談する場に持っていく紙。読む人は暗号資産に
   詳しくない前提で、専門用語には短い説明を添える。
   推定は推定と書き、断定しない。 */
/* パックは利用者の自由記入を紙に載せる。そのまま埋め込むと崩れるのでここで無害化する。 */
function escHtml(s) {
  return String(s == null ? '' : s).replace(/[&<>"]/g, c => ({ '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;' }[c]));
}

function packRow(label, value) {
  if (value == null || value === '' || (Array.isArray(value) && !value.length)) return '';
  const v = Array.isArray(value) ? value.join(' / ') : String(value);
  return `<tr><th>${escHtml(label)}</th><td>${escHtml(v).split(String.fromCharCode(10)).join('<br>')}</td></tr>`;
}

function buildTimelinePackHTML(h, form) {
  const a    = h.answers || {};
  const txs  = form.txSummary || [];
  const now  = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  const name = h.customerName || '';

  // 時系列：チェーンに記録が残っている送金と、ご回答から分かる出来事を混ぜて古い順に並べる。
  const events = txs.map(t => ({
    time: t.blockTime || '',
    what: `${t.tokenSymbol ? `${t.tokenAmount} ${t.tokenSymbol}` : `${t.amount} ${t.chain}`} を送金`
        + (t.exchange ? `（到達先の推定：${t.exchange}）` : ''),
    src: 'ブロックチェーンの記録',
  }));
  if (a.b5) events.unshift({ time: String(a.b5).split('〜')[0].trim(), what: '相手と接触（' + (a.b2 || '経路不明') + '）', src: 'ご回答' });
  if (a.d1 === 'はい') events.push({ time: '（現在）', what: '追加の送金・費用を要求されている', src: 'ご回答' });
  if (a.d2 && a.d2 !== '試していない') events.push({ time: '（時期不明）', what: '出金を試みた：' + a.d2, src: 'ご回答' });

  const txRows = txs.map((t, i) => `<tr>
      <td>${i + 1}</td><td>${escHtml(t.blockTime || '不明')}</td>
      <td>${escHtml(t.tokenSymbol ? `${t.tokenAmount} ${t.tokenSymbol}` : `${t.amount} ${t.chain}`)}</td>
      <td class="mono">${escHtml(t.txid)}</td>
      <td>${escHtml(t.exchange || '未判明')}</td></tr>`).join('');

  return `<!DOCTYPE html><html lang="ja"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>BitTo 被害時系列パック</title><style>
body{font-family:-apple-system,'Hiragino Kaku Gothic ProN','Noto Sans JP',Meiryo,sans-serif;color:#111;
  line-height:1.8;max-width:820px;margin:0 auto;padding:28px 22px;font-size:14px}
h1{font-size:20px;margin:0 0 4px}
h2{font-size:15px;margin:26px 0 8px;padding-bottom:5px;border-bottom:2px solid #111}
.meta{color:#666;font-size:12px;margin-bottom:6px}
.note{background:#f5f5f5;border-left:3px solid #999;padding:10px 12px;font-size:12px;color:#444;margin:10px 0}
table{width:100%;border-collapse:collapse;margin:8px 0;font-size:12.5px}
th,td{border:1px solid #ccc;padding:7px 8px;text-align:left;vertical-align:top}
th{background:#f0f0f0;width:30%}
table.tl th{width:auto}
.mono{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:11px;word-break:break-all}
.warn{background:#fff3f3;border:1px solid #e0a0a0;padding:12px 14px;border-radius:6px}
ul.story{margin:8px 0 0 20px;padding:0}
ul.story li{margin:6px 0;font-size:13px;line-height:1.8}
.warn b{color:#b32}
.btns{margin:18px 0}
button{font:inherit;padding:9px 16px;border:1px solid #333;background:#111;color:#fff;border-radius:6px;cursor:pointer}
@media print{.btns{display:none}body{padding:0}}
</style></head><body>
<h1>BitTo 被害時系列パック</h1>
<div class="meta">作成日時：${escHtml(now)}${name ? '　／　ご依頼者：' + escHtml(name) + ' 様' : ''}</div>
<div class="note">本資料は、公開ブロックチェーンの解析結果と、ご本人からうかがった内容をまとめたものです。
到達取引所等は<b>推定を含みます</b>。資産の回収・返還を保証するものではありません。</div>
<div class="btns"><button onclick="window.print()">印刷 / PDFで保存</button></div>

<h2>1. 概要</h2>
<table>
${packRow('最初の送金（チェーン記録）', txs[0] ? `${txs[0].blockTime}　${txs[0].tokenSymbol ? `${txs[0].tokenAmount} ${txs[0].tokenSymbol}` : `${txs[0].amount} ${txs[0].chain}`}` : '')}
${packRow('送金元アドレス', txs[0] ? txs[0].sender : '')}
${packRow('送金の回数（ご申告）', a.c1)}
${packRow('総額（ご申告・概算）', a.c2)}
${packRow('送金の手段', a.c3)}
${packRow('報告書', form.report ? form.report.reportUrl : '')}
</table>

<h2>2. 時系列</h2>
<table class="tl"><tr><th style="width:22%">日時</th><th>出来事</th><th style="width:24%">根拠</th></tr>
${events.map(e => `<tr><td>${escHtml(e.time || '不明')}</td><td>${escHtml(e.what)}</td><td>${escHtml(e.src)}</td></tr>`).join('')}
</table>
<div class="note">「ブロックチェーンの記録」はチェーン上に残っている事実です。「ご回答」はご本人の記憶にもとづく内容です。</div>

<h2>3. 送金の記録（解析結果）</h2>
${txs.length ? `<table class="tl"><tr><th style="width:6%">#</th><th style="width:20%">日時</th><th style="width:18%">数量</th><th>TXID</th><th style="width:20%">到達取引所（推定）</th></tr>${txRows}</table>`
             : '<div class="note">解析済みの送金がまだありません。</div>'}

<h2>4. 最初の送金の経緯</h2>
<table>
${packRow('名目', a.a1)}
${packRow('送金先として指示されたサイト・アプリ', a.a2)}
${packRow('アドレスの渡され方', a.a3)}
${packRow('送金直前に言われたこと', a.a4)}
</table>

<h2>5. 相手方の情報</h2>
<table>
${packRow('名乗り', a.b1)}
${packRow('最初の接触経路', a.b2)}
${packRow('連絡手段', a.b3)}
${packRow('アカウント名・ID・電話番号', a.b4)}
${packRow('やり取りの期間', a.b5)}
</table>

<h2>6. いまの状況</h2>
<table>
${packRow('追加の送金・費用の要求', a.d1)}
${packRow('出金を試みたか', a.d2)}
${packRow('相手との連絡', a.d3)}
${packRow('相手のサイト・アプリ', a.d4)}
${packRow('銀行振込先（判明分）', a.c5)}
${packRow('他のTXID（ご申告）', a.c4)}
</table>

<h2>7. すでに行った対応・保全している証拠</h2>
<table>
${packRow('警察への相談', a.e1)}
${packRow('取引所への申告', a.e2)}
${packRow('回収業者への連絡', a.e3)}
${packRow('保全している証拠', a.f1)}
${packRow('その他', a.note)}
</table>
${a.e3 === '連絡した' ? '<div class="warn"><b>回収業者にご連絡済みとのことです。</b>「必ず取り戻せる」「回収の前に前払い金が必要」と言われている場合は、二次被害の典型的なサインです。支払い前に、警察・消費者ホットライン188へご相談ください。</div>' : ''}

<h2>8. 経緯（ご本人の記述）</h2>
${a.story ? `<ul class="story">${String(a.story).split(String.fromCharCode(10))
    .map(l => { let t = l.trim(); while (t && '・-–—*●○•>＞'.includes(t[0])) t = t.slice(1).trim(); return t; })
    .filter(Boolean)
    .map(l => `<li>${escHtml(l)}</li>`).join('')}</ul>`
  : '<div class="note">ご記入がありません。</div>'}

<h2>9. BitToができること／できないこと</h2>
<table><tr><th style="width:50%">できること</th><th>できないこと</th></tr>
<tr><td>公開チェーンの資金経路の解析<br>着金先取引所・サービスの推定<br>警察・取引所への提出資料の整理<br>不正利用申告文の作成<br>相談先・必要書類の案内</td>
<td>取引所へ凍結を命令する<br>KYC情報を強制的に取得する<br>資金の残存を保証する<br>被害資金の返還を保証する<br>秘密鍵で資金を取り戻す</td></tr></table>
<div class="note">緊急・進行中の犯罪は110。緊急でない警察相談は#9110、被害届は最寄りの警察署、消費者トラブルは188、
詐欺的投資・無登録業者は金融庁の相談窓口が候補です。</div>
</body></html>`;
}

/* ══ ヒアリングAPI ═══════════════════════════════════════════
   購入者限定。開始には決済後に発行される申込トークンが要る。
   1つの申込に1つのヒアリング（作り直さず再開させる）。 */
app.post('/api/hearing/start', express.json(), (req, res) => {
  const token = (req.body && req.body.token || '').trim();
  const form  = txidFormTokens.get(token);
  if (!form) return res.status(403).json({ error: 'この機能は報告書をご購入いただいた方専用です' });

  let id = [...hearings.entries()].find(([, h]) => h.token === token)?.[0];
  if (!id) {
    id = crypto.randomUUID();
    hearings.set(id, {
      id, token,
      customerName: form.customerName || '',
      email: form.email || '',
      reportUrl: form.report?.reportUrl || '',
      answers: {}, status: 'draft',
      createdAt: Date.now(), updatedAt: Date.now(),
    });
    saveHearings();
  }
  res.json({ ok: true, id, first: (form.txSummary || [])[0] || null, txCount: (form.txSummary || []).length });
});

app.get('/api/hearing/:id', (req, res) => {
  const h = hearings.get(req.params.id);
  if (!h) return res.status(404).json({ error: '見つかりません' });
  const form = txidFormTokens.get(h.token) || {};
  res.json({
    ok: true, id: h.id, status: h.status, answers: h.answers,
    customerName: h.customerName, reportUrl: h.reportUrl,
    first: (form.txSummary || [])[0] || null, txSummary: form.txSummary || [],
    sheetLogged: h.sheetLogged ?? null, sheetError: h.sheetError || null,
  });
});

// 下書き保存（自動保存用）。答えの上書きだけを行い、状態は変えない。
/* 自由記入をそのまま受けると、保存先（永続ボリューム・スプレッドシート）を
   いくらでも膨らませられる。項目ごとに上限を置いて切り詰める。
   経緯は長くなるので他より広く取る。 */
const HEARING_MAX = { story: 8000, note: 4000, _default: 1000 };
function trimAnswers(input) {
  const out = {};
  for (const [k, v] of Object.entries(input || {})) {
    const max = HEARING_MAX[k] || HEARING_MAX._default;
    if (Array.isArray(v)) out[k] = v.slice(0, 30).map(x => String(x).slice(0, 200));
    else if (v == null) out[k] = '';
    else out[k] = String(v).slice(0, max);
  }
  return out;
}

app.post('/api/hearing/save', express.json(), (req, res) => {
  const { id, answers } = req.body || {};
  const h = hearings.get(id);
  if (!h) return res.status(404).json({ error: '見つかりません' });
  if (h.status === 'submitted') return res.status(409).json({ error: '送信済みです' });
  h.answers = { ...h.answers, ...trimAnswers(answers) };
  h.updatedAt = Date.now();
  saveHearings();
  res.json({ ok: true, savedAt: h.updatedAt });
});

app.post('/api/hearing/submit', express.json(), async (req, res) => {
  const { id, answers } = req.body || {};
  const h = hearings.get(id);
  if (!h) return res.status(404).json({ error: '見つかりません' });
  h.answers = { ...h.answers, ...trimAnswers(answers) };
  h.status = 'submitted';
  h.submittedAt = Date.now();
  h.updatedAt = Date.now();
  saveHearings();
  res.json({ ok: true });   // 先に返す。シート書き込みは待たせない

  const form  = txidFormTokens.get(h.token) || {};
  const first = (form.txSummary || [])[0] || {};
  const record = {
    ...h.answers,
    submittedAt:  new Date(h.submittedAt).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }),
    customerName: h.customerName,
    email:        h.email,
    reportUrl:    form.report?.reportUrl || h.reportUrl || '',
    firstTime:    first.blockTime || '',
    firstAmount:  first.tokenSymbol ? `${first.tokenAmount} ${first.tokenSymbol}` : (first.amount != null ? `${first.amount} ${first.chain || ''}` : ''),
    firstChain:   first.chain || '',
    firstExchange: first.exchange || '',
    token:        h.token,
  };
  const r = await appendHearingToSheet(record);
  h.sheetLogged = r.ok;
  h.sheetError  = r.ok ? null : r.reason;
  saveHearings();
});

/* すでにあるタブを整形し直す。見出しを変えたときや、手で触って崩れたときに戻す。 */
app.get('/api/admin/hearing-format', requireAdmin, async (_req, res) => {
  const sheets = getSheets();
  if (!sheets || !HEARING_SHEET_ID) return res.json({ ok: false, reason: 'Sheets未設定' });
  try {
    const meta = await sheets.spreadsheets.get({ spreadsheetId: HEARING_SHEET_ID });
    const tab  = (meta.data.sheets || []).find(sh => sh.properties && sh.properties.title === HEARING_SHEET_TAB);
    if (!tab) return res.json({ ok: false, reason: 'タブ「' + HEARING_SHEET_TAB + '」が見つかりません' });
    await sheets.spreadsheets.values.update({
      spreadsheetId: HEARING_SHEET_ID,
      range: HEARING_SHEET_TAB + '!A1',
      valueInputOption: 'RAW',
      requestBody: { values: [HEARING_FIELDS.map(f => f[1])] },
    });
    await formatHearingTab(sheets, tab.properties.sheetId);
    res.json({
      ok: true,
      spreadsheet: meta.data.properties && meta.data.properties.title,
      tab: HEARING_SHEET_TAB, columns: HEARING_FIELDS.length,
      url: 'https://docs.google.com/spreadsheets/d/' + HEARING_SHEET_ID + '/edit#gid=' + tab.properties.sheetId,
    });
  } catch (e) {
    res.status(500).json({ ok: false, reason: e.message });
  }
});

/* シートへの書き込みが失敗した回答をまとめて送り直す。
   失敗の主因は共有設定の付け忘れで、直したあとに手で入れ直すのは現実的でない。
   回答自体はサーバーに残っているので、権限がついた時点で流し込める。 */
app.get('/api/admin/hearing-resend', requireAdmin, async (_req, res) => {
  const pending = [...hearings.values()].filter(h => h.status === 'submitted' && h.sheetLogged !== true);
  const results = [];
  for (const h of pending) {
    const form  = txidFormTokens.get(h.token) || {};
    const first = (form.txSummary || [])[0] || {};
    const r = await appendHearingToSheet({
      ...h.answers,
      submittedAt:  new Date(h.submittedAt || h.updatedAt).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }),
      customerName: h.customerName,
      email:        h.email,
      reportUrl:    form.report?.reportUrl || h.reportUrl || '',
      firstTime:    first.blockTime || '',
      firstAmount:  first.tokenSymbol ? `${first.tokenAmount} ${first.tokenSymbol}` : (first.amount != null ? `${first.amount} ${first.chain || ''}` : ''),
      firstChain:   first.chain || '',
      firstExchange: first.exchange || '',
      token:        h.token,
    });
    h.sheetLogged = r.ok;
    h.sheetError  = r.ok ? null : r.reason;
    results.push({ id: h.id, ok: r.ok, reason: r.reason || null });
  }
  saveHearings();
  res.json({ ok: true, tried: results.length, sent: results.filter(r => r.ok).length, results });
});

// 資料本体。PDF化でもこのURLを開くので、認証は報告書と同じ「URLを知っている人だけ」の方式。
app.get('/api/hearing/:id/pack', (req, res) => {
  const h = hearings.get(req.params.id);
  if (!h) return res.status(404).send('見つかりません');
  const form = txidFormTokens.get(h.token) || {};
  res.setHeader('Content-Type', 'text/html; charset=utf-8');
  res.send(buildTimelinePackHTML(h, form));
});

app.get('/api/hearing/:id/pack.pdf', async (req, res) => {
  const h = hearings.get(req.params.id);
  if (!h) return res.status(404).send('見つかりません');
  try {
    const file = path.join(REPORTS_DIR, `pack-${h.id}.pdf`);
    await generatePackPdf(h.id, file);
    res.setHeader('Content-Type', 'application/pdf');
    res.setHeader('Content-Disposition', `attachment; filename="BitTo-timeline-${h.id}.pdf"`);
    fs.createReadStream(file).pipe(res);
  } catch (e) {
    console.error('[Pack] PDF生成に失敗:', e.message);
    res.status(500).send('PDFを作成できませんでした。ページ上部の「印刷 / PDFで保存」をお試しください。');
  }
});

// ヒアリング画面。購入者に配るリンクは /hearing/<申込トークン>。
app.get('/hearing/:token', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'hearing.html')));

// TXID入力フォーム（ワンタイムリンク）
app.get('/txid-form/:token', (req, res) => {
  const data = txidFormTokens.get(req.params.token);
  if (!data) return res.status(404).sendFile(path.join(__dirname, 'public', 'form-expired.html'));
  // 使用済みでもフォームページを返す。ページ側が status を見て調査中／報告書リンクを表示する。
  // 以前はBitToだけ手前で form-used.html に落としていたため、アプリのレポートタブから
  // 開いても「使用済みです」で行き止まりになり、報告書にたどり着けなかった
  // （txid-form.html 側の使用済み対応が実行される前に弾かれていた）。
  res.sendFile(path.join(__dirname, 'public', 'txid-form.html'));
});

// TXID入力フォーム情報取得API
app.get('/api/txid-form-info/:token', (req, res) => {
  const data = txidFormTokens.get(req.params.token);
  if (!data) return res.status(404).json({ error: 'リンクが無効または期限切れです' });
  if (data.used) return res.status(410).json({ error: 'このリンクはすでに使用済みです', used: true, brand: data.brand || 'bitto' });
  res.json({ ok: true, count: data.count, customerName: data.customerName, brand: data.brand || 'bitto', prefillTxid: data.prefillTxid || '' });
});

// 調査の進捗・結果取得API（決済後フォームの申請完了画面でポーリング）
app.get('/api/txid-form-result/:token', (req, res) => {
  const data = txidFormTokens.get(req.params.token);
  if (!data) return res.status(404).json({ error: 'リンクが無効または期限切れです' });
  res.json({
    status: data.status || (data.used ? 'investigating' : 'paid_waiting_txid'),
    report: data.report || null,
    errorMsg: data.errorMsg || null,
  });
});

// TXID送信・調査開始API
app.post('/api/submit-txids', express.json(), async (req, res) => {
  const { token, txids } = req.body;
  const formData = txidFormTokens.get(token);
  if (!formData)       return res.status(404).json({ error: 'リンクが無効または期限切れです' });
  if (formData.used)   return res.status(410).json({ error: 'このリンクはすでに使用済みです' });
  if (!Array.isArray(txids) || txids.length === 0) return res.status(400).json({ error: 'TXIDが必要です' });
  if (txids.length > formData.count) return res.status(400).json({ error: `件数が超過しています（最大${formData.count}件）` });

  // 即座に使用済みにして二重送信を防ぐ
  formData.used = true;
  formData.status = 'investigating';
  res.json({ ok: true });

  // バックグラウンドで調査・レポート生成
  (async () => {
    try {
      if (formData.userId) {
        await lineClient.pushMessage(formData.userId, {
          type: 'text',
          text: `🔍 TXIDを受け付けました！\n${txids.length}件の調査を開始します\n通常1〜3分でレポートをお届けします`,
        });
      }

      const list = [];
      for (const item of txids) {
        try {
          console.log(`[Submit] 調査中: ${item.txid} (${item.chain})`);
          const cacheKey = item.txid.toLowerCase();
          let result = txidCache.get(cacheKey)?.result;
          if (!result) {
            result = await investigate(item.txid, item.chain);
            txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
          }
          list.push({ txid: item.txid, chain: item.chain, result });
        } catch (e) {
          console.error(`[Submit] 調査失敗: ${item.txid}`, e.message);
        }
      }

      if (list.length === 0) throw new Error('全てのTXIDの調査に失敗しました');

      const issuedAt   = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
      // AI本文が無くても報告書は出せる。ここで待ち続けると納品が止まるので、
      // 上限を超えたら本文なしで先へ進める（最後の砦）。
      const aiData     = await Promise.race([
        generateAIContent(list, formData.customerName),
        new Promise(resolve => setTimeout(() => {
          console.error('[Submit] AI生成が上限を超えたため本文なしで続行します');
          resolve({ analysis: null, requests: [] });
        }, GEMINI_TOTAL_TIMEOUT_MS + 15000)),
      ]).catch(() => ({ analysis: null, requests: [] }));
      const reportId   = crypto.randomUUID();
      const reportUrl  = `${BASE_URL}/report/${reportId}`;
      const reportHtml = generateReportHTML(list, formData.customerName, issuedAt, aiData, reportUrl,
        formData.brand || 'bitto',
        // 経緯をうかがう資料への入口。報告書はあとから見返されるので、ここにも置く
        (formData.brand !== 'connection') ? `${BASE_URL}/hearing/${token}` : '');
      await saveReport(reportId, reportHtml);

      // SheetsにレポートURLを記録
      updateSheetReportUrl(formData.sessionId, reportUrl).catch(console.error);

      // LINEにレポートURL送信
      if (formData.userId) {
        await lineClient.pushMessage(formData.userId, {
          type: 'text',
          text: `✅ 調査レポートが完成しました！\n\n📄 ${reportUrl}\n\n━━━━━━━━━━━━━━━\n📱 PDFとして保存する方法\n━━━━━━━━━━━━━━━\n① 上のURLを「長押し」\n② 「ブラウザで開く」を選択\n③ レポート内のQRコードを\n　 カメラで読み取ってもOK\n④ Safari画面下の共有ボタン\n⑤「PDFとして保存」を選択\n━━━━━━━━━━━━━━━`,
        });
      }

      // 納品情報はブランド共通で記録する。
      // 以前はConnectionの分岐内だけで設定していたため、BitToは報告書が完成しても
      // status が investigating のまま残り、報告書URLも保存されず、アプリの
      // レポートタブやフォーム再訪から報告書にたどり着けなかった（メールが唯一の導線だった）。
      formData.status = 'done';
      formData.report = { reportUrl, issuedAt };
      /* 被害時系列パックのヒアリングは「最初の送金」を起点に聞く。
         報告書HTMLからは取り出せないので、必要な項目だけ申込に残す。
         古い順に並べておき、先頭を最初の送金として扱う。 */
      formData.txSummary = list.map(i => ({
        txid: i.txid,
        chain: i.result.chain,
        blockTime: i.result.blockTime,
        amount: i.result.amount,
        tokenSymbol: i.result.tokenSymbol || null,
        tokenAmount: i.result.tokenAmount || null,
        sender: i.result.sender || (i.result.path && i.result.path[0] && i.result.path[0].address) || null,
        exchange: (i.result.exchanges && i.result.exchanges[0] && i.result.exchanges[0].name) || null,
      })).sort((a, b) => new Date(a.blockTime || 0) - new Date(b.blockTime || 0));
      saveTxidForms();

      // ブランド別の納品処理
      if (formData.brand === 'connection') {
        // Connection：サポートチャットを開設
        const chatToken = crypto.randomUUID();
        const chatUrl   = `${BASE_URL}/support/${chatToken}`;
        connectionChats.set(chatToken, {
          txid: list.map(l => l.txid).join(', '), chain: list[0].chain,
          customerName: formData.customerName, email: formData.email, reportUrl,
          reportSummary: buildReport(list[0].result).slice(0, 3000),
          messages: [], createdAt: Date.now(),
        });
        saveConnectionChats();
        // Connectionはサポートチャットも案内する
        formData.report.chatUrl = chatUrl;
        // メールでも案内（Railwayのメール不達時はブラウザ表示でカバー）
        if (formData.email) {
          sendEmail(
            formData.email,
            '【Connection】正式調査報告書が完成しました',
            buildConnectionEmailHTML(formData.customerName, reportUrl, chatUrl, issuedAt)
          ).catch(console.error);
        }
      } else if (formData.email) {
        sendEmail(
          formData.email,
          '【BitTo】詳細調査レポートが完成しました',
          buildReportEmailHTML(formData.customerName, reportUrl, issuedAt,
            (formData.brand !== 'connection') ? `${BASE_URL}/hearing/${token}` : ''),
          'bitto'   // 渡さないと送信元が Connection 名義になる（迷惑メール判定の一因）
        ).catch(console.error);
      }

    } catch (e) {
      formData.status = 'error';
      formData.errorMsg = e.message;
      console.error('[Submit] エラー:', e.message);
      if (formData.userId) {
        lineClient.pushMessage(formData.userId, {
          type: 'text', text: `⚠️ レポート生成エラー\n${e.message}\nサポートにご連絡ください`,
        }).catch(() => {});
      }
    }
  })();
});

// テスト用プレビューレポート（決済・LINE不要）
// アクセス: /report/preview
// Gemini AIをスキップ: /report/preview?ai=0
app.get('/report/preview', async (req, res) => {
  const issuedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  const mockList = [{
    txid: 'a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2',
    chain: 'btc',
    result: {
      chain: 'BTC',
      txid: 'a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2',
      blockTime: '2024-11-03 12:34:56',
      blockHeight: 868421,
      amount: 0.52341200,
      fee: 0.00003210,
      sender: '1A2B3C4D5E6F7G8H9I0Jabcdefghijkl123456',
      senderLabel: '',
      path: [
        {
          address: '1A2B3C4D5E6F7G8H9I0Jabcdefghijkl123456',
          label: '', role: 'sender', isExchange: false,
          balance: 0.00012340, txCount: 3, balanceUSD: 8.45,
        },
        {
          address: '1RelayMidAddr9XXXXXXXXXXXXXXXXXXXXXXXX',
          label: '', role: 'relay', isExchange: false,
          amount: 0.52341200, time: '2024-11-03 12:41:00',
          balance: 0.00000120, txCount: 2, balanceUSD: 0.08,
        },
        {
          address: '34xp4vRocGJym3xR7yCVpFHoCNxv4twsEo',
          label: 'Binance Hot Wallet', role: 'exchange', isExchange: true,
          amount: 0.52338000, time: '2024-11-03 13:02:15',
          balance: 12500.85, txCount: 1250000, balanceUSD: 857083200,
        },
      ],
      exchanges: [{ name: 'Binance Hot Wallet', address: '34xp4vRocGJym3xR7yCVpFHoCNxv4twsEo', amount: 0.52338000 }],
    },
  }];

  let aiData = { analysis: null, requests: [] };
  if (req.query.ai !== '0' && GEMINI_KEY) {
    console.log('[Preview] Gemini AI 生成中...');
    // プレビューは運営自身の確認用なので失敗通知メールは送らない
    aiData = await generateAIContent(mockList, 'テストユーザー', { notify: false }).catch(() => ({ analysis: null, requests: [] }));
  }

  const brand = req.query.brand === 'connection' ? 'connection' : 'bitto';
  const html = generateReportHTML(mockList, 'テストユーザー（プレビュー）', issuedAt, aiData, '', brand);
  res.setHeader('Content-Type', 'text/html; charset=utf-8');
  res.send(html);
});

// 有料レポートページ（ファイル優先 → メモリキャッシュのフォールバック）
/* 報告書のPDF。/report/:id より先に置くこと（後だと :id が "xxx.pdf" に食われる）。
   まだ生成できていない場合はその場で作る（既存の報告書にも後から効かせるため）。 */
app.get('/report/:id.pdf', async (req, res) => {
  const id = req.params.id;
  const file = path.join(REPORTS_DIR, `${id}.pdf`);
  if (!fs.existsSync(file)) {
    if (!(await loadReport(id))) return res.status(404).send('レポートが見つかりません');
    try {
      await generateReportPdf(id);
    } catch (e) {
      console.error('[PDF] 要求時の生成に失敗:', e.message);
      return res.status(500).send('PDFを作成できませんでした。ページ上部の「PDF保存 / 印刷」をお試しください。');
    }
  }
  res.setHeader('Content-Type', 'application/pdf');
  res.setHeader('Content-Disposition', `attachment; filename="BitTo-report-${id}.pdf"`);
  fs.createReadStream(file).pipe(res);
});

app.get('/report/:id', async (req, res) => {
  const html = await loadReport(req.params.id);
  if (!html) {
    return res.status(404).send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><title>レポートが見つかりません</title>
<style>body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:40px;max-width:400px}
h1{color:#f87171;font-size:1.3rem;margin-bottom:12px}.icon{font-size:3rem;margin-bottom:16px}p{color:#94a3b8;line-height:1.7}</style></head>
<body><div class="card"><div class="icon">⚠️</div><h1>レポートが見つかりません</h1>
<p>URLの有効期限が切れているか、リンクが正しくありません。<br><br>ご不明な点はLINEにてお問い合わせください。</p></div></body></html>`);
  }
  res.setHeader('Content-Type', 'text/html; charset=utf-8');
  res.send(html);
});

// ══════════════════════════════════════════════════════════════
// Connection — Web版 資金追跡アプリ（BitToと同一エンジン・別ブランド）
// 価格：1TXID ¥11,000（税込）／正式報告書＋専任サポートチャット付
// ══════════════════════════════════════════════════════════════
const CONNECTION_PRICE = 11000;

// ── 調査ジョブ（非同期実行＋ポーリング） ──────────────────────
const connectionJobs = new Map(); // jobId → { status, txid, chain, result, error, createdAt }
setInterval(() => {
  const cutoff = Date.now() - 3600000;
  for (const [id, job] of connectionJobs) if (job.createdAt < cutoff) connectionJobs.delete(id);
}, 600000);

// ── 簡易レート制限（IPごと 調査30回/時） ──────────────────────
// 8回/時では通常利用や動作確認の途中で遮断され、利用者からは「調査が出ない」と
// 見分けがつかないため引き上げた。携帯回線はCGNATで多数の利用者が同一IPになる点にも配慮。
/* 1時間の上限だけだと、30回×24時間＝720回まで回せてしまう。
   外部APIとGeminiの費用がそのまま出ていくので、1日の上限も置く。
   携帯回線はCGNATで多数の利用者が同一IPになるため、日次は緩めにする。 */
const connRateMap = new Map();
const CONN_LIMIT_HOUR = 30;
const CONN_LIMIT_DAY  = 80;
function connRateOk(ip) {
  const now = Date.now();
  const arr = (connRateMap.get(ip) || []).filter(t => now - t < 86400000);
  connRateMap.set(ip, arr);
  if (arr.filter(t => now - t < 3600000).length >= CONN_LIMIT_HOUR) return false;
  if (arr.length >= CONN_LIMIT_DAY) return false;
  arr.push(now);
  return true;
}
// 溜まりっぱなしにしない（1日経った記録は捨てる）
setInterval(() => {
  const cutoff = Date.now() - 86400000;
  for (const [ip, arr] of connRateMap) {
    const keep = arr.filter(t => t > cutoff);
    if (keep.length) connRateMap.set(ip, keep); else connRateMap.delete(ip);
  }
}, 3600000);

// ── サポートチャット（購入者専用・ファイル永続化） ─────────────
const connectionChats = new Map(); // token → { txid, chain, customerName, email, reportUrl, reportSummary, messages, createdAt }
const CONN_CHATS_FILE = path.join(REPORTS_DIR, 'connection-chats.json');
try {
  const saved = JSON.parse(fs.readFileSync(CONN_CHATS_FILE, 'utf8'));
  for (const [k, v] of Object.entries(saved)) connectionChats.set(k, v);
  console.log(`[Connection] サポートチャット${connectionChats.size}件を復元`);
} catch {}
function saveConnectionChats() {
  fsp.writeFile(CONN_CHATS_FILE, JSON.stringify(Object.fromEntries(connectionChats)), 'utf8')
    .catch(e => console.error('[Connection] チャット保存失敗:', e.message));
}

// ── 注文処理（Stripe webhook / テストモード共通） ──────────────
async function fulfillConnectionOrder({ txid, customerName, email, count = 1 }) {
  console.log(`[Connection] 注文処理開始: ${txid} / ${email} / ${count}件`);

  // 複数件の場合はTXID入力フォームを発行してメールで案内
  if (count > 1) {
    const formToken = crypto.randomUUID();
    txidFormTokens.set(formToken, {
      sessionId: `connection-${formToken.slice(0, 8)}`, userId: '', count,
      customerName, email, brand: 'connection', used: false, createdAt: Date.now(),
    });
    const formUrl = `${BASE_URL}/txid-form/${formToken}`;
    if (email) {
      await sendEmail(email, '【Connection】調査するTXIDのご入力をお願いします',
        buildConnectionTxidFormEmailHTML(customerName, formUrl, count));
    }
    console.log(`[Connection] TXIDフォーム発行: ${formUrl}`);
    return { formUrl };
  }

  const chain = detectChain(txid);
  if (!chain) throw new Error('TXIDの形式が不正です');

  const cacheKey = txid.toLowerCase();
  let result = txidCache.get(cacheKey)?.result;
  if (!result) {
    result = await investigate(txid, chain);
    txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
  }

  const list     = [{ txid, chain, result }];
  const issuedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  const aiData   = await generateAIContent(list, customerName).catch(() => ({ analysis: null, requests: [] }));
  const reportId  = crypto.randomUUID();
  const reportUrl = `${BASE_URL}/report/${reportId}`;
  await saveReport(reportId, generateReportHTML(list, customerName, issuedAt, aiData, reportUrl, 'connection'));

  // サポートチャットを開設
  const chatToken = crypto.randomUUID();
  const chatUrl   = `${BASE_URL}/support/${chatToken}`;
  connectionChats.set(chatToken, {
    txid, chain, customerName, email, reportUrl,
    reportSummary: buildReport(result).slice(0, 3000),
    messages: [], createdAt: Date.now(),
  });
  saveConnectionChats();

  if (email) {
    await sendEmail(email, '【Connection】正式調査報告書が完成しました',
      buildConnectionEmailHTML(customerName, reportUrl, chatUrl, issuedAt));
  }
  console.log(`[Connection] 注文処理完了: ${reportUrl}`);
  return { reportUrl, chatUrl };
}

function buildConnectionTxidFormEmailHTML(name, formUrl, count) {
  return `<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"></head>
<body style="margin:0;background:#0a0c12;font-family:'Hiragino Mincho ProN','Yu Mincho',serif;padding:32px 16px">
<div style="max-width:560px;margin:0 auto;background:#12151f;border:1px solid #2a3045;border-radius:12px;overflow:hidden">
  <div style="padding:36px 32px 28px;text-align:center;border-bottom:1px solid #2a3045">
    <div style="font-size:30px;letter-spacing:3px;color:#c9a96e;font-weight:600;font-family:Georgia,'Times New Roman',serif">Connection</div>
    <div style="margin:14px auto 0;color:#c9a96e;font-size:11px;letter-spacing:2px">──────&nbsp;✦&nbsp;──────</div>
  </div>
  <div style="padding:32px;color:#eae6dc;font-size:14px;line-height:2">
    <p style="margin:0 0 18px">${name} 様</p>
    <p style="margin:0 0 18px">この度はConnectionをご利用いただき、誠にありがとうございます。<br>お支払いを確認いたしました。</p>
    <p style="margin:0 0 18px">以下のフォームより、調査をご希望のTXIDを<strong style="color:#c9a96e">${count}件</strong>ご入力ください。<br>ご入力後、順次調査を行い正式調査報告書をお送りいたします。</p>
    <div style="text-align:center;margin:28px 0">
      <a href="${formUrl}" style="display:inline-block;background:#c9a96e;color:#0a0c12;text-decoration:none;padding:14px 40px;border-radius:6px;font-weight:700;letter-spacing:2px">TXIDを入力する</a>
    </div>
    <p style="margin:18px 0 0;font-size:12px;color:#8b91a0">⚠️ このフォームは1回のみご使用いただけます。<br>すでに追跡調査済みのTXIDも含めてご入力ください。</p>
  </div>
</div>
</body></html>`;
}

function buildConnectionEmailHTML(name, reportUrl, chatUrl, issuedAt) {
  return `<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"></head>
<body style="margin:0;background:#0a0c12;font-family:'Hiragino Mincho ProN','Yu Mincho',serif;padding:32px 16px">
<div style="max-width:560px;margin:0 auto;background:#12151f;border:1px solid #2a3045;border-radius:12px;overflow:hidden">
  <div style="padding:36px 32px 28px;text-align:center;border-bottom:1px solid #2a3045">
    <div style="font-size:30px;letter-spacing:3px;color:#c9a96e;font-weight:600;font-family:Georgia,'Times New Roman',serif">Connection</div>
    <div style="margin:14px auto 0;color:#c9a96e;font-size:11px;letter-spacing:2px">──────&nbsp;✦&nbsp;──────</div>
  </div>
  <div style="padding:32px;color:#eae6dc;font-size:14px;line-height:2">
    <p style="margin:0 0 18px">${name} 様</p>
    <p style="margin:0 0 18px">この度はConnectionをご利用いただき、誠にありがとうございます。<br>ご依頼いただいた正式調査報告書が完成いたしました。</p>
    <div style="text-align:center;margin:28px 0">
      <a href="${reportUrl}" style="display:inline-block;background:#c9a96e;color:#0a0c12;text-decoration:none;padding:14px 40px;border-radius:6px;font-weight:700;letter-spacing:2px">調査報告書を確認する</a>
    </div>
    <div style="background:#0e1119;border:1px solid #2a3045;border-radius:8px;padding:20px 24px;margin:24px 0">
      <p style="margin:0 0 8px;color:#c9a96e;font-size:13px;letter-spacing:2px">専任サポートチャット</p>
      <p style="margin:0 0 12px;font-size:13px;color:#b8bcc8">報告書の内容に関するご質問、凍結要請や警察への提出手順など、<br>専任サポートがいつでもご相談を承ります。</p>
      <a href="${chatUrl}" style="color:#c9a96e;font-size:13px">${chatUrl}</a>
    </div>
    <p style="margin:18px 0 0;font-size:12px;color:#8b91a0">発行日時：${issuedAt}<br>このメールは大切に保管してください。</p>
  </div>
</div>
</body></html>`;
}

// ── ページ配信 ────────────────────────────────────────────────
app.get('/connection', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection.html')));
// BitTo：チャット型の無料追跡UI（アプリ化の土台）
app.get('/bitto', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto.html')));
app.get('/privacy', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-privacy.html')));
app.get('/connection/privacy', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-privacy.html')));
app.get('/bitto/privacy', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-privacy.html')));
app.get('/bitto-privacy', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-privacy.html')));

// ── データ削除ページ（Google Playアカウント削除要件：公開URLとフォーム） ──
app.get('/data-deletion', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-data-deletion.html')));
app.get('/connection/data-deletion', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-data-deletion.html')));
app.get('/bitto/data-deletion', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-data-deletion.html')));
app.get('/bitto-data-deletion', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-data-deletion.html')));

// TXIDの見つけ方ガイド
app.get('/bitto/txid-guide', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-txid-guide.html')));
app.get('/bitto/txid', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'bitto-txid-guide.html')));
app.get('/connection/txid-guide', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-txid-guide.html')));
app.get('/connection/txid', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'connection-txid-guide.html')));
// NOTE: no bare '/txid-guide' route — it collides with the static public/txid-guide/ image dir.
// Canonical URLs are /bitto/txid-guide and /connection/txid-guide.

// データ削除リクエストの受付（運営に通知＋申請者に受付確認）
app.post('/api/data-deletion-request', express.json(), async (req, res) => {
  try {
    const esc = s => String(s || '').replace(/[<>&"]/g, c => ({ '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;' }[c]));
    const name   = esc((req.body.name || '').toString().trim().slice(0, 100));
    const email  = (req.body.email || '').toString().trim().slice(0, 200);
    const detail = esc((req.body.detail || '').toString().trim().slice(0, 1000));
    if (!name)  return res.status(400).json({ error: 'お名前が未入力です' });
    if (!email || !/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email)) return res.status(400).json({ error: 'メールアドレスの形式が正しくありません' });
    const brand = req.body.brand === 'bitto' ? 'BitTo' : 'Connection';
    const at = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    const CONTACT = 'himesen.inc2512@gmail.com';
    // 運営へ通知
    await sendEmail(CONTACT, `【${brand}】データ削除のご請求`,
      `<p>データ削除のご請求を受け付けました。本人確認のうえ対応してください。</p>
       <table style="border-collapse:collapse;font-size:14px">
         <tr><td style="padding:4px 10px;color:#64748b">受付日時</td><td style="padding:4px 10px">${at}</td></tr>
         <tr><td style="padding:4px 10px;color:#64748b">お名前</td><td style="padding:4px 10px">${name}</td></tr>
         <tr><td style="padding:4px 10px;color:#64748b">メール</td><td style="padding:4px 10px">${esc(email)}</td></tr>
         <tr><td style="padding:4px 10px;color:#64748b;vertical-align:top">詳細</td><td style="padding:4px 10px;white-space:pre-wrap">${detail || '（記載なし）'}</td></tr>
       </table>`,
      brand
    ).catch(e => console.error('[DataDeletion] 運営通知失敗:', e.message));
    // 申請者へ受付確認
    await sendEmail(email, `【${brand}】データ削除のご請求を受け付けました`,
      `<p>${name} 様</p>
       <p>この度は、データ削除のご請求をいただきありがとうございます。以下の内容で受け付けいたしました。</p>
       <p>本人確認のうえ、原則30日以内に対象データを削除し、完了のご連絡をお送りいたします。<br>
       なお、法令上の保存義務がある取引・会計記録は、法定期間の経過後に消去いたします。</p>
       <p style="color:#64748b;font-size:13px">受付日時：${at}</p>
       <p style="color:#64748b;font-size:13px">本メールにお心当たりがない場合は、破棄してください。</p>
       <p>${brand}（Himesen株式会社）</p>`,
      brand
    ).catch(e => console.error('[DataDeletion] 申請者確認失敗:', e.message));
    console.log(`[DataDeletion] 受付(${brand}): ${name} / ${email}`);
    res.json({ ok: true });
  } catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/support/:token', (req, res) => {
  if (!connectionChats.has(req.params.token)) {
    return res.status(404).send('<!DOCTYPE html><html lang="ja"><body style="background:#0a0c12;color:#eae6dc;font-family:serif;display:flex;align-items:center;justify-content:center;min-height:100vh"><div style="text-align:center"><p style="letter-spacing:2px;color:#c9a96e;font-size:24px">Connection</p><p>このサポートチャットは見つかりませんでした。</p></div></body></html>');
  }
  res.sendFile(path.join(__dirname, 'public', 'connection-support.html'));
});
app.get('/connection/success', (_req, res) => res.send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>お申し込み完了 — Connection</title>
<style>
body{margin:0;background:#0a0c12;color:#eae6dc;font-family:'Hiragino Mincho ProN','Yu Mincho',serif;display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}
.card{background:#12151f;border:1px solid #2a3045;border-radius:14px;padding:48px 36px;max-width:460px;width:100%;text-align:center}
.logo{font-family:Georgia,'Times New Roman',serif;font-size:30px;letter-spacing:2px;font-weight:600;background:linear-gradient(180deg,#f0e2b6,#c9a96e 60%,#a8854a);-webkit-background-clip:text;background-clip:text;color:transparent}
.rule{color:#c9a96e;font-size:11px;letter-spacing:2px;margin:14px auto 28px}
h1{font-size:18px;font-weight:600;margin:0 0 16px}
p{font-size:13.5px;line-height:2;color:#b8bcc8;margin:0 0 12px}
</style></head><body>
<div class="card">
  <div class="logo">Connection</div>
  <div class="rule">──────&nbsp;✦&nbsp;──────</div>
  <h1>お申し込みが完了しました</h1>
  <p>正式調査報告書の作成を開始いたしました。<br>完成次第、ご登録のメールアドレスへ<br>報告書と専任サポートチャットのご案内をお送りします。</p>
  <p style="font-size:12px;color:#8b91a0">通常10分〜30分ほどで完成します。<br>メールが届かない場合は迷惑メールフォルダをご確認ください。</p>
</div>
</body></html>`));

// ── 調査API ──────────────────────────────────────────────────
app.post('/api/connection/investigate', express.json(), async (req, res) => {
  const txid  = (req.body.txid || '').trim();
  const chain = detectChain(txid);
  if (!chain) return res.status(400).json({ error: 'TXIDの形式が正しくありません。64文字のトランザクションIDをご入力ください。' });
  const ip = (req.headers['x-forwarded-for'] || '').split(',')[0].trim() || req.ip || '';
  if (!connRateOk(ip)) return res.status(429).json({ error: '調査回数の上限に達しました。しばらく時間をおいてお試しください。' });

  const jobId = crypto.randomUUID();
  connectionJobs.set(jobId, { status: 'running', txid, chain, createdAt: Date.now() });
  (async () => {
    try {
      const cacheKey = txid.toLowerCase();
      let result = txidCache.get(cacheKey)?.result;
      if (!result) {
        // 内部の時間予算をすり抜けて investigate() が固まると、ジョブが running のまま残り
        // クライアントは永久に「解析中」になる。最後の砦として全体に上限時間を課し、
        // 必ず done か error のどちらかで終わらせる。
        result = await Promise.race([
          investigate(txid, chain),
          new Promise((_, reject) => setTimeout(
            () => reject(new Error('調査が時間内に完了しませんでした。時間をおいてもう一度お試しください。')),
            INVESTIGATE_HARD_TIMEOUT_MS
          )),
        ]);
        txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
      }
      const job = connectionJobs.get(jobId);
      if (job) { job.status = 'done'; job.result = result; }
    } catch (e) {
      console.error('[Connection] 調査エラー:', e.message);
      const job = connectionJobs.get(jobId);
      if (job) { job.status = 'error'; job.error = e.message; }
    }
  })();
  res.json({ jobId, chain: chain.toUpperCase() });
});

app.get('/api/connection/job/:id', (req, res) => {
  const job = connectionJobs.get(req.params.id);
  // 不明なジョブ（保存期間切れ or サーバー再起動で消失）。旧BitToアプリ(1.0)は 404 を
  // 握りつぶして無限ポーリング＝ハングするため、200 + status:error で返し、
  // どのクライアントでも「エラー表示して停止」できるようにする（Connection/新BitToはerrorを処理済）。
  if (!job) return res.json({ status: 'error', error: '調査データが見つかりませんでした（保存期間切れ、またはサーバー更新の可能性）。お手数ですが、もう一度TXIDを送信してください。' });
  res.json({ status: job.status, result: job.status === 'done' ? job.result : undefined, error: job.error });
});

// ── ウォレット詳細API（ノードクリック時） ──────────────────────
app.get('/api/connection/address/:addr', async (req, res) => {
  try {
    const addr  = req.params.addr;
    const chain = String(req.query.chain || 'eth').toLowerCase();
    const info  = await getAddressInfo(addr, chain);
    const db    = getLabel(addr);
    const fetched = await fetchAddressLabel(addr, chain).catch(() => '');
    const label = fetched || db.label || info?.bcLabel || '';
    const isEx  = db.type === 'exchange' || isExchange(label);

    let txs = [];
    if (chain === 'eth' && ETHERSCAN_KEY) {
      const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${addr}&page=1&offset=10&sort=desc&apikey=${ETHERSCAN_KEY}`;
      const j = await (await fetch(url)).json();
      txs = (Array.isArray(j.result) ? j.result : []).map(t => ({
        hash: t.hash, from: t.from, to: t.to,
        value: parseFloat(t.value) / 1e18, unit: 'ETH',
        time: new Date(parseInt(t.timeStamp) * 1000).toISOString(),
        direction: t.from.toLowerCase() === addr.toLowerCase() ? 'out' : 'in',
      }));
    } else if (chain === 'xrp') {
      const j = await (await fetch(`https://api.xrpscan.com/api/v1/account/${addr}/transactions`)).json();
      txs = (j.transactions || []).slice(0, 10).map(t => ({
        hash: t.hash, from: t.Account, to: t.Destination || '',
        value: parseFloat(t.Amount) / 1e6 || 0, unit: 'XRP',
        time: t.date, direction: t.Account === addr ? 'out' : 'in',
      }));
    } else if (chain === 'btc' && BLOCKCHAIR_KEY) {
      const j = await (await fetch(`https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}&limit=10`)).json();
      const hashes = j.data?.[addr]?.transactions || [];
      txs = hashes.slice(0, 10).map(h => ({ hash: h, from: '', to: '', value: null, unit: 'BTC', time: '', direction: '' }));
    }

    let type = 'wallet';
    if (isEx) type = 'exchange';
    else if (info?.txCount != null && info.txCount >= 50000) type = 'hot_wallet';

    res.json({
      address: addr, chain: chain.toUpperCase(), label, isExchange: isEx, type,
      balance: info?.balance ?? null, balanceUSD: info?.balanceUSD ?? null,
      txCount: info?.txCount ?? null, txs,
    });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

// ── 決済API（¥11,000／1TXID） ─────────────────────────────────
app.post('/api/connection/checkout', express.json(), async (req, res) => {
  try {
    const { txid, name, email, phone, count } = req.body;
    const t = (txid || '').trim();
    const n = Math.max(1, Math.min(10, parseInt(count) || 1));
    const amount = CONNECTION_PRICE * n;
    if (!email) return res.status(400).json({ error: 'メールアドレスを入力してください' });

    // 決済後に表示するTXID入力フォームのトークンを先に発行
    const formToken = crypto.randomUUID();
    const sessionId = `connection-${formToken.slice(0, 8)}`;
    txidFormTokens.set(formToken, {
      sessionId, userId: '', count: n,
      customerName: name || 'お客様', email, phone: phone || '',
      brand: 'connection', used: false, createdAt: Date.now(),
      prefillTxid: t, status: 'paid_waiting_txid',
    });
    const formUrl = `${BASE_URL}/txid-form/${formToken}`;

    // 申込記録をSheetsへ
    const submittedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    appendToSheet([
      submittedAt, name || '', phone || '', email, '', String(n),
      String(amount), sessionId, '', '申込済み(Connection)',
    ]).catch(console.error);

    if (!stripe) {
      // テストモード：決済を飛ばして直接TXID入力フォームへ
      return res.json({ url: formUrl });
    }

    const session = await stripe.checkout.sessions.create({
      payment_method_types: ['card'],
      customer_email: email,
      line_items: [{
        price_data: {
          currency: 'jpy',
          product_data: {
            name:        `Connection 正式調査報告書（${n}件）`,
            description: 'ブロックチェーン資金追跡調査・正式報告書＋専任サポートチャット',
          },
          unit_amount: CONNECTION_PRICE,
        },
        quantity: n,
      }],
      mode: 'payment',
      success_url: formUrl,                       // 決済後はTXID入力フォームへ遷移
      cancel_url:  `${BASE_URL}/connection`,
      metadata: { brand: 'connection', formToken, customerName: name || '', email, phone: phone || '', count: String(n) },
    });
    res.json({ url: session.url });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

// ── サポートチャットAPI ────────────────────────────────────────
app.get('/api/connection/chat/:token', (req, res) => {
  const chat = connectionChats.get(req.params.token);
  if (!chat) return res.status(404).json({ error: 'チャットが見つかりません' });
  res.json({ customerName: chat.customerName, reportUrl: chat.reportUrl, messages: chat.messages });
});

app.post('/api/connection/chat/:token', express.json(), async (req, res) => {
  try {
    const chat = connectionChats.get(req.params.token);
    if (!chat) return res.status(404).json({ error: 'チャットが見つかりません' });
    const message = (req.body.message || '').trim().slice(0, 2000);
    if (!message) return res.status(400).json({ error: 'メッセージが空です' });

    const isFirst = chat.messages.filter(m => m.role === 'user').length === 0;
    chat.messages.push({ role: 'user', text: message, at: Date.now() });

    // 初回メッセージは運営者にも通知
    if (isFirst && SMTP_USER) {
      sendEmail(SMTP_USER, '【Connection】サポートチャットに新規お問い合わせ',
        `<p>お客様：${chat.customerName} 様（${chat.email}）</p><p>TXID：${chat.txid}</p><p>メッセージ：${message}</p><p><a href="${BASE_URL}/support/${req.params.token}">チャットを開く</a></p>`
      ).catch(console.error);
    }

    let reply = 'お問い合わせありがとうございます。担当者が確認のうえ、ご登録のメールアドレスへご回答いたします。';
    if (GEMINI_KEY) {
      const history = chat.messages.slice(-12).map(m => `${m.role === 'user' ? 'お客様' : 'サポート'}：${m.text}`).join('\n');
      const prompt = `あなたは暗号資産の資金追跡調査サービス「Connection」の専任サポート担当です。
お客様は正式調査報告書（¥11,000）をご購入済みの大切なお客様です。

【お客様情報】お名前：${chat.customerName} 様
【調査対象TXID】${chat.txid}
【調査結果の要約】
${chat.reportSummary}

【対応方針】
- 丁寧で落ち着いた敬語。高級サービスにふさわしい上質な対応
- 調査結果の見方、取引所への凍結要請の進め方、警察への被害届提出の流れを具体的に案内する
- 法律判断が必要な内容は弁護士への相談を推奨する
- 被害回復を保証する表現は絶対に使わない
- わからないことは正直に伝え、担当者からのメール回答を案内する
- 回答は400文字以内

【これまでの会話】
${history}

サポート担当としての返信のみを出力してください。`;
      const text = await geminiGenerate(prompt, { temperature: 0.4, maxOutputTokens: 600 });
      if (text) reply = text;
    }

    chat.messages.push({ role: 'assistant', text: reply, at: Date.now() });
    saveConnectionChats();
    res.json({ reply });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

// ── 初回相談AI（購入前・無料・匿名） ──────────────────────────
// 返金可能性を問われたときに必ず提示する説明。法的に重要なため、AIの裁量に委ねず常に定型文を前置する。
const REFUND_NOTICE = `【返金の可能性について】
暗号資産は、銀行振込の詐欺で使われる「振り込め詐欺救済法（被害回復分配法）」の対象外です。同法は預金口座を対象とした制度で、暗号資産交換業者の口座は預金口座にあたらないため、法律に基づいて自動的に返金・分配される仕組みはありません。

そのうえで、現実的に取り得る道すじは次のとおりです。
① 記録の保全（TXID、相手とのやり取り、送金履歴、相手の情報のスクリーンショット）
② 資金の追跡と、到達した取引所の特定
③ 特定できた取引所への連絡・凍結の要請（凍結するかどうかは取引所の判断です）
④ 警察への相談・被害届（各都道府県警のサイバー犯罪相談窓口、または最寄りの警察署）

弁護士へのご相談も選択肢の一つです。ただし暗号資産には返金分配の法的枠組みが無いため、対応できる範囲が限られる場合があります。まずは②③④を優先してご検討ください。
※制度の一般的な説明であり、個別の法律判断ではありません。`;

const consultRateMap = new Map(); // IP → timestamps[]
app.post('/api/connection/consult', express.json(), async (req, res) => {
  try {
    // IPレート制限：30メッセージ/時
    const ip = (req.headers['x-forwarded-for'] || req.ip || 'unknown').toString().split(',')[0].trim();
    const now = Date.now();
    const hist = (consultRateMap.get(ip) || []).filter(t => now - t < 3600000);
    if (hist.length >= 30) return res.status(429).json({ error: 'ご相談が混み合っています。しばらくしてから再度お試しください。' });
    hist.push(now); consultRateMap.set(ip, hist);

    const message = (req.body.message || '').trim().slice(0, 2000);
    if (!message) return res.status(400).json({ error: 'メッセージが空です' });
    const messages = Array.isArray(req.body.messages) ? req.body.messages.slice(-10) : [];
    const ctx = req.body.context || null;
    // ブランド別のAIペルソナ（BitToは無料アプリ＝有料商品の案内をしない）
    const brand = req.body.brand === 'bitto' ? 'bitto' : 'connection';

    // 追跡結果の文脈を組み立て
    let caseInfo = '（まだ追跡を行っていない、または追跡情報なし）';
    if (ctx && ctx.chain) {
      const exNames = (ctx.exchanges || []).filter(Boolean).join('、');
      // 取引所の特定状況を曖昧さなく伝える（凍結要請状は「名称判明」時のみ作成可能）
      let exState, freezeLetter;
      const isBitto = brand === 'bitto';
      if (exNames) {
        exState = `判明（${exNames}）`;
        freezeLetter = isBitto
          ? `判明した取引所（${exNames}）へ、ご相談者ご自身で連絡し凍結を要請できます。※BitToは書面を作成しません`
          : '作成できます（宛先の取引所が判明しているため）';
      } else if (ctx.reachedExchange) {
        exState = '推定（取引所系とみられるウォレットに到達したが、名称は特定できていない）';
        freezeLetter = isBitto
          ? '要請先の取引所を特定できないため、現時点では凍結要請ができません'
          : '作成できません（宛先の取引所を特定できないため）';
      } else {
        exState = '未特定（既知のラベル情報が無く特定できない。※取引所に到達していないとは限らない）';
        freezeLetter = isBitto
          ? '要請先の取引所を特定できないため、現時点では凍結要請ができません'
          : '作成できません（宛先の取引所を特定できないため）';
      }
      const freezeLabel = isBitto ? '取引所への凍結要請' : '凍結要請状';
      caseInfo = `チェーン：${ctx.chain}\n送金額：${ctx.amount || '不明'}\n経由数：${ctx.hops != null ? ctx.hops + '段階' : '不明'}\n取引所の特定状況：${exState}\n${freezeLabel}：${freezeLetter}\nDEX・ブリッジ経由の可能性：${ctx.viaDex ? 'あり（最終特定が難しい場合があります）' : '低い'}`;
    }

    // 「返金の可能性」を尋ねられたかはコード側で判定する（プロンプト内の条件分岐はモデルが誤読するため）
    const asksRefund = /戻っ|戻る|戻り|戻せ|もど|取り戻|返金|返って|返済|回収|リカバリ|取返|取り返/.test(message);
    let reply = 'ただいまAIの応答が混み合っています。恐れ入りますが、少し時間をおいてもう一度お試しください。';
    if (GEMINI_KEY) {
      const refundBlock = asksRefund
        ? `【重要】この質問は「返金の可能性」に関するものです。
返金制度についての定型の説明文（振り込め詐欺救済法／被害回復分配法が暗号資産に適用されないこと、①〜④の道すじ、弁護士について）は、**あなたの回答の前に自動で挿入されます**。
したがって、**あなたはその内容を一切繰り返さないでください**（「振り込め詐欺救済法」「被害回復分配法」「弁護士」という語を書かない）。
あなたが書くのは、上の【ご相談者の追跡結果】に当てはめた「このケースで次に何をすべきか」だけです。**3文以内・200文字以内**の箇条書きで簡潔に。`
        : `【この質問は「返金の可能性」に関するものではありません】
- 「振り込め詐欺救済法」「返金・分配の制度」「弁護士」の一般説明は**書かないでください**。
- ご相談者が尋ねた事柄にだけ、直接お答えください。
- 全体450文字以内。`;
      const history = messages.map(m => `${m.role === 'user' ? 'ご相談者' : '相談員'}：${m.text}`).join('\n');
      const bittoPrompt = `あなたは暗号資産の資金追跡サービス「BitTo」の調査AIです。
詐欺被害などで不安を抱えた方が多いので、まず安心していただくことを最優先にしてください。

【サービス概要】
- TXID（取引ID）を送ると、資金の流れを追跡して可視化します（追跡は無料）
- 対応チェーン：ビットコイン(BTC)／イーサリアム(ETH)／XRP
- 到達した取引所の候補を「判明／推定／未特定」に分けて表示します
- 警察・取引所に相談する際の正式な書面が必要な方には、任意で「正式調査報告書」（税込¥6,600・買い切り／1TXID）をご用意しています。取引所への資産凍結要請、警察・弁護士へ相談する際の調査報告書、AI総合分析、購入後のサポートを含みます

【ご相談者の追跡結果】
${caseInfo}

【対応方針】
- 丁寧で落ち着いた敬語。寄り添う対応
- 名乗りは「BitToの調査AI」のみ。個人名・架空の氏名・伏字は絶対に使わない
- 毎回挨拶を繰り返さず、会話が続いている場合は自然に本題へ
- 上記の追跡結果を踏まえ、その方のケースに即して具体的に説明する
- 取引所が「判明」している場合：その取引所への連絡・凍結要請と、警察への相談を案内する
- 取引所が「推定」「未特定」の場合：**ラベル情報が無いだけで、到達していないとは限らない**と正直に説明する。断定しない
- DEX・海外取引所・匿名化を経由している場合は、最終特定が難しい可能性を正直に伝える
- 被害の回復・資産の奪還・犯人特定・凍結を「保証」する表現は絶対に使わない
- 法律判断・返金交渉の代行はしない（弁護士法に配慮）。制度の一般的な説明にとどめる
- 画面上の追跡結果は無料。正式な書面が必要な場合のみ、任意で正式調査報告書（税込¥6,600・買い切り）を自然にご案内する（押し売りはしない）
- 取引所名が**判明**している場合：報告書に取引所向けの資産凍結要請を添えられること、警察への相談時に使える資料になることを前向きに伝える。ただし凍結の可否は取引所の判断であり、返金・資産回収を保証しないことも正直に添える
- 取引所名が**推定・未特定**の場合：資産凍結要請は作成できないと正直に伝え、報告書の価値は「資金経路の客観的な記録」「警察へ相談する際の資料」に限定して説明する（過大な期待を持たせない）
- 報告書の用途を述べるときは「提出」という語を使わず、「相談する際の資料」「判断材料」と表現する。何が証拠として採用されるかは捜査機関が決めることであり、こちらが約束できないため
- 高額な着手金や成功報酬を求める他社と異なり、BitToの報告書は税込¥6,600の買い切り1回のみで追加請求はない。この違いは、押し売りにならない範囲で正直に伝えてよい
- TXIDの場所・見つけ方が分からない様子のときは、送金・出金履歴の詳細画面に長い英数字で表示されていることを伝え、取引所別の「TXIDの見つけ方ガイド」で確認できると案内する（画面にガイドを開くボタンが表示されます）
- 不安を煽らない



【取引所が「推定」「未特定」のときの厳格なルール】
- 「取引所に到達していない」と断定しない。**ラベル情報が無いだけで、到達していないとは限らない**と説明する
- 宛先が特定できないため、取引所への凍結要請は現時点では行えないことを正直に伝える
- できることとして「記録の保全」「警察への相談・被害届」を優先的に案内する

【これまでの相談】
${history}
ご相談者：${message}

${refundBlock}

【この返信の書き方（厳守）】
- **挨拶・お礼・自己紹介を書かない**。1文目から本題に入る
- **聞かれた質問にまっすぐ答える**。聞かれていないことを述べない
- **追跡結果を再説明しない**（利用者の画面に既に表示済み）。触れる場合は1文まで
- 箇条書きを使う。日本語

調査AIとしての返信のみを出力してください。`;

      const connectionPrompt = `あなたは暗号資産の資金追跡調査サービス「Connection」の初回相談員です。
これは正式依頼【前】の無料相談です。詐欺被害などで不安を抱えた方が多いので、まず安心していただくことを最優先にしてください。

【サービス概要】
- TXID（取引ID）を入力すると、資金の流れをフローマップで可視化（追跡は無料）
- 正式調査報告書（税込¥11,000／1TXID）には、取引所向け資産凍結要請状、警察・弁護士提出用の調査報告書、AI総合分析、購入後の専任サポートチャットが含まれます
- 対応チェーン：ビットコイン(BTC)／イーサリアム(ETH)／XRP
- 当社が担うのは「調査 → 到達した取引所の特定 → 取引所への凍結要請に使える客観的資料の作成」までです。**凍結するか否かは取引所の判断**であり、当社が凍結や返金を行うことはできません。

【ご相談者の追跡結果】
${caseInfo}

【対応方針】
- 丁寧で落ち着いた敬語。高級サービスにふさわしい、寄り添う上質な対応
- 個人名は名乗らない（「Connectionの相談員」とだけ名乗る）。「〇〇」等の伏字や架空の氏名は絶対に使わない
- 毎回挨拶を繰り返さず、会話が続いている場合は自然に本題へ
- 上記の追跡結果を踏まえ、その方のケースに即して具体的に説明する
- 取引所名が**判明**している場合：報告書に凍結要請状を添えられること、警察へ提出できる資料になることを前向きに伝える
- 取引所名が**推定・未特定**の場合：**凍結要請状は作成できません**。ラベル情報が無いだけで到達していないとは限らない旨を説明し、証拠資料としての報告書や開示請求の案内に切り替える（過大な期待を持たせない）
- DEX・海外取引所・匿名化を経由している場合は、最終特定が難しい可能性を正直に伝える
- 被害の回復・資産の奪還・犯人特定・凍結を「保証」する表現は絶対に使わない
- 法律判断・返金交渉の代行はしない（弁護士法に配慮）。制度の一般的な説明にとどめる
- 不安を煽らず、押し売りもしない。納得されたら「正式調査報告書のご依頼」を自然に案内する



【★最重要：取引所が「推定」「未特定」のときの厳格なルール】
上の【ご相談者の追跡結果】の「凍結要請状」欄が「作成できません」の場合、以下を厳守してください。
- **「報告書は取引所への凍結要請に使える」と絶対に案内しない**（宛先の取引所を特定できないため、凍結要請状は作成できません）
- 「取引所に到達していない」と断定しない。**ラベル情報が無いだけで、到達していないとは限らない**と説明する
- 報告書の価値は「**資金経路の客観的な記録**」「**警察へ提出する資料**」「開示請求を検討する際の材料」に限定して、正直に説明する
- **効果が限定的であることを明示**し、ご依頼を無理に勧めない。判断はお客様に委ねる
- 「11,000円の価値はありますか」と聞かれたら、上記を踏まえて**正直に**答える。過大な期待を持たせる表現は禁止

【これまでの相談】
${history}
ご相談者：${message}

${refundBlock}

【この返信の書き方（厳守）】
- **挨拶・お礼・自己紹介を書かない**。1文目から本題に入る
- **聞かれた質問にまっすぐ答える**。聞かれていないことを述べない
- **追跡結果を再説明しない**（利用者の画面に既に表示済み）。触れる場合は1文まで
- 箇条書きを使う。日本語

相談員としての返信のみを出力してください。`;

      const prompt = brand === 'bitto' ? bittoPrompt : connectionPrompt;
      // 500文字の日本語回答が途中で切れないよう余裕を持たせる
      const text = await geminiGenerate(prompt, { temperature: 0.5, maxOutputTokens: 1400 });
      if (text) reply = text;
    }
    if (asksRefund) reply = `${REFUND_NOTICE}

${reply}`;
    res.json({ reply });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

// ── IAP（App内課金）レシート検証：RevenueCat ─────────────────────
// クライアントの購入後に呼ばれ、RevenueCatのレシートを検証。
// 検証OKの場合のみ txidFormTokens にトークンを発行して formUrl を返す（不正防止）。
// REVENUECAT_SECRET_KEY 未設定時は 503（承認前は安全に無効化）。
app.post('/api/connection/iap/verify', express.json(), async (req, res) => {
  try {
    const { appUserId, transactionIds, productId, platform, name, email, phone, count } = req.body || {};
    const want = Math.max(1, Math.min(10, parseInt(count) ||
      (Array.isArray(transactionIds) ? transactionIds.length : 1)));
    if (!email)     return res.status(400).json({ error: 'メールアドレスが必要です' });
    if (!appUserId) return res.status(400).json({ error: '購入情報が不足しています' });
    if (!REVENUECAT_SECRET_KEY)
      return res.status(503).json({ error: 'IAP検証は準備中です（ストアアカウント承認後に有効化）' });

    // RevenueCat REST：subscriber 情報を取得
    const rcRes = await fetch(`https://api.revenuecat.com/v1/subscribers/${encodeURIComponent(appUserId)}`, {
      headers: { Authorization: `Bearer ${REVENUECAT_SECRET_KEY}`, 'Content-Type': 'application/json' },
    });
    if (!rcRes.ok) return res.status(502).json({ error: '購入の確認に失敗しました' });
    const rcData = await rcRes.json();
    const nonSubs = (rcData.subscriber && rcData.subscriber.non_subscriptions) || {};

    // 消費型購入を平坦化（商品ID一致・未消費のみ）
    const txList = [];
    for (const pid of Object.keys(nonSubs)) {
      if (RC_PRODUCT_IDS.length && !RC_PRODUCT_IDS.includes(pid)) continue;
      for (const t of (nonSubs[pid] || [])) {
        const tid = t.store_transaction_id || t.id;
        if (!tid || consumedIapTx.has(tid)) continue;
        txList.push({ pid, tid, ms: Date.parse(t.purchase_date || '') || 0, sandbox: !!t.is_sandbox });
      }
    }
    txList.sort((a, b) => b.ms - a.ms);

    // クライアント指定のトランザクションIDを優先突き合わせ
    const provided = new Set((transactionIds || []).filter(Boolean));
    const chosen = [];
    for (const tx of txList) {
      if (chosen.length >= want) break;
      if (provided.has(tx.tid)) chosen.push(tx);
    }
    // 不足分は直近(60分以内)の未消費購入で補完（同一ユーザーの正当な購入のみ）
    if (chosen.length < want) {
      const cutoff = Date.now() - 60 * 60 * 1000;
      for (const tx of txList) {
        if (chosen.length >= want) break;
        if (chosen.includes(tx)) continue;
        if (tx.ms && tx.ms < cutoff) continue;
        chosen.push(tx);
      }
    }
    if (!chosen.length) return res.status(402).json({ error: '有効な購入が確認できませんでした' });

    chosen.forEach(tx => consumedIapTx.add(tx.tid));
    const n = chosen.length;

    // TXID入力フォームのトークンを発行（Stripeフローと同じ構造）
    const formToken = crypto.randomUUID();
    const sessionId = `connection-${formToken.slice(0, 8)}`;
    txidFormTokens.set(formToken, {
      sessionId, userId: '', count: n,
      customerName: name || 'お客様', email, phone: phone || '',
      brand: 'connection', used: false, createdAt: Date.now(),
      prefillTxid: '', status: 'paid_waiting_txid',
      iap: {
        platform: platform || '', appUserId,
        productId: productId || (chosen[0] && chosen[0].pid) || '',
        transactionIds: chosen.map(c => c.tid), sandbox: chosen.some(c => c.sandbox),
      },
    });
    const formUrl = `${BASE_URL}/txid-form/${formToken}`;

    // 申込記録
    const submittedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    appendToSheet([
      submittedAt, name || '', phone || '', email, '', String(n),
      String(CONNECTION_PRICE * n), sessionId, '', '申込済み(Connection/IAP)',
    ]).catch(console.error);

    // 申込確認・利用規約同意メール
    sendEmail(email, '【Connection】お申し込みを受け付けました（正式調査報告書）',
      `<div style="font-family:sans-serif;line-height:1.8;color:#222">
        <p>${name || 'お客様'} 様</p>
        <p>正式調査報告書のお申し込みを受け付けました。ご利用ありがとうございます。</p>
        <p><b>調査件数：</b>${n}件　<b>お支払い：</b>¥${(CONNECTION_PRICE * n).toLocaleString()}（税込）</p>
        <p>続けて、以下のフォームから調査対象の <b>TXID</b> をご入力ください（${n}件）：<br>
          <a href="${formUrl}">${formUrl}</a></p>
        <p>調査完了後、<b>調査報告書</b>と<b>専任サポートチャット</b>を、このメールアドレスとアプリ内でお届けします。</p>
        <hr style="border:none;border-top:1px solid #eee;margin:18px 0">
        <p style="font-size:13px;color:#666">
          ■ お申し込み時に<b>利用規約に同意</b>いただいています。主な内容：<br>
          ・本サービスは公開ブロックチェーン情報に基づく調査・情報提供サービスです。<br>
          ・デジタルコンテンツの性質上、決済後のキャンセル・返金はお受けできません。<br>
          ・本サービスは被害の回復・資産の奪還・犯人の特定を保証するものではありません。<br>
          ・本サービスは法律事務を提供するものではありません。<br>
          プライバシーポリシー：<a href="${BASE_URL}/privacy">${BASE_URL}/privacy</a>
        </p>
        <p style="font-size:13px;color:#666">運営：Himesen株式会社　お問い合わせ：himesen.inc2512@gmail.com</p>
      </div>`
    ).catch(console.error);

    res.json({ ok: true, formUrl });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

// ── BitToアプリ IAP（App内課金）レシート検証 ──────────────────
// Connection版(/api/connection/iap/verify)と同型。商品IDを BITTO_PRODUCT_ID に限定して分離。
// REVENUECAT_SECRET_KEY 未設定時は 503（承認前は安全に無効化）。
/* 購入済みの申込を復元する。
   レポートタブは端末のlocalStorageに依存しているため、機種変更・再インストール・
   データ消去で消える。メールが唯一の復旧手段だが、キャリアメールは受信設定で
   そもそも届かないことがあり（Gmailのように迷惑メールに入るのではなく拒否される）、
   支払ったのに報告書にもTXID入力フォームにもたどり着けない状態になりうる。

   サーバーは発行時に appUserId と transactionIds を保存しているので、
   ストアのレシートから復元できる。ログインは不要。

   照合はクライアントが送ったIDではなくRevenueCatから取得したIDで行う。
   他人の申込を引き出せないようにするため。 */
app.post('/api/bitto/orders/restore', express.json(), async (req, res) => {
  try {
    const { appUserId } = req.body || {};
    if (!appUserId) return res.status(400).json({ error: '購入情報が不足しています' });
    if (!REVENUECAT_SECRET_KEY)
      return res.status(503).json({ error: '購入の復元は準備中です' });

    const rcRes = await fetch(`https://api.revenuecat.com/v1/subscribers/${encodeURIComponent(appUserId)}`, {
      headers: { Authorization: `Bearer ${REVENUECAT_SECRET_KEY}`, 'Content-Type': 'application/json' },
    });
    if (!rcRes.ok) return res.status(502).json({ error: '購入の確認に失敗しました' });
    const rcData = await rcRes.json();
    const nonSubs = (rcData.subscriber && rcData.subscriber.non_subscriptions) || {};

    // このユーザーが実際に持っているBitTo商品のトランザクションIDを集める
    const owned = new Set();
    for (const pid of Object.keys(nonSubs)) {
      if (!(bittoUnitsOf(pid) > 0)) continue;
      for (const t of (nonSubs[pid] || [])) {
        const tid = t.store_transaction_id || t.id;
        if (tid) owned.add(tid);
      }
    }
    if (!owned.size) return res.json({ ok: true, orders: [] });

    // そのトランザクションで発行した申込を探す
    const orders = [];
    for (const [token, v] of txidFormTokens.entries()) {
      if (v.brand !== 'bitto' || !v.iap) continue;
      const ids = v.iap.transactionIds || [];
      if (!ids.some(id => owned.has(id))) continue;
      orders.push({
        url: `${BASE_URL}/txid-form/${token}`,
        count: v.count || 1,
        name: v.customerName || '',
        email: v.email || '',
        status: v.status || (v.used ? 'investigating' : 'paid_waiting_txid'),
        reportUrl: (v.report && v.report.reportUrl) || null,
        at: v.createdAt || 0,
      });
    }
    orders.sort((a, b) => b.at - a.at);
    console.log(`[Restore] appUserId=${String(appUserId).slice(0, 12)}… 復元${orders.length}件`);
    res.json({ ok: true, orders });
  } catch (e) {
    console.error('[Restore] 失敗:', e.message);
    res.status(500).json({ error: '購入の復元に失敗しました' });
  }
});

app.post('/api/bitto/iap/verify', express.json(), async (req, res) => {
  try {
    const { appUserId, transactionIds, productId, platform, name, email, phone, count } = req.body || {};
    const want = Math.max(1, Math.min(BITTO_MAX_TXID, parseInt(count) ||
      (Array.isArray(transactionIds) ? transactionIds.length : 1)));
    if (!email)     return res.status(400).json({ error: 'メールアドレスが必要です' });
    if (!appUserId) return res.status(400).json({ error: '購入情報が不足しています' });
    if (!REVENUECAT_SECRET_KEY)
      return res.status(503).json({ error: 'IAP検証は準備中です（ストアアカウント承認後に有効化）' });

    const rcRes = await fetch(`https://api.revenuecat.com/v1/subscribers/${encodeURIComponent(appUserId)}`, {
      headers: { Authorization: `Bearer ${REVENUECAT_SECRET_KEY}`, 'Content-Type': 'application/json' },
    });
    if (!rcRes.ok) return res.status(502).json({ error: '購入の確認に失敗しました' });
    const rcData = await rcRes.json();
    const nonSubs = (rcData.subscriber && rcData.subscriber.non_subscriptions) || {};

    // 消費型購入を平坦化（BitTo商品のみ・未消費のみ）
    const txList = [];
    for (const pid of Object.keys(nonSubs)) {
      // BitToの商品だけ受け付ける。新Google Play方式は product_id:購入オプション の
      // 複合IDになるため、`:` より前を見て判定する。
      // まとめ買い商品（1回の購入で複数件）もここで許可される。
      if (!(bittoUnitsOf(pid) > 0)) continue;
      for (const t of (nonSubs[pid] || [])) {
        const tid = t.store_transaction_id || t.id;
        if (!tid || consumedIapTx.has(tid)) continue;
        txList.push({ pid, tid, ms: Date.parse(t.purchase_date || '') || 0, sandbox: !!t.is_sandbox });
      }
    }
    txList.sort((a, b) => b.ms - a.ms);

    // まとめ買い商品は1トランザクションで複数件になるため、件数ではなく
    // 付与件数の合計で必要分に達したかを判定する。
    const provided = new Set((transactionIds || []).filter(Boolean));
    const chosen = [];
    let units = 0;
    for (const tx of txList) {
      if (units >= want) break;
      if (provided.has(tx.tid)) { chosen.push(tx); units += bittoUnitsOf(tx.pid); }
    }
    if (units < want) {
      const cutoff = Date.now() - 60 * 60 * 1000;
      for (const tx of txList) {
        if (units >= want) break;
        if (chosen.includes(tx)) continue;
        if (tx.ms && tx.ms < cutoff) continue;
        chosen.push(tx); units += bittoUnitsOf(tx.pid);
      }
    }
    if (!chosen.length) return res.status(402).json({ error: '有効な購入が確認できませんでした' });

    chosen.forEach(tx => consumedIapTx.add(tx.tid));
    // 実際に購入が確認できた分だけを付与する（クライアントの申告では増やせない）
    const n = units;

    // TXID入力フォームのトークンを発行（brand=bitto）
    const formToken = crypto.randomUUID();
    const sessionId = `bitto-${formToken.slice(0, 8)}`;
    txidFormTokens.set(formToken, {
      sessionId, userId: '', count: n,
      customerName: name || 'お客様', email, phone: phone || '',
      brand: 'bitto', used: false, createdAt: Date.now(),
      prefillTxid: '', status: 'paid_waiting_txid',
      iap: {
        platform: platform || '', appUserId,
        productId: productId || (chosen[0] && chosen[0].pid) || '',
        transactionIds: chosen.map(c => c.tid), sandbox: chosen.some(c => c.sandbox),
      },
    });
    const formUrl = `${BASE_URL}/txid-form/${formToken}`;

    // 申込記録
    const submittedAt = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
    appendToSheet([
      submittedAt, name || '', phone || '', email, '', String(n),
      String(BITTO_PRICE * n), sessionId, '', '申込済み(BitTo/IAP)',
    ]).catch(console.error);

    // 申込確認・利用規約同意メール
    sendEmail(email, '【BitTo】お申し込みを受け付けました（正式調査報告書）',
      `<div style="font-family:sans-serif;line-height:1.8;color:#222">
        <p>${name || 'お客様'} 様</p>
        <p>正式調査報告書のお申し込みを受け付けました。ご利用ありがとうございます。</p>
        <p><b>調査件数：</b>${n}件　<b>お支払い：</b>¥${(BITTO_PRICE * n).toLocaleString()}（税込）</p>
        <p>続けて、以下のフォームから調査対象の <b>TXID</b> をご入力ください（${n}件）：<br>
          <a href="${formUrl}">${formUrl}</a></p>
        <p>調査完了後、<b>調査報告書</b>を、このメールアドレスとアプリ内でお届けします。</p>
        <hr style="border:none;border-top:1px solid #eee;margin:18px 0">
        <p style="font-size:13px;color:#666">
          ■ お申し込み時に<b>利用規約に同意</b>いただいています。主な内容：<br>
          ・本サービスは公開ブロックチェーン情報に基づく調査・情報提供サービスです。<br>
          ・デジタルコンテンツの性質上、決済後のキャンセル・返金はお受けできません。<br>
          ・本サービスは被害の回復・資産の奪還・犯人の特定を保証するものではありません。<br>
          ・本サービスは法律事務を提供するものではありません。<br>
          プライバシーポリシー：<a href="${BASE_URL}/bitto/privacy">${BASE_URL}/bitto/privacy</a>
        </p>
        <p style="font-size:13px;color:#666">運営：Himesen株式会社　お問い合わせ：info@himesen-25.com</p>
      </div>`,
      'bitto'
    ).catch(console.error);

    // count は実際に付与した件数。アプリ側の記録と表示をこれに合わせる
    res.json({ ok: true, formUrl, count: n });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

app.get('*', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));

app.listen(PORT, () => {
  console.log(`\n✅ BitTo サーバー起動完了`);
  console.log(`🌐 http://localhost:${PORT}`);
  console.log(`📡 LINE Webhook: ${BASE_URL}/webhook`);
  console.log(`🔑 Blockchair : ${BLOCKCHAIR_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 LINE       : ${LINE_CHANNEL_ACCESS_TOKEN ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Stripe     : ${stripe ? '✓ 本番モード' : '⚠ テストモード（決済スキップ）'}`);
  console.log(`🔑 Sheets     : ${GOOGLE_SHEET_ID && process.env.GOOGLE_SERVICE_ACCOUNT_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Mail(SMTP) : ${SMTP_USER && SMTP_PASS ? '✓' : '⚠ 未設定'}`);
  console.log(`🧪 プレビュー : ${BASE_URL}/report/preview`);
  console.log();
});

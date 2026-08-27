// ============================================================
// BitTo — LINE ブロックチェーン自動調査サーバー
// BTC / ETH / XRP / TRON(USDT) 対応 | LINE Messaging API + Stripe 決済
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
// gemini-2.0-flash は提供終了（API応答で確認）。残すと失敗のたびに無駄な再試行が増えるため外した。
const GEMINI_FALLBACK_MODELS    = [...new Set([GEMINI_MODEL, 'gemini-flash-latest'])];
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
const txidCache       = new Map();
/* ★有料レポートで無料の結果を使い回さない。
   無料調査は外部ラベルを1回しか引かず、素性もAMLスコアも付けない。
   それをそのまま納品すると、代金をいただいた方に無料品質を渡すことになる。
   有料が要るときは、無料で作った結果を捨てて調べ直す。 */
function cachedResult(key, wantPaid) {
  const c = txidCache.get(key);
  if (!c) return null;
  if (wantPaid && !c.paid) {
    console.log('[Cache] 無料で調べた結果のため、有料レポート用に調べ直します');
    return null;
  }
  return c.result;
} // txid（小文字）→ { result, investigatedAt }
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

/* 画像から文字を読む用。geminiGenerate はテキスト専用で、有料レポートの生成に
   使われている。そこへ画像対応を混ぜると納品物の経路を壊しかねないので分けた。

   ★モデルは実測で選んだ（2026-08-25・同じEtherscan画面を各3回）。

     gemini-3.5-flash-lite      3/3 成功  1.9秒
     gemini-flash-lite-latest   3/3 成功  1.3秒
     gemini-2.5-flash           0/3      （混雑で返らず）
     gemini-flash-latest        1/1 成功  32.8秒 ← レポート用の既定。画像には遅すぎる

   ★thinkingConfig は付けないこと。
     lite系のモデルは「Request contains an invalid argument」で即座に落ちる。
     付けずに投げると同じモデルが1〜2秒で正しく返す。ここで丸一日溶かしかねない。

   ★先頭は別名（latest）ではなく版を固定したものにしている。
     別名は中身が入れ替わるので、遅い版に差し替わっても気づけない。 */
const VISION_MODELS   = ['gemini-3.5-flash-lite', 'gemini-flash-lite-latest', GEMINI_MODEL];
const VISION_TIMEOUT_MS = 20000;   // 待たせるより次のモデルへ移る方がよい
async function geminiVision(prompt, base64, mimeType = 'image/jpeg') {
  if (!GEMINI_KEY) return null;
  const deadline = Date.now() + GEMINI_TOTAL_TIMEOUT_MS;
  const tried = [];
  /* 実測で「This model is currently experiencing high demand」が返ることがある。
     一時的なもので、別のモデルか少し後なら通る。利用者に撮り直させる前にこちらで粘る。 */
  const attempts = [];
  for (const model of [...new Set(VISION_MODELS)]) attempts.push(model, model);
  for (const model of attempts) {
    if (Date.now() >= deadline) { tried.push('総時間の上限に到達'); break; }
    if (tried.length) await new Promise(r => setTimeout(r, 600));
    try {
      // キーはURLに載せずヘッダーで渡す（URLはログや中継に残るため）
      const r = await fetch(`https://generativelanguage.googleapis.com/v1beta/models/${model}:generateContent`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'x-goog-api-key': GEMINI_KEY },
        body: JSON.stringify({
          contents: [{ parts: [{ text: prompt }, { inline_data: { mime_type: mimeType, data: base64 } }] }],
          generationConfig: { temperature: 0, maxOutputTokens: 800 },
        }),
        signal: AbortSignal.timeout(VISION_TIMEOUT_MS),
      });
      const j = await r.json();
      const text = j.candidates?.[0]?.content?.parts?.[0]?.text;
      if (text) {
        if (tried.length) console.warn(`[GeminiVision] 復旧 model=${model} ／ 失敗: ${tried.join(' | ')}`);
        return text.trim();
      }
      tried.push(`${model}: ${j.error?.message || j.candidates?.[0]?.finishReason || 'empty'}`);
    } catch (e) {
      tried.push(`${model}: ${e.message}`);
    }
  }
  console.error('[GeminiVision] 全て失敗:', tried.join(' | '));
  return null;
}

/* OCRの読み違いを直す。
   TXIDは16進数（0-9 a-f）しか取らないので、「16進数に無い文字」だけを
   置き換える表を持てば、正しい文字を壊す心配がない。
   ⚠️ b・c・d・e・f は16進数として正しい。B→8 のような変換は入れないこと。 */
const OCR_FIX = {
  O:'0', o:'0', Q:'0', D:'0', U:'0', u:'0',
  I:'1', i:'1', l:'1', L:'1', J:'1', '|':'1', '!':'1',
  Z:'2', z:'2',
  S:'5', s:'5',
  G:'6', g:'6',
  T:'7', t:'7',
  q:'9', y:'9',
};
function fixHex(raw) {
  return String(raw || '').split('')
    .map(ch => (/[0-9a-fA-F]/.test(ch) ? ch : (OCR_FIX[ch] || ch)))
    .join('');
}

/* 読み取った文字列からTXIDを拾う。
   直した版でしか見つからなければ corrected を立て、画面側で断りを出す。

   ★補正は「行まるごとが64桁になるか」で判定する。文章の途中を部分一致で拾うと、
     周りの文字まで16進数に変えてしまい、実在しないTXIDを作る。
     例：「zzz<TXID>zzz」→ zzz が 222 になって前後が繋がり、別の64桁が生まれる。 */
function pickTxidsFromText(text) {
  const out   = [];
  const seen  = new Set();
  const exact = /^(0x)?[0-9a-fA-F]{64}$/;
  const add = (t, corrected) => {
    const key = t.toLowerCase();
    if (seen.has(key)) return;
    seen.add(key);
    const chain = /^0x/.test(t) ? 'eth' : (t === t.toUpperCase() ? 'xrp' : 'btc');
    out.push({ txid: t, chain, corrected });
  };

  // Geminiには「1行に1件」と指示してある。行ごとに丸ごと見るのが一番正確。
  for (const line of String(text || '').split('\n')) {
    const t = line.replace(/\s+/g, '');
    if (!t) continue;
    if (exact.test(t)) { add(t, false); continue; }
    const fixed = fixHex(t);
    if (exact.test(fixed)) add(fixed, true);
  }

  // 指示に従わず説明文を混ぜてきた場合と、途中で折り返された場合の保険。
  // ここでは補正をかけない（上記の理由でありもしないTXIDを作るため）。
  const flat = String(text || '').replace(/\s+/g, '');
  for (const t of flat.match(/0x[0-9a-fA-F]{64}|[0-9a-fA-F]{64}/g) || []) add(t, false);

  return out;
}

/* 画像からTXIDを読み取る。
   「画像からTXIDを取り出せない」利用者のための入口（PROJECT-LOG 第4-N節）。
   高齢の方を想定しているが、そもそもTXIDのコピーはこの製品で最初につまずく場所。

   ★画像は保存しない。
     被害者のスクリーンショットには取引所の残高や個人情報が写っていることが多い。
     Geminiへ渡すだけで、こちらのディスクには一切書かない。 */
/* 認証のない入口からGeminiを呼ぶので、連打されると課金がそのまま増える。
   被害者が撮り直しながら数回試すのは普通なので、そこは通す。
   メモリ上だけの簡易な制限（再起動で消えてよい。厳密さより事故防止が目的）。 */
const ocrHits = new Map();   // IP → 直近の呼び出し時刻の配列
const OCR_WINDOW_MS = 10 * 60 * 1000;
const OCR_MAX       = 20;    // 10分で20回。撮り直しには十分で、機械的な連打は止まる
function ocrRateOk(ip) {
  const now = Date.now();
  const list = (ocrHits.get(ip) || []).filter(t => now - t < OCR_WINDOW_MS);
  if (list.length >= OCR_MAX) { ocrHits.set(ip, list); return false; }
  list.push(now);
  ocrHits.set(ip, list);
  if (ocrHits.size > 5000) {   // 放置すると増え続けるので、たまに古いものを捨てる
    for (const [k, v] of ocrHits) if (!v.some(t => now - t < OCR_WINDOW_MS)) ocrHits.delete(k);
  }
  return true;
}

app.post('/api/ocr-txid', express.json({ limit: '12mb' }), async (req, res) => {
  try {
    const ip = req.headers['x-forwarded-for']?.split(',')[0].trim() || req.ip || 'unknown';
    if (!ocrRateOk(ip)) return res.json({ ok: false, reason: 'rate_limited' });
    const raw = String(req.body?.image || '');
    const m = raw.match(/^data:(image\/[a-zA-Z0-9.+-]+);base64,(.+)$/);
    if (!m) return res.json({ ok: false, reason: 'bad_image' });
    const [, mimeType, base64] = m;
    if (!GEMINI_KEY) return res.json({ ok: false, reason: 'no_key' });

    const prompt = [
      'この画像に写っている「トランザクションID（TXID／取引ハッシュ）」を、',
      '1つ残らずすべて抜き出してください。複数写っている場合は全部です。',
      'TXIDは 16進数（0-9 と a-f）だけでできた64文字の文字列です。先頭に 0x が付くこともあります。',
      '1行に1件、そのまま出力してください。説明・見出し・記号・番号は付けないでください。',
      '改行や折り返しで途中に空白が入っている場合は、繋げて1件として出力してください。',
      '確信が持てない文字があっても、見えたとおりに出力してください（こちらで検算します）。',
      'TXIDが見つからない場合は NONE とだけ出力してください。',
    ].join('\n');

    const text = await geminiVision(prompt, base64, mimeType);
    if (!text) return res.json({ ok: false, reason: 'gemini_failed' });

    const found = pickTxidsFromText(text);
    console.log(`[OCR] ${found.length}件 検出${found.some(f => f.corrected) ? '（読み違いの補正あり）' : ''}`);
    return res.json({ ok: true, txids: found });
  } catch (e) {
    console.error('[OCR] 失敗:', e.message);
    return res.json({ ok: false, reason: 'error' });
  }
});

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

/* ── 初動パック（無料）のPDF化 ──────────────────────────────
   これまでは画面側で組んだHTMLを window.open で開いていたが、
   スマホではポップアップが塞がれてHTMLファイルのダウンロードに落ちる。
   端末に降りたHTMLは開きにくく、弁護士や警察に渡す形にもならない。
   「PDFで苦戦する利用者」を助けるのが目的なので、PDFで渡す（第4-N節）。

   ★画面から渡すのは【データだけ】。HTMLは受け取らない。
     利用者が送ったHTMLをサーバーのChromeで開くと、file:// や内部アドレスを
     読ませる攻撃が成立する。組み立ては必ずこちら側で行う。

   ★できたPDFは保存しない。 TXID・アドレス・被害内容が入るため、
     その場で返して捨てる（OCRの画像と同じ考え方）。 */
// エスケープは既存の escHtml（下方で宣言・巻き上げで使える）を使う。二重に持たない。

function packRowsHTML(results) {
  const rs = Array.isArray(results) ? results : [];
  if (!rs.length) {
    return `<tr><td colspan="5" style="color:#777">（TXIDの解析結果がまだありません。「AI調査チャット」でTXIDを送信すると、ここに自動で入ります）</td></tr>`;
  }
  return rs.map(r => {
    const p    = Array.isArray(r.path) ? r.path : [];
    const dest = p.length ? p[p.length - 1] : null;
    const ex   = [...new Set(p.filter(n => n.isExchange && n.label).map(n => n.label))];
    const amt  = r.tokenSymbol ? `${r.tokenAmount} ${r.tokenSymbol}`
                               : `${r.amount != null ? r.amount : ''} ${r.chain || ''}`;
    return `<tr><td>${escHtml(r.chain || '')}</td><td class="mono">${escHtml(r.txid || '')}</td>`
         + `<td>${escHtml(amt)}</td><td class="mono">${escHtml((dest && dest.address) || '')}</td>`
         + `<td>${ex.length ? escHtml(ex.join('、')) + '（推定）' : '未特定'}</td></tr>`;
  }).join('');
}

function buildInitialPackHTML(results) {
  const now = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  const blankRow = '<tr><td><span class="fill">&nbsp;</span></td><td><span class="fill" style="min-width:420px">&nbsp;</span></td></tr>';
  return `<!DOCTYPE html><html lang="ja"><head><meta charset="UTF-8">
<title>BitTo 初動パック</title><style>
body{font-family:-apple-system,'Hiragino Kaku Gothic ProN','Noto Sans JP',Meiryo,sans-serif;color:#111;line-height:1.8;max-width:820px;margin:0 auto;padding:28px 22px;font-size:14px}
h1{font-size:20px;margin:0 0 4px}h2{font-size:15px;margin:26px 0 8px;padding-bottom:5px;border-bottom:2px solid #111}
.meta{color:#666;font-size:12px;margin-bottom:6px}
.note{background:#f5f5f5;border-left:3px solid #999;padding:10px 12px;font-size:12px;color:#444;margin:10px 0}
table{width:100%;border-collapse:collapse;margin:8px 0;font-size:12.5px}
th,td{border:1px solid #ccc;padding:7px 8px;text-align:left;vertical-align:top}
th{background:#f0f0f0}
.mono{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:11px;word-break:break-all}
.fill{border-bottom:1px solid #999;display:inline-block;min-width:180px}
ul{margin:6px 0 6px 20px;padding:0}li{margin:4px 0}
.warn{background:#fff3f3;border:1px solid #e0a0a0;padding:12px 14px;border-radius:6px}
.warn b{color:#b32}
pre{background:#f7f7f7;border:1px solid #ddd;padding:12px;white-space:pre-wrap;font-family:inherit;font-size:12.5px;border-radius:5px}
</style></head><body>
<h1>BitTo 初動パック</h1>
<div class="meta">作成日時：${escHtml(now)}　／　作成：BitTo（公開ブロックチェーン解析ツール）</div>
<div class="note">本資料は、公開ブロックチェーン情報にもとづく<b>解析結果と初動の整理用テンプレート</b>です。到達取引所等は<b>推定を含みます</b>。資産の回収・返還を保証するものではありません。</div>
<h2>1. 調査対象の記録</h2>
<table><tr><th>チェーン</th><th>TXID</th><th>数量</th><th>最終確認アドレス</th><th>到達取引所（推定）</th></tr>${packRowsHTML(results)}</table>
<table>
<tr><th style="width:32%">送金日時</th><td><span class="fill">&nbsp;</span></td></tr>
<tr><th>送金元（取引所・ウォレット）</th><td><span class="fill">&nbsp;</span></td></tr>
<tr><th>被害額（日本円換算・概算）</th><td><span class="fill">&nbsp;</span></td></tr>
<tr><th>相手との接触経路</th><td><span class="fill">&nbsp;</span>（SNS／マッチング／広告／電話 等）</td></tr>
</table>
<h2>2. 証拠保全チェックリスト</h2>
<ul>
<li>☐ TXID（取引ID）を控えた（途中で切れていないか確認）</li>
<li>☐ 送金日時・数量・通貨（BTC／ETH／XRP／USDT等）を控えた</li>
<li>☐ 送金元の取引所の出金履歴のスクリーンショット</li>
<li>☐ 相手とのやり取り（SNS・チャット・メール）のスクリーンショット</li>
<li>☐ 相手のサイトURL・アプリ名・口座／ウォレット情報</li>
<li>☐ 銀行振込がある場合は振込明細（銀行・日時・金額・口座）</li>
<li>☐ 本資料（初動パック）を保存・印刷</li>
</ul>
<div class="note">※ パスワード・2段階認証コード・秘密鍵・シードフレーズは<b>誰にも渡さないでください</b>。調査・確認に一切不要です。</div>
<h2>3. 時系列メモ（警察・取引所への説明用）</h2>
<table><tr><th style="width:22%">日時</th><th>出来事（誰から・どこで・何を言われ・いくら送ったか）</th></tr>${blankRow.repeat(6)}</table>
<h2>4. 取引所への連絡文（テンプレート）</h2>
<div class="note">送金元の取引所、および（判明していれば）到達先の取引所のサポート窓口へ提出してください。<b>凍結の可否は取引所の判断です。</b></div>
<pre>件名：不正利用（詐欺被害）に関するご報告と記録保全のお願い

お世話になっております。以下の送金について、詐欺被害に遭ったため報告いたします。
可能な範囲での記録の保全と、必要なご案内をお願いいたします。

■ 送金情報
・TXID：
・チェーン／通貨：
・送金日時：
・数量：
・送金元（当方）アカウント：
・送金先アドレス：

■ 被害の経緯（概要）


■ 依頼事項
・上記取引に関する記録の保全
・貴社所定の手続きのご案内
・警察への相談を予定しており、必要書類があればご教示ください

■ 連絡先
・氏名：
・メールアドレス：
・電話番号：
</pre>
<h2>5. ⚠️ 二次被害（回収詐欺）への注意</h2>
<div class="warn">被害後に接触してくる「回収業者」による<b>二次被害</b>が多発しています。以下は詐欺の典型的なサインです。
<ul>
<li><b>「返金の可能性が高い」と期待を持たせる</b></li>
<li><b>調査に高額な費用を提示する</b></li>
<li>電話をかけてきて、契約を急かす</li>
<li>遠隔操作アプリの導入を求める</li>
<li>シードフレーズ・秘密鍵・2段階認証コードを聞いてくる</li>
<li>警察・政府機関との「特別な関係」を主張する</li>
<li>「凍結済みだが解除費用が必要」と言う</li>
<li>追加の費用を請求する</li>
</ul>
FBI・CFTCも、前払いを求める暗号資産回収サービスについて注意を呼びかけています。</div>
<h2>6. BitToができること／できないこと</h2>
<table><tr><th style="width:50%">できること</th><th>できないこと</th></tr>
<tr><td>公開チェーンの資金経路の解析<br>着金先取引所・サービスの推定<br>警察・取引所への提出資料の整理<br>不正利用申告文の作成<br>資金移動の継続監視<br>相談先・必要書類の案内</td>
<td>取引所へ凍結を命令する<br>KYC情報を強制的に取得する<br>資金の残存を保証する<br>被害資金の返還を保証する<br>強制処分を行う<br>秘密鍵で資金を取り戻す</td></tr></table>
<div class="note">緊急・進行中の犯罪は110。緊急でない警察相談は#9110、被害届は最寄りの警察署、消費者トラブルは188、詐欺的投資・無登録業者は金融庁の相談窓口が候補です。</div>
</body></html>`;
}

/* PDFの生成は重い（Chromiumのページを1枚開く）。連打で並ぶと他の納品まで遅れるため、
   OCRと同じ考え方で軽く絞る。 */
const packHits = new Map();
function packRateOk(ip) {
  const now = Date.now();
  const list = (packHits.get(ip) || []).filter(t => now - t < 10 * 60 * 1000);
  if (list.length >= 10) { packHits.set(ip, list); return false; }
  list.push(now); packHits.set(ip, list);
  if (packHits.size > 5000) {
    for (const [k, v] of packHits) if (!v.some(t => now - t < 10 * 60 * 1000)) packHits.delete(k);
  }
  return true;
}

/* できたPDFは【メモリだけ】に短時間置き、普通のURLで取りに来てもらう。

   ★blob: のURLで渡してはいけない。
     iOSのブラウザ（Chrome等）は blob: を「外部アプリを開こうとしている」と扱い、
     確認ダイアログが出たうえ、開くことも保存もできない。実機で確認済み。
     普通の https のURLなら、そのまま表示され、共有シートにも乗る。

   ディスクには書かない。TXID・アドレス・被害内容が入るため。 */
const packFiles = new Map();   // token → { pdf, name, at }
const PACK_TTL_MS = 20 * 60 * 1000;
function sweepPackFiles() {
  const now = Date.now();
  for (const [k, v] of packFiles) if (now - v.at > PACK_TTL_MS) packFiles.delete(k);
}

app.post('/api/pack/pdf', express.json({ limit: '2mb' }), async (req, res) => {
  const ip = req.headers['x-forwarded-for']?.split(',')[0].trim() || req.ip || 'unknown';
  if (!packRateOk(ip)) return res.status(429).json({ ok: false, reason: 'rate_limited' });

  const results = Array.isArray(req.body?.results) ? req.body.results.slice(0, 20) : [];
  let page;
  try {
    const browser = await getPdfBrowser();
    page = await browser.newPage();
    // setContent なので外部への通信は起きない。テンプレートも当方のもの。
    await page.setContent(buildInitialPackHTML(results), { waitUntil: 'load', timeout: PDF_TIMEOUT_MS });
    const pdf = await page.pdf({
      format: 'A4', printBackground: true,
      margin: { top: '12mm', right: '10mm', bottom: '12mm', left: '10mm' },
    });
    sweepPackFiles();
    const token = crypto.randomBytes(16).toString('hex');
    const name  = `BitTo_shodo_pack_${new Date().toISOString().slice(0, 10)}.pdf`;
    packFiles.set(token, { pdf, name, at: Date.now() });
    console.log(`[Pack] 初動パックPDF ${results.length}件分 / ${Math.round(pdf.length / 1024)}KB`);
    res.json({ ok: true, url: `/api/pack/file/${token}`, size: pdf.length });
  } catch (e) {
    console.error('[Pack] PDF生成失敗:', e.message);
    res.status(500).json({ ok: false, reason: 'pdf_failed' });
  } finally {
    if (page) await page.close().catch(() => {});
  }
});

/* 取りに来る側。?dl=1 なら保存、無ければその場で表示。
   トークンは推測できない長さで、20分で消える。 */
app.get('/api/pack/file/:token', (req, res) => {
  sweepPackFiles();
  const f = packFiles.get(String(req.params.token || ''));
  if (!f) return res.status(404).send('この書類は期限切れです。もう一度作成してください。');
  res.setHeader('Content-Type', 'application/pdf');
  res.setHeader('Cache-Control', 'private, no-store');
  res.setHeader('Content-Disposition',
    `${req.query.dl ? 'attachment' : 'inline'}; filename="${f.name}"`);
  res.end(f.pdf);
});

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

/* ══ 管理画面から足したラベル ══════════════════════════════
   ★到達先の名前が分かっても、コードを直してデプロイするまで反映されなかった。
     24時間動かすものなので、確認したその場で反映できるようにする。

   ★置き場所が2つになるので、必ず「git用の書き出し」を用意する。
     ここ（永続ディスク）はボリュームを作り直すと消える。
     時々コード側（address-labels.json）へ写して、消えても困らないようにする。

   ★誤って登録すると、誤った凍結要請先が出る。
     コードと違って差分の確認も履歴も無いので、
     一覧・削除・登録日時を必ず添える。 */
const MANUAL_LABEL_FILE = path.join(DATA_DIR, 'manual-labels.json');
let manualLabels = {};        // 小文字アドレス → { name, at }
try {
  if (fs.existsSync(MANUAL_LABEL_FILE)) {
    manualLabels = JSON.parse(fs.readFileSync(MANUAL_LABEL_FILE, 'utf8')) || {};
    for (const [addr, v] of Object.entries(manualLabels)) {
      const name = typeof v === 'string' ? v : v && v.name;
      if (name) LABEL_DB[addr.toLowerCase()] = name;
    }
    console.log(`[LABEL_DB] 管理画面から足した分 ${Object.keys(manualLabels).length}件を読み込み`);
  }
} catch (e) { console.error('[LABEL_DB] 管理分の読み込みに失敗:', e.message); }

/* アドレスの形。チェーンごとに違うので、共通して言えることだけ見る。
   ★厳しくしすぎると登録できないチェーンが出る。緩すぎると事故のもと。 */
function looksLikeAddress(a) {
  const s = String(a || '').trim();
  if (/^0x[0-9a-fA-F]{40}$/.test(s)) return true;              // EVM
  if (/^T[1-9A-HJ-NP-Za-km-z]{33}$/.test(s)) return true;      // TRON
  if (/^r[1-9A-HJ-NP-Za-km-z]{24,34}$/.test(s)) return true;   // XRP
  if (/^(bc1|[13])[0-9a-zA-Z]{25,70}$/.test(s)) return true;   // BTC
  return false;
}

function saveManualLabels() {
  return fsp.writeFile(MANUAL_LABEL_FILE, JSON.stringify(manualLabels, null, 1), 'utf8')
    .catch(e => console.error('[LABEL_DB] 管理分の保存に失敗:', e.message));
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
  'gmoコイン': {
    url: 'https://coin.z.com/jp/',
    support: 'https://support.coin.z.com',
    note: '運営：GMOコイン株式会社（日本の暗号資産交換業者）。日本語で照会でき、警察からの照会にも国内法に基づき対応する体制があります。',
  },
  'gmo coin': {
    url: 'https://coin.z.com/jp/',
    support: 'https://support.coin.z.com',
    note: '運営：GMOコイン株式会社（日本の暗号資産交換業者）。',
  },
  'sbi vc': {
    url: 'https://www.sbivc.co.jp/',
    support: 'https://www.sbivc.co.jp/faqs',
    note: '運営：SBI VCトレード株式会社（日本の暗号資産交換業者）。DMM Bitcoin の口座・預かり資産の移管先でもあります（2025年3月）。',
  },
  'sbivc': {
    url: 'https://www.sbivc.co.jp/',
    support: 'https://www.sbivc.co.jp/faqs',
    note: '運営：SBI VCトレード株式会社（日本の暗号資産交換業者）。',
  },
  bitpoint: {
    url: 'https://www.bitpoint.co.jp/',
    support: 'https://faq.bitpoint.co.jp/',
    note: '運営：SBI VCトレード株式会社（日本の暗号資産交換業者）。',
  },
  '楽天ウォレット': {
    url: 'https://www.rakuten-wallet.co.jp/',
    support: 'https://faqsystem.jp/rakuten_wallet/',
    note: '運営：楽天ウォレット株式会社（日本の暗号資産交換業者）。',
  },
  'rakuten wallet': {
    url: 'https://www.rakuten-wallet.co.jp/',
    support: 'https://faqsystem.jp/rakuten_wallet/',
    note: '運営：楽天ウォレット株式会社（日本の暗号資産交換業者）。',
  },
  'dmm bitcoin': {
    url: 'https://www.sbivc.co.jp/',
    support: 'https://www.sbivc.co.jp/faqs',
    note: 'DMM Bitcoin はサービスを終了し、口座・預かり資産は SBI VCトレード株式会社へ移管されました（同社の公表・2025年3月）。照会は移管先の SBI VCトレードへ行ってください。',
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
  /* ★実際の被害案件の到達先で、語彙に無く取引所と判定できなかったもの。
     htx は huobi の現在の名称。coincorner は英国の取引所。
     名前が引けていても、ここに無いと「到達した」と扱えない。 */
  'htx','coincorner',
  'phemex','bitmart','digifinex','xt.com','latoken','probit',
  // 国内取引所
  'gmo coin','gmoコイン','sbi vc','bitpoint','dmm bitcoin','bittrade',
  'coinbest','okcoin','bitmax','decurret','coinbook','bitTrade',
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

/* ラベルDBには取引所のウォレットだけでなく、USDTなどの
   トークンコントラクトも入っている（Etherscan由来の一括登録）。
   これを取引所として扱うと「Tether USD に到達しました」で追跡が止まり、
   本当の着金先（取引所）にたどり着けない。名前で切り分ける。 */
const TOKEN_KEYWORDS = [
  'tether','usdt','usdc','usd coin','busd','dai','trueusd','tusd','pax','frax',
  'wrapped','weth','wbtc','token','peg','stablecoin','erc-20','erc20','coin)',
];
const VIA_KEYWORDS = [
  'bridgers','transit finance','transitswap','transitfinance',
  'changenow','fixedfloat','simpleswap','sideshift','stealthex','exolix',
  'lifi','socket','squid','rango','thorchain','rubic','xy finance','paraswap',
  '1inch','0x protocol','uniswap','sushiswap','pancakeswap','router','swap router',
  'dex','aggregator','cross-chain','crosschain','bridge','near intents',
  'rainbow bridge','stargate','layerzero','hop protocol','across','celer',
  'multichain','anyswap','synapse','connext',
];
/* 「経由」＝DEX・ブリッジ・両替。取引所と同じ扱いにすると
   凍結要請の宛先を誤って案内してしまう。 */
function isViaService(label) {
  if (!label) return false;
  const lo = String(label).toLowerCase();
  return VIA_KEYWORDS.some(k => lo.includes(k));
}

function isTokenContract(label) {
  if (!label) return false;
  const lo = String(label).toLowerCase();
  return TOKEN_KEYWORDS.some(k => lo.includes(k));
}

function getLabel(addr) {
  if (!addr) return { label: '', type: 'unknown' };
  const lo = addr.toLowerCase();
  const found = LABEL_DB[lo] || LABEL_DB[addr];
  if (found) return { label: found, type: isTokenContract(found) ? 'token' : 'exchange' };
  /* ★一度お金を払って引いた名前は、その場だけでなくずっと使う。
     外部APIの結果はディスクに貯めてあるのに、この関数（＝次の一手を
     選ぶときの判定に使う）が見ていなかった。
     そのため「すでに取引所と分かっているアドレス」を候補として
     優先できず、払った分を活かせていなかった。
     空文字は「引いたが名前が無かった」印なので、名前としては扱わない。 */
  const cached = cachedLabelName(lo);
  if (cached) return { label: cached, type: isTokenContract(cached) ? 'token' : 'exchange' };
  return { label: '', type: 'unknown' };
}

/* labelCache はこの関数より後ろで作られる。読み込み中に呼ばれても
   落ちないようにしておく（起動順に依存させない）。 */
function cachedLabelName(lo) {
  try {
    if (!labelCache || !labelCache.has(lo)) return '';
    const c = labelCache.get(lo);
    return (typeof c === 'string' ? c : (c && c.name)) || '';
  } catch { return ''; }
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
const MISTTRACK_PAID_LOOKUPS = Number(process.env.MISTTRACK_PAID_LOOKUPS ?? 5);   // 有料レポート1件あたり（枝を追うぶん増やした）
const MISTTRACK_FREE_LOOKUPS = Number(process.env.MISTTRACK_FREE_LOOKUPS ?? 1);   // 無料の追跡1件あたり（0で無料は呼ばない）
const MISTTRACK_DAILY_CAP    = Number(process.env.MISTTRACK_DAILY_CAP ?? 5);      // 1日の上限（無料）
const MISTTRACK_MONTH_CAP    = Number(process.env.MISTTRACK_MONTH_CAP ?? 15);     // 1か月の上限
const MISTTRACK_TOTAL_CAP    = Number(process.env.MISTTRACK_TOTAL_CAP ?? 100);    // 購入した総回数（使い切ったら止まる）
/* 有料の報告書のために取っておく回数。無料の追跡はここに手を付けない。
   代金をいただいた調査で「名前が引けませんでした」となるのが最悪のため。 */
const MISTTRACK_PAID_RESERVE = Number(process.env.MISTTRACK_PAID_RESERVE ?? 30);

/* 使った回数の記録。前払い分を守るのが目的なので、
   再デプロイで0に戻らないようファイルに残す（報告書と同じ永続ボリューム）。 */
const LABEL_USAGE_FILE = path.join(REPORTS_DIR, 'label-usage.json');
let labelUsage = { day: '', count: 0, month: '', monthCount: 0, total: 0 };
try {
  if (fs.existsSync(LABEL_USAGE_FILE)) {
    labelUsage = { ...labelUsage, ...JSON.parse(fs.readFileSync(LABEL_USAGE_FILE, 'utf8')) };
    console.log(`[LabelAPI] これまでの照会 ${labelUsage.total}回を復元`);
  }
} catch (e) { console.error('[LabelAPI] 使用記録の読み込み失敗:', e.message); }
function saveLabelUsage() {
  fsp.writeFile(LABEL_USAGE_FILE, JSON.stringify(labelUsage), 'utf8')
    .catch(e => console.error('[LabelAPI] 使用記録の保存失敗:', e.message));
}

function labelDayKey()   { return new Date().toLocaleDateString('ja-JP', { timeZone: 'Asia/Tokyo' }); }
function labelMonthKey() { return labelDayKey().slice(0, 7); }   // 2026/8/20 → 2026/8

/* 日・月・総量のどれかに当たったら照会しない。
   当たっても調査自体は続く（名前が付かないだけ）。 */
/* ★動作確認のための調査は、買った回数を使わない。
   実際に起きたこと：修正の検証で1日に十数件の調査を流し、
   ★その日の外部ラベルの枠を使い切ってしまった。
   その結果、利用者が本番で試したとき取引所名が出なかった。
   検証は本番と同じ経路を通したいが、代金のかかる部分だけは避けたい。
   合言葉は要らない。この印を付けると結果が減るだけで、得をする使い方が無いため。 */
const SELFTEST_PREFIX = 'selftest-';
const isSelfTest = device => String(device || '').startsWith(SELFTEST_PREFIX);

function labelQuotaOk(paid = false, device = null) {
  if (isSelfTest(device)) {
    console.log('[LabelAPI] 動作確認のため外部ラベルは引きません');
    return false;
  }
  const d = labelDayKey(), m = labelMonthKey();
  if (labelUsage.day !== d)   { labelUsage.day = d; labelUsage.count = 0; }
  if (labelUsage.month !== m) { labelUsage.month = m; labelUsage.monthCount = 0; }
  // 買った分を超えることだけは誰であっても許さない
  if (labelUsage.total >= MISTTRACK_TOTAL_CAP) {
    console.warn(`[LabelAPI] 購入分を使い切りました（${labelUsage.total}/${MISTTRACK_TOTAL_CAP}）。以後は自前DBのみで動きます`);
    return false;
  }
  // 日次・月次は無料利用の暴走止め。代金をいただいた報告書は対象外にする
  if (paid) return true;
  // 無料は、有料のために取っておく分には手を付けない
  if (labelUsage.total >= MISTTRACK_TOTAL_CAP - MISTTRACK_PAID_RESERVE) {
    console.warn(`[LabelAPI] 残り${MISTTRACK_TOTAL_CAP - labelUsage.total}回は有料調査用に確保します（無料分は停止）`);
    return false;
  }
  if (labelUsage.monthCount >= MISTTRACK_MONTH_CAP) { console.warn('[LabelAPI] 今月の上限に達しました（無料分）'); return false; }
  if (labelUsage.count >= MISTTRACK_DAILY_CAP)      { console.warn('[LabelAPI] 本日の上限に達しました（無料分）'); return false; }
  // 1人が使い占めるのを防ぐ。全体の枠が残っていても、この人はここまで
  if (!deviceQuotaOk(device)) return false;
  return true;
}
function labelQuotaUse(device) {
  labelUsage.count++; labelUsage.monthCount++; labelUsage.total++;
  if (device) {
    const u = deviceUsageOf(device);
    u.count++; u.monthCount++;
    saveDeviceUsage();
  }
  saveLabelUsage();
}

/* ── 1利用者あたりの上限 ────────────────────────────────────
   全体の上限だけだと、1人が繰り返し調べただけで全員分を使い切ってしまう。
   逆に利用者ごとの上限だけでは、人数が増えた分だけ購入分が減るので守れない。
   ★両方が要る。全体＝買った分を守る。利用者ごと＝1人の使い占めを防ぐ。 */
const DEVICE_USAGE_FILE = path.join(REPORTS_DIR, 'label-usage-device.json');
const MISTTRACK_USER_DAILY = Number(process.env.MISTTRACK_USER_DAILY ?? 5);
const MISTTRACK_USER_MONTH = Number(process.env.MISTTRACK_USER_MONTH ?? 15);
let deviceUsage = {};   // 端末ID → { day, count, month, monthCount }
try {
  if (fs.existsSync(DEVICE_USAGE_FILE)) {
    deviceUsage = JSON.parse(fs.readFileSync(DEVICE_USAGE_FILE, 'utf8')) || {};
    console.log(`[LabelAPI] 利用者ごとの記録 ${Object.keys(deviceUsage).length}件を復元`);
  }
} catch (e) { console.error('[LabelAPI] 利用者記録の読み込み失敗:', e.message); }
function saveDeviceUsage() {
  fsp.writeFile(DEVICE_USAGE_FILE, JSON.stringify(deviceUsage), 'utf8')
    .catch(e => console.error('[LabelAPI] 利用者記録の保存失敗:', e.message));
}
function deviceUsageOf(device) {
  const d = labelDayKey(), m = labelMonthKey();
  let u = deviceUsage[device];
  if (!u) u = deviceUsage[device] = { day: d, count: 0, month: m, monthCount: 0 };
  if (u.day !== d)   { u.day = d; u.count = 0; }
  if (u.month !== m) { u.month = m; u.monthCount = 0; }
  return u;
}
function deviceQuotaOk(device) {
  if (!device) return true;                      // 端末IDが無い経路は全体の上限だけで守る
  const u = deviceUsageOf(device);
  if (u.monthCount >= MISTTRACK_USER_MONTH) { console.warn(`[LabelAPI] この利用者の今月分が上限（${device}）`); return false; }
  if (u.count      >= MISTTRACK_USER_DAILY) { console.warn(`[LabelAPI] この利用者の本日分が上限（${device}）`); return false; }
  return true;
}
const MISTTRACK_COIN = { btc: 'BTC', eth: 'ETH', tron: 'USDT-TRC20' };
/* 対象外のチェーンに投げても名前は返らず、回数だけ減る。
   MistTrackはETH・BTC・TRON系など21チェーンに対応するが、XRPは含まれない。 */
function misttrackSupports(chain) { return !!MISTTRACK_COIN[chain]; }

/* XRPScanのアカウント名。取引所名が入る場所が2か所あり、どちらか一方しか
   埋まっていないことがある（実測：Binanceはname、Bitstampはusername）。
   verified が付いているものは、ドメイン所有の確認が済んだアカウント。 */
function xrpAccountName(j) {
  const a = (j && j.accountName) || {};
  const name = (a.name || a.username || j.username || '').trim();
  return name;
}

/* 住所プロファイル。そのアドレスが「何者か」を返す。
   取引先分析が「どこに着いたか」を解くのに対し、こちらは
   過去に詐欺として報告されているか・ENSやTwitterが紐づいているかを見る。
   引く相手は着金先ではなく、被害者が最初に送った相手（犯人が指定したアドレス）。
   そこが報告に載っている可能性がいちばん高い。
   ※ エンドポイント名は address_profile ではなく address_trace（要注意）。 */
const MISTTRACK_PROFILE_FREE = Number(process.env.MISTTRACK_PROFILE_FREE ?? 0);
const MISTTRACK_PROFILE_PAID = Number(process.env.MISTTRACK_PROFILE_PAID ?? 1);
const PROFILE_CACHE_FILE = path.join(DATA_DIR, 'profile-cache.json');
const profileCache = new Map();   // 小文字アドレス → 整形済みプロフィール（null＝引いたが何も無し）
try {
  const saved = JSON.parse(fs.readFileSync(PROFILE_CACHE_FILE, 'utf8'));
  for (const [addr, p] of Object.entries(saved)) profileCache.set(addr, p);
  console.log(`[Profile] キャッシュ ${profileCache.size}件を読み込み`);
} catch { /* 初回は無い */ }
function saveProfileCache() {
  fsp.writeFile(PROFILE_CACHE_FILE, JSON.stringify(Object.fromEntries(profileCache), null, 2), 'utf8')
    .catch(e => console.error('[Profile] キャッシュ保存失敗:', e.message));
}
function profileApiUrl(addr, chain) {
  const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
  return `${MISTTRACK_BASE}/address_trace?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`;
}
/* 不正事案の種別。報告書にそのまま載るので、断定を避けた日本語にする。 */
const MALICIOUS_LABEL = {
  phishing:   'フィッシング（偽サイト・偽アプリによる詐取）',
  ransom:     '恐喝・ランサムウェア',
  stealing:   '窃取（不正送金・ハッキング）',
  laundering: '資金洗浄',
};
/* 応答は data の下に use_platform / malicious_event / relation_info。
   それぞれ { 種別: { count, 種別_list } } という形。 */
function pickProfileFromResponse(j) {
  const d = (j && j.data) || {};
  const bucket = (obj, key) => {
    const b = (obj || {})[key] || {};
    const list = Array.isArray(b[`${key}_list`]) ? b[`${key}_list`].filter(v => typeof v === 'string' && v.trim()) : [];
    return { count: Number(b.count) || 0, list };
  };
  const malicious = [];
  for (const key of Object.keys(MALICIOUS_LABEL)) {
    const b = bucket(d.malicious_event, key);
    if (b.count > 0 || b.list.length) malicious.push({ 種別: MALICIOUS_LABEL[key], 件数: b.count, 事例: b.list });
  }
  const platforms = {};
  for (const key of ['exchange', 'dex', 'mixer', 'nft']) {
    const b = bucket(d.use_platform, key);
    if (b.list.length) platforms[key] = b.list;
  }
  const relation = {};
  for (const key of ['wallet', 'ens', 'twitter']) {
    const b = bucket(d.relation_info, key);
    if (b.list.length) relation[key] = b.list;
  }
  const first = typeof d.first_address === 'string' ? d.first_address.trim() : '';
  const empty = !malicious.length && !Object.keys(platforms).length && !Object.keys(relation).length && !first;
  return empty ? null : { firstAddress: first, malicious, platforms, relation };
}
async function lookupProfileAPI(addr, chain) {
  if (!MISTTRACK_KEY || !misttrackSupports(chain)) return null;
  const lo = addr.toLowerCase();
  if (profileCache.has(lo)) return profileCache.get(lo);
  try {
    const res = await fetchT(profileApiUrl(addr, chain));
    const j   = await res.json();
    if (j && j.success === false) {
      console.warn('[Profile] 失敗応答:', scrubKey(JSON.stringify(j).slice(0, 160)));
      return null;   // キーの誤りや上限。キャッシュしない
    }
    const picked = pickProfileFromResponse(j);
    profileCache.set(lo, picked);
    saveProfileCache();
    console.log(`[Profile] ${addr.slice(0, 10)}... → ${picked ? `不正事案${picked.malicious.length}種・ENS${(picked.relation.ens || []).length}件` : '該当なし'}`);
    return picked;
  } catch (e) {
    console.error('[Profile] 照会失敗:', addr.slice(0, 12), scrubKey(e.message));
    return null;
  }
}

/* AMLリスクスコア。そのアドレスが不正な資金とどれだけ近いかを 3〜100 で返す。
   素性（address_trace）が「報告されているか」を見るのに対し、こちらは
   制裁対象・窃取・ミキサーとの距離を、ホップ数と割合つきで返す。
   有料レポートでのみ引く（費用を売上にひもづける）。無料調査は従来どおり
   「匿名化・スワップ経由」「ブリッジ・DEX経由」の検出だけ。
   ※ このエンドポイントだけ v3。MISTTRACK_BASE は v1 なので差し替える。 */
/* ── 対処行動（address_action）と 住所概要（address_overview） ──────
   契約している7エンドポイントのうち、この2つを使っていなかった。

   ★対処行動は「現金化されたか」に答えられる。
     被害者が「どこへ行ったか」の次に知りたいのがここ。
     まだ換金されていなければ凍結に意味があり、済んでいれば別の手を打つ。
   ★住所概要は残高と累計の受払い。「その口座に今も残っているか」を示せる。
     凍結要請の緊急度を伝える材料になる。

   どちらも有料レポートのみ。無料に付けると有料との差が無くなる。 */
const MISTTRACK_ACTION_FREE = Number(process.env.MISTTRACK_ACTION_FREE ?? 0);
const MISTTRACK_ACTION_PAID = Number(process.env.MISTTRACK_ACTION_PAID ?? 1);
const MISTTRACK_OVERVIEW_FREE = Number(process.env.MISTTRACK_OVERVIEW_FREE ?? 0);
const MISTTRACK_OVERVIEW_PAID = Number(process.env.MISTTRACK_OVERVIEW_PAID ?? 1);
const ACTION_CACHE_FILE   = path.join(DATA_DIR, 'action-cache.json');
const OVERVIEW_CACHE_FILE = path.join(DATA_DIR, 'overview-cache.json');
const actionCache   = new Map();
const overviewCache = new Map();
for (const [file, map, name] of [[ACTION_CACHE_FILE, actionCache, 'Action'],
                                 [OVERVIEW_CACHE_FILE, overviewCache, 'Overview']]) {
  try {
    for (const [k, v] of Object.entries(JSON.parse(fs.readFileSync(file, 'utf8')))) map.set(k, v);
    console.log(`[${name}] キャッシュ ${map.size}件を読み込み`);
  } catch { /* 初回は無い */ }
}
const saveActionCache   = () => fsp.writeFile(ACTION_CACHE_FILE,   JSON.stringify(Object.fromEntries(actionCache)),   'utf8').catch(() => {});
const saveOverviewCache = () => fsp.writeFile(OVERVIEW_CACHE_FILE, JSON.stringify(Object.fromEntries(overviewCache)), 'utf8').catch(() => {});

/* 応答の形はドキュメントと実データで揺れることがあるので、
   在りそうな名前を順に見て、無ければ黙って諦める（落とさない）。 */
const num = v => { const n = Number(v); return Number.isFinite(n) ? n : null; };
function pickActionFromResponse(j) {
  const d = (j && (j.data || j.result)) || j || {};
  const out = {};
  // 現金化・入出金の傾向。名前の候補を広めに拾う
  const dep = num(d.deposit_amount ?? d.total_deposit ?? d.deposit);
  const wdr = num(d.withdraw_amount ?? d.total_withdraw ?? d.withdraw);
  if (dep != null) out.入金額 = dep;
  if (wdr != null) out.出金額 = wdr;
  const plat = d.platform || d.platforms || d.exchange || d.cashout;
  if (Array.isArray(plat) && plat.length) out.利用先 = plat.map(p => (typeof p === 'string' ? p : p.name || p.platform)).filter(Boolean).slice(0, 8);
  const first = d.first_seen || d.first_tx_time || d.first_time;
  const last  = d.last_seen  || d.last_tx_time  || d.last_time;
  if (first) out.最初の活動 = String(first);
  if (last)  out.最後の活動 = String(last);
  return Object.keys(out).length ? out : null;
}
function pickOverviewFromResponse(j) {
  const d = (j && (j.data || j.result)) || j || {};
  const out = {};
  const bal = num(d.balance);
  const rec = num(d.received_amount ?? d.total_received ?? d.received);
  const snt = num(d.spent_amount ?? d.total_spent ?? d.sent_amount ?? d.sent);
  const cnt = num(d.txs_count ?? d.tx_count ?? d.transaction_count);
  if (bal != null) out.残高 = bal;
  if (rec != null) out.累計受取 = rec;
  if (snt != null) out.累計送金 = snt;
  if (cnt != null) out.取引回数 = cnt;
  const first = d.first_seen || d.first_tx_time;
  const last  = d.last_seen  || d.last_tx_time;
  if (first) out.最初の活動 = String(first);
  if (last)  out.最後の活動 = String(last);
  return Object.keys(out).length ? out : null;
}
/* 外部APIの日時は UNIX秒・ミリ秒・ISO文字列のどれでも来る。
   数値のまま報告書に出ると「1758921743」となって読めない。
   判断できないものは、いじらずそのまま出す（勝手な解釈で誤った日付にしない）。 */
function fmtUnixOrText(v) {
  const s = String(v).trim();
  if (/^\d{10}$/.test(s)) return new Date(Number(s) * 1000).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  if (/^\d{13}$/.test(s)) return new Date(Number(s)).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  const d = new Date(s);
  if (!isNaN(d.getTime()) && /\d{4}/.test(s)) return d.toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  return s;
}

async function lookupMistTrackSimple(kind, addr, chain) {
  const conf = kind === 'action'
    ? { path: 'address_action',   cache: actionCache,   save: saveActionCache,   pick: pickActionFromResponse,   tag: 'Action' }
    : { path: 'address_overview', cache: overviewCache, save: saveOverviewCache, pick: pickOverviewFromResponse, tag: 'Overview' };
  if (!MISTTRACK_KEY || !misttrackSupports(chain)) return null;
  const lo = addr.toLowerCase();
  if (conf.cache.has(lo)) return conf.cache.get(lo);
  try {
    const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
    const res = await fetchT(`${MISTTRACK_BASE}/${conf.path}?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`);
    const j = await res.json();
    if (j && j.success === false) {
      console.warn(`[${conf.tag}] 失敗応答:`, scrubKey(JSON.stringify(j).slice(0, 160)));
      return null;   // キーの誤りや上限。キャッシュしない
    }
    const picked = conf.pick(j);
    conf.cache.set(lo, picked);
    conf.save();
    console.log(`[${conf.tag}] ${addr.slice(0, 10)}... → ${picked ? Object.keys(picked).join('・') : '該当なし'}`);
    return picked;
  } catch (e) {
    console.error(`[${conf.tag}] 照会失敗:`, addr.slice(0, 12), scrubKey(e.message));
    return null;
  }
}

const MISTTRACK_RISK_FREE = Number(process.env.MISTTRACK_RISK_FREE ?? 0);
const MISTTRACK_RISK_PAID = Number(process.env.MISTTRACK_RISK_PAID ?? 1);
const RISK_CACHE_FILE = path.join(DATA_DIR, 'risk-cache.json');
const riskCache = new Map();   // 小文字アドレス → 整形済みリスク（null＝引いたが何も無し）
try {
  const saved = JSON.parse(fs.readFileSync(RISK_CACHE_FILE, 'utf8'));
  for (const [addr, r] of Object.entries(saved)) riskCache.set(addr, r);
  console.log(`[Risk] キャッシュ ${riskCache.size}件を読み込み`);
} catch { /* 初回は無い */ }
function saveRiskCache() {
  fsp.writeFile(RISK_CACHE_FILE, JSON.stringify(Object.fromEntries(riskCache), null, 2), 'utf8')
    .catch(e => console.error('[Risk] キャッシュ保存失敗:', e.message));
}
function riskApiUrl(addr, chain) {
  const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
  const base = MISTTRACK_BASE.replace(/\/v\d+$/, '/v3');
  return `${base}/risk_score?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`;
}
/* 被害に遭われた方が読む文章になる。英語のまま出さない。
   知らない値が増えたときは原文のまま通す（黙って消すと気づけない）。 */
const RISK_LEVEL_JA = { Low: '低い', Moderate: '中程度', High: '高い', Severe: '非常に高い' };
const RISK_DETAIL_JA = {
  'Malicious Address':                          '悪質なアドレスとして登録されています',
  'Suspected Malicious Address':                '悪質なアドレスの疑いがあります',
  'High-risk Tag Address':                      '高リスクのタグが付いています',
  'Medium-risk Tag Address':                    '中リスクのタグが付いています',
  'Mixer':                                      '匿名化サービス（ミキサー）です',
  'Sanctioned Entity':                          '制裁対象として指定された事業者です',
  'Risk Exchange':                              'リスクのある取引所です',
  'Gambling':                                   'ギャンブル関連です',
  'Involved Theft Activity':                    '窃取（ハッキング・不正送金）に関与しています',
  'Involved Ransom Activity':                   '恐喝・ランサムウェアに関与しています',
  'Involved Phishing Activity':                 'フィッシングに関与しています',
  'Involved Illicit Activity':                  '不正な活動に関与しています',
  'Interact With Malicious Address':            '悪質なアドレスとやり取りがあります',
  'Interact With Suspected Malicious Address':  '悪質な疑いのあるアドレスとやり取りがあります',
  'Interact With High-risk Tag Address':        '高リスクのアドレスとやり取りがあります',
  'Interact With Medium-risk Tag Addresses':    '中リスクのアドレスとやり取りがあります',
};
const RISK_TYPE_JA = {
  sanctioned_entity: '制裁対象', illicit_activity: '不正な活動', mixer: '匿名化サービス',
  gambling: 'ギャンブル', risk_exchange: 'リスクのある取引所', bridge: 'ブリッジ',
};
/* 応答は data の下に score / risk_level / detail_list / risk_detail / hacking_event。
   risk_report_url も返るがアクセストークン付きなので保存も表示もしない。 */
function pickRiskFromResponse(j) {
  const d = (j && j.data) || {};
  const score = Number(d.score);
  if (!Number.isFinite(score)) return null;
  const details = (Array.isArray(d.detail_list) ? d.detail_list : [])
    .filter(v => typeof v === 'string' && v.trim())
    .map(v => RISK_DETAIL_JA[v] || v);
  /* 割合の大きい順に3件。全部載せると読み手が要点を掴めない。 */
  const exposures = (Array.isArray(d.risk_detail) ? d.risk_detail : [])
    .filter(x => x && typeof x.entity === 'string' && x.entity.trim())
    .sort((a, b) => (Number(b.percent) || 0) - (Number(a.percent) || 0))
    .slice(0, 3)
    .map(x => ({
      相手:   x.entity.trim(),
      種別:   RISK_TYPE_JA[x.risk_type] || x.risk_type || '',
      経路:   x.exposure_type === 'direct' ? '直接' : '間接',
      ホップ: Number(x.hop_num) || 0,
      割合:   Number(x.percent) || 0,
    }));
  const level = typeof d.risk_level === 'string' ? d.risk_level.trim() : '';
  const hacking = typeof d.hacking_event === 'string' ? d.hacking_event.trim() : '';
  return { score, level, levelJa: RISK_LEVEL_JA[level] || level, details, exposures, hacking };
}
async function lookupRiskAPI(addr, chain) {
  if (!MISTTRACK_KEY || !misttrackSupports(chain)) return null;
  const lo = addr.toLowerCase();
  if (riskCache.has(lo)) return riskCache.get(lo);
  try {
    const res = await fetchT(riskApiUrl(addr, chain));
    const j   = await res.json();
    if (j && j.success === false) {
      console.warn('[Risk] 失敗応答:', scrubKey(JSON.stringify(j).slice(0, 160)));
      return null;   // キーの誤りや上限。キャッシュしない
    }
    const picked = pickRiskFromResponse(j);
    riskCache.set(lo, picked);
    saveRiskCache();
    console.log(`[Risk] ${addr.slice(0, 10)}... → ${picked ? `${picked.score}/100（${picked.level}）・指標${picked.details.length}件` : '該当なし'}`);
    return picked;
  } catch (e) {
    console.error('[Risk] 照会失敗:', addr.slice(0, 12), scrubKey(e.message));
    return null;
  }
}

/* 経路上のアドレスの「取引回数」と「名前が付いたか」を貯める。
   MistTrackを引くかどうかのしきい値を、見当ではなく分布で決めるため。
   すでに取得済みの値を書くだけなので、外部APIは一切使わない。 */
const HOPSTATS_FILE = path.join(DATA_DIR, 'hop-stats.json');
const HOPSTATS_MAX  = 3000;   // 貯めすぎない。分布を見るには十分
let hopStats = [];
try { hopStats = JSON.parse(fs.readFileSync(HOPSTATS_FILE, 'utf8')) || []; } catch { /* 初回は無い */ }
let hopStatsDirty = false;
function recordHopStat(node, chain, idx, total) {
  if (!node || node.txCount == null || !Number.isFinite(node.txCount)) return;
  hopStats.push({
    at: Date.now(), chain, idx, total,
    tx: node.txCount,
    // 名前が付いたか。推定でついた名前は「付いた」に数えない
    named: !!(node.label && !node.inferred),
    inferred: !!node.inferred,
    ex: !!node.isExchange, via: !!node.isVia, token: !!node.isToken,
  });
  if (hopStats.length > HOPSTATS_MAX) hopStats = hopStats.slice(-HOPSTATS_MAX);
  hopStatsDirty = true;
}
/* 書き込みは調査ごとに1回だけ。ノードごとに書くとディスクを叩きすぎる。 */
function saveHopStats() {
  if (!hopStatsDirty) return;
  hopStatsDirty = false;
  fsp.writeFile(HOPSTATS_FILE, JSON.stringify(hopStats), 'utf8')
    .catch(e => console.error('[HopStats] 保存失敗:', e.message));
}

/* 取引先分析（相手方分析）。ラベルが引けなかったときの代替。
   取引所は利用者ごとに使い捨ての入金アドレスを発行するため、そのアドレス自体には
   名前が付かない。しかし「送り先の大半がBinance」なら、Binanceの入金用と分かる。
   1照会につき回数を消費するので、有料調査の着金先だけに使う（既定）。 */
/* 無料の追跡でも取引先分析を引く。月15回・1日5回の上限は共通なので、
   これを1にしても1か月に使う回数の上限は変わらない。変わるのは使い道で、
   「名前だけを15件」より「着金先まで特定できた結果を7件」の方が役に立つ。
   0にすれば無料では引かなくなる。 */
const MISTTRACK_CP_FREE = Number(process.env.MISTTRACK_CP_FREE ?? 1);
const MISTTRACK_CP_PAID = Number(process.env.MISTTRACK_CP_PAID || 1);
/* 上位の取引先がこの割合に満たなければ「よく使う相手」とは言えない。
   0.003%のBinanceを根拠に「Binanceの入金アドレス」とは書けない。 */
const CP_MIN_PERCENT = Number(process.env.MISTTRACK_CP_MIN_PERCENT || 30);
const CP_CACHE_FILE = path.join(DATA_DIR, 'counterparty-cache.json');
const cpCache = new Map();   // 小文字アドレス → [{name,percent}]（[]＝引いたが該当なし）
try {
  const cached = JSON.parse(fs.readFileSync(CP_CACHE_FILE, 'utf8'));
  for (const [addr, list] of Object.entries(cached)) cpCache.set(addr, list);
  console.log(`[Counterparty] キャッシュ ${cpCache.size}件を読み込み`);
} catch { /* 初回は無い */ }
function saveCpCache() {
  fsp.writeFile(CP_CACHE_FILE, JSON.stringify(Object.fromEntries(cpCache), null, 2), 'utf8')
    .catch(e => console.error('[Counterparty] キャッシュ保存失敗:', e.message));
}
function counterpartyApiUrl(addr, chain) {
  const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
  return `${MISTTRACK_BASE}/address_counterparty?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`;
}
/* 応答は { success, msg, address_counterparty_list:[{name,amount,percent}] }。
   ラベル取得と違って data で包まれていない。 */
function pickCounterpartyFromResponse(j) {
  const list = Array.isArray(j && j.address_counterparty_list) ? j.address_counterparty_list : [];
  return list
    .filter(x => x && typeof x.name === 'string' && x.name.trim())
    .map(x => ({ name: x.name.trim(), percent: Number(x.percent) || 0 }))
    // 「Unknown」は名前ではないので落とす
    .filter(x => x.name.toLowerCase() !== 'unknown')
    .sort((a, b) => b.percent - a.percent)
    .slice(0, 5);
}
async function lookupCounterpartyAPI(addr, chain) {
  if (!MISTTRACK_KEY || !misttrackSupports(chain)) return [];
  const lo = addr.toLowerCase();
  if (cpCache.has(lo)) return cpCache.get(lo) || [];
  try {
    const res = await fetchT(counterpartyApiUrl(addr, chain));
    const j   = await res.json();
    if (j && j.success === false) {
      console.warn('[Counterparty] 失敗応答:', scrubKey(JSON.stringify(j).slice(0, 160)));
      return [];   // キーの誤りや上限。キャッシュしない
    }
    const picked = pickCounterpartyFromResponse(j);
    cpCache.set(lo, picked);
    saveCpCache();
    console.log(`[Counterparty] ${addr.slice(0, 10)}... → ${picked.length ? picked.map(c => `${c.name} ${c.percent}%`).join(' / ') : '該当なし'}`);
    return picked;
  } catch (e) {
    console.error('[Counterparty] 照会失敗:', addr.slice(0, 12), scrubKey(e.message));
    return [];
  }
}
/* 取引先の並びから「着金先の取引所」を1つ選ぶ。
   DEX・ブリッジ・トークン契約は通り道であって着金先ではないので飛ばす。 */
function exchangeFromCounterparty(list) {
  for (const c of list || []) {
    if (isTokenContract(c.name) || isViaService(c.name)) continue;
    if (!isExchange(c.name)) continue;
    return c.percent >= CP_MIN_PERCENT ? c : null;   // 上位の取引所が薄ければ諦める
  }
  return null;
}
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
/* 応答例：
     { "success": true, "msg": "",
       "data": { "label_list": ["Binance", "hot"], "label_type": "exchange" } }
   label_list は「事業者名＋種別タグ」の混在。先頭を名前として使い、残りは括弧で添える。
   label_type は exchange / defi / mixer / nft / 空 のいずれか。
   これがあると、名前の文字列を当てにせず種類を判断できる。 */
function pickLabelFromResponse(j) {
  const d = (j && j.data) || {};
  const list = Array.isArray(d.label_list) ? d.label_list.filter(v => typeof v === 'string' && v.trim()) : [];
  let name = '';
  if (list.length) {
    const head = list[0].trim();
    const rest = list.slice(1).map(v => v.trim()).filter(Boolean);
    name = rest.length ? `${head}（${rest.join('・')}）` : head;
  } else {
    // 形が変わった場合に備えて、よくある入れ物も見る
    for (const c of [d.label, d.labels, d.entity, d.name, j && j.label, j && j.name]) {
      if (typeof c === 'string' && c.trim()) { name = c.trim(); break; }
      if (Array.isArray(c) && c.length) { const f = c.find(v => typeof v === 'string' && v.trim()); if (f) { name = f.trim(); break; } }
    }
  }
  const type = typeof d.label_type === 'string' ? d.label_type.trim().toLowerCase() : '';
  return { name, type };
}

function scrubKey(msg) {
  const m = String(msg || '');
  return MISTTRACK_KEY ? m.split(MISTTRACK_KEY).join('***') : m;
}

function labelApiUrl(addr, chain) {
  const coin = MISTTRACK_COIN[chain] || String(chain).toUpperCase();
  return `${MISTTRACK_BASE}/address_labels?coin=${coin}&address=${encodeURIComponent(addr)}&api_key=${MISTTRACK_KEY}`;
}

/* 戻り値は { name, type }。type は exchange / defi / mixer / nft / ''。
   キャッシュは古い形式（文字列）も読めるようにしておく。 */
async function lookupLabelAPI(addr, chain) {
  const empty = { name: '', type: '' };
  if (!MISTTRACK_KEY || !misttrackSupports(chain)) return empty;
  const lo = addr.toLowerCase();
  if (labelCache.has(lo)) {
    const c = labelCache.get(lo);
    return typeof c === 'string' ? { name: c, type: '' } : (c || empty);
  }
  try {
    const res = await fetchT(labelApiUrl(addr, chain));
    const j   = await res.json();
    if (j && j.success === false) {
      console.warn('[LabelAPI] 失敗応答:', scrubKey(JSON.stringify(j).slice(0, 160)));
      return empty;   // キーの誤りや上限。キャッシュしない
    }
    const picked = pickLabelFromResponse(j);
    labelCache.set(lo, picked);
    saveLabelCache();
    if (picked.name) console.log(`[LabelAPI] ${addr.slice(0, 10)}... → "${picked.name}" (${picked.type || '種別なし'})`);
    else console.log('[LabelAPI] 名前なし:', addr.slice(0, 12), JSON.stringify(j).slice(0, 160));
    return picked;
  } catch (e) {
    // 失敗はキャッシュしない（通信断・レート制限なら次の調査で拾える）
    console.error('[LabelAPI] 照会失敗:', addr.slice(0, 12), scrubKey(e.message));
    return empty;
  }
}

function isExchange(label) {
  if (!label) return false;
  // トークンコントラクトは取引所ではない（「Binance: BNB Token」のように
  // 取引所名を含む名前もあるため、先に弾く）
  if (isTokenContract(label)) return false;
  /* ★DEX・ブリッジ・ルーターも取引所ではない。
     EX_KEYWORDS には歴史的に VIA_KEYWORDS の語が丸ごと入っており
     （41語が重複）、`uniswap` を含む名前まで取引所と判定していた。
     たとえば UniswapV2Pair が「到達した取引所」として報告書に載ると、
     利用者は Uniswap に凍結を依頼しようとする。
     しかし DEX は運営者が資金を止められる仕組みではないので、
     そこは行き止まりであって、要請先ではない。
     ホップ選択の側では !isVia で除いていたが、
     最初の送金先とトークン受取人の判定では除いていなかった。 */
  if (isViaService(label)) return false;
  if (isContractName(label)) return false;
  return EX_KEYWORDS.some(k => label.toLowerCase().includes(k));
}

/* ★契約の名前は、取引所の名前ではない。
   実測（第4-Y節）：0x6352a56c… が「OpenOceanExchangeProxy」という名前で
   凍結要請先の一覧に載っていた。OpenOcean は DEX アグリゲーターで、
   運営者が資金を止められる仕組みではない。要請しても止まらない。
   EX_KEYWORDS の 'exchange' に当たっていたのが原因。

   DEX を1つずつ語彙に足しても、次に出てきた名前でまた同じことが起きる。
   ★形で見分ける：ソースコードから来る契約名は
     「空白なしのキャメルケース」（OpenOceanExchangeProxy・ButterRouterV3）。
     取引所のラベルは「Binance 14」「Crypto.com Exchange」のように
     空白か数字を伴うか、「OKX」「Coinbase」のように大文字の山が1つ以下。

   契約らしい語（exchange・swap・router 等）を含み、かつ
   キャメルケースの1語である場合だけ落とす。取引所名は巻き込まない。 */
const CONTRACTISH = ['exchange', 'swap', 'router', 'proxy', 'adapter', 'aggregator',
  'settler', 'bridge', 'pool', 'vault', 'handler', 'executor', 'forwarder', 'factory'];

function isContractName(label) {
  const s = String(label || '').trim();
  if (!s || /[\s:：]/.test(s)) return false;                    // 空白や区切りを含む＝ラベル
  if (!CONTRACTISH.some(k => s.toLowerCase().includes(k))) return false;
  const caps = (s.match(/[A-Z]/g) || []).length;
  const lows = (s.match(/[a-z]/g) || []).length;
  return caps >= 2 && lows >= 2;                                // キャメルケースの1語
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
  /* ★「500回以上・残高ゼロ」で取引所と推定するのはやめた。
     それは詐欺師が資金を素通りさせる中継ウォレットの典型でもある。
     取引所と見なすと、そこを「到達先」として追跡を打ち切ってしまい、
     本当の到達先（＝凍結を頼む相手）に辿り着けない。
     実測：505回・残高0のアドレスを取引所と判定して停止し、
     その先にあった Binance を見失っていた。
     取引回数が多いこと自体は、画面の注意書きで別途伝えている。 */
  return null;
}

/* 入金用アドレスの推定。
   条件＝次のノードが取引所で、自分は「取引回数が少なく残高をほぼ持たない」。
   取引所のホットウォレット（取引回数が数万回）と取り違えないよう、
   回数の少なさを条件に入れている。 */
/* 利用者が多いコントラクトの目安。これ以上の取引があるDEX・ブリッジ・
   トークン契約は、その先を追っても同一資金と言えない。 */
const VIA_TRAFFIC_STOP = 10000;
/* 利用者が多いアドレスを通った先は、同一資金と言えないので打ち切る。

   ★ラベルの有無で判断してはいけない。
     実測：同じ取引を2回調べたら行き先が変わった。
       1回目 … → MainnetSettler → 0x4b36b6a5…（4.58 ETH）
       2回目 … → MainnetSettler → 0x510b2d8e…（20.03 ETH）
     MainnetSettler は取引回数 373,001 回の共有決済コントラクトで、
     無数の人の資金が通る。そこから「金額が最大の送金」を選ぶと、
     新しい取引が流れ込むたびに別人の資金を掴む。
     2回目の 20.03 ETH は被害額 4.87 ETH より多く、明らかに他人の資金。

     それでも素通りしていたのは、打ち切りの条件が
     「経由サービス」「トークン契約」というラベル付きのノードに
     限られていたため。MainnetSettler はどちらのラベルも持たない。

   ★取引所は打ち切らない。そこが到達先＝要請先そのものなので、
     取引回数が多いのは当たり前。

   ★2026-08-26 方針変更：経路を切り落とすのをやめ、印を付けて全部見せる。
     利用者の指摘（記録：第4-Z節）——
       「利用者が多いからといって、その先が同じ資金でないと断言もできない」
     そのとおりで、切る側にも根拠は無い。暗号資産に名前は書かれておらず、
     ★「同じ資金である保証が無い」のは経路全体の前提であって、
       混雑した地点から急に始まる話ではない。
     切り落とすと、被害者は行き先を知る手段そのものを失う。
     見せたうえで「同一資金の保証は無い」と添える方が、判断材料が多い。
     判断するのは読み手（被害者・弁護士・警察）。 */
function truncateAfterVia(path) {
  /* 印を付けた地点より先を「確度が下がる区間」として記す。切り落とさない。 */
  const markAfter = (i, reason) => {
    path[i].traceStop  = true;
    path[i].stopReason = reason;
    for (let k = i + 1; k < path.length; k++) path[k].afterStop = true;
    if (i < path.length - 1) {
      console.log(`[trace] index ${i}（${reason}）以降は確度が下がる区間として表示`);
    }
  };
  for (let i = 1; i < path.length; i++) {
    const n = path[i];
    // 到達先の取引所は打ち切らない（そこが目的地）
    if (n.isExchange) continue;
    const crowded = n.txCount != null && n.txCount >= VIA_TRAFFIC_STOP;
    /* 情報を取れなかった区間は「混雑していないと確かめられていない」。 */
    if (n.unverified) { markAfter(i, 'unverified'); return; }
    if (!n.isVia && !n.isToken && !crowded) continue;
    // 取引が少ない小規模なサービスは、まだ追える見込みがあるので続ける
    // 取引回数が取れないことがある（WETHは0で返ってきた）。その場合は打ち切る側に倒す。
    if ((n.isVia || n.isToken) && !crowded
        && n.txCount != null && n.txCount > 0) continue;
    // 次のノードを同じ取引の中から特定できているなら、推測ではないので続ける
    if (path[i + 1] && path[i + 1].sameTx) continue;
    console.log(`[trace] ${n.label || 'このアドレス'}（取引${n.txCount ?? '不明'}回）から先は確度が下がる`);
    markAfter(i, crowded ? 'crowded' : 'via');
    return;
  }
}

const DEPOSIT_MAX_TX = 50;
function markDepositAddresses(path) {
  for (let i = 1; i < path.length - 1; i++) {
    const node = path[i], next = path[i + 1];
    if (!node || !next || node.isExchange || node.isVia || node.isToken) continue;
    if (!(next.isExchange && !next.isVia && !next.isToken)) continue;
    if (node.txCount == null || node.txCount > DEPOSIT_MAX_TX) continue;
    if (node.balance != null && node.balance > 0.01) continue;
    node.isDeposit  = true;
    node.depositFor = next.label || '';
    if (!node.label) node.label = '取引所の入金用アドレス（推定）';
    console.log(`[Deposit] 入金用アドレスと推定: ${node.address?.slice(0, 10)}... → ${next.label || '取引所'}`);
  }
}

// ══ アドレス残高・TX件数取得 ══════════════════════════════════

const priceCache = new Map(); // chain → { price, ts }

async function getUSDPrice(chain) {
  const key = chain.toLowerCase();
  const cached = priceCache.get(key);
  if (cached && Date.now() - cached.ts < 300000) return cached.price; // 5分キャッシュ
  try {
    const ids = { btc: 'bitcoin', eth: 'ethereum', xrp: 'ripple',
                  tron: 'tron', polygon: 'matic-network' }[key];
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
/* ══ どこが遅いかを後から見られるようにする ══════════════════
   ★調査が時間切れになったとき、Railway のログを見ないと原因が分からず、
     推測で削っては外すことを3回繰り返した（第5-G節）。
     外側から封じ込めるだけでは、同じことがまた起きる。

   ★記録は「遅かったもの」だけに絞る。全部残すと量が多すぎて読めないし、
     速い呼び出しの記録には診断上の価値がない。
   ★アドレスやTXIDはそのまま残さない。問い合わせ先（どのサービスの何を
     呼んだか）が分かれば原因は追えるので、中身は削る。 */
/* Blockchair のアドレス照会は、実測で7回中4回が失敗していた（診断画面で判明）。
   ★返ってこない相手を6秒待つのは、そのぶん他を諦めることになる。
   短く見切って、Etherscan の残高に切り替える。 */
const BLOCKCHAIR_TIMEOUT_MS = 2500;

const SLOW_CALL_MS = 1500;
const SLOW_KEEP    = 120;
const slowCalls    = [];        // { at, host, what, ms, ng }

/* URLから「どのサービスの何を呼んだか」だけを取り出す。鍵や住所は残さない。 */
function callTag(url) {
  try {
    const u = new URL(url);
    const q = u.searchParams;
    const what = [q.get('module'), q.get('action'), q.get('chainid') ? 'chain' + q.get('chainid') : '']
      .filter(Boolean).join('/');
    return { host: u.host, what: what || u.pathname.split('/').slice(0, 4).join('/') };
  } catch { return { host: '?', what: '?' }; }
}

function noteSlowCall(url, ms, ng) {
  if (ms < SLOW_CALL_MS && !ng) return;
  const { host, what } = callTag(url);
  slowCalls.push({ at: new Date().toISOString(), host, what, ms, ng: ng || '' });
  if (slowCalls.length > SLOW_KEEP) slowCalls.splice(0, slowCalls.length - SLOW_KEEP);
}

async function fetchT(url, opts = {}, ms = FETCH_TIMEOUT_MS) {
  const t0 = Date.now();
  try {
    const r = await fetch(url, { ...opts, signal: AbortSignal.timeout(ms) });
    noteSlowCall(url, Date.now() - t0, r.ok ? '' : `HTTP ${r.status}`);
    return r;
  } catch (e) {
    noteSlowCall(url, Date.now() - t0, e.name === 'TimeoutError' ? '時間切れ' : e.message);
    throw e;
  }
}

/* 追跡で使う外部API（Etherscan・Blockchair）の取得。
   ホップが増えて呼び出し回数が増えた分、失敗も増える。一度だけ取り直す。 */
async function apiJson(url) {
  for (let attempt = 1; attempt <= 2; attempt++) {
    try {
      const j = await (await fetchT(url)).json();
      const limited = j && typeof j.result === 'string' && /rate limit/i.test(j.result);
      if (!limited) return j;
      console.warn('[Etherscan] 回数制限。待って取り直します');
    } catch (e) {
      if (attempt === 2) throw e;
      console.warn('[Etherscan] 取得失敗、取り直します:', e.message);
    }
    await new Promise(r => setTimeout(r, 1200));
  }
  return { result: [] };
}
// 以下3つの時間予算は加算される（追跡→付帯情報→内部送金の順に直列実行）。
// 合計が長いと利用者が結果を待ちきれず「調査が出ない」と受け取られるため、
// 初回照会と合わせて約40秒で必ず返るよう配分する。超過分は部分結果で打ち切る。
const TRACE_BUDGET_MS = 27000;   // トークン契約・ブリッジを通過点として追い越すようになり、
                                 // ホップ数が増えた分だけ時間が要る（18秒では取引所の手前で切れていた）
// アドレス情報付与(enrich)の時間予算。USDT等の巨大コントラクトが混じっても全体を止めない。
/* 予算の合計が INVESTIGATE_HARD_TIMEOUT_MS を超えると、
   利用者には「時間内に完了しませんでした」としか出ない（実測で62秒→失敗）。
   TRACE 27 + ENRICH 15 + CALLS 6 = 48秒に収め、上限側にも余裕を持たせる。 */
const ENRICH_BUDGET_MS = 15000;   // 混雑したコントラクトはBlockchairの応答が遅い。ここで足りないと経路を確かめられない
// investigateETH の内部呼び出し(calls)ラベル取得の時間予算。
const CALLS_BUDGET_MS = 6000;
/* ブリッジを渡った先（TRON）を追う時間。参考経路と同時には使わない。
   両方に満額を与えると持ち時間75秒を超え、実測で時間切れになった。 */
const CROSSCHAIN_BUDGET_MS = 20000;
// 上記の予算をすべてすり抜けた場合に調査ジョブを強制終了させる上限時間。
/* ★無料と有料で、待たせ方がまったく違う。
     無料調査   利用者が画面の前で待っている
                → 画面で「1件あたり30秒〜2分」と案内しているので、その内側
     有料レポート ★メールで届ける。待たせていない
                → 「通常10分〜30分ほどで完成します」と案内済み
                → 1件に5分かけてよい

   ★75秒は当社が自分で決めた数字で、外部からの制限ではなかった。
     絞りすぎていたぶん、枝を追う余裕が無かった。 */
const INVESTIGATE_HARD_TIMEOUT_MS = 110000;        // 無料（案内の2分以内）
const INVESTIGATE_HARD_PAID_MS    = 300000;        // 有料（メール配信なので余裕がある）
const investigateHardMs = paid => paid ? INVESTIGATE_HARD_PAID_MS : INVESTIGATE_HARD_TIMEOUT_MS;

/* 同じアドレスを何度も照会しない。
   取引所のホットウォレットや共有コントラクトは、別々の調査でも繰り返し出てくる。
   ★残高は変わるので長くは持たない。10分だけ覚える。
     古い残高を「現在の残高」として出すのは、凍結の判断を誤らせる。 */
const ADDR_INFO_TTL_MS = 10 * 60 * 1000;
const addrInfoCache = new Map();     // "chain:addr" → { at, info }

async function getAddressInfo(addr, chain) {
  const ck = `${chain}:${String(addr).toLowerCase()}`;
  const hit = addrInfoCache.get(ck);
  if (hit && Date.now() - hit.at < ADDR_INFO_TTL_MS) return hit.info;
  const info = await getAddressInfoFresh(addr, chain);
  addrInfoCache.set(ck, { at: Date.now(), info });
  if (addrInfoCache.size > 500) {    // 際限なく溜めない
    for (const k of [...addrInfoCache.keys()].slice(0, 100)) addrInfoCache.delete(k);
  }
  return info;
}

async function getAddressInfoFresh(addr, chain) {
  try {
    if (chain === 'eth') {
      /* ★実測（診断画面 2026-08-27）：この問い合わせが7回中4回失敗し、
         そのたびに上限の6秒を待っていた。1件の調査67秒のうち39秒がここ。
         しかも失敗時に1回やり直すので、1件あたり最大12秒を使っていた。
         ★遅い相手には、待つ時間を短くし、やり直さない。
           待っても返ってこないものを待ち続ける理由がない。 */
      let d = null;
      try {
        const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
        const j = await (await fetchT(url, {}, BLOCKCHAIR_TIMEOUT_MS)).json();
        d = j.data?.[addr.toLowerCase()]?.address || null;
      } catch (e) { console.warn('[AddrInfo] Blockchairが応答せず:', e.message); }

      const price = await getUSDPrice('eth');
      if (d) {
        const balNative = parseFloat(d.balance || 0) / 1e18;
        // Blockchairが持つアドレスラベル・コントラクト名を取得
        const bcLabel   = d.label || d.contract_name || '';
        return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price, bcLabel };
      }
      /* ★返ってこなくても、何も無いよりは残高だけでも出す。
         取引回数は Etherscan では数えられないので null にする。
         0 を入れると「使われていないアドレス」と読まれる。 */
      try {
        const b = await apiJson(esUrl('eth', `module=account&action=balance&address=${addr}&tag=latest`));
        const wei = String(b.result ?? '');
        if (/^\d+$/.test(wei)) {
          const balNative = Number(wei) / 1e18;
          return { balance: balNative, txCount: null, balanceUSD: balNative * price, bcLabel: '' };
        }
      } catch (e) { console.error('[AddrInfo] Etherscanの残高も取れず:', e.message); }
      return null;
    }
    /* ★Ethereum 以外のEVMチェーン。
       Blockchair は Ethereum しか扱わないので、そこへ問い合わせてはいけない。
       同じ形のアドレスが Ethereum にも存在するため、★別チェーンの残高を
       そのアドレスのものとして表示してしまう。 */
    if (isEVM(chain)) {
      const j = await apiJson(esUrl(chain, `module=account&action=balance&address=${addr}&tag=latest`));
      const wei = String(j.result ?? '');
      if (!/^\d+$/.test(wei)) return null;
      const balNative = Number(wei) / 1e18;
      const price = await getUSDPrice(EVM_CHAINS[chain].priceKey);
      /* ★取引回数は取れない。Etherscanに件数を返す口が無く、
         nonce（自分が出した数）は受け取りを含まないので代用できない。
         0 を入れると「取引0回＝使われていない」と読まれるので入れない。
         数えられないものを数えたことにしない。 */
      return { balance: balNative, txCount: null, balanceUSD: balNative * price, bcLabel: '' };
    }
    if (chain === 'btc') {
      const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const j = await apiJson(url);
      const d = j.data?.[addr]?.address;
      if (!d) return null;
      const balNative = parseFloat(d.balance || 0) / 1e8;
      const price     = await getUSDPrice('btc');
      const bcLabel   = d.label || '';
      return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price, bcLabel };
    }
    if (chain === 'tron') {
      const r = await fetchT(`${TRONGRID}/v1/accounts/${addr}`, { headers: tronHeaders() });
      const j = await r.json();
      const d = (j.data || [])[0] || {};
      /* 被害の大半はUSDTなので、TRXの残高よりUSDTの残高を見たい。
         trc20 は [{コントラクト: 残高}] の配列で返る。 */
      const usdtEntry = (d.trc20 || []).find(o => o && o[TRON_USDT] != null);
      const usdt = usdtEntry ? Number(usdtEntry[TRON_USDT]) / 1e6 : 0;
      const trx  = Number(d.balance || 0) / 1e6;
      /* この応答に取引回数は無い。0を入れると「取引 0回」と出て、
         使われていないアドレスに見えてしまうので入れない。 */
      return { balance: usdt || trx, txCount: null, balanceUSD: usdt || null,
               bcLabel: tronTags.get(addr) || '' };
    }
    if (chain === 'xrp') {
      const r = await fetchT(`https://api.xrpscan.com/api/v1/account/${addr}`);
      const j = await r.json();
      const balNative = parseFloat(j.xrpBalance || 0);
      const price     = await getUSDPrice('xrp');
      // XRPScanのアカウント名（取引所名が入ることが多い）
      const bcLabel   = xrpAccountName(j);
      /* XRPScanのこの応答に取引回数は無い。0を入れると画面に「取引 0回」と
         出てしまい、取引所なのに使われていないように見える。件数は出さない。 */
      return { balance: balNative, txCount: null, balanceUSD: balNative * price, bcLabel };
    }
  } catch (e) { console.error('[AddrInfo]', addr, e.message); }
  return null;
}

/* ══ ブリッジの渡り先を、取引そのものから読む ══════════════════
   ★これまで「チェーンをまたいだ先は公開情報では繋がらない」と判定していた
     （第4-T節・第4-W節）。Dune・Allium・Bitquery・unbridge・Bridgers自社APIを
     すべて実測で落とした。しかし前提が誤っていた。

   ブリッジは「どのチェーンの、どのアドレスへ渡すか」を引数として受け取る。
   ★つまり渡り先は、こちら側の取引の呼び出しデータに最初から書かれている。
     外部サービスも、追加費用も要らない。

   実データで確認（利用者提供の正解経路）：
     0x54129a57… の cross(...) 呼び出し
       4番目のアドレス 0x5486532d51dd715157358d99e44d5e1af47d44f0
       3番目の数値     728126428（TRONのチェーンID）
     → THg8gEMorrryNJSCaTsbJJnGBw7q2bF68Y
       利用者が OKLink で手作業確認した渡り先と完全に一致。
     同じブリッジの他4件でも成立（TRON3件・Arbitrum1件）。

   ★対応していない呼び出しは黙って何も返さない。
     ブリッジごとに引数の形が違うので、確かめた形だけを読む。 */
const BRIDGE_CHAINS = {
  1: 'Ethereum', 10: 'Optimism', 56: 'BNB Chain', 137: 'Polygon', 250: 'Fantom',
  8453: 'Base', 42161: 'Arbitrum', 43114: 'Avalanche', 59144: 'Linea',
  728126428: 'TRON',
};
const TRON_CHAIN_ID = 728126428;
const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';

/* 20バイトのアドレスをTRONの表記に直す。
   TRONは 0x41 を頭に付け、二重SHA-256の先頭4バイトを検査用に足して base58 で書く。 */
function toTronAddress(hex20) {
  const h = String(hex20 || '').replace(/^0x/, '');
  if (!/^[0-9a-fA-F]{40}$/.test(h)) return null;
  const body = Buffer.from('41' + h, 'hex');
  const sum = crypto.createHash('sha256')
    .update(crypto.createHash('sha256').update(body).digest()).digest();
  const full = Buffer.concat([body, sum.subarray(0, 4)]);
  let n = BigInt('0x' + full.toString('hex')), out = '';
  while (n > 0n) { out = B58[Number(n % 58n)] + out; n /= 58n; }
  for (const b of full) { if (b === 0) out = '1' + out; else break; }
  return out;
}

/* Bridgers／TransitSwap の cross(...)。実データで引数の位置を確かめた形だけ読む。 */
const BRIDGE_METHODS = {
  '0x6b3ec416': { addrIdx: 3, chainIdx: 7, amountIdx: 5, name: 'Bridgers／TransitSwap' },
};

/* ★渡り先に「実際にいくら届いたか」を、TRON側の受取記録から読む。
   ブリッジに渡した額（ETH）をそのまま金額照合に使ってはいけない。
   実測：2.9 ETH を渡し、TRON側には 12,409.6 USDT が届いていた。
   ETHの数字で USDT を照合しても一致するはずがなく、
   毎回「合流」と判定されて送金先ごとの合計で選ぶことになる。 */
/* ★TronGridは連続で叩くと断ってくる（回数制限）。
   断られた応答は data を持たないので、そのまま使うと
   ★「送金が無い」と見分けがつかず、追跡が静かに止まる。
   実測：XRPからTRONへ渡った先で1段しか進まず、その先の
   Binance に届かなかった。診断画面に api.trongrid.io の失敗が出ていた。

   ★取得できなかったことと、無いことは違う。
     区別できないまま進むと、誤った結論を静かに出す。
   少し待って1度だけ取り直し、それでも駄目なら「取得できず」と分かる形で返す。 */
/* ★TRONの取得を断られた記録。調査ごとに0に戻す。
   断られたことを黙っていると、利用者には「送金がそこで終わった」と見える。
   実測：この案件はTRON側1段で止まったが、原因は資金の終点ではなく
   TronGridの 429（回数制限）だった。事実と違う結論を静かに出していた。 */
let tronDenied = 0;
function tronDeniedReset() { tronDenied = 0; }
function tronDeniedCount() { return tronDenied; }

async function tronJson(url) {
  for (let i = 1; i <= 2; i++) {
    try {
      const r = await fetchT(url, { headers: tronHeaders() });
      if (r.ok) return await r.json();
      if (i === 2) tronDenied++;
      console.warn(`[TronGrid] 応答 ${r.status}${i === 1 ? '。待って取り直します' : '。諦めます'}`);
    } catch (e) {
      if (i === 2) tronDenied++;
      console.warn(`[TronGrid] 取得失敗: ${e.message}${i === 1 ? '。取り直します' : ''}`);
    }
    if (i === 1) await new Promise(res => setTimeout(res, 1200));
  }
  return null;                       // ★null＝取得できず。空配列（＝無い）とは区別する
}

async function getBridgeArrivalTRON(addr, fromMs) {
  const win = 6 * 3600 * 1000;                       // 払い出しは数分〜数時間遅れる
  try {
    /* 受け手として絞り込む。集約ウォレットは送出に埋もれることがあるため。 */
    const url = `${TRONGRID}/v1/accounts/${addr}/transactions/trc20`
      + `?limit=50&order_by=block_timestamp,asc&only_to=true&min_timestamp=${Math.max(0, fromMs - 60000)}`;
    const j = await tronJson(url);
    if (!j) return null;                 // ★取得できず。無いとは限らない
    for (const t of (j.data || [])) {
      if (t.to !== addr) continue;                   // 受け取りだけ
      if (t.block_timestamp - fromMs > win) break;   // 昇順なので、離れたら打ち切り
      const dec = Number(t.token_info?.decimals != null ? t.token_info.decimals : 6);
      const amount = Number(t.value || 0) / Math.pow(10, dec);
      if (!(amount > 0)) continue;
      return { amount, token: t.token_info?.symbol || 'TRC20',
               time: new Date(t.block_timestamp).toISOString(), txHash: t.transaction_id };
    }
  } catch (e) { console.error('[ブリッジ] 着金の読み取り失敗:', e.message); }
  return null;
}

/* ★対応していないブリッジを、黙って見逃さないための記録。
   実際の依頼で出会った呼び出しだけが、次に足すべきものを教えてくれる。
   ここに残しておけば「どのブリッジを足せば何件救えるか」が数で分かる。
   ★推測で優先順位を決めない。 */
const UNKNOWN_BRIDGE_FILE = path.join(REPORTS_DIR, 'unknown-bridges.json');
let unknownBridges = {};
try {
  if (fs.existsSync(UNKNOWN_BRIDGE_FILE))
    unknownBridges = JSON.parse(fs.readFileSync(UNKNOWN_BRIDGE_FILE, 'utf8')) || {};
} catch (e) { console.error('[ブリッジ] 記録の読み込みに失敗:', e.message); }

function noteUnknownBridge(methodId, contract, txHash, label) {
  if (!methodId || methodId.length !== 10) return;
  const r = unknownBridges[methodId] || { 件数: 0, 契約: [], 例: [], 初回: new Date().toISOString() };
  r.件数++;
  if (contract && !r.契約.includes(contract)) r.契約 = r.契約.concat(contract).slice(0, 5);
  if (txHash && r.例.length < 3) r.例.push(txHash);
  if (label && !r.名前) r.名前 = label;
  r.最終 = new Date().toISOString();
  unknownBridges[methodId] = r;
  fsp.writeFile(UNKNOWN_BRIDGE_FILE, JSON.stringify(unknownBridges), 'utf8').catch(() => {});
  console.log(`[ブリッジ] 未対応の呼び出し ${methodId}（${label || contract}）通算${r.件数}件`);
}

/* ★XRPのブリッジは、渡り先をメモ欄にそのまま書いている。
   実データ（利用者提供・XRP→TRON）：
     {"toToken":"USDT(TRON)|…","destination":"TWgKiwJt1aCwy…", …}
   EVMは呼び出しデータ、XRPはメモ欄。★置き場所が違うだけで、
   「渡り先は送金する側が指定する」という点は同じ。
   だから読める。外部サービスは要らない。

   ★確かめた形以外は名乗らない。鍵の名前はブリッジごとに違うので、
     よくあるものだけを見て、住所の形をしていなければ採用しない。 */
const MEMO_DEST_KEYS = ['destination', 'receiver', 'recipient', 'toAddress', 'to'];

function decodeBridgeMemo(memos) {
  for (const m of (memos || [])) {
    let raw = m?.Memo?.MemoData ?? m?.MemoData ?? '';
    if (typeof raw !== 'string' || !raw) continue;
    /* 記録上は16進のことがある。読めるなら文字に直す。 */
    if (/^[0-9A-Fa-f]+$/.test(raw) && raw.length % 2 === 0 && raw.length > 20) {
      try { raw = Buffer.from(raw, 'hex').toString('utf8'); } catch { /* そのまま使う */ }
    }
    let j = null;
    try { j = JSON.parse(raw); } catch { continue; }
    if (!j || typeof j !== 'object') continue;
    let dest = null;
    for (const k of MEMO_DEST_KEYS) {
      if (typeof j[k] === 'string' && looksLikeAddress(j[k])) { dest = j[k]; break; }
    }
    if (!dest) continue;
    /* 渡り先チェーンは、アドレスの形から決める。
       通貨名の表記（"USDT(TRON)|…"）はブリッジごとに違うので当てにしない。 */
    let chain = null;
    if (/^T[1-9A-HJ-NP-Za-km-z]{33}$/.test(dest)) chain = 'tron';
    else if (/^0x[0-9a-fA-F]{40}$/.test(dest))    chain = 'eth';
    else if (/^r[1-9A-HJ-NP-Za-km-z]{24,34}$/.test(dest)) chain = 'xrp';
    if (!chain) continue;
    const label = { tron: 'TRON', eth: 'Ethereum', xrp: 'XRP' }[chain];
    return { address: dest, chainKey: chain, chainName: label,
             bridge: 'ブリッジ（メモ欄の指定）',
             token: typeof j.toToken === 'string' ? j.toToken.split('|')[0] : undefined };
  }
  return null;
}

function decodeBridgeCall(input) {
  const s = String(input || '').toLowerCase();
  const spec = BRIDGE_METHODS[s.slice(0, 10)];
  if (!spec) return null;
  const w = i => s.slice(10 + i * 64, 10 + (i + 1) * 64);
  if (w(0).length < 64) return null;
  const base = parseInt(w(0), 16) / 32;
  if (!Number.isFinite(base)) return null;
  const rawAddr = w(base + spec.addrIdx);
  const rawChain = w(base + spec.chainIdx);
  if (rawAddr.length < 64 || rawChain.length < 64) return null;
  const hex20 = rawAddr.slice(24);
  if (!/^[0-9a-f]{40}$/.test(hex20) || /^0+$/.test(hex20)) return null;
  const chainId = Number(BigInt('0x' + rawChain));
  if (!BRIDGE_CHAINS[chainId]) return null;          // 知らないチェーンは名乗らない
  const amount = Number(BigInt('0x' + w(base + spec.amountIdx))) / 1e18;
  const address = chainId === TRON_CHAIN_ID ? toTronAddress(hex20) : '0x' + hex20;
  if (!address) return null;
  return { bridge: spec.name, chainId, chainName: BRIDGE_CHAINS[chainId], address,
           amount: Number.isFinite(amount) && amount > 0 ? amount : null };
}

/* 全体の締切までに残っている時間。締切が渡っていなければ従来どおりの予算。
   ★後段（参考経路・ブリッジ先）は「あれば嬉しい」情報なので、
     ここを削ってでも本体を返し切る。何も返さないのが最悪。 */
const INVESTIGATE_SOFT_LIMIT_MS = 96000;         // 無料：上限110秒に対し14秒の余白
const INVESTIGATE_SOFT_PAID_MS  = 280000;        // 有料：上限300秒に対し20秒の余白
const investigateSoftMs = paid => paid ? INVESTIGATE_SOFT_PAID_MS : INVESTIGATE_SOFT_LIMIT_MS;
function budgetLeft(opts, want) {
  const d = opts && opts.hardDeadline;
  if (!Number.isFinite(d)) return want;
  return Math.max(0, Math.min(want, d - Date.now()));
}

/* ══ 分散した資金を、割合を持って追う ══════════════════════
   ★1本だけ追う方式は、資金が分けられる経路に向いていない。
     実測（利用者提供・BTC）：0.85→0.70→0.56→… と13段にわたって
     小分けにされ、13段追っても取引所に届かなかった。
     一方、別の枝は3段で Binance に着いていた。

   ★「どこへ、どれだけ」を出す。
     被害資金の何%がその枝を通ったかを持ち回り、多い順に追う。
     大きい枝ほど凍結の価値が高いので、時間をそこから使う。

   割合の出し方は、送り出した額のうちその枝が占める分を掛けていく。
   増えている（他人の資金と混ざった）場合は1を上限にする。
   ★資金追跡で広く使われる考え方で、根拠を説明できる。 */
const EXPLORE_MAX_VISITS = 24;      // 訪問する地点の上限
const EXPLORE_MAX_DEPTH  = 6;       // 何段先まで見るか
const EXPLORE_MIN_SHARE  = 0.02;    // 2%未満の枝は追わない（数が増えるだけ）
/* ★枝の先の名前を、費用のかからない範囲で引く上限。
   これが無いと、枝の探索は自前DB（19件）に載っている取引所しか見つけられない。
   XRPは3件・TRONは0件しか無く、仕組みが入っていても実際には発火しなかった
   （実測：利用者提供のXRP調査で、3段すべて「未特定」で終わった）。
   ★MistTrackの残り回数は使わない。無料の情報源だけを短い見切りで使う。 */
const EXPLORE_NAME_LOOKUPS    = 8;      // 1回の探索で名前を引く上限
const EXPLORE_NAME_TIMEOUT_MS = 2500;   // 1件あたりの見切り（遅い相手で全体を止めない）
const EXPLORE_NAME_MIN_SHARE  = 0.05;   // 5%未満の枝には引かない（上限を使い切らせない）

/* その地点から出ていった先を、まとめて返す。
   本線として選ばれた1件と、控えに残った送金先を合わせる。 */
async function nextCandidatesAny(addr, time, amountIn, chain) {
  let nx = null;
  try {
    if (chain === 'btc')      nx = await getNextTxBTC(addr, time, amountIn);
    else if (isEVM(chain))    nx = await getNextTxETH(addr, time, amountIn, chain);
    else if (chain === 'xrp') nx = await getNextTxXRP(addr, time, amountIn);
    else if (chain === 'tron')nx = await getNextTxTRON(addr, time, amountIn);
  } catch (e) { console.error('[枝の探索] 取得に失敗:', e.message); }
  if (!nx) return [];
  const one = c => ({ address: c.addr || c.address, amount: c.amount, time: c.time,
                      label: c.label || '', token: c.token, txHash: c.txHash,
                      isExchange: !!c.isExchange });
  return [one(nx), ...(nx._siblings || []).map(one)].filter(c => c.address);
}

function isNamedExchange(label, isEx) {
  const l = String(label || '');
  return !!(isEx && l && !isViaService(l) && !isTokenContract(l));
}

async function exploreArrivals(start, chain, deadline) {
  const seen = new Set([String(start.address).toLowerCase()]);
  const queue = [{ address: start.address, time: start.time, amount: start.amount,
                   share: 1, depth: 0, trail: [] }];
  const arrivals = [], dead = [];
  let visits = 0, nameLookups = 0;
  while (queue.length && visits < EXPLORE_MAX_VISITS && Date.now() < deadline - 3000) {
    queue.sort((a, b) => b.share - a.share);       // 割合の大きい枝から
    const cur = queue.shift();
    if (cur.depth >= EXPLORE_MAX_DEPTH) continue;
    visits++;
    const cands = await nextCandidatesAny(cur.address, cur.time, cur.amount, chain);
    if (!cands.length) { if (cur.share >= 0.05) dead.push(cur); continue; }
    for (const c of cands) {
      const k = String(c.address).toLowerCase();
      if (seen.has(k)) continue;
      /* この枝が運んだ割合。減っていれば分割された分、
         増えていれば他人の資金が混ざったので1を上限にする。 */
      const frac = (Number.isFinite(c.amount) && Number.isFinite(cur.amount) && cur.amount > 0)
        ? Math.min(1, c.amount / cur.amount) : 1;
      const share = cur.share * frac;
      if (share < EXPLORE_MIN_SHARE) continue;
      seen.add(k);
      const trail = cur.trail.concat([c.address]);

      /* ★名前が付いていなければ、無料の情報源に当たってみる。
         XRPScanのアカウント名・TronScanのタグ・Etherscanの契約名など、
         すでに他の場所で使っている無料の口を、ここでも使う。
         引いた結果は覚えるので、同じアドレスに何度も当たらない。 */
      let label = c.label, isEx = c.isExchange;
      if (!label && nameLookups < EXPLORE_NAME_LOOKUPS
          && share >= EXPLORE_NAME_MIN_SHARE && Date.now() < deadline - 4000) {
        nameLookups++;
        label = await Promise.race([
          fetchAddressLabel(c.address, chain).catch(() => ''),
          new Promise(r => setTimeout(() => r(''), EXPLORE_NAME_TIMEOUT_MS)),
        ]) || '';
        if (label) isEx = isExchange(label) && !isViaService(label) && !isTokenContract(label);
      }

      if (isNamedExchange(label, isEx)) {
        arrivals.push({ address: c.address, label, share,
                        amount: c.amount, hops: cur.depth + 1, trail });
        continue;                                  // 着いたらその枝は止める
      }
      queue.push({ address: c.address, time: c.time, amount: c.amount,
                   share, depth: cur.depth + 1, trail });
    }
  }
  arrivals.sort((a, b) => b.share - a.share);
  dead.sort((a, b) => b.share - a.share);
  console.log(`[枝の探索] ${visits}地点を確認、名前を引いた ${nameLookups}件、`
    + `取引所に到達 ${arrivals.length}件`);
  return { arrivals, dead, visits };
}

async function enrichPathWithAddressInfo(path, chain, opts = {}) {
  let exchangeCount = 0;                 // 判明＋推定を合わせた取引所ノード数
  let apiLookups    = 0;                 // 外部ラベルAPIを引いた回数（1調査あたりの上限あり）
  // 有料レポートは名前がそのまま凍結要請の宛先になるので多めに引く
  const lookupBudget = opts.paid ? MISTTRACK_PAID_LOOKUPS : MISTTRACK_FREE_LOOKUPS;
  const deadline = Date.now() + budgetLeft(opts, ENRICH_BUDGET_MS);  // 巨大コントラクト混在でも全体を止めない
  let truncatedAt = -1;                            // 途中で打ち切った位置（-1＝最後まで回った）
  /* ★最終到達先を最初に調べる。
     以前は経路の順に調べていたので、時間が足りないと★一番重要な最終到達先が
     真っ先に切り捨てられていた。取引所かどうかの推定は取引回数から行うため、
     情報が無いと「取引所に到達していない」という報告書になる。
     実測：到達先の取引回数が取れず、推定が消え、凍結要請先が空になった。
     被害者が最も知りたい一点なので、時間の使い方の優先順位を逆にする。 */
  const order = [];
  if (path.length > 1) order.push(path.length - 1);
  for (let i = 0; i < path.length; i++) if (i !== path.length - 1 || path.length <= 1) order.push(i);
  for (const idx of order) {
    const node = path[idx];
    if (!node.address) continue;
    if (node._enriched) continue;
    node._enriched = true;
    if (Date.now() > deadline) {
      console.log(`[enrich] 時間予算に達したため残りノードの情報付与を省略`);
      /* ★ここから先は取引回数が分からない＝「利用者が多いアドレスか」を
         判定できない。判定できないまま経路を見せると、共有の決済
         コントラクトを素通りして他人の資金を指してしまう（実測あり）。
         確かめられなかった区間は、確定した経路として出さない。
         ★調べる順番を変えたので、位置ではなく「調べたか」で印を付ける。 */
      for (let k = 0; k < path.length; k++) {
        if (!path[k]._enriched) {
          path[k].unverified = true;
          if (truncatedAt < 0) truncatedAt = k;
        }
      }
      break;
    }
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
    /* 着金先の名前が最優先。回数を手前のノードで使い切ると、肝心の
       到達先が名無しのまま終わる（実際にそうなった）。最後の1回は着金先に残す。 */
    const isLastNode = idx === path.length - 1;
    /* 送金元（起点）は照会しない。被害者自身が使った取引所であり、
       本人に聞けば分かる。有料の回数はその先に使う。 */
    const isSender = idx === 0 || node.role === 'sender';
    if (!node.label && MISTTRACK_KEY && !isSender
        && (isLastNode || inferExchangeByBehavior(node))) {
      const known = labelCache.has(node.address.toLowerCase());
      const budgetOk = isLastNode ? apiLookups < lookupBudget : apiLookups < lookupBudget - 1;
      if (known || (budgetOk && labelQuotaOk(opts.paid, opts.device))) {
        if (!known) { apiLookups++; labelQuotaUse(opts.device); }
        const api = await lookupLabelAPI(node.address, chain);
        if (api.name) {
          node.label = api.name;
          node.labelType = api.type || undefined;
          /* 種別が返るならそれを信じる。名前の文字列判定より確実。
             defi（DEX・ブリッジ）とmixerは着金先ではなく通り道なので、
             取引所としては扱わない。 */
          if (api.type === 'exchange') node.isExchange = true;
          else if (api.type === 'defi' || api.type === 'mixer') { node.isVia = true; node.isExchange = false; }
          else if (!api.type && isExchange(api.name)) node.isExchange = true;
          if (api.type === 'mixer') node.isMixer = true;
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

    /* ③ 2個目の取引所で停止：以降は取引所内移動の可能性が高く意味が薄いため切り捨て

       ★送金元（index 0）は数に入れない。
         被害者が取引所から出金して送っている場合、起点が取引所になるのは当たり前で、
         それは「到達した先」ではない。数えてしまうと、次に取引所らしきものが
         1つ出ただけで打ち切られ、本当の到達先まで辿り着けない。
         実測：Binanceまで9ホップ必要な取引が、3ノードで切られていた。 */
    if (node.isExchange && idx > 0) {
      exchangeCount++;
      if (exchangeCount >= 2) {
        path.splice(idx + 1);
        console.log(`[trace] 2個目の取引所で停止（index ${idx}、以降を切り捨て）`);
        break;
      }
    }
  }

  markDepositAddresses(path);
  truncateAfterVia(path);

  /* ★ブリッジで別のチェーンへ渡っていたら、その渡り先を取引から読む。
     読めたら、そのチェーンで追跡を続ける。
     これまでは「ここから先は追えません」で終わっていた地点（第5-C節）。 */
  /* ★XRPのブリッジは、渡り先をメモ欄に書いている。
     置き場所が違うだけで「渡り先は送金する側が指定する」点は同じ。
     実データ（利用者提供・XRP→TRON）でメモから読めることを確認した。 */
  if (chain === 'xrp') {
    for (const n of path) {
      if (!n.txHash || n.bridgeTo) continue;
      if (budgetLeft(opts, 20000) < 5000) break;
      try {
        const r = await fetchT(`https://api.xrpscan.com/api/v1/tx/${n.txHash}`);
        if (!r.ok) continue;
        const t = await r.json();
        const info = decodeBridgeMemo(t.Memos);
        if (!info) continue;
        n.bridgeTo = { bridge: info.bridge, chainId: null, chainName: info.chainName,
                       address: info.address, amount: n.amount ?? null,
                       arrivedToken: info.token || null };
        console.log(`[ブリッジ] メモ欄から渡り先: ${info.chainName} の ${info.address}`);
        /* 渡り先がTRONなら、そのまま追い続ける。 */
        if (info.chainKey === 'tron') {
          const fromMs = new Date(normalizeTimeStr(n.time || Date.now())).getTime();
          const arr = await getBridgeArrivalTRON(info.address, Number.isFinite(fromMs) ? fromMs : Date.now());
          if (arr) { n.bridgeTo.arrivedAmount = arr.amount; n.bridgeTo.arrivedToken = arr.token; }
          const tHops = await traceHops(info.address, arr?.time || n.time || new Date().toISOString(),
            'tron', 8, Date.now() + budgetLeft(opts, CROSSCHAIN_BUDGET_MS), null, arr?.amount ?? null)
            .catch(() => []);
          if (tHops.length) {
            n.crossChainHops = tHops.map(h => ({
              address: h.address, label: h.label || '', amount: h.amount, token: h.token,
              isExchange: h.isExchange, isVia: h.isVia, time: h.time, txHash: h.txHash,
              pooled: !!h.pooled, poolDests: h.poolDests ?? null }));
            const ex = tHops.find(h => h.isExchange && !h.isVia && !h.isToken);
            if (ex) n.crossChainExchange = { name: ex.label || '取引所（名称未判明）', address: ex.address };
          }
        }
        break;
      } catch (e) { console.error('[ブリッジ] メモ欄の読み取りに失敗:', e.message); }
    }
  }

  if (isEVM(chain)) {
    for (const n of path) {
      if (!n.txHash || n.bridgeTo) continue;
      if (!(n.isVia || n.traceStop)) continue;     // ブリッジらしい地点だけ見る
      if (budgetLeft(opts, 20000) < 4000) break;   // 残り時間が無ければ諦める
      try {
        const j = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=proxy`
          + `&action=eth_getTransactionByHash&txhash=${n.txHash}&apikey=${ETHERSCAN_KEY}`);
        const info = decodeBridgeCall(j.result?.input);
        if (!info) {
          /* ★対応していないブリッジを黙って見逃さない。
             実際の依頼で出会った呼び出しだけが、次に足すべきものを教える。 */
          const mid = String(j.result?.input || '').slice(0, 10);
          if (mid.length === 10 && mid !== '0x00000000') {
            noteUnknownBridge(mid, n.address, n.txHash, n.label);
          }
          continue;
        }
        n.bridgeTo = info;
        console.log(`[ブリッジ] ${info.bridge} → ${info.chainName} の ${info.address}`);
        /* 渡り先がTRONなら、そのまま追い続ける。
           ★被害者が知りたいのは換金先であって、ブリッジの名前ではない。 */
        if (info.chainId === TRON_CHAIN_ID) {
          /* 渡した先に実際にいくら届いたかを読む。ここを取らないと、
             ETHの数字でUSDTを照合することになり、金額の一致がまったく効かない。 */
          const fromMs = new Date(normalizeTimeStr(n.time || Date.now())).getTime();
          const arr = await getBridgeArrivalTRON(info.address, Number.isFinite(fromMs) ? fromMs : Date.now());
          if (arr) {
            info.arrivedAmount = arr.amount;
            info.arrivedToken  = arr.token;
            console.log(`[ブリッジ] 着金: ${arr.amount} ${arr.token}（${arr.time}）`);
          }
          /* ★時間の取り合いに注意。参考経路と足すと持ち時間（75秒）を超え、
             実測で「時間内に完了しませんでした」になった。
             渡り先を追えたなら参考経路は要らないので、その分をこちらに回す。 */
          const tHops = await traceHops(info.address, arr?.time || n.time || new Date().toISOString(),
            'tron', 8, Date.now() + budgetLeft(opts, CROSSCHAIN_BUDGET_MS), null, arr?.amount ?? null).catch(() => []);
          if (tHops.length) {
            n.crossChainHops = tHops.map(h => ({
              address: h.address, label: h.label || '', amount: h.amount, token: h.token,
              isExchange: h.isExchange, isVia: h.isVia, time: h.time, txHash: h.txHash,
              pooled: !!h.pooled, poolDests: h.poolDests ?? null,
            }));
            /* ★渡った先が「大量に混ぜる場所」なら、それ自体が伝えるべき事実。
               実測：この先は1段で送金先9箇所、2段で26箇所、3段で36箇所に分かれ、
               扱う額も被害額の数百倍だった。個人の財布ではない。
               ここから1本に絞って取引所名を出すのは、根拠のない断定になる。
               ★出せないことを黙るより、規模を数で示す方が捜査の役に立つ。 */
            const spread = tHops.filter(h => h.poolDests > 1).map(h => h.poolDests);
            if (spread.length) n.crossChainSpread = spread;
            const ex = tHops.find(h => h.isExchange && !h.isVia && !h.isToken);
            if (ex) {
              n.crossChainExchange = { name: ex.label || '取引所（名称未判明）', address: ex.address };
              console.log(`[ブリッジ] 渡った先で取引所に到達: ${ex.label || '名称未判明'}`);
            }
          }
        }
        break;                                     // ブリッジは1件読めれば足りる
      } catch (e) { console.error('[ブリッジ] 読み取り失敗:', e.message); }
    }
  }

  /* 打ち切った地点から先を、参考として3件だけ添える。
     何も見えないまま終わるより、状況を判断する材料にはなる。
     確定ではないことは報告書側で明示する。 */
  const stopNode = (path || []).find(p => p.traceStop);

  /* ★合流地点（他人の資金と混ざった場所）も、追跡が確かでなくなる点。
     打ち切っていなくても、そこから先は選ばなかった宛先に正解がありうる。
     実測（第4-X節）：合流地点Cでは正解が金額順2位（44.2%）で、
     本線（55.8%）だけを追うと Binance を落としていた。
     選ばなかった宛先も枝として最後まで追う。 */
  const poolNode = (path || []).find(p => p.pooled && (p.siblings || []).length);

  /* ★打ち切った先を、そのまま最後まで追った経路も「参考」として出す。
     出さないと、混雑した地点で止まるたびに利用者は到達先に辿り着けない。
     被害者が知りたいのは「どこへ換金されたか」なので、
     何も出さないより、確度を明記して出す方が役に立つ。

     確定（＝同じ取引で追えた範囲）と参考（＝最大の送金を追った場合）を
     分けて両方見せる。凍結要請を出す判断は読み手がする。 */
  /* 送金元（index 0）は到達先ではないので数えない。
     「取引所・サービス系ウォレット（推定）」のような振る舞いからの推定も数えない。
     名前が無ければ凍結要請の宛先にならず、利用者にとって到達したことにならない。 */
  const alreadyReached = path.some((p, i) =>
    i > 0 && p.isExchange && !p.inferred && !p.isVia && !p.isToken);

  /* ══ 取引所に届く分岐を探して、本線に採用する ══════════════
     ★利用者の指摘（第5-J節）：同じTXIDを3回調べて3回とも経路が違い、
       取引所名が出たのは1回だけだった。
       「3回調べないと分からない」では、調査として成立していない。

     原因：分岐点でどちらか一方を選び、外れたらそのまま終わっていた。
     どちらを選ぶかは、その時に取れたデータで変わる（＝毎回変わる）。

     ★選び方を変えるのではなく、【確かめてから選ぶ】。
       分岐の候補を実際に数手ずつ追い、取引所に届いた方を本線にする。
       届く先が分かっているなら、推測で選ぶ理由がない。

     直前の分岐から順に試す。分かれてすぐの方が、同じ資金である
     確からしさが高いため。 */
  if (!alreadyReached && isEVM(chain) && budgetLeft(opts, 20000) > 6000) {
    const tried = [];
    const seekDeadline = Date.now() + budgetLeft(opts, 18000);
    outer:
    for (let i = path.length - 1; i >= 1; i--) {
      for (const sib of (path[i].siblings || []).slice(0, 2)) {
        if (!sib.address || tried.length >= 6) break outer;
        if (Date.now() > seekDeadline - 4000) break outer;
        if (path.some(p => String(p.address).toLowerCase() === String(sib.address).toLowerCase())) continue;
        tried.push(sib.address);
        const hops = await traceHops(sib.address, sib.time || path[i].time, chain, 5,
          seekDeadline, null, Number.isFinite(sib.amount) ? sib.amount : null).catch(() => []);
        const exIdx = hops.findIndex(h => h.isExchange && h.label && !h.isVia && !h.isToken);
        if (exIdx < 0) continue;
        /* ★見つけた。この分岐を本線にする。
           元の本線は捨てず、参考として控えに残す（記録は事実なので伏せない）。 */
        const dropped = path.slice(i).map(p => ({ address: p.address, label: p.label || '', amount: p.amount }));
        path.splice(i);
        const db = getLabel(sib.address);
        path.push({ address: sib.address, label: sib.label || db.label || '', amount: sib.amount,
          token: sib.token, time: sib.time, txHash: sib.txHash,
          isExchange: false, branchTaken: true, droppedBranch: dropped });
        for (const h of hops.slice(0, exIdx + 1)) path.push(h);
        console.log(`[分岐探索] ${sib.address.slice(0, 12)}… の先で ${hops[exIdx].label} に到達。この分岐を採用`);
        break outer;
      }
    }
  }

  /* ★資金が分けられている場合、1本追っただけでは行き先が分からない。
     被害資金の何%がどこへ渡ったかを、枝ごとに追って出す。
     ★凍結要請は複数の取引所へ同時に出せるので、全部見つける方が役に立つ。
     有料は時間に余裕がある（メール配信）ので、そのぶん深く探す。 */
  const first = (path || [])[1];
  if (first && first.address && budgetLeft(opts, 40000) > 8000) {
    try {
      const budget = budgetLeft(opts, opts.paid ? 90000 : 25000);
      const found = await exploreArrivals(
        { address: first.address, time: first.time || path[0]?.time, amount: first.amount },
        chain, Date.now() + budget);
      if (found.arrivals.length) {
        path.exploredArrivals = found.arrivals;      // 経路と一緒に持ち回る
        for (const a of found.arrivals) {
          if (!path.some(p => String(p.address).toLowerCase() === String(a.address).toLowerCase())) {
            path.push({ address: a.address, label: a.label, amount: a.amount,
              isExchange: true, exploredShare: a.share, exploredHops: a.hops,
              role: 'explored' });
          } else {
            const n = path.find(p => String(p.address).toLowerCase() === String(a.address).toLowerCase());
            if (n && n.exploredShare == null) n.exploredShare = a.share;
          }
        }
      }
      path.exploredDead = found.dead.slice(0, 3);
    } catch (e) { console.error('[枝の探索] 失敗:', e.message); }
  }

  const reachedAfterSeek = path.some((p, i) =>
    i > 0 && p.isExchange && !p.inferred && !p.isVia && !p.isToken);
  const refNode = stopNode || poolNode;
  /* ★渡り先を追えたなら、参考経路（＝追えないときの代わり）は要らない。
     時間を取り合って全体が時間切れになる（実測）。 */
  const bridgeFollowed = (path || []).some(p => p.bridgeTo && p.crossChainHops);
  if (refNode && isEVM(chain) && refNode.address && !reachedAfterSeek && !bridgeFollowed
      && budgetLeft(opts, 20000) > 4000) {
    const refDeadline = Date.now() + budgetLeft(opts, 20000);
    try {
      /* 1本だけ追うと、混雑した地点では候補が数十件あるため当たりを引けない。
         金額の大きい順に3本追い、取引所に着いたものを全て出す。

         合流地点の場合は、選ばなかった宛先がすでに金額順で手元にある。
         取り直さずにそれを使う（API呼出しを増やさない）。 */
      /* 経路を切り落とさなくなったので、本線がすでに通った宛先は枝から外す。
         同じものを2度見せても判断材料は増えない。 */
      const onPath = new Set((path || []).map(p => String(p.address || '').toLowerCase()));
      const raw = stopNode
        ? await listNextCandidatesETH(stopNode.address, stopNode.time || Date.now(), 4, chain)
        : poolNode.siblings.slice(0, 4).map(s => ({
            address: s.address, label: s.label || '', amount: s.amount,
            time: s.time || poolNode.time, token: s.token, gapMin: 0,
          }));
      const starts = raw.filter(s => !onPath.has(String(s.address || '').toLowerCase())).slice(0, 3);
      const branches = [];
      for (const st of starts) {
        if (Date.now() > refDeadline) { console.log('[参考経路] 時間切れで残りの枝を省略'); break; }
        const hops = await traceHops(st.address, st.time, 'eth', 6, refDeadline).catch(() => []);
        const chainHops = [{ address: st.address, label: st.label || '', amount: st.amount, token: st.token }]
          .concat(hops.map(h => ({ address: h.address, label: h.label || '', amount: h.amount, token: h.token })));
        const exIdx = hops.findIndex(h => h.isExchange && !h.isVia && !h.isToken);
        const ex = exIdx >= 0 ? hops[exIdx] : null;
        branches.push({
          hops: chainHops,
          reachedExchange: ex ? (ex.label || '取引所（名称未判明）') : null,
          reachedAddress:  ex ? ex.address : null,
          reachedHops:     ex ? exIdx + 2 : null,   // 起点の1件を足す
          exchangeUnnamed: !!(ex && !ex.label),
        });
        console.log(`[参考経路] ${st.address.slice(0, 10)}… から${hops.length}ホップ`
          + (ex ? ` → ${ex.label || '名称未判明の取引所'}` : '（取引所には未到達）'));
      }
      if (branches.length) refNode.referenceTrace = { branches };
    } catch (e) { console.error('[参考経路] 失敗:', e.message); }
  }

  /* ★無料調査の外部ラベルは1件あたり1回しか引けない。
     これまでは「最後のノード」に使っていたが、そこは打ち切り地点（ルーター等）で、
     名前が引けても凍結要請の宛先にならない。
     参考経路で取引所に着いていて、その名前が無いなら、そこに使う方が役に立つ。
     被害者が本当に欲しいのは「どこへ換金されたか」の名前。 */
  const unnamed = refNode?.referenceTrace?.branches?.find(b => b.exchangeUnnamed);
  if (unnamed && MISTTRACK_KEY && labelQuotaOk(opts.paid, opts.device)) {
    try {
      labelQuotaUse(opts.device);
      const api = await lookupLabelAPI(unnamed.reachedAddress, chain);
      if (api.name) {
        unnamed.reachedExchange = api.name;
        unnamed.exchangeUnnamed = false;
        console.log(`[参考経路] 到達先の名前を取得: ${api.name}`);
      }
    } catch (e) { console.error('[参考経路] 名前の取得に失敗:', e.message); }
  }

  /* 旧「候補3件を3ホップだけ追う」処理は、上の参考経路と同じことを
     二重にやっていた（実測で77秒に達し上限超過）。統合し、
     報告書が使う nextCandidates は参考経路の結果から作る。 */
  if (refNode?.referenceTrace?.branches) {
    const bs = refNode.referenceTrace.branches;
    refNode.nextCandidates = bs.filter(b => b.reachedExchange).map(b => ({
      address: b.hops[0].address, label: b.hops[0].label || '',
      amount: b.hops[0].amount, time: b.hops[0].time,
      reachedExchange: b.reachedExchange, reachedAddress: b.reachedAddress, reachedHops: b.reachedHops,
      gapMin: b.hops[0].gapMin ?? 0,
    }));
    refNode.candidatesChecked = bs.length;
  }

  /* 時間予算で打ち切ると、名前がいちばん要る最後のノード（着金先）だけ
     取り残される。そこだけ後から埋める。待ち時間は入れない。 */
  const last = path[path.length - 1];
  if (truncatedAt >= 0 && last && last.address && !last.label) {
    try {
      const info = await getAddressInfo(last.address, chain);
      if (info) {
        last.balance = info.balance; last.txCount = info.txCount; last.balanceUSD = info.balanceUSD;
        if (info.bcLabel && !last.label) {
          last.label = info.bcLabel;
          if (isExchange(info.bcLabel)) last.isExchange = true;
        }
      }
      /* ★経路が短いと last が送金元そのものになる。
         被害者が出金した元に名前を引いても、凍結の宛先にはならない。
         ★無料は1件あたり1回しか引けないので、ここで使うと到達先に残らない。 */
      const lastIsSender = !last || last.role === 'sender' || last === path[0];
      if (!last.label && MISTTRACK_KEY && !lastIsSender) {
        const known = labelCache.has(last.address.toLowerCase());
        if (known || (apiLookups < lookupBudget && labelQuotaOk(opts.paid, opts.device))) {
          if (!known) { apiLookups++; labelQuotaUse(opts.device); }
          const api = await lookupLabelAPI(last.address, chain);
          if (api.name) {
            last.label = api.name;
            last.labelType = api.type || undefined;
            if (api.type === "exchange") last.isExchange = true;
            else if (api.type === "defi" || api.type === "mixer") { last.isVia = true; last.isExchange = false; }
            else if (!api.type && isExchange(api.name)) last.isExchange = true;
            if (api.type === "mixer") last.isMixer = true;
          }
        }
      }
      if (!last.label && !last.isExchange) {
        const inferred = inferExchangeByBehavior(last);
        if (inferred) { last.label = inferred; last.isExchange = true; last.inferred = true; }
      }
      console.log("[enrich] 打ち切り後、最後のノードだけ補完しました");
    } catch (e) { console.error("[enrich] 最後のノードの補完に失敗:", e.message); }
  }

  /* 着金先の名前が取れなかった／推定どまりのときだけ、取引先分析を引く。
     取引所の入金用アドレスはラベルが付かないが、送り先の大半が特定の取引所なら
     そこの入金用と判断できる。DEX・ブリッジ・トークン契約は通り道なので対象外。 */
  /* 犯人が指定してきたアドレス（最初の送金先）の素性を調べる。
     過去に詐欺として報告されていれば、報告書の説得力が変わる。
     すでに名前の付いた取引所なら、素性は分かっているので引かない。 */
  /* 動作確認では素性の照会も行わない（買った回数を使わない） */
  const pfBudget = isSelfTest(opts.device) ? 0
    : (opts.paid ? MISTTRACK_PROFILE_PAID : MISTTRACK_PROFILE_FREE);
  const target = (path || [])[1];
  const knownExchange = target && target.isExchange && target.label && !target.inferred && !target.cpInferred;
  if (pfBudget > 0 && MISTTRACK_KEY && misttrackSupports(chain)
      && target && target.address && !knownExchange && !target.isVia && !target.isToken) {
    const known = profileCache.has(target.address.toLowerCase());
    if (known || labelQuotaOk(opts.paid, opts.device)) {
      if (!known) labelQuotaUse(opts.device);
      const pf = await lookupProfileAPI(target.address, chain).catch(() => null);
      if (pf) {
        target.profile = pf;
        if (pf.malicious.length) {
          console.log(`[Profile] 不正事案として報告あり: ${pf.malicious.map(m => m.種別 + m.件数 + '件').join(' / ')}`);
        }
      }
    }
  }

  /* 同じアドレス（犯人が指定してきた送金先）のAMLリスクスコア。
     素性が「報告されているか」なのに対し、こちらは不正な資金との距離を数値で返す。
     有料レポートのみ。素性と同じ条件で引くので、対象なら1件につき1回で済む。 */
  const rkBudget = opts.paid ? MISTTRACK_RISK_PAID : MISTTRACK_RISK_FREE;
  if (rkBudget > 0 && MISTTRACK_KEY && misttrackSupports(chain)
      && target && target.address && !knownExchange && !target.isVia && !target.isToken) {
    const known = riskCache.has(target.address.toLowerCase());
    if (known || labelQuotaOk(opts.paid, opts.device)) {
      if (!known) labelQuotaUse(opts.device);
      const rk = await lookupRiskAPI(target.address, chain).catch(() => null);
      if (rk) target.risk = rk;
    }
  }

  /* 「現金化されたか」と「今も残っているか」。
     どちらも犯人が指定してきたアドレス（最初の送金先）について引く。
     被害者が最も知りたい2点で、報告書の価値に直結する。 */
  for (const [kind, budget, field] of [
    ['action',   opts.paid ? MISTTRACK_ACTION_PAID   : MISTTRACK_ACTION_FREE,   'action'],
    ['overview', opts.paid ? MISTTRACK_OVERVIEW_PAID : MISTTRACK_OVERVIEW_FREE, 'overview'],
  ]) {
    if (!(budget > 0) || !MISTTRACK_KEY || !misttrackSupports(chain)) continue;
    if (!target || !target.address || knownExchange || target.isVia || target.isToken) continue;
    const cache = kind === 'action' ? actionCache : overviewCache;
    const known = cache.has(target.address.toLowerCase());
    if (!known && !labelQuotaOk(opts.paid, opts.device)) continue;
    if (!known) labelQuotaUse(opts.device);
    const v = await lookupMistTrackSimple(kind, target.address, chain).catch(() => null);
    if (v) target[field] = v;
  }

  // しきい値を決め直すための材料を残す（外部APIは使わない）
  (path || []).forEach((n, i) => recordHopStat(n, chain, i, path.length));
  saveHopStats();

  const cpBudget = opts.paid ? MISTTRACK_CP_PAID : MISTTRACK_CP_FREE;
  const named = last && last.isExchange && last.label && !last.inferred;
  if (cpBudget > 0 && MISTTRACK_KEY && misttrackSupports(chain)
      && last && last.address && !named && !last.isVia && !last.isToken
      && last.role !== 'sender' && last !== path[0]) {   // ★出金元には使わない
    const known = cpCache.has(last.address.toLowerCase());
    if (known || labelQuotaOk(opts.paid, opts.device)) {
      if (!known) labelQuotaUse(opts.device);
      const cp = await lookupCounterpartyAPI(last.address, chain).catch(() => []);
      if (cp.length) {
        last.counterparty = cp;
        const hit = exchangeFromCounterparty(cp);
        if (hit) {
          last.label      = `${hit.name}（取引先から推定）`;
          last.isExchange = true;
          last.cpInferred = true;
          last.cpPercent  = hit.percent;
          console.log(`[Counterparty] 着金先を ${hit.name} と推定（取引の${hit.percent}%）`);
        } else {
          console.log('[Counterparty] 取引所と言える相手は見つかりませんでした');
        }
      }
    }
  }
}

// ══ チェーン自動判定 ══════════════════════════════════════════
/* ══ EVM系チェーン ══════════════════════════════════════════
   ★TXIDの形が同じなので、0x+64桁を Ethereum と決めつけていた。
     実例（利用者の正解経路④）は Polygon の取引で、被害者には
     「見つかりません」としか出なかった。精度以前に調査が成立しない。

   Etherscan は v2 で全チェーン同じ形のAPIになっており、chainid を
   変えるだけで同じ処理が使える。ただし★無料で使えるチェーンは限られる
   （2026-08-26 実測）。使えないチェーンを足すと、無いものを在ると
   言うことになるので入れない。

     Ethereum  1        ✅ 無料
     Polygon   137      ✅ 無料
     Arbitrum  42161    ✅ 無料
     BNB・Optimism・Base・Avalanche   ❌「Free API access is not supported」

   ★同時に複数の調査が走るので、現在のチェーンを大域変数で持ってはいけない。
     必ず引数で渡す。 */
const EVM_CHAINS = {
  eth:      { id: 1,     symbol: 'ETH', name: 'Ethereum', priceKey: 'eth' },
  polygon:  { id: 137,   symbol: 'POL', name: 'Polygon',  priceKey: 'polygon' },
  arbitrum: { id: 42161, symbol: 'ETH', name: 'Arbitrum', priceKey: 'eth' },
};
/* 0x+64桁のTXIDを、この順に探す。見つかった時点で確定する。 */
const EVM_TRY_ORDER = ['eth', 'polygon', 'arbitrum'];

function isEVM(chain)  { return !!EVM_CHAINS[chain]; }
function evmId(chain)  { return (EVM_CHAINS[chain] || EVM_CHAINS.eth).id; }
function evmSymbol(chain) { return (EVM_CHAINS[chain] || EVM_CHAINS.eth).symbol; }
/* Etherscan v2 の入口。chain を渡し忘れても Ethereum として動く（従来どおり）。 */
function esUrl(chain, query) {
  return `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&${query}&apikey=${ETHERSCAN_KEY}`;
}

function detectChain(input) {
  const s = input.trim();
  if (/^0x[0-9a-fA-F]{64}$/.test(s)) return 'eth';
  if (/^[0-9a-f]{64}$/.test(s))       return 'btc';
  if (/^[0-9A-F]{64}$/.test(s))       return 'xrp';
  if (/^[0-9a-fA-F]{64}$/.test(s))    return 'btc';
  return null;
}

// ══ TRON（TRC20・USDT） ══════════════════════════════════════

/* USDTのTRC20コントラクト。日本の詐欺被害で最も多い送金手段。 */
const TRON_USDT = 'TR7NHqjeKQxGTCi8q8ZY4pL8otSzgjLj6t';
const TRONGRID  = 'https://api.trongrid.io';
const TRONSCAN  = 'https://apilist.tronscanapi.com';
/* キー無しでも動く。入れると回数制限が緩む（TronGrid・TronScan共通の書式）。 */
const TRON_KEY  = process.env.TRON_API_KEY || '';
const tronHeaders = () => (TRON_KEY ? { 'TRON-PRO-API-KEY': TRON_KEY } : {});
const isTronAddr = a => /^T[1-9A-HJ-NP-Za-km-z]{33}$/.test(String(a || ''));

/* TronScanは取引の応答に取引所名を同梱してくる（addressTag）。
   追加の照会が要らないので、XRPにおけるXRPScanと同じ立ち位置で使える。
   MistTrackの回数を使わずに済むのが大きい。 */
const TRON_TAGS_FILE = path.join(DATA_DIR, 'tron-tags.json');
const tronTags = new Map();   // アドレス → 名前
try {
  const saved = JSON.parse(fs.readFileSync(TRON_TAGS_FILE, 'utf8'));
  for (const [addr, name] of Object.entries(saved)) tronTags.set(addr, name);
  console.log(`[TronTags] ${tronTags.size}件を読み込み`);
} catch { /* 初回は無い */ }
let tronTagsTimer = null;
/* 取引ごとに何度も呼ばれるので、まとめて書く。 */
function saveTronTags() {
  if (tronTagsTimer) return;
  tronTagsTimer = setTimeout(() => {
    tronTagsTimer = null;
    fsp.writeFile(TRON_TAGS_FILE, JSON.stringify(Object.fromEntries(tronTags), null, 2), 'utf8')
      .catch(e => console.error('[TronTags] 保存失敗:', e.message));
  }, 2000);
}
function rememberTronTags(tagObj) {
  if (!tagObj || typeof tagObj !== 'object') return;
  let added = 0;
  for (const [addr, name] of Object.entries(tagObj)) {
    if (typeof name !== 'string' || !name.trim()) continue;
    if (tronTags.get(addr) === name.trim()) continue;
    tronTags.set(addr, name.trim());
    added++;
  }
  if (added) { console.log(`[TronTags] ${added}件を追加（計${tronTags.size}件）`); saveTronTags(); }
}

/* TronScanの取引明細。TRC20送金と通常のTRX送金の両方をここで解く。 */
async function tronTxInfo(txid) {
  const r = await fetchT(`${TRONSCAN}/api/transaction-info?hash=${encodeURIComponent(txid)}`, { headers: tronHeaders() });
  const j = await r.json();
  if (!j || !j.timestamp) return null;   // 見つからないときは {} が返る
  rememberTronTags(j.addressTag);
  const tr = (j.trc20TransferInfo || [])[0];
  if (tr) {
    const dec = Number(tr.decimals != null ? tr.decimals : 6);
    return {
      time: j.timestamp, block: j.block,
      from: tr.from_address, to: tr.to_address,
      amount: Number(tr.amount_str || 0) / Math.pow(10, dec),
      token: tr.symbol || 'TRC20', contract: tr.contract_address,
      // 送金当時のドル建て評価額。あとから価格を引き直す必要がない
      usdAtTime: Number(tr.usdValue?.history?.amountInUsd) || null,
    };
  }
  const cd = j.contractData || {};
  if (j.contractType === 1 && cd.to_address) {
    return {
      time: j.timestamp, block: j.block,
      from: cd.owner_address, to: cd.to_address,
      amount: Number(cd.amount || 0) / 1e6, token: null, contract: null,
      usdAtTime: Number(cd.usdValue?.current?.amountInUsd) || null,
    };
  }
  return null;   // スワップ等。追跡の起点にはしない
}

// ══ 外部ラベル取得（Etherscan / Blockchair） ══════════════════

const labelFetchCache = new Map(); // addr → label（二重取得防止）

/* バイトコードに埋まった契約名を拾う。
   `revert("TransitAggregateBridgeV5: xxx")` のような書き方をしている契約から、
   コロンの前の識別子を取る。

   ★誤検出を避けるため、条件を厳しくする。
     ・英字で始まり、英数字だけ
     ・6文字以上、40文字以内
     ・大文字を含む（Solidityの契約名の慣習）
     ・よくあるエラーメッセージの語（Ownable, SafeMath 等）は除く
   拾えなければ黙って null。無いものを名乗らせない。 */
/* ★ライブラリ名を除外しないと、そちらばかり拾う。実データで確認した例：
     TransitSwapRouterV5   TransferHelper×6 / Ownable×2 / SafeCast×2 / ReentrancyGuard×1
     未公開のブリッジ       TransferHelper×3 / Ownable×2 / TransitAggregateBridgeV5×1
   本名は1回しか出てこないことがあるので、回数で選んではいけない。
   ライブラリを除いて残ったものを採り、残らなければ null（無いものを名乗らせない）。 */
const BYTECODE_NAME_SKIP = /^(ownable|safemath|safecast|safeerc20|safetransfer|transferhelper|address|strings|context|initializable|pausable|reentrancyguard|erc20|erc721|erc1155|erc1967|proxy|uups|beacon|eip712|ecdsa|merkle|counters|math|signedmath|clones|create2|multicall|accesscontrol|governor|votes|nonces|permit|pair|library|helper|util|utils)/i;
function nameFromBytecode(codeHex) {
  const hex = String(codeHex || '').replace(/^0x/, '');
  if (hex.length < 200) return null;                 // コントラクトでない
  let s = '';
  for (let i = 0; i + 1 < hex.length; i += 2) {
    const c = parseInt(hex.substr(i, 2), 16);
    s += (c >= 32 && c < 127) ? String.fromCharCode(c) : '\n';
  }
  // 「名前:」の形を優先して探す（Solidityのrevert文の慣習）
  const cands = [];
  /* 直前が識別子の一部なら、名前の途中を拾っている（"Has-Hyphen" から "Hyphen" 等）。
     そういう断片を名前として出すと、実在しないサービス名になる。 */
  for (const m of s.matchAll(/(?<![A-Za-z0-9_\-])([A-Za-z][A-Za-z0-9]{5,39}):/g)) cands.push(m[1]);
  for (const c of cands) {
    if (BYTECODE_NAME_SKIP.test(c)) continue;
    if (!/[A-Z]/.test(c)) continue;                  // 大文字を含まないものは除く
    if (!/[a-z]/.test(c)) continue;                  // 全部大文字も除く（定数名など）
    return c;
  }
  return null;
}

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
  if (isEVM(chain) && ETHERSCAN_KEY) {
    try {
      const url = `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=contract&action=getsourcecode&address=${addr}&apikey=${ETHERSCAN_KEY}`;
      const j = await apiJson(url);
      const name = j.result?.[0]?.ContractName || '';
      // 意味のあるコントラクト名のみ採用（"Vyper_contract"などは除外）
      if (name && name.length > 2 && !['Vyper_contract','0x','_'].some(s => name.startsWith(s))) {
        label = name;
        console.log(`[ExLabel] Etherscan契約名: ${addr.slice(0,10)}... → "${name}"`);
      }
    } catch {}
  }

  /* ②-b ソースが未公開でも、バイトコードに名前が埋まっていることがある。
     Solidity は文字列リテラルをそのまま持つため、`revert("Xxx: ...")` のような
     書き方をしている契約は名前が読める。

     実例：TransitSwap のブリッジ本体2つはソース未公開で②も③も名前を返さず、
     経路に「未特定」と出ていた。バイトコードには
     "TransitAggregateBridgeV5:" が埋まっていた。
     ブリッジやルーターは自分の名前をエラーメッセージに入れる作りが多く、
     この一段で拾える範囲が広がる。

     Etherscanの無料APIで、MistTrackの回数を使わずに済むのも大きい。 */
  if (!label && isEVM(chain) && ETHERSCAN_KEY) {
    try {
      const j = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=proxy`
        + `&action=eth_getCode&address=${addr}&tag=latest&apikey=${ETHERSCAN_KEY}`);
      const found = nameFromBytecode(j.result || '');
      if (found) {
        label = found;
        console.log(`[ExLabel] バイトコードから契約名: ${addr.slice(0, 10)}... → "${found}"`);
      }
    } catch {}
  }

  // ③ Blockchair アドレスラベル（BTC / ETH）
  if (!label && (chain === 'btc' || chain === 'eth') && BLOCKCHAIR_KEY) {
    try {
      const chain2 = chain === 'btc' ? 'bitcoin' : 'ethereum';
      const addrKey = chain === 'eth' ? addr.toLowerCase() : addr;
      const url = `https://api.blockchair.com/${chain2}/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const j = await apiJson(url);
      const d = j.data?.[addrKey]?.address;
      const bcLbl = d?.label || d?.contract_name || '';
      if (bcLbl) {
        label = bcLbl;
        console.log(`[ExLabel] Blockchairラベル: ${addr.slice(0,10)}... → "${bcLbl}"`);
      }
    } catch {}
  }

  // ④ TronScanのタグ（TRON のみ）。取引の応答に同梱されている分を先に使う
  if (!label && chain === 'tron') {
    if (tronTags.has(addr)) {
      label = tronTags.get(addr);
      console.log(`[ExLabel] TronScanタグ: ${addr.slice(0,10)}... → "${label}"`);
    }
  }

  // ⑤ XRPScan アカウント名（XRP のみ）
  if (!label && chain === 'xrp') {
    try {
      const r = await fetchT(`https://api.xrpscan.com/api/v1/account/${addr}`);
      const j = await r.json();
      const xrpName = xrpAccountName(j);
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

/* ★ビットコインは「お釣り」があるぶん、他のチェーンより間違えやすい。
   1つの送金で複数の宛先に出力が出る。うち1つは送金者自身へ戻る釣り銭で、
   多くの場合それが**最も大きい**。
   以前はその最大の出力を選んでいたので、★釣り銭＝犯人の同じ財布に
   戻る側を「次の送金先」として追っていた可能性がある。
   （ETHで直したのと同じ誤り。第4-S節。BTCには入っていなかった） */
async function getNextTxBTC(addr, afterTime, amountIn) {
  try {
    const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
    const j = await apiJson(url);
    const txHashes = j.data?.[addr]?.transactions || [];
    const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
    const cands = [];
    for (const txHash of txHashes.slice(0, 8)) {
      await new Promise(res => setTimeout(res, 250));
      try {
        const tr = await fetchT(`https://api.blockchair.com/bitcoin/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
        const tj = await tr.json();
        const tdata = tj.data?.[txHash];
        if (!tdata) continue;
        const inputs  = tdata.inputs  || [];
        const outputs = tdata.outputs || [];
        if (!inputs.some(i => i.recipient === addr)) continue;   // 出ていく送金だけ
        const txMs = new Date(normalizeTimeStr(tdata.transaction.time)).getTime();
        if (txMs < refMs - 3600000) continue;
        /* ★釣り銭の除き方は「追跡中のアドレス自身へ戻る出力」だけにする。
           一度は「入力に出てくるアドレス全部」に広げたが、実データで害が出た。
           正解経路6本・27区間で比較（第5-B節）：
             自分自身だけ除く … 本線21・候補に残る6・見失う0
             入力すべて除く   … 本線21・候補に残る5・★見失う1
           集約ウォレットは同じアドレスが入力にも出力にも現れる。
           実例：0x8504d47c… は入力26件で、正解の送金先 bc1qsyy7f38… が
           入力にも出力にも出ていた。広い方の規則だと正解ごと消えて、
           枝にも残らず、被害者は行き先を永久に失う。 */
        for (const o of outputs) {
          if (!o.recipient || o.recipient === addr) continue;
          const lbl = getLabel(o.recipient).label || '';
          cands.push({
            addr: o.recipient, amount: o.value / 1e8, time: tdata.transaction.time,
            txHash, label: lbl, txMs,
            isExchange: isExchange(lbl) && !isViaService(lbl) && !isTokenContract(lbl),
          });
        }
      } catch { continue; }
    }
    if (cands.length) {
      const chosen = pickNextHop(cands, amountIn);
      chosen._siblings = chosen._siblings || cands.filter(c => c !== chosen).slice(0, 4);
      console.log(`[HOP] BTC送金先: ${chosen.addr} ${chosen.amount} BTC 候補${cands.length}件`
        + `${chosen._matched ? ' ★入金額と一致' : ''}${chosen._pooled ? ' ★合流' : ''}`);
      return chosen;
    }
  } catch (e) { console.error('getNextTxBTC:', e.message); }
  return null;
}

/* ── 次の一手をどう選ぶか ────────────────────────────────────
   ★これまで「金額が最大の送金」を追っていたが、これが根本的に間違っていた。

   実例（利用者が提示した実際の経路）
     起点→A  0.071152 ETH
     A→B     0.071144 ETH  ← ほぼ同額。手数料の分だけ減っている＝同じ資金
     B→C     7.721607 ETH  ← ここで他の被害者分と集約された
     C→D     7.722068 ETH  ← また同額で動く
     D→E     9.906473 ETH  → Binance

   A地点で当社は 2.907681 ETH を選んでいた。正解は 0.071144 ETH で、
   むしろ小さい方だった。「最大」を追うのは、集約された後にだけ通用する話で、
   集約される前にやると、その時点で別人の資金に乗り換えてしまう。

   そこで順序を変える。
     ① 入ってきた額とほぼ同じ額の送金 ＝ 同じ資金が動いたと言える（最も確か）
     ② 取引所への送金
     ③ 金額が最大（集約後を想定した従来の推測）

   手数料で少し減るのが普通なので、2%の幅を見る。増える側にも同じ幅を許すのは、
   同じ取引の中で複数の入金がまとまることがあるため。 */
function pickNextHop(candidates, amountIn) {
  /* ★金額の一致は「入金の直後」に限る。
     実測（第4-X節）：合流地点Cで 0.712624 ETH の入金に対し、
     0.695155 ETH という近い額の送金が一致として選ばれていた。
     しかしそれは**8日後**の送金で、正解は**15分後**の 2.2 ETH だった。
     資金を逃がす側は数分〜数時間で動く。何日も経った額の近さは偶然であり、
     それを掴むと経路ごと別人の資金に乗り換えてしまう。

     窓の中に候補が1件も無いときだけ、全体を見る（休眠していた場合）。 */
  const inWindow = candidatesInWindow(candidates);

  if (Number.isFinite(amountIn) && amountIn > 0) {
    const ok = c => Number.isFinite(c.amount);
    /* ★同じ資金が動くなら、手数料の分だけ減ることはあっても増えることはない。
       増えている＝別の資金が混ざっている。まず「同額以下」から選ぶ。

       実例：B地点で 2.9076808 ETH が入り、候補が2つあった。
         2.9123（差0.0046・増えている）← 単純な近さで選ぶとこちら
         2.9000（差0.0077・減っている）← 正解。ここからブリッジへ渡っていた
       近さだけで選ぶと、より近い方＝別の資金を掴む。 */
    const feeOnly = inWindow
      .filter(c => ok(c) && c.amount <= amountIn * 1.000001 && c.amount >= amountIn * 0.95)
      .sort((a, b) => (amountIn - a.amount) - (amountIn - b.amount));
    if (feeOnly.length) { feeOnly[0]._matched = true; return attachExchangeSiblings(feeOnly[0], candidates); }
    /* 同額以下が無い場合のみ、わずかに増えている分も見る。
       同じ取引の中で複数の入金がまとまることがあるため。 */
    const tol = Math.max(amountIn * 0.02, 1e-9);
    const near = inWindow
      .filter(c => ok(c) && Math.abs(c.amount - amountIn) <= tol)
      .sort((a, b) => Math.abs(a.amount - amountIn) - Math.abs(b.amount - amountIn));
    if (near.length) { near[0]._matched = true; return attachExchangeSiblings(near[0], candidates); }
  }
  /* ★ここに来た＝入ってきた額に見合う送金が1件も無い。
     他人の資金と合流（プール）した地点で、1件の送金には対応しない。

     このとき「最大の1件」を選ぶのは誤り。実測（第4-X節）：
       合流地点E：入金 2.19975 ETH に対し送出94件・送金先63箇所。
         正解は 17.645478 ETH（Binance）で、時系列では5番目。
         最大の1件は 34.718806 ETH（別の宛先）＝外れ。
         最古の1件は  1.858016 ETH（別の宛先）＝外れ。
       ところが「送金先ごとに合計」すると Binance が 268.6 ETH・18回で
       全体の78.5%を占め、堂々の1位になる。

     資金をまとめて運ぶ側は、同じ宛先へ何度も送る。
     1件ずつ見ると紛れるが、宛先ごとに束ねると本命が浮かぶ。 */
  return attachExchangeSiblings(
    pickByDestinationVolume(candidates, Number.isFinite(amountIn) && amountIn > 0, amountIn), candidates);
}

/* ★同じ地点から取引所へも送られていたら、本線に選ばなくても必ず控える。

   実測（TRON経路②）：入金 2976.71 に対し 2834（95%）が別のアドレスへ、
   138.21（5%）が Binance へ出ていた。同額に近い方を本線に選ぶのは
   間違いではないが、★被害者が欲しいのは換金先の名前であって、
   どちらが本線かではない。選ばなかった方に取引所があるなら、
   それは報告書に出さなければならない。

   合流地点では、そもそもどちらが「その資金」かを断定できない。
   断定できないからこそ、取引所を落とさない。 */
function attachExchangeSiblings(chosen, candidates) {
  const seen = new Set([String(chosen.addr).toLowerCase()]);
  const ex = [];
  for (const c of candidates) {
    if (!c.isExchange) continue;
    const k = String(c.addr).toLowerCase();
    if (seen.has(k)) continue;
    seen.add(k);
    ex.push(c);
  }
  if (!ex.length) return chosen;
  const rest = (chosen._siblings || []).filter(x => !seen.has(String(x.addr).toLowerCase()));
  chosen._siblings = ex.concat(rest).slice(0, 6);   // 取引所を先頭に置く
  chosen._exchangeSiblings = ex.slice(0, 4);
  return chosen;
}

/* 合流地点で「どこへ流れたか」を、送金先ごとの合計で判断する。
   窓を切るのは、何ヶ月も先の無関係な送金まで足し込まないため。 */
const POOL_WINDOW_MS = 24 * 60 * 60 * 1000;

/* この倍率を超えて金額が増えたら「薄まった」と見る。
   ★薄まっても追跡はやめない。説明を添えて、その先の取引所まで記載する。
     10倍は控えめな線。集約は正当に金額を増やすので、
     少し増えた程度で「薄まった」と言うと、確かな経路まで疑わしく見せてしまう。 */
const DILUTION_MIN_X = 10;

/* 入金の直後だけを見る。候補は入金以降しか入っていないので、
   最も早い1件を起点にして、そこから24時間で切る。
   時刻が分からない候補は落とさない（判断材料が無いだけで、無関係とは限らない）。 */
function candidatesInWindow(candidates) {
  const times = candidates.map(c => c.txMs).filter(Number.isFinite);
  if (!times.length) return candidates;
  const t0 = Math.min(...times);
  /* ★取引所への送金は、窓の外でも落とさない。
     実測（TRON経路③）：入金の24時間より後に、74%の額が取引所へ出ていた。
     窓で切ったせいで候補から消え、55%の別アドレスを選んでいた。
     窓は「無関係な将来の送金に引きずられない」ためのもので、
     換金先そのものを捨てるためのものではない。 */
  const win = candidates.filter(c => !Number.isFinite(c.txMs)
    || c.txMs - t0 <= POOL_WINDOW_MS || c.isExchange);
  return win.length ? win : candidates;
}

function pickByDestinationVolume(candidates, pooled, amountIn) {
  const win = candidatesInWindow(candidates);
  /* ★額が0の送金は資金の移動ではない（契約の呼び出し等）。
     数に入れると「2箇所へ分散・最大100%」のような、意味の通らない
     表示になる。実測（第4-Y節）で発生した。 */
  const moved = win.filter(c => Number.isFinite(c.amount) && c.amount > 0);
  const use = moved.length ? moved : win;

  const by = new Map();
  for (const c of use) {
    const k = String(c.addr).toLowerCase();
    const g = by.get(k) || { total: 0, count: 0, first: c, isExchange: false };
    g.total += Number.isFinite(c.amount) ? c.amount : 0;
    g.count++;
    if (c.isExchange) g.isExchange = true;
    if ((c.txMs || 0) < (g.first.txMs || 0)) g.first = c;   // 代表は最初の1件
    by.set(k, g);
  }
  const ranked = [...by.values()].sort((a, b) => b.total - a.total);
  const sum = ranked.reduce((s, g) => s + g.total, 0);

  /* 取引所が宛先にあるなら、そこを優先する。被害者が知りたいのは換金先。 */
  const pick = ranked.find(g => g.isExchange) || ranked[0];
  const chosen = pick.first;

  if (pooled) {
    chosen._pooled = true;
    chosen._poolShare = sum > 0 ? pick.total / sum : null;
    chosen._poolDests = ranked.length;
    /* ★「金額が一致しない」を全部『合流』と呼んでいたのが誤りだった。
       実データ（BTC・13段）：0.85→0.70→0.56→0.41→0.27→0.14 と
       ★減り続けているのに、全地点に「他の資金と合流しています」と出ていた。
       減っているのは合流ではなく【分割】。資金が小分けにされ、
       一部だけが先へ進み、残りは別の送金先へ渡っている。

       ★向きが逆のものを同じ言葉で呼ぶと、読み手は事実を取り違える。
         合流なら「他人の資金が混ざった」、分割なら「残りが他所にある」。
         被害者にとって意味がまったく違う。 */
    const out = Number.isFinite(chosen.amount) ? chosen.amount : null;
    chosen._poolKind = (Number.isFinite(amountIn) && amountIn > 0 && out != null)
      ? (out > amountIn * 1.000001 ? 'merged' : (out < amountIn * 0.95 ? 'split' : 'merged'))
      : 'merged';
    chosen._keptShare = (chosen._poolKind === 'split' && Number.isFinite(amountIn) && amountIn > 0)
      ? out / amountIn : null;
    /* ★合流地点では1本に絞れない。実測C地点では正解が2位（44.2%）だった。
       上位の宛先を枝として残し、参考経路で全部追う。 */
    chosen._siblings = ranked.filter(g => g !== pick).slice(0, 4).map(g => ({
      addr: g.first.addr, label: g.first.label, amount: g.total,
      txHash: g.first.txHash, time: g.first.time, txMs: g.first.txMs,
      _poolShare: sum > 0 ? g.total / sum : null,
    }));
  }
  return chosen;
}

async function getNextTxETH(addr, afterTime, amountIn, chain = 'eth') {
  const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
  console.log(`[HOP] ETH追跡: ${addr} / 基準: ${isNaN(refMs) ? '不明' : new Date(refMs).toISOString()}`);

  /* ★取得は「入金時刻のブロックから」。1件あたり1000件しか取れないため、
     startblock=0 だと**最も古い1000件**（通常TXは昇順）または
     **最新の1000件**（内部・トークンは降順）しか見えない。
     どちらも入金直後の窓から外れる。

     実測：取引49,763回のアドレスで、入金直後の送金が候補に入らず、
     まったく別の枝へ流れていた。手作業で追った経路（Binanceに到達）とは
     4ホップ目で分岐していた。

     入金のブロックから取れば、何件あっても「入金の直後」を確実に拾える。
     以前 listNextCandidatesETH で同じ誤りを直している（第4-H節）。 */
  const startBlock = Number.isFinite(refMs) && refMs > 0
    ? await blockNoByTime(Math.floor(refMs / 1000), chain) : 0;

  // ① 通常TX（EOAからの送金）
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=txlist&address=${addr}&startblock=${startBlock}&endblock=latest&page=1&offset=1000&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const j = await apiJson(url);
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Etherscan TX: ${txs.length}件`);
    const candidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      if (!tx.to) continue;
      /* ★ETHが1円も動いていない取引は、ここでは候補にしない。
         USDTを送るときの取引は「宛先＝USDTの契約・金額0」という形で記録される。
         これを候補にすると、★USDTの契約そのものが行き先として経路に出る。
         実測：経路の途中に「Tether USD (USDT)」が中継地点として現れていた。
         資金はUDTの契約に入るのではなく、契約を通して誰かに渡っている。
         本当の受取先はトークンの記録側（この関数の後半）に出るので、そちらへ回す。
         内部でETHが動く呼び出しは、内部取引の側で拾える。 */
      if (parseFloat(tx.value || '0') === 0) continue;
      const db = getLabel(tx.to);
      const lbl = db.label || '';
      const isTok = db.type === 'token' || isTokenContract(lbl);
      const isVia = isViaService(lbl);
      const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));
      candidates.push({ addr: tx.to, amount: parseFloat(tx.value)/1e18, time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, txMs });
    }
    if (candidates.length > 0) {
      const chosen = pickNextHop(candidates, amountIn);
      chosen._siblings = chosen._siblings || candidates.filter(c => c.addr !== chosen.addr).slice(0, 4);
      console.log(`[HOP] ETH送金先: ${chosen.addr} label="${chosen.label}" amount=${chosen.amount} candidates=${candidates.length}`
        + (chosen._matched ? ' ★入金額と一致' : ''));
      return chosen;
    }
  } catch(e) { console.error('[HOP] Etherscan ETH:', e.message); }

  // ② 内部TX（スマートコントラクト・プロキシ経由の資金移動）
  // ※ sort=desc で最新TX から取得（古いコントラクトはascだと過去TXしか取れない問題を修正）
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=txlistinternal&address=${addr}&startblock=${startBlock}&endblock=latest&page=1&offset=1000&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const j = await apiJson(url);
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Internal TX: ${txs.length}件`);
    const intCandidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue; // 昇順に変えたため、入金より前は読み飛ばす
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      if (!tx.to) continue;
      if (tx.type === 'delegatecall' || tx.type === 'staticcall') continue; // 実ETH移動なし
      const amt = parseFloat(tx.value) / 1e18;
      if (amt < 0.001) continue;
      const db  = getLabel(tx.to); // ローカルDBのみ（高速）
      const lbl = db.label || '';
      const isTok = db.type === 'token' || isTokenContract(lbl);
      const isVia = isViaService(lbl);
      const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));
      intCandidates.push({ addr: tx.to, amount: amt, time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, txMs });
    }
    if (intCandidates.length > 0) {
      const chosen = pickNextHop(intCandidates, amountIn);
      chosen._siblings = chosen._siblings || intCandidates.filter(c => c.addr !== chosen.addr).slice(0, 4);
      console.log(`[HOP] 内部TX送金先: ${chosen.addr} label="${chosen.label}" amt=${chosen.amount} total=${intCandidates.length}`);
      return chosen;
    }
  } catch(e) { console.error('[HOP] Internal TX:', e.message); }

  try {
    const url = `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=tokentx&address=${addr}&startblock=${startBlock}&endblock=latest&page=1&offset=1000&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const j = await apiJson(url);
    const txs = Array.isArray(j.result) ? j.result : [];
    const tokenCandidates = [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue; // 昇順に変えたため、入金より前は読み飛ばす
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      /* 記号を騙るトークンは追わない。実データで「ETH」を名乗る別トークンを
         掴み、無関係の経路を追っていた（第4-R節）。 */
      if (isImpostorToken(tx.tokenSymbol, tx.contractAddress, chain)) {
        console.log(`[HOP] 「${tx.tokenSymbol}」を名乗る別トークンのため追わない（${String(tx.contractAddress).slice(0, 12)}…）`);
        continue;
      }
      const db  = getLabel(tx.to);
      const lbl = db.label || '';
      const isTok = db.type === 'token' || isTokenContract(lbl);
      const isVia = isViaService(lbl);
      const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));
      const dec  = parseInt(tx.tokenDecimal) || 18;
      tokenCandidates.push({ addr: tx.to, amount: parseFloat(tx.value)/Math.pow(10,dec), time: new Date(txMs).toISOString(), txHash: tx.hash, label: lbl, isExchange: isEx, token: tx.tokenSymbol, txMs });
    }
    if (tokenCandidates.length > 0) {
      const chosen = pickNextHop(tokenCandidates, amountIn);
      console.log(`[HOP] ERC-20送金先: ${chosen.addr} token=${chosen.token} exchange=${chosen.isExchange}`);
      return chosen;
    }
  } catch(e) { console.error('[HOP] ERC20:', e.message); }

  /* ★ここから先の最終手段は Blockchair で、Blockchair は Ethereum しか扱わない。
     同じ形のアドレスは他のEVMチェーンにも存在するので、Polygon の追跡中に
     ここへ来ると★Ethereum 側の無関係な送金を「次の送金先」として掴む。
     Ethereum のときだけ使う。 */
  if (chain !== 'eth') return null;

  try {
    /* ★ここも短く見切る。実測（診断画面）で最長6秒・失敗6件が続いていた。
       Etherscan（通常・内部・トークンの3種）で候補が1件も無かったときの
       最後の手段なので、★見つからないまま長く待つ価値がない。
       やり直しもしない（失敗が2倍の時間になる）。 */
    const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}&limit=10`;
    const j = await (await fetchT(url, {}, BLOCKCHAIR_TIMEOUT_MS)).json();
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

/* XRPの Amount は2種類ある。
   ・XRPそのもの → 文字列のドロップ数（100万分の1 XRP）
   ・発行された通貨 → { currency, issuer, value } というまとまり
   以前は常に parseFloat(…)/1e6 としていたため、後者では NaN になり、
   金額が読めないまま次を選んでいた。 */
function xrpAmount(a) {
  if (a == null) return null;
  if (typeof a === 'object') {
    const v = parseFloat(a.value);
    if (!Number.isFinite(v)) return null;
    /* ★XRP本体は、まとまりで返ってきても中身はドロップ数。
       実データ（xrpscan）：{"value":192256521,"currency":"XRP"} ＝ 192.256521 XRP。
       ここで割らないと1,000,000倍で読み、金額の一致がまったく効かなくなる。
       発行された別通貨（USD等）は、その通貨の単位そのままなので割らない。 */
    return String(a.currency).toUpperCase() === 'XRP' ? v / 1e6 : v;
  }
  const v = parseFloat(a);
  return Number.isFinite(v) ? v / 1e6 : null;   // 文字列はドロップ数
}

/* XRPの取引記録は XRPL の公開ノードから取る。
   ★以前は xrpscan の一覧を使っていたが、★最新25件しか返らない。
     実測（正解経路①②）：目的の送金がその25件に入っておらず、
     正解が候補にすら現れなかった（2区間とも見失った）。
     ETHの送金・トークンの送金・TRONに続いて、同じ誤りの4例目。

   公開ノードの account_tx は1回200件・marker で続きを取れる。
   新しい順に取り、着金時刻より古くなったら止める。 */
const XRPL_RPC = process.env.XRPL_RPC || 'https://xrplcluster.com/';
const XRPL_MAX_PAGES = 5;                      // 1000件まで。無限に遡らない
const RIPPLE_EPOCH = 946684800;                // 2000-01-01 との差（秒）

async function xrplAccountTx(addr, refMs) {
  const out = [];
  let marker = null;
  for (let page = 0; page < XRPL_MAX_PAGES; page++) {
    const params = { account: addr, ledger_index_min: -1, ledger_index_max: -1, limit: 200 };
    if (marker) params.marker = marker;
    const r = await fetchT(XRPL_RPC, {
      method: 'POST', headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ method: 'account_tx', params: [params] }),
    });
    if (!r.ok) break;
    const j = await r.json();
    const rows = j.result?.transactions || [];
    if (!rows.length) break;
    let oldest = Infinity;
    for (const row of rows) {
      const t = row.tx || row.tx_json || {};
      const sec = Number(t.date ?? row.close_time_iso ? null : t.date);
      const ms = Number.isFinite(t.date) ? (t.date + RIPPLE_EPOCH) * 1000
               : Date.parse(row.close_time_iso || t.date || '');
      if (!Number.isFinite(ms)) continue;
      oldest = Math.min(oldest, ms);
      out.push({ tx: t, meta: row.meta || row.metaData, ms, hash: t.hash || row.hash });
    }
    marker = j.result?.marker;
    if (!marker || oldest < refMs - 1000) break;   // 着金より前まで遡ったら終わり
  }
  return out;
}

async function getNextTxXRP(addr, afterTime, amountIn) {
  try {
    const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
    const rows = await xrplAccountTx(addr, Number.isFinite(refMs) ? refMs : 0);
    /* ★以前は「最初に見つけた1件」を返していた。ETHで直した誤りが残っていた。 */
    const cands = [];
    for (const row of rows) {
      const tx = row.tx || {};
      if (tx.TransactionType !== 'Payment') continue;
      if (tx.Account !== addr) continue;
      if (!tx.Destination) continue;
      if (!(row.ms >= refMs - 1000)) continue;
      /* 実際に届いた額。分割払いのときは Amount と一致しない。 */
      const delivered = row.meta && typeof row.meta === 'object'
        ? (row.meta.delivered_amount ?? row.meta.DeliveredAmount) : null;
      const amt = xrpAmount(delivered ?? tx.Amount);
      const lbl = getLabel(tx.Destination).label || '';
      cands.push({
        addr: tx.Destination, amount: amt, time: new Date(row.ms).toISOString(),
        txHash: row.hash, label: lbl, txMs: row.ms,
        token: (tx.Amount && typeof tx.Amount === 'object') ? tx.Amount.currency : undefined,
        isExchange: isExchange(lbl) && !isViaService(lbl) && !isTokenContract(lbl),
      });
    }
    if (cands.length) {
      const chosen = pickNextHop(cands, amountIn);
      chosen._siblings = chosen._siblings || cands.filter(c => c !== chosen).slice(0, 4);
      console.log(`[HOP] XRP送金先: ${chosen.addr} ${chosen.amount} 候補${cands.length}件`
        + `${chosen._matched ? ' ★入金額と一致' : ''}`);
      return chosen;
    }
  } catch (e) { console.error('getNextTxXRP:', e.message); }
  return null;
}

/* TRONで次に出ていった送金を探す。TRC20を先に見て、無ければTRXを見る。
   min_timestamp と昇順指定が効くので、着金の直後の送金だけを取れる。 */
async function getNextTxTRON(addr, afterTime, amountIn) {
  const refMs = new Date(afterTime).getTime();
  try {
    /* ★送り手として絞り込む（only_from）。
       絞らないと受取に埋もれる。実測：ブリッジの渡り先 THg8gE… は
       受取45件・送出5件の集約ウォレットで、50件取っても送出が
       ほとんど入らず、追跡がその場で途切れていた。
       絞ると同じ50件が全部「出ていった送金」になる。 */
    const url = `${TRONGRID}/v1/accounts/${addr}/transactions/trc20`
      + `?limit=50&order_by=block_timestamp,asc&only_from=true&min_timestamp=${Math.max(0, refMs - 1000)}`;
    const j = await tronJson(url);
    if (!j) return null;                 // ★取得できず。無いとは限らない
    /* ★以前は「最初に見つけた1件」を返していた。
       ETHで直したのと同じ誤り（第4-S節・第4-X節）が残っていた。
       ★TRONのUSDT-TRC20は日本の被害でいちばん多い経路なので、
         ここが一番効く場所だった。 */
    const cands = [];
    for (const t of (j.data || [])) {
      if (t.from !== addr) continue;              // 出ていった分だけ
      if (t.block_timestamp < refMs - 1000) continue;
      const dec = Number(t.token_info?.decimals != null ? t.token_info.decimals : 6);
      const lbl = getLabel(t.to).label || tronTags.get(t.to) || '';
      cands.push({
        addr: t.to, amount: Number(t.value || 0) / Math.pow(10, dec),
        time: new Date(t.block_timestamp).toISOString(), txHash: t.transaction_id,
        token: t.token_info?.symbol || 'TRC20', label: lbl,
        isExchange: isExchange(lbl) && !isViaService(lbl) && !isTokenContract(lbl),
        txMs: t.block_timestamp,
      });
    }
    if (cands.length) {
      const chosen = pickNextHop(cands, amountIn);
      /* 同じ地点から他にも出ていれば控えておく。犯人が資金を分けたとき、
         こちらが本命の可能性がある。お客様に調べ直す手がかりを渡すため。 */
      chosen._siblings = chosen._siblings
        || cands.filter(c => c !== chosen).slice(0, 4);
      console.log(`[HOP] TRC20送金先: ${chosen.addr} ${chosen.amount} ${chosen.token}`
        + ` 候補${cands.length}件${chosen._matched ? ' ★入金額と一致' : ''}${chosen._pooled ? ' ★合流' : ''}`);
      return chosen;
    }
  } catch (e) { console.error('getNextTxTRON(trc20):', e.message); }
  try {
    const url = `${TRONGRID}/v1/accounts/${addr}/transactions`
      + `?limit=50&order_by=block_timestamp,asc&min_timestamp=${Math.max(0, refMs - 1000)}`;
    const j = await tronJson(url);
    if (!j) return null;                 // ★取得できず。無いとは限らない
    const cands = [];
    for (const t of (j.data || [])) {
      const c = t.raw_data?.contract?.[0];
      if (!c || c.type !== 'TransferContract') continue;
      const v = c.parameter?.value || {};
      if (v.owner_address_base58 && v.owner_address_base58 !== addr) continue;
      const to = v.to_address_base58 || v.to_address;
      if (!isTronAddr(to)) continue;              // 16進表記のものは扱わない
      if (t.block_timestamp < refMs - 1000) continue;
      const lbl = getLabel(to).label || tronTags.get(to) || '';
      cands.push({
        addr: to, amount: Number(v.amount || 0) / 1e6,
        time: new Date(t.block_timestamp).toISOString(), txHash: t.txID, label: lbl,
        isExchange: isExchange(lbl) && !isViaService(lbl) && !isTokenContract(lbl),
        txMs: t.block_timestamp,
      });
    }
    if (cands.length) {
      const chosen = pickNextHop(cands, amountIn);
      chosen._siblings = chosen._siblings || cands.filter(c => c !== chosen).slice(0, 4);
      console.log(`[HOP] TRX送金先: ${chosen.addr} ${chosen.amount} 候補${cands.length}件`);
      return chosen;
    }
  } catch (e) { console.error('getNextTxTRON(trx):', e.message); }
  return null;
}

/* 交換・橋渡しのコントラクトに入った資金の出口を、同じ取引の中から読む。
   Blockchairの取引明細には内部送金（calls）が含まれるので、
   そのコントラクトから出ていった分を拾う。推測が入らない。 */
async function getSwapOutputETH(routerAddr, txHash, prevAddr) {
  if (!txHash) return null;
  try {
    const j = await apiJson(`https://api.blockchair.com/ethereum/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
    const data = j.data?.[String(txHash).toLowerCase()];
    if (!data) return null;
    const router = String(routerAddr).toLowerCase();
    const prev   = String(prevAddr || '').toLowerCase();
    const outs = (data.calls || [])
      .filter(c => c.sender && c.recipient
        && String(c.sender).toLowerCase() === router
        && String(c.recipient).toLowerCase() !== prev
        && String(c.recipient).toLowerCase() !== router
        && parseFloat(c.value || '0') > 0)
      .map(c => ({
        addr: c.recipient,
        amount: parseFloat(c.value) / 1e18,
        time: data.transaction?.time,
        txHash,
        label: c.recipient_label || '',
      }))
      .sort((a, b) => b.amount - a.amount);
    if (!outs.length) return null;
    console.log(`[SwapOut] ${routerAddr.slice(0, 10)}... の同一取引内の出金: ${outs.length}件 → ${outs[0].addr.slice(0, 10)}...`);
    const chosen = outs[0];
    chosen._siblings = outs.slice(1, 5).map(o => ({ addr: o.addr, label: o.label, amount: o.amount, txHash }));
    chosen._sameTx = true;
    return chosen;
  } catch (e) {
    console.error('[SwapOut] 取得失敗:', e.message);
    return null;
  }
}

/* 日時差がこれを超えたら報告書側で強調する。除外はしない。
   間があくほど同じ資金である確からしさは下がるが、無関係とは限らない。 */
const CANDIDATE_WARN_GAP_MIN = 60;

/* 時刻からブロック番号を引く。ここを起点に昇順で取るために使う。
   引けなければ 0（＝最初から）。その場合は従来どおりの精度に落ちるだけで壊れない。 */
async function blockNoByTime(sec, chain = 'eth') {
  try {
    const j = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=block`
      + `&action=getblocknobytime&timestamp=${sec}&closest=before&apikey=${ETHERSCAN_KEY}`);
    const n = parseInt(j.result);
    return Number.isFinite(n) && n > 0 ? n : 0;
  } catch { return 0; }
}

/* 打ち切り地点から次に出ていった送金を数件拾う。
   確定情報ではないため「参考」としてのみ使う。ラベルAPIは呼ばない（消費しない）。

   ★ 日時差での足切りはしない。被害に気づくのが1〜3ヶ月後という相談は多く、
     犯人が資金を10日・1ヶ月寝かせてから動かす例は実際にある。そこを外すと
     肝心の動きを見落とす。離れていることは報告書に見えるように出して、
     読み手に判断してもらう。

   ★ 取得は「入金時刻のブロックから昇順」。以前は降順で直近100件を取って
     時刻で絞っていたため、混雑したアドレスでは入金直後の送金が100件の中に
     入らず、ずっと後の送金が「最も近い3件」になっていた（実例 +526分）。
     昇順なら、間が何日あいても「次に出ていった送金」を確実に拾える。 */
async function listNextCandidatesETH(addr, afterTime, limit = 3, chain = 'eth') {
  try {
    const refSec = Math.floor(new Date(normalizeTimeStr(afterTime)).getTime() / 1000);
    if (!refSec) return [];
    const startBlock = await blockNoByTime(refSec, chain);
    /* 打ち切り地点はコントラクト（WETH等）であることが多い。
       コントラクトは通常の取引の送信者にならないので、内部送金を見る。
       個人の住所だった場合に備えて、空なら通常の取引も見る。 */
    const base = `https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&address=${addr}`
      + `&startblock=${startBlock}&endblock=latest&page=1&offset=100&sort=asc&apikey=${ETHERSCAN_KEY}`;
    /* ★以前は「内部送金が空のときだけ通常の取引も見る」としていた。
       実測（第4-X節）：個人ウォレット 0x0280baf5… は通常取引1000件超の
       集約ウォレットだが、内部取引が1件だけあった。そのため通常取引を
       まったく見に行かず、枝が0本になり参考経路が出なかった。
       Binance へ流れていたのに、利用者には何も示せていない。
       ★どちらか一方では足りない。両方を見て合わせる。 */
    const [ji, jn] = await Promise.all([
      apiJson(base + '&action=txlistinternal').catch(() => ({})),
      apiJson(base + '&action=txlist').catch(() => ({})),
    ]);
    const txs = [].concat(
      Array.isArray(ji.result) ? ji.result : [],
      Array.isArray(jn.result) ? jn.result : [],
    ).filter(t => t.isError !== '1').sort((a, b) => a.timeStamp - b.timeStamp);
    /* ★以前は「時系列で先頭3件」を返していた。混雑した地点では外れる。
       実測（第4-X節）：合流地点Eで入金後の送出は94件・送金先63箇所。
       時系列の1〜3番目は 1.858 / 0.231 / 0.014 ETH でいずれも無関係。
       正解のBinanceは5番目だが、送金先ごとに合計すると268.6 ETH で1位。

       同じ宛先への送金を束ね、合計額の大きい順に返す。 */
    const by = new Map();
    for (const t of txs) {
      const sec = parseInt(t.timeStamp);
      if (!(sec >= refSec)) continue;                                   // 入金より前は対象外
      if (sec - refSec > POOL_WINDOW_MS / 1000) continue;               // 窓の外は別件とみなす
      if (String(t.from).toLowerCase() !== String(addr).toLowerCase()) continue;  // 出ていく送金だけ
      if (!t.to) continue;
      const k = String(t.to).toLowerCase();
      const amt = parseFloat(t.value || '0') / 1e18;
      const g = by.get(k) || {
        address: t.to,
        label: getLabel(t.to).label || '',
        amount: 0,
        sends: 0,
        time: new Date(sec * 1000).toISOString(),
        txHash: t.hash,
        gapMin: Math.round((sec - refSec) / 60),
      };
      g.amount += amt;
      g.sends++;
      by.set(k, g);      // 代表の時刻・TXIDは最初の1件（昇順で来るため）
    }
    const out = [...by.values()].sort((a, b) => b.amount - a.amount).slice(0, limit);
    if (out.length) {
      console.log(`[Candidates] 次の送金 ${out.length}件（日時差 ${out.map(c => c.gapMin + '分').join('・')}）`);
    }
    return out;
  } catch (e) {
    console.error('[Candidates] 取得失敗:', e.message);
    return [];
  }
}

/* ── トークンの正体を、記号ではなくコントラクトで確かめる ──────────
   ★記号（tokenSymbol）は誰でも自由に付けられる。
     実際の調査で「ETH」を名乗る別トークン（0xa491c239…）を掴み、
     被害資金とは無関係の経路を追ってしまっていた。
     詐欺の現場では、追跡を撹乱するためにこの種のトークンが撒かれる。

   下記のアドレスは実データ（Etherscanの転送記録）で記号との一致を確認済み。
   ここに無い記号は判断しない（知らないトークンを偽物扱いしない）。 */
/* ★同じ記号でも、チェーンごとにコントラクトが違う。
   Ethereum の USDT のアドレスで Polygon の USDT を照合すると、
   本物を偽物と判定して追跡を止めてしまう。
   ★偽トークン対策が、そのまま「正規のチェーンを追えない」原因になる。
   知らないチェーンでは判断しない（偽物扱いしない）のが安全側。 */
const GENUINE_TOKENS_BY_CHAIN = {
  eth: {
    usdt: '0xdac17f958d2ee523a2206206994597c13d831ec7',
    usdc: '0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48',
    weth: '0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2',
    dai:  '0x6b175474e89094c44da98b954eedeac495271d0f',
    wbtc: '0x2260fac5e5542a773aa44fbcfedf7c193bc2c599',
  },
  polygon: {
    usdt: '0xc2132d05d31c914a87c6611c10748aeb04b58e8f',
    usdc: '0x3c499c542cef5e3811e1192ce70d8cc03d5c3359',   // ネイティブUSDC
    weth: '0x7ceb23fd6bc0add59e62ac25578270cff1b9f619',
    dai:  '0x8f3cf7ad23cd3cadbd9735aff958023239c6a063',
    wbtc: '0x1bfd67037b42cf73acf2047067bd4f2c47d9bfd6',
  },
  arbitrum: {
    usdt: '0xfd086bc7cd5c481dcc9c85ebe478a1c0b69fcbb9',
    usdc: '0xaf88d065e77c8cc2239327c5edb3a432268e5831',   // ネイティブUSDC
    weth: '0x82af49447d8a07e3bd95bd0d56f35241523fbab1',
    dai:  '0xda10009cbd5d07dd0cecc66161fc93d7c9000da1',
    wbtc: '0x2f2a2543b76a4166549f7aab2e75bef0aefc5b0f',
  },
};
const GENUINE_TOKENS = GENUINE_TOKENS_BY_CHAIN.eth;   // 既存呼び出し用
/* 「ETH」「BTC」はそもそもERC-20の記号として名乗る理由がない。
   本物のETHはトークンではないので、ERC-20で ETH を名乗っている時点で別物。 */
const RESERVED_SYMBOLS = new Set(['eth', 'btc', 'bitcoin', 'ethereum']);

/* 偽装が疑われるトークンか。true なら被害資金として追わない。 */
function isImpostorToken(symbol, contract, chain = 'eth') {
  const s = String(symbol || '').trim().toLowerCase();
  const c = String(contract || '').trim().toLowerCase();
  if (!s || !c) return false;
  if (RESERVED_SYMBOLS.has(s)) return true;              // ERC-20で ETH/BTC を名乗る＝別物
  /* ★そのチェーンの正解を知らないなら、判断しない。
     知らないまま「違う」と決めると、正規のトークンを追えなくなる。 */
  const table = GENUINE_TOKENS_BY_CHAIN[chain];
  if (!table) return false;
  const genuine = table[s];
  if (genuine && genuine !== c) return true;             // 有名な記号だがアドレスが違う
  return false;                                          // 知らない記号は判断しない
}

/* ── トークン（ERC-20）になった資金を追う ──────────────────────
   ETHをUSDTにスワップされると、これまでは追跡がそこで止まっていた。
   USDTの「コントラクト」を経路の一点として扱い、取引数が桁違いに多いため
   truncateAfterVia で打ち切られていた（実機で「USDTで止まる」と報告あり）。

   ★これは実態の取り違えだった。
     USDTのコントラクトに資金が入るわけではない。スワップで起きるのは
     「あるアドレスがUSDTを持つようになった」ことだけで、
     そのアドレスのERC-20送金を追えば、資金はそのまま辿れる。
     ミキサーと違って匿名化されていない。

   暗号資産詐欺の資金は最終的にUSDTへ化けることが多いので、ここが切れると
   肝心の到達先（＝凍結を頼む相手）が分からないまま終わる。 */

/* スワップの取引から「どのトークンが誰にいくら渡ったか」を読む。 */
async function getSwapTokenOutETH(txHash, holderAddr, chain = 'eth') {
  try {
    const want = t => t.hash?.toLowerCase() === String(txHash).toLowerCase()
                   && t.to?.toLowerCase() === String(holderAddr).toLowerCase();
    const j = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=tokentx`
      + `&address=${holderAddr}&page=1&offset=100&sort=desc&apikey=${ETHERSCAN_KEY}`);
    const list = Array.isArray(j.result) ? j.result : [];
    let hit = list.find(want);
    /* ★最新100件しか見ないので、古い取引だと入っていない。
       実測：2023年の取引で交換先を読めず、DEXのルーターを追って迷子になった。
       見つからないときだけ、その取引のブロックに絞って取り直す。 */
    if (!hit) {
      const t = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=proxy`
        + `&action=eth_getTransactionByHash&txhash=${txHash}&apikey=${ETHERSCAN_KEY}`);
      const blk = parseInt(t.result?.blockNumber, 16);
      if (Number.isFinite(blk)) {
        const j2 = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=tokentx`
          + `&address=${holderAddr}&startblock=${blk}&endblock=${blk}&page=1&offset=100&sort=asc&apikey=${ETHERSCAN_KEY}`);
        hit = (Array.isArray(j2.result) ? j2.result : []).find(want);
      }
    }
    if (!hit) return null;
    if (isImpostorToken(hit.tokenSymbol, hit.contractAddress, chain)) {
      console.log(`[TokenOut] 「${hit.tokenSymbol}」を名乗る別トークンのため追わない`);
      return null;
    }
    return {
      contract: hit.contractAddress,
      symbol:   hit.tokenSymbol || 'TOKEN',
      decimals: parseInt(hit.tokenDecimal) || 18,
      amount:   parseFloat(hit.value) / Math.pow(10, parseInt(hit.tokenDecimal) || 18),
    };
  } catch (e) { console.error('[TokenOut] 取得失敗:', e.message); return null; }
}

/* トークンを持っているアドレスから、次にそのトークンが出ていった先を探す。
   選び方はETHのときと同じ（取引所優先 → 次に金額最大）。 */
/* ★交換後の資金が「別のアドレス」へ渡される場合。
   手元に戻ってくるとは限らない。アグリゲーターは受取先を指定できるので、
   交換の出口が第三のアドレスになることがある。

   実測（利用者の正解経路④・Polygon）：
     経緯B が 3,629 USDC を Bitget Swap に渡し、
     交換後の 3,617 USDT は★経緯C（別アドレス）へ渡っていた。
     手元に戻る場合しか見ていなかったので、ルーターを追って
     AlgebraPool・UniswapV3Pool と配管に迷い込んでいた。

   出口の見分け方：その取引の中で【一度も送り手にならないアドレス】が
   受け取ったもの。配管（プール・ルーター）は必ず送り手にもなる。
   実データで確認：出口候補3件のうち最大が正解（3,617 USDT）だった。 */
async function getSwapExitETH(txHash, fromAddr, chain = 'eth') {
  try {
    const j = await apiJson(esUrl(chain, `module=proxy&action=eth_getTransactionReceipt&txhash=${txHash}`));
    const logs = (j.result?.logs || []).filter(l =>
      l.topics?.[0] === ERC20_TRANSFER_TOPIC && l.topics.length >= 3);
    if (logs.length < 2) return null;                 // 単純な送金は対象外
    const addrOf = t => ('0x' + String(t).slice(26)).toLowerCase();
    const senders = new Set(logs.map(l => addrOf(l.topics[1])));
    const me = String(fromAddr).toLowerCase();
    /* 入り口で渡したトークン。出口はそれとは別の通貨のはず。 */
    const inLog = logs.find(l => addrOf(l.topics[1]) === me);
    const inToken = inLog ? String(inLog.address).toLowerCase() : null;

    let best = null;
    for (const l of logs) {
      const to = addrOf(l.topics[2]);
      if (senders.has(to) || to === me) continue;     // 配管は送り手にもなる
      const token = String(l.address).toLowerCase();
      if (inToken && token === inToken) continue;     // 渡した通貨のままなら交換ではない
      let v; try { v = BigInt(l.data); } catch { continue; }
      if (v <= 0n) continue;
      if (!best || v > best.value) best = { to, token, value: v, txHash };
    }
    if (!best) return null;

    /* 通貨の名前と桁を、その取引の記録から取る。 */
    const blk = parseInt(j.result.blockNumber, 16);
    const tk = (await apiJson(esUrl(chain,
      `module=account&action=tokentx&address=${best.to}&startblock=${blk}&endblock=${blk}&page=1&offset=100&sort=asc`))).result;
    const hit = (Array.isArray(tk) ? tk : []).find(t =>
      String(t.hash).toLowerCase() === String(txHash).toLowerCase()
      && String(t.contractAddress).toLowerCase() === best.token);
    if (!hit) return null;
    if (isImpostorToken(hit.tokenSymbol, hit.contractAddress, chain)) return null;
    const dec = parseInt(hit.tokenDecimal) || 18;
    return { address: best.to, contract: hit.contractAddress,
             symbol: hit.tokenSymbol || 'TOKEN', decimals: dec,
             amount: Number(best.value) / Math.pow(10, dec) };
  } catch (e) { console.error('[SwapExit] 取得失敗:', e.message); return null; }
}

async function getNextTokenTxETH(addr, afterTime, contract, decimals = 18, amountIn = null, chain = 'eth') {
  try {
    const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
    /* ★開始ブロックを指定していなかったため、1件あたり200件の制限で
       「最も古い200件」しか見えていなかった。第4-H節でETHの送金について
       直したのと同じ誤りが、トークンの側に残っていた。
       実測：2023年12月の送金を探すのに、6月からの200件を見ていて届かず、
       交換は読めているのに、その先へ進めずに終わっていた。 */
    const startBlock = Number.isFinite(refMs) && refMs > 0
      ? await blockNoByTime(Math.floor(refMs / 1000), chain) : 0;
    const j = await apiJson(`https://api.etherscan.io/v2/api?chainid=${evmId(chain)}&module=account&action=tokentx`
      + `&contractaddress=${contract}&address=${addr}&startblock=${startBlock}&endblock=latest`
      + `&page=1&offset=200&sort=asc&apikey=${ETHERSCAN_KEY}`);
    const list = Array.isArray(j.result) ? j.result : [];
    const candidates = [];
    for (const t of list) {
      const txMs = parseInt(t.timeStamp) * 1000;
      if (txMs < refMs) continue;                                    // 入金より前は対象外
      if (String(t.from).toLowerCase() !== String(addr).toLowerCase()) continue;  // 出ていく分だけ
      if (!t.to) continue;
      const db  = getLabel(t.to);
      const lbl = db.label || '';
      const isTok = db.type === 'token' || isTokenContract(lbl);
      const isVia = isViaService(lbl);
      candidates.push({
        addr: t.to, amount: parseFloat(t.value) / Math.pow(10, decimals),
        time: new Date(txMs).toISOString(), txHash: t.hash, label: lbl,
        isExchange: !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl)),
        token: t.tokenSymbol || '', txMs,
      });
    }
    if (!candidates.length) return null;
    /* ★ここも「取引所優先→最大」のままだった。ETHの側で直した
       「入ってきた額と同じ送金を追う」（第4-S節・第4-X節）を通す。 */
    const chosen = pickNextHop(candidates, amountIn);
    chosen._siblings = chosen._siblings || candidates.filter(c => c.addr !== chosen.addr).slice(0, 4);
    console.log(`[HOP] トークン送金先: ${chosen.addr} ${chosen.amount} ${chosen.token} candidates=${candidates.length}`
      + `${chosen._matched ? ' ★入金額と一致' : ''}${chosen._pooled ? ' ★合流' : ''}`);
    return chosen;
  } catch (e) { console.error('[HOP] tokentx:', e.message); return null; }
}

async function traceHops(startAddr, startTime, chain, maxHops = 10, deadline = Date.now() + TRACE_BUDGET_MS, startToken = null, startAmount = null) {
  const hops = [];
  let currentAddr = startAddr;
  let currentTime = startTime;
  const visited = new Set([startAddr.toLowerCase()]);
  let exCount = 0;                       // ラベルで判明した取引所の数
  let incomingHash = null;               // いま居る住所へ資金を運んできた取引
  let prevAddr = null;                   // その1つ前の住所
  let currentIsVia = false;              // いま居るのが交換・橋渡しのコントラクトか
  let lastCandidates = 0;                // 直前の地点に送金先がいくつあったか（混雑の目安）
  /* いま居る地点に入ってきた額。次の一手を選ぶとき、同額の送金があれば
     それが同じ資金である証拠になる（第4-S節）。 */
  let currentAmount = Number.isFinite(startAmount) ? startAmount : null;
  let token = startToken;                // 資金がトークンなら {contract,symbol,decimals}
  if (token) console.log(`[traceHops] ${token.symbol} として追跡を開始する`);
  for (let i = 0; i < maxHops; i++) {
    if (Date.now() > deadline) { console.log(`[traceHops] 時間予算に達したため打ち切り（${i}ホップで部分結果を返す）`); break; }
    let next = null;
    /* 資金がトークンになっている間は、そのトークンの送金だけを追う。
       ETHの送金を見ても、もうそこに資金は流れていない。 */
    if (isEVM(chain) && token) {
      next = await getNextTokenTxETH(currentAddr, currentTime, token.contract, token.decimals, currentAmount, chain);
      if (!next) { console.log(`[traceHops] ${token.symbol} はこのアドレスから動いていない`); break; }
    }
    /* 同じ取引の中の出金を先に読む。
       時刻と金額で選ぶより確実で、他人の資金を拾わない。

       ★以前は「経由・トークンとラベルが付いた地点」でしか試していなかった。
         しかし AllowanceHolder（1,104万回）や MainnetSettler（37万回）のような
         共有の決済コントラクトはラベルが付かないため素通りし、
         そこから「金額が最大の送金」を選んでいた。
         結果、同じ取引を2回調べると行き先が変わり、
         2回目は被害額より大きい額（＝他人の資金）を掴んでいた。

         同じ取引の中で追える限りは、混雑した地点でも先へ進んでよい。
         「大きく動いた先を追う」こと自体は正しい方法で、
         問題は【どこで】それを使うか。共有コントラクトの中では使えない。 */
    /* 毎回やると1ホップにつき1回の問い合わせが増え、調査が時間切れになる（実測）。
       混雑した地点だけに絞る。直前の候補が多いほど、そこは混雑している。 */
    const crowdedHere = currentIsVia || lastCandidates >= 3;
    if (!next && chain === 'eth' && incomingHash && crowdedHere) {
      next = await getSwapOutputETH(currentAddr, incomingHash, prevAddr);
      if (next) console.log(`[traceHops] 同じ取引の中で次の送金先を特定（推測ではない）`);
    }
    if (!next) {
      /* ★入ってきた額は全チェーンに渡す。以前はETHにしか渡しておらず、
         BTC・XRP・TRONでは「最大の1件」「最初の1件」を選んだままだった。 */
      if (chain === 'btc') next = await getNextTxBTC(currentAddr, currentTime, currentAmount);
      else if (isEVM(chain)) next = await getNextTxETH(currentAddr, currentTime, currentAmount, chain);
      else if (chain === 'xrp') next = await getNextTxXRP(currentAddr, currentTime, currentAmount);
      else if (chain === 'tron') next = await getNextTxTRON(currentAddr, currentTime, currentAmount);
    }
    if (!next) break;
    if (visited.has(next.addr.toLowerCase())) break; // ループ防止
    visited.add(next.addr.toLowerCase());
    const db  = getLabel(next.addr);
    const fetchedLabel = await fetchAddressLabel(next.addr, chain);
    const lbl = fetchedLabel || db.label || next.label || '';
    let isTok = db.type === 'token' || isTokenContract(lbl);
    const isVia = isViaService(lbl);
    const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));

    /* ★次がトークンのコントラクトなら、そこへ「入った」のではない。
       いま居るアドレスがそのトークンを持つようになっただけなので、
       コントラクトを経路に足さず、トークンの追跡に切り替えて同じ地点から続ける。
       これをしないと USDT で追跡が止まる。 */
    /* ★DEXのルーターに送った場合も同じこと。ルーターは通り道であって、
       交換された資金は【いま居るアドレスに戻ってくる】。
       ルーターを追うと、そこから先はDEXの内部配管（プール・WETH・別の
       ルーター…）に迷い込み、被害者の資金とは無関係の経路になる。

       実測（利用者提供の正解経路）：
         経緯C 0x98e6be27… は 11:20 に 64.5 ETH を Uniswap へ送り、
         11:22 に交換後の USDT を CoinCorner へ送っていた。
         当社は Uniswap を追って WETH・1inch・Spender と迷走していた。
         ★正解は「Cの手元で ETH が USDT に化けた」と読むこと。 */
    /* ★「まだトークンを追っていないとき」に限っていたのが誤りだった。
       被害の大半はUSDT・USDCで始まるので、その状態から別の通貨へ
       交換される場合こそ見なければならない。
       実測（正解経路④・Polygon）：USDCを追っている最中に USDC→USDT の
       交換があり、条件に阻まれて検出できず、DEXの配管を延々と辿っていた。
       すでに持っている通貨と違うものが出てきたときだけ「交換」とみなす。 */
    const sameToken = t => token && t
      && String(t.contract).toLowerCase() === String(token.contract).toLowerCase();
    /* ★交換の確認は1ホップあたり最大4回の問い合わせになる。
       持ち時間が残り少ないときにこれを始めると、1周だけで予算を超え、
       ★調査そのものが時間切れで失敗する（実測：単純なETH送金で75秒到達）。
       時間切れは間違った答えより悪い。利用者には何も出せない。
       余裕があるときだけ確認する。 */
    const roomForSwap = Date.now() < deadline - 8000;
    if (isEVM(chain) && (isTok || isVia) && roomForSwap) {
      const t0 = await getSwapTokenOutETH(next.txHash, currentAddr, chain);
      const t = sameToken(t0) ? null : t0;
      if (t) {
        token = t;
        const holder = hops.length ? hops[hops.length - 1] : null;
        if (holder) { holder.swapTo = t.symbol; holder.token = t.symbol; }
        /* ★追う額も、交換後の数字に入れ替える。ETHの数字のまま
           トークンを照合しても一致するはずがない（第5-Cで同じ誤りをした）。 */
        currentAmount = Number.isFinite(t.amount) ? t.amount : null;
        console.log(`[traceHops] ${t.symbol} に交換された（${t.amount}）。ここからは ${t.symbol} を追う`);
        visited.delete(next.addr.toLowerCase());   // コントラクトは通過点なので訪問済みにしない
        currentIsVia = false;
        continue;                                   // 住所は変えず、次の周回でトークンを追う
      }
      /* ★手元に戻ってこない場合。交換後の資金が別のアドレスへ渡っている。
         ルーターは経路に残す（ブリッジの読み取りがそこを見るため）が、
         追跡は出口のアドレスから続ける。 */
      /* 出口探しはトークンのコントラクト相手には不要。
         トークン契約に送った場合、交換後は自分の手元に戻る（上で確認済み）。
         別アドレスへ渡るのはルーター（経由）を通したときだけ。 */
      const exit0 = isVia ? await getSwapExitETH(next.txHash, currentAddr, chain) : null;
      const exit = sameToken(exit0) ? null : exit0;      // 同じ通貨なら交換ではない
      if (exit && exit.address.toLowerCase() !== currentAddr.toLowerCase()
          && !visited.has(exit.address.toLowerCase())) {
        const holder = hops.length ? hops[hops.length - 1] : null;
        if (holder) { holder.swapTo = exit.symbol; }
        hops.push({ address: next.addr, label: lbl, amount: next.amount,
          token: next.token, isExchange: false, isToken: isTok, isVia: true,
          time: next.time, txHash: next.txHash, siblings: [], swapTo: exit.symbol });
        console.log(`[traceHops] ${exit.symbol} に交換され、${exit.address.slice(0, 12)}… へ渡った（${exit.amount}）`);
        /* ★出口のアドレスも経路に載せる。載せないと、実在する受取先が
           報告書から抜け落ちる。★そこが取引所なら、抜けた瞬間に
           凍結要請の宛先を失う。名前も引いて確かめる。 */
        const exDb  = getLabel(exit.address);
        const exLbl = (await fetchAddressLabel(exit.address, chain)) || exDb.label || '';
        const exTok = exDb.type === 'token' || isTokenContract(exLbl);
        const exVia = isViaService(exLbl);
        const exIsEx = !exTok && !exVia && (exDb.type === 'exchange' || isExchange(exLbl));
        hops.push({ address: exit.address, label: exLbl, amount: exit.amount, token: exit.symbol,
          isExchange: exIsEx, isToken: exTok, isVia: exVia, sameTx: true,
          time: next.time, txHash: next.txHash, siblings: [] });
        if (exIsEx) {
          exCount++;
          console.log(`[traceHops] 取引所到達(${exCount}件目): ${exLbl}`);
        }
        token         = { contract: exit.contract, symbol: exit.symbol, decimals: exit.decimals };
        currentAmount = Number.isFinite(exit.amount) ? exit.amount : null;
        prevAddr      = currentAddr;
        currentAddr   = exit.address;
        currentTime   = next.time;
        incomingHash  = next.txHash;
        currentIsVia  = false;
        visited.add(exit.address.toLowerCase());
        continue;
      }
      // 何のトークンか読めなければ、従来どおりの扱いに落とす
    }

    // 同時送金先（siblings）を保存
    const siblings = (next._siblings || []).map(s => ({
      address: s.addr, label: s.label || '', amount: s.amount, token: s.token,
      txHash: s.txHash || '',   // これを渡せば、その枝をそのまま調べられる
      time: s.time || next.time,   // 枝をそのまま追い続けるのに要る
      poolShare: s._poolShare ?? null,
    }));
    console.log(`[traceHops] ホップ${i+1}: ${next.addr.slice(0,10)}... label="${lbl}" exchange=${isEx} siblings=${siblings.length}`);
    hops.push({ address: next.addr, label: lbl, amount: next.amount,
      token: next.token || (token ? token.symbol : undefined),
      isExchange: isEx, isToken: isTok, isVia, sameTx: !!next._sameTx,
      time: next.time, txHash: next.txHash, siblings,
      /* 合流地点は「同じ資金を追えた」とは言えない。読み手が確度を判断できるよう、
         合流したことと、その先の分かれ方をそのまま伝える。 */
      pooled: !!next._pooled, poolShare: next._poolShare ?? null, poolDests: next._poolDests ?? null,
      poolKind: next._poolKind || null, keptShare: next._keptShare ?? null,
      /* ★どれだけ薄まったか。入ってきた額に対し、出ていく額が何倍か。
         実測：被害資金 25.83 USDT が入った地点から 64,832 USDT が出ていた（約2,500倍）。
         被害資金はその流れの約1%で、1本を選ぶ根拠は無い。
         ★それでも先は追い、到達した取引所は必ず記載する（方針・第5-H節）。
           薄まったことを理由に伏せると、被害者は手がかりを失うだけ。
           数字で薄まり具合を示し、判断は読み手に委ねる。
         通貨が変わった区間は倍率に意味が無いので出さない。 */
      dilutionX: (Number.isFinite(currentAmount) && currentAmount > 0
                  && Number.isFinite(next.amount) && next.amount > currentAmount * DILUTION_MIN_X
                  && (next.token || null) === (token ? token.symbol : null))
                 ? Math.round(next.amount / currentAmount) : null,
      /* ★同じ地点から取引所へも出ていた場合。本線に選ばなくても報告書に出す。 */
      exchangeNearby: (next._exchangeSiblings || []).map(x => ({
        address: x.addr, label: x.label || '', amount: x.amount, token: x.token, txHash: x.txHash })) });
    if (isEx) {
      exCount++;
      console.log(`[traceHops] 取引所到達(${exCount}件目): ${lbl}`);
      if (exCount >= 2) break;          // 2個目の取引所で停止
    }
    prevAddr     = currentAddr;
    currentAddr  = next.addr;
    currentTime  = next.time;
    incomingHash = next.txHash;
    currentIsVia = isVia || isTok;
    lastCandidates = (next._siblings || []).length + 1;
    currentAmount  = Number.isFinite(next.amount) ? next.amount : null;
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
  /* ★送金元を経路の先頭に置く。
     これが無いと、報告書は経路の1件目を「送金元」として表示するので、
     ★受取先が送金元として出て、以降が丸ごと1段ずれる（利用者の指摘・第5-K節）。
     実測：送金元 bc1qnsupj8… が経路から消え、受取先 bc1q3grc4… が
     「送金元」と表示されていた。
     他のチェーン（ETH・TRON・XRP）は先頭に送金元を置いており、
     ★BTCだけが違う形だった。 */
  const senderDb = getLabel(senderAddr);
  const path = [{ address: senderAddr, label: senderDb.label || '', role: 'sender',
                  time: tx.time }];
  const exchanges = [];
  for (const out of outputs) {
    if (changeAddrs.has(out.recipient)) continue;
    const db = getLabel(out.recipient);
    const fetchedLabel = await fetchAddressLabel(out.recipient, 'btc');
    const lbl = fetchedLabel || db.label || out.recipient_label || '';
    const isTok = db.type === 'token' || isTokenContract(lbl);
    const isVia = isViaService(lbl);
    const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));
    path.push({ address: out.recipient, label: lbl, amount: out.value/1e8, isExchange: isEx,
                time: tx.time });
    if (isEx) exchanges.push({ name: lbl, address: out.recipient, amount: out.value/1e8 });
  }
  // 全ての送金先アドレスからホップ追跡（取引所が見つかっていない送金先のみ）
  // ※ 安全のため最大10件（一括送金TXでの過負荷防止）
  /* 先頭は送金元。そこから追ってはいけない（自分の出金元を追うことになる） */
  const nonExPaths = path.filter(p => !p.isExchange && p.role !== 'sender');
  const btcDeadline = Date.now() + TRACE_BUDGET_MS;   // 全送金先の追跡を合計でこの時間内に収める
  for (const startNode of nonExPaths.slice(0, 10)) {
    if (Date.now() > btcDeadline) break;
    /* ★この送金先が受け取った額を渡す。渡さないと最初の一手で
       釣り銭側（送金者自身に戻る出力）を掴みうる。 */
    const hops = await traceHops(startNode.address, tx.time, 'btc', 10, btcDeadline,
      null, Number.isFinite(startNode.amount) ? startNode.amount : null);
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

/* ══ Ethereum 以外のEVMチェーン（Polygon・Arbitrum）══════════
   ★Ethereum の調査は Blockchair の取引明細に依存していて、
     Blockchair は Ethereum しか扱わない。
     そこで他チェーンは Etherscan だけで組む。実績のあるETHの処理には
     触れない（せっかく正解経路で検証した部分を壊さないため）。

   必要なものは3つだけ：
     ① 取引そのもの（送金元・宛先・額・日時）
     ② トークン送金なら、その受取先と通貨
     ③ そこから先は traceHops（既にチェーン対応済み）に渡す */
const ERC20_TRANSFER_TOPIC = '0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef';

/* TXIDがどのEVMチェーンのものかを、1回ずつの軽い問い合わせで確かめる。
   ★「見つからない」と「通信に失敗した」を混同しない。
     失敗したチェーンは判断を保留し、他を試す。
     すべて空振りしたときだけ「どこにも無い」と言う。 */
async function detectEVMChain(hash) {
  const h = hash.startsWith('0x') ? hash : '0x' + hash;
  let anyError = false;
  for (const c of EVM_TRY_ORDER) {
    try {
      const j = await apiJson(esUrl(c, `module=proxy&action=eth_getTransactionByHash&txhash=${h}`));
      if (j.result && j.result.from) {
        console.log(`[investigate] ${EVM_CHAINS[c].name} の取引と判明`);
        return c;
      }
      /* result が null＝そのチェーンには無い。NOTOK＝そのチェーンは使えない。
         どちらも「次を試す」でよい。 */
      if (j.result == null && j.status !== '0') continue;
      if (j.status === '0') { anyError = true; continue; }
    } catch (e) {
      anyError = true;                       // 一時的な失敗。無いとは言い切れない
      console.error(`[investigate] ${EVM_CHAINS[c].name} の確認に失敗:`, e.message);
    }
  }
  if (anyError) console.log('[investigate] 一部のチェーンを確認できませんでした');
  return null;
}

async function investigateEVM(hash, chain) {
  const h = hash.startsWith('0x') ? hash : '0x' + hash;
  const meta = EVM_CHAINS[chain];
  const tx = (await apiJson(esUrl(chain, `module=proxy&action=eth_getTransactionByHash&txhash=${h}`))).result;
  if (!tx || !tx.from) throw new Error(`${meta.name} TXが見つかりません`);

  const blk = parseInt(tx.blockNumber, 16);
  const b = (await apiJson(esUrl(chain, `module=proxy&action=eth_getBlockByNumber&tag=0x${blk.toString(16)}&boolean=false`))).result;
  const timeIso = new Date(parseInt(b?.timestamp || '0', 16) * 1000).toISOString();
  const nativeAmt = parseInt(tx.value, 16) / 1e18;

  /* トークンの送金なら、実際の受取先は記録（ログ）の中にある。
     tx.to はトークンのコントラクトで、そこに資金が入るわけではない。 */
  let recipient = tx.to, amount = nativeAmt, tokenSymbol = null, tokenAmount = null, tokenCtx = null;
  const tk = (await apiJson(esUrl(chain,
    `module=account&action=tokentx&address=${tx.from}&startblock=${blk}&endblock=${blk}&page=1&offset=100&sort=asc`))).result;
  const mine = (Array.isArray(tk) ? tk : []).filter(t =>
    String(t.hash).toLowerCase() === h.toLowerCase() && String(t.from).toLowerCase() === String(tx.from).toLowerCase());
  const hit = mine.find(t => !isImpostorToken(t.tokenSymbol, t.contractAddress, chain)) || null;
  if (hit) {
    const dec = parseInt(hit.tokenDecimal) || 18;
    recipient   = hit.to;
    tokenSymbol = hit.tokenSymbol || 'TOKEN';
    tokenAmount = parseFloat(hit.value) / Math.pow(10, dec);
    amount      = tokenAmount;
    tokenCtx    = { contract: hit.contractAddress, symbol: tokenSymbol, decimals: dec };
  }

  const senderDb = getLabel(tx.from);
  const recipDb  = getLabel(recipient);
  const recipLbl = (await fetchAddressLabel(recipient, chain)) || recipDb.label || '';
  const isRecipToken = recipDb.type === 'token' || isTokenContract(recipLbl);
  const isRecipEx = !isRecipToken && !isViaService(recipLbl)
    && (recipDb.type === 'exchange' || isExchange(recipLbl));

  const path = [
    { address: tx.from,  label: senderDb.label || '', role: 'sender', time: timeIso },
    { address: recipient, label: recipLbl, role: 'recipient', time: timeIso,
      isExchange: isRecipEx, isToken: isRecipToken, amount, token: tokenSymbol || undefined },
  ];
  const exchanges = isRecipEx ? [{ name: recipLbl, address: recipient, amount }] : [];
  if (!isRecipEx) {
    const hops = await traceHops(recipient, timeIso, chain, 10,
      Date.now() + TRACE_BUDGET_MS, tokenCtx, Number.isFinite(amount) ? amount : null);
    for (const hop of hops) {
      if (path.some(p => String(p.address).toLowerCase() === String(hop.address).toLowerCase())) continue;
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }
  return {
    chain: meta.name, chainKey: chain, txid: h, blockTime: timeIso, blockHeight: blk,
    amount: nativeAmt, fee: null, tokenSymbol, tokenAmount,
    sender: tx.from, senderLabel: senderDb.label, recipient, path, exchanges,
  };
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
  /* 宛先がトークンのコントラクトなら、そこは通過点。
     実際に資金を受け取るのは ERC-20 転送の受取先なので、追跡を続ける。 */
  const isRecipToken = recipDb.type === 'token' || isTokenContract(recipLbl);
  const isRecipEx = !isRecipToken && (recipDb.type === 'exchange' || isExchange(recipLbl));
  const path = [
    { address: tx.sender,    label: senderDb.label || tx.sender_label || '', role: 'sender' },
    { address: tx.recipient, label: recipLbl, role: 'recipient', isExchange: isRecipEx, isToken: isRecipToken },
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
    const isTok = db.type === 'token' || isTokenContract(lbl);
    const isVia = isViaService(lbl);
    const isEx = !isTok && !isVia && (db.type === 'exchange' || isExchange(lbl));
    const callAmt = parseFloat(call.value || '0') / 1e18;
    if (callAmt > 0.000001 || isEx) { // 実質送金額ありまたは既知取引所
      path.push({ address: call.recipient, label: lbl, role: 'internal', isExchange: isEx, isToken: isTok, amount: callAmt });
      if (isEx) exchanges.push({ name: lbl, address: call.recipient, amount: callAmt });
    }
  }

  // ERC-20トークン送金の検出（送金額0の場合）
  let tokenSymbol = null;
  let tokenAmount = 0;
  let tokenRecipient = null;
  let tokenCtx = null;              // 資金がトークンなら、その先も同じトークンで追う
  /* ETHの送金額が0＝トークンの送金。宛先がトークンの契約でも同じ。
     スワップ（ETHを送ってトークンを受け取る）も拾えるよう、両方を条件にする。 */
  if ((parseFloat(tx.value) === 0 || isRecipToken) && tx.block_id) {
    try {
      const etUrl = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=tokentx&address=${tx.sender}&startblock=${tx.block_id}&endblock=${tx.block_id}&sort=asc&apikey=${ETHERSCAN_KEY}`;
      const etR = await fetchT(etUrl);
      const etJ = await etR.json();
      const tokenTxs = Array.isArray(etJ.result) ? etJ.result : [];
      let matchTx = tokenTxs.find(t => t.hash.toLowerCase() === h.toLowerCase());
      if (matchTx && isImpostorToken(matchTx.tokenSymbol, matchTx.contractAddress)) {
        console.log(`[ETH] 「${matchTx.tokenSymbol}」を名乗る別トークン。被害資金として扱わない`);
        matchTx = null;
      }
      if (matchTx) {
        const dec = parseInt(matchTx.tokenDecimal) || 18;
        tokenSymbol = matchTx.tokenSymbol;
        tokenAmount = parseFloat(matchTx.value) / Math.pow(10, dec);
        tokenRecipient = matchTx.to;
        console.log(`[ETH] ERC-20検出: ${tokenAmount} ${tokenSymbol} → ${tokenRecipient}`);
        tokenCtx = { contract: matchTx.contractAddress, symbol: tokenSymbol, decimals: dec };
        // トークン受取人がpath未登録なら追加
        if (tokenRecipient && !path.some(p => p.address?.toLowerCase() === tokenRecipient.toLowerCase())) {
          const trDb  = getLabel(tokenRecipient);
          const trLbl = await fetchAddressLabel(tokenRecipient, 'eth').catch(() => '') || trDb.label || '';
          const trIsEx = trDb.type === 'exchange' || isExchange(trLbl);
          path.push({ address: tokenRecipient, label: trLbl, role: 'token_recipient', isExchange: trIsEx, amount: tokenAmount, token: tokenSymbol });
          /* ★トークンのコントラクトは経路から外す。
             USDTを送るとき、宛先はUSDTの契約になるが、そこに資金が置かれるわけではない。
             実際の受取人が分かった以上、契約を経路に残すと
             「Tether USD に到達した」という誤った読み方になるうえ、
             取引数が桁違いに多いため truncateAfterVia が
             その後ろ（＝本当の受取人）ごと切り落としてしまう。 */
          if (isRecipToken) {
            const ci = path.findIndex(p => p.address?.toLowerCase() === tx.recipient?.toLowerCase());
            if (ci > 0) { path.splice(ci, 1); console.log(`[ETH] ${tokenSymbol}の契約を経路から外した（送金の手段であって到達先ではない）`); }
          }
          if (trIsEx) exchanges.push({ name: trLbl, address: tokenRecipient, amount: tokenAmount });
        }
      }
    } catch(e) { console.error('[ETH] ERC20検出エラー:', e.message); }
  }

  // 直接送金先が取引所でない場合 → 送金先からホップ追跡
  const traceFrom = tokenRecipient || tx.recipient;
  if (!isRecipEx && !exchanges.length) {
    /* 資金がトークンなら、その旨を渡す。渡さないとETHの送金を探しに行き、
       「次TX見つからず」で止まる（USDT送金で実際に起きていた）。 */
    const startAmt = tokenRecipient ? tokenAmount : (parseFloat(tx.value) / 1e18);
    const hops = await traceHops(traceFrom, tx.time, 'eth', 10, Date.now() + TRACE_BUDGET_MS, tokenCtx, startAmt);
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
  /* ★先頭2つにも時刻と金額を入れる。ここが空だと、枝の探索が
     「いつ・いくら」を知らないまま始まり、その場で行き止まりになる
     （実測：XRPの調査で1地点だけ見て終わっていた）。
     画面で1次先だけ金額が出ていなかったのも同じ理由。 */
  const path = [
    { address: tx.Account, label: senderDb.label, role: 'sender', time: tx.date },
    { address: tx.Destination, label: destLbl, role: 'recipient', isExchange: isDestEx,
      time: tx.date, amount: xrpAmount(tx.Amount) },
  ];
  const exchanges = isDestEx ? [{ name: destLbl, address: tx.Destination, amount: xrpAmount(tx.Amount) }] : [];
  if (!isDestEx) {
    /* ★受け取った額を渡す。渡さないと最初の一手が「最初に見つけた1件」になる。 */
    const hops = await traceHops(tx.Destination, tx.date, 'xrp', 10,
      Date.now() + TRACE_BUDGET_MS, null, xrpAmount(tx.Amount));
    for (const hop of hops) {
      if (!path.some(p => p.address === hop.address)) {
        path.push(hop);
        if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
      }
    }
  }
  return { chain: 'XRP', txid: h, blockTime: tx.date, blockHeight: tx.ledger_index,
    amount: xrpAmount(tx.Amount), sender: tx.Account, senderLabel: senderDb.label,
    recipient: tx.Destination, destTag: tx.DestinationTag, path, exchanges };
}

/* TRON。被害の大半はUSDT-TRC20で、TronScanが取引所名（addressTag）まで
   同梱してくれるため、名前を引くための追加照会がほとんど要らない。 */
async function investigateTRON(txid) {
  const t = await tronTxInfo(txid);
  if (!t) throw new Error('TRON TXが見つかりません');
  const senderDb = getLabel(t.from);
  const destDb   = getLabel(t.to);
  const destLbl  = (await fetchAddressLabel(t.to, 'tron')) || destDb.label || '';
  const isDestEx = destDb.type === 'exchange' || isExchange(destLbl);
  const tTime = new Date(t.time).toISOString();     // ★枝の探索の起点に渡す
  const path = [
    { address: t.from, label: senderDb.label || tronTags.get(t.from) || '', role: 'sender',
      time: tTime },
    { address: t.to, label: destLbl, role: 'recipient', isExchange: isDestEx,
      amount: t.amount, token: t.token || undefined, time: tTime },
  ];
  const exchanges = isDestEx ? [{ name: destLbl, address: t.to, amount: t.amount }] : [];
  if (!isDestEx) {
    /* ★受け取った額を渡す。TRONは日本の被害でいちばん多い経路。 */
    const hops = await traceHops(t.to, new Date(t.time).toISOString(), 'tron', 10,
      Date.now() + TRACE_BUDGET_MS, null, Number.isFinite(t.amount) ? t.amount : null);
    for (const hop of hops) {
      if (path.some(p => p.address === hop.address)) continue;
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }
  return { chain: 'TRON', txid, blockTime: new Date(t.time).toISOString(), blockHeight: t.block,
    amount: t.token ? null : t.amount, tokenAmount: t.token ? t.amount : undefined,
    tokenSymbol: t.token || undefined, amountUSD: t.usdAtTime,
    sender: t.from, senderLabel: senderDb.label, recipient: t.to, path, exchanges };
}

/* 経路から到達取引所の一覧を作る。★何度呼んでも同じ結果になるようにしてある。
   情報付けが締切をまたいで終わることがあり、そのとき一覧を作った時点では
   まだ「取引所」と分かっていない場合がある（実測：経路には取引所と出ているのに
   凍結要請先が空になった）。呼び出し側が最後にもう一度呼べるようにする。 */
/* 薄まった地点より後ろか。経路の順に見て、最初の薄まりから先を印にする。 */
function markAfterDilution(path) {
  let seen = null;
  for (const n of (path || [])) {
    if (seen) n.afterDilution = seen;
    if (n.dilutionX && !seen) seen = { at: n.address, x: n.dilutionX, label: n.label || '' };
  }
  return seen;
}

function collectExchanges(result) {
  markAfterDilution(result && result.path);
  result.exchanges = result.exchanges || [];
  /* ★被害者が出金した元は、凍結を要請する相手ではない。
     本線の先頭は除いていたが、★分岐やブリッジ先で見つけた取引所には
     効いていなかった。資金が元の場所へ戻ることはあるので、
     アドレスそのもので除く（利用者の指摘・第5-K節）。
     ※同じ取引所の【別の】アドレスは対象。そこは要請先になりうる。 */
  const origin = new Set([
    String(result.sender || '').toLowerCase(),
    String((result.path || [])[0]?.address || '').toLowerCase(),
  ].filter(Boolean));
  const isOrigin = a => origin.has(String(a || '').toLowerCase());
  result.exchanges = result.exchanges.filter(e => !isOrigin(e.address));
  for (const [i, n] of (result.path || []).entries()) {
    // 先頭は送金元。被害者が出金した取引所であって、凍結を要請する相手ではない
    if (i === 0 || n.role === 'sender') continue;
    if (!n.isExchange || n.isVia || n.isToken || !n.address) continue;
    if (isOrigin(n.address)) continue;                 // 出金元は要請先ではない
    if (result.exchanges.some(e => (e.address || '').toLowerCase() === n.address.toLowerCase())) continue;
    /* ★薄まった地点より後ろでも、必ず記載する（方針・第5-H節）。
       薄まったことは印として添え、判断は読み手に委ねる。
       ★伏せると被害者は手がかりを失うだけで、良いことは何も無い。 */
    result.exchanges.push({ name: n.label || '取引所（名称未判明）', address: n.address,
      amount: n.amount, afterDilution: n.afterDilution || null,
      share: n.exploredShare ?? null, hops: n.exploredHops ?? null,
      explored: n.role === 'explored' || undefined });
  }

  /* ★経路の途中で「同じ地点から取引所へも送られていた」場合も載せる。
     本線に選ばなかっただけで、送金の記録は残っている。
     実測（TRON経路②）：入金の5%が Binance へ出ていたが、
     95%の別送金を本線にしたため、報告書に Binance が出てこなかった。
     ★被害者が欲しいのは換金先の名前であって、どちらが本線かではない。 */
  for (const [i, n] of (result.path || []).entries()) {
    if (i === 0 || n.role === 'sender') continue;
    for (const e of (n.exchangeNearby || [])) {
      if (!e.address || isOrigin(e.address)) continue;   // 出金元は要請先ではない
      if (result.exchanges.some(x => String(x.address || '').toLowerCase() === e.address.toLowerCase())) continue;
      result.exchanges.push({ name: e.label || '取引所（名称未判明）', address: e.address,
        amount: e.amount, sameHop: true });
    }
  }

  /* ★ブリッジを渡った先で取引所に着いた場合も、凍結要請の宛先に載せる。
     被害者が知りたいのは換金先であって、ブリッジの名前ではない。
     どのチェーンのアドレスかを添えないと、要請文が書けない。 */
  for (const n of (result.path || [])) {
    const ex = n.crossChainExchange;
    if (!ex || !ex.address || isOrigin(ex.address)) continue;   // 出金元は要請先ではない
    if (result.exchanges.some(e => String(e.address || '').toLowerCase() === ex.address.toLowerCase())) continue;
    result.exchanges.push({ name: ex.name, address: ex.address,
      amount: n.bridgeTo?.amount ?? null, chain: n.bridgeTo?.chainName || null, viaBridge: true });
  }

}

/* 調査1件ごとの「どの段に何秒かかったか」。直近だけ残す。
   ★これが無いと、時間切れの原因を推測でしか追えない。 */
const PHASE_KEEP = 40;
const phaseLog   = [];          // { at, txid(先頭のみ), chain, total, phases: {段: ms} }

function mkPhases(txid) {
  const t0 = Date.now();
  let last = t0;
  const phases = {};
  return {
    mark(name) { phases[name] = Date.now() - last; last = Date.now(); },
    done(chain) {
      phaseLog.push({ at: new Date().toISOString(), txid: String(txid).slice(0, 12) + '…',
                      chain: chain || '?', total: Date.now() - t0, phases });
      if (phaseLog.length > PHASE_KEEP) phaseLog.splice(0, phaseLog.length - PHASE_KEEP);
    },
  };
}

async function investigate(txid, chain, opts = {}) {
  /* ★全体の締切。各段の予算を足しただけでは守れない（1周にかかる時間が
     増えると超える。実測で2回とも時間切れになった）。
     ★時間切れは何も出せない＝間違った答えより悪い。
     残り時間から後段の予算を削って、必ず内側で終える。 */
  const hardDeadline = Date.now() + investigateSoftMs(opts.paid);
  tronDeniedReset();                 // ★この調査でTRONに断られた回数を数え直す
  const ph = mkPhases(txid);
  let result;
  if (chain === 'btc') {
    /* TRONのTXIDはBTCと同じ64桁の小文字16進で、形では区別できない。
       BTCで見つからなければTRONを試す。日本の被害はUSDT-TRC20が最も多い。 */
    try {
      result = await investigateBTC(txid);
    } catch (e) {
      /* 通信断とTX不在を混同しない。混同するとBTCの一時障害が
         「TRONにも見つかりません」という誤った案内になる。 */
      if (!/見つかりません/.test(e.message)) throw e;
      console.log(`[investigate] BTCで見つからず、TRONとして試します`);
      try {
        result = await investigateTRON(txid);
        chain  = 'tron';
      } catch (e2) {
        if (!/見つかりません/.test(e2.message)) throw e2;
        throw new Error('このTXIDは BTC・TRON のどちらにも見つかりませんでした');
      }
    }
  }
  else if (chain === 'eth') {
    /* ★0x+64桁のTXIDは、EVM系のどのチェーンでも同じ形。
       Ethereum に無ければ、他のチェーンを順に試す。
       試さないと、被害者には「見つかりません」としか出ない
       （実例：利用者の正解経路④は Polygon の取引だった。第5-E節）。
       BTC→TRON で既に使っている「見つからなければ次を試す」と同じ形。 */
    /* ★どのチェーンにあるかを、先に軽い問い合わせだけで確かめる。
       以前は「Ethereum で失敗したら例外の文言を見て次を試す」形にしたが、
       通信の一時的な失敗（時間切れ）まで「見つからない」と混同するうえ、
       ★逆に時間切れを本物の失敗として投げ返してしまい、
         他のチェーンを試さずに調査ごと終わっていた（実測）。
       探すことと調べることを分ける。 */
    chain = await detectEVMChain(txid);
    ph.mark('チェーンの特定');
    if (!chain) throw new Error('このTXIDは Ethereum・Polygon・Arbitrum のいずれにも見つかりませんでした');
    /* ★Ethereum の調査は Blockchair の取引明細に依存していて、
       相手が遅いと全体を巻き込む。締切内に返らなければ、
       Etherscan だけで組んだ軽い方に切り替える。
       ★内部の呼び出し明細は落ちるが、経路と到達先は出る。
         何も出せないより、出せる分を出す。 */
    if (chain === 'eth') {
      const sub = Math.max(5000, hardDeadline - Date.now() - 12000);
      result = await Promise.race([
        investigateETH(txid),
        new Promise(res => setTimeout(() => res(null), sub)),
      ]);
      ph.mark('本体の調査(Blockchair)');
      if (!result) {
        console.log('[investigate] Blockchair 側が締切に間に合わず、Etherscan だけで調べ直します');
        result = await investigateEVM(txid, 'eth');
      }
    } else {
      result = await investigateEVM(txid, chain);
    }
  }
  else if (chain === 'xrp') result = await investigateXRP(txid);
  else if (chain === 'tron') result = await investigateTRON(txid);
  else throw new Error('未対応チェーン');

  // 各アドレスノードに残高・TX件数を付加
  /* ★情報付け（残高・ラベル・参考経路・ブリッジ先）は「あれば嬉しい」情報。
     どれだけ遅れても、経路そのものは返し切る。
     ★以前はここが延びると調査ごと失敗し、利用者には何も出せなかった
       （実測で3回連続、同じTXIDが75秒の上限で失敗）。
     締切が来たら待つのをやめて先へ進む。付いた分だけ使う。 */
  await Promise.race([
    enrichPathWithAddressInfo(result.path, chain, { ...opts, hardDeadline })
      .catch(e => console.error('[investigate] 情報付けに失敗:', e.message)),
    new Promise(res => setTimeout(res, Math.max(2000, hardDeadline - Date.now()))),
  ]);
  if (Date.now() > hardDeadline) console.log('[investigate] 締切のため情報付けを途中で切り上げました');

  /* 到達取引所の一覧は経路をたどる段階で作られるが、名前が後から
     （ラベルAPIや振る舞い推定で）付くことがある。その分をここで足す。
     これをしないと、経路には「取引所」と出ているのに一覧が空になり、
     画面の見出しや報告書の凍結要請先が出てこない。
     DEX・ブリッジ・トークン契約は着金先ではないので入れない。 */
  ph.mark('情報付け');
  result.tronDenied = tronDeniedCount();   // ★断られた回数を説明に載せるため
  collectExchanges(result);
  attachNotes(result);

  /* ★取引所が出なかったとき、「見つからなかった」で終わらせない。
     詐欺の資金が現金化のため取引所へ届くまでは1週間以内のことが多い
     （運営の実感・記録：第4-Z節）。送金からまだ日が浅いなら、
     追跡が途中で止まるのは資金がまだ動いている最中である可能性が高い。
     ★ここは被害者が最も焦っている時期で、
       「見つかりません」だけ返すのは事実としても不親切であり、
       数日後の再調査という次の行動を示せる場面。 */
  const t0 = new Date(normalizeTimeStr(result.blockTime)).getTime();
  if (!result.exchanges.length && Number.isFinite(t0) && t0 > 0) {
    const days = Math.floor((Date.now() - t0) / 86400000);
    if (days >= 0 && days <= STILL_MOVING_DAYS) result.stillMoving = { days };
  }
  ph.done(result.chain);
  return result;
}

/* 詐欺資金が取引所に届くまでの日数の目安。これを過ぎても出ない場合は
   「移動中」ではなく、追跡の限界（ブリッジ等）を疑う。 */
const STILL_MOVING_DAYS = 7;

function stillMovingText(sm) {
  if (!sm) return '';
  const d = sm.days === 0 ? '本日' : `${sm.days}日前`;
  return `送金は${d}です。詐欺被害の資金が現金化のため取引所へ届くまでは`
    + `1週間以内のことが多く、いま取引所が出ないのは`
    + `資金がまだ移動している最中である可能性があります。`
    + `数日後にもう一度同じTXIDで調べると、取引所が判明することがあります。`;
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
          const st = s.txHash ? `\n   ┃  TXID：${s.txHash}` : '';
          return `   ┣ 同時送金先：${sa}${sl}${sm}${st}`;
        }).join('\n')
      : '';
    /* 合流したことは文章でも必ず伝える。伏せると確定した経路と読まれる。 */
    const poolLine = !p.pooled ? ''
      : p.poolDests > 1
        ? `\n   ⚠ ここで他の資金と合流（この直後 ${p.poolDests}箇所に分散`
          + `${p.poolShare != null ? `／最大の送金先が ${Math.round(p.poolShare * 100)}%` : ''}）`
        : `\n   ⚠ ここで他の資金と合流`;
    return `🔵 中継アドレス（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}${poolLine}${siblingLines}`;
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
    const moving = result.stillMoving ? `\n\n⏳ ${stillMovingText(result.stillMoving)}` : '';
    exSection = `\n⚠️ 取引所判定\n━━━━━━━━━━━━━━━━━\n送金先は既知の取引所DBに一致しませんでした。${lastLabel}${lastAddr}${moving}\n追加追跡が必要な場合はご連絡ください。`;
  }

  const amountDisplay = (result.tokenSymbol && result.tokenAmount > 0)
    ? `${result.tokenAmount.toFixed(6)} ${result.tokenSymbol}（ERC-20トークン）`
    : `${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}`;
  /* 経路を見せる以上、読み方を必ず添える（記録：第4-Z節）。 */
  const caveat = `\n\n📖 この経路の読み方\n━━━━━━━━━━━━━━━━━\n`
    + `経路はブロックチェーン上の記録でつながっていますが、最初に送金されたものと\n`
    + `同じ資金である保証はありません。暗号資産には印が無く、複数の資金が同じ\n`
    + `アドレスを通ると区別できないためです。追跡全体の前提としてご承知ください。`;
  return `📊 BitTo 調査レポート\n━━━━━━━━━━━━━━━━━\n${em} チェーン：${result.chain}\n🔗 TXID：${txShort}\n📅 送金日時：${fmtDate(result.blockTime)}\n💰 送金額：${amountDisplay}${(result.fee != null && !isNaN(result.fee)) ? `\n⛽ 手数料：${result.fee.toFixed(8)} ${result.chain}` : ''}${result.destTag != null ? `\n🏷 宛先タグ：${result.destTag}` : ''}\n\n📍 送金経路\n━━━━━━━━━━━━━━━━━\n${pathLines.join('\n　↓\n')}${caveat}\n${exSection}${tplSection}\n\n🔒 BitTo が自動生成したレポートです`;
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
/* 合言葉をURLに載せると、ブラウザの履歴・サーバーのログ・共有したURLに残る。
   実際に検索欄へ貼られて外部に出たことがあるため、一度使ったら Cookie に移し、
   URLからは消す。以後はURLに合言葉が現れない。 */
const ADMIN_COOKIE = 'bitto_admin';
const ADMIN_COOKIE_MAX_AGE = 12 * 60 * 60 * 1000;   // 12時間で切れる
function readCookie(req, name) {
  const raw = req.headers.cookie || '';
  for (const part of raw.split(';')) {
    const i = part.indexOf('=');
    if (i < 0) continue;
    if (part.slice(0, i).trim() === name) {
      try { return decodeURIComponent(part.slice(i + 1).trim()); } catch { return ''; }
    }
  }
  return '';
}
/* 長さや先頭の一致具合で応答時間が変わらないようにして比べる。 */
function adminTokenMatches(given) {
  const a = Buffer.from(String(given || ''), 'utf8');
  const b = Buffer.from(ADMIN_TOKEN, 'utf8');
  if (a.length !== b.length) return false;
  try { return crypto.timingSafeEqual(a, b); } catch { return false; }
}
function adminOk(req) {
  if (!ADMIN_TOKEN) return true;
  const t = (req.query && req.query.t)
    || req.headers['x-admin-token']
    || readCookie(req, ADMIN_COOKIE) || '';
  return adminTokenMatches(t);
}
/* 合言葉を間違えた回数。総当たりを遅らせる。 */
const adminTries = new Map();   // IP → { n, until }
function adminTryOk(ip) {
  const t = adminTries.get(ip);
  if (t && t.until > Date.now()) return false;
  return true;
}
function adminTryFail(ip) {
  const t = adminTries.get(ip) || { n: 0, until: 0 };
  t.n++;
  // 5回間違えたら15分待たせる
  if (t.n >= 5) { t.until = Date.now() + 15 * 60 * 1000; t.n = 0; }
  adminTries.set(ip, t);
}
function reqIp(req) {
  return (req.headers['x-forwarded-for'] || '').split(',')[0].trim() || req.ip || '';
}

function requireAdmin(req, res, next) {
  if (!adminOk(req)) {
    /* 画面を開こうとした場合は入力欄へ送る。合言葉付きURLを
       組み立てさせると、貼り間違えて外部に出る（実際に起きた）。
       APIは従来どおり404のまま。総当たりの的にしない。 */
    if (String(req.headers.accept || '').includes('text/html')) {
      return res.redirect('/admin/login?next=' + encodeURIComponent(req.path));
    }
    return res.status(404).send('Not found');
  }
  /* URLで渡ってきたときは Cookie に移し、合言葉を消したURLへ送り直す。
     画面を開いた場合だけ。curl などのAPI利用は、そのまま応答する。 */
  if (ADMIN_TOKEN && req.query && req.query.t) {
    res.cookie(ADMIN_COOKIE, ADMIN_TOKEN, {
      httpOnly: true,                       // JavaScriptから読めない
      secure: BASE_URL.startsWith('https'),
      sameSite: 'strict',                   // 他サイトからの遷移では送られない
      maxAge: ADMIN_COOKIE_MAX_AGE,
      path: '/',
    });
    if (String(req.headers.accept || '').includes('text/html')) {
      const q = new URLSearchParams(req.query);
      q.delete('t');
      const rest = q.toString();
      return res.redirect(req.path + (rest ? '?' + rest : ''));
    }
  }
  next();
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


/* 経路によく出るサービスの一行説明。名前に含まれる語で引く。
   暗号資産に不慣れな方にも、その地点が何なのかが分かるようにする。 */
const SERVICE_NOTES = [
  ['li.fi',        '複数のチェーンにまたがって交換・移動をまとめて行う橋渡しサービス'],
  ['lifidiamond',  '複数のチェーンにまたがって交換・移動をまとめて行う橋渡しサービス（LI.FI）'],
  ['tokenlon',     '取引所を介さずに通貨を交換できるサービス（分散型取引所）'],
  ['permit2',      'ウォレットの利用許可をまとめて扱うUniswapの仕組み。資金の保管先ではない'],
  ['wrapped ether','ETHを他のサービスで扱える形（WETH）に置き換える仕組み。中身はETHのまま'],
  ['weth',         'ETHを他のサービスで扱える形に置き換える仕組み。中身はETHのまま'],
  ['tokenwrapper', '通貨を別の形式に置き換える仕組み'],
  ['ammwrapper',   '交換の仲介を行う仕組み（分散型取引所の一部）'],
  ['uniswap',      '取引所を介さずに通貨を交換できるサービス（分散型取引所）'],
  ['sushiswap',    '取引所を介さずに通貨を交換できるサービス（分散型取引所）'],
  ['1inch',        '複数の分散型取引所から有利な交換先を探すサービス'],
  ['paraswap',     '複数の分散型取引所から有利な交換先を探すサービス'],
  ['transitswap',  '複数のチェーンにまたがる交換サービス'],
  ['bridgers',     '複数のチェーンにまたがる交換・橋渡しサービス'],
  ['stargate',     'チェーン間で資金を移動させる橋渡しサービス'],
  ['layerzero',    'チェーン間で資金を移動させる橋渡しの仕組み'],
  ['hop protocol', 'チェーン間で資金を移動させる橋渡しサービス'],
  ['across',       'チェーン間で資金を移動させる橋渡しサービス'],
  ['synapse',      'チェーン間で資金を移動させる橋渡しサービス'],
  ['thorchain',    '異なるチェーンの通貨を直接交換できるサービス'],
  ['changenow',    '口座開設なしで通貨を交換できるサービス'],
  ['fixedfloat',   '口座開設なしで通貨を交換できるサービス'],
  ['simpleswap',   '口座開設なしで通貨を交換できるサービス'],
  ['sideshift',    '口座開設なしで通貨を交換できるサービス'],
  ['tornado',      '資金の出所を分からなくするサービス（ミキサー）。ここを通ると追跡が著しく困難になります'],
  ['mixer',        '資金の出所を分からなくするサービス（ミキサー）。ここを通ると追跡が著しく困難になります'],
  ['tether',       '米ドルに連動する通貨（USDT）を発行する仕組み'],
  ['usdc',         '米ドルに連動する通貨（USDC）を発行する仕組み'],
];
/* ★経路を見せる以上、その読み方を必ず添える。
   暗号資産に印は無く、複数の資金が同じアドレスを通れば区別できない。
   「同じ資金である保証が無い」のは経路全体の前提であって、
   どこか特定の地点から急に始まる話ではない（記録：第4-Z節）。
   前提を書かずに線だけ見せると、確定した事実として読まれる。
   読むのは被害者・弁護士・警察で、これをもとに動く人たち。 */
/* ══ 説明文はサーバーが書く ══════════════════════════════════
   ★これまで、判定はサーバー・説明文は画面側、と分かれていた。
     アプリは画面のコードを中に抱えているので、★説明を直すたびに
     ストア審査とビルドが要る。実際、今日だけで文言を何度も直しており、
     アプリ側だけが古い説明のまま取り残されていた。

   ★判定した側が説明を書く。表示する側は受け取ったものを出すだけ。
     こうすれば、文言の調整にビルドも審査も要らない。
     判定と説明が離れていると、片方だけ古くなる。

   受け渡しは飾りの無い文だけにする。見た目は表示する側が決める。
   HTMLを送らないので、貼り付け先で壊れる心配もない。 */
function note(kind, level, title, text, sub) {
  return { kind, level, title, text, sub: sub || undefined };
}

/* 経路の1地点に添える説明。 */
function nodeNotes(p) {
  const out = [];
  if (p.pooled) {
    const many = p.poolDests > 1;
    const keepSub = 'ただし、この先で到達した取引所は伏せずに記載しています。'
      + '経路が記録として存在することは事実であり、照会の価値があるためです。'
      + '確度の但し書きとあわせて、警察・弁護士にお伝えください。';
    if (p.poolKind === 'split') {
      /* ★減っている＝合流ではなく分割。残りが別の送金先にある、という事実を伝える。
         「合流」と書くと、読み手は他人の資金が混ざったと受け取ってしまう。 */
      const kept = p.keptShare != null ? Math.round(p.keptShare * 100) : null;
      out.push(note('pooled', 'warn', 'ここで資金が分けられています',
        (kept != null ? `入ってきた資金のうち約${kept}%がこの先へ進んでいます。` : '')
        + (many ? `残りは別の送金先（全部で${p.poolDests}箇所）へ渡っています。` : '残りは別へ渡っています。')
        + 'そのため、ここから先はご依頼の資金の一部だけを追っていることになります。',
        keepSub));
    } else {
      out.push(note('pooled', 'warn', 'ここで他の資金と合流しています',
        (many ? `この直後、資金は${p.poolDests}箇所に分かれています。` : '')
        + (many && p.poolShare != null ? `そのうち最も多い送金先が${Math.round(p.poolShare * 100)}%で、この先はそれを追っています。` : '')
        + '複数の資金がまとまるため、ここから先は同じ資金と言い切れません。',
        keepSub));
    }
  }
  if (p.dilutionX) {
    out.push(note('dilution', 'warn', `約${p.dilutionX}倍の流れに合流しています`,
      'この先に出てくる送金先は、ご依頼の資金が届いたものとは断定できません。',
      'ただし経路が記録として存在することは事実なので、伏せずに記載しています。'));
  }
  if (p.bridgeTo) {
    /* ★経路の枠そのものに出す。下に説明を置くだけでは見落とされる。
       「ここで別のチェーンへ渡った」は、経路を目で追う人が
       いちばん知りたい一点。 */
    const t = p.bridgeTo;
    out.push(note('bridge', 'good', `ここで ${t.chainName} へ渡っています`,
      `渡り先：${t.address}`
      + (t.arrivedAmount != null ? `／届いた額：${String(t.arrivedAmount).slice(0, 14)} ${t.arrivedToken || ''}` : '')));
  }
  if (p.branchTaken) {
    out.push(note('branch', 'info', 'この地点では複数の送金先がありました',
      'それぞれの先を実際にたどり、取引所に到達した方をこの経路として採用しています。',
      (p.droppedBranch || []).length
        ? '採用しなかった送金先：' + p.droppedBranch.map(d => (d.label ? d.label + ' ' : '') + d.address).join('／')
        : undefined));
  }
  return out;
}

/* その通貨の単位。★ブリッジの説明で ETH に固定していた誤りを直すために使う。 */
function nativeUnit(chain) {
  return { btc: 'BTC', eth: 'ETH', polygon: 'POL', arbitrum: 'ETH',
           xrp: 'XRP', tron: 'TRX' }[String(chain || '').toLowerCase()] || '';
}

/* 調査全体に添える説明。 */
function resultNotes(result) {
  const path = result.path || [];
  const out = [];
  const stop = path.find(p => p.traceStop);
  const crowd = stop && (stop.stopReason === 'crowded' || stop.stopReason === 'via');
  out.push(note('caveat', 'info', 'この経路の読み方',
    '経路はブロックチェーン上の記録でつながっていますが、最初に送金されたものと'
    + '同じ資金である保証はありません。暗号資産には印が無く、複数の資金が同じ'
    + 'アドレスを通ると区別できないためです。これは本調査に限らず、'
    + 'ブロックチェーン追跡全体の前提です。',
    crowd ? `とくに ${stop.label || '利用者の多いアドレス'} から先は、多くの人の資金が通る地点を`
      + '経由しているため確度が下がります。ただしつながり自体は記録に残っているため、'
      + '判断材料として省かずに記載しています。' : undefined));

  /* ★TRONの取得を断られたなら、そう書く。黙っていると
     「そこで送金が終わった」と読まれ、事実と違う結論になる。 */
  if (result.tronDenied > 0) {
    out.push(note('tron-limit', 'warn', 'TRONの照会が制限され、追跡を最後まで行えていません',
      `TRONの取引履歴の取得を ${result.tronDenied} 回断られました（回数制限）。`
      + 'この先に送金が無かったのではなく、確認できなかったという意味です。',
      '時間をおいて再度お試しいただくと、続きをたどれる場合があります。'));
  }
  const b = path.find(p => p.bridgeTo);
  if (b) {
    const t = b.bridgeTo;
    out.push(note('bridge', 'good', '別のチェーンへ渡った先が判明しました',
      `${b.label || 'このコントラクト'}（${t.bridge}）から ${t.chainName} へ渡っています。`
      + `渡った先のアドレス：${t.address}`
      /* ★単位は調査した通貨に合わせる。ここを ETH に固定していたため、
         XRPの調査で「1998.9995 ETH」と誤った通貨名を出していた（実測）。 */
      + (t.amount != null ? `／渡した額：${String(t.amount).slice(0, 12)} ${nativeUnit(result.chain)}` : '')
      + (t.arrivedAmount != null ? `／届いた額：${String(t.arrivedAmount).slice(0, 14)} ${t.arrivedToken || ''}` : '')
      /* ★渡った先で追えた分も必ず書く。追ったのに見せなければ、
         被害者にとっては追っていないのと同じ。 */
      + ((b.crossChainHops || []).length
          ? `　${t.chainName} 側でさらに ${b.crossChainHops.length} 段たどりました：`
            + b.crossChainHops.map((h, i) => `${i + 1}. ${h.address}`
                + (h.label ? `（${h.label}）` : '')
                + (h.amount != null ? ` ${String(h.amount).slice(0, 12)} ${h.token || ''}` : '')).join('　')
          : '')
      + (b.crossChainExchange ? `　到達した取引所：${b.crossChainExchange.name}（${b.crossChainExchange.address}）` : ''),
      '渡り先は、ブリッジへの送金に含まれる指定内容から復元しています。'
      + 'ブリッジは通貨を換えて払い出すため、送った額と数字が変わります。'
      + `照会の際は、チェーン名（${t.chainName}）を必ず添えてください。`));
  }
  /* ★分けられた資金の行き先を、割合つきでまとめて出す。
     凍結要請は複数の取引所へ同時に出せるので、
     「どこへ、どれだけ」が分かることに意味がある。 */
  const withShare = (result.exchanges || []).filter(e => e.share != null);
  if (withShare.length > 1) {
    const lines = withShare.slice(0, 6)
      .map(e => `${e.name}：約${Math.round(e.share * 100)}%（${e.hops != null ? e.hops + '次先' : ''}）`)
      .join('／');
    out.push(note('spread', 'good', '分けられた資金の行き先',
      `ご依頼の資金は複数に分かれています。それぞれの枝を実際にたどった結果、`
      + `次の取引所に到達しました。${lines}`,
      '割合は、各地点で送り出された額のうちその枝が占める分を掛け合わせた概算です。'
      + '断定はできませんが、★どの取引所へ多く流れたかの目安になります。'
      + '凍結要請は複数の取引所へ同時に出せます。'));
  }
  if (result.stillMoving) {
    out.push(note('moving', 'warn', 'まだ資金が動いている最中かもしれません',
      stillMovingText(result.stillMoving)));
  }
  return out;
}

/* 結果に説明文を載せる。何度呼んでも同じになるようにする。 */
function attachNotes(result) {
  if (!result) return result;
  for (const p of (result.path || [])) p.notes = nodeNotes(p);
  result.notes = resultNotes(result);
  return result;
}

/* ★どうやって見つけた取引所かを、必ず添える。
   これまで「本線で到達した」「同じ地点から分岐して到達した」
   「ブリッジを渡った先で到達した」を区別せず、すべて同じ確度に見せていた。

   ★名前を出すこと自体は正しい。合流地点では「どちらが本件の資金か」を
     そもそも断定できないのだから、断定できないことを理由に伏せるのは
     被害者から手がかりを奪うだけになる。
   ★問題は、断定できないものを断定として見せること。
     凍結要請を出すか決めるのは読み手（被害者・弁護士・警察）で、
     判断には「どのくらい確かか」が要る。 */
function exProvenanceHTML(ex) {
  if (!ex) return '';
  /* ★薄まった先でも必ず記載する（方針・第5-H節）。
     伏せると被害者は手がかりを失うだけ。薄まり具合を数字で示し、
     判断は読み手（被害者・弁護士・警察）に委ねる。 */
  if (ex.afterDilution) {
    const d = ex.afterDilution;
    return `<p class="flow-note" style="border-left:3px solid var(--r-accent);padding-left:10px">
    <strong>■ この取引所は、資金が大きくまとめられた地点より先で到達したものです。</strong><br>
    経路上の <strong>${escHtml(d.label || d.at || 'ある地点')}</strong> で、
    ご依頼の資金は<strong>約${escHtml(String(d.x))}倍の流れに合流</strong>しています。
    そこから先は多数の資金が混ざるため、<strong>この取引所に届いたのがご依頼の資金である、
    とは断定できません。</strong><br>
    ただし<strong>この経路が記録として存在することは事実です。</strong>
    照会の価値はあると考え、判断材料として記載しています。
    <strong>警察・弁護士にご相談の際は、この但し書きも併せてお伝えください。</strong></p>`;
  }
  if (ex.viaBridge) return `<p class="flow-note" style="border-left:3px solid #10b981;padding-left:10px">
    <strong>■ この取引所は、ブリッジを渡った先（${escHtml(ex.chain || '別チェーン')}）で到達したものです。</strong><br>
    渡り先はブリッジへの送金に含まれる指定内容から復元しています。
    <strong>照会の際は、チェーン名（${escHtml(ex.chain || '')}）を必ず添えてください。</strong>
    アドレスの形が同じでも、チェーンが違えば別の口座です。</p>`;
  if (ex.sameHop) return `<p class="flow-note" style="border-left:3px solid var(--r-accent);padding-left:10px">
    <strong>■ この取引所は、経路上の同じ地点から【分岐して】送られた先です。</strong><br>
    その地点では複数の宛先へ同時に送金されており、
    <strong>どれが本件の資金かを一つに断定することはできません。</strong>
    ただし<strong>この取引所へ送金された記録は実在します。</strong>
    照会の価値はあると考え、判断材料として記載しています。</p>`;
  return '';
}

/* 2件目以降も、見つけ方を添えて並べる。1件目だけ出して他を伏せない。 */
function exOthersHTML(list) {
  const rest = (list || []).slice(1);
  if (!rest.length) return '';
  return `<h4 style="margin:18px 0 10px">🏦 このほかに到達した取引所</h4>
    <table class="info-table">
      ${rest.map(e => `<tr><th>${escHtml(e.name || '取引所')}</th><td>
        <span class="mono">${escHtml(e.address)}</span>
        ${e.chain ? `<br><span style="font-size:0.9em">チェーン：${escHtml(e.chain)}</span>` : ''}
        <br><span style="font-size:0.9em;color:#aaa">${
          e.viaBridge ? 'ブリッジを渡った先で到達'
          : e.sameHop ? '同じ地点から分岐して到達（本件の資金と断定はできません）'
          : '経路をたどって到達'}</span></td></tr>`).join('')}
    </table>`;
}

function traceCaveatHTML(path) {
  const stop  = (path || []).find(p => p.traceStop);
  const crowd = stop && (stop.stopReason === 'crowded' || stop.stopReason === 'via');
  const name  = stop && stop.label ? stop.label : '利用者の多いアドレス';
  return `<div class="caveat-box">
    <p style="margin:0 0 6px"><strong>この経路の読み方</strong></p>
    <p style="margin:0">経路はブロックチェーン上の記録でつながっていますが、
    <strong>最初に送金されたものと同じ資金である保証はありません。</strong>
    暗号資産には印が無く、複数の資金が同じアドレスを通ると区別できないためです。
    これは本調査に限らず、ブロックチェーン追跡全体の前提です。</p>
    ${crowd ? `<p style="margin:8px 0 0">とくに <strong>${escHtml(name)}</strong> から先は、
    多くの人の資金が通る地点を経由しているため確度が下がります（薄い枠で示しています）。
    ただし<strong>つながり自体は記録に残っています。</strong>
    判断材料として省かず記載しています。</p>` : ''}
  </div>`;
}

function serviceNote(label) {
  if (!label) return '';
  const lo = String(label).toLowerCase();
  for (const [key, note] of SERVICE_NOTES) if (lo.includes(key)) return note;
  return '';
}

// ══ 有料HTMLレポート生成 ══════════════════════════════════════

function generateReportHTML(results, customerName, issuedAt, aiData = {}, reportUrl = '', brand = 'bitto', hearingUrl = '') {
  const chainFull = { BTC: 'Bitcoin', ETH: 'Ethereum', XRP: 'XRP Ledger', TRON: 'TRON（TRC20）' };

  // ── ブランド出し分け（未指定はBitTo＝従来どおり） ──
  const BRANDS = {
    bitto: {
      pageTitle: 'BitTo 詳細調査レポート',
      coverH1:   '🔗 BitTo 詳細調査レポート',
      coverH1Plain: '詳細調査報告書',
      coverH1Style: '',
      coverSub:  'ブロックチェーン送金経路・取引所特定 調査報告書',
      footer:    '本レポートは BitTo が自動生成した調査報告書です。参考資料としてご活用ください。',
    },
    connection: {
      pageTitle: 'Connection 正式調査報告書',
      coverH1:   'Connection',
      coverH1Plain: '正式調査報告書',
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
    // 資金経路（アドレスとTXIDを順に並べる。図より読みやすく、印刷でも崩れない）
    const routeRows = (r.path || []).map((p, i) => {
      const mark = i === 0 ? '起点' : `経緯${String.fromCharCode(64 + i)}`;   // A, B, C…
      const name = p.label ? `（${escHtml(p.label)}）` : '';
      // この行へ入ってくる送金のTXID。1つ目は調査対象のTXID
      const inTx = i === 0 ? '' : (i === 1 ? r.txid : (p.txHash || ''));
      const arrow = i === 0 ? '' : `<tr class="route-tx"><td colspan="2">↓ TXID　<span class="mono">${escHtml(inTx || '（記録なし）')}</span></td></tr>`;
      return `${arrow}<tr><th>${mark}</th><td><span class="mono">${escHtml(p.address || '')}</span>${name ? ` <b>${name}</b>` : ''}</td></tr>`;
    }).join('');
    const coinId      = { BTC: 'bitcoin', ETH: 'ethereum', XRP: 'ripple', TRON: 'tron' }[r.chain] || 'ethereum';
    /* USDTのようなステーブルコインは、価格推移を出しても常に1ドル付近で
       判断材料にならない。送金額そのものがドル建てなので、グラフは出さない。 */
    const isStable    = /^(usdt|usdc|busd|dai|tusd|usdd|fdusd)$/i.test(String(r.tokenSymbol || ''));
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
      else if (p.isToken) { cls = 'relay'; icon = '🔁'; roleLabel = `スワップ／トークンの通過点（${i}次先）${p.swapTo ? `：→ ${p.swapTo}` : ''}`; }
      else if (p.isVia)   { cls = 'relay'; icon = '🔀'; roleLabel = `経由（DEX・ブリッジ・両替）（${i}次先）`; }
      else if (p.isDeposit) { cls = 'exchange'; icon = '🏧'; roleLabel = `取引所の入金用アドレス（推定）（${i}次先）${p.depositFor ? `：${p.depositFor} 宛` : ''}`; }
      else if (p.isExchange && p.inferred) { cls = 'exchange'; icon = '★'; roleLabel = `🏦 取引所候補（${i}次先・推定）`; }
      else if (p.isExchange) { cls = 'exchange'; icon = '★'; roleLabel = `🏦 取引所到達（${i}次先）`; }
      else if (p.role === 'internal') { cls = 'relay'; icon = '◆'; roleLabel = `内部コール（${i}次先）`; }
      /* このアドレスでトークンに換えられた場合。ここから先は通貨が変わるので、
         読み手が「別の資金では」と誤解しないよう、換わった地点を明示する。 */
      else if (p.swapTo)     { cls = 'relay';    icon = '🔁'; roleLabel = `${i}次先：ここで ${p.swapTo} に交換`; }
      /* ★取引回数が桁違いに多いアドレスは、個人の財布ではなく共有のコントラクト。
         「未特定」と書くと「誰の財布か分からない」と読まれるが、実際は
         何なのか分かっている（数百万人が通る通り道）。
         名前を1つずつ登録するのではなく回数で判定するので、
         知らないコントラクトでも同じように扱える。
         警察や弁護士に説明するときも、通り道だと分かる方が伝わる。 */
      else if (p.txCount != null && p.txCount >= VIA_TRAFFIC_STOP) {
        cls = 'relay'; icon = '🔀';
        roleLabel = `経由（利用者の多いコントラクト・取引${p.txCount.toLocaleString()}回）（${i}次先）`;
      }
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
      // 名前だけでは何のサービスか分からないため、分かるものには一行説明を添える
      const svcNote  = serviceNote(p.label);
      const svcTd    = svcNote ? `<div class="node-note">💡 ${svcNote}</div>` : '';
      /* ★ここで他人の資金と混ざった、という事実を隠さない。
         合流地点から先は「同じ資金を追えた」とは言えず、確度が一段落ちる。
         凍結要請を出す判断は読み手（被害者・弁護士・警察）がするので、
         材料を伏せてはいけない。 */
      /* 送金先が1箇所しかないなら「分散」も「割合100%」も意味を成さない。
         合流した事実だけを伝える。数字を足すほど正確になるわけではない。 */
      const poolMany = p.poolDests > 1;
      /* ★どれだけ薄まったかを数字で出す。追跡は続けるが、確度は正直に示す。 */
      /* ★分岐を確かめて採用した地点。どう選んだかを隠さない。 */
      const brTd = p.branchTaken ? `<div class="node-note" style="color:#93c5fd">
        ◆ この地点では複数の送金先がありました。<strong>それぞれの先を実際にたどり、
        取引所に到達した方をこの経路として採用しています。</strong>
        ${(p.droppedBranch||[]).length ? '<br><span style="color:#aaa">採用しなかった送金先：'
          + p.droppedBranch.map(d => escHtml((d.label ? d.label + ' ' : '') + d.address)).join('／') + '</span>' : ''}
      </div>` : '';
      const dilTd = p.dilutionX ? `<div class="node-note" style="color:#fbbf24">
        ⚠ ここでご依頼の資金は<strong>約${p.dilutionX}倍の流れに合流</strong>しています。
        <br><span style="color:#aaa">この先に出てくる送金先は、ご依頼の資金が届いたものとは断定できません。
        ただし<strong>経路が記録として存在することは事実</strong>なので、伏せずに記載しています。</span>
      </div>` : '';
      const poolTd = p.pooled ? `<div class="node-note" style="color:#fbbf24">
        ⚠ ここで<strong>他の資金と合流</strong>しています。${poolMany ? `この直後、資金は<strong>${p.poolDests}箇所</strong>に分かれています。` : ''}
        ${poolMany && p.poolShare != null ? `そのうち最も多い送金先が<strong>${Math.round(p.poolShare * 100)}%</strong>で、この先はそれを追っています。` : ''}
        <br><span style="color:#aaa">複数の資金がまとまるため、ここから先は同じ資金と言い切れません。${poolMany ? '他の送金先は後述の「参考経路」に記載しています。' : ''}</span>
        <br><span style="color:#aaa"><strong>ただし、この先で到達した取引所は伏せずに記載しています。</strong>
        経路が記録として存在することは事実であり、照会の価値があるためです。
        確度の但し書きとあわせて、警察・弁護士にお伝えください。</span>
      </div>` : '';

      return `
        <div class="flow-node ${cls}${p.afterStop ? ' after-stop' : ''}">
          <div class="node-role"><span class="node-icon">${icon}</span>${roleLabel}${exBadge}</div>
          <div class="node-address">${p.address}</div>
          ${balTd}${txCntTd}${timeTd}${amtTd}${svcTd}${poolTd}${dilTd}${brTd}
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
      /* 「見つかりません」で終わらせない。送金から日が浅いなら
         まだ移動中の可能性が高く、数日後の再調査という次の行動がある。 */
      exHTML = `<p class="no-ex">送金先は既知の取引所DBに一致しませんでした。${lastLabelHtml}</p>`
        + (r.stillMoving ? `<div class="note-box" style="margin-top:12px">
            <p style="margin:0"><strong>⏳ まだ資金が動いている最中かもしれません。</strong></p>
            <p style="margin:6px 0 0">${escHtml(stillMovingText(r.stillMoving))}</p>
          </div>` : '');
    }
    let tplHTML = '';
    if (r.exchanges && r.exchanges.length > 0) {
      const ex      = r.exchanges[0];
      const contact = getExchangeContact(ex.name);

      exHTML = `
        ${exProvenanceHTML(ex)}
        <table class="info-table">
          <tr><th>取引所名</th><td>${ex.name || '特定済み'}</td></tr>
          <tr><th>着金アドレス</th><td class="mono">${ex.address}</td></tr>
          <tr><th>着金額</th><td>${(ex.amount != null && !isNaN(ex.amount)) ? ex.amount.toFixed(8) : '不明'} ${ex.chain || r.chain}</td></tr>
        </table>
        ${exOthersHTML(r.exchanges)}
        ${contact ? `
        <h4 style="margin:18px 0 10px">📞 取引所連絡先・対応窓口</h4>
        <table class="info-table">
          <tr><th>公式サイト</th><td><a href="${contact.url}">${contact.url}</a></td></tr>
          ${contact.email ? `<tr><th>サポートメール</th><td>${contact.email}</td></tr>` : ''}
          <tr><th>サポートURL</th><td><a href="${contact.support}">${contact.support}</a></td></tr>
          ${contact.leo ? `<tr><th>法執行機関窓口</th><td><a href="${contact.leo}">${contact.leo}</a></td></tr>` : ''}
          ${contact.note ? `<tr><th>対応メモ</th><td>${contact.note}</td></tr>` : ''}
        </table>` : `
        <h4 style="margin:18px 0 10px">📞 連絡先の調べ方</h4>
        <div class="note-box">
          <p style="margin:0 0 8px">この事業者の窓口情報は当社に登録がありません。以下の順で確認できます。</p>
          <ol style="margin:0 0 8px 18px;padding:0">
            <li>公式サイトを検索し、<strong>Support / Help</strong> から不正利用の申告フォームを探す</li>
            <li>フッターの <strong>Law Enforcement / Compliance</strong>（法執行機関向け窓口）を探す。
                こちらがあれば、警察経由の照会が最も通りやすい</li>
            <li>見つからない場合は <strong>support@ / compliance@ +ドメイン</strong> 宛に、下記のテンプレートを送る</li>
          </ol>
          <p style="margin:0;font-size:0.85em">※ 海外の事業者は日本の警察の照会に応じる義務がありません。
          対応するかどうかは事業者の判断になります。</p>
        </div>`}`;

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

    /* USDT（Tether発行）なら、発行体への凍結要請窓口を併記する。
       Tetherは自社発行のトークンを、取引所を介さずアドレス単位で凍結できるため、
       取引所を特定できなかった場合に残る数少ない実効的な要請先になる。
       最初の送金が別の通貨でも、途中でUSDTにスワップされていれば今の資金はUSDTなので対象。 */
    let tetherHTML = '';
    const usdtRe    = /usdt|tether/i;
    const usdtFirst = usdtRe.test(r.tokenSymbol || '');
    const usdtNode  = (r.path || []).find(p => usdtRe.test(p.token || '') || usdtRe.test(p.swapTo || ''));
    if (usdtFirst || usdtNode) {
      const exFound = !!(r.exchanges && r.exchanges.length);
      const holder  = lastPathNode?.address || '';
      tetherHTML = `
        <h3>🪙 Tether社（USDT発行体）への凍結要請</h3>
        <div style="background:rgba(5,150,105,.08);border:1px solid rgba(5,150,105,.3);border-radius:8px;padding:14px 16px">
          <p style="margin:0 0 10px">本件の資金は <strong>USDT（Tether社発行）</strong>です${usdtFirst ? '' : '（経路の途中でUSDTに交換されています）'}。
          Tether社は自社発行のUSDTを<strong>アドレス単位で凍結する権限</strong>を持ちます。
          ${exFound
            ? '到達先取引所への要請に加え、<strong>発行体（Tether社）への凍結要請も有効</strong>です。'
            : '<strong>取引所を特定できていない場合でも、Tether社であれば資金が置かれているアドレスを直接凍結できます。</strong>本件では、こちらへの要請が有力な選択肢になります。'}</p>
          <table class="info-table">
            ${holder ? `<tr><th>凍結を求めるアドレス</th><td class="mono">${holder}</td></tr>` : ''}
            <tr><th>法執行機関向け窓口</th><td><a href="https://tether.to/en/legal/?tab=law-enforcement-requests">https://tether.to/en/legal/?tab=law-enforcement-requests</a></td></tr>
            <tr><th>連絡先メール</th><td>inforequests@tether.to</td></tr>
          </table>
          <p style="font-size:0.85em;color:#94a3b8;margin:10px 0 0">※ 通常、Tether社への要請は警察・弁護士等の法執行機関を通じて行います。本資料を添えてご相談ください。
          凍結の可否はTether社の判断であり、応じる義務はありません。また、凍結できるのは<strong>そのアドレスに残っている分だけ</strong>で、既に移動・換金された分は対象になりません。</p>
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

        <h3>🔗 資金経路</h3>
        <p style="font-size:0.82rem;color:var(--r-ink2);margin:0 0 8px">調査により、下記のとおり資金が移動していました。</p>
        <table class="info-table route-table">${routeRows}</table>

        ${isStable ? `<h3>📈 送金額の評価</h3>
        <p style="font-size:0.86rem;margin:0 0 8px">${escHtml(String(r.tokenSymbol))} は米ドルに連動する通貨（ステーブルコイン）のため、
        価格の推移は掲載しません。送金額 <strong>${r.tokenAmount != null ? r.tokenAmount.toLocaleString() : ""} ${escHtml(String(r.tokenSymbol))}</strong> が、
        そのままドル建ての金額に相当します。${r.amountUSD ? `送金時点の評価額は <strong>約 $${Number(r.amountUSD).toLocaleString(undefined,{maximumFractionDigits:2})}</strong> です。` : ""}</p>` : `
        <h3>📈 ${r.chain}価格推移（送金前後30日）</h3>
        <div class="chart-wrap">
          <p class="tx-price-label"></p>
          <canvas id="priceChart${idx}" data-coin="${coinId}" data-time="${blockTimeMs}"></canvas>
        </div>`}

        <h3>📍 送金経路詳細</h3>
        <div class="flow-map">${flowNodes}</div>
        ${traceCaveatHTML(r.path)}
        ${(() => {
          /* ブリッジで止まった場合は、事情が違うので別に書く。
             資金が消えたのではなく、別のチェーンへ渡っている。
             そしてブリッジ運営者は、取引所と同じく記録を持つ照会先になる。
             「他のツールで調べてください」では被害者の助けにならない。 */
          /* ★渡り先が読めた場合は、こちらを出す。「追えません」ではない。 */
          const cb = (r.path || []).find(p => p.bridgeTo);
          if (cb) {
            const t = cb.bridgeTo, hops = cb.crossChainHops || [], ex = cb.crossChainExchange;
            return `<p class="flow-note" style="border-left:3px solid #10b981;padding-left:10px">
        <strong>■ 別のチェーンへ渡った先が判明しました。</strong><br>
        <strong>${escHtml(cb.label || 'このコントラクト')}</strong>（${escHtml(t.bridge)}）から
        <strong>${escHtml(t.chainName)}</strong> へ渡っています。<br>
        渡った先のアドレス：<strong class="mono">${escHtml(t.address)}</strong>
        ${t.amount != null ? `／ 渡した額：<strong>${escHtml(String(t.amount).slice(0, 12))} ETH</strong>` : ''}
        ${t.arrivedAmount != null ? `<br>届いた額：<strong>${escHtml(String(t.arrivedAmount).slice(0, 14))} ${escHtml(t.arrivedToken || '')}</strong>
        <span style="font-size:0.9em">（ブリッジは通貨を換えて払い出すため、送った額と数字が変わります）</span>` : ''}
        ${hops.length ? `<br><br><strong>${escHtml(t.chainName)} 側で ${hops.length} 段階たどりました。</strong><br>
        ${hops.map((h, i) => `${i + 1}. <span class="mono">${escHtml(h.address)}</span>`
            + `${h.label ? ' ' + escHtml(h.label) : ''}`
            + `${h.amount != null ? ' ' + escHtml(String(h.amount).slice(0, 10)) + (h.token ? ' ' + escHtml(h.token) : '') : ''}`
            + `${h.isExchange ? ' 🏦' : ''}`).join('<br>')}` : ''}
        ${ex ? `<br><br><strong>🏦 到達した取引所：${escHtml(ex.name)}</strong><br>
        <span class="mono">${escHtml(ex.address)}</span>` : ''}
        ${cb.crossChainSpread ? `<br><br><strong>■ この先は、多数の宛先へ分かれています。</strong><br>        たどった各地点で <strong>${cb.crossChainSpread.join('箇所・')}箇所</strong> へ分散しており、        扱われている金額も被害額を大きく上回ります。        <strong>個人の財布ではなく、資金をまとめて動かす仕組みの特徴です。</strong><br>        ここから先を1本に絞って着金先を断定することはできません。        <strong>この分散の規模そのものが、組織的な資金移動を示す資料になります。</strong>` : ''}
        <br><br><span style="font-size:0.9em">※ 渡り先は、ブリッジへの送金に含まれる指定内容から復元しています。
        ${ex ? '' : `${escHtml(t.chainName)} 側の追跡はここまでです。`}</span>
        </p>`;
          }
          const b = (r.path || []).find(p => p.traceStop && (p.isVia || isViaService(p.label)));
          if (!b) return '';
          return `<p class="flow-note" style="border-left:3px solid var(--r-accent);padding-left:10px">
        <strong>■ この地点で、資金は別のチェーンへ渡った可能性があります。</strong><br>
        <strong>${escHtml(b.label || 'このコントラクト')}</strong> は、チェーンをまたいで資産を移す仕組み（ブリッジ）です。
        ブリッジは自社の資金プールから移転先チェーンへ払い出すため、
        <strong>ブロックチェーン上に移転元と移転先を結ぶ記録が残りません。</strong>
        公開情報だけでは、この先を追うことができません。<br><br>
        <strong>ただし、資金が消えたわけではありません。</strong>
        ブリッジの運営者は「いつ・どのチェーンの・どのアドレスへ払い出したか」の記録を保持しています。
        <strong>取引所と同じく、警察・弁護士を通じた照会の対象になります。</strong>
        本資料の該当箇所（送金日時・数量・当該コントラクトのアドレス）を添えてご相談ください。<br>
        <span style="font-size:0.9em">※ 移転先のアドレスが判明した場合は、そのアドレスから改めて調査すると、その先を追跡できます。</span>
        </p>`;
        })()}
        ${(r.path || []).some(p => p.traceStop && !p.isVia && !isViaService(p.label)) ? `<p class="flow-note" style="border-left:3px solid var(--r-accent);padding-left:10px">
        <strong>■ この地点から先は、同一の資金と特定できないため追跡を終了しています。</strong><br>
        交換（DEX）や橋渡し（ブリッジ）のコントラクトには、多数の利用者の資金がまとめて集まり、
        同時に多くの送金が出ていきます。そのため「次に出ていった送金」をたどっても、
        それがご依頼の資金である保証はありません。<strong>根拠のない到達先をご提示しないため、
        当社ではこの地点で追跡を打ち切っています。</strong><br>
        続きをお調べになる場合は、次のいずれかが必要です。<br>
        ・この地点の取引を個別に精査する追加調査（同一取引内での資金の出口を特定する作業）<br>
        ・資金が別のチェーンへ移動している場合は、移動先のチェーンでの調査<br>
        なお、ここまでの経路（この地点に資金が入ったこと）は、ブロックチェーン上の記録として確認できています。</p>` : ''}
        ${(() => {
          // 送金先アドレスの素性。不正事案の報告があれば最優先で示す
          const pn = (r.path || []).find(p => p && p.profile);
          if (!pn) return '';
          const pf = pn.profile;
          const 一覧 = (title, obj, keys) => {
            const rows = keys.filter(k => (obj[k[0]] || []).length)
              .map(k => `<tr><th style="width:9em">${k[1]}</th><td>${obj[k[0]].map(escHtml).join('、')}</td></tr>`).join('');
            return rows ? `<p class="ref-p" style="margin-top:12px"><strong>${title}</strong></p><table class="info-table">${rows}</table>` : '';
          };
          const 不正 = pf.malicious.length ? `
            <div style="background:rgba(248,113,113,.10);border:1px solid rgba(248,113,113,.45);border-radius:8px;padding:12px 14px;margin:10px 0">
              <p style="margin:0 0 8px"><strong>このアドレスは、不正事案に関与したものとして外部の解析事業者に報告されています。</strong></p>
              <table class="info-table">
                <tr><th style="width:16em">報告されている種別</th><th>件数</th><th>事案名</th></tr>
                ${pf.malicious.map(m => `<tr><td>${escHtml(m.種別)}</td><td>${m.件数}件</td><td>${(m.事例 || []).map(escHtml).join('、') || '—'}</td></tr>`).join('')}
              </table>
            </div>` : `<p class="ref-p">当社が参照した範囲では、<strong>不正事案としての報告は確認されませんでした</strong>
              （報告が無いことは、安全であることを意味しません）。</p>`;
          return `<div class="ref-box">
            <div class="ref-h">送金先アドレスの属性情報</div>
            <p class="ref-p">お客様が最初に送金されたアドレス（<span class="mono">${escHtml(pn.address || '')}</span>）について、
            外部の解析事業者が保有する情報を照会した結果です。</p>
            ${不正}
            ${pf.firstAddress ? `<p class="ref-p">このアドレスの<strong>手数料（ガス代）の出所</strong>：<span class="mono">${escHtml(pf.firstAddress)}</span><br>
            <span style="font-size:0.9em;color:#aaa">新しく作られたウォレットは残高が無いため、送金するには誰かが手数料を送る必要があります。
            その送り主は、同じ人物の別のウォレットか、その人物が使った取引所である可能性があります。
            <strong>相手方の特定を進める際の手がかり</strong>になります。</span></p>` : ''}
            ${一覧('利用が確認されたサービス', pf.platforms, [['exchange','取引所'],['dex','DEX'],['mixer','匿名化サービス'],['nft','NFT']])}
            ${(() => {
              /* ★日本の登録業者との接点は、被害者にとって最も価値のある情報。
                 海外業者と違い、資金決済法・犯収法の対象で、捜査機関の照会に応じる。
                 数値や名前を並べるだけでは、被害者も警察もその意味に気づけない。 */
              const JP = ['coincheck', 'bitflyer', 'bitbank', 'gmo', 'sbi', 'bitpoint', 'dmm',
                          'zaif', 'bittrade', 'coinbest', 'decurret', 'okcoin', 'bitmax', 'liquid'];
              const list = [].concat(pf.platforms.exchange || []);
              const hit = [...new Set(list.filter(n => JP.some(k => String(n).toLowerCase().includes(k))))];
              if (!hit.length) return '';
              return `<div style="background:rgba(5,150,105,.10);border:1px solid rgba(5,150,105,.35);border-radius:8px;padding:12px 14px;margin:10px 0">
                <p style="margin:0"><strong>■ 日本の登録業者との接点が確認されています：${escHtml(hit.join('、'))}</strong></p>
                <p style="margin:8px 0 0;font-size:0.92em">これは<strong>本件で最も重要な手がかりの一つ</strong>です。
                日本の暗号資産交換業者は金融庁の登録を受けており、<strong>資金決済法・犯罪収益移転防止法にもとづく本人確認記録と取引記録の保存義務</strong>があります。
                海外の業者と異なり、<strong>捜査機関からの照会に応じる体制が国内にあります</strong>。<br>
                警察へのご相談・弁護士へのご依頼の際は、<strong>この事実を必ずお伝えください。</strong>
                相手方の本人確認情報にたどり着ける可能性が、海外業者のみの場合と比べて大きく変わります。</p>
                <p style="margin:8px 0 0;font-size:0.85em;color:#aaa">※ 接点があるという記録であり、当該業者に現在も資金があることを意味するものではありません。
                また、当該業者に落ち度があることを示すものでもありません。</p>
              </div>`;
            })()}
            ${一覧('このアドレスに紐づく情報', pf.relation, [['ens','ENS名'],['twitter','X（Twitter）'],['wallet','関連ウォレット']])}
            <p class="ref-warn"><strong>この情報の扱いについて</strong><br>
            上記は外部事業者に蓄積された報告・関連付けであり、<strong>当社が独自に事実関係を確認したものではありません</strong>。
            相手方の特定や法的な主張の根拠とされる場合は、必ず捜査機関を通じて確認してください。
            ${(pf.relation.ens || []).length || (pf.relation.twitter || []).length ? 'ENS名やSNSアカウントは、捜査機関が発信者情報開示を検討する際の手がかりになり得ます。' : ''}</p>
          </div>`;
        })()}
        ${(() => {
          /* 「現金化されたか」と「今も残っているか」。
             被害者が最も知りたい2点。凍結要請を出す意味があるかの判断材料になる。 */
          const an = (r.path || []).find(p => p && (p.action || p.overview));
          if (!an) return '';
          const ac = an.action || {}, ov = an.overview || {};
          const rows = [];
          if (ov.残高      != null) rows.push(['現在の残高', `${ov.残高} ${escHtml(r.chain || '')}`]);
          if (ov.累計受取  != null) rows.push(['これまでに受け取った合計', `${ov.累計受取} ${escHtml(r.chain || '')}`]);
          if (ov.累計送金  != null) rows.push(['これまでに送り出した合計', `${ov.累計送金} ${escHtml(r.chain || '')}`]);
          if (ov.取引回数  != null) rows.push(['取引回数', `${ov.取引回数} 回`]);
          if (ac.入金額    != null) rows.push(['取引所等への入金額', String(ac.入金額)]);
          if (ac.出金額    != null) rows.push(['取引所等からの出金額', String(ac.出金額)]);
          if (Array.isArray(ac.利用先) && ac.利用先.length) rows.push(['利用が確認されたサービス', escHtml(ac.利用先.join('、'))]);
          const 活動 = ov.最後の活動 || ac.最後の活動;
          /* 応答は UNIX秒・ミリ秒・文字列のいずれでも来る。
             そのまま出すと「1758921743」と表示され、利用者には読めない。 */
          if (活動) rows.push(['最後に動いた日時', escHtml(fmtUnixOrText(活動))]);
          if (!rows.length) return '';
          const 残っている = ov.残高 != null && ov.残高 > 0;
          return `<div class="ref-box">
            <div class="ref-h">送金先アドレスの状況（資金は動かされたか）</div>
            <p class="ref-p">お客様が最初に送金されたアドレス（<span class="mono">${escHtml(an.address || '')}</span>）の
            現在の状況です。<strong>資金がまだ残っているかどうかは、凍結を要請する意味があるかの判断材料になります。</strong></p>
            <table class="info-table">
              ${rows.map(([k, v]) => `<tr><th style="width:44%">${k}</th><td>${v}</td></tr>`).join('')}
            </table>
            <p class="ref-p" style="margin-top:10px">${残っている
              ? '<strong>このアドレスには残高が残っています。</strong>本資料の要請テンプレートを使い、<strong>取引所への凍結要請をお送りください。</strong>'
              : '<strong>このアドレスの残高はほぼ残っていません。</strong>資金は既に別のアドレスへ移されたか、換金された可能性があります。ただし移動先の追跡は本資料の経路に記載しています。'}</p>
            <p class="ref-warn">これらは外部の解析事業者が公開情報から集計した数値です。
            取引所の内部記録とは一致しない場合があります。</p>
          </div>`;
        })()}

        ${(() => {
          /* AMLリスクスコア。数値だけを大きく出すと独り歩きするので、
             必ず「何がスコアの理由か」と「何を意味しないか」を添える。 */
          const rn = (r.path || []).find(p => p && p.risk);
          if (!rn) return '';
          const rk = rn.risk;
          const 高 = rk.score >= 60;
          const 色 = 高 ? '248,113,113' : (rk.score >= 30 ? '251,191,36' : '110,231,183');
          return `<div class="ref-box">
            <div class="ref-h">送金先アドレスのリスク評価（AMLスコア）</div>
            <p class="ref-p">お客様が最初に送金されたアドレス（<span class="mono">${escHtml(rn.address || '')}</span>）が、
            不正な資金とどの程度近いかを外部の解析事業者が評価した数値です。</p>
            <div style="background:rgba(${色},.10);border:1px solid rgba(${色},.45);border-radius:8px;padding:12px 14px;margin:10px 0">
              <p style="margin:0"><strong style="font-size:15px">${rk.score} / 100</strong>
              ${rk.levelJa ? `（リスク水準：<strong>${escHtml(rk.levelJa)}</strong>）` : ''}</p>
              ${rk.details.length ? `<ul style="margin:8px 0 0;padding-left:1.2em">
                ${rk.details.map(d => `<li>${escHtml(d)}</li>`).join('')}
              </ul>` : ''}
            </div>
            ${rk.hacking ? `<p class="ref-p">関連が指摘されている事案：<strong>${escHtml(rk.hacking)}</strong></p>` : ''}
            ${rk.exposures.length ? `<p class="ref-p" style="margin-top:12px"><strong>スコアの根拠となった資金のつながり</strong></p>
            <table class="info-table">
              <tr><th>相手</th><th>種別</th><th>経路</th><th style="text-align:right">割合</th></tr>
              ${rk.exposures.map(e => `<tr><td>${escHtml(e.相手)}</td><td>${escHtml(e.種別)}</td>
                <td>${escHtml(e.経路)}（${e.ホップ}ホップ先）</td>
                <td style="text-align:right">${e.割合 >= 0.1 ? e.割合.toFixed(1) : '&lt;0.1'}%</td></tr>`).join('')}
            </table>` : ''}
            <p class="ref-warn"><strong>この数値の扱いについて</strong><br>
            スコアは<strong>このアドレスに出入りした資金全体</strong>をもとに算出されており、
            お客様の資金がそのまま不正な資金になったことを示すものではありません。
            また、スコアが低いことは<strong>安全であることを意味しません</strong>
            （新しく作られたアドレスは、記録が無いため低く出ます）。
            相手方の特定や法的な主張の根拠とされる場合は、必ず捜査機関を通じて確認してください。</p>
          </div>`;
        })()}
        ${(() => {
          // 取引先分析で着金先を推定した場合、その内訳を根拠として示す
          const cn = (r.path || []).find(p => Array.isArray(p.counterparty) && p.counterparty.length);
          if (!cn) return '';
          const rows = cn.counterparty.map(c => `<tr><td>${escHtml(c.name)}</td><td style="text-align:right">${c.percent >= 0.1 ? c.percent.toFixed(1) : '&lt;0.1'}%</td></tr>`).join('');
          return `<div class="ref-box">
            <div class="ref-h">参考情報：着金先アドレスの取引先分析</div>
            <p class="ref-p">取引所は利用者ごとに入金用のアドレスを発行するため、そのアドレス自体には
            取引所名が登録されていないことがあります。そこで、着金先アドレス
            （<span class="mono">${escHtml(cn.address || '')}</span>）が
            <strong>実際にやり取りしている相手の割合</strong>を示します。${cn.cpInferred ? 'この結果から、着金先を <strong>' + escHtml(String(cn.label || '')) + '</strong> と推定しています。' : ''}</p>
            <table class="info-table">
              <tr><th>取引先</th><th style="width:6em;text-align:right">割合</th></tr>
              ${rows}
            </table>
            <p class="ref-warn"><strong>この推定は確定ではありません。</strong>取引先の割合は入出金の両方を含み、
            第三者を経由した取引も含まれます。凍結のご要請にあたっては、必ず捜査機関を通じて
            当該取引所へ確認してください。</p></div>`;
        })()}
        ${(() => {
          const sn = (r.path || []).find(p => p.traceStop && p.candidatesChecked);
          if (!sn) return '';
          if (!(sn.nextCandidates || []).length) {
            return `<div class="ref-box"><div class="ref-h">参考情報（未確定）：この先の追跡</div>
              <p class="ref-p">上記の地点から<strong>次に出ていった送金${sn.candidatesChecked}件</strong>について、
              さらに追跡を行いました。
              <strong>いずれも取引所には到達しませんでした</strong>（当社が追跡できた範囲内での結果です）。
              これらの送金がご依頼の資金である保証はないため、到達先としての記載は行いません。</p></div>`;
          }
          /* 日時差は分で書くと桁が大きくなって離れ具合を掴めない。
             時間・日に繰り上げる。1時間を超えたら色を変えるが、除外はしない。
             犯人が資金を寝かせてから動かす例があるため、間があく＝無関係ではない。 */
          const fmtGap = min =>
            min < 60        ? `+${min}分`
          : min < 60 * 24   ? `+${Math.floor(min / 60)}時間${min % 60 ? (min % 60) + '分' : ''}`
          :                   `+${Math.floor(min / 1440)}日${Math.floor((min % 1440) / 60) ? Math.floor((min % 1440) / 60) + '時間' : ''}`;
          const 離れている = sn.nextCandidates.some(c => c.gapMin > CANDIDATE_WARN_GAP_MIN);
          return `<div class="ref-box">
            <div class="ref-h">参考情報（未確定）：この先で取引所に着いた送金</div>
            <p class="ref-p">上記の地点から<strong>次に出ていった送金${sn.candidatesChecked}件</strong>をさらに追跡し、
            <strong>取引所に到達したものだけ</strong>を記載しています
            （${sn.candidatesChecked}件のうち${sn.nextCandidates.length}件）。
            多数の利用者の資金が集まる地点であるため、
            <strong>これらがご依頼の資金である保証はありません</strong>。
            状況を判断する材料としてのみご覧ください。</p>
            <table class="info-table">
              <tr><th style="width:5.5em">日時差</th><th>この地点から出た送金先</th><th>到達した取引所（未確定）</th></tr>
              ${sn.nextCandidates.map(c => `<tr>
                <td${c.gapMin > 60 ? ' style="color:#fbbf24;font-weight:700"' : ''}>${fmtGap(c.gapMin)}</td>
                <td><span class="mono">${escHtml(c.address)}</span>${c.label ? `<br><b>${escHtml(c.label)}</b>` : ''}
                    <br><span style="font-size:0.78rem;color:var(--r-ink2)">${c.amount ? c.amount.toFixed(6) : '—'} ${escHtml(r.chain)}</span></td>
                <td><b>${escHtml(c.reachedExchange || '')}</b>
                    <br><span class="mono" style="font-size:0.72rem">${escHtml(c.reachedAddress || '')}</span>
                    <br><span style="font-size:0.78rem;color:var(--r-ink2)">${c.reachedHops}回の送金を経て到達</span></td></tr>`).join('')}
            </table>
            ${離れている ? `<p class="ref-p" style="margin-top:8px;font-size:0.85em;color:#fbbf24">
            ⚠ <strong style="color:#fbbf24">色の付いた日時差</strong>は、資金が入ってから1時間以上あいて出ていった送金です。
            間があくほど、ご依頼の資金とは別の資金である可能性は上がります。
            ただし、<strong style="color:#fbbf24">資金をしばらく置いてから動かす手口は珍しくありません</strong>。
            間があいていること自体が、無関係であることを意味するものではありません。</p>` : ''}
            <p class="ref-warn"><strong>法執行機関・取引所へご相談の際のお願い</strong><br>
            この欄は<strong>確定した到達先ではありません</strong>。凍結の要請や被害届で「資金の到達先」として
            提示すると、<strong>無関係な方の口座を対象にしてしまう恐れ</strong>があります。
            ご相談の際は、この部分が未確定であることを十分にご理解のうえ、
            必要に応じて「参考情報」として区別してお伝えください。</p>
          </div>`;
        })()}
        ${(r.path || []).some(p => p.isDeposit) ? `<p class="flow-note">※ <strong>🏧 入金用アドレス</strong>＝取引所が利用者ごとに割り当てる受け取り専用のアドレスと推定されます
        （受け取った資金をまとめて取引所のウォレットへ移す形が見られるため）。ここに着金している場合、
        <strong>その取引所が口座名義人の情報を保有している可能性</strong>があります。ただし名義人が誰であるかを当社が特定することはできません。</p>` : ''}
        ${(r.path || []).some(p => p.isVia || p.isToken) ? `<p class="flow-note">※ <strong>🔀 経由</strong>＝DEX・ブリッジ・両替サービスです。資金の通り道であって着金先ではないため、
        凍結の要請先にはなりません。ブリッジを通っている場合、資金は<strong>別のチェーンへ移動している可能性</strong>があります。
        <strong>🔁 スワップ／トークン</strong>＝そこで別の通貨（USDT等）に交換された地点です。</p>` : ''}
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
    /* 表紙。1ページを使い切る */
    .page{margin-bottom:28px}
    .cover-page{background:var(--r-coverbg);color:var(--r-coverink);border:1px solid var(--r-border);
      border-radius:12px;padding:56px 32px;text-align:center}
    /* ロゴは絵の中で文字が左寄りに描かれている。枠で切り取り、少し縮めて右へ寄せ、
       文字が中央に見えるようにする。 */
    .cover-logo-box{width:132px;height:132px;border-radius:24px;margin:0 auto 18px;overflow:hidden;background:#0E2038}
    .cover-logo{width:100%;height:100%;display:block;transform:scale(.86) translateX(17px)}
    .cover-brand{font-size:1.6rem;font-weight:800;letter-spacing:2px;color:var(--r-accent);margin-bottom:26px}
    .cover-title{font-size:1.5rem;margin:0 0 6px;letter-spacing:2px}
    .cover-sub{font-size:0.85rem;color:var(--r-coversub);margin-bottom:38px}
    .cover-client{font-size:1.25rem;font-weight:700;margin-bottom:40px}
    .cover-info{width:auto;min-width:60%;margin:0 auto;font-size:0.85rem}
    .doc-h{font-size:1.05rem;margin:0 0 10px;padding-bottom:6px;border-bottom:2px solid var(--r-accent)}
    .doc-h3{font-size:0.95rem;margin:22px 0 8px}
    .doc-p{font-size:0.88rem;line-height:1.9;margin-bottom:22px}
    .doc-ol{margin:0 0 22px 20px;padding:0;font-size:0.88rem;line-height:1.9}
    .doc-ol li{margin-bottom:6px}
    .doc-note{font-size:0.8rem;color:var(--r-ink2);line-height:1.8;margin-top:12px}
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
    /* 確度が下がる区間。消さずに、点線で区別する */
    .flow-node.after-stop{border-style:dashed;opacity:.72}
    .caveat-box{margin:12px 0 4px;padding:12px 14px;border-radius:8px;font-size:0.86em;line-height:1.85;
                background:rgba(125,180,255,.07);border:1px solid rgba(125,180,255,.26)}
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
    .node-note{font-size:0.76rem;color:var(--r-ink2);margin-top:6px;padding:6px 8px;border-radius:6px;
      background:var(--r-softbg);border:1px solid var(--r-line);line-height:1.7}
    .usd-val{color:var(--r-usd);font-size:0.76rem;font-weight:600}
    .badge{background:var(--r-badgebg);color:var(--r-badgeink);font-size:0.72rem;padding:2px 8px;border-radius:10px;margin-left:6px;font-weight:400}
    .flow-arrow{font-size:1.4rem;color:var(--r-ink2);margin:4px 0;line-height:1}
    .no-ex{color:var(--r-ink2);font-size:0.85rem;padding:10px}
    .note-box{background:var(--r-softbg);border:1px solid var(--r-border);border-radius:8px;padding:12px 14px;font-size:0.85rem;line-height:1.8;color:var(--r-ink2)}
    .ref-box{border:1px dashed var(--r-border);border-radius:8px;padding:14px;margin:14px 0;background:var(--r-softbg)}
    .ref-h{font-size:0.9rem;font-weight:700;color:var(--r-ink);margin-bottom:8px}
    .ref-p{font-size:0.82rem;color:var(--r-ink2);line-height:1.8;margin-bottom:10px}
    .ref-warn{font-size:0.8rem;line-height:1.8;margin-top:10px;padding:10px 12px;border-radius:6px;
      background:rgba(248,113,113,.10);border:1px solid rgba(248,113,113,.45);color:var(--r-ink2)}
    .ref-warn strong{color:#F87171}
    .note-box strong{color:var(--r-ink)}
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
    .route-table th{white-space:nowrap;width:6.5em;font-weight:700}
    .route-table td{word-break:break-all}
    .route-table .route-tx td{background:var(--r-softbg);font-size:0.78rem;color:var(--r-ink2);padding:5px 8px}
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
      .page{break-after:page;page-break-after:always;margin-bottom:0}
      .cover-page{border-radius:0;min-height:88vh;display:flex;flex-direction:column;justify-content:center}
      /* 経路のノード・表・テンプレートがページの境目で割れないようにする */
      .flow-node, .flow-arrow, .info-table tr, .template-box, .chart-wrap,
      .ai-box, .note-box, .flow-hint { break-inside: avoid; page-break-inside: avoid; }
      h3 { break-after: avoid; page-break-after: avoid; }
    }
    /* 画面でもノードの途中で改ページされないようにしておく（PDFはこの指定も見る） */
    .flow-node{break-inside:avoid;page-break-inside:avoid}
    .info-table{break-inside:auto}
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

  <div class="cover-page page">
    <div class="cover-logo-box"><img class="cover-logo" src="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAIAAAACACAIAAABMXPacAAA/t0lEQVR42s29abBl13Uetr69z7nTu+/1PHejMYMEQYAkSIogSIAUI1mSTdJyxSxbdsmSLJWVxIlFxSXJVR5UiR2Vy1HZkUp2LNtlOYpoR7Is0RQp0aJEUuZMgQQIEA0SjR7Q6Hl60313OGfvLz/OOXuvfc5tlX8kVW6ATfTr9+49dw9r+Na3vgU5/B4RilBERCAiIhQABIWAUFB9VepvIgiBkBQRQITC+ser1zAiIuUMNhscfaR/5OFy/fL0wrN+vi0wrF8GUv0wCRGBkNUfBaBUb+yKbPfhwfHHt1/4hKD6B6yfMLyvelsIWb2GwDvTXxnf8x39/XfvnP/q9rmvC530hiBESNGv0fyh+l/zaKweKH4H1XPH92T4weqbqpUTov6cECGSxWX9RQohIpKFtydFQAiaFWf1f1APCSEJ/RRk/ZEl7JRbCNk/cO/wxFu8Kycvf65YvyjGCoxIfP16L4HwqRA/Q70UUu1K9XQQQD0LJaxY+Eo8KLBuMdk49Qf9fSdX73nr6PDrNs98ZXbtZYpB3q92vXPoWnsASHz18J1hcdSuNJ+hWtrmXMTf0j2rvxGsXjCrDh/V54Go55L0D6w3QfQW1Ofe0JdSFvmeYyv3vF2ywfTCN+ZXvy30yHqsvxHVEY3PiO4LhS2JHxLVNlTnS51gsvmG8HSsz40gk0zm188sbp4bHX90fP+7RyfetH3mS4ub58XmkvURniKuXfVWTBcvnLD6UeoPIvGtKQIKGU589RJUByz+GNWSMt4ACBk+cX1H6g1FvO7V68XHEJHqtNKxKLLxvtHJt2arh2aXT00vvsByjqxfX2egWTyGu59YkepdSKnsW3hK79WtkGD1yOabAIjersqQNdczH4jI5MJzO5dPjY69cdfD311sXd8+84Vy84bkAxhTPVF9tQmitoVojIXUuxzMZbXLbD66Op7VvQHip0L90RuT1r4NQloZ3918DtQnNOy0CFC/qaAy/UBtuwQQGECExQy90ejut63c/Q43ubn9rc8sbp6FsbBZdBS1Sa1/Or1dQLjvzVmpFhmDVTs+UNx4BYByRdWS12ai/aEY3qA+uBSBzSm+uHl2dv1Mtnpw9b4n7MrucvMKZ9tiMhhDKscklX0Guka/ckWsl6lrXkRvS/yB6uuEsjJontHKatwAqJdF6pxaVqn6TpZzmGx47JGV+56kL7df/s+zK6eEgqzHxvnoFwUQ3ExjVxCemW1L6U1/bMf7y5vnABMeuvLGYQ20C6m3L+6PXlBB1qcrFtdOL25f6O87Ob77bbBZuXmVxUJs3jg8tXJ6nZrnJ7VTDB+jtQvxxdR21Kclbh4gIlbGdyO+SLhF0jlf8VsA0C2Ern/4oZX732V6452zX55deJZugawnwcsLw+MhcUDBo1U7Uvt17WEBI/SmNzTjg+XN8zD1QzEeq7DQ8Ziy8evNezZRE6VxIQZZzy925ldOlVvXhkcfHp94M+nKzSviS9hMeaDK49RGrbmkoh4jbE9Y5eC+wfQcxw2szUxcaYvKBFXWTmqDUxtoJPccEBgjvhRf9vYcX3ngqWz18OzCczvnvuIXE2R91F5R3cbgJFoPVEcBwe03hzSJCL3pjczKAXf7fPCD1TqgCY30pWY8ctBmWf1bmXmBMbC5m27Orrzki9n45OODIw/5+aTcui4CmEyFqiItWxRvbXx6FVa3rwRayxFcfPPkWQxQY3TSBMuN84eI1EHOPFs9NDzxmB3tnl16aXb5RfEl8n7tblTAtiROagV8jbFv/WTjcShCknRlFQlIZ62RxuPV41c7q25r9PqV32bjJ5D1BTK7fnp249zo6MOrDz09Ovmm7dNfLNYvS94XY0HPzrugCefUYkF/amWuiU4c2njvOsMSgcXq3dXnRdtLMzpnksXMDsYr935H/9ijxe2Lk9OfK9dfg8lgcwrbZjEc1cREEC1Hkrqy1AqJ0CMfmtFut3EJ8VyDaTjWxOLqcIbAFOmGJlaiOd1ZDpHi9quzKy9nK/tW73tHPt5fbF3jbKvyz21LgiYWSRxGHVvoRAXhmVIrHgKR6vNarN5NthY9GApAyHJmst7wrsdHJ9/qZtuT058rrp+BgdhcRZP69MbbGVeGMWRu1lKfF8aTWm8Vqg3AcLffuNTYHLDJhBBfN8QZ8TOr6DT8QLh2qe8kRYisL/Tza6dnN870958c3/cE8kG5cYXFHDaXxKa3DQzUDoj6ECocDo6LIRQJX7dYvSf5QkiXBOLmAhkcfcPo/idFZHL6i/PLL5Kuiu6VZUM0u2qtw5fBbrjGkO7qGIaidoaCfCC9MbeuVO6LKrTRUERqdFGFtcnxFLXtQLKSDHGCgc19OZtd+VaxcaV/6MHh8TcBLLauiithM9wp2GwlV2GxoWwSqtMMQSuwFCvjk2moawRG3EJY9g7cN37gKdNfnZ7/6uzCsyznyHoCE19C3R11oHRQqDJXatcsymMz7ESyDQBsD6bH6e0axqhPUXPeGL6io7TmTZF6DKoMAnX0pderPnowyPpuujm/fIqLneGJN4+OvI7FrNy8LkKYLNxrJPCF9vvNhUscCBG3oTmjgAjiBtShtS/EFfne4ysPvDtbOzq/9PzOua/42Rbyfkx/61CJ6vAixnqdyKE5c2zbTL3i6c8CoHdicwx3cXKjtq7Q4Q0l+oEaiNN+Pi6sDl3Cj+jMtFnNakVIVllkuX19dvmUiFm7/4nBoXvL7ZtuckuMgbFooDq0oRsCaUKjcwK9W41BrPKACsL04ubZyp6V+9/VP/y6xbUzO6c/57avI+uLsaKSxer4KABQFDCR/M7UAqGTNSJY/NRZkYQxWDuO/h4ppzLfgMl1FNUE6ES4d2THNXZTVUgHI4vBJMJrkCJichhbrL82vfySHe5afeipfO1QsXHZz7bEZjCmgWmkfQOlHfXFfKW6APWbVN995D1Cz2JmR7uGdz2e7T66uHZ6+trzLKaS9QUi3rccrXKlVeynt72NNCTONYEX0YqLmMBqHqt3SW+X+AVEOLnCxXaNk7GTlgecC4gWqRMNy5J1CRgZW7tTY1KoIigvxcyu7B3f+458z7H5lW9Pzn3VLyaSj6qEMcbJCTQu6nQpw4CIZ0LESv+gyXuDk28d3vN2P9uanP7c4torAiDLKzvTmBO2Us7mmDOki+EziYqOVBxWLR9TML4KYckkniKMld4uKXfEzcWXAoNiwhjstQGgkBwLCGEdVqfvjtY3a7Q/iU27DhXI+r6Yza+8tFi/Mjz04Oq93wGbFRtXWMwkywHTLJQ6glSxtbqbSYkBguFb/lrvwINuujm98HW3eUVsDpNVoT3ZMtBM0SlKrA2o5aN0gazGx6XAd2IEqP2viEhvTWBqzK/YYbFTAwJkZzuT4BDLLAEDfq2xkWTb0UamI16LWPRwhbiyd/D+1fueMDbbPvPV6eUXRUTyfkCka8sQA13foNLhw8e9t6OHv396/uuz819lMas8LRJjUPvbJXltq6RBdpK4O/85qXRQAfAqvHNF/bLljMVOvRlVoGKMgdjq/ytIVi/nUlsQfQ66xwepAUdSB2gQhOoJjYXtucmN6WvPsyxG97x9eOgBP5+4rRsiFJPFD+gX4hbiSzEGMCIeFBGDlr+Tg+8UimQ9CEOiLBGLEPGlYWFtRoHQk74xtujAa0wCHX1/4hIzBVsp7Si1gkxrR1ylxCIQGKGn0JVOFnMpS3EiMJJZyXPp9Wyeiaf3vrm6MflB+0KEd0UXxAxYRdvaRjNblye4mInNRsceHd/1pnL71tYrny82r0nWF6HQ9/Yctf2Rn28vNm7QFWKtsKnX6hgJh5/msqigeghjjVtf/+Efev9P/8SPTKdzU6fmRJJ1UqHD7Cx5rNOhkzWoy0idSkXkJCkViifns9nm5mR9Y/u1S9fPX7j47TMXTr187vxrl/3WjthcVkZZnvlqJ0TB3c1dIGLaSGV6QszKJJtJq75N8TDEk6SXcm7y4ejEm/rH3jC7dmZ67itie7sf+d7e/hNCR4qfb208+7HFrYvIh7q2TAGArIWRSFLVJADxcuTokYceuEf+a/21tTU5febCF7/y3Md///N/9KWvb1+7LcOBHQ5J732odC8vSdV19LTQzmZ9FMoawhEoXI0QSD6kd9uvfH7nykv9A/cOjr5xeOwNvX3H/WxLvCfEruzb85YP3vj8R9xipwGX4p20Mj4ZsYfoduubZ43x0+kTTzz2vqfevlgUFahIT+/J6t9lv7xv/sY3v4Xv9Okf43fRq++J3+STF/TVf3vvnPO+/qHhoH/k8P63Pf7IX/rz3/sXPvjdR48funjp8rXzFykm6+Vt7gQgojI4dFNaRtBbZ3eIZSt2gGlkPZaz8uopWIwfeLcUOwBgDIxhubCjPW62VVw/W9VLNB5hWshByxCRFNLAGGOsNcbAwJjqP6wxxhgD1G7RGFQ+0RgDC5jqn8pRht+NsVA/BhgYi/C0zb8WxlgDGAsD2OYFrTHWwlqT2Syz1lprYbz3ZVkWRVE6d++9x3/6wz/8zGf+7b/85//r6x44Xt68QU9rjQQSTZW4kDpyiKcuiVMi2BoDWibYbYDB6R1MJr0Vkw+ELkl5jaF4M9ol4uo3qUoTJEmjY2WqbY3UBNLTJRyApmYboscmY0g+SwNqMgbcdTpNNmBcK/9qAisw5NqxRKGwwlbCCxhjM2sN4JwvinI4GvzVH/z+r376//7f/sH/vJJbt7mZZaaKMgIlpYomdGDQjdkiRUch/gxlZ0ChaxWQQ19MjSANCilCFtO40tERVBkEfb0oNUyiNl4lc0l2wiQOZaw2UCdfaXpVf3/keKTPiIT7lS5NyPcqGygx+CKbb66uEZBl1ntfFOXKaPi3/uaPfuGT/+qdb39DefO2sRYioKuuNVJ+UXh3KpoFEdalttFIrkuAtIx4x/kk23XU7n/Qu9JkffGFkOKdCMSV86tnxPSYgpUhLI2nra6uoMm8WmEyqflkkDakvOyXJvIAKa+IsToZo6OuzRZ2chEm9CT1PdWlRGYtyaIoH33kwT/8xL/+az/+A259o7b/9HUJiWwdhDqLjuFqBSrXrB02iXurds9ibgerowffO7r/Sbd969azH3dlYfpjk+Um75ks3zz12eLWBWS9NL2qnPDoGGwW68TqY4FiDPzOzpPvfvy/ec87nPfGGEGbUtUuSMcaZwzsm2ySLZ6EPgvQm4R2Mt2CrIMnQ4fgpoIMWGOcc3mWvf97nxoOB7//iT+w/Z4Yg2bjm1KPBFYjm6OvbT402FM9XpUKlDNjs+Fdbx7e84Sbb09Pf67cvOh2NmeXT3G2TjGLG2c3X/zs7NKLyPIqi4w5NyAiWbZ6sNy8JiaDgXgyKTWzU5DT10Ua4D2QBVjj8CG2C6VlIFIk2OZZauCo+lmqClob5gpmR7PkNNM04TmKtdZ7+sL99E/+cD/Hh3/qH2V79jnva+CBKdUUKiwPxA5J8pEqrmW5gDGDo4/0Dz/sppvbL/4nt3VVsgGyIYVuZ2Prpc9mR9fd+kXONtEbkUSL2SQikGz1/nctNi5PX3vOz7aQ9dGY8qRKnjAym5QGOmNk5ZhjvSmwW9mQnKhwuLoaX/+FKiKyxdyqKzpoOIeKEYyEo0iVuwtqfm8EIa01i0XxE//jD21Oy7/3s/8027PqyoIhma9dc1V1a5hwzZawoStCQFDcQoS9/fesnHyb927n/DPFzXMCSG8F9PROIDAZ+2v9/Xcvynmx2BF11TQJjSJm85u/J74cP/id/WNvFBG6hQp1lZMKWVqghTTxCfWZZrDFCFdBdOQQnEJN9FN0E1L7k6bOQATDGAl/SdzUSq2ANtxUGb0ss2Xp/u5P/eif/9B3lTeuGWvSZF0AoWleg01xNphWA4oXt8jGe8cPvW9w4i3TSy9sPPfR4tZ5ZD2xeeOUWGfwvsxHaybrC700dKDu0xq3mE3Ofmnn7BftYPfovnfne+6mL+mKZtOMZuZKK8YEOhBawleqzmYgSAZ4KNK16k1lc4VSPm76stTsCiRGEQlfGW3mc0PlNID3/v/8+b919/3H/HRqrRUhxDcJLsXXyGB9g0JeQLKc295wePI7hve8s9y6vvXcx2YXXxAANg8lRgggRsTU4WntMusiTBJ7NI9rYCyyYTm5tXP2C/MrL2arh3tHHjWj3aAX+iXk6soyVnckHkXGGg8raxNy2QpPo2eEd1QWXF8Yioj3DRmoToubShdDxOLjQjOcdlWrUw+jmLwRmTNwzu/dt/v/+Ed/l2V15zwTqjtrXl9NiDIipJuJQf/IG4b3POnLcvulP5y99qyIl6wvvj5fEux25NEZZT+C2a6dfF0GgWQ1YG0zESm3rpRbV7O1o9mee11/3W1dEpYpHN1YVlVpV4Fg1dOBBrP7/+DX0tDWe++d14RWNiB6k+s23rK5VyFFsdaUZfmB73vqgx98+qP//nftnr2uMfXqVtV3CL4ATLb3nmz3CRbTnXNf8pPbYjPJ+tEmMpB1m/6PdpkSSYpHUIEhWdh1ocBkFJSblzC5jsEeMz4ixbbwVrTADElYrEJCA9AAya2tifcekZedoL0VPzB2gJCyrJjCWHCG9t95no9Gw7DHZekAMfH1KXV3T0gXNfLKkL7+7Q//lY9//A98FePTE/XL1IGyL0VgVg6Y3SdgzPzat/32dYFI3q9ua8p/jowBRoSebfy5WTNVxmeGaP8aWNZkQucnV2FyDMbSG6s6Q30+oPuDUJcSSG+NvXjp6vve/yNbOzObD2LRilItUosyoJnziMUkBr9bh9uRtS+jQb5/356H7jn6zre9+X3f+cS99xyvtsFE9J8p54iqXAEIjTXOubc+/uj3fN93/c5HP23Xhq50tcUwRrwXFuiv2V3HxfbcxiVOrlMEthesYk37CRU0KPKnsAX6twiUjG6SIsgSiEUhHYAVv+B8XdwsKWmwrirrcl/ICURksSjOXbi6WFCyTLwqEy+h1He/wpgMdXny1Re9e/nUmS9+5ku/8isfWz24//1/6smf/O9/4PE3P+y9Jz2Mqc1xvTaUTklIhN7TWvmxv/T+3/ntT7E5pxQPT5MNZLQP/TU33eD2VXovJpOYv6sPr1CppjEEoa2l4ZErullCkWLTx5NUhEjG/hoRK2LEF2CZlPzS/qLapKgiRm+wUsjCWEPF1EuPZYdT36JHNjEgqViI9f3NMOwDVoxszeYf+dXf/o3f+OhP/vUf/Ps/++Esy4LpUzyEOsKCAkCtNSLy9LvecuzkwYuXb5nBkHQikP6aDPdKOXM3T4srxGQwWVKdCbl9E3qBywi6seEtuEdd/GsuNBo4WpOvg+EMNlTxwJqkSudKbJXFa3PkSU/xFB/Yy2zwplgGqMFAxtCoDorYxD/h61X45CmOKL1zRQkw27NW9kb/8Of++Z/7y39zZzJV2FNE6yTkLU17C4CydLvWxk8/+RbZ2Tag2IH094gYbl7k1hXxDsY2yVikiROtEwSNuzSk7sZhet+KX5pQFSFaNBp2JokulQZMEZkAEiAtz1M1K7IJuzUTFR3sp8UgVpRqMeorJr5yKM3XuTBL58XY3rHjH/vNT/3gj/8dCKrCToMuMGAkEhs6GPbpu977RGUJKIbFhLPbdIVUS5+QkIj0ZBPocpPaLNE0LSRB9blrNDTZx1A3TUBCpPRpEJGDHxKVtA3EhLSbGmpTjGUmZLLQGBeLAwz7gYTPXLULN8G9qbiqxaLID+37zX/7sV/65Y9kmfWeiRVKOMJoGh4gIo8/9vpsz76yLFFOxC8AIwDrn1d8FTLFnVRiHi9tvcQK8TFp/b0D6wOmuaZMyLZUqBSZkh9rRLYGCbr9Y4mjb3xh5JcrHqoyE+m7NOa6toKQFr2igfYAU39IiitLszb+2Z/7hUuXr1lr6L0AbHi6CDlQ48Gq/Tx54sjRwwelKOr2xi63hYzUiMZC1j5Pub6GLJzGh+3oghGukFCSZOvyNEWvBIKgbrFJa1R/MgcI1AxZZXkSRnt9z6CSA4Q6dUpS0ikuQuhPoffODIY3L93+tf/n4wAcVSGRCtlRNs97v7Y2vuvIblksKnBQJw4N+N9qDq+tNGKJpoY+oJnQpOjG3zsQlyhikkvP5Baw3aXNpnO11XyQ+IBQ7kKbHNgKLBlBdkDDSUFxIEYAmobeqtPEbMRQBCu7fuv3Pu+dt9bWsIcOENRZC/ndkUO7pVzoLsAUW60cSV2qQnqmmT5DE/hwKYzcwraqj5zpYw7Nx5Jup2STJ9a5E1rlXIo2Jxp7Qor4q1OdAHAMFaEoutDmToVCeLCINa+/fute/tzzz79y5ty9954sS1clzNB9Uoyv470nZXW0Is5psFF1zzShZuTaRqAbCVgcV54Nc55sdydqBmcVmGcJ2zjpEG/Tx5hWGFPBgqRMAHSw4g4tPOCUSEvYCLUp+ibqaohfDM+l7HLNiCaE9DQWO+vbl6/efOCBe621/yVw0+ramopChHEFI3eaSdNV7KpBbaeYmhhEl1HH1KGg0OLnImvDalBh0BJGd6o3oouRZCSsJzcOoo9e0hJDiKZ2Q5Py9CdP7pdoAKMqlvj4+gSywb/7rU+de/XKYjGzxqrzrEqQFBFxnnmeP3/qrAz6FVqrrHUgaDHJ4ZsO9MCWQNPewNjArCgusX7YKB8koSsz5FliwysIOgBvTdwdszwuExmp/9Yvod7G7Ql5YXWYKZq11nShN9IMEttqQsBbK9lEXRJUUG60qsbTSz/7Z//i1//ZL/2aVMmtIMHOWv1YAhn0ZDTwzutCNFXBkp4C0Zcg/a87KBY0F7lL/dDdXJn8mbdi4ViUMi9lZy7TucwK2ZlzOsPCVXzgxD4oWkSy+mkfVsLuCotWbYFpKskm8P9Q/zGYv1ahJ8XrdF8HmpgcscXJmNUxYOqb5b1WFqECFapooi49tBU/mlvQxqI6jVZM2p2oLmtozWseDgrzqR8jk8++wJD7e1dBB+K9eC+eYiDeYUl7TPLEaDqkUwp0588QcU6mRUUMabJ3qj5VjXg3dakkljCJFVOwVOg/IOBQNLEUm4rg0pA5Ju0NhJeEFBF/SwgAjMyCrCf9nohvhQv1ghvUlyw2PqHuUmi+NeONLcW/DrFHWGm71IcuoZKRaTTUKdcA3Jnlb7t3/D/9aU4XsEY8jVAIf8dWoujUTI3qmCqi8kH5BrV9AWkQ9WESfmVKfNAZfMwT6nCz7iZljUtGHnjgSNQ4hnMyyGbn1+c/99uwAQEnWn23jNpZge2rP1gmtQ9InAe7sL2K8NEh/7fPvNb+aII5AlKW2Dfuv+8tZmsmFV/TM+nqZLjVgTjbBECE7iJmgLw6/KIWx6vTpKCJMc3FpWKqM2lDVuBPo2VU2U9H7B37Tz47n+7I6qhB0aFuAjVGyS70W/kAqLiaCS+ekvyrz3tiF0QJbrQaZxQproHPvPjtOTZ2aEzDhVB9uqL6mJC64U7TG1O1OqM2XpTqkm8+j0+z9+oj+/QAka0CnwRUqCVoId5j2C9ffFXKUoyJmXeSc0uqrRVghMB2rBWzFG0HrZCxHXQiIEdcGvIEaluCVtATtmacwUCsERNEf9gCRZUvSERXGnA61s4qFanQIZJ8VgHTrodEuKTJlaDh5hjYsn11opqgZix5/8oVsXlbKaQ5LxWbvC2+Qd0pWsN18aQ3+BKXQ0pp0aDVhpj2jiGiuFSJGyXmJM0itjANaLpnqsYn7TqENnWiS07ajtZMjNaHijc1TXua1VedNJJcNtStE+XWTvnNV6Wf1wUNiaJ4kvoZaXHbI9ZNIwY1wGkAY6I+XgTlVWMp0JWWYRp6sh0uaUUHpOC2It0z5XWmVZAGRqyxnZDrxQJJhUMiAaNE/ZAOQ7lE6YSpPKAoQYKEQl2/tvdc6c1Pvea/dRH9TDzTj8ekhYBUxTHFTBcRMuP6bXGOpidZn6CIFwisrT+cyQVWSzUqa8w2yBWsfdQ/ZEudLxzD0OePll6EbvZj6nGQMOUb6KNxf1VrnyRdpoGXEnUMm+om2gFyQj7TpA/dAl1/0Ql7+fx3/pjTOYY9OnbsTHOZ6sSWSuJTNKMpsz/wJO47KOM1f3OH19dley7bhdyeyPqmbM+ldGJMPFRkp9EuEnUDTtaAkO3aOkXotegjoVrBg0psXZ6MUorKNkRZVB1cBnAS0NA5xUuCa6rV126OaXKatHh2K/GkYNibv3Rh8dGvYHUozrcaH6mLbh1AlJIofGXACrcgm7dlfSqThUxL2Z7KbA4aSi1QFihyXYkWSNdKNxRRfY6halwaaWSSsLNDdYzKnqG3ix1wFIqsndRFAUZyRJK6JZGy0mtLBY6YNubUqZpzbnUw++VPyo0N2TsWF5092zUY3+kIbEn6SVb+u89LWQpLsVasrboRxFgaI6BkNvUc7TOTVLVEswaTjnOEE4GGINQBSxsz0o67BOLZGJNYJIO2FUlpPCJ4WpmXWgMi5Vs0rphyJ9pGfBTnuH9t9rvPlP/+S9i1IqXvaGdSWJN8l5Bx0/hSRDIZZ0DeoNc6jfDoCM5A7oTEkUurcOxIlCG0NzFamPrktnpJqY8NleBAYCeJdIw5I70GnRpTqorTIFV19o+WgDEbYCOqgJVe9qzMTl/c+Zn/SzKTHmckuVdthkxaqVGryxpkMeI8nRfnxTM8r0Kn2BTzpZOOqdpCt6moCTk7iCCku8YJFZ6qOahNf2w8fFy9lIKJlnAnul3ysQznQ8uRT5shYxIahWohpeOelelrN7Z/9Jfk9oS9KviJ5pdJsIkUl6EG56m6vo2oyEnJ7nL5oU4dCkW6fSwJsMguIy70WtVrrUjvDNvFROEyFAMZAs+mkUiZwQ5fOFVGaFNkGJVaSNDTV52jvgKBVEsCHUXoD+2aPvfK9l/833nmiqz04dmxMcuIfpEqL+wqcYtkTWhah3BoREi0sDPvoOfN5UIcuirEVj1DvJfC0fkapWeMjatd9Ekk3gIKhCJSEe5CJBs6X5GIVUhL3z6UomAoXhyrBEg86xoECK8i7FoYgejlZvewmMwm//Tjs3/8MZkXGA9ZeoQcV51ahLTyDuItKYwPQjIpSykdhoMmjmtkd6gvU8u9U9oErsi7a9rXdD1A9ddkGQ6MZZCJqbXdImGh/mPtq0xI+Ctz45u+2sLJrGDhhB4Ks0gF8QgFa8cyRvUQNpPc0Ds21GsliNJ4q8xKbkXE3dyY/+YzO7/yaffMWRkPMOyLY00AiCTP2J+G2AyUaLhFvicSV5qZcU/WBv7V2+gPKzEULW3RBBpJSrwsQqDuBm7qKtShAEkZ9Nwr17b+zkeq5avl3ZuarxgIhc7VnKmK5QlVOxn2sW/VHt07eOhYdvygUGRr5quSnddyJojV7YjeVDU5iDFuY6u0ICmLsuqdA0RgYEAKnedszlvb7uxV97Uz5VdedmeuSpZhz4o4VklvIqoLzT1mwtqiCrADubehSlavku363Z8dnjy68/MfXf8nH8WQNEbMgJ5SzoUQmzVjL3ScC4jwTy51NyFvgvDl1p2/Pv3F30kpX2hh9SkXAHVAXbPtKL3+zr7V7HUHex985/D977RGZGtandaEOqCy2ugBvfO7x9NPf23yU7+CfXtkMacrYDOBDY0n9cZM57JTiFCGfexaERE6X0+f0GpoQOBDpArNFHp612SuFe0T1Nl9lYitvu6kgOOf+ODmS6/h0Ioc2cPrU7l8i+sTub0jGxPZWG8SilYrVqIoT3bvBxINpOr+5xZ717TuC9tleyyrtFJB3OI3txafubH47Euzj3xm9DMfGj7xBnNrk6YhMegcKiUb0RrZmIz+1NsW/+YzxRdfxMpQBIJSAC/tPhDs6VdMdvE+jPVoJRGMfVna49T0dB9qjaTyh4ncQDbfnpere2a/8VF+9pvcMxBfSunFCWhYFOKdzBdL8McuGzHhzUN3HrLJcirfQFfha7oEQiWBy1RCiC2RKyHFGuxaEUj5tVc2f+gX5e//5dGffYdsTmjR8XugUnGnCAufrebD/+57ii+/IJmprSuampEWfItlemhWfwLQpV3+CVXHWvqSvlDZagreVBtw7c/8Lziw4v/oRThwvhDvGpV1injJsk5re6r8eYeyQRR1CyTRiN1XfwqalTE3YNJsEpsVGYtVTdNM1SO2Npai3Pzrv+CLxcqHnsL6llRcoJTPpRo+KLl1t7fzdz+SPfmm8osvYaVHMpF+VgddF7yZgOQINf0YsSSrb2Qubn3Tb6yraSvo1A9h+Oxp/4lnxFj2LDJIL5c8owUNxNq626ZTDupaCUi7HEAtrK36CBJee010DDTb0BVb3xjFp9fDFCAwrCIiiKyuTP7er86eP4vxEJ4BAyYVDJQgFcxWBoM/904pfIOLsEOaDyzgcC2UXHK1adUbsBHYaH4XY7i1JQPj33zQPHaXzAuWUXwSugNFxGA0lN2rcUhMpaXDUNineC/LNEF5R9LbnbIDpe+KoONcBfOGsa5Z71DQuq7wo0CHrmH6uqmIpCDPOJnv/OP/6I1B6DFtzVaKmDQkt5zMs3c+IAfHXBS1cHTcafVz1K3aMa2kQaxARBkVEIC1srWZve2e/Z/++YP/8i8c/MTf3v1rP2N6kNIl2G7tkGGEUiUjsSFXtLYjlxa9upgE7lQ7g9Y7wpLMOAjTw2iJ66i33UwsqdFUY9jqf/DE7nH52W/M//MLMh5qVxoCUjTC8/Xbz+bmxH772AmZzmGNGlfSlIJiMwdrWMwR3qNwUjoUhcznmC9kPud0IZOZTKYynWNecjIByl2/8D+sPHB3Nl9ki9naB757+De+X7amdS9nOgYmY5K0xy7OVCkKS092wtCCLOmsi0MPUmXuxFUEklJTgA8JZVCLZNoOGhh8jXCtCDibTf/jFwbvfUw4FZjUioMJhCr0HtZkb7nf/f4LlTJ40CVARR0DxEKsRW4lz6Tfq4yzDHLp5dKz6GXSz9HLpZ/LuI+VPgsntzaxMc3vO7Ty4F2+2KC18LBuMnjf45N/+B/EueoqSxSkQKYiFsbBZFSSKil3Fh1QmrKs3RdJJVQJWEOvScPB0fq7od0YSPVnJKHnQKXMHs7LoF98/axbn2SZFceUCKthQwrEw5jC56+/a97rpWC2UrxoFDNZRYbzQvIMO0askWpXMoM8k16fg4wWspjLzpyFIY0svO9b45w4kd4qbk1k4WTQE+dFjOrPlQyeLOYiRno9QEhXyYMoHUfqhsNQ9kghNyzzAMGUR8HaKIUamvZj707CWwjU5EQqvpnhEDksaBoQ+z1e3fTnrsnrj8nOooFoPFQPY3OjCIg4nx/dL8OeeJ9gYM24MHEUeJmXsShdDTVRmgv1u3hXe0prxZri9sb1x+/e8+EfyrKpk2yymG39k18XVETVkK00/QHSz817Hsei9F96nvR12mt6YvtSzoRl7JYMVG3oVjw9x4ayVINNefTmVBtNAFYlxSWKrktmI9TDADWnSpBZbk2LC9fzR+5SiU866bLhd0Mgpbd7x2Z14Demklm06nD1ArERO4IiFwf9o1BJy+P9oseBtek/+A17dbryXY8sNqZb/+qT5We/Iatjlg4weo4iBZl57CG+/Y1+Z4fPfxtb2/LgSSkg61PZmRIUk4u1lHanbMvxsjVIRZKBbbH0mJCNaqoZu0p2wTKBaMVZbM2iYaJ4VpZufVOsTVCMRL48piNSejvom9HA35ogs93JikIwau2khajm8zTKf4Hk4EW8mAzWbv/if9j+pV8XJ9IbyNqqOBenJIaxUSKZ/8ZpWIPZVLZngkzOXBIPEYqxcK4JQ5monLI1ITT40iBu0ukF6KTO6YqzpWuvuYJttEIFcw1yK8GzcV6qsQJIOT9MOZikNZIZXT2l1tup+fJR0SnxdQwdr1CUJkCquXxOdg8DxwDeMWIWsW1dhJlMp/yjZ8SgSnplUVTIb63x6p3QJ3MWuJxDu8QB17Xctp5QOveGUUxfwwChDh/ZeIlCupp9qao+ARlTBd6gf8kussTlVq5OmKIPZGIVqZm+eklCqy1FKE6Uv0CHu1ZHfYbWSL/PvFd/qzECK7BpTQydiFKg4f7WaKFkmpTWiVMMklRfL60vMKESQqvJSavfBun0JrVcqlSJrgAUo2Whqlen3D8liWQ6Qt8Qg64aR8icoUbIKa1caIiYEIOQa8R3MJA0mVFWgwpHVvqKKXWCXgkGMNHjSXwJVdkBlKVzLiozSyApciAm9QkBeUlLKzpEvtbIqNTKSVoFlKrvvDVG05csZizmamRUPf1P0qbHZiNNiPIB1GwtgZAZdWEnRo2a2pymWKopH4naLZaqOLWZFR3AHy23F0cqhk4tVaxTFW+EDYzFD6Qjq8II03R0CBOyvZg8kd6PdLYGdgakknuFEZOxXNiVvf0jr/fTjfm10+JdHcC5me2Pvfcsy3pCq58jy5H3/WLWlP8EvrT9Fb/YYZibqGoIyYzEOLVAIMskPBkH7aVIXVN2ZyJwr1H0hNTefmUkVBNE31/nb0AqgKRPrYGWsEgFvVr1HrBujBGx/cpzAkZgAYoYGFthRARQiYohc5N1ZBw+9N589SDEw+bT88+gN2Qx6+05uvr6715sXtk+9YfVUCRj7cpD78lWD229+Kly+wZszmLWO/LIyv3vnF98dnL2q2Jt1g4CtWDmneAfPQByyTWBKFXFyIbhks6gTnMyQqOGnnOB5fmF1m9odKrVEADVjRveJ/R5SCT70YlbCDLJViTroYos86EYC5PD5sZABKY3oHdu+xaygc2HnG8h72cru0RQ9RHl++4z44OZL2D7vgpeBqvZ2jEzHNuVfeXWdYERiF09IP2R3X8vzj9L+ixKrkoiM3FHfnqSdyHtou8S1nX/C+N06DjWgXqULhX8SDVdPPxJCZ8lIEUQIqFngjok09hjP6GvPHA8Gx5V1mnWaPoyX+fkmggqKb0abgKEXmB94YqbZwcH7mUxn1+/IDYTOjHZ9NI3xebljTPVbFkCbro+PfdlM1gtbpyBseJLgZ1ffFboilvn6UuY6g2qgM+3VE8ql2LEZGlTeDO3KqWjhVvB6Jg6TMjIV1Bje+kDHwlJF06Qfg1zvmrKTjJtKsIW+k4ypiusBLKR+g+0WFQ0EHrMNyUbYLQfIpxcY7moJsCwlkKAiBeY6bmvLq6c8q7w86kYS+8Fxs+3Jt/6jMCIyYVexMNksysviUil+QaKwPjZ5s7LnxVYGFt1yDCdQVmJfjgIJBsi74uZtCbodttjkMghxAIKRZOfQ9EVCJr2qAkDCDW9KHgFpOPXagBCIlMPpBhjjHHOIRBE0LGNTOCkJHqF6sCpvljssJxhuNfuPimucFuXWU5he0l7tbCc3BZjxFhFwbOS58GH1xGnzaJISv1oFnkW7rCR1rgWUnwh+cisHpVsVA2VbLV5dkrDHf0xpFX0UD9K2kO8hN8lUdRVXb+1jFQrk2gY8DTWsCzcxjrqhzTKy+sesqi2p2XXkwaYWBg2IuDODbdxjiLZgddlu45Xwq2R9SQCmwFWohKBNFBEg/UAhFFCQwiMQIYqaFWKEhIwAkO/AIzdfdKsnfDFjLN1+kLowURnpyt8KKkkQTqUQippWiXSWq2Gp27jD0sfVOgjHBEVyyAEPYTWGJtZtzkZjYY//mMf6mc5vasEONIpshHHSblyWjcr1XpgU6pypVs/426dNqO9veOP29WD4ub0riLIqJXl0rZ5sEUGZYuvzNBbSICugCuyXcfyI4+J6fnbZzm9qRj4urmASMs0Qf5TkTnR0nCGRPWrJuVMKbVBmAaqXqFoooAYwFpjMkvv3Pptd/vGe556y+c//ss/9Td+ZF5W0lkedaFGoGsyELbU4NlRBG7NxK78j+2xmBZXXyjXz+cHHhrc84QdrLHYEfogRJ9KDTLaNYi4BVggASqSyaYAMlDo5na02+6/XwTlzXN+52ZV+ZN2K27C/0G7RTuo1yDM4pFEyZHL+RSB0tLFGUI84524ko6+XIj3o7273/M9T/7YD3/o/X/6vdaar33tlIgLIuAB+0ZnYB+ZoNM+agOqmYBK6VgoYozQuK3LfnKzd/DBlXufKDevTC+/yGKWOIbYh1SjSPRu9YF3za6+XGxcQdajGqqpxtlIBmv6xx43q4cW119xN16hOJisCcDZHl3RzZiWtMWzZ1lYMVaY9JkaNuwUtgYqanW72GAcMZ08H+xaGRw7sv/1D973xONveO/T73jw/hMiUhbOwxsDcQuxvUZ0IG0nS+98lGqI/Dm0gIbkjFWrZftCP7/0jfL2+eGJx3c/9oHZxReml18UAbJ+1HzTFSpfmvEesz5u6i8+Tk1qug5EJBs//L3lzq35mc+72RZsBppK9CRVU2IX8+lSHyqlgKNHD37x93+1UhhRVgpdggQV5Njp/ZZ4KiHD4WD3rtW11VF4JO99VbQ0xtT4NxIiaKuhTYuNpFx9ttA8FdUoRaoKRcgHrphtv/yZ3u5jKycfHxx5/eT8Hy9unBWTw2aUJE0XEbqSbtawwGuGmigJABFks9eeW9w8p2TYm+3SyluyXJuJXXVbspf3Hnrwbvn/4Zf33pWuEjysJMIrCW9jjMCoS8OkJStZXoS+/Jr0FRmGVMgrVOMJdPcnYCQbLDYuLZ6/Njr2xrXXf2e5cXn79BfKyW3JB1V9v6HXWEdL5IEBhUZDLUKcZLa4cbYab8Jg/BpVWNyx9YDdPr2QPnn6pm0z1XmLCZVAWnNLVB1Sz+1O/7aakLRE1E5HlN6DLf1SnREiuqNKMxJKBkeB7my3YUF3gFXWf+fC12ZXXxrf/da9j/+3O5dfmJz9Y5YL5AOBYTmTxXa5edkvplIWzAeNuqNiCpIQyWDztkBCp/MC7WMuLfHcVG8MDXgOrVLCZmJTknCZdutrJX6trZOuKoIaxesoGopq8NbyeUCCO2EpGBv6wE08DKIkLpPUnyJANvDlYvOlP9i59M3VB5/e9+Sj2698eXbpG+LL3qGHRkcfzsZ7/YF7ZlcP7Vw6VREsgFZVTWlFIBXeUe/YNfxhKkzrmJCJ0K7iKms2XqKdqZi0cWo6O1O32emOal/SZq1NYhDRTtaj6ibbw19F8fc7LI3unKaKcW7YG5eTW7e//tHB0UdGJx4zgxGnG2uPfh9s3y8mZsXuPvpwvuvIxjc+gXwQSnm1IlqFbwBJGSsZZ0ssQ0Srtiq5c9OkcIlQvZYL6YZO7FZJ4kwKaUsfp+IIWvyHjIwAiNR1q2WyDVSsDD0xDctVGND1hE0CZPvI8tlrX7/1pX/t5tPVN/1ZeufmWwKId+XOrdHxN/QP3E1XJPYMTT9rdDuQZKg1u1PZwQRvTwoyWDaDTctA1LR5JJ+Q6PB6gcTHaK6htBV1m2F0uENhTRIE9c6EYrb0MLW8L6JCfdLmGOplQvEOWV/EcL5Zl14qU2aMeCci/YP3i3dNfB3TQpOkWFQ6PImmZ1T1RFt+OxnOiw5E0RU6Yes7VUaPNDSEyrFTBbFW14aislJJRKd3sRk2z3bBJs2PVV9bENlIuk+QijREiAUQWGMtXCEMKvpeRAgjxgp90vAIxTHuqA20eQKS4Fbgn9Ai2ekQRUfmIJkGfQdaXRRma92YOtVnChGiNaaFak5huGds6Sho7WfqoA0t1RB96OpCglJMb+b4iNCX29elGjlIL3SVDjiBxcYVJQ8fLaKBeGEiDo47nl2JWp+R4ylh4lBXzCadcp7OGEgqM4hcAl12a4uPpoqKSyKZoHDV8Jyx5CR1x3kobRGqCZPtgDklONUhBkTEWBFyMentuys7/Mj09iXkK1WfoQjtaFe5cX1++dvV/BmmahimCzQEUYWuZkMUvqBmfyat3VSYrRI5QMCB48RSQP+dEl5HnOSWcomgMZ5mG7wPI+Cg5r63A+euYFLQpQsyRqj19okwTywYopaqc6AHi5fFxOaDXW/6wPih73QbFzee+9jk/LP0rholNr9+bv3Zj9EVgKXu6KcAyCSOhITq0g0wJ9KgEgq3ChXWUM6gHmWkhJB0s6REfkDbTypRQ/X/sZIZ6AFVhzXFOydCa0xT4vWqCy7q/ElUOktmBTPFVpRuL9hq8BNFlA+m0xiWC6Ebnnh0dNebi41r61//bT9bh+1vnfrUzpkV28u99+VkXUjYHtOO6ToThslYTpENIgrfnj2EoIHsPWOvljSSd1FfuWqW0BQPBWGrSRKNb/OK5ZLKXTJ81mbwm9Sj3qoczjZTvUVkMp1WFUXWs5ERtfoRtT60PFxFUzFAGoxKaxwo9HDK9PiTTopFvuvI+P4nxeSbL366uPWq5H3JhqSHtW6+5XYKgYHNq/lYiIOFQuMbst2PfWDnwnPzq6fEGDG5Zr2GvlFjDYAstwDkv5pfly9f//Iff+Njv/fpT37ma8hyQgQWWSYZJDOwtt7jtGU9rmGWsSzRzATRI5fYzZEZ6xkUSDEzvdHK/U/m++6evfb8zmvPCT36KwzFHBImo8mU5HcH3KAIJJuc+8rw2KO9fcem579WTm5J1icglSBztdzWzuZuc3N7Op1lWZboKyeFMBUaALqhrRPvMNXqSQm6VMPRBGRt4Ofz+a3bm5euXD9z9tUXXjr33DdfeunlC7eu3ZKikNEIvR7FirG+9IvJVCZTyTKpdImhGRf1/EYxBvMFiiJRyyVE9UlqHeWK2QYYuoWQ/cOvG931uJvcWv/6b/nJbekNIFaBDbUYDVIiboywSDVuaf/bYbLBsTf299+3uHF2evl5uhI2j4pbvlxdHa+t9F2xMAZt2r8ulEVNqKS5A1qKJ/T6xl6oZeBa8xLe+2rKxGy6s7k98/NSFgsRI71c+j2b9wD4ag4ARLzH6gpGPVaDxFu6xTqiNEYqjZSNaSW61M7rofR/GpKFuIUd7R3c/XY7GM/OP7O4cVZsBpOxrvYiASlTEgDULWCkngI48nQ9KnS0a3D0Tcj788vfLNYvibEwlpVeGZvqkR5HhTvQtrojIJZE+7hj/sAuBmOEXowRUwlx1rIenloTsPnNNW2dQYOHeoxUO7xGloVJCUhZEonocrlAng+OPmb3nCxunJ5fflF8WVVpQjc6tOa+6l0ILUVpYB1arQ4/1XDJS/oy2328t/8BP58srr3kZ5s1ocW0K18kl87GS8ELhplHQSa9Y386qtRJbTJ0p3iyO1ilIQ1p9ABJ7Vpa5jJoaDfPptRbAyoENe6+mmPns70n+0cf9fPJ7NVn/HQdWV9Sbg60YKziLoc+myjrkUZ6kCNPJboTroDJ8r332JX95dbl8var9E5MFvU7O5PA0e0o6uxBusyJQGeNTLfXt+EMVA6ppUuagPRoyUVhyUgiaZRptKdFC79C7Y0Zr50v7Gj34Oij0luZXzlV3npVjKkJtVxCQ9ZrQrZFDRXtlspZHnk6wVkEIp5ubnqr2b77TNYvbp11kxv1xC7FutUUT8qSEKIFzGkYN6QxUWG3jr6povbKaJgYEXQkJNmSWOfSwQpc2l0L6aCkjREhIG4Bk+cHHsh3Hy83Li+uvURXIOsnA2VStnhghsW+OaaNpFpIOc4vOvx0Il5dGwBDOmFpVw7atWN+se02LrLYEWMR57qEeDYySWLbSCq0gaSqoqWLtU0QJDosbAjMHmkXABK9FqaycT5OtFdZ5ZI6m+JDBi44IOIdyWztsN13P8t5ee1bfr4B02NUxQTTBhq1FequKrX7tvYX9PxatQFRtTD4JV+KsWblkBnu8dPbfnJNvGOl1tUQMJhySlsuVatuJH09CT1U1/+pkiKIWKFrSXhobBSqmyiax1r9EqL1WnQvuu6o0SGdX2CwK9t3v9i+u33ObV0VGBgbdzQOXYkeBUjHfOjpbin5POZgzdNajO9GCsCFxgZUrBgRzjb8YssMdpnRAREvxZQgYNXsjETsutUKg0ZTPc6SaP5R4lFI9JrrJTKArbhWiGAQ4ngwNG+NzmhpPTKuWXEw2nokDTCspneaPfdk+x7w01vl1Rf9fBO2F4IYTeDQ0CCgUV8sqfRpFb0O/AIcejoG8RqBCdzi+hR5CNHfZUb7xDs3ucZiWk/vkg6JQ5ap9Orpl0yiWEVB1/ORBMYKcpYziG7b6JJ9lHFb1taDZuxFaJRRXd4AvdCb0X6zdpS+dLdf5WILJlMSp5Gyj5bGcfOhuYwnqz0NpNWbU/9lpugqej2IdFgrYUXA+aabb2B4wO466ecb3L5GX6Ket+1bMtHprKFWCIx4jJWkR1Or1wRKaGOVAANM0OagaylsqXC3RpTpFifCl8hX7O6TYntu/byfrqNCb8i0hNaWagodVGnxGh3Uj9rxoCNsbzG+C8uYU6IrolBFORgpJlxsmd6KWT0EY1jsMPE+ut6COFpJgRit0APUQ1d1S5SBycUVkrDctAloCdghKTJD2cB0aiwBeCfGmrXjGB/1s3V/+wyLKUwmSgsZnZneyYwO1c2XiAqFQmE3XVKrUX3ByvgktIFrD8hTZzTm8VZYcr4pvrTjg+jvYjllOZdacSnR14BBi3PG1Fe0hOKhJdVgxPbEL5aQ4FMRj1alENJJevW+0YPEaL/Zfa+I+NvnOL0pAGAlDapavjXh1iUtPdAHMNEcCrNJ4xYl5Z2s4dtSzSgNwULQlBTRCH71nybjYqu8sWlG+7Jdd/lix29foSsEVk9Zb5ljNh0yLVoxEuIEohwAjILLFFDbOf6BwQF9hhmmdDRJli9Mf4zVY2Jybl3001sQwOSUZHJ5CxLhnbS3a2XxOMCnhRiAlbRTMiQlEn+EVsYnYzuHEpgCIqHpDvBNXeH0iwnnW+ivmdXDoLDYrsB2SQYRYVkDpm6r6QyWhwCWpi9ursghKt9Rp4opDIKgsFGfOCOAuBLG2l3HzPgwZxt+44IUOzBWy1zoHiat4QIVo6FVJtYnGwn8FlRnEx/AQJCkCCzqDVCZSKo2ubS1R/TAHJMJvZ/eZrFjhnvNcB/dnOW05ior9QVdjVY3E21Z69DsCyu2L26ONk2v1llOul6jkD3YGhsrTkg7Pmj23EXv/eZrnK3DGDUsPRooRvJs0jvf7HczR7otD4A76IqhFYDoQLsuSUb0Cg05AII7zBGTzsmta5XGstgu17ftcL/ddULKqdu6ynIKkxFQPVIMnEHU3az1uMdk3kMzyQiwTIZlROanDv2qthbGqZONs6UjPfqrWD0qsH79NT/fEtQN0lQZQ8vx6sxIR4hJGyxbmtDSmSqOrpoYtNgHmZHJwF2mIX1qGNgtFWkpdkhGiJ/eksW2WTmU7bvf7dzwk+viXeUYWpooemxuJXylZFmaNTcmmbgmUbgnMr1SmcagKQRfmKyH1aOSj/30pt++BmHVm6iB8pjHkGnnThRJoSRLEf0NY48QkjFM+oKwpa6nlJ0l022EuCMhiAnIA6YRti66QUwm3vnNV30+MqvH89E+t3HJz27RWDSFpe7cSOjeV2iVS9N0tjJh8Faaz3F6V8pEogfEjA9ifJjzbXfrFXFzgaGYRIarO5UUOknSI2nUPCHN/o2PjNaYat5B3VCPNYUga0nTahRBUoqsHneUYk6pyar232RSTP2t0xzuNbuOmPE+t3mJxU6l0twaIxzpAhXNrynoBWacOmLVeMc4PyPh7ZmKgu8w2G1Xj3h6t/4q55uCul8nWeNU/abFi2F6UxEYhVFST0tLalXpJfVnSVGiKvepFraJgpAEg919SJPklrhXCgTFINjQGBYTTm+a/jjbdUK8ZznTepRC6XB/FAXI5JIPpWK5dtvLgJaqI4RAZtaOmtUjnN7yGxdYzqtEPaiC1odJQ0FJqB+LpQxCgkE5MzKZ0x3oZA9YRvdDVIKNTRr/Lz4ijV/r2J9VAAAAAElFTkSuQmCC" alt="BitTo"></div>
    <div class="cover-brand">BitTo</div>
    <h1 class="cover-title">${BR.coverH1Plain || '調査報告書'}</h1>
    <div class="cover-sub">${BR.coverSub}</div>
    <div class="cover-client">${escHtml(customerName)}　様</div>
    <table class="cover-info">
      <tr><th>発行日時</th><td>${issuedAt}</td></tr>
      <tr><th>調査件数</th><td>${results.length}件</td></tr>
      <tr><th>作成</th><td>BitTo</td></tr>
    </table>
  </div>

  <div class="page">
    <h2 class="doc-h">調査の目的</h2>
    <p class="doc-p">本報告書は、公開されているブロックチェーンの記録をもとに、ご依頼いただいた送金について
    <strong>資金がどのアドレスを経由し、どこへ到達したか</strong>を明らかにするものです。
    警察・弁護士へのご相談、および取引所への申告の際の資料としてご利用いただけます。</p>

    <h2 class="doc-h">調査の方法</h2>
    <ol class="doc-ol">
      <li>ご依頼のTXID（取引ID）から、送金の日時・数量・送金元・送金先を取得します。</li>
      <li>送金先アドレスのその後の取引を順にたどり、資金の移動経路を組み立てます。</li>
      <li>到達したアドレスを、当社データベース・公開情報・外部のラベル情報と照合し、
          取引所／DEX・ブリッジ（経由）／トークンの契約 などの種別を判定します。</li>
      <li>名称が判明しない場合は、取引回数や残高の状況から推定します。推定の場合はその旨を明記します。</li>
    </ol>

    <h2 class="doc-h">この調査で分かること・分からないこと</h2>
    <table class="info-table">
      <tr><th style="width:50%">分かること</th><th>分からないこと</th></tr>
      <tr>
        <td>資金が経由したアドレスと移動の順序<br>到達先（取引所・サービス）の推定<br>
            交換・橋渡し（スワップ／ブリッジ）が行われた地点<br>各アドレスの残高と取引回数（照会時点）</td>
        <td>取引所の内部で行われた移動<br>法定通貨への交換（現金化）の有無<br>
            口座の名義人が誰であるか<br>資金が現在も残っているかの保証</td>
      </tr>
    </table>
    <p class="doc-note">※ 本報告書は解析結果の提示を目的としたもので、資産の回収・返還を保証するものではありません。
    到達先の判定には推定が含まれます。</p>
  </div>

  <div class="page">
    <h2 class="doc-h">ご依頼内容</h2>
    <table class="info-table">
      <tr><th style="width:12em">ご依頼のTXID件数</th><td>${results.length}件</td></tr>
      <tr><th>送金元アドレス</th><td>${
        [...new Set(results.map(x => x.result && (x.result.sender || (x.result.path && x.result.path[0] && x.result.path[0].address))).filter(Boolean))]
          .map(a => `<span class="mono">${escHtml(a)}</span>`).join('<br>') || '不明'
      }</td></tr>
    </table>

    <h3 class="doc-h3">ご依頼のトランザクション</h3>
    <table class="info-table route-table">
      ${results.map((x, i) => {
        const rr = x.result || {};
        const amt = (rr.tokenSymbol && rr.tokenAmount > 0)
          ? `${rr.tokenAmount} ${rr.tokenSymbol}`
          : `${rr.amount != null ? rr.amount : '不明'} ${rr.chain || ''}`;
        return `<tr><th>${i + 1}</th><td><span class="mono">${escHtml(x.txid)}</span><br>
          <span style="font-size:0.8rem;color:var(--r-ink2)">${escHtml(fmtDate(rr.blockTime))}　／　送金額：${escHtml(amt)}</span></td></tr>`;
      }).join('')}
    </table>
  </div>

  ${aiData.analysis ? `
  <div class="page">
    <div class="ai-overall">
      <div class="ai-header">
        <span class="ai-title">🔎 総合調査分析レポート</span>
      </div>
      <div class="ai-body">${aiData.analysis}</div>
    </div>
  </div>` : ''}

  ${sectionsHTML}

  <p style="text-align:center;color:#94a3b8;font-size:0.78rem;margin-top:20px">
    ${BR.footer}
  </p>
</div>

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
    const paidRun = false;
    let result = cachedResult(cacheKey, paidRun);
    if (result) {
      console.log(`[CACHE] キャッシュ利用: ${txid}`);
    } else {
      result = await investigate(txid, chain);
      txidCache.set(cacheKey, { result, investigatedAt: Date.now(), paid: !!paidRun });
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
      text: `🔄 リセットしました\n\nTXIDをお送りください\n対応：BTC / ETH / XRP / TRON(USDT)`,
    });
  }

  const chain = detectChain(text);

  switch (session.state) {

    // ── 最初のメッセージ ──────────────────────────────────
    case 'idle': {
      session.state = 'waiting_txid';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `先ずは無料調査を開始しますので\nTXIDを1件ずつお送りください\n\n※ TXIDの取得方法はLINEプロフィールを\n　ご参照ください\n\n対応：BTC / ETH / XRP / TRON(USDT)`,
      });
    }

    // ── TXID 待ち ─────────────────────────────────────────
    case 'waiting_txid': {
      if (!chain) {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `TXIDを認識できませんでした\n\nBTC / ETH / XRP / TRON(USDT) のTXIDをお送りください\n（例：ETH は 0x から始まる66文字）`,
        });
      }
      session.txid  = text;
      session.chain = chain;
      session.state = 'investigating';

      const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger', tron: 'TRON（TRC20）' }[chain];
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
          text: `次のTXIDをお送りください\n対応：BTC / ETH / XRP / TRON(USDT)`,
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
      const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger', tron: 'TRON（TRC20）' }[chain];
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
        type: 'text', text: `TXIDをお送りください\n対応：BTC / ETH / XRP / TRON(USDT)`,
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
        const paidRun = true;
        let result = cachedResult(cacheKey, paidRun);
        if (!result) {
          result = await investigate(txid, chain, { paid: true });
          /* ★情報付けが締切をまたいで終わることがある。返す直前にもう一度
           一覧を作り直す。何度呼んでも同じ結果になる作りにしてある。 */
        collectExchanges(result);
  attachNotes(result);
        txidCache.set(cacheKey, { result, investigatedAt: Date.now(), paid: !!paidRun });
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
    const picked = pickLabelFromResponse(j);
    res.json({ ok: r.ok, status: r.status, 名前: picked.name || '(なし)', 種別: picked.type || '(なし)', raw: j });
  } catch (e) {
    res.status(500).json({ error: scrubKey(e.message) });
  }
});

/* 取引回数の分布。MistTrackを引くしきい値（いまは2万回）を決め直すために見る。
   「名前が付いたアドレスの取引回数」と「付かなかったアドレスの取引回数」が
   分かれる境目が、本来のしきい値。 */
/* ★どこが遅いかを見る画面。時間切れの原因を推測でなく事実で追うため。
   調査が時間切れになっても、内側の処理は最後まで走って記録を残すので、
   ここに後から出てくる。 */
/* ★到達先の名前を、確認したその場で登録する画面。
   デプロイも再起動も要らない。次の調査から名前が出る。 */
app.get('/api/admin/labels', requireAdmin, (req, res) => {
  const t = String(req.query.t || '');
  const esc = x => String(x ?? '').replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const rows = Object.entries(manualLabels)
    .map(([a, v]) => ({ addr: a, name: typeof v === 'string' ? v : (v && v.name) || '',
                        at: (v && v.at) || '' }))
    .sort((x, y) => String(y.at).localeCompare(String(x.at)));
  const msg = req.query.msg ? `<p style="color:#3DDC97">${esc(req.query.msg)}</p>` : '';
  const err = req.query.err ? `<p style="color:#f87171">${esc(req.query.err)}</p>` : '';
  /* git へ写すための書き出し。ここ（永続ディスク）はボリュームを作り直すと消えるため。 */
  const forGit = rows.map(r => `  "${r.addr}": ${JSON.stringify(r.name)}`).join(',\n');
  res.type('html').send(`<!doctype html><meta charset="utf-8">
<title>BitTo 到達先の名前</title>
<style>body{font-family:system-ui;margin:20px;background:#12151c;color:#e8ecf3;font-size:14px}
h1{font-size:18px}h2{font-size:15px;margin:22px 0 8px}
input,button{font-size:14px;padding:7px 9px;border-radius:6px;border:1px solid #2a3140;background:#1b2130;color:#e8ecf3}
button{background:#2563eb;border-color:#2563eb;cursor:pointer}
table{border-collapse:collapse;width:100%}th,td{border:1px solid #2a3140;padding:5px 8px;text-align:left;font-size:13px}
th{background:#1b2130}.mono{font-family:ui-monospace,monospace;font-size:12px}
p{color:#9aa4b5;line-height:1.8}textarea{width:100%;height:150px;background:#1b2130;color:#e8ecf3;
border:1px solid #2a3140;border-radius:6px;font-family:ui-monospace,monospace;font-size:12px;padding:8px}
.warn{background:rgba(251,191,36,.10);border:1px solid rgba(251,191,36,.34);border-radius:8px;padding:10px 12px}</style>
<h1>到達先の名前を登録</h1>
${msg}${err}
<div class="warn"><b>誤って登録すると、誤った凍結要請先が出ます。</b>
必ず出所（OKLink・MistTrack・警察からの回答など）を確認してから登録してください。</div>

<h2>登録</h2>
<form method="POST" action="/api/admin/labels?t=${esc(t)}">
  <input name="addr" placeholder="アドレス" style="width:44%" required>
  <input name="name" placeholder="名前（例：Binance／WhiteBIT）" style="width:28%" required>
  <button type="submit">登録する</button>
</form>
<p>対応：0x…（Ethereum系）／T…（TRON）／r…（XRP）／bc1・1・3…（Bitcoin）<br>
登録した瞬間から有効です。デプロイも再起動も要りません。</p>

<h2>登録済み ${rows.length}件</h2>
${rows.length ? `<table><tr><th>アドレス</th><th>名前</th><th>登録日時</th><th></th></tr>
${rows.map(r => `<tr><td class="mono">${esc(r.addr)}</td><td>${esc(r.name)}</td>
  <td>${esc(String(r.at).slice(0, 16).replace('T', ' '))}</td>
  <td><form method="POST" action="/api/admin/labels/delete?t=${esc(t)}" style="margin:0">
    <input type="hidden" name="addr" value="${esc(r.addr)}">
    <button style="background:#7f1d1d;border-color:#7f1d1d">削除</button></form></td></tr>`).join('')}</table>`
  : '<p>まだありません。</p>'}

<h2>コードへ写す用</h2>
<p>ここ（サーバーのディスク）はボリュームを作り直すと消えます。<br>
ときどき下記を <b>address-labels.json</b> に貼って、コード側にも残してください。</p>
<textarea readonly>${esc(forGit)}</textarea>`);
});

app.post('/api/admin/labels', requireAdmin, express.urlencoded({ extended: false }), async (req, res) => {
  const t = encodeURIComponent(String(req.query.t || ''));
  const addr = String(req.body.addr || '').trim();
  const name = String(req.body.name || '').trim();
  const back = (k, v) => res.redirect(`/api/admin/labels?t=${t}&${k}=${encodeURIComponent(v)}`);
  if (!looksLikeAddress(addr)) return back('err', 'アドレスの形が正しくありません');
  if (!name || name.length > 60) return back('err', '名前は1〜60文字で入力してください');
  if (/[<>]/.test(name)) return back('err', '名前に使えない記号があります');
  const key = addr.toLowerCase();
  const before = LABEL_DB[key];
  manualLabels[key] = { name, at: new Date().toISOString() };
  LABEL_DB[key] = name;                     // その場で有効にする
  await saveManualLabels();
  console.log(`[LABEL_DB] 管理画面から登録: ${key.slice(0, 12)}… → "${name}"`);
  return back('msg', before && before !== name
    ? `登録しました（「${before}」から変更）` : '登録しました');
});

app.post('/api/admin/labels/delete', requireAdmin, express.urlencoded({ extended: false }), async (req, res) => {
  const t = encodeURIComponent(String(req.query.t || ''));
  const key = String(req.body.addr || '').trim().toLowerCase();
  if (manualLabels[key]) {
    delete manualLabels[key];
    delete LABEL_DB[key];                   // 消したら即座に効かなくする
    await saveManualLabels();
    console.log(`[LABEL_DB] 管理画面から削除: ${key.slice(0, 12)}…`);
  }
  return res.redirect(`/api/admin/labels?t=${t}&msg=${encodeURIComponent('削除しました')}`);
});

app.get('/api/admin/timing', requireAdmin, (req, res) => {
  const esc = x => String(x ?? '').replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
  const byHost = {};
  for (const c of slowCalls) {
    const k = c.host + ' ' + c.what;
    const b = byHost[k] || (byHost[k] = { n: 0, sum: 0, max: 0, ng: 0 });
    b.n++; b.sum += c.ms; b.max = Math.max(b.max, c.ms); if (c.ng) b.ng++;
  }
  const rank = Object.entries(byHost).sort((a, b) => b[1].sum - a[1].sum);
  res.type('html').send(`<!doctype html><meta charset="utf-8">
<title>BitTo どこが遅いか</title>
<style>body{font-family:system-ui;margin:20px;background:#12151c;color:#e8ecf3;font-size:14px}
h2{font-size:16px;margin:24px 0 8px}table{border-collapse:collapse;width:100%;margin-bottom:8px}
th,td{border:1px solid #2a3140;padding:5px 8px;text-align:left;font-size:13px}
th{background:#1b2130}.n{text-align:right;font-variant-numeric:tabular-nums}
.ng{color:#f87171}.hi{color:#fbbf24;font-weight:700}p{color:#9aa4b5;line-height:1.8}</style>
<h1 style="font-size:18px">どこが遅いか</h1>
<p>${SLOW_CALL_MS}ミリ秒以上かかった呼び出しと、失敗した呼び出しだけを残しています。<br>
アドレスやTXIDは記録していません（どのサービスの何を呼んだかだけ）。<br>
※ 再起動すると消えます。調査を流した直後にご覧ください。</p>

<h2>遅い問い合わせ先（合計時間の多い順）</h2>
${rank.length ? `<table><tr><th>問い合わせ先</th><th class="n">回数</th><th class="n">合計</th><th class="n">最長</th><th class="n">失敗</th></tr>
${rank.map(([k, b]) => `<tr><td>${esc(k)}</td><td class="n">${b.n}</td>
  <td class="n ${b.sum > 10000 ? 'hi' : ''}">${(b.sum / 1000).toFixed(1)}秒</td>
  <td class="n ${b.max > 4000 ? 'hi' : ''}">${(b.max / 1000).toFixed(1)}秒</td>
  <td class="n ${b.ng ? 'ng' : ''}">${b.ng}</td></tr>`).join('')}</table>`
  : '<p>まだ記録がありません。</p>'}

<h2>調査ごとの内訳（新しい順）</h2>
${phaseLog.length ? `<table><tr><th>日時</th><th>TXID</th><th>チェーン</th><th class="n">合計</th><th>段ごと</th></tr>
${[...phaseLog].reverse().map(p => `<tr><td>${esc(p.at.slice(5, 19).replace('T', ' '))}</td>
  <td>${esc(p.txid)}</td><td>${esc(p.chain)}</td>
  <td class="n ${p.total > 60000 ? 'hi' : ''}">${(p.total / 1000).toFixed(1)}秒</td>
  <td>${Object.entries(p.phases).map(([k, v]) =>
    `${esc(k)} <span class="${v > 20000 ? 'hi' : ''}">${(v / 1000).toFixed(1)}秒</span>`).join('／')}</td></tr>`).join('')}</table>`
  : '<p>まだ記録がありません。</p>'}

<h2>直近の遅い呼び出し（新しい順・20件）</h2>
${slowCalls.length ? `<table><tr><th>日時</th><th>問い合わせ先</th><th class="n">所要</th><th>結果</th></tr>
${[...slowCalls].reverse().slice(0, 20).map(c => `<tr><td>${esc(c.at.slice(11, 19))}</td>
  <td>${esc(c.host)} ${esc(c.what)}</td>
  <td class="n ${c.ms > 4000 ? 'hi' : ''}">${(c.ms / 1000).toFixed(1)}秒</td>
  <td class="${c.ng ? 'ng' : ''}">${esc(c.ng || 'OK')}</td></tr>`).join('')}</table>`
  : ''}`);
});

app.get('/api/admin/hop-stats', requireAdmin, (req, res) => {
  const chain = String(req.query.chain || '').toLowerCase();
  let rows = hopStats.filter(r => !r.via && !r.token);   // 通り道は対象外
  if (chain) rows = rows.filter(r => r.chain === chain);
  const BANDS = [0, 10, 50, 100, 500, 1000, 5000, 20000, 100000, 500000, Infinity];
  const band = tx => {
    for (let i = 0; i < BANDS.length - 1; i++) if (tx >= BANDS[i] && tx < BANDS[i + 1]) {
      return BANDS[i + 1] === Infinity ? BANDS[i].toLocaleString() + '回以上'
        : BANDS[i].toLocaleString() + '〜' + (BANDS[i + 1] - 1).toLocaleString() + '回';
    }
    return '?';
  };
  const tally = {};
  for (const r of rows) {
    const k = band(r.tx);
    tally[k] = tally[k] || { 件数: 0, 名前あり: 0, 推定のみ: 0, 取引所: 0 };
    tally[k].件数++;
    if (r.named)    tally[k].名前あり++;
    if (r.inferred) tally[k].推定のみ++;
    if (r.ex)       tally[k].取引所++;
  }
  for (const k of Object.keys(tally)) {
    const t = tally[k];
    t['名前が付いた割合'] = Math.round(t.名前あり / t.件数 * 100) + '%';
  }
  res.json({
    件数: rows.length,
    ためた期間: rows.length ? {
      最古: new Date(Math.min(...rows.map(r => r.at))).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }),
      最新: new Date(Math.max(...rows.map(r => r.at))).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }),
    } : null,
    現在のしきい値: 'TX 20,000回以上でMistTrackを引く',
    取引回数の分布: tally,
  });
});

/* 住所プロファイルの疎通確認。1回分を消費する。
   エンドポイントは address_trace（address_profile ではない）。 */
app.get('/api/admin/profile', requireAdmin, async (req, res) => {
  const addr  = (req.query.address || '').trim();
  const chain = (req.query.chain || 'eth').toLowerCase();
  if (!addr) return res.status(400).json({ error: 'address が必要です' });
  if (!MISTTRACK_KEY) return res.json({ ok: false, reason: 'MISTTRACK_API_KEY が未設定です' });
  if (!misttrackSupports(chain)) return res.json({ ok: false, reason: chain + ' は MistTrack の対象外です' });
  try {
    const r = await fetchT(profileApiUrl(addr, chain));
    const j = await r.json();
    res.json({ ok: r.ok, status: r.status, 整形後: pickProfileFromResponse(j), raw: j });
  } catch (e) {
    res.status(500).json({ error: scrubKey(e.message) });
  }
});

/* AMLリスクスコアの疎通確認。1回分を消費する。
   このエンドポイントだけ v3 なので、URLの組み立ても含めてここで確かめる。 */
app.get('/api/admin/risk', requireAdmin, async (req, res) => {
  const addr  = (req.query.address || '').trim();
  const chain = (req.query.chain || 'eth').toLowerCase();
  if (!addr) return res.status(400).json({ error: 'address が必要です' });
  if (!MISTTRACK_KEY) return res.json({ ok: false, reason: 'MISTTRACK_API_KEY が未設定です' });
  if (!misttrackSupports(chain)) return res.json({ ok: false, reason: chain + ' は MistTrack の対象外です' });
  try {
    const r = await fetchT(riskApiUrl(addr, chain));
    const j = await r.json();
    res.json({ ok: r.ok, status: r.status, 整形後: pickRiskFromResponse(j), raw: j });
  } catch (e) {
    res.status(500).json({ error: scrubKey(e.message) });
  }
});

/* 取引先分析の疎通確認。1回分を消費するので、確認のとき以外は使わない。 */
app.get('/api/admin/counterparty', requireAdmin, async (req, res) => {
  const addr  = (req.query.address || '').trim();
  const chain = (req.query.chain || 'eth').toLowerCase();
  if (!addr) return res.status(400).json({ error: 'address が必要です' });
  if (!MISTTRACK_KEY) return res.json({ ok: false, reason: 'MISTTRACK_API_KEY が未設定です' });
  if (!misttrackSupports(chain)) return res.json({ ok: false, reason: chain + ' は MistTrack の対象外です' });
  try {
    const r = await fetchT(counterpartyApiUrl(addr, chain));
    const j = await r.json();
    const picked = pickCounterpartyFromResponse(j);
    const hit    = exchangeFromCounterparty(picked);
    res.json({
      ok: r.ok, status: r.status,
      取引先: picked,
      推定した取引所: hit ? hit.name + '（' + hit.percent + '%）' : '(なし)',
      raw: j,
    });
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
${a.e3 === '連絡した' ? '<div class="warn"><b>回収業者にご連絡済みとのことです。</b>「返金の可能性が高い」「調査に高額な費用が必要」と言われている場合は、二次被害の典型的なサインです。支払い前に、警察・消費者ホットライン188へご相談ください。</div>' : ''}

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

/* 合言葉の入力欄。ここだけは合言葉なしで開ける。 */
function adminLoginPage(next, err) {
  const safeNext = /^\/[A-Za-z0-9/_-]*$/.test(next || '') ? next : '/admin';
  return `<!DOCTYPE html><html lang="ja"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="robots" content="noindex,nofollow">
<title>BitTo 管理</title><style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0C1728;color:#C7D6EC;font-family:-apple-system,'Hiragino Sans','Noto Sans JP',Meiryo,sans-serif;
display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}
form{background:#152741;border:1px solid #2C4468;border-radius:12px;padding:28px 26px;width:100%;max-width:420px}
h1{font-size:17px;margin-bottom:6px}
p{font-size:12.5px;color:#8FA3C4;line-height:1.8;margin-bottom:18px}
input{width:100%;background:#0C1728;border:1px solid #2C4468;border-radius:8px;color:#C7D6EC;
font:inherit;font-size:16px;padding:12px 13px;margin-bottom:14px}
input:focus{outline:none;border-color:#34E1C8}
button{width:100%;background:#34E1C8;color:#062A25;border:none;border-radius:8px;
font:inherit;font-weight:700;font-size:15px;padding:13px;cursor:pointer}
button:hover{background:#4FE9D4}
.err{background:rgba(248,113,113,.12);border:1px solid #F87171;color:#F87171;
border-radius:8px;padding:10px 12px;font-size:12.5px;margin-bottom:14px;line-height:1.7}
</style></head><body>
<form method="post" action="/admin/login">
  <h1>BitTo 管理</h1>
  <p>Railway の <b>ADMIN_TOKEN</b> に設定した合言葉を貼り付けてください。<br>
  一度入れると12時間は入力不要です。</p>
  ${err ? `<div class="err">${escHtml(err)}</div>` : ''}
  <input type="password" name="token" placeholder="合言葉を貼り付け" autocomplete="current-password" autofocus>
  <input type="hidden" name="next" value="${escHtml(safeNext)}">
  <button type="submit">開く</button>
</form></body></html>`;
}

app.get('/admin/login', (req, res) => {
  if (!ADMIN_TOKEN) return res.redirect('/admin');
  if (adminOk(req)) return res.redirect('/admin');   // すでに入れている
  res.type('html').send(adminLoginPage(String(req.query.next || '/admin'), ''));
});

/* 合言葉は本文（POST）で受け取る。URLに載せないので履歴にもログにも残らない。 */
app.post('/admin/login', express.urlencoded({ extended: false }), (req, res) => {
  const ip = reqIp(req);
  const next = String((req.body && req.body.next) || '/admin');
  if (!adminTryOk(ip)) {
    return res.status(429).type('html')
      .send(adminLoginPage(next, '入力を何度も間違えたため、しばらく開けません。15分ほどお待ちください。'));
  }
  if (!adminTokenMatches((req.body && req.body.token) || '')) {
    adminTryFail(ip);
    console.warn('[Admin] 合言葉が違います:', ip);
    return res.status(401).type('html').send(adminLoginPage(next, '合言葉が違います。'));
  }
  res.cookie(ADMIN_COOKIE, ADMIN_TOKEN, {
    httpOnly: true,
    secure: BASE_URL.startsWith('https'),
    sameSite: 'strict',
    maxAge: ADMIN_COOKIE_MAX_AGE,
    path: '/',
  });
  adminTries.delete(ip);
  res.redirect(/^\/[A-Za-z0-9/_-]*$/.test(next) ? next : '/admin');
});

/* Cookieを消す。共用の端末で開いたときに使う。 */
app.get('/admin/logout', (_req, res) => {
  res.clearCookie(ADMIN_COOKIE, { path: '/' });
  res.redirect('/admin/login');
});

/* 相談チャットの記録を見る。一覧では本文を伏せ、開いたときだけ全文を出す。
   画面は /admin/chats?t=<ADMIN_TOKEN>。 */
app.get('/api/admin/chatlogs', requireAdmin, (req, res) => {
  const q = String(req.query.q || '').trim();
  const device = String(req.query.device || '').trim();
  let list = chatLogs;
  if (device) list = list.filter(c => c.device === device);
  if (q) list = list.filter(c => (c.q + ' ' + c.a).includes(q));
  const total = list.length;
  const page = Math.max(1, parseInt(req.query.page) || 1);
  const per = 50;
  const rows = list.slice().reverse().slice((page - 1) * per, page * per).map(c => ({
    id: c.id, at: new Date(c.at).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }),
    device: c.device, brand: c.brand,
    // 一覧では冒頭だけ。全文は個別に開いたときだけ返す
    抜粋: c.q.slice(0, 40) + (c.q.length > 40 ? '…' : ''),
  }));
  res.json({ 件数: total, ページ: page, 記録: rows });
});

app.get('/api/admin/chatlogs/:id', requireAdmin, (req, res) => {
  const c = chatLogs.find(x => x.id === req.params.id);
  if (!c) return res.status(404).json({ error: '見つかりません' });
  res.json({ ...c, at: new Date(c.at).toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' }) });
});

/* 削除請求への対応。端末IDを指定して、その端末の記録をすべて消す。 */
app.get('/api/admin/chatlogs-delete', requireAdmin, (req, res) => {
  const device = String(req.query.device || '').trim();
  if (!device) return res.status(400).json({ error: 'device が必要です' });
  const before = chatLogs.length;
  chatLogs = chatLogs.filter(c => c.device !== device);
  saveChatLogs();
  console.log(`[ChatLog] 削除請求により ${before - chatLogs.length}件を削除（端末 ${device}）`);
  res.json({ ok: true, 削除件数: before - chatLogs.length, 残り: chatLogs.length });
});

app.get('/admin/chats', requireAdmin, (_req, res) => res.sendFile(path.join(__dirname, 'public', 'admin-chats.html')));

/* ラベルAPIの使用状況。前払いの残りを見積もるために使う。 */
app.get('/api/admin/label-usage', requireAdmin, (_req, res) => {
  const d = labelDayKey(), m = labelMonthKey();
  res.json({
    設定: {
      '有料1件あたり': MISTTRACK_PAID_LOOKUPS,
      '無料1件あたり': MISTTRACK_FREE_LOOKUPS,
      '1日の上限': MISTTRACK_DAILY_CAP,
      '1か月の上限': MISTTRACK_MONTH_CAP,
      '購入した総回数': MISTTRACK_TOTAL_CAP,
      '1利用者あたり1日': MISTTRACK_USER_DAILY,
      '1利用者あたり1か月': MISTTRACK_USER_MONTH,
      キー: MISTTRACK_KEY ? '設定済み' : '未設定',
    },
    '利用者ごとの記録件数': Object.keys(deviceUsage).length,
    '本日': labelUsage.day === d ? labelUsage.count : 0,
    '今月': labelUsage.month === m ? labelUsage.monthCount : 0,
    'これまでの合計': labelUsage.total,
    '残り': Math.max(0, MISTTRACK_TOTAL_CAP - labelUsage.total),
    '無料が使える残り': Math.max(0, MISTTRACK_TOTAL_CAP - MISTTRACK_PAID_RESERVE - labelUsage.total),
    '有料のために確保': MISTTRACK_PAID_RESERVE,
    'キャッシュ済みアドレス': labelCache.size,
    '取引先分析キャッシュ': cpCache.size,
    'TRONで覚えた取引所名': tronTags.size,
    '素性キャッシュ': profileCache.size,
    'リスクスコアキャッシュ': riskCache.size,
    '取引先分析の回数': { '無料': MISTTRACK_CP_FREE, '有料': MISTTRACK_CP_PAID, '採用する最低割合': CP_MIN_PERCENT + '%' },
    'リスクスコアの回数': { '無料': MISTTRACK_RISK_FREE, '有料': MISTTRACK_RISK_PAID },
  });
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
          const paidRun = true;
          let result = cachedResult(cacheKey, paidRun);
          if (!result) {
            result = await investigate(item.txid, item.chain, { paid: true });
            /* ★情報付けが締切をまたいで終わることがある。返す直前にもう一度
           一覧を作り直す。何度呼んでも同じ結果になる作りにしてある。 */
        collectExchanges(result);
  attachNotes(result);
        txidCache.set(cacheKey, { result, investigatedAt: Date.now(), paid: !!paidRun });
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
/* 端末ごと。被害直後に何件も調べる人がいるので、窮屈にしない。 */
const DEVICE_LIMIT_HOUR = Number(process.env.DEVICE_LIMIT_HOUR ?? 15);
const DEVICE_LIMIT_DAY  = Number(process.env.DEVICE_LIMIT_DAY  ?? 40);
const connDeviceMap = new Map();
/* IPごと。いまは端末ごとの上限が主なので、こちらは「端末IDを変えながら
   叩く相手」への最後の歯止め。携帯回線は数百人が同じIPを共有するため、
   ここを詰めると無関係の被害者まで巻き添えになる。広めに取る。
   MistTrackの消費は別枠（1日5回）で守られているので、緩めても費用は増えない。 */
const CONN_LIMIT_HOUR = Number(process.env.CONN_LIMIT_HOUR ?? 60);
const CONN_LIMIT_DAY  = Number(process.env.CONN_LIMIT_DAY  ?? 200);
/* 携帯回線は多数の利用者が少数のIPを共有する（CGNAT）。IPだけで数えると、
   同じ回線の他人が使った分で被害者が締め出される。実際に困るのは、
   被害直後に何度も調べたい人が「上限に達しました」で止まること。
   そこで端末ごとの数を主にし、IPは荒らしへの最後の歯止めとして緩く持つ。
   端末IDは利用者側で作られるので、それだけでは歯止めにならない。両方見る。 */
function connRateOk(ip, device) {
  const now = Date.now();
  const count = (key, map, perHour, perDay) => {
    if (!key) return true;                       // 手がかりが無ければこの軸では数えない
    const arr = (map.get(key) || []).filter(t => now - t < 86400000);
    map.set(key, arr);
    if (arr.filter(t => now - t < 3600000).length >= perHour) return false;
    if (arr.length >= perDay) return false;
    return true;
  };
  const okDevice = count(device, connDeviceMap, DEVICE_LIMIT_HOUR, DEVICE_LIMIT_DAY);
  const okIp     = count(ip,     connRateMap,   CONN_LIMIT_HOUR,   CONN_LIMIT_DAY);
  if (!okDevice) { console.warn('[Rate] 端末の上限:', String(device).slice(0, 8)); return false; }
  if (!okIp)     { console.warn('[Rate] IPの上限:', ip); return false; }
  /* 通す時だけ記録する。弾いた分まで数えると、待っても解除されなくなる。
     count() が済んだ時点で、どちらの Map にも配列が入っている。 */
  if (device) connDeviceMap.get(device).push(now);
  if (ip)     connRateMap.get(ip).push(now);
  return true;
}
// 溜まりっぱなしにしない（1日経った記録は捨てる）
setInterval(() => {
  const cutoff = Date.now() - 86400000;
  for (const map of [connRateMap, connDeviceMap])
  for (const [ip, arr] of map) {
    const keep = arr.filter(t => t > cutoff);
    if (keep.length) map.set(ip, keep); else map.delete(ip);
  }
}, 3600000);

/* ══ 相談チャットの記録 ═══════════════════════════════════════
   目的：どんな相談が来ているかを運営が把握し、案内文を直すため。
   保存しないもの：氏名・メールアドレス・IPアドレス
   保存するもの　：端末ごとのランダムID・日時・ブランド・質問・回答
   伏せるもの　　：シードフレーズ・秘密鍵・パスワードらしき文字列 */
const CHATLOG_FILE = path.join(REPORTS_DIR, 'chatlogs.json');
let chatLogs = [];
try {
  if (fs.existsSync(CHATLOG_FILE)) {
    chatLogs = JSON.parse(fs.readFileSync(CHATLOG_FILE, 'utf8'));
    console.log(`[ChatLog] ${chatLogs.length}件を復元`);
  }
} catch (e) { console.error('[ChatLog] 復元失敗:', e.message); }

function saveChatLogs() {
  fsp.writeFile(CHATLOG_FILE, JSON.stringify(chatLogs), 'utf8')
    .catch(e => console.error('[ChatLog] 保存失敗:', e.message));
}

/* 万一漏れたときの被害を小さくするため、保存前に伏せる。
   利用者が誤って書いてしまうことがあるため、こちらで持たない。 */
function maskSecrets(text) {
  let t = String(text || '');
  // 12語以上の英単語の羅列＝シードフレーズの可能性
  t = t.replace(/\b([a-z]{3,10}\s+){11,23}[a-z]{3,10}\b/gi, '［シードフレーズらしき記載を伏せました］');
  // 0x以外の64桁16進＝秘密鍵の可能性（TXIDは0x付きなので残る）
  t = t.replace(/(^|[^0-9a-fx])([0-9a-f]{64})(?![0-9a-f])/gi, (m, p) => p + '［秘密鍵らしき記載を伏せました］');
  // 「パスワード」の後に続く文字列
  t = t.replace(/(パスワード|password|暗証番号)\s*[:：はが]?\s*\S+/gi, '$1［伏せました］');
  return t;
}

function addChatLog(entry) {
  chatLogs.push({
    id: crypto.randomUUID(),
    at: Date.now(),
    device: String(entry.device || '').slice(0, 40) || '（不明）',
    brand: entry.brand === 'bitto' ? 'BitTo' : 'Connection',
    q: maskSecrets(entry.q).slice(0, 2000),
    a: String(entry.a || '').slice(0, 4000),
    txids: (entry.txids || []).slice(0, 5),
  });
  if (chatLogs.length > 20000) chatLogs = chatLogs.slice(-20000);   // 際限なく増やさない
  saveChatLogs();
}

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
  const paidRun = true;
  let result = cachedResult(cacheKey, paidRun);
  if (!result) {
    result = await investigate(txid, chain, { paid: true });
    txidCache.set(cacheKey, { result, investigatedAt: Date.now(), paid: !!paidRun });
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
    // AI相談の記録は端末ごとの番号でしか消せないため、請求時に受け取る
    const device = esc((req.body.device || '').toString().trim().slice(0, 40));
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
         <tr><td style="padding:4px 10px;color:#64748b">端末の番号</td><td style="padding:4px 10px">${device || '（記載なし）'}</td></tr>
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
  const ip = reqIp(req);
  const device = String((req.body && req.body.device) || '').trim().slice(0, 64);
  if (!connRateOk(ip, device)) return res.status(429).json({ error: '調査回数の上限に達しました。しばらく時間をおいてお試しください。' });

  const jobId = crypto.randomUUID();
  connectionJobs.set(jobId, { status: 'running', txid, chain, createdAt: Date.now() });
  (async () => {
    try {
      const cacheKey = txid.toLowerCase();
      const paidRun = false;
      let result = cachedResult(cacheKey, paidRun);
      if (!result) {
        // 内部の時間予算をすり抜けて investigate() が固まると、ジョブが running のまま残り
        // クライアントは永久に「解析中」になる。最後の砦として全体に上限時間を課し、
        // 必ず done か error のどちらかで終わらせる。
        result = await Promise.race([
          investigate(txid, chain, { device }),
          new Promise((_, reject) => setTimeout(
            () => reject(new Error('調査が時間内に完了しませんでした。時間をおいてもう一度お試しください。')),
            investigateHardMs(paidRun)
          )),
        ]);
        /* ★情報付けが締切をまたいで終わることがある。返す直前にもう一度
           一覧を作り直す。何度呼んでも同じ結果になる作りにしてある。 */
        collectExchanges(result);
  attachNotes(result);
        txidCache.set(cacheKey, { result, investigatedAt: Date.now(), paid: !!paidRun });
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
        value: (xrpAmount(t.Amount) || 0), unit: 'XRP',
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
    // 相談内容を記録する（氏名・メール・IPは保存しない）
    addChatLog({
      device: req.body.device,
      brand,
      q: message,
      a: reply,
      txids: (ctx && ctx.txid) ? [ctx.txid] : [],
    });
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
  /* ★追跡そのものに使う鍵を先に出す。TronGridの鍵が無いと回数制限（429）で
     TRON側の追跡が途中で止まり、利用者には「そこで送金が終わった」と見える。
     実測：XRP→TRONの案件で、資金の終点ではなく制限で止まっていた。 */
  console.log(`🔑 Etherscan  : ${ETHERSCAN_KEY ? '✓' : '⚠ 未設定（EVMの追跡が止まります）'}`);
  console.log(`🔑 TronGrid   : ${TRON_KEY ? '✓' : '⚠ 未設定（TRONの追跡が制限で止まります）'}`);
  console.log(`🔑 MistTrack  : ${MISTTRACK_KEY ? '✓' : '⚠ 未設定（取引所名が引けません）'}`);
  console.log(`🔑 Blockchair : ${BLOCKCHAIR_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 LINE       : ${LINE_CHANNEL_ACCESS_TOKEN ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Stripe     : ${stripe ? '✓ 本番モード' : '⚠ テストモード（決済スキップ）'}`);
  console.log(`🔑 Sheets     : ${GOOGLE_SHEET_ID && process.env.GOOGLE_SERVICE_ACCOUNT_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Mail(SMTP) : ${SMTP_USER && SMTP_PASS ? '✓' : '⚠ 未設定'}`);
  console.log(`🧪 プレビュー : ${BASE_URL}/report/preview`);
  console.log();
});

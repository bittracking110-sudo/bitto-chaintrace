// ============================================================
// BitTo — LINE ブロックチェーン自動調査サーバー
// BTC / ETH / XRP 対応 | LINE Messaging API + Stripe 決済
// ============================================================
require('dotenv').config();
const express  = require('express');
const crypto   = require('crypto');
const fetch    = require('node-fetch');
const cors     = require('cors');
const path     = require('path');
const line     = require('@line/bot-sdk');

const app  = express();
const PORT = process.env.PORT || 3000;

// ── APIキー ────────────────────────────────────────────────
const BLOCKCHAIR_KEY            = process.env.BLOCKCHAIR_API_KEY;
const ETHERSCAN_KEY             = process.env.ETHERSCAN_API_KEY;
const GEMINI_KEY                = process.env.GEMINI_API_KEY;
const LINE_CHANNEL_ACCESS_TOKEN = process.env.LINE_CHANNEL_ACCESS_TOKEN;
const LINE_CHANNEL_SECRET       = process.env.LINE_CHANNEL_SECRET;
const STRIPE_SECRET_KEY         = process.env.STRIPE_SECRET_KEY;
const STRIPE_WEBHOOK_SECRET     = process.env.STRIPE_WEBHOOK_SECRET;
const BASE_URL                  = process.env.BASE_URL || `http://localhost:${PORT}`;

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
// ユーザーごとの会話状態
// state: idle → h_name → h_damage → h_reason → h_txid
//        → investigating → tos → awaiting_payment → paid
const userSessions = new Map();

// TXIDの調査結果キャッシュ（全ユーザー共通・API節約）
const txidCache = new Map();

// Stripe決済セッション
const pendingSessions = new Map();

function getSession(userId) {
  if (!userSessions.has(userId)) {
    userSessions.set(userId, { state: 'idle' });
  }
  return userSessions.get(userId);
}

function resetSession(userId) {
  userSessions.set(userId, { state: 'idle' });
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
  // ─── HitBTC ───
  '0x1c4b70a3968436b9a0a9cf5205c787eb81bb558c': 'HitBTC',
  '0x0a98fb70939162725ae863267f8b056e9d890906': 'HitBTC',
  '0xf259869dfc3f3de5e1b2292882e3d59c8f2d1b01': 'HitBTC',
  '0x3d28a7c8d8f4f06b5f60d5855e5a1f6b5f59f95c': 'HitBTC',
  '1KAt6STtisWMMVo63xFER7NnGBBBBMHTNK': 'HitBTC BTC',
  '1GZEgEoAOcMKoqz93MPpFfQpFPDyKi41jh': 'HitBTC BTC',
  // ─── その他主要取引所 ───
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

const EX_KEYWORDS = [
  'binance','okx','okex','coinbase','kraken','bitfinex','huobi',
  'bybit','kucoin','gate','bitflyer','coincheck','zaif','liquid',
  'ftx','bittrex','bitstamp','upbit','bithumb','exchange','hot wallet',
  'cold wallet','bitbank','mexc','crypto.com','hot','cold',
  'hitbtc','hit btc','poloniex','gemini','bitget','lbank','whitebit',
  'phemex','bitmart','digifinex','xt.com','latoken','probit',
];

function getLabel(addr) {
  if (!addr) return { label: '', type: 'unknown' };
  const lo = addr.toLowerCase();
  const found = LABEL_DB[lo] || LABEL_DB[addr];
  if (found) return { label: found, type: 'exchange' };
  return { label: '', type: 'unknown' };
}

function isExchange(label) {
  if (!label) return false;
  const l = label.toLowerCase();
  return EX_KEYWORDS.some(k => l.includes(k));
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

// ══ マルチホップ追跡 ══════════════════════════════════════════

// 時刻文字列を安全にISO形式へ正規化（末尾Zの重複を防ぐ）
function normalizeTimeStr(t) {
  if (!t) return t;
  if (typeof t === 'string') {
    return t.replace(' ', 'T').replace(/Z+$/, '') + 'Z';
  }
  return t;
}

async function getNextTxBTC(addr, afterTime) {
  try {
    const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txHashes = j.data?.[addr]?.transactions || [];
    const normalizedTime = normalizeTimeStr(afterTime);
    const refMs = new Date(normalizedTime).getTime();

    for (const txHash of txHashes.slice(0, 8)) {
      await new Promise(res => setTimeout(res, 250));
      try {
        const tr = await fetch(`https://api.blockchair.com/bitcoin/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
        const tj = await tr.json();
        const tdata = tj.data?.[txHash];
        if (!tdata) continue;
        const inputs  = tdata.inputs  || [];
        const outputs = tdata.outputs || [];
        const isOutgoing = inputs.some(i => i.recipient === addr);
        if (!isOutgoing) continue;
        const txNorm = tdata.transaction.time.replace(' ', 'T') + 'Z';
        const txMs = new Date(txNorm).getTime();
        if (txMs < refMs - 3600000) continue;
        const target = outputs.filter(o => o.recipient !== addr)
          .sort((a, b) => b.value - a.value)[0];
        if (!target) continue;
        return { addr: target.recipient, amount: target.value / 1e8, time: tdata.transaction.time, txHash };
      } catch { continue; }
    }
  } catch (e) { console.error('getNextTxBTC:', e.message); }
  return null;
}

async function getNextTxETH(addr, afterTime) {
  const normalizedTime = normalizeTimeStr(afterTime);
  const refMs = new Date(normalizedTime).getTime();
  console.log(`[HOP] ETH追跡: ${addr} / 基準時刻: ${isNaN(refMs) ? '(不明)' : new Date(refMs).toISOString()}`);

  // ── Method 1: Etherscan 通常TX ──────────────────────────
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${addr}&startblock=0&endblock=latest&page=1&offset=100&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Etherscan TX件数: ${txs.length}, status: ${j.status}, msg: ${j.message}`);
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      const db = getLabel(tx.to);
      console.log(`[HOP] ETH送金先発見: ${tx.to} (${db.label || 'unknown'})`);
      return { addr: tx.to, amount: parseFloat(tx.value)/1e18, time: new Date(txMs).toISOString(), txHash: tx.hash, label: db.label||'' };
    }
  } catch(e) { console.error('[HOP] Etherscan ETH error:', e.message); }

  // ── Method 2: Etherscan ERC-20（USDT/USDC等）──────────
  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=tokentx&address=${addr}&startblock=0&endblock=latest&page=1&offset=50&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Etherscan ERC20件数: ${txs.length}`);
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      const db = getLabel(tx.to);
      const dec = parseInt(tx.tokenDecimal) || 18;
      console.log(`[HOP] ERC20送金先発見: ${tx.to} token:${tx.tokenSymbol}`);
      return { addr: tx.to, amount: parseFloat(tx.value)/Math.pow(10,dec), time: new Date(txMs).toISOString(), txHash: tx.hash, label: db.label||'', token: tx.tokenSymbol };
    }
  } catch(e) { console.error('[HOP] Etherscan ERC20 error:', e.message); }

  // ── Method 3: Blockchair（フォールバック）──────────────
  try {
    const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}&limit=10`;
    const r = await fetch(url);
    const j = await r.json();
    const txHashes = j.data?.[addr.toLowerCase()]?.transactions || [];
    console.log(`[HOP] Blockchair TX件数: ${txHashes.length}`);
    for (const txHash of txHashes.slice(0, 8)) {
      await new Promise(res => setTimeout(res, 300));
      const tr = await fetch(`https://api.blockchair.com/ethereum/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
      const tj = await tr.json();
      const txData = tj.data?.[txHash.toLowerCase()];
      if (!txData) continue;
      const tx = txData.transaction;
      if (tx.sender?.toLowerCase() !== addr.toLowerCase()) continue;
      const txNorm = tx.time.replace(' ', 'T') + 'Z';
      if (new Date(txNorm).getTime() < refMs) continue;
      const db  = getLabel(tx.recipient);
      const lbl = db.label || tx.recipient_label || '';
      console.log(`[HOP] Blockchair送金先発見: ${tx.recipient} (${lbl})`);
      return { addr: tx.recipient, amount: parseFloat(tx.value)/1e18, time: tx.time, txHash, label: lbl };
    }
  } catch(e) { console.error('[HOP] Blockchair ETH error:', e.message); }

  console.log(`[HOP] ${addr} → 次のTXが見つかりませんでした`);
  return null;
}

async function getNextTxXRP(addr, afterTime) {
  try {
    const r = await fetch(`https://api.xrpscan.com/api/v1/account/${addr}/transactions`);
    const j = await r.json();
    const txs = (j.transactions || j || []);
    const refMs = new Date(afterTime).getTime();
    for (const tx of txs) {
      if (tx.Account !== addr) continue;
      const txMs = new Date(tx.date).getTime();
      if (txMs < refMs - 1000) continue;
      const db = getLabel(tx.Destination);
      return { addr: tx.Destination, amount: parseFloat(tx.Amount) / 1e6, time: tx.date, txHash: tx.hash, label: db.label || '' };
    }
  } catch (e) { console.error('getNextTxXRP:', e.message); }
  return null;
}

async function traceHops(startAddr, startTime, chain, maxHops = 3) {
  const hops = [];
  let currentAddr = startAddr;
  let currentTime = startTime;

  for (let i = 0; i < maxHops; i++) {
    let next = null;
    if (chain === 'btc') next = await getNextTxBTC(currentAddr, currentTime);
    else if (chain === 'eth') next = await getNextTxETH(currentAddr, currentTime);
    else if (chain === 'xrp') next = await getNextTxXRP(currentAddr, currentTime);
    if (!next) break;

    const db  = getLabel(next.addr);
    const lbl = db.label || next.label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    hops.push({ address: next.addr, label: lbl, amount: next.amount, isExchange: isEx, time: next.time, txHash: next.txHash });
    if (isEx) break;
    currentAddr = next.addr;
    currentTime = next.time;
  }
  return hops;
}

// ══ ブロックチェーン調査 ══════════════════════════════════════

async function investigateBTC(txid) {
  const url  = `https://api.blockchair.com/bitcoin/dashboards/transaction/${txid}?key=${BLOCKCHAIR_KEY}`;
  const r    = await fetch(url);
  const j    = await r.json();
  const data = j.data?.[txid];
  if (!data) throw new Error('BTC TXが見つかりません');

  const tx      = data.transaction;
  const inputs  = data.inputs  || [];
  const outputs = data.outputs || [];

  const senderAddr  = inputs[0]?.recipient || '不明';
  const senderLabel = getLabel(senderAddr);
  const changeAddrs = new Set(inputs.map(i => i.recipient));

  const path = [];
  const exchanges = [];

  for (const out of outputs) {
    if (changeAddrs.has(out.recipient)) continue;
    const db  = getLabel(out.recipient);
    const lbl = db.label || out.recipient_label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    path.push({ address: out.recipient, label: lbl, amount: out.value / 1e8, isExchange: isEx });
    if (isEx) exchanges.push({ name: lbl, address: out.recipient, amount: out.value / 1e8 });
  }

  if (exchanges.length === 0 && path.length > 0) {
    const trackAddr = path[0].address;
    const hops = await traceHops(trackAddr, tx.time, 'btc', 3);
    for (const hop of hops) {
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }

  return {
    chain: 'BTC', txid,
    blockTime: tx.time, blockHeight: tx.block_id,
    amount: tx.output_total / 1e8, fee: tx.fee / 1e8,
    sender: senderAddr, senderLabel: senderLabel.label,
    path, exchanges,
  };
}

async function investigateETH(hash) {
  const h    = hash.startsWith('0x') ? hash : '0x' + hash;
  const url  = `https://api.blockchair.com/ethereum/dashboards/transaction/${h}?key=${BLOCKCHAIR_KEY}`;
  const r    = await fetch(url);
  const j    = await r.json();
  const data = j.data?.[h.toLowerCase()];
  if (!data) throw new Error('ETH TXが見つかりません');

  const tx    = data.transaction;
  const calls = data.calls || [];

  const senderDb = getLabel(tx.sender);
  const recipDb  = getLabel(tx.recipient);
  const recipLbl = recipDb.label || tx.recipient_label || '';
  const isRecipEx = recipDb.type === 'exchange' || isExchange(recipLbl);

  const path = [
    { address: tx.sender,    label: senderDb.label || tx.sender_label || '', role: 'sender' },
    { address: tx.recipient, label: recipLbl, role: 'recipient', isExchange: isRecipEx },
  ];
  const exchanges = [];
  if (isRecipEx) exchanges.push({ name: recipLbl, address: tx.recipient, amount: parseFloat(tx.value) / 1e18 });

  for (const call of calls) {
    const db  = getLabel(call.recipient);
    const lbl = db.label || call.recipient_label || '';
    if (db.type === 'exchange' || isExchange(lbl)) {
      exchanges.push({ name: lbl, address: call.recipient, amount: parseFloat(call.value || '0') / 1e18 });
      path.push({ address: call.recipient, label: lbl, role: 'internal', isExchange: true });
    }
  }

  if (exchanges.length === 0) {
    const hops = await traceHops(tx.recipient, tx.time, 'eth', 3);
    for (const hop of hops) {
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }

  return {
    chain: 'ETH', txid: h,
    blockTime: tx.time, blockHeight: tx.block_id,
    amount: parseFloat(tx.value) / 1e18, fee: (tx.gas_used * tx.gas_price) / 1e18,
    sender: tx.sender, senderLabel: senderDb.label,
    recipient: tx.recipient, path, exchanges,
  };
}

async function investigateXRP(txid) {
  const h = txid.toUpperCase();
  const r = await fetch(`https://api.xrpscan.com/api/v1/tx/${h}`);
  const t = await r.text();
  if (t === 'Not found') throw new Error('XRP TXが見つかりません');
  const tx = JSON.parse(t);

  const senderDb = getLabel(tx.Account);
  const destDb   = getLabel(tx.Destination);
  const destLbl  = destDb.label || tx.destinationName || '';
  const isDestEx = destDb.type === 'exchange' || isExchange(destLbl);

  const path = [
    { address: tx.Account,     label: senderDb.label, role: 'sender' },
    { address: tx.Destination, label: destLbl, role: 'recipient', isExchange: isDestEx },
  ];
  const exchanges = isDestEx ? [{ name: destLbl, address: tx.Destination, amount: parseFloat(tx.Amount) / 1e6 }] : [];

  if (exchanges.length === 0) {
    const hops = await traceHops(tx.Destination, tx.date, 'xrp', 3);
    for (const hop of hops) {
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }

  return {
    chain: 'XRP', txid: h,
    blockTime: tx.date, blockHeight: tx.ledger_index,
    amount: parseFloat(tx.Amount) / 1e6,
    sender: tx.Account, senderLabel: senderDb.label,
    recipient: tx.Destination, destTag: tx.DestinationTag,
    path, exchanges,
  };
}

async function investigate(txid, chain) {
  if (chain === 'btc') return investigateBTC(txid);
  if (chain === 'eth') return investigateETH(txid);
  if (chain === 'xrp') return investigateXRP(txid);
  throw new Error('未対応チェーン');
}

// ══ レポート生成 ══════════════════════════════════════════════

function fmtDate(d) {
  if (!d) return '不明';
  try {
    const s = typeof d === 'string'
      ? d.replace(' ', 'T').replace(/Z?$/, 'Z').replace('ZZ', 'Z')
      : d;
    const dt = new Date(s);
    if (isNaN(dt.getTime())) return '不明';
    return dt.toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
  } catch (e) {
    return '不明';
  }
}

function buildReport(result) {
  const em      = { BTC: '₿', ETH: 'Ξ', XRP: '✕' }[result.chain] || '🔗';
  const txShort = result.txid.slice(0, 10) + '...' + result.txid.slice(-6);

  const pathLines = (result.path || []).map((p, i) => {
    const addrShort = p.address.slice(0, 10) + '...' + p.address.slice(-6);
    const lbl = p.label ? ` [${p.label}]` : '';
    if (i === 0) return `🔴 被害者ウォレット\n   ${addrShort}${lbl}`;
    const timeStr   = p.time ? `\n   📅 ${fmtDate(p.time)}` : '';
    const amountStr = (p.amount != null && !isNaN(p.amount) && p.amount > 0)
      ? `\n   💰 ${p.amount.toFixed(6)} ${p.token || result.chain}` : '';
    if (p.isExchange) return `🏦 取引所到達（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}`;
    return `🔵 中継アドレス（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}`;
  });
  const pathText = pathLines.join('\n　↓\n');

  let exSection = '';
  let tplSection = '';

  if (result.exchanges && result.exchanges.length > 0) {
    const ex = result.exchanges[0];
    exSection = `
🏦 判明した取引所
━━━━━━━━━━━━━━━━━
取引所名：${ex.name || '特定済み'}
アドレス：${ex.address.slice(0, 12)}...${ex.address.slice(-6)}
着金額　：${(ex.amount != null && !isNaN(ex.amount)) ? ex.amount.toFixed(8) : '不明'} ${result.chain}`;

    tplSection = `

📝 取引所への要請テンプレート
━━━━━━━━━━━━━━━━━
【${ex.name || '取引所'} サポートチームへ】

件名：不正送金に関する緊急凍結要請

拝啓

不正な仮想通貨送金について緊急のご対応をお願いいたします。

■ トランザクションID
${result.txid}

■ チェーン：${result.chain}
■ 送金日時（JST）：${fmtDate(result.blockTime)}
■ 送金額：${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}
■ 着金アドレス：${ex.address}

上記は詐欺被害に起因する不正送金の疑いがあります。
①上記アドレスの凍結措置
②関連する取引情報の保全
について緊急のご対応をお願い申し上げます。

敬具
━━━━━━━━━━━━━━━━━`;
  } else {
    exSection = `
⚠️ 取引所判定
━━━━━━━━━━━━━━━━━
送金先は既知の取引所DBに一致しませんでした。
追加追跡が必要な場合はご連絡ください。`;
  }

  return `📊 BitTo 調査レポート
━━━━━━━━━━━━━━━━━
${em} チェーン：${result.chain}
🔗 TXID：${txShort}
📅 送金日時：${fmtDate(result.blockTime)}
💰 送金額：${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}${(result.fee != null && !isNaN(result.fee)) ? `\n⛽ 手数料：${result.fee.toFixed(8)} ${result.chain}` : ''}${result.destTag != null ? `\n🏷 宛先タグ：${result.destTag}` : ''}

📍 送金経路
━━━━━━━━━━━━━━━━━
${pathText}
${exSection}${tplSection}

🔒 BitTo が自動生成したレポートです`;
}

// ══ Stripe 決済 ══════════════════════════════════════════════

async function createCheckoutSession(userId, txid, chain) {
  const sessionId = crypto.randomUUID();
  pendingSessions.set(sessionId, { userId, txid, chain, createdAt: Date.now() });

  const session = await stripe.checkout.sessions.create({
    payment_method_types: ['card'],
    line_items: [{
      price_data: {
        currency: 'jpy',
        product_data: {
          name:        'BitTo ブロックチェーン調査レポート',
          description: `${chain.toUpperCase()} TXID: ${txid.slice(0, 20)}...`,
        },
        unit_amount: 6600,
      },
      quantity: 1,
    }],
    mode: 'payment',
    // 住所・電話番号をStripe側で収集
    billing_address_collection: 'required',
    phone_number_collection: { enabled: true },
    // 規約への同意チェックボックス
    consent_collection: { terms_of_service: 'required' },
    success_url: `${BASE_URL}/payment/success?sid=${sessionId}`,
    cancel_url:  `${BASE_URL}/payment/cancel`,
    metadata: { sessionId, userId, txid, chain },
  });

  pendingSessions.set(sessionId, { userId, txid, chain, stripeId: session.id, createdAt: Date.now() });
  return { url: session.url, sessionId };
}

// ══ 利用規約テキスト ════════════════════════════════════════
const TOS_TEXT = `📋 BitTo 調査サービス 利用規約
━━━━━━━━━━━━━━━━━
■ サービス内容
ブロックチェーン公開データを解析し
送金先取引所を特定する調査サービスです

■ 料金
・送金経路・取引所特定：無料
・詳細調査レポート：¥6,600（税込）

■ 返金について
本サービスはデジタル調査コンテンツの
提供のため、調査開始後の返金は
いたしかねます

・取引所への凍結・資金回収を
　保証するものではありません
・調査結果に法的効力はありません
・結果に関わらず返金対応は行いません

■ 免責事項
・全追跡の成功を保証しません
・取引所の対応結果は当社管理外です
・本レポートは被害申告・警察相談の
　参考資料としてご活用ください

■ 個人情報の取扱い
収集情報は調査業務のみに使用し
第三者への提供はしません
━━━━━━━━━━━━━━━━━
上記に同意される場合は

「同意する」

とご返信ください`;

// ══ LINE 会話フロー ══════════════════════════════════════════

const HELP_TEXT = `📋 BitTo 使い方ガイド
━━━━━━━━━━━━━━━━━
詐欺被害に遭われた場合、TXIDを
もとに送金先取引所を自動追跡します

💬 ご利用方法
まずメッセージを送ってください
順番にご案内します

対応チェーン：
₿ Bitcoin (BTC)
Ξ Ethereum (ETH)
✕ XRP Ledger (XRP)

💴 料金
・送金経路・取引所特定：無料
・詳細レポート：¥6,600（税込）

「リセット」で最初からやり直し`;

// 調査をバックグラウンドで実行し、完了後にLINEへpush
async function runInvestigation(userId, txid, chain) {
  const session = getSession(userId);
  const cacheKey = txid.toLowerCase();

  try {
    // キャッシュ確認（同じTXIDは再調査しない）
    let result = txidCache.get(cacheKey)?.result;
    if (result) {
      console.log(`[CACHE] キャッシュ利用: ${txid}`);
    } else {
      result = await investigate(txid, chain);
      txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
    }

    session.investigationResult = result;

    // 無料調査結果を通知
    const exName = result.exchanges?.[0]?.name || null;
    const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger' }[chain];
    const summaryMsg = exName
      ? `✅ 送金先取引所を特定しました\n\nチェーン：${chainName}\n取引所名：${exName}\n送金日時：${fmtDate(result.blockTime)}\n\n詳細レポートを取得するには\n次の手続きにお進みください`
      : `🔍 送金経路の追跡が完了しました\n\nチェーン：${chainName}\n送金日時：${fmtDate(result.blockTime)}\n取引所：DBに一致なし\n\n詳細レポートでさらに詳しく\n調査いたします`;

    await lineClient.pushMessage(userId, { type: 'text', text: summaryMsg });

    // 利用規約を送付
    session.state = 'tos';
    await lineClient.pushMessage(userId, { type: 'text', text: TOS_TEXT });

  } catch (e) {
    console.error('[調査エラー]', e.message);
    session.state = 'h_txid';
    await lineClient.pushMessage(userId, {
      type: 'text',
      text: `⚠️ 調査中にエラーが発生しました\n\n${e.message}\n\nTXIDをご確認の上、再度送ってください`,
    });
  }
}

async function handleLineEvent(event) {
  if (event.type !== 'message' || event.message.type !== 'text') return;

  const userId  = event.source.userId;
  const text    = event.message.text.trim();
  const session = getSession(userId);

  // ── グローバルコマンド（どの状態でも反応） ──────────────
  if (['ヘルプ', 'help', '？', '?'].includes(text.toLowerCase())) {
    return lineClient.replyMessage(event.replyToken, { type: 'text', text: HELP_TEXT });
  }
  if (['リセット', 'reset', 'やり直し', 'やりなおし'].includes(text.toLowerCase())) {
    resetSession(userId);
    return lineClient.replyMessage(event.replyToken, {
      type: 'text',
      text: '🔄 最初からやり直します\n\nご相談内容をお聞きします\n\n① お名前を教えてください',
    });
  }

  // ── 状態別ハンドラ ──────────────────────────────────────
  switch (session.state) {

    // ── 最初のメッセージ ──────────────────────────────────
    case 'idle': {
      session.state = 'h_name';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `ご相談ありがとうございます。\n順番にお聞きします。\n\n① お名前を教えてください`,
      });
    }

    // ── ① 名前 ────────────────────────────────────────────
    case 'h_name': {
      session.hearingName = text;
      session.state = 'h_damage';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `② 被害を受けた通貨と金額を教えてください\n例：ETH 2.5枚 / BTC 0.1 / USDT 50,000`,
      });
    }

    // ── ② 被害金額・通貨 ──────────────────────────────────
    case 'h_damage': {
      session.damage = text;
      session.state = 'h_reason';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `③ 被害の経緯を簡単に教えてください`,
      });
    }

    // ── ③ 経緯 ────────────────────────────────────────────
    case 'h_reason': {
      session.reason = text;
      session.state = 'h_txid';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `④ 調査するTXID（トランザクションID）を送ってください\n\n対応：BTC / ETH / XRP`,
      });
    }

    // ── ④ TXID受信 → 無料調査 ────────────────────────────
    case 'h_txid': {
      const chain = detectChain(text);
      if (!chain) {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `TXIDを認識できませんでした\n\nBTC / ETH / XRP のTXIDを送ってください\n（ETH: 0xから始まる66文字）`,
        });
      }

      // 同じユーザーが同じTXIDで決済済み → レポート再送
      if (
        session.paidAt &&
        session.txid &&
        session.txid.toLowerCase() === text.toLowerCase() &&
        session.reportResult
      ) {
        await lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `このTXIDはすでに調査済みです\n\n📄 レポートを再送します`,
        });
        await lineClient.pushMessage(userId, { type: 'text', text: buildReport(session.reportResult) });
        return;
      }

      // 同じユーザーが同じTXIDで調査済み（未決済）→ 結果と決済リンクを再表示
      if (
        session.txid &&
        session.txid.toLowerCase() === text.toLowerCase() &&
        session.investigationResult &&
        !session.paidAt
      ) {
        await lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `このTXIDはすでに調査済みです\n\n詳細レポートの決済にお進みください\n利用規約を再度ご確認ください`,
        });
        session.state = 'tos';
        await lineClient.pushMessage(userId, { type: 'text', text: TOS_TEXT });
        return;
      }

      // 新しいTXID → 調査開始
      session.txid  = text;
      session.chain = chain;
      session.investigationResult = null;
      session.state = 'investigating';

      const chainName = { btc: 'Bitcoin', eth: 'Ethereum', xrp: 'XRP Ledger' }[chain];
      const txShort   = text.slice(0, 10) + '...' + text.slice(-6);

      // キャッシュにある場合は「調査済みデータを使用」と通知
      const cacheKey = text.toLowerCase();
      const cached   = txidCache.get(cacheKey);
      const waitMsg  = cached
        ? `🔍 ${chainName} のTXIDを受け付けました\nTXID：${txShort}\n\n⚡ 過去の調査データを取得中...`
        : `🔍 ${chainName} のTXIDを受け付けました\nTXID：${txShort}\n\n⚙️ 送金経路を追跡中です...\n通常30秒〜2分かかります\nしばらくお待ちください`;

      await lineClient.replyMessage(event.replyToken, { type: 'text', text: waitMsg });

      // バックグラウンドで調査実行（awaitしない）
      runInvestigation(userId, text, chain).catch(console.error);
      return;
    }

    // ── 調査実行中 ────────────────────────────────────────
    case 'investigating': {
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `⚙️ ただいま調査中です\nしばらくお待ちください\n\n完了次第、結果をお送りします`,
      });
    }

    // ── 利用規約への同意待ち ──────────────────────────────
    case 'tos': {
      if (text !== '同意する') {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `「同意する」とご返信いただくと\n次のステップに進めます\n\n同意されない場合、\nレポートの作成ができません`,
        });
      }

      // 同意済み → 決済リンク作成
      if (!stripe) {
        // テストモード（Stripe未設定）→ 直接レポート送付
        session.state = 'paid';
        session.paidAt = Date.now();
        session.reportResult = session.investigationResult;
        await lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `✅ 同意を確認しました\n\n📄 レポートを生成中...`,
        });
        if (session.investigationResult) {
          await lineClient.pushMessage(userId, { type: 'text', text: buildReport(session.investigationResult) });
        }
        return;
      }

      try {
        const payment = await createCheckoutSession(userId, session.txid, session.chain);
        session.state = 'awaiting_payment';
        const txShort = session.txid.slice(0, 10) + '...' + session.txid.slice(-6);
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `✅ 同意を確認しました\n\n💳 お支払いページ\n${payment.url}\n\nTXID：${txShort}\n料金：¥6,600（税込）\n\n※ お支払いページにて\n　 お名前・住所・電話番号を\n　 ご入力ください\n\nお支払い完了後、自動でレポートを\nお送りします`,
        });
      } catch (e) {
        return lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `⚠️ 決済リンクの生成に失敗しました\n${e.message}\n\nしばらく後に「同意する」と\n再度送ってください`,
        });
      }
    }

    // ── 決済待ち ──────────────────────────────────────────
    case 'awaiting_payment': {
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `💳 お支払いをお待ちしています\n\nお支払い完了後、自動でレポートを\nお送りします\n\nキャンセルする場合は\n「リセット」と送ってください`,
      });
    }

    // ── 決済済み ──────────────────────────────────────────
    case 'paid': {
      // 同じTXIDを送ってきた → レポート再送
      const chain = detectChain(text);
      if (chain && session.txid && text.toLowerCase() === session.txid.toLowerCase()) {
        await lineClient.replyMessage(event.replyToken, {
          type: 'text',
          text: `📄 以前のレポートを再送します`,
        });
        if (session.reportResult) {
          await lineClient.pushMessage(userId, { type: 'text', text: buildReport(session.reportResult) });
        }
        return;
      }
      // 別のTXID or メッセージ → 新規ヒアリング開始
      resetSession(userId);
      const ns = getSession(userId);
      ns.state = 'h_name';
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `新しいご相談ですね\n\n① お名前を教えてください`,
      });
    }

    // ── 想定外の状態 ──────────────────────────────────────
    default: {
      resetSession(userId);
      return lineClient.replyMessage(event.replyToken, {
        type: 'text',
        text: `ご相談ありがとうございます\n\n① お名前を教えてください`,
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
      const { sessionId, userId, txid, chain } = s.metadata;
      const userSession = getSession(userId);

      try {
        await lineClient.pushMessage(userId, {
          type: 'text',
          text: '✅ お支払いを確認しました！\n\n📄 レポートを生成中...\n通常1〜2分でお届けします',
        });

        // キャッシュ優先、なければ再調査
        const cacheKey = txid.toLowerCase();
        let result = txidCache.get(cacheKey)?.result || userSession.investigationResult;
        if (!result) {
          result = await investigate(txid, chain);
          txidCache.set(cacheKey, { result, investigatedAt: Date.now() });
        }

        const reportText = buildReport(result);
        await lineClient.pushMessage(userId, { type: 'text', text: reportText });

        // セッション更新
        userSession.state        = 'paid';
        userSession.paidAt       = Date.now();
        userSession.reportResult = result;
        pendingSessions.delete(sessionId);

      } catch (e) {
        console.error('レポート生成エラー:', e);
        await lineClient.pushMessage(userId, {
          type: 'text',
          text: `⚠️ レポート生成エラー\n${e.message}\n\nサポートにご連絡ください`,
        });
      }
    }
    res.json({ received: true });
  }
);

// 決済完了・キャンセルページ
app.get('/payment/success', (_req, res) => res.send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>決済完了 — BitTo</title>
<style>body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:40px;max-width:380px}
h1{color:#34d399;font-size:1.5rem;margin-bottom:12px}.icon{font-size:3rem;margin-bottom:16px}p{color:#94a3b8;line-height:1.6}</style></head>
<body><div class="card"><div class="icon">✅</div><h1>決済が完了しました</h1>
<p>レポートを生成中です。<br>LINEにレポートをお送りしますので<br>しばらくお待ちください。</p></div></body></html>`));

app.get('/payment/cancel', (_req, res) => res.send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>キャンセル — BitTo</title>
<style>body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:40px;max-width:380px}
h1{color:#f87171;font-size:1.5rem;margin-bottom:12px}.icon{font-size:3rem;margin-bottom:16px}p{color:#94a3b8;line-height:1.6}</style></head>
<body><div class="card"><div class="icon">❌</div><h1>キャンセルされました</h1>
<p>調査を再開する場合は<br>LINEで「同意する」と再度<br>ご返信ください。</p></div></body></html>`));

// LINE Webhook
app.post('/webhook', line.middleware(lineConfig), async (req, res) => {
  res.json({ ok: true });
  await Promise.all(req.body.events.map(handleLineEvent)).catch(console.error);
});

app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ── REST API（ChainTrace UI用）────────────────────────────
app.get('/api/status', (_req, res) => res.json({
  ok: true,
  mode: stripe ? 'production' : 'test（Stripeなし）',
  keys: { blockchair: !!BLOCKCHAIR_KEY, etherscan: !!ETHERSCAN_KEY, gemini: !!GEMINI_KEY, line: !!LINE_CHANNEL_ACCESS_TOKEN, stripe: !!stripe },
  webhook: `${BASE_URL}/webhook`,
}));

app.get('/api/btc/tx/:txid', async (req, res) => {
  try { const r = await fetch(`https://api.blockchair.com/bitcoin/dashboards/transaction/${req.params.txid}?key=${BLOCKCHAIR_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/btc/address/:addr', async (req, res) => {
  try { const r = await fetch(`https://api.blockchair.com/bitcoin/dashboards/address/${req.params.addr}?key=${BLOCKCHAIR_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/tx/:hash', async (req, res) => {
  try { const h = req.params.hash.startsWith('0x') ? req.params.hash : '0x' + req.params.hash;
    const r = await fetch(`https://api.blockchair.com/ethereum/dashboards/transaction/${h}?key=${BLOCKCHAIR_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/address/:addr', async (req, res) => {
  try { const r = await fetch(`https://api.blockchair.com/ethereum/dashboards/address/${req.params.addr}?key=${BLOCKCHAIR_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/txlist/:addr', async (req, res) => {
  try {
    const { page = 1, offset = 20, sort = 'desc' } = req.query;
    const r = await fetch(`https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${req.params.addr}&startblock=0&endblock=latest&page=${page}&offset=${offset}&sort=${sort}&apikey=${ETHERSCAN_KEY}`);
    res.json(await r.json());
  } catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/label/:addr', async (req, res) => {
  try { const r = await fetch(`https://api.etherscan.io/v2/api?chainid=1&module=contract&action=getsourcecode&address=${req.params.addr}&apikey=${ETHERSCAN_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/eth/balance/:addr', async (req, res) => {
  try { const r = await fetch(`https://api.etherscan.io/v2/api?chainid=1&module=account&action=balance&address=${req.params.addr}&tag=latest&apikey=${ETHERSCAN_KEY}`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/xrp/tx/:txid', async (req, res) => {
  try { const r = await fetch(`https://api.xrpscan.com/api/v1/tx/${req.params.txid.toUpperCase()}`);
    const t = await r.text(); if (t === 'Not found') return res.status(404).json({ error: 'Not found' }); res.json(JSON.parse(t)); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.get('/api/xrp/address/:addr', async (req, res) => {
  try { const r = await fetch(`https://api.xrpscan.com/api/v1/account/${req.params.addr}/transactions`); res.json(await r.json()); }
  catch (e) { res.status(500).json({ error: e.message }); }
});
app.post('/api/ai/analyze', async (req, res) => {
  try {
    const { prompt } = req.body;
    if (!prompt) return res.status(400).json({ error: 'promptが必要です' });
    const r = await fetch(`https://generativelanguage.googleapis.com/v1/models/gemini-2.0-flash:generateContent?key=${GEMINI_KEY}`, {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ contents: [{ parts: [{ text: prompt }] }], generationConfig: { temperature: 0.2, maxOutputTokens: 1000 } }),
    });
    const j = await r.json();
    if (!r.ok) return res.status(r.status).json({ error: j.error?.message });
    res.json({ text: j.candidates?.[0]?.content?.parts?.[0]?.text || '' });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

app.get('*', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));

// ── サーバー起動 ────────────────────────────────────────────
app.listen(PORT, () => {
  console.log(`\n✅ BitTo サーバー起動完了`);
  console.log(`🌐 http://localhost:${PORT}`);
  console.log(`📡 LINE Webhook: ${BASE_URL}/webhook`);
  console.log(`🔑 Blockchair : ${BLOCKCHAIR_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 LINE       : ${LINE_CHANNEL_ACCESS_TOKEN ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Stripe     : ${stripe ? '✓ 本番モード' : '⚠ テストモード（決済スキップ）'}`);
  console.log();
});

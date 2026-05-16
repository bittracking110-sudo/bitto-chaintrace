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
// Railway は RAILWAY_PUBLIC_DOMAIN を自動設定する → https:// を付けて使用
const BASE_URL = process.env.BASE_URL
  || (process.env.RAILWAY_PUBLIC_DOMAIN
      ? `https://${process.env.RAILWAY_PUBLIC_DOMAIN}`
      : `http://localhost:${PORT}`);

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
const userSessions  = new Map(); // userId → session
const txidCache     = new Map(); // txid（小文字）→ { result, investigatedAt }
const pendingSessions = new Map(); // sessionId → { userId, txidCount, stripeId }
const reportCache    = new Map(); // reportId  → { results[], customerName, issuedAt }

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
  // ─── HitBTC ───
  '0x1c4b70a3968436b9a0a9cf5205c787eb81bb558c': 'HitBTC',
  '0x0a98fb70939162725ae863267f8b056e9d890906': 'HitBTC',
  '0xf259869dfc3f3de5e1b2292882e3d59c8f2d1b01': 'HitBTC',
  '0x3d28a7c8d8f4f06b5f60d5855e5a1f6b5f59f95c': 'HitBTC',
  '1KAt6STtisWMMVo63xFER7NnGBBBBMHTNK': 'HitBTC BTC',
  '1GZEgEoAOcMKoqz93MPpFfQpFPDyKi41jh': 'HitBTC BTC',
  // ─── その他 ───
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
  return EX_KEYWORDS.some(k => label.toLowerCase().includes(k));
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
    const r = await fetch(`https://api.coingecko.com/api/v3/simple/price?ids=${ids}&vs_currencies=usd`);
    const j = await r.json();
    const price = j[ids]?.usd || 0;
    priceCache.set(key, { price, ts: Date.now() });
    return price;
  } catch { return 0; }
}

async function getAddressInfo(addr, chain) {
  try {
    if (chain === 'eth') {
      const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const r = await fetch(url);
      const j = await r.json();
      const d = j.data?.[addr.toLowerCase()]?.address;
      if (!d) return null;
      const balNative = parseFloat(d.balance || 0) / 1e18;
      const price     = await getUSDPrice('eth');
      return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price };
    }
    if (chain === 'btc') {
      const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
      const r = await fetch(url);
      const j = await r.json();
      const d = j.data?.[addr]?.address;
      if (!d) return null;
      const balNative = parseFloat(d.balance || 0) / 1e8;
      const price     = await getUSDPrice('btc');
      return { balance: balNative, txCount: d.transaction_count || 0, balanceUSD: balNative * price };
    }
    if (chain === 'xrp') {
      const r = await fetch(`https://api.xrpscan.com/api/v1/account/${addr}`);
      const j = await r.json();
      const balNative = parseFloat(j.xrpBalance || 0);
      const price     = await getUSDPrice('xrp');
      return { balance: balNative, txCount: j.TxCount || 0, balanceUSD: balNative * price };
    }
  } catch (e) { console.error('[AddrInfo]', addr, e.message); }
  return null;
}

async function enrichPathWithAddressInfo(path, chain) {
  for (const node of path) {
    if (!node.address) continue;
    await new Promise(res => setTimeout(res, 250)); // レート制限対策
    const info = await getAddressInfo(node.address, chain);
    if (info) {
      node.balance    = info.balance;
      node.txCount    = info.txCount;
      node.balanceUSD = info.balanceUSD;
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

// ══ マルチホップ追跡 ══════════════════════════════════════════

function normalizeTimeStr(t) {
  if (!t) return t;
  if (typeof t === 'string') return t.replace(' ', 'T').replace(/Z+$/, '') + 'Z';
  return t;
}

async function getNextTxBTC(addr, afterTime) {
  try {
    const url = `https://api.blockchair.com/bitcoin/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txHashes = j.data?.[addr]?.transactions || [];
    const refMs = new Date(normalizeTimeStr(afterTime)).getTime();
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

  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=txlist&address=${addr}&startblock=0&endblock=latest&page=1&offset=100&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    console.log(`[HOP] Etherscan TX: ${txs.length}件`);
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      if (tx.isError === '1') continue;
      const db = getLabel(tx.to);
      console.log(`[HOP] ETH送金先: ${tx.to} (${db.label || 'unknown'})`);
      return { addr: tx.to, amount: parseFloat(tx.value)/1e18, time: new Date(txMs).toISOString(), txHash: tx.hash, label: db.label||'' };
    }
  } catch(e) { console.error('[HOP] Etherscan ETH:', e.message); }

  try {
    const url = `https://api.etherscan.io/v2/api?chainid=1&module=account&action=tokentx&address=${addr}&startblock=0&endblock=latest&page=1&offset=50&sort=asc&apikey=${ETHERSCAN_KEY}`;
    const r = await fetch(url);
    const j = await r.json();
    const txs = Array.isArray(j.result) ? j.result : [];
    for (const tx of txs) {
      const txMs = parseInt(tx.timeStamp) * 1000;
      if (txMs < refMs) continue;
      if (tx.from.toLowerCase() !== addr.toLowerCase()) continue;
      const db = getLabel(tx.to);
      const dec = parseInt(tx.tokenDecimal) || 18;
      return { addr: tx.to, amount: parseFloat(tx.value)/Math.pow(10,dec), time: new Date(txMs).toISOString(), txHash: tx.hash, label: db.label||'', token: tx.tokenSymbol };
    }
  } catch(e) { console.error('[HOP] ERC20:', e.message); }

  try {
    const url = `https://api.blockchair.com/ethereum/dashboards/address/${addr}?key=${BLOCKCHAIR_KEY}&limit=10`;
    const r = await fetch(url);
    const j = await r.json();
    const txHashes = j.data?.[addr.toLowerCase()]?.transactions || [];
    for (const txHash of txHashes.slice(0, 8)) {
      await new Promise(res => setTimeout(res, 300));
      const tr = await fetch(`https://api.blockchair.com/ethereum/dashboards/transaction/${txHash}?key=${BLOCKCHAIR_KEY}`);
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
    const r = await fetch(`https://api.xrpscan.com/api/v1/account/${addr}/transactions`);
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
    const lbl = db.label || out.recipient_label || '';
    const isEx = db.type === 'exchange' || isExchange(lbl);
    path.push({ address: out.recipient, label: lbl, amount: out.value/1e8, isExchange: isEx });
    if (isEx) exchanges.push({ name: lbl, address: out.recipient, amount: out.value/1e8 });
  }
  if (exchanges.length === 0 && path.length > 0) {
    const hops = await traceHops(path[0].address, tx.time, 'btc', 3);
    for (const hop of hops) {
      path.push(hop);
      if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount });
    }
  }
  return { chain: 'BTC', txid, blockTime: tx.time, blockHeight: tx.block_id,
    amount: tx.output_total/1e8, fee: tx.fee/1e8,
    sender: senderAddr, senderLabel: getLabel(senderAddr).label, path, exchanges };
}

async function investigateETH(hash) {
  const h   = hash.startsWith('0x') ? hash : '0x' + hash;
  const url = `https://api.blockchair.com/ethereum/dashboards/transaction/${h}?key=${BLOCKCHAIR_KEY}`;
  const r   = await fetch(url);
  const j   = await r.json();
  const data = j.data?.[h.toLowerCase()];
  if (!data) throw new Error('ETH TXが見つかりません');
  const tx = data.transaction;
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
  if (isRecipEx) exchanges.push({ name: recipLbl, address: tx.recipient, amount: parseFloat(tx.value)/1e18 });
  for (const call of calls) {
    const db = getLabel(call.recipient);
    const lbl = db.label || call.recipient_label || '';
    if (db.type === 'exchange' || isExchange(lbl)) {
      exchanges.push({ name: lbl, address: call.recipient, amount: parseFloat(call.value||'0')/1e18 });
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
  return { chain: 'ETH', txid: h, blockTime: tx.time, blockHeight: tx.block_id,
    amount: parseFloat(tx.value)/1e18, fee: (tx.gas_used * tx.gas_price)/1e18,
    sender: tx.sender, senderLabel: senderDb.label, recipient: tx.recipient, path, exchanges };
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
  const exchanges = isDestEx ? [{ name: destLbl, address: tx.Destination, amount: parseFloat(tx.Amount)/1e6 }] : [];
  if (exchanges.length === 0) {
    const hops = await traceHops(tx.Destination, tx.date, 'xrp', 3);
    for (const hop of hops) { path.push(hop); if (hop.isExchange) exchanges.push({ name: hop.label, address: hop.address, amount: hop.amount }); }
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
    const lbl = p.label ? ` [${p.label}]` : '';
    if (i === 0) return `🔴 被害者ウォレット\n   ${addrShort}${lbl}`;
    const timeStr   = p.time ? `\n   📅 ${fmtDate(p.time)}` : '';
    const amountStr = (p.amount != null && !isNaN(p.amount) && p.amount > 0)
      ? `\n   💰 ${p.amount.toFixed(6)} ${p.token || result.chain}` : '';
    if (p.isExchange) return `🏦 取引所到達（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}`;
    return `🔵 中継アドレス（${i}次先）\n   ${addrShort}${lbl}${timeStr}${amountStr}`;
  });

  let exSection = '';
  let tplSection = '';
  if (result.exchanges && result.exchanges.length > 0) {
    const ex = result.exchanges[0];
    exSection = `\n🏦 判明した取引所\n━━━━━━━━━━━━━━━━━\n取引所名：${ex.name || '特定済み'}\nアドレス：${ex.address.slice(0,12)}...${ex.address.slice(-6)}\n着金額　：${(ex.amount != null && !isNaN(ex.amount)) ? ex.amount.toFixed(8) : '不明'} ${result.chain}`;
    tplSection = `\n\n📝 取引所への要請テンプレート\n━━━━━━━━━━━━━━━━━\n【${ex.name || '取引所'} サポートチームへ】\n\n件名：不正送金に関する緊急凍結要請\n\n拝啓\n\n不正な仮想通貨送金について緊急のご対応をお願いいたします。\n\n■ トランザクションID\n${result.txid}\n\n■ チェーン：${result.chain}\n■ 送金日時（JST）：${fmtDate(result.blockTime)}\n■ 送金額：${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}\n■ 着金アドレス：${ex.address}\n\n上記は詐欺被害に起因する不正送金の疑いがあります。\n①上記アドレスの凍結措置\n②関連する取引情報の保全\nについて緊急のご対応をお願い申し上げます。\n\n敬具\n━━━━━━━━━━━━━━━━━`;
  } else {
    exSection = `\n⚠️ 取引所判定\n━━━━━━━━━━━━━━━━━\n送金先は既知の取引所DBに一致しませんでした。\n追加追跡が必要な場合はご連絡ください。`;
  }

  return `📊 BitTo 調査レポート\n━━━━━━━━━━━━━━━━━\n${em} チェーン：${result.chain}\n🔗 TXID：${txShort}\n📅 送金日時：${fmtDate(result.blockTime)}\n💰 送金額：${(result.amount != null && !isNaN(result.amount)) ? result.amount.toFixed(8) : '不明'} ${result.chain}${(result.fee != null && !isNaN(result.fee)) ? `\n⛽ 手数料：${result.fee.toFixed(8)} ${result.chain}` : ''}${result.destTag != null ? `\n🏷 宛先タグ：${result.destTag}` : ''}\n\n📍 送金経路\n━━━━━━━━━━━━━━━━━\n${pathLines.join('\n　↓\n')}\n${exSection}${tplSection}\n\n🔒 BitTo が自動生成したレポートです`;
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
      ? `<br/>残高: ${node.balance < 0.0001 ? node.balance.toFixed(6) : node.balance.toFixed(4)} ${chain}` : '';
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

function generateReportHTML(results, customerName, issuedAt) {
  const chainFull = { BTC: 'Bitcoin', ETH: 'Ethereum', XRP: 'XRP Ledger' };

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
      if (i === 0)       { cls = 'victim';   icon = '●'; roleLabel = '被害者ウォレット'; }
      else if (p.isExchange) { cls = 'exchange'; icon = '★'; roleLabel = `取引所到達（${i}次先）`; }
      else               { cls = 'relay';    icon = '◆'; roleLabel = `中継アドレス（${i}次先）`; }

      const exBadge  = p.label ? `<span class="badge">${p.label}</span>` : '';
      const timeTd   = p.time ? `<div class="node-meta">📅 ${fmtDate(p.time)}</div>` : '';
      const amtTd    = (p.amount != null && !isNaN(p.amount) && p.amount > 0)
        ? `<div class="node-meta">💸 送金額: ${p.amount.toFixed(8)} ${p.token || r.chain}</div>` : '';
      const usdStr   = (p.balanceUSD != null && !isNaN(p.balanceUSD))
        ? ` <span class="usd-val">≈ $${p.balanceUSD < 1 ? p.balanceUSD.toFixed(4) : p.balanceUSD.toLocaleString('en-US',{maximumFractionDigits:2})}</span>` : '';
      const balTd    = (p.balance != null && !isNaN(p.balance))
        ? `<div class="node-meta">💰 残高: ${p.balance < 0.0001 ? p.balance.toFixed(8) : p.balance.toFixed(4)} ${r.chain}${usdStr}</div>` : '';
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
    let exHTML = '<p class="no-ex">送金先は既知の取引所DBに一致しませんでした。</p>';
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
■ 送金額：${(r.amount != null && !isNaN(r.amount)) ? r.amount.toFixed(8) : '不明'} ${r.chain}
■ 着金アドレス：${ex.address}

上記は詐欺被害に起因する不正送金の疑いがあります。
以下について緊急のご対応をお願い申し上げます。

① 上記アドレスの即時凍結措置
② 関連する取引情報・KYC情報の保全
③ 当局への情報提供へのご協力

敬具</div>`;
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
          <tr><th>送金額</th><td>${(r.amount != null && !isNaN(r.amount)) ? r.amount.toFixed(8) : '不明'} ${r.chain}</td></tr>
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

        <h3>🏦 取引所判定</h3>
        ${exHTML}
        ${tplHTML}
      </section>`;
  }).join('');

  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>BitTo 詳細調査レポート</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:'Hiragino Kaku Gothic Pro','Meiryo',sans-serif;background:#f4f5f7;color:#1a1a2e;padding:24px 16px 60px;font-size:14px}
    .container{max-width:760px;margin:0 auto}
    /* カバー */
    .cover{background:#1a1a2e;color:#fff;border-radius:12px;padding:32px;margin-bottom:24px;display:flex;justify-content:space-between;align-items:flex-start;gap:16px}
    .cover-left h1{font-size:1.5rem;margin-bottom:4px}
    .cover-left p{color:#94a3b8;font-size:0.85rem}
    .cover-meta{text-align:right;font-size:0.82rem;color:#94a3b8;line-height:1.8}
    .cover-meta strong{color:#e2e8f0;display:block}
    /* セクション */
    .tx-section{background:#fff;border:1px solid #e2e8f0;border-radius:10px;padding:24px;margin-bottom:20px}
    .tx-header{display:flex;align-items:center;gap:10px;margin-bottom:16px;padding-bottom:12px;border-bottom:2px solid #e2e8f0}
    .chain-badge{background:#1a1a2e;color:#fff;padding:4px 12px;border-radius:20px;font-weight:700;font-size:0.9rem}
    .tx-num{color:#64748b;font-size:0.85rem}
    h3{font-size:0.95rem;color:#1a1a2e;margin:20px 0 10px;padding-left:8px;border-left:3px solid #3b82f6}
    h4{font-size:0.88rem;color:#374151}
    /* テーブル */
    .info-table{width:100%;border-collapse:collapse;margin-bottom:8px}
    .info-table th{width:140px;background:#f8fafc;padding:8px 10px;text-align:left;font-size:0.82rem;color:#64748b;border:1px solid #e2e8f0;white-space:nowrap}
    .info-table td{padding:8px 10px;border:1px solid #e2e8f0;font-size:0.85rem;word-break:break-all}
    .info-table a{color:#3b82f6;text-decoration:none}
    .mono{font-family:'Courier New',monospace;font-size:0.78rem;color:#1e3a5f;word-break:break-all}
    /* フローマップ */
    .flow-map{display:flex;flex-direction:column;align-items:center;gap:0;margin:12px 0}
    .flow-node{width:100%;border-radius:10px;padding:14px 16px;border:2px solid}
    .flow-node.victim  {background:#fff5f5;border-color:#fca5a5}
    .flow-node.relay   {background:#eff6ff;border-color:#93c5fd}
    .flow-node.exchange{background:#f0fdf4;border-color:#86efac}
    .node-role{font-weight:700;font-size:0.85rem;margin-bottom:6px;display:flex;align-items:center;gap:6px}
    .node-icon{font-size:0.75rem}
    .flow-node.victim   .node-role{color:#dc2626}
    .flow-node.relay    .node-role{color:#2563eb}
    .flow-node.exchange .node-role{color:#16a34a}
    .node-address{font-family:'Courier New',monospace;font-size:0.77rem;color:#374151;word-break:break-all;background:#fff;border:1px solid #e2e8f0;border-radius:6px;padding:6px 8px;margin-bottom:4px}
    .node-meta{font-size:0.78rem;color:#64748b;margin-top:3px}
    .usd-val{color:#059669;font-size:0.76rem;font-weight:600}
    .badge{background:#1a1a2e;color:#fff;font-size:0.72rem;padding:2px 8px;border-radius:10px;margin-left:6px;font-weight:400}
    .flow-arrow{font-size:1.4rem;color:#94a3b8;margin:4px 0;line-height:1}
    .no-ex{color:#64748b;font-size:0.85rem;padding:10px}
    /* 要請テンプレート */
    .template-box{background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:16px;font-size:0.82rem;white-space:pre-wrap;line-height:1.8;word-break:break-all;margin-top:10px}
    /* 印刷ボタン */
    .print-bar{background:#fff;border:1px solid #e2e8f0;border-radius:10px;padding:16px 20px;margin-bottom:20px;display:flex;align-items:center;justify-content:space-between}
    .print-bar p{font-size:0.83rem;color:#64748b}
    .print-btn{background:#1a1a2e;color:#fff;border:none;border-radius:8px;padding:10px 20px;font-size:0.9rem;font-weight:700;cursor:pointer}
    .print-btn:hover{opacity:0.85}
    /* Mermaid フロー図 */
    .mermaid-wrap{background:#fafbfc;border:1px solid #e2e8f0;border-radius:8px;padding:16px;margin-bottom:8px;overflow-x:auto;text-align:center}
    .mermaid-wrap pre{display:inline-block;text-align:left}
    /* 価格チャート */
    .chart-wrap{background:#fff;border:1px solid #e2e8f0;border-radius:8px;padding:16px;margin-bottom:8px}
    .tx-price-label{font-size:0.82rem;color:#dc2626;font-weight:600;margin-bottom:8px;text-align:right}
    .chart-error{color:#94a3b8;font-size:0.82rem;text-align:center;padding:20px 0}
    .page-break{page-break-before:always}
    @media print{
      body{background:#fff;padding:0}
      .print-bar{display:none}
      .tx-section{border:none;padding:0;margin-bottom:40px}
      .cover{border-radius:0}
    }
  </style>
</head>
<body>
<div class="container">
  <div class="print-bar">
    <p>📄 このページを印刷 → 「PDFとして保存」でPDF化できます</p>
    <button class="print-btn" onclick="window.print()">🖨 PDF保存 / 印刷</button>
  </div>

  <div class="cover">
    <div class="cover-left">
      <h1>🔗 BitTo 詳細調査レポート</h1>
      <p>ブロックチェーン送金経路・取引所特定 調査報告書</p>
    </div>
    <div class="cover-meta">
      <strong>依頼者</strong>${customerName}
      <strong>発行日時</strong>${issuedAt}
      <strong>調査件数</strong>${results.length}件
    </div>
  </div>

  ${sectionsHTML}

  <p style="text-align:center;color:#94a3b8;font-size:0.78rem;margin-top:20px">
    本レポートは BitTo が自動生成した調査報告書です。参考資料としてご活用ください。
  </p>
</div>

<!-- Mermaid.js -->
<script type="module">
  import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs';
  mermaid.initialize({
    startOnLoad: true, theme: 'base',
    themeVariables: { fontSize: '13px', fontFamily: "'Courier New', monospace" }
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
    try {
      const res = await fetch(
        'https://api.coingecko.com/api/v3/coins/' + coinId +
        '/market_chart/range?vs_currency=usd&from=' + from + '&to=' + to
      );
      const d = await res.json();
      if (!d.prices || !d.prices.length) throw new Error('データなし');

      const labels = d.prices.map(([ts]) => {
        const dt = new Date(ts);
        return (dt.getMonth() + 1) + '/' + dt.getDate();
      });
      const values = d.prices.map(([, p]) => p);

      // 送金時に最も近いインデックス
      let txIdx = d.prices.findIndex(([ts]) => ts >= txTime);
      if (txIdx < 0) txIdx = values.length - 1;
      const txPrice = values[txIdx];

      // 送金時価格をラベル表示
      const lbl = canvas.parentElement.querySelector('.tx-price-label');
      if (lbl && txPrice) {
        lbl.textContent = '● 送金時価格: $' + txPrice.toLocaleString('en-US', { maximumFractionDigits: 2 });
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
      canvas.parentElement.innerHTML = '<p class="chart-error">価格データ取得失敗（CoinGecko APIレート制限の可能性）</p>';
    }
  }
})();
</script>
</body>
</html>`;
}

// 調査後に送るサービス案内メッセージ
function buildServiceMsg(applyUrl) {
  return `📋 BitTo 調査サービス
━━━━━━━━━━━━━━━━━
ブロックチェーン公開データを解析し
送金先取引所を特定する調査サービスです。
公的機関への提出資料を作成します。

■ 料金
・送金経路・取引所特定：無料
・詳細調査レポート 1TXID：¥6,600（税込）
・複数TXIDもまとめて対応可能

📝 詳細レポートをご希望の場合は
下記フォームよりお申し込みください

🔗 ${applyUrl}`;
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

    // サービス案内＋フォームURL
    const applyUrl = `${BASE_URL}/apply?uid=${encodeURIComponent(userId)}`;
    await lineClient.pushMessage(userId, { type: 'text', text: buildServiceMsg(applyUrl) });

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
・詳細レポート：¥6,600（税込）/ 件

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
          await lineClient.pushMessage(userId, { type: 'text', text: buildServiceMsg(applyUrl) });
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
      const { sessionId, userId, txidCount, customerName } = s.metadata;
      const userSession = getSession(userId);
      const count = parseInt(txidCount) || 1;

      try {
        await lineClient.pushMessage(userId, {
          type: 'text',
          text: `✅ お支払いを確認しました！\n\n📄 詳細レポートを生成中...\n通常1〜2分でお届けします`,
        });

        // 調査済みリストから最新N件を取得
        const list = (userSession.investigatedList || []).slice(-count);

        if (list.length === 0) {
          // セッションが失われた場合（サーバー再起動等）→ キャッシュから試行
          await lineClient.pushMessage(userId, {
            type: 'text',
            text: `⚠️ 調査データが見つかりませんでした\nサポートまでご連絡ください`,
          });
        } else {
          // 有料HTMLレポートを生成してURLを送付
          const reportId  = crypto.randomUUID();
          const issuedAt  = new Date().toLocaleString('ja-JP', { timeZone: 'Asia/Tokyo' });
          const cName     = customerName || '（お名前）';
          reportCache.set(reportId, { results: list, customerName: cName, issuedAt });
          const reportUrl = `${BASE_URL}/report/${reportId}`;

          await lineClient.pushMessage(userId, {
            type: 'text',
            text: `✅ お支払いが確認されました\n\n📄 詳細調査レポートが完成しました\n\n${reportUrl}\n\nブラウザで開いて\n「印刷」→「PDFとして保存」\nでPDF化できます`,
          });
        }

        pendingSessions.delete(sessionId);
      } catch (e) {
        console.error('レポート生成エラー:', e);
        await lineClient.pushMessage(userId, {
          type: 'text', text: `⚠️ レポート生成エラー\n${e.message}\nサポートにご連絡ください`,
        });
      }
    }
    res.json({ received: true });
  }
);

// 申し込みフォームからの決済セッション作成
app.post('/api/create-checkout', express.json(), async (req, res) => {
  if (!stripe) return res.status(503).json({ error: 'Stripe未設定（テストモード）' });
  try {
    const { uid, name, phone, email, address, txid_count } = req.body;
    const count  = Math.max(1, Math.min(10, parseInt(txid_count) || 1));
    const amount = 6600 * count;
    const sessionId = crypto.randomUUID();

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
      cancel_url:  `${BASE_URL}/apply?uid=${encodeURIComponent(uid || '')}`,
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
<p>やり直す場合はLINEにて<br>フォームリンクをご確認ください。</p></div></body></html>`));

// LINE Webhook
app.post('/webhook', line.middleware(lineConfig), async (req, res) => {
  res.json({ ok: true });
  await Promise.all(req.body.events.map(handleLineEvent)).catch(console.error);
});

app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ── REST API ────────────────────────────────────────────────
app.get('/api/status', (_req, res) => res.json({
  ok: true, mode: stripe ? 'production' : 'test（Stripeなし）',
  keys: { blockchair: !!BLOCKCHAIR_KEY, etherscan: !!ETHERSCAN_KEY, gemini: !!GEMINI_KEY, line: !!LINE_CHANNEL_ACCESS_TOKEN, stripe: !!stripe },
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
app.post('/api/ai/analyze', express.json(), async (req, res) => {
  try { const { prompt } = req.body;
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

// /apply → apply.html（クエリパラメータ付きでも対応）
app.get('/apply', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'apply.html')));

// 有料レポートページ（reportCache から HTML を配信）
app.get('/report/:id', (req, res) => {
  const data = reportCache.get(req.params.id);
  if (!data) {
    return res.status(404).send(`<!DOCTYPE html>
<html lang="ja"><head><meta charset="UTF-8"><title>レポートが見つかりません</title>
<style>body{margin:0;background:#0a0c10;color:#e2e8f0;font-family:sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px}
.card{background:#111318;border:1px solid #252d3d;border-radius:16px;padding:40px;max-width:400px}
h1{color:#f87171;font-size:1.3rem;margin-bottom:12px}.icon{font-size:3rem;margin-bottom:16px}p{color:#94a3b8;line-height:1.7}</style></head>
<body><div class="card"><div class="icon">⚠️</div><h1>レポートが見つかりません</h1>
<p>URLの有効期限が切れているか、リンクが正しくありません。<br><br>ご不明な点はLINEにてお問い合わせください。</p></div></body></html>`);
  }
  res.setHeader('Content-Type', 'text/html; charset=utf-8');
  res.send(generateReportHTML(data.results, data.customerName, data.issuedAt));
});

app.get('*', (_req, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));

app.listen(PORT, () => {
  console.log(`\n✅ BitTo サーバー起動完了`);
  console.log(`🌐 http://localhost:${PORT}`);
  console.log(`📡 LINE Webhook: ${BASE_URL}/webhook`);
  console.log(`🔑 Blockchair : ${BLOCKCHAIR_KEY ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 LINE       : ${LINE_CHANNEL_ACCESS_TOKEN ? '✓' : '⚠ 未設定'}`);
  console.log(`🔑 Stripe     : ${stripe ? '✓ 本番モード' : '⚠ テストモード（決済スキップ）'}`);
  console.log();
});

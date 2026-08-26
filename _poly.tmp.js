/* Polygon対応が実データで動くか。正解経路④で確かめる。使い終わったら消す。 */
require('dotenv').config();
process.env.MISTTRACK_API_KEY = '';           // ラベルAPIは使わない
const fs = require('fs');
const src = fs.readFileSync('server.js', 'utf8');
const H = '0xe6b2adf17067c40846fb07eae85d8a2f93f368cb24bff0d471a9ce50f07be3db';
const T = { '0xa1647109ba577a10fcce6122fbc11beca70330bc':'正解A',
  '0xc62280be065c52bb1fcb8169129186f84bccdc5a':'正解B',
  '0x11235534a66a33c366b84933d5202c841539d1c9':'正解C',
  '0x356e5c3b30805d438c10c2c876a3d610674add47':'正解D',
  '0x0873d6b7ffde3750465ee2c1a68900d7cd880880':'★★正解E Bitget' };
(async () => {
  // server.js をそのまま読み込むと待ち受けが始まるので、必要な関数だけ取り出す
  const i = src.indexOf('const EVM_CHAINS');
  const j = src.indexOf('// ══ レポート生成');
  console.log('※ 実サーバに投げて確認します');
  const B = 'https://delightful-insight-production-00a3.up.railway.app';
  const r = await fetch(B + '/api/connection/investigate', { method: 'POST',
    headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ txid: H, device: 'verify-polygon' }) });
  const { jobId } = await r.json();
  for (let k = 0; k < 40; k++) {
    await new Promise(x => setTimeout(x, 4000));
    const jr = await (await fetch(`${B}/api/connection/job/${jobId}`)).json();
    if (jr.status === 'running') continue;
    if (jr.status !== 'done') { console.log('結果:', jr.status, jr.error || ''); return; }
    const res = jr.result;
    console.log('チェーン:', res.chain);
    (res.path || []).forEach((p, n) => {
      const hit = T[String(p.address).toLowerCase()];
      console.log(`${String(n).padStart(2)} ${p.address} ${p.amount != null ? String(p.amount).slice(0,12) : ''} ${p.token||''} ${hit ? '  ←'+hit : ''}`);
      console.log(`    ${p.label||'(名前なし)'} 取引所=${!!p.isExchange} 経由=${!!p.isVia} 交換先=${p.swapTo||'—'}`);
    });
    console.log('凍結要請先:', JSON.stringify(res.exchanges||[]));
    return;
  }
})();

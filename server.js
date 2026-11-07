'use strict';
/* Servidor online simples para o Roleplay Imperial.
   Sem dependências: só Node 18+.  Rodar:  node server.js
   - serve o jogo (game.html) em /
   - WebSocket em /ws  (mesmo protocolo que o jogo já usa)
   - até MAX_PLAYERS (padrão 75) jogadores ao mesmo tempo
   - contas salvas em accounts.json (senha com hash scrypt) */
const http = require('http'), fs = require('fs'), path = require('path'),
      crypto = require('crypto'), zlib = require('zlib');

const PORT = +process.env.PORT || 3000;
const MAX = +process.env.MAX_PLAYERS || 75;
const DATA = process.env.DATA_DIR || __dirname;
const ACC_FILE = path.join(DATA, 'accounts.json');
const GAME_FILE = path.join(__dirname, 'game.html');
const MAXMSG = 8192;
const ORGS = new Set(['fam', 'pol', 'fav', 'exe']);

/* ---------- contas ---------- */
let accounts = {};
try { accounts = JSON.parse(fs.readFileSync(ACC_FILE, 'utf8')); } catch (e) { accounts = {}; }
let saveTimer = null;
function saveAccounts(now) {
  const run = () => {
    saveTimer = null;
    try { fs.writeFileSync(ACC_FILE + '.tmp', JSON.stringify(accounts)); fs.renameSync(ACC_FILE + '.tmp', ACC_FILE); }
    catch (e) { console.error('erro ao salvar contas:', e.message); }
  };
  if (now) { if (saveTimer) clearTimeout(saveTimer); run(); }
  else if (!saveTimer) saveTimer = setTimeout(run, 5000);
}
const hashPw = (p, salt) => crypto.scryptSync(p, salt, 32).toString('hex');
function checkPw(p, acc) {
  const a = Buffer.from(hashPw(p, acc.salt), 'hex'), b = Buffer.from(acc.hash, 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

/* ---------- WebSocket mínimo (RFC 6455) ---------- */
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function frame(op, payload) {
  const n = payload.length; let h;
  if (n < 126) h = Buffer.from([0x80 | op, n]);
  else if (n < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(n, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([h, payload]);
}
const textFrame = obj => frame(1, Buffer.from(JSON.stringify(obj)));

class Conn {
  constructor(sock) {
    this.s = sock; this.buf = Buffer.alloc(0); this.frag = null;
    this.alive = true; this.closed = false; this.p = null;
    this.tokens = 40; this.chatT = []; this.fails = 0;
    sock.setNoDelay(true);
    sock.on('data', d => this.onData(d));
    sock.on('close', () => this.onClose());
    sock.on('error', () => sock.destroy());
  }
  sendRaw(buf) {
    if (this.closed) return;
    if (this.s.writableLength > 1 << 20) { this.s.destroy(); return; } // cliente lento demais
    this.s.write(buf);
  }
  send(obj) { this.sendRaw(textFrame(obj)); }
  close(code) {
    if (this.closed) return;
    const b = Buffer.alloc(2); b.writeUInt16BE(code || 1000, 0);
    try { this.s.end(frame(8, b)); } catch (e) { /* ignore */ }
    setTimeout(() => this.s.destroy(), 1000).unref();
  }
  onData(chunk) {
    this.buf = Buffer.concat([this.buf, chunk]);
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = !!(b[0] & 0x80), op = b[0] & 0x0f, masked = !!(b[1] & 0x80);
      let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) {
        if (b.length < 10) return;
        const big = b.readBigUInt64BE(2);
        if (big > BigInt(MAXMSG)) return this.close(1009);
        len = Number(big); off = 10;
      }
      if (len > MAXMSG) return this.close(1009);
      if (!masked) return this.close(1002);
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) data[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      if (op === 8) { this.close(1000); return; }
      if (op === 9) { this.sendRaw(frame(10, data)); continue; }
      if (op === 10) { this.alive = true; continue; }
      if (op === 1 || op === 2 || op === 0) {
        if (op !== 0) this.frag = { op, parts: [] };
        if (!this.frag) return this.close(1002);
        this.frag.parts.push(data);
        if (this.frag.parts.reduce((a, c) => a + c.length, 0) > MAXMSG) return this.close(1009);
        if (fin) {
          const full = Buffer.concat(this.frag.parts), o = this.frag.op; this.frag = null;
          if (o === 1) this.onText(full.toString('utf8'));
        }
      }
    }
  }
  onText(txt) {
    if (this.tokens < 1) return;      // limite de mensagens por segundo
    this.tokens--;
    let d; try { d = JSON.parse(txt); } catch (e) { return; }
    if (!d || typeof d !== 'object') return;
    try { handle(this, d); } catch (e) { console.error('erro handle:', e.message); }
  }
  onClose() {
    if (this.closed) return; this.closed = true;
    leave(this);
  }
}

/* ---------- estado do jogo ---------- */
const players = new Map();      // id -> player
const byName = new Map();       // nome minúsculo -> player
let nextId = 1;

const clampN = (v, lo, hi) => (Number.isFinite(v) ? Math.max(lo, Math.min(hi, v)) : 0);
function broadcast(obj, except) {
  const f = textFrame(obj);
  for (const p of players.values()) if (p !== except) p.conn.sendRaw(f);
}
const pub = p => ({ id: p.id, n: p.name, x: p.x, z: p.z, h: p.h, f: p.f });

function enter(conn, name, acc) {
  if (players.size >= MAX) { conn.send({ t: 'err', m: 'Servidor cheio (' + MAX + '/' + MAX + '). Tente de novo daqui a pouco.' }); return; }
  const key = name.toLowerCase();
  if (byName.has(key)) { conn.send({ t: 'err', m: 'Esta conta já está online.' }); return; }
  const p = { id: nextId++, name, key, acc, conn, x: 0, z: 0, h: 0, f: 1, s: 0, dirty: false };
  conn.p = p; players.set(p.id, p); byName.set(key, p);
  conn.send({
    t: 'ok', n: name, money: acc.money, deliv: acc.deliv, hasGun: !!acc.hasGun,
    players: [...players.values()].filter(q => q !== p).map(pub), count: players.size
  });
  broadcast(Object.assign({ t: 'join' }, pub(p)), p);
  broadcast({ t: 'count', n: players.size });
  console.log('+ ' + name + ' (' + players.size + '/' + MAX + ')');
}
function leave(conn) {
  const p = conn.p; if (!p) return;
  conn.p = null; players.delete(p.id); byName.delete(p.key);
  saveAccounts();
  broadcast({ t: 'leave', id: p.id });
  broadcast({ t: 'count', n: players.size });
  console.log('- ' + p.name + ' (' + players.size + '/' + MAX + ')');
}

const NAME_RE = /^[A-Za-z0-9_À-ÿ]{3,14}$/;
function auth(conn, d, create) {
  if (conn.p) return;
  const u = typeof d.u === 'string' ? d.u.trim() : '', pw = typeof d.p === 'string' ? d.p : '';
  if (!NAME_RE.test(u)) { conn.send({ t: 'err', m: 'Usuário: 3 a 14 letras, números ou _' }); return; }
  if (pw.length < 3 || pw.length > 64) { conn.send({ t: 'err', m: 'Senha: de 3 a 64 caracteres' }); return; }
  if (players.size >= MAX) { conn.send({ t: 'err', m: 'Servidor cheio (' + MAX + '/' + MAX + ').' }); return; }
  const key = u.toLowerCase();
  if (create) {
    if (accounts[key]) { conn.send({ t: 'err', m: 'Este usuário já existe. Use Entrar.' }); return; }
    const salt = crypto.randomBytes(16).toString('hex');
    accounts[key] = { name: u, salt, hash: hashPw(pw, salt), money: 50, deliv: 0, hasGun: false };
    saveAccounts(true);
  }
  const acc = accounts[key];
  if (!acc || !checkPw(pw, acc)) {
    if (++conn.fails >= 5) conn.close(1008);
    conn.send({ t: 'err', m: 'Usuário ou senha incorretos' }); return;
  }
  enter(conn, acc.name, acc);
}

function handle(conn, d) {
  switch (d.t) {
    case 'reg': return auth(conn, d, true);
    case 'login': return auth(conn, d, false);
  }
  const p = conn.p; if (!p) return;
  switch (d.t) {
    case 'pos':
      p.x = clampN(+d.x, -3000, 3000); p.z = clampN(+d.z, -3000, 3000);
      p.h = clampN(+d.h, -10, 10); p.f = d.f ? 1 : 0; p.s = clampN(+d.s, -200, 200);
      p.dirty = true; break;
    case 'save':
      p.acc.money = Math.floor(clampN(+d.money, 0, 1e12));
      p.acc.deliv = Math.floor(clampN(+d.deliv, 0, 1e9));
      p.acc.hasGun = !!d.hasGun;
      saveAccounts(); break;
    case 'din': {   // /dinheiro: no máximo R$ 1.000.000 no total por conta
      const LIM = 1000000, add = Math.max(0, LIM - (p.acc.din || 0));
      p.acc.din = (p.acc.din || 0) + add; p.acc.money += add;
      saveAccounts(); p.conn.send({ t: 'din', add }); break;
    }
    case 'chat': {
      if (typeof d.m !== 'string') return;
      const now = Date.now();
      conn.chatT = conn.chatT.filter(t => now - t < 5000);
      if (conn.chatT.length >= 10) return;      // anti-flood
      conn.chatT.push(now);
      const m = d.m.slice(0, 120);
      if (!m.trim()) return;
      broadcast({ t: 'chat', m, n: p.name });   // inclui o remetente (o cliente não mostra sozinho)
      break;
    }
    case 'inv': case 'invr': {
      if (typeof d.to !== 'string' || !ORGS.has(d.o)) return;
      const q = byName.get(d.to.trim().toLowerCase());
      if (!q || q === p) return;
      q.conn.send(d.t === 'inv' ? { t: 'inv', from: p.name, o: d.o } : { t: 'invr', from: p.name, o: d.o, ok: d.ok ? 1 : 0 });
      break;
    }
  }
}

/* posições: 10x por segundo, só de quem se mexeu */
setInterval(() => {
  const list = [];
  for (const p of players.values()) if (p.dirty) { p.dirty = false; list.push([p.id, p.x, p.z, p.h, p.f, p.s]); }
  if (!list.length) return;
  const f = textFrame({ t: 'st', p: list });
  for (const p of players.values()) p.conn.sendRaw(f);
}, 100);

/* recarrega fichas de mensagens por segundo + detecta conexões mortas */
const conns = new Set();
setInterval(() => { for (const c of conns) c.tokens = 40; }, 1000).unref();
setInterval(() => {
  for (const c of conns) {
    if (!c.alive) { c.s.destroy(); continue; }
    c.alive = false; c.sendRaw(frame(9, Buffer.alloc(0)));
  }
}, 25000).unref();

/* ---------- app instalável (PWA): manifest, service worker e ícones ---------- */
const MANIFEST = JSON.stringify({
  name: 'Roleplay Imperial', short_name: 'Imperial', start_url: '/', scope: '/',
  display: 'fullscreen', background_color: '#1b2a44', theme_color: '#1b2a44',
  icons: [
    { src: '/icon-192.png', sizes: '192x192', type: 'image/png', purpose: 'any maskable' },
    { src: '/icon-512.png', sizes: '512x512', type: 'image/png', purpose: 'any maskable' }
  ]
});
const SW = "self.addEventListener('install',()=>self.skipWaiting());" +
  "self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));" +
  "self.addEventListener('fetch',e=>{if(e.request.mode==='navigate')e.respondWith(fetch(e.request).catch(()=>new Response('Sem conexão com o servidor. Tente de novo.',{status:503,headers:{'Content-Type':'text/plain; charset=utf-8'}})))});";
const CRC_T = (() => { const t = []; for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
function crc32(b) { let c = 0xffffffff; for (let i = 0; i < b.length; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ 0xffffffff) >>> 0; }
function chunk(type, data) {
  const t = Buffer.from(type), len = Buffer.alloc(4), crc = Buffer.alloc(4);
  len.writeUInt32BE(data.length); crc.writeUInt32BE(crc32(Buffer.concat([t, data])));
  return Buffer.concat([len, t, data, crc]);
}
function makeIcon(size) {   // ícone simples: fundo azul-escuro com um anel dourado
  const raw = Buffer.alloc((size * 3 + 1) * size), c = size / 2;
  for (let y = 0; y < size; y++) {
    raw[y * (size * 3 + 1)] = 0;
    for (let x = 0; x < size; x++) {
      const d = Math.hypot(x + .5 - c, y + .5 - c) / size;
      let col = [27, 42, 68];
      if (d < .30 && d > .22) col = [240, 190, 60];
      else if (d < .10) col = [240, 190, 60];
      const o = y * (size * 3 + 1) + 1 + x * 3; raw[o] = col[0]; raw[o + 1] = col[1]; raw[o + 2] = col[2];
    }
  }
  const ihdr = Buffer.alloc(13); ihdr.writeUInt32BE(size, 0); ihdr.writeUInt32BE(size, 4); ihdr[8] = 8; ihdr[9] = 2;
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ihdr), chunk('IDAT', zlib.deflateSync(raw)), chunk('IEND', Buffer.alloc(0))]);
}
const ICONS = { '/icon-192.png': makeIcon(192), '/icon-512.png': makeIcon(512) };

/* ---------- HTTP ---------- */
let cache = { mt: 0, raw: null, gz: null };
function gameBuf() {
  const st = fs.statSync(GAME_FILE);
  if (st.mtimeMs !== cache.mt) { const raw = fs.readFileSync(GAME_FILE); cache = { mt: st.mtimeMs, raw, gz: zlib.gzipSync(raw) }; }
  return cache;
}
const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/manifest.json') { res.writeHead(200, { 'Content-Type': 'application/manifest+json' }); return res.end(MANIFEST); }
  if (url === '/sw.js') { res.writeHead(200, { 'Content-Type': 'text/javascript', 'Cache-Control': 'no-cache' }); return res.end(SW); }
  if (ICONS[url]) { res.writeHead(200, { 'Content-Type': 'image/png', 'Cache-Control': 'public, max-age=86400' }); return res.end(ICONS[url]); }
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok ' + players.size + '/' + MAX); }
  if (url === '/' || url === '/index.html' || url === '/game.html') {
    try {
      const g = gameBuf(), gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
      res.writeHead(200, Object.assign({ 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }, gz ? { 'Content-Encoding': 'gzip' } : {}));
      return res.end(gz ? g.gz : g.raw);
    } catch (e) { res.writeHead(500); return res.end('game.html não encontrado ao lado do server.js'); }
  }
  res.writeHead(404); res.end('404');
});
server.on('upgrade', (req, sock) => {
  if (req.url.split('?')[0] !== '/ws' || (req.headers.upgrade || '').toLowerCase() !== 'websocket' || !req.headers['sec-websocket-key']) { sock.destroy(); return; }
  if (conns.size >= MAX * 3) { sock.destroy(); return; }   // proteção contra abuso de conexões
  const acc = crypto.createHash('sha1').update(req.headers['sec-websocket-key'] + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
  const c = new Conn(sock); conns.add(c); sock.on('close', () => conns.delete(c));
  c.send({ t: 'hello', n: players.size, max: MAX });
});
server.listen(PORT, () => console.log('Servidor no ar: http://localhost:' + PORT + '  (máx. ' + MAX + ' jogadores)'));

function bye() { saveAccounts(true); process.exit(0); }
process.on('SIGINT', bye); process.on('SIGTERM', bye);

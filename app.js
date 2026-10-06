'use strict';
/* Soul ERP: three databases (souls, healthcare records, hospitals) in localStorage.
   Prototype only: production needs a server-side API, TLS and a real SQL database. */
const $ = (s, r = document) => r.querySelector(s);
const enc = new TextEncoder();
const hex = b => [...new Uint8Array(b)].map(x => x.toString(16).padStart(2, '0')).join('');
const rnd = n => hex(crypto.getRandomValues(new Uint8Array(n)));
const rid = p => p + '-' + rnd(4).toUpperCase();
const now = () => new Date().toISOString();
const PORTAL = document.body.dataset.portal; // 'admin' (hospital) | 'doctor' | 'super' (administration)
const LIMIT = 5, LOCK_MS = 300000, IDLE_MS = 600000;
let S = null, tab = null, idleT, hsel = '', editId = null, rf = { h: '', q: '' };
const ROLE = { admin: 'Receptionist', doctor: 'Doctor', super: 'Administrator' };
const DEMO = { admin: ['HOSP-1001', 'ADM-001', 'Admin@123'], doctor: ['HOSP-1001', 'DOC-001', 'Doctor@123'], super: ['SYS-001', 'SysAdmin@123'] };
let editH = null, editS = null;

/* Pure-JS PBKDF2-HMAC-SHA256: used when crypto.subtle is unavailable (e.g. http://192.168.x.x). Same output as WebCrypto. */
const PR = []; for (let n = 2; PR.length < 64; n++) if (PR.every(p => n % p)) PR.push(n);
const K256 = PR.map(p => Math.floor(Math.cbrt(p) % 1 * 2 ** 32)), H256 = PR.slice(0, 8).map(p => Math.floor(Math.sqrt(p) % 1 * 2 ** 32));
function sha256(m) {
  const l = m.length, n = ((l + 9 + 63) >> 6) << 6, b = new Uint8Array(n); b.set(m); b[l] = 128;
  const dv = new DataView(b.buffer); dv.setUint32(n - 4, (l * 8) >>> 0); dv.setUint32(n - 8, Math.floor(l / 2 ** 29));
  const h = H256.slice(), w = new Uint32Array(64);
  for (let o = 0; o < n; o += 64) {
    for (let i = 0; i < 16; i++) w[i] = dv.getUint32(o + i * 4);
    for (let i = 16; i < 64; i++) { const a = w[i - 15], c = w[i - 2]; w[i] = (w[i - 16] + (((a >>> 7) | (a << 25)) ^ ((a >>> 18) | (a << 14)) ^ (a >>> 3)) + w[i - 7] + (((c >>> 17) | (c << 15)) ^ ((c >>> 19) | (c << 13)) ^ (c >>> 10))) >>> 0; }
    let [a, q, c, d, e, f, g, z] = h;
    for (let i = 0; i < 64; i++) {
      const t1 = (z + (((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7))) + ((e & f) ^ (~e & g)) + K256[i] + w[i]) >>> 0;
      const t2 = ((((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10))) + ((a & q) ^ (a & c) ^ (q & c))) >>> 0;
      z = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = q; q = a; a = (t1 + t2) >>> 0;
    }
    [a, q, c, d, e, f, g, z].forEach((v, i) => h[i] = (h[i] + v) >>> 0);
  }
  const out = new Uint8Array(32), ov = new DataView(out.buffer); h.forEach((v, i) => ov.setUint32(i * 4, v)); return out;
}
function pbkdf2js(pw, salt, iter) {
  const k = pw.length > 64 ? sha256(pw) : pw, ip = new Uint8Array(64).fill(0x36), op = new Uint8Array(64).fill(0x5c);
  k.forEach((v, i) => { ip[i] ^= v; op[i] ^= v; });
  const hm = m => { const a = new Uint8Array(64 + m.length); a.set(ip); a.set(m, 64); const c = new Uint8Array(96); c.set(op); c.set(sha256(a), 64); return sha256(c); };
  const s = new Uint8Array(salt.length + 4); s.set(salt); s[s.length - 1] = 1;
  let u = hm(s); const t = u.slice();
  for (let i = 1; i < iter; i++) { u = hm(u); for (let j = 0; j < 32; j++) t[j] ^= u[j]; }
  return t;
}


/* ---------- security primitives ---------- */
async function hash(pw, salt) {
  if (globalThis.crypto && crypto.subtle) {
    const k = await crypto.subtle.importKey('raw', enc.encode(pw), 'PBKDF2', false, ['deriveBits']);
    return hex(await crypto.subtle.deriveBits({ name: 'PBKDF2', salt: enc.encode(salt), iterations: 150000, hash: 'SHA-256' }, k, 256));
  }
  await new Promise(r => setTimeout(r, 30));
  return hex(pbkdf2js(enc.encode(pw), enc.encode(salt), 150000));
}
const safeEq = (a, b) => { let d = a.length ^ b.length; for (let i = 0; i < a.length; i++) d |= a.charCodeAt(i) ^ (b.charCodeAt(i) || 0); return d === 0; };
const strong = p => p.length >= 8 && /[a-z]/.test(p) && /[A-Z]/.test(p) && /\d/.test(p);
const ALLOW = { admin: ['admin'], onboard: ['doctor'], doctor: ['doctor'], super: ['super'], audit: ['admin', 'super'] };
const need = r => { if (!S || !(ALLOW[r] || [r]).includes(S.role)) throw new Error('Not authorised for this action.'); };

/* ---------- storage ---------- */
const DB = {
  get(k, d) { try { return JSON.parse(localStorage.getItem('erp_' + k)) ?? d; } catch { return d; } },
  set(k, v) { localStorage.setItem('erp_' + k, JSON.stringify(v)); }
};
const hosp = () => DB.get('hospitals', []).find(x => x.lic === S.lic);
const upd = fn => { const a = DB.get('hospitals'); fn(a.find(x => x.lic === S.lic)); DB.set('hospitals', a); };
const myTokens = () => DB.get('tokens', []).filter(t => t.lic === S.lic);
const updTok = (id, fn) => { const a = DB.get('tokens', []); const t = a.find(x => x.id === id && x.lic === S.lic); if (!t) throw new Error('Token not found.'); fn(t); DB.set('tokens', a); };
const soulOf = id => DB.get('souls', []).find(s => s.id === id);
function log(a, who) { const l = DB.get('audit', []); l.unshift({ t: now(), lic: S?.lic || '-', u: who || S?.sub || '-', a }); DB.set('audit', l.slice(0, 300)); }

/* Demo data: hashes are precomputed so first load is instant. Demo passwords: Admin@123, Doctor@123, SysAdmin@123 */
function seed() {
  if (!DB.get('hospitals')) {
    DB.set('hospitals', [{ lic: 'HOSP-1001', name: 'Paws & Care Veterinary Hospital', addr: '12 MG Road, Bengaluru', phone: '080-5550100', open: true, next: 1,
      subs: [{ sub: 'ADM-001', name: 'Hospital Admin', role: 'admin', salt: 'a1b2c3d4e5f60718', hash: '5dfdd5de5aa1ff96ce169f1ab0dbdaf0dc452d9188dbeeed968db8d067508840' }, { sub: 'DOC-001', name: 'Dr. Meera Rao', role: 'doctor', salt: 'b2c3d4e5f6071829', hash: 'c3d2a0dc4e3f8d09f254d1827cc022b78d371cbbed906e855cb654a74256cf7e' }] }]);
    DB.set('souls', [{ id: 'SOUL-A1B2C3D4', name: 'Bruno', species: 'Dog', breed: 'Labrador', age: 4, sex: 'M', owner: 'Arjun K', contact: '9876500000' }]);
    DB.set('records', []); DB.set('tokens', []);
  }
  if (!DB.get('sysadmins')) DB.set('sysadmins', [{ sub: 'SYS-001', name: 'System Administrator', role: 'super', salt: 'c3d4e5f60718293a', hash: 'ca20b39adb1fd055f664cd1cf0529526781f8068c645a9e822ce8e60e5ef4ab3' }]);
}

/* ---------- safe DOM builder (no innerHTML anywhere) ---------- */
function h(t, a = {}, ...c) {
  const e = document.createElement(t);
  for (const [k, v] of Object.entries(a)) k.startsWith('on') ? e.addEventListener(k.slice(2), v) : e.setAttribute(k, v);
  c.flat().forEach(x => e.append(x?.nodeType ? x : document.createTextNode(x ?? '')));
  return e;
}
function toast(m, ok) { const t = h('div', { class: 'toast' + (ok ? ' ok' : ''), role: 'alert' }, m); document.body.append(t); setTimeout(() => t.remove(), ok ? 9000 : 3500); }
async function act(fn) { try { await fn(); render(); } catch (x) { toast(x.message); } }
function form(fs, label, fn) {
  const f = h('form', { class: 'grid' }, fs.map(([n, l, t = 'text', v = '']) => h('label', {}, l,
    t === 'ta' ? h('textarea', { name: n, maxlength: 1000, rows: 3 }, v)
    : Array.isArray(t) ? (() => { const s = h('select', { name: n }, t.map(o => h('option', { value: o[0] }, o[1]))); if (v) s.value = v; return s; })()
    : h('input', { name: n, type: t, value: v, maxlength: 120, required: '', autocomplete: 'off' }))), h('button', { class: 'btn' }, label));
  f.onsubmit = e => { e.preventDefault(); act(() => fn(Object.fromEntries(new FormData(f)))); };
  return f;
}
const card = (t, ...c) => h('div', { class: 'card' }, h('h2', {}, t), ...c);
const table = (heads, rows, empty = 'Nothing here yet.') => rows.length
  ? h('div', { class: 'scroll' }, h('table', {}, h('tr', {}, heads.map(x => h('th', {}, x))), rows.map(r => h('tr', {}, r.map(c => h('td', {}, c))))))
  : h('p', { class: 'muted' }, empty);
const btn = (l, fn, cls = '') => h('button', { class: 'sm ' + cls, onclick: () => act(fn) }, l);
const sure = m => { if (!confirm(m)) throw new Error('Cancelled.'); };
const dl = rows => h('dl', {}, ...rows.flatMap(([k, v]) => [h('dt', {}, k), h('dd', {}, v)]));
const soulDl = s => dl([['Soul ID', s.id], ['Name', s.name], ['Species / breed', s.species + ' / ' + s.breed], ['Age', s.age], ['Sex', s.sex], ['Owner', s.owner], ['Contact', s.contact]]);
const soulOpts = () => DB.get('souls', []).map(s => [s.id, `${s.id}: ${s.name} (${s.owner})`]);
const badge = (t, c) => h('span', { class: 'badge ' + c }, t);
const stat = (n, l) => h('div', { class: 'stat' }, h('b', {}, n), h('span', {}, l));
const recCard = r => h('div', { class: 'card' }, h('p', { class: 'muted' }, `${new Date(r.t).toLocaleString()}, token ${r.token}, ${r.docName}, ${r.lic}, ${r.soul}`),
  dl([['Complaint', r.complaint], ['Observation', r.observation], ['Diagnostics', r.diagnostics], ['Results', r.results]]));

/* ---------- auth ---------- */
const COPY = {
  admin: ['Hospital login', 'Receptionist access: tokens, Soul IDs, staff and hospital status.'],
  doctor: ['Doctor login', 'Onboard patients and record consultations.'],
  super: ['Administration login', 'Monitor every hospital and manage hospital, doctor and staff accounts.']
};
function loginView() {
  const fields = PORTAL === 'super' ? [['sub', 'Administrator ID', 'text'], ['pw', 'Password', 'password']]
    : [['lic', 'Hospital license key', 'text'], ['sub', PORTAL === 'admin' ? 'Receptionist sub license key' : 'Doctor sub license key', 'text'], ['pw', 'Password', 'password']];
  const er = h('p', { class: 'err', role: 'alert' }), go = h('button', { class: 'btn' }, 'Sign in');
  const f = h('form', {}, ...fields.map(([n, l, t]) => h('label', {}, l, h('input', { name: n, type: t, required: '', maxlength: 64, autocomplete: n === 'pw' ? 'current-password' : 'off' }))), er, go);
  f.onsubmit = async e => {
    e.preventDefault(); er.textContent = ''; go.disabled = true; go.textContent = 'Checking...';
    try {
      const lic = f.lic ? f.lic.value.trim().toUpperCase() : 'SYSTEM', sub = f.sub.value.trim().toUpperCase(), key = lic + '|' + sub;
      const L = DB.get('lock', {}), l = L[key] || { n: 0, until: 0 };
      if (l.until > Date.now()) throw new Error(`Too many attempts. Try again in ${Math.ceil((l.until - Date.now()) / 60000)} min.`);
      const u = PORTAL === 'super' ? DB.get('sysadmins', []).find(x => x.sub === sub) : DB.get('hospitals', []).find(x => x.lic === lic)?.subs.find(x => x.sub === sub);
      const ok = u && u.role === PORTAL && safeEq(await hash(f.pw.value, u.salt), u.hash);
      if (!ok) { l.n++; if (l.n >= LIMIT) { l.until = Date.now() + LOCK_MS; l.n = 0; } L[key] = l; DB.set('lock', L); log('Failed login', key); throw new Error('Invalid credentials.'); }
      delete L[key]; DB.set('lock', L);
      S = { lic: PORTAL === 'super' ? '' : lic, sub, name: u.name, role: u.role };
      log('Signed in'); tab = null; touch(); render();
    } catch (x) { er.textContent = x.message; go.disabled = false; go.textContent = 'Sign in'; }
  };
  const fill = h('button', { type: 'button', class: 'ghost', onclick: () => { [...f.querySelectorAll('input')].forEach((i, n) => { i.value = DEMO[PORTAL][n]; }); er.textContent = ''; } }, 'Fill demo credentials');
  const reset = h('a', { href: '#', onclick: e => { e.preventDefault(); if (!confirm('Reset all demo data? This deletes everything saved in this browser.')) return; Object.keys(localStorage).filter(k => k.startsWith('erp_')).forEach(k => localStorage.removeItem(k)); sessionStorage.clear(); seed(); toast('Demo data reset. Try signing in again.', true); } }, 'Reset demo data');
  const note = location.protocol === 'file:' ? h('p', { class: 'muted small' }, 'Tip: you opened this file directly. If logins or shared data misbehave, run start.py (or python3 -m http.server) and open http://localhost:8000 instead.') : null;
  return h('div', { class: 'auth' },
    h('aside', { class: 'auth-brand' }, h('div', { class: 'brand' }, h('span', { class: 'logo' }, 'S'), 'Soul ERP'), h('h2', {}, 'One record for every soul in your care.'), h('p', {}, 'Tokens, onboarding, consultations and health records in one secure workspace.')),
    h('div', { class: 'auth-form' }, h('h1', {}, COPY[PORTAL][0]), h('p', { class: 'muted' }, COPY[PORTAL][1]), h('div', { class: 'card' }, f, h('div', { class: 'row' }, fill, reset)), note, h('a', { href: 'index.html' }, 'Choose a different login')));
}
function logout() { if (S) log('Signed out'); S = null; sessionStorage.removeItem('erp_s'); clearTimeout(idleT); render(); }
function touch() {
  if (!S) return; clearTimeout(idleT);
  sessionStorage.setItem('erp_s', JSON.stringify({ ...S, exp: Date.now() + IDLE_MS }));
  idleT = setTimeout(() => { toast('Signed out after 10 minutes of inactivity.'); logout(); }, IDLE_MS);
}

/* ---------- views ---------- */
const V = {
  /* administration: read-only monitoring, plus management of hospital, doctor and staff details */
  overview() {
    need('super'); const hs = DB.get('hospitals', []), tk = DB.get('tokens', []), rc = DB.get('records', []), day = x => new Date(x).toDateString();
    const days = [...Array(7)].map((_, i) => { const d = new Date(); d.setDate(d.getDate() - 6 + i); return d.toDateString(); }), counts = days.map(d => rc.filter(r => day(r.t) === d).length), mx = Math.max(1, ...counts);
    const chart = h('div', { class: 'chart' }, days.map((d, i) => { const i2 = h('i'); i2.style.height = Math.round(counts[i] / mx * 100) + 'px'; return h('div', { class: 'col' }, h('span', {}, counts[i]), i2, h('small', {}, d.slice(0, 3))); }));
    const hc = x => { const t = tk.filter(y => y.lic === x.lic); return h('div', { class: 'hcard' }, h('div', { class: 'hc-top' }, h('b', {}, x.name), badge(x.open ? 'Open' : 'Closed', x.open ? 'on' : 'off')), h('small', { class: 'muted' }, x.lic + ', ' + x.addr),
      h('div', { class: 'mini' }, stat(t.filter(y => y.st === 'waiting').length, 'Waiting'), stat(t.filter(y => ['called', 'onboarded'].includes(y.st)).length, 'In consult'), stat(rc.filter(r => r.lic === x.lic).length, 'Reports'), stat(x.subs.filter(u => u.role === 'doctor').length, 'Doctors'))); };
    return h('section', {}, h('div', { class: 'stats' }, stat(hs.length, 'Hospitals'), stat(hs.filter(x => x.open).length, 'Open now'), stat(DB.get('souls', []).length, 'Soul IDs'), stat(rc.length, 'Health records'),
      stat(tk.filter(t => t.st === 'waiting').length, 'Tokens waiting'), stat(tk.filter(t => day(t.t) === day(now()) && t.st === 'done').length, 'Served today'), stat(hs.reduce((n, x) => n + x.subs.length, 0), 'Staff accounts')),
      h('div', { class: 'two' }, card('Consultations, last 7 days', chart), card('Hospitals at a glance', h('div', { class: 'hcards' }, hs.length ? hs.map(hc) : h('p', { class: 'muted' }, 'No hospitals yet.')))),
      card('Recent activity', table(['Time', 'Hospital', 'User', 'Action'], DB.get('audit', []).slice(0, 8).map(a => [new Date(a.t).toLocaleString(), a.lic, a.u, a.a]))));
  },
  hospitals() {
    need('super'); const e = editH && DB.get('hospitals', []).find(x => x.lic === editH);
    return h('section', {}, e ? card('Edit ' + e.lic, form([['name', 'Hospital name', 'text', e.name], ['addr', 'Address', 'text', e.addr], ['phone', 'Phone', 'tel', e.phone]], 'Save details', d => { need('super'); const a = DB.get('hospitals'); Object.assign(a.find(x => x.lic === e.lic), d); DB.set('hospitals', a); log('Edited hospital ' + e.lic); editH = null; }), btn('Cancel', () => { editH = null; }))
      : card('Register a hospital', form([['name', 'Hospital name'], ['addr', 'Address'], ['phone', 'Phone', 'tel'], ['aname', 'First receptionist name'], ['pw', 'Receptionist password (8+, upper, lower, number)', 'password']], 'Create hospital', async d => {
        need('super'); if (!strong(d.pw)) throw new Error('Password is too weak.');
        const lic = rid('HOSP'), sub = rid('ADM'), salt = rnd(8), a = DB.get('hospitals', []);
        a.push({ lic, name: d.name, addr: d.addr, phone: d.phone, open: true, next: 1, subs: [{ sub, name: d.aname, role: 'admin', salt, hash: await hash(d.pw, salt) }] });
        DB.set('hospitals', a); log('Created hospital ' + lic); toast(`Created. License key ${lic}, receptionist sub license ${sub}`, true); })),
      card('All hospitals', table(['License key', 'Name', 'Address', 'Phone', 'Status', 'Staff', ''], DB.get('hospitals', []).map(x => [x.lic, x.name, x.addr, x.phone, badge(x.open ? 'Open' : 'Closed', x.open ? 'on' : 'off'), x.subs.length,
        [btn('Edit', () => { editH = x.lic; }), btn('Delete', () => { need('super'); if (DB.get('records', []).some(r => r.lic === x.lic)) throw new Error('This hospital has healthcare records and cannot be deleted.'); sure(`Delete ${x.name}?`);
          DB.set('hospitals', DB.get('hospitals').filter(z => z.lic !== x.lic)); DB.set('tokens', DB.get('tokens', []).filter(t => t.lic !== x.lic)); log('Deleted hospital ' + x.lic); }, 'danger')]]))));
  },
  staffall() {
    need('super'); const hs = DB.get('hospitals', []), e = editS && hs.find(x => x.lic === editS[0])?.subs.find(u => u.sub === editS[1]);
    const rows = hs.flatMap(x => x.subs.map(u => [x.name, u.sub, u.name, badge(ROLE[u.role], u.role === 'doctor' ? 'warn' : 'on'), [
      btn('Edit', () => { editS = [x.lic, u.sub]; }),
      btn('Reset password', async () => { need('super'); const p = prompt('New password for ' + u.name + ' (8+, upper, lower, number)'); if (p === null) throw new Error('Cancelled.'); if (!strong(p)) throw new Error('Password is too weak.');
        const salt = rnd(8), hh = await hash(p, salt), a = DB.get('hospitals'); Object.assign(a.find(z => z.lic === x.lic).subs.find(y => y.sub === u.sub), { salt, hash: hh }); DB.set('hospitals', a); log('Reset password ' + u.sub); toast('Password updated.', true); }),
      btn('Remove', () => { need('super'); sure('Remove ' + u.name + '?'); const a = DB.get('hospitals'); const z = a.find(y => y.lic === x.lic); z.subs = z.subs.filter(y => y.sub !== u.sub); DB.set('hospitals', a); log('Removed ' + u.sub); }, 'danger')]]));
    return h('section', {}, e ? card('Edit ' + e.sub, form([['name', 'Full name', 'text', e.name], ['role', 'Role', [['doctor', 'Doctor'], ['admin', 'Receptionist']], e.role]], 'Save changes', d => { need('super'); const a = DB.get('hospitals'); Object.assign(a.find(x => x.lic === editS[0]).subs.find(u => u.sub === editS[1]), d); DB.set('hospitals', a); log('Edited ' + editS[1]); editS = null; }), btn('Cancel', () => { editS = null; }))
      : card('Add doctor or receptionist', hs.length ? form([['lic', 'Hospital', hs.map(x => [x.lic, x.name])], ['name', 'Full name'], ['role', 'Role', [['doctor', 'Doctor'], ['admin', 'Receptionist']]], ['pw', 'Password (8+, upper, lower, number)', 'password']], 'Create sub license', async d => {
        need('super'); if (!strong(d.pw)) throw new Error('Password is too weak.'); const salt = rnd(8), sub = rid(d.role === 'admin' ? 'ADM' : 'DOC'), hh = await hash(d.pw, salt), a = DB.get('hospitals');
        a.find(x => x.lic === d.lic).subs.push({ sub, name: d.name, role: d.role, salt, hash: hh }); DB.set('hospitals', a); log('Created sub license ' + sub); toast('Created. Sub license key: ' + sub, true); }) : h('p', { class: 'muted' }, 'Create a hospital first.')),
      card('Doctors and receptionists', table(['Hospital', 'Sub license', 'Name', 'Role', ''], rows)));
  },
  live() {
    need('super'); const hs = DB.get('hospitals', []), nm = l => hs.find(x => x.lic === l)?.name || l;
    const live = DB.get('tokens', []).filter(t => ['waiting', 'called', 'onboarded'].includes(t.st));
    const stage = t => t.st === 'waiting' ? badge('Waiting', 'off') : badge(t.st === 'called' ? 'Onboarding' : 'In consultation', 'warn');
    return card('Live queue, all hospitals (read-only)', table(['Hospital', 'Token', 'Soul', 'Complaint', 'Stage', 'Doctor'], live.map(t => [nm(t.lic), t.no, t.soul, t.complaint, stage(t), t.doc || '-']), 'No active tokens right now.'));
  },
  soulsRO() {
    need('super'); const list = h('div'), draw = q => list.replaceChildren(table(['Soul ID', 'Name', 'Species / breed', 'Age', 'Sex', 'Owner', 'Contact'],
      DB.get('souls', []).filter(s => JSON.stringify(s).toLowerCase().includes(q.toLowerCase())).map(s => [s.id, s.name, s.species + ' / ' + s.breed, s.age, s.sex, s.owner, s.contact])));
    draw(''); const search = h('input', { type: 'search', placeholder: 'Search Soul IDs', maxlength: 60 }); search.oninput = () => draw(search.value);
    return card('Soul ID directory (read-only)', search, list);
  },
  records() {
    need('super'); const hs = DB.get('hospitals', []);
    const sel = h('select', { 'aria-label': 'Hospital' }, h('option', { value: '' }, 'All hospitals'), hs.map(x => h('option', { value: x.lic }, x.name))); sel.value = rf.h;
    const q = h('input', { type: 'search', placeholder: 'Filter by Soul ID or text', value: rf.q, maxlength: 60 });
    const go = () => { rf = { h: sel.value, q: q.value }; render(); }; sel.onchange = go; q.onchange = go;
    const recs = DB.get('records', []).filter(r => (!rf.h || r.lic === rf.h) && JSON.stringify(r).toLowerCase().includes(rf.q.toLowerCase())).slice(-50).reverse();
    return h('section', {}, card('Health records (read-only)', h('p', { class: 'muted' }, 'Administrators can read incident reports but cannot change them.'), h('div', { class: 'grid' }, sel, q)),
      recs.map(recCard), !recs.length && h('p', { class: 'muted' }, 'No records match.'));
  },
  sysadmins() {
    need('super');
    return h('section', {}, card('Add administrator', form([['name', 'Full name'], ['pw', 'Password (8+, upper, lower, number)', 'password']], 'Create administrator', async d => {
      need('super'); if (!strong(d.pw)) throw new Error('Password is too weak.'); const salt = rnd(8), sub = rid('SYS');
      DB.set('sysadmins', [...DB.get('sysadmins', []), { sub, name: d.name, role: 'super', salt, hash: await hash(d.pw, salt) }]); log('Created administrator ' + sub); toast('Created. Administrator ID: ' + sub, true); })),
      card('Administrators', table(['ID', 'Name', ''], DB.get('sysadmins', []).map(u => [u.sub, u.name, u.sub === S.sub ? 'You' : btn('Remove', () => { need('super'); sure('Remove ' + u.name + '?'); DB.set('sysadmins', DB.get('sysadmins').filter(y => y.sub !== u.sub)); log('Removed ' + u.sub); }, 'danger')]))));
  },

  /* hospital pov (receptionist) */
  tokens() {
    const hs = hosp(), q = myTokens(), w = q.filter(t => t.st === 'waiting'), busy = q.filter(t => ['called', 'onboarded'].includes(t.st));
    const move = (t, d) => { need('admin'); const a = DB.get('tokens', []); const ix = a.map((x, i) => x.lic === S.lic && x.st === 'waiting' ? i : -1).filter(i => i >= 0);
      const p = ix.indexOf(a.findIndex(x => x.id === t.id)), o = ix[p + d]; if (o === undefined) return; [a[ix[p]], a[o]] = [a[o], a[ix[p]]]; DB.set('tokens', a); log(`Reordered token ${t.no}`); };
    return h('section', {},
      card('Issue token', !hs.open ? h('p', { class: 'muted' }, 'The hospital is closed. Open it from the Hospital tab to issue tokens.') : !soulOpts().length ? h('p', { class: 'muted' }, 'Register a Soul ID first.')
        : form([['soul', 'Soul ID', soulOpts()], ['complaint', 'User complaint', 'ta']], 'Issue token', d => {
          need('admin'); if (!hosp().open) throw new Error('Hospital is closed.'); if (!soulOf(d.soul)) throw new Error('Unknown Soul ID.');
          const no = hosp().next; upd(x => x.next++);
          const a = DB.get('tokens', []); a.push({ id: rid('TK'), lic: S.lic, no, soul: d.soul, complaint: d.complaint.slice(0, 1000), st: 'waiting', t: now() }); DB.set('tokens', a); log(`Issued token ${no} to ${d.soul}`); })),
      card('Waiting queue', table(['Token', 'Soul', 'Complaint', 'Reorder / remove'], w.map(t => [t.no, soulOf(t.soul)?.name + ' (' + t.soul + ')', t.complaint,
        [btn('Up', () => move(t, -1)), btn('Down', () => move(t, 1)), btn('Remove', () => { need('admin'); sure(`Remove token ${t.no} from the queue?`); updTok(t.id, x => x.st = 'removed'); log(`Removed token ${t.no}`); }, 'danger')]]), 'No one is waiting.')),
      card('With a doctor', table(['Token', 'Soul', 'Handled by', 'Stage'], busy.map(t => [t.no, t.soul, t.doc, badge(t.st === 'called' ? 'Onboarding' : 'In consultation', 'warn')]), 'No active consultations.')));
  },
  souls() {
    if (S.role === 'super') return V.soulsRO();
    const ed = editId && soulOf(editId);
    const list = h('div'), draw = q => list.replaceChildren(table(['Soul ID', 'Name', 'Species / breed', 'Age', 'Owner', 'Contact', ''],
      DB.get('souls', []).filter(s => JSON.stringify(s).toLowerCase().includes(q.toLowerCase())).map(s => [s.id, s.name, s.species + ' / ' + s.breed, s.age, s.owner, s.contact,
        [btn('Edit', () => { need('admin'); editId = s.id; }),
          btn('Delete', () => { need('admin'); if (DB.get('records', []).some(r => r.soul === s.id)) throw new Error('This soul has healthcare records and cannot be deleted.'); sure('Delete ' + s.id + '?'); DB.set('souls', DB.get('souls').filter(x => x.id !== s.id)); log('Deleted ' + s.id); }, 'danger')]])));
    draw('');
    const search = h('input', { type: 'search', placeholder: 'Search Soul IDs', maxlength: 60 }); search.oninput = () => draw(search.value);
    const fields = s => [['name', 'Pet name', 'text', s.name], ['species', 'Species', 'text', s.species], ['breed', 'Breed', 'text', s.breed], ['age', 'Age (years)', 'number', s.age], ['sex', 'Sex', [['M', 'Male'], ['F', 'Female']], s.sex], ['owner', 'Owner name', 'text', s.owner], ['contact', 'Owner contact', 'tel', s.contact]];
    return h('section', {}, ed ? card('Edit ' + ed.id, form(fields(ed), 'Save changes', d => { need('admin'); const a = DB.get('souls'); Object.assign(a.find(x => x.id === ed.id), { ...d, age: Math.max(0, +d.age || 0) }); DB.set('souls', a); log('Edited ' + ed.id); editId = null; }), btn('Cancel', () => { editId = null; }))
      : card('Register a soul', form(fields({ name: '', species: '', breed: '', age: '', sex: 'M', owner: '', contact: '' }), 'Create Soul ID', d => { need('admin'); const a = DB.get('souls', []); a.push({ id: rid('SOUL'), ...d, age: Math.max(0, +d.age || 0) }); DB.set('souls', a); log('Created soul ' + d.name); })),
      card('Soul ID directory', search, list));
  },
  staff() {
    const hs = hosp();
    return h('section', {}, card('Add sub license', form([['name', 'Full name'], ['role', 'Role', [['doctor', 'Doctor'], ['admin', 'Admin']]], ['pw', 'Password (8+, upper, lower, number)', 'password']], 'Create sub license', async d => {
      need('admin'); if (!strong(d.pw)) throw new Error('Password is too weak.');
      const salt = rnd(8), sub = rid(d.role === 'admin' ? 'ADM' : 'DOC'), hh = await hash(d.pw, salt);
      upd(x => x.subs.push({ sub, name: d.name, role: d.role, salt, hash: hh })); log('Created sub license ' + sub); toast('Created. Sub license key: ' + sub, true); })),
      card('Staff and admins', table(['Sub license', 'Name', 'Role', ''], hs.subs.map(u => [u.sub, u.name, u.role, [
        btn('Reset password', async () => { need('admin'); const p = prompt('New password for ' + u.name + ' (8+, upper, lower, number)'); if (p === null) throw new Error('Cancelled.'); if (!strong(p)) throw new Error('Password is too weak.');
          const salt = rnd(8), hh = await hash(p, salt); upd(x => Object.assign(x.subs.find(y => y.sub === u.sub), { salt, hash: hh })); log('Reset password ' + u.sub); toast('Password updated.', true); }),
        u.sub !== S.sub && btn('Remove', () => { need('admin'); sure('Remove ' + u.name + '?'); upd(x => x.subs = x.subs.filter(y => y.sub !== u.sub)); log('Removed ' + u.sub); }, 'danger')]]))));
  },
  hospital() {
    const hs = hosp();
    return h('section', {}, card('Status', h('p', {}, 'License key: ', h('b', {}, hs.lic)), h('p', {}, 'The hospital is currently ', badge(hs.open ? 'Open' : 'Closed', hs.open ? 'on' : 'off'), '.'),
      btn(hs.open ? 'Close hospital' : 'Open hospital', () => { need('admin'); upd(x => x.open = !x.open); log('Hospital ' + (hs.open ? 'closed' : 'opened')); })),
      card('Hospital details', form([['name', 'Name', 'text', hs.name], ['addr', 'Address', 'text', hs.addr], ['phone', 'Phone', 'tel', hs.phone]], 'Save details', d => { need('admin'); upd(x => Object.assign(x, d)); log('Updated hospital details'); })));
  },
  audit() { need('audit'); const all = S.role === 'super'; return card(all ? 'Audit log (all hospitals)' : 'Audit log', table(['Time', 'Hospital', 'User', 'Action'], DB.get('audit', []).filter(a => all || a.lic === S.lic).slice(0, 100).map(a => [new Date(a.t).toLocaleString(), a.lic, a.u, a.a]))); },

  /* doctor pov */
  queue() {
    const q = myTokens(), cur = q.find(t => ['called', 'onboarded'].includes(t.st) && t.doc === S.sub), w = q.filter(t => t.st === 'waiting');
    const out = [h('div', { class: 'card' }, h('p', { class: 'muted' }, 'Current token'), h('div', { class: 'token' }, cur ? cur.no : '-'), h('br'),
      !cur && btn('Call next token', () => { need('onboard'); if (!w.length) throw new Error('No one is waiting.'); updTok(w[0].id, t => { t.st = 'called'; t.doc = S.sub; }); log('Called token ' + w[0].no); }))];
    if (cur) {
      const s = soulOf(cur.soul);
      out.push(card('Patient onboarding', soulDl(s), h('p', {}, h('b', {}, 'User complaint: '), cur.complaint),
        cur.st === 'called' ? btn('Complete onboarding', () => { need('onboard'); updTok(cur.id, t => t.st = 'onboarded'); log('Onboarded token ' + cur.no); }) : badge('Onboarding complete', 'on')));
      if (cur.st === 'onboarded') out.push(card('Consultation', form([['observation', 'Observation', 'ta'], ['diagnostics', 'Diagnostics', 'ta'], ['results', 'Results', 'ta']], 'Save incident report and close token', d => {
          need('doctor'); const r = DB.get('records', []); r.push({ id: rid('REC'), soul: cur.soul, lic: S.lic, doc: S.sub, docName: S.name, token: cur.no, complaint: cur.complaint, observation: d.observation, diagnostics: d.diagnostics, results: d.results, t: now() });
          DB.set('records', r); updTok(cur.id, t => t.st = 'done'); log(`Closed token ${cur.no}, report saved for ${cur.soul}`); })));
    }
    out.push(card('Waiting', table(['Token', 'Soul', 'Complaint'], w.map(t => [t.no, t.soul, t.complaint]), 'No one is waiting.')));
    return h('section', {}, out);
  },
  history() {
    need('doctor');
    const sel = h('select', { 'aria-label': 'Soul ID' }, h('option', { value: '' }, 'Choose a Soul ID'), soulOpts().map(o => h('option', { value: o[0] }, o[1])));
    sel.value = hsel; sel.onchange = () => { hsel = sel.value; if (hsel) log('Viewed records of ' + hsel); render(); };
    const recs = hsel ? DB.get('records', []).filter(r => r.soul === hsel).reverse() : [];
    return h('section', {}, card('Patient history', sel), recs.map(recCard), hsel && !recs.length && h('p', { class: 'muted' }, 'No incident reports for this soul yet.'));
  }
};

const TABS = {
  admin: [['tokens', 'Tokens'], ['souls', 'Soul IDs'], ['staff', 'Staff and admins'], ['hospital', 'Hospital'], ['audit', 'Audit log']],
  doctor: [['queue', 'Queue'], ['history', 'Patient history']],
  super: [['overview', 'Dashboard'], ['hospitals', 'Hospitals'], ['staffall', 'Doctors and staff'], ['live', 'Live queue'], ['souls', 'Soul IDs'], ['records', 'Health records'], ['sysadmins', 'Administrators'], ['audit', 'Audit log']]
};
function render() {
  const app = $('#app'); app.replaceChildren();
  if (!S) return app.append(loginView());
  const tabs = TABS[S.role]; if (!tabs.some(t => t[0] === tab)) tab = tabs[0][0];
  const hs = S.role === 'super' ? null : hosp();
  const body = (() => { try { return V[tab](); } catch (x) { return h('p', { class: 'err' }, x.message); } })();
  app.append(h('div', { class: 'shell' },
    h('aside', { class: 'side' }, h('div', { class: 'brand' }, h('span', { class: 'logo' }, 'S'), 'Soul ERP'),
      h('nav', {}, tabs.map(([k, l]) => h('button', { class: k === tab ? 'act' : '', onclick: () => { tab = k; render(); } }, l))),
      h('div', { class: 'user' }, h('b', {}, S.name), h('small', {}, `${ROLE[S.role]}, ${S.sub}`), h('button', { class: 'ghost', onclick: logout }, 'Sign out'))),
    h('div', { class: 'content' }, h('header', { class: 'bar' }, h('h1', {}, tabs.find(t => t[0] === tab)[1]),
      h('div', { class: 'bar-r' }, S.role === 'super' ? badge('Read-only monitoring', 'warn') : [h('span', { class: 'hname' }, hs.name), badge(hs.open ? 'Open' : 'Closed', hs.open ? 'on' : 'off')])), h('main', {}, body))));
}

['click', 'keydown', 'touchstart'].forEach(ev => addEventListener(ev, touch, { passive: true }));
try {
  seed();
  const s = JSON.parse(sessionStorage.getItem('erp_s') || 'null');
  if (s && s.exp > Date.now() && s.role === PORTAL) { S = s; if (S.role !== 'super' && !hosp()) S = null; else touch(); }
  render();
} catch (x) { $('#app').append(h('p', { class: 'err pad' }, 'Could not start: ' + x.message + '. Browser storage may be blocked.')); }

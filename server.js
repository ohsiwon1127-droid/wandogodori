// 실시간 멀티플레이어 바카라 서버 (가상 칩 전용, 실제 결제/환전 없음)
require('dotenv').config();
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const express = require('express');
const http = require('http');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');
const { Server } = require('socket.io');
const { MongoClient } = require('mongodb');

const PORT = process.env.PORT || 3000;
const JWT_SECRET = process.env.JWT_SECRET || crypto.randomBytes(32).toString('hex');
const ADMIN_SIGNUP_CODE = process.env.ADMIN_SIGNUP_CODE || '';
const MONGODB_URI = process.env.MONGODB_URI || '';
const DATA_FILE = path.join(__dirname, 'data', 'users.json');

const BET_MS = 15000;      // 베팅 시간 (조금 늘림)
const REVEAL_MS = 8000;
const DECKS = 8;
const START_BALANCE = 0;   // 가입 축하 칩 없음 - 관리자 승인/충전 필요
const HISTORY_LIMIT = 44;  // 경기 기록 동그라미 최대 개수
const CHIP = '칩';
const ODDS = { player: 1, banker: 0.95, tie: 8, playerPair: 11, bankerPair: 11 };

if (!process.env.JWT_SECRET) {
  console.warn('[경고] JWT_SECRET 환경변수가 없어 재시작마다 임시 키를 사용합니다. 배포 시 반드시 지정하세요.');
}
if (!ADMIN_SIGNUP_CODE) {
  console.warn('[경고] ADMIN_SIGNUP_CODE가 없어 관리자 계정을 만들 수 없습니다.');
}
if (!MONGODB_URI) {
  console.warn('[경고] MONGODB_URI가 없어 로컬 파일에 저장합니다. Render 같은 호스팅에서는 재배포/재시작 시 데이터가 사라질 수 있습니다. README를 참고해 무료 DB를 연결하세요.');
}

// ---------- persistence layer ----------
// DB(MongoDB)가 있으면 그쪽을 진짜 저장소로 쓰고, 없으면 로컬 JSON 파일로 대체(로컬 테스트용, 재배포 시 유실 가능)
let db = null;
let usersCollection = null;

function fileLoadAll() {
  try { return JSON.parse(fs.readFileSync(DATA_FILE, 'utf8')); } catch (e) { return {}; }
}
function fileSaveAll() {
  try {
    fs.mkdirSync(path.dirname(DATA_FILE), { recursive: true });
    fs.writeFileSync(DATA_FILE, JSON.stringify(users, null, 2));
  } catch (e) { console.error('파일 저장 실패:', e.message); }
}

let users = {}; // usernameLower -> { username, passwordHash, balance, isAdmin, status, createdAt }

async function initPersistence() {
  if (MONGODB_URI) {
    const client = new MongoClient(MONGODB_URI);
    await client.connect();
    db = client.db(); // 연결 문자열에 db 이름이 없으면 기본 db 사용
    usersCollection = db.collection('users');
    const docs = await usersCollection.find({}).toArray();
    for (const doc of docs) {
      users[doc._id] = {
        username: doc.username, passwordHash: doc.passwordHash, balance: doc.balance,
        isAdmin: doc.isAdmin, status: doc.status || 'approved', createdAt: doc.createdAt,
      };
    }
    console.log(`[DB] MongoDB 연결 완료, 유저 ${docs.length}명 로드`);
  } else {
    users = fileLoadAll();
  }
}

async function persistUser(usernameLower) {
  const u = users[usernameLower];
  if (!u) return;
  if (usersCollection) {
    try {
      await usersCollection.updateOne(
        { _id: usernameLower },
        { $set: { username: u.username, passwordHash: u.passwordHash, balance: u.balance, isAdmin: u.isAdmin, status: u.status, createdAt: u.createdAt } },
        { upsert: true }
      );
    } catch (e) { console.error('DB 저장 실패:', e.message); }
  } else {
    fileSaveAll();
  }
}

function findByUsername(username) {
  return users[String(username).toLowerCase()] || null;
}

// 배포 플랫폼이 재시작 신호를 보낼 때 파일 모드라면 마지막으로 한 번 더 저장
function shutdown(signal) {
  console.log(`[${signal}] 종료 신호 수신, 저장 후 종료합니다...`);
  if (!usersCollection) { try { fileSaveAll(); } catch (e) {} }
  process.exit(0);
}
process.on('SIGINT', () => shutdown('SIGINT'));
process.on('SIGTERM', () => shutdown('SIGTERM'));

// ---------- card / baccarat logic ----------
const SUITS = ['♠', '♥', '♦', '♣'];
const SUIT_COLOR = { '♠': 'black', '♣': 'black', '♥': 'red', '♦': 'red' };
const RANKS = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];

function cardValue(rank) {
  if (rank === 'A') return 1;
  if (['10', 'J', 'Q', 'K'].includes(rank)) return 0;
  return parseInt(rank, 10);
}
function buildShoe() {
  const cards = [];
  for (let d = 0; d < DECKS; d++) {
    for (const suit of SUITS) {
      for (const rank of RANKS) cards.push({ rank, suit, color: SUIT_COLOR[suit] });
    }
  }
  for (let i = cards.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [cards[i], cards[j]] = [cards[j], cards[i]];
  }
  return cards;
}
function total(cards) {
  return cards.reduce((sum, c) => sum + cardValue(c.rank), 0) % 10;
}
function bankerShouldDraw(bankerTotal, playerThird) {
  if (bankerTotal <= 2) return true;
  if (bankerTotal === 3) return playerThird === null || playerThird !== 8;
  if (bankerTotal === 4) return playerThird !== null && playerThird >= 2 && playerThird <= 7;
  if (bankerTotal === 5) return playerThird !== null && playerThird >= 4 && playerThird <= 7;
  if (bankerTotal === 6) return playerThird !== null && (playerThird === 6 || playerThird === 7);
  return false;
}
function computeRound() {
  const shoe = buildShoe();
  let idx = 0;
  const p1 = shoe[idx++], b1 = shoe[idx++], p2 = shoe[idx++], b2 = shoe[idx++];
  const playerCards = [p1, p2];
  const bankerCards = [b1, b2];
  const playerPair = p1.rank === p2.rank;
  const bankerPair = b1.rank === b2.rank;
  let pTotal = total(playerCards);
  let bTotal = total(bankerCards);
  const natural = pTotal >= 8 || bTotal >= 8;
  let playerThirdVal = null;
  if (!natural) {
    if (pTotal <= 5) {
      const c = shoe[idx++];
      playerCards.push(c);
      playerThirdVal = cardValue(c.rank);
      pTotal = total(playerCards);
    }
    if (bankerShouldDraw(bTotal, playerThirdVal)) {
      const c = shoe[idx++];
      bankerCards.push(c);
      bTotal = total(bankerCards);
    }
  }
  const outcome = pTotal > bTotal ? 'player' : bTotal > pTotal ? 'banker' : 'tie';
  return { playerCards, bankerCards, pTotal, bTotal, outcome, playerPair, bankerPair, natural };
}
function settleBet(bet, round) {
  let payout = 0;
  const m = bet.main;
  if (m) {
    if (m.side === 'player') {
      if (round.outcome === 'player') payout += m.amount * 2;
      else if (round.outcome === 'tie') payout += m.amount;
    } else if (m.side === 'banker') {
      if (round.outcome === 'banker') payout += m.amount + Math.floor(m.amount * 0.95);
      else if (round.outcome === 'tie') payout += m.amount;
    } else if (m.side === 'tie') {
      if (round.outcome === 'tie') payout += m.amount * (1 + ODDS.tie);
    }
  }
  const pr = bet.pair;
  if (pr) {
    if (pr.side === 'playerPair' && round.playerPair) payout += pr.amount * (1 + ODDS.playerPair);
    if (pr.side === 'bankerPair' && round.bankerPair) payout += pr.amount * (1 + ODDS.bankerPair);
  }
  const risked = (m ? m.amount : 0) + (pr ? pr.amount : 0);
  return { payout, net: payout - risked };
}

// ---------- round state machine (single shared table) ----------
let currentRound = { id: 0, phase: 'betting', endsAt: 0, bets: new Map(), result: null };
let history = [];

function publicBetsList() {
  const list = [];
  for (const [username, bet] of currentRound.bets.entries()) list.push({ username, main: bet.main, pair: bet.pair });
  return list;
}
function betCounts() {
  let player = 0, banker = 0, tie = 0;
  for (const bet of currentRound.bets.values()) {
    if (bet.main.side === 'player') player++;
    else if (bet.main.side === 'banker') banker++;
    else if (bet.main.side === 'tie') tie++;
  }
  return { player, banker, tie };
}
function socketIdsFor(username) {
  const set = userSockets.get(username);
  return set ? Array.from(set) : [];
}
function pushBalance(username) {
  const u = findByUsername(username);
  if (!u) return;
  for (const sid of socketIdsFor(username)) io.to(sid).emit('balance:update', { balance: u.balance });
}
function broadcastPresence() { io.emit('presence:update', { count: userSockets.size }); }
function broadcastBets() { io.emit('bets:update', { roundId: currentRound.id, bets: publicBetsList(), counts: betCounts() }); }

function startBettingPhase() {
  currentRound = { id: currentRound.id + 1, phase: 'betting', endsAt: Date.now() + BET_MS, bets: new Map(), result: null };
  io.emit('round:betting', { roundId: currentRound.id, endsAt: currentRound.endsAt });
  broadcastBets();
  setTimeout(runReveal, BET_MS);
}

async function runReveal() {
  const round = computeRound();
  currentRound.phase = 'reveal';
  currentRound.result = round;
  currentRound.endsAt = Date.now() + REVEAL_MS;
  history = [round.outcome, ...history].slice(0, HISTORY_LIMIT);

  const settlements = {};
  const changedUsernames = [];
  for (const [username, bet] of currentRound.bets.entries()) {
    const { payout, net } = settleBet(bet, round);
    const u = findByUsername(username);
    if (u && payout > 0) { u.balance += payout; changedUsernames.push(username.toLowerCase()); }
    settlements[username] = { payout, net };
  }
  for (const lower of changedUsernames) await persistUser(lower);

  io.emit('round:reveal', { roundId: currentRound.id, endsAt: currentRound.endsAt, round, history });

  // 가장 많이 딴 사람 전체 공지
  let topWinner = null;
  for (const [username, s] of Object.entries(settlements)) {
    if (s.net > 0 && (!topWinner || s.net > topWinner.net)) topWinner = { username, net: s.net };
  }
  if (topWinner) io.emit('round:winner', topWinner);

  for (const [username, s] of Object.entries(settlements)) {
    const u = findByUsername(username);
    for (const sid of socketIdsFor(username)) {
      io.to(sid).emit('settle', { roundId: currentRound.id, ...s, balance: u ? u.balance : 0 });
    }
  }
  setTimeout(startBettingPhase, REVEAL_MS);
}

// ---------- auth helpers ----------
const USERNAME_RE = /^[a-zA-Z0-9_]{3,16}$/;

function signToken(user) { return jwt.sign({ u: user.username }, JWT_SECRET, { expiresIn: '30d' }); }
function verifyToken(token) {
  try { return findByUsername(jwt.verify(token, JWT_SECRET).u); } catch (e) { return null; }
}
function requireAuth(req, res, next) {
  const header = req.headers.authorization || '';
  const token = header.startsWith('Bearer ') ? header.slice(7) : null;
  const user = token ? verifyToken(token) : null;
  if (!user) return res.status(401).json({ error: '로그인이 필요합니다.' });
  req.user = user;
  next();
}
function requireAdmin(req, res, next) {
  if (!req.user || !req.user.isAdmin) return res.status(403).json({ error: '관리자 권한이 필요합니다.' });
  next();
}

// ---------- express app ----------
const app = express();
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

app.get('/', (req, res) => res.redirect('/login.html'));
app.get('/health', (req, res) => res.json({ ok: true, time: Date.now() }));

app.post('/api/signup', async (req, res) => {
  const { username, password, adminCode } = req.body || {};
  if (!USERNAME_RE.test(username || '')) {
    return res.status(400).json({ error: '아이디는 영문/숫자/밑줄 3~16자여야 합니다.' });
  }
  if (!password || password.length < 4) {
    return res.status(400).json({ error: '비밀번호는 4자 이상이어야 합니다.' });
  }
  if (findByUsername(username)) {
    return res.status(409).json({ error: '이미 사용 중인 아이디입니다.' });
  }
  const passwordHash = await bcrypt.hash(password, 10);
  const isAdmin = !!(ADMIN_SIGNUP_CODE && adminCode && adminCode === ADMIN_SIGNUP_CODE);
  const status = isAdmin ? 'approved' : 'pending';
  const user = { username, passwordHash, balance: START_BALANCE, isAdmin, status, createdAt: Date.now() };
  users[username.toLowerCase()] = user;
  await persistUser(username.toLowerCase());

  if (status === 'pending') {
    return res.json({ pending: true, message: '가입 신청이 완료되었습니다. 관리자 승인 후 로그인할 수 있어요.' });
  }
  const token = signToken(user);
  res.json({ token, username: user.username, isAdmin: user.isAdmin, balance: user.balance });
});

app.post('/api/login', async (req, res) => {
  const { username, password } = req.body || {};
  const user = findByUsername(username || '');
  if (!user) return res.status(401).json({ error: '아이디 또는 비밀번호가 올바르지 않습니다.' });
  const ok = await bcrypt.compare(password || '', user.passwordHash);
  if (!ok) return res.status(401).json({ error: '아이디 또는 비밀번호가 올바르지 않습니다.' });
  if (user.status !== 'approved') return res.status(403).json({ error: '관리자 승인 대기 중입니다. 승인 후 로그인해주세요.' });
  const token = signToken(user);
  res.json({ token, username: user.username, isAdmin: user.isAdmin, balance: user.balance });
});

app.get('/api/me', requireAuth, (req, res) => {
  res.json({ username: req.user.username, isAdmin: req.user.isAdmin, balance: req.user.balance });
});

app.get('/api/admin/users', requireAuth, requireAdmin, (req, res) => {
  const list = Object.values(users).map(u => ({
    username: u.username, balance: u.balance, isAdmin: u.isAdmin, status: u.status, createdAt: u.createdAt,
  })).sort((a, b) => a.username.localeCompare(b.username));
  res.json({ users: list });
});

app.post('/api/admin/approve', requireAuth, requireAdmin, async (req, res) => {
  const target = findByUsername((req.body || {}).username || '');
  if (!target) return res.status(404).json({ error: '해당 유저를 찾을 수 없습니다.' });
  target.status = 'approved';
  await persistUser(target.username.toLowerCase());
  res.json({ username: target.username, status: target.status });
});

app.post('/api/admin/reject', requireAuth, requireAdmin, async (req, res) => {
  const usernameLower = String((req.body || {}).username || '').toLowerCase();
  const target = users[usernameLower];
  if (!target) return res.status(404).json({ error: '해당 유저를 찾을 수 없습니다.' });
  delete users[usernameLower];
  if (usersCollection) { try { await usersCollection.deleteOne({ _id: usernameLower }); } catch (e) {} }
  else fileSaveAll();
  res.json({ username: target.username, deleted: true });
});

// 충전/차감 겸용: amount가 양수면 충전, 음수면 차감 (잘못 충전했을 때 되돌리는 용도)
app.post('/api/admin/recharge', requireAuth, requireAdmin, async (req, res) => {
  const { username, amount } = req.body || {};
  const target = findByUsername(username || '');
  const amt = Math.trunc(Number(amount));
  if (!target) return res.status(404).json({ error: '해당 유저를 찾을 수 없습니다.' });
  if (!Number.isFinite(amt) || amt === 0 || Math.abs(amt) > 1000000) {
    return res.status(400).json({ error: `${CHIP} 조정 값이 올바르지 않습니다. (0이 아닌 -1,000,000 ~ 1,000,000)` });
  }
  const newBalance = target.balance + amt;
  if (newBalance < 0) {
    return res.status(400).json({ error: `차감 후 잔액이 음수가 됩니다. (현재 ${target.balance.toLocaleString('en-US')}${CHIP})` });
  }
  target.balance = newBalance;
  await persistUser(target.username.toLowerCase());
  pushBalance(target.username);
  res.json({ username: target.username, balance: target.balance });
});

const server = http.createServer(app);
const io = new Server(server);

const userSockets = new Map(); // username -> Set<socketId>

io.use((socket, next) => {
  const token = socket.handshake.auth && socket.handshake.auth.token;
  const user = token ? verifyToken(token) : null;
  if (!user) return next(new Error('인증 실패'));
  if (user.status !== 'approved') return next(new Error('승인 대기 중'));
  socket.data.username = user.username;
  next();
});

io.on('connection', (socket) => {
  const username = socket.data.username;
  if (!userSockets.has(username)) userSockets.set(username, new Set());
  userSockets.get(username).add(socket.id);

  const u = findByUsername(username);
  socket.emit('joined', {
    username,
    balance: u ? u.balance : 0,
    isAdmin: u ? u.isAdmin : false,
    round: { id: currentRound.id, phase: currentRound.phase, endsAt: currentRound.endsAt, result: currentRound.result },
    history,
    myBet: currentRound.bets.get(username) || null,
    bets: publicBetsList(),
    counts: betCounts(),
  });
  broadcastPresence();

  socket.on('placeBet', async ({ main, pair }) => {
    if (currentRound.phase !== 'betting') return;
    if (currentRound.bets.has(username)) return;
    if (!main || !main.side || !(main.amount > 0)) return;
    if (!['player', 'banker', 'tie'].includes(main.side)) return;

    let pairBet = null;
    if (pair && pair.side && pair.side !== 'none') {
      if (!['playerPair', 'bankerPair'].includes(pair.side)) return;
      if (!(pair.amount > 0)) return;
      pairBet = { side: pair.side, amount: Math.floor(pair.amount) };
    }
    const mainBet = { side: main.side, amount: Math.floor(main.amount) };
    const totalStake = mainBet.amount + (pairBet ? pairBet.amount : 0);

    const target = findByUsername(username);
    if (!target || target.balance < totalStake) {
      socket.emit('errorMsg', { message: `${CHIP}이 부족합니다. 관리자에게 충전을 요청하세요.` });
      return;
    }
    target.balance -= totalStake;
    currentRound.bets.set(username, { main: mainBet, pair: pairBet });
    await persistUser(username.toLowerCase());

    pushBalance(username);
    broadcastBets();
  });

  socket.on('disconnect', () => {
    const set = userSockets.get(username);
    if (set) { set.delete(socket.id); if (set.size === 0) userSockets.delete(username); }
    broadcastPresence();
  });
});

(async () => {
  await initPersistence();
  startBettingPhase();
  server.listen(PORT, () => {
    console.log(`바카라 라이브 테이블 서버 실행 중: http://localhost:${PORT}`);
  });
})();

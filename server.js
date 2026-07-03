// Ten 2026 — online multiplayer server
// Zero dependencies: runs on stock Node 18+ with `node server.js`
// Rooms with 4-letter codes, bots fill empty seats, hands stay server-side.

"use strict";
const http = require("http");
const crypto = require("crypto");

const PORT = process.env.PORT || 3000;

/* ===================== Card model ===================== */
const SUITS = ["S", "H", "D", "C"];
const SUIT_NAME = { S: "Spades", H: "Hearts", D: "Diamonds", C: "Clubs" };
const NEXT = { 0: 1, 1: 2, 2: 3, 3: 0 };
const TEAM_OF = ["A", "B", "A", "B"]; // seats 0&2 vs 1&3

function freshDeck() {
  const d = [];
  for (const s of SUITS) for (let r = 2; r <= 14; r++) d.push({ suit: s, rank: r });
  return d;
}
function shuffle(a) {
  a = a.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function rankLabel(r) {
  return { 11: "J", 12: "Q", 13: "K", 14: "A" }[r] || String(r);
}
function sameCard(a, b) { return a.suit === b.suit && a.rank === b.rank; }

/* ===================== Game (one room's engine) ===================== */
class Game {
  constructor(room) {
    this.room = room;
    this.version = 0;
    this.phase = "lobby"; // lobby -> draw -> trump -> reveal -> playing -> over
    this.players = [null, null, null, null];
    this.hostToken = null;
    this.seriesPicker = null;      // seat that picks trump next hand; null = draw needed
    this.seriesWins = { A: 0, B: 0 };
    this.reset();
  }

  reset() {
    this.trump = null;
    this.hands = [[], [], [], []];
    this.trick = [];
    this.turn = 0;
    this.leader = 0;
    this.picker = 0;
    this.teamTens = { A: 0, B: 0 };
    this.teamHouses = { A: 0, B: 0 };
    this.captured = { A: [], B: [] }; // {hasTen, tenCards:[]}
    this.tenOwner = {};
    this.seen = [];
    this.voids = [{}, {}, {}, {}];
    this.locked = false;
    this.sweepDecided = false;
    this.sweepPrompt = null; // {team} when a human team must decide
    this.fifthAnnounced = false;
    this.pool = this.pool || []; // names of players who haven't picked a team yet
    this.drawResults = null;
    this.drawDeck = [];
    this.drawTurn = 0;
    this.trumpOptions = null;
    this.status = "";
    this.result = null;
    this.deck = [];
    this.timers = [];
  }

  bump() { this.version++; }
  say(t) { this.status = t; this.bump(); }
  after(ms, fn) {
    const id = setTimeout(() => { fn(); }, ms);
    this.timers.push(id);
  }
  clearTimers() { this.timers.forEach(clearTimeout); this.timers = []; }

  seatName(s) { return this.players[s] ? this.players[s].name : "—"; }
  isBot(s) { return !this.players[s] || this.players[s].bot; }

  /* ---------- start: interactive draw, then trump ---------- */
  startHand() {
    this.clearTimers();
    const keepPlayers = this.players, host = this.hostToken;
    this.reset();
    this.players = keepPlayers;
    this.hostToken = host;

    if (this.seriesPicker != null) {
      // series continues: winners hold the pick, no draw
      this.picker = this.seriesPicker;
      this.leader = this.seriesPicker;
      this.beginTrumpPhase();
      return;
    }
    this.phase = "draw";
    this.drawDeck = shuffle(freshDeck());
    this.drawResults = [];
    this.drawTurn = 0;
    this.say(this.seatName(0) + " draws first — pick a card. Highest card picks trump.");
    this.scheduleBotDraw();
  }

  scheduleBotDraw() {
    if (this.phase !== "draw") return;
    if (this.drawTurn > 3) return;
    if (!this.isBot(this.drawTurn)) return;
    const seat = this.drawTurn;
    this.after(1100, () => {
      if (this.phase === "draw" && this.drawTurn === seat) this.doDraw(seat);
    });
  }

  doDraw(seat) {
    if (this.phase !== "draw" || this.drawTurn !== seat) return { ok: false, err: "Not your draw." };
    const card = this.drawDeck.pop();
    this.drawResults.push({ seat, card });
    this.drawTurn++;
    if (this.drawTurn <= 3) {
      this.say(this.seatName(seat) + " drew the " + rankLabel(card.rank) + " of " + SUIT_NAME[card.suit] + ". " + this.seatName(this.drawTurn) + " draws next.");
      this.scheduleBotDraw();
    } else {
      this.say(this.seatName(seat) + " drew the " + rankLabel(card.rank) + " of " + SUIT_NAME[card.suit] + ".");
      this.after(900, () => this.resolveDraw());
    }
    return { ok: true };
  }

  resolveDraw() {
    const results = this.drawResults;
    const byTeam = (t) => results.filter((r) => TEAM_OF[r.seat] === t).map((r) => r.card.rank).sort((a, b) => b - a);
    const a = byTeam("A"), b = byTeam("B");
    let winTeam = null;
    if (a[0] !== b[0]) winTeam = a[0] > b[0] ? "A" : "B";
    else if (a[1] !== b[1]) winTeam = a[1] > b[1] ? "A" : "B"; // second-card tiebreak, like the table rule
    if (!winTeam) {
      this.say("Dead tie — redrawing.");
      this.after(1200, () => {
        this.drawDeck = shuffle(freshDeck());
        this.drawResults = [];
        this.drawTurn = 0;
        this.say(this.seatName(0) + " draws first — pick a card.");
        this.scheduleBotDraw();
        this.bump();
      });
      return;
    }
    const highest = results.slice().sort((x, y) => y.card.rank - x.card.rank)[0];
    this.picker = highest.seat;
    this.leader = highest.seat;
    this.beginTrumpPhase();
  }

  beginTrumpPhase() {
    // deal first five, 5-4-4 style
    this.deck = shuffle(freshDeck());
    this.hands = [[], [], [], []];
    let s = this.picker;
    for (let round = 0; round < 5; round++)
      for (let i = 0; i < 4; i++) { this.hands[s].push(this.deck.pop()); s = NEXT[s]; }

    this.phase = "trump";
    const suitsHeld = [...new Set(this.hands[this.picker].map((c) => c.suit))];
    this.trumpOptions = suitsHeld;
    this.say(this.seatName(this.picker) + " drew highest and picks trump from their first five.");

    if (this.isBot(this.picker)) {
      this.after(1600, () => {
        const hand5 = this.hands[this.picker];
        const best = suitsHeld
          .map((su) => {
            const cs = hand5.filter((c) => c.suit === su);
            return { su, n: cs.length, w: cs.reduce((t, c) => t + c.rank, 0) };
          })
          .sort((a, b) => b.n - a.n || b.w - a.w)[0];
        this.setTrump(best.su);
      });
    }
  }

  setTrump(suit) {
    if (!this.trumpOptions.includes(suit)) return false;
    this.trump = suit;
    // deal the rest: 4 each, then 4 each
    let s = this.picker;
    for (let round = 0; round < 8; round++)
      for (let i = 0; i < 4; i++) { this.hands[s].push(this.deck.pop()); s = NEXT[s]; }
    for (const h of this.hands)
      h.sort((a, b) => SUITS.indexOf(a.suit) - SUITS.indexOf(b.suit) || a.rank - b.rank);
    this.phase = "reveal";
    this.say(this.seatName(this.picker) + " chose " + SUIT_NAME[suit] + " as trump.");
    this.after(3000, () => {
      this.phase = "playing";
      this.turn = this.leader;
      this.say(this.seatName(this.turn) + " leads the first round.");
      this.after(900, () => this.advanceIfBot());
    });
    return true;
  }

  /* ---------- rules ---------- */
  legalPlays(seat) {
    const hand = this.hands[seat];
    if (!this.trick.length) return hand.slice();
    const led = this.trick[0].card.suit;
    const m = hand.filter((c) => c.suit === led);
    return m.length ? m : hand.slice();
  }
  cardBeats(a, b, led, trump) {
    const aT = a.suit === trump, bT = b.suit === trump;
    if (aT && bT) return b.rank > a.rank;
    if (aT) return false;
    if (bT) return true;
    if (a.suit === led && b.suit === led) return b.rank > a.rank;
    return false;
  }
  trickWinner(trick, trump) {
    const led = trick[0].card.suit;
    let best = trick[0];
    for (let i = 1; i < trick.length; i++)
      if (this.cardBeats(best.card, trick[i].card, led, trump)) best = trick[i];
    return best.seat;
  }

  playCard(seat, card) {
    if (this.phase !== "playing" || this.locked || this.turn !== seat) return { ok: false, err: "Not your turn." };
    const legal = this.legalPlays(seat);
    if (!legal.some((c) => sameCard(c, card))) {
      const led = this.trick.length ? this.trick[0].card.suit : null;
      return { ok: false, err: led ? "You must follow suit (" + SUIT_NAME[led] + ")." : "Illegal card." };
    }
    const idx = this.hands[seat].findIndex((c) => sameCard(c, card));
    if (idx === -1) return { ok: false, err: "Card not in hand." };

    this.seen.push(card);
    if (this.trick.length && card.suit !== this.trick[0].card.suit) this.voids[seat][this.trick[0].card.suit] = true;

    this.hands[seat].splice(idx, 1);
    this.trick.push({ seat, card });

    if (this.trick.length === 4) {
      this.locked = true;
      this.bump();
      this.after(1300, () => this.resolveTrick());
    } else {
      this.turn = NEXT[seat];
      this.say(this.seatName(this.turn) + "'s turn.");
      this.after(900, () => this.advanceIfBot());
    }
    return { ok: true };
  }

  resolveTrick() {
    const winnerSeat = this.trickWinner(this.trick, this.trump);
    const winnerTeam = TEAM_OF[winnerSeat];
    const tens = this.trick.filter((t) => t.card.rank === 10);
    const hasTen = tens.length > 0;

    if (hasTen) {
      this.teamTens[winnerTeam] += tens.length;
      tens.forEach((t) => (this.tenOwner[t.card.suit] = winnerTeam));
    } else this.teamHouses[winnerTeam]++;

    this.captured[winnerTeam].push({ hasTen, tenCards: tens.map((t) => t.card) });

    this.trick = [];
    this.leader = winnerSeat;
    this.turn = winnerSeat;
    this.say(this.seatName(winnerSeat) + (hasTen ? (tens.length > 1 ? " takes TWO tens!" : " takes the ten!") : " takes the house."));

    const totalTens = this.teamTens.A + this.teamTens.B;
    const allOut = totalTens === 4;
    const cardsLeft = this.hands[0].length > 0;
    const split22 = this.teamTens.A === 2 && this.teamTens.B === 2;
    const q25 = (t) => this.teamTens[t] === 2 && this.teamHouses[t] >= 5;
    const done25 = q25("A") || q25("B");
    const handOver = !cardsLeft || done25 || (allOut && !split22);

    this.after(1100, () => {
      this.locked = false;
      if (handOver) return this.finishHand();

      const threeTeam = this.teamTens.A === 3 ? "A" : this.teamTens.B === 3 ? "B" : null;
      if (threeTeam && !this.sweepDecided) {
        this.sweepDecided = true;
        const teamSeats = threeTeam === "A" ? [0, 2] : [1, 3];
        const humanOnTeam = teamSeats.some((s) => !this.isBot(s));
        if (humanOnTeam) {
          this.locked = true;
          this.sweepPrompt = { team: threeTeam };
          this.say((threeTeam === "A" ? "Team " + this.seatName(0) : "Team " + this.seatName(1)) + " has three tens — take the win or play for the sweep?");
          return;
        }
        const lastTenSuit = SUITS.find((su) => !this.tenOwner[su]);
        const holdsIt = teamSeats.some((s) => this.hands[s].some((c) => c.rank === 10 && c.suit === lastTenSuit));
        if (!holdsIt) { this.say("Three tens — they take the win."); this.after(900, () => this.finishHand()); return; }
        this.say("Three tens — they're playing on for the sweep!");
      }

      const fifthFight = allOut && split22 && !this.fifthAnnounced;
      if (fifthFight) this.fifthAnnounced = true;
      this.say((fifthFight ? "Tens split 2-2 — it all comes down to the fifth house! " : "") + this.seatName(this.turn) + " leads next.");
      this.after(800, () => this.advanceIfBot());
    });
  }

  sweepChoice(playOn) {
    if (!this.sweepPrompt) return { ok: false, err: "No decision pending." };
    this.sweepPrompt = null;
    this.locked = false;
    if (!playOn) { this.finishHand(); return { ok: true }; }
    this.say("Playing on for the sweep. " + this.seatName(this.turn) + " leads next.");
    this.after(700, () => this.advanceIfBot());
    return { ok: true };
  }

  finishHand() {
    // hard rule: 2-2 tens can only end on a 5th house or empty hands
    const split22 = this.teamTens.A === 2 && this.teamTens.B === 2;
    if (split22 && this.hands[0].length > 0 && this.teamHouses.A < 5 && this.teamHouses.B < 5) {
      this.locked = false;
      this.say("Tens split 2-2 — the fifth house decides it. Play on!");
      this.after(700, () => this.advanceIfBot());
      return;
    }
    const q = (t) => this.teamTens[t] >= 3 || (this.teamTens[t] >= 2 && this.teamHouses[t] >= 5);
    let winner = null;
    if (q("A") && !q("B")) winner = "A";
    else if (q("B") && !q("A")) winner = "B";
    else if (this.teamTens.A !== this.teamTens.B) winner = this.teamTens.A > this.teamTens.B ? "A" : "B";
    else if (this.teamHouses.A !== this.teamHouses.B) winner = this.teamHouses.A > this.teamHouses.B ? "A" : "B";

    const sweep = this.teamTens.A === 4 || this.teamTens.B === 4;
    if (winner) {
      this.seriesWins[winner]++;
      if (TEAM_OF[this.picker] === winner) {
        this.seriesPicker = this.picker; // winners keep the pick
      } else {
        let s = NEXT[this.picker];
        while (TEAM_OF[s] !== winner) s = NEXT[s];
        this.seriesPicker = s; // pick passes clockwise onto the winning team
      }
    }
    this.phase = "over";
    this.result = {
      winner,
      sweep,
      tensA: this.teamTens.A, housesA: this.teamHouses.A,
      tensB: this.teamTens.B, housesB: this.teamHouses.B,
    };
    this.say(winner ? "Team " + (winner === "A" ? this.seatName(0) + "/" + this.seatName(2) : this.seatName(1) + "/" + this.seatName(3)) + " wins the hand" + (sweep ? " — with a sweep plint!" : "!") : "Hand tied.");
  }

  /* ---------- bots: the same strategy as the solo game ---------- */
  advanceIfBot() {
    if (this.phase !== "playing" || this.locked) return;
    if (!this.isBot(this.turn)) return;
    const card = this.botChoose(this.turn);
    this.playCard(this.turn, card);
  }

  unseenBy(seat) {
    const known = this.seen.concat(this.hands[seat], this.trick.map((t) => t.card));
    return freshDeck().filter((c) => !known.some((k) => sameCard(k, c)));
  }
  isBoss(card, unseen) { return !unseen.some((c) => c.suit === card.suit && c.rank > card.rank); }
  seatsStillToPlay() {
    const played = new Set(this.trick.map((t) => t.seat));
    const out = [];
    let s = this.turn;
    for (let i = 0; i < 4; i++) { if (!played.has(s)) out.push(s); s = NEXT[s]; }
    return out.slice(1);
  }
  oppsBehind(seat) { return this.seatsStillToPlay().filter((s) => TEAM_OF[s] !== TEAM_OF[seat]); }
  winsForSure(seat, card, unseen) {
    const hyp = this.trick.concat([{ seat, card }]);
    if (this.trickWinner(hyp, this.trump) !== seat) return false;
    if (!this.seatsStillToPlay().length) return true;
    const led = this.trick.length ? this.trick[0].card.suit : card.suit;
    return !unseen.some((c) => this.cardBeats(card, c, led, this.trump));
  }
  safeForTeam(seat, unseen) {
    if (!this.trick.length) return false;
    const w = this.trickWinner(this.trick, this.trump);
    if (TEAM_OF[w] !== TEAM_OF[seat]) return false;
    if (!this.oppsBehind(seat).length) return true;
    const winCard = this.trick.find((t) => t.seat === w).card;
    const led = this.trick[0].card.suit;
    return !unseen.some((c) => this.cardBeats(winCard, c, led, this.trump));
  }
  pickRinse(seat, pool) {
    const nonTen = pool.filter((c) => c.rank !== 10);
    if (!nonTen.length) return pool.slice().sort((a, b) => a.rank - b.rank)[0];
    const hand = this.hands[seat];
    const tenSuits = {};
    hand.forEach((c) => { if (c.rank === 10) tenSuits[c.suit] = true; });
    const groups = {};
    nonTen.forEach((c) => (groups[c.suit] = groups[c.suit] || []).push(c));
    const order = Object.keys(groups).sort((s1, s2) => {
      const g = (tenSuits[s1] ? 1 : 0) - (tenSuits[s2] ? 1 : 0);
      if (g) return g;
      const t = (s1 === this.trump ? 1 : 0) - (s2 === this.trump ? 1 : 0);
      if (t) return t;
      return hand.filter((c) => c.suit === s1).length - hand.filter((c) => c.suit === s2).length;
    });
    return groups[order[0]].sort((a, b) => a.rank - b.rank)[0];
  }

  botChoose(seat) {
    const legal = this.legalPlays(seat);
    if (legal.length === 1) return legal[0];
    const trump = this.trump;
    const unseen = this.unseenBy(seat);
    const myTens = legal.filter((c) => c.rank === 10);
    const nonTens = legal.filter((c) => c.rank !== 10);

    if (!this.trick.length) {
      const safeTen = myTens.find((t) => this.isBoss(t, unseen) && (t.suit === trump || !unseen.some((c) => c.suit === trump)));
      if (safeTen) return safeTen;
      const bosses = nonTens
        .filter((c) => c.suit !== trump && this.isBoss(c, unseen))
        .filter((c) => !this.oppsBehind(seat).some((s) => this.voids[s][c.suit]))
        .sort((a, b) => b.rank - a.rank);
      if (bosses.length) return bosses[0];
      const tenSuits = new Set(this.hands[seat].filter((c) => c.rank === 10).map((c) => c.suit));
      const probe = nonTens.filter((c) => tenSuits.has(c.suit) && c.suit !== trump && c.rank < 10).sort((a, b) => a.rank - b.rank);
      if (probe.length) return probe[0];
      const quiet = nonTens
        .filter((c) => c.suit !== trump)
        .filter((c) => !this.oppsBehind(seat).some((s) => this.voids[s][c.suit]))
        .sort((a, b) => a.rank - b.rank);
      if (quiet.length) return quiet[0];
      const low = nonTens.sort((a, b) => a.rank - b.rank);
      return low.length ? low[0] : legal.slice().sort((a, b) => a.rank - b.rank)[0];
    }

    const led = this.trick[0].card.suit;
    const trickHasTen = this.trick.some((t) => t.card.rank === 10);
    const curWin = this.trickWinner(this.trick, trump);
    const partnerWinning = TEAM_OF[curWin] === TEAM_OF[seat];
    const winners = legal
      .filter((c) => this.trickWinner(this.trick.concat([{ seat, card: c }]), trump) === seat)
      .sort((a, b) => a.rank - b.rank);
    const sure = winners.filter((c) => this.winsForSure(seat, c, unseen));

    if (trickHasTen && !partnerWinning) {
      if (sure.length) {
        const nts = sure.filter((c) => c.rank !== 10);
        return nts.length ? nts[0] : sure[0];
      }
      const ntw = winners.filter((c) => c.rank !== 10);
      if (ntw.length) return ntw[0];
      return this.pickRinse(seat, legal);
    }

    if (partnerWinning) {
      const safe = this.safeForTeam(seat, unseen);
      if (safe && myTens.length) return myTens[0];
      if (safe) return this.pickRinse(seat, legal);
      const cheapSure = sure.filter((c) => c.rank !== 10);
      if (cheapSure.length && trickHasTen) return cheapSure[0];
      return this.pickRinse(seat, legal);
    }

    // enemy winning a plain house — card economy
    const myTeam = TEAM_OF[seat], oppTeam = myTeam === "A" ? "B" : "A";
    const critical =
      (this.teamTens[oppTeam] >= 2 && this.teamHouses[oppTeam] >= 4) ||
      (this.teamTens[myTeam] >= 2 && this.teamHouses[myTeam] >= 4);
    const tensDone = this.teamTens.A + this.teamTens.B === 4;
    const late = this.hands[seat].length <= 4;
    const honorsFree = critical || tensDone || late;
    const isHonor = (c) => c.suit === trump && c.rank >= 11;

    if (sure.length) {
      const tenSure = sure.find((c) => c.rank === 10);
      if (tenSure) return tenSure;
      const nts = sure.filter((c) => c.rank !== 10);
      const nonTrumpSure = nts.filter((c) => c.suit !== trump);
      if (nonTrumpSure.length) return nonTrumpSure[0];
      const cheapTrump = nts.filter((c) => c.suit === trump && c.rank < 11);
      if (cheapTrump.length) return cheapTrump[0];
      if (nts.length && honorsFree) return nts[0];
    }
    if (winners.length && !this.seatsStillToPlay().length) {
      const ntw = winners.filter((c) => c.rank !== 10);
      const afford = ntw.filter((c) => !isHonor(c));
      if (afford.length) return afford[0];
      if (ntw.length && honorsFree) return ntw[0];
    }

    const enemyWinCard = this.trick.find((t) => t.seat === curWin).card;
    const enemyBehind = this.oppsBehind(seat).length > 0;
    const ledTenAtLarge = unseen.some((c) => c.suit === led && c.rank === 10);

    if (!trickHasTen && enemyBehind && ledTenAtLarge && enemyWinCard.suit === led && enemyWinCard.rank < 10) {
      const climb = winners.filter((c) => c.suit === led && c.rank > 10).sort((a, b) => a.rank - b.rank);
      if (climb.length) return climb[0];
    }
    if (winners.length && enemyWinCard.suit !== trump) {
      const strong = enemyWinCard.rank >= 11 || this.isBoss(enemyWinCard, unseen);
      if (strong) {
        const tw = winners.filter((c) => c.suit === trump && c.rank !== 10).sort((a, b) => a.rank - b.rank);
        const afford = tw.filter((c) => c.rank < 11);
        if (afford.length) return afford[0];
        if (tw.length && honorsFree) return tw[0];
      }
    }
    if (winners.length && ledTenAtLarge) {
      const someoneMustFollow = this.seatsStillToPlay().some((s) => !this.voids[s][led]);
      if (someoneMustFollow) {
        const cheapW = winners.filter((c) => c.rank !== 10 && !isHonor(c));
        if (cheapW.length) return cheapW[0];
        const honorW = winners.filter((c) => c.rank !== 10);
        const trumpCount = this.hands[seat].filter((x) => x.suit === trump).length;
        if (honorW.length && (trumpCount <= 2 || late)) return honorW[0];
      }
    }
    return this.pickRinse(seat, legal);
  }

  /* ---------- per-seat view (hand privacy lives here) ---------- */
  snapshot(seat, isHost) {
    return {
      v: this.version,
      host: !!isHost,
      pool: this.pool.slice(),
      phase: this.phase,
      youAre: seat,
      names: this.players.map((p, i) => (p ? p.name : null)),
      bots: this.players.map((p) => !p || p.bot),
      trump: this.trump,
      turn: this.turn,
      locked: this.locked,
      status: this.status,
      hand: seat != null ? this.hands[seat] : [],
      handCounts: this.hands.map((h) => h.length),
      legal: seat != null && this.phase === "playing" && this.turn === seat && !this.locked ? this.legalPlays(seat) : [],
      trick: this.trick,
      teamTens: this.teamTens,
      teamHouses: this.teamHouses,
      captured: {
        A: this.captured.A.map((t) => ({ hasTen: t.hasTen, tenCards: t.tenCards })),
        B: this.captured.B.map((t) => ({ hasTen: t.hasTen, tenCards: t.tenCards })),
      },
      drawResults: this.drawResults,
      drawTurn: this.phase === "draw" ? this.drawTurn : null,
      picker: this.picker,
      trumpOptions: this.phase === "trump" && seat === this.picker ? this.trumpOptions : null,
      pickerFive: this.phase === "trump" && seat === this.picker ? this.hands[seat] : null,
      seriesWins: this.seriesWins,
      seriesPickerName: this.seriesPicker != null ? this.seatName(this.seriesPicker) : null,
      sweepPrompt:
        this.sweepPrompt && seat != null && TEAM_OF[seat] === this.sweepPrompt.team && !this.isBot(seat)
          ? true : false,
      result: this.result,
    };
  }
}

/* ===================== Rooms & HTTP API ===================== */
const rooms = new Map(); // code -> {game, tokens: Map<token, seat>, created}

function newCode() {
  const A = "ABCDEFGHJKMNPQRSTUVWXYZ23456789";
  for (;;) {
    let c = "";
    for (let i = 0; i < 4; i++) c += A[crypto.randomInt(A.length)];
    if (!rooms.has(c)) return c;
  }
}
function newToken() { return crypto.randomBytes(12).toString("hex"); }

// prune rooms older than 6 hours
setInterval(() => {
  const cutoff = Date.now() - 6 * 3600 * 1000;
  for (const [code, r] of rooms) if (r.created < cutoff) { r.game.clearTimers(); rooms.delete(code); }
}, 15 * 60 * 1000).unref();

function json(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, {
    "Content-Type": "application/json",
    "Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Headers": "Content-Type",
    "Access-Control-Allow-Methods": "GET,POST,OPTIONS",
  });
  res.end(body);
}

const server = http.createServer((req, res) => {
  if (req.method === "OPTIONS") return json(res, 204, {});
  const url = new URL(req.url, "http://x");
  const path = url.pathname;

  if (req.method === "GET" && path === "/") return json(res, 200, { ok: true, game: "Ten 2026", rooms: rooms.size });

  if (req.method === "GET" && path === "/state") {
    const room = rooms.get((url.searchParams.get("room") || "").toUpperCase());
    if (!room) return json(res, 404, { err: "Room not found." });
    const tok = url.searchParams.get("token");
    const seat = room.tokens.get(tok);
    return json(res, 200, room.game.snapshot(seat != null ? seat : null, tok === room.game.hostToken));
  }

  if (req.method !== "POST") return json(res, 404, { err: "Not found." });

  let body = "";
  req.on("data", (d) => { body += d; if (body.length > 10000) req.destroy(); });
  req.on("end", () => {
    let data = {};
    try { data = JSON.parse(body || "{}"); } catch (_) { return json(res, 400, { err: "Bad JSON." }); }

    if (path === "/create") {
      const code = newCode();
      const game = new Game(code);
      const token = newToken();
      const name = String(data.name || "Player").slice(0, 14) || "Player";
      game.hostToken = token;
      game.pool.push(name);
      game.say("Waiting for players... share code " + code);
      const entry = { game, tokens: new Map([[token, null]]), names: new Map([[token, name]]), created: Date.now() };
      rooms.set(code, entry);
      return json(res, 200, { room: code, token, seat: null });
    }

    const room = rooms.get(String(data.room || "").toUpperCase());
    if (!room) return json(res, 404, { err: "Room not found." });
    const game = room.game;

    if (path === "/join") {
      if (game.phase !== "lobby") return json(res, 400, { err: "Game already started." });
      if (room.tokens.size >= 4) return json(res, 400, { err: "Room is full." });
      const token = newToken();
      const name = String(data.name || "Player").slice(0, 14) || "Player";
      room.tokens.set(token, null);
      room.names.set(token, name);
      game.pool.push(name);
      game.say(name + " joined — pick a team!");
      return json(res, 200, { room: game.room, token, seat: null });
    }

    if (!room.tokens.has(data.token)) return json(res, 403, { err: "Bad token." });
    const seat = room.tokens.get(data.token); // null until a team is chosen

    if (path === "/team") {
      if (game.phase !== "lobby") return json(res, 400, { err: "Teams can only change in the lobby." });
      const want = data.team === "A" ? [0, 2] : data.team === "B" ? [1, 3] : null;
      if (!want) return json(res, 400, { err: "Bad team." });
      const name = room.names.get(data.token) || "Player";
      if (seat != null && want.includes(seat)) return json(res, 200, { ok: true, seat });
      const target = want.find((s) => !game.players[s]);
      if (target == null) return json(res, 400, { err: "That team is full." });
      if (seat != null) game.players[seat] = null;
      else game.pool = game.pool.filter((n) => n !== name);
      game.players[target] = { name, bot: false };
      room.tokens.set(data.token, target);
      game.say(name + " joined Team " + data.team + ".");
      return json(res, 200, { ok: true, seat: target });
    }

    if (path === "/start") {
      if (data.token !== game.hostToken) return json(res, 403, { err: "Only the host can start." });
      if (game.phase !== "lobby" && game.phase !== "over") return json(res, 400, { err: "Already running." });
      // seat anyone who never picked a team
      for (const [tok, st] of room.tokens) {
        if (st != null) continue;
        const free = [0, 1, 2, 3].find((s) => !game.players[s]);
        if (free == null) break;
        const nm = room.names.get(tok) || "Player";
        game.players[free] = { name: nm, bot: false };
        room.tokens.set(tok, free);
        game.pool = game.pool.filter((n) => n !== nm);
      }
      for (let s = 0; s < 4; s++) if (!game.players[s]) game.players[s] = { name: "Bot " + s, bot: true };
      game.pool = [];
      if (data.fresh) { game.seriesPicker = null; game.seriesWins = { A: 0, B: 0 }; }
      game.startHand();
      return json(res, 200, { ok: true });
    }

    if (path === "/draw") {
      const r = game.doDraw(seat);
      return json(res, r.ok ? 200 : 400, r);
    }

    if (path === "/trump") {
      if (game.phase !== "trump" || seat !== game.picker) return json(res, 400, { err: "Not your pick." });
      return game.setTrump(String(data.suit)) ? json(res, 200, { ok: true }) : json(res, 400, { err: "You must pick a suit from your first five cards." });
    }

    if (path === "/play") {
      const r = game.playCard(seat, { suit: String(data.suit), rank: Number(data.rank) });
      return json(res, r.ok ? 200 : 400, r);
    }

    if (path === "/sweep") {
      if (!game.sweepPrompt || TEAM_OF[seat] !== game.sweepPrompt.team) return json(res, 400, { err: "No decision pending for you." });
      const r = game.sweepChoice(!!data.playOn);
      return json(res, r.ok ? 200 : 400, r);
    }

    return json(res, 404, { err: "Not found." });
  });
});

server.listen(PORT, () => console.log("Ten 2026 server listening on :" + PORT));

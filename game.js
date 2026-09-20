/* ============================================================
 *  土耳其方块 · Turkey Blocks
 *
 *  棋盘 10 行 × 9 列
 *  · 每个方块 = 一行内「连在一起的若干格」，长度 1~4，长度即类型，
 *    它是不可拆的刚体：只有整条的所有格子下方都空，才能整体下落 1 格。
 *  · 玩家按住任意一条方块左右拖动（拖多远都行，只算 1 次移动）。
 *  · 每次移动后：整盘下落 → 满行消除 → 底部涨出新的一行（未填满）。
 *  · 涨行时若有格子被顶出屏幕最上方 → 游戏结束。
 * ============================================================ */
(function () {
  'use strict';

  /* ============================================================
   * 一、常量与配置
   * ============================================================ */

  var ROWS = 10;   // 行（0 = 最上一行/危险行，9 = 最下一行）
  var COLS = 9;    // 列

  // 类型：1~4 = 普通方块（长度即类型），5 = 金色积分奖励格，6 = 红色困难块
  var T = { N1: 1, N2: 2, N3: 3, N4: 4, SP: 5, ADV: 6 };
  var MAXLEN = 4;

  var DEFAULT_CFG = {
    /* —— 涨行 —— */
    emptyMin: 2,          // 新行至少空几格
    emptyMax: 5,          // 新行至多空几格
    spEvery: 5,           // 每涨 N 行，其中 1 条 1 格方块变成金色奖励格
    advFirst: 8,          // 第几次涨行开始出现红色困难块
    advEvery: 10,         // 之后每 N 行出现 1 条困难块
    rampEvery: 20,        // 每涨 N 行难度 +1 档（0 = 关闭）
    minRows: 2,           // 场上「有格子的行数」少于这个数时，自动从底部补行
    emptyTilt: 0.3,       // 难度对「空格数」的倾斜：每档让新行更偏向 emptyMin（空格更少、行更满）
    advTighten: 2,        // 每升 1 档，困难行间隔缩短几行（有下限 4）
    levelWeights: null,   // 每个档位的 [1格,2格,3格,4格] 权重表；null = 用 DEFAULT_LEVEL_WEIGHTS

    /* —— 连击系数：一次操作消掉 N 行时，积分 ×系数（向上取整） —— */
    combo2: 1.2,
    combo3: 1.4,
    combo4: 1.6,
    combo5: 2.0,

    /* —— 计分 —— */
    skillCost: 1000,
    scorePerCell: 50,
    skillPerCell: 10,
    spScore: 200,
    spSkill: 10,
    advScore: 100,
    advSkill: 10,
    advFullScore: 1000,
    advFullSkill: 100,

    /* —— 规则 —— */
    skill4Mode: 'shrink', // shrink = 4 格砍成 2 格；retag = 原地改标为 2 类型
    preview: true
  };

  var CFG = loadCfg();

  function loadCfg() {
    var saved = null;
    try { saved = JSON.parse(localStorage.getItem('tb_cfg2') || 'null'); } catch (e) {}
    var c = JSON.parse(JSON.stringify(DEFAULT_CFG));
    if (saved && typeof saved === 'object') {
      for (var k in c) {
        if (k === 'levelWeights') {
          if (saved.levelWeights && typeof saved.levelWeights === 'object') c.levelWeights = saved.levelWeights;
        } else if (typeof saved[k] === typeof c[k]) c[k] = saved[k];
      }
    }
    return c;
  }
  function saveCfg() { try { localStorage.setItem('tb_cfg2', JSON.stringify(CFG)); } catch (e) {} }

  var SKILL = {
    1: { name: '1 类型 · 铺展', short: '把这一格左右两侧的连续空格全部铺成 1 类型方块' },
    2: { name: '2 类型 · 清除', short: '移除场上所有 2 类型方块（不计分）' },
    3: { name: '3 类型 · 拆分', short: '场上所有 3 类型方块拆成 3 个独立的 1 类型方块' },
    4: { name: '4 类型 · 折半', short: '场上所有 4 类型方块砍掉一半，剩下 2 格变成 2 类型' }
  };

  /* ============================================================
   * 二、状态
   * ============================================================ */

  var G = {
    board: [],          // board[r][c] = null | { id, t, gid }
    nextRow: null,      // 下一行预告 [{ c, len, t }]
    sel: null,          // 技能选中格
    drag: null,
    score: 0, skill: 0,
    cellsCleared: 0, rowsCleared: 0, tideCount: 0, moves: 0, cellsAdded: 0, comboMax: 0,
    busy: false, over: false, running: false, runId: 0,
    cellMap: {}, nextId: 1, gidSeq: 1,
    advGroups: {},      // 困难块 gid -> 剩余格数
    suppressClick: false, toastTimer: null
  };

  var BEST = 0;
  try { BEST = Number(localStorage.getItem('tb_best2') || 0) || 0; } catch (e) {}

  /* ============================================================
   * 三、工具
   * ============================================================ */

  function $(id) { return document.getElementById(id); }
  function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }
  function randInt(a, b) { return a + Math.floor(Math.random() * (b - a + 1)); }
  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }
  function weightedPick(w) {
    var total = 0, k, last = null;
    for (k in w) { total += w[k]; last = k; }
    if (total <= 0) return Number(last);
    var x = Math.random() * total;
    for (k in w) { x -= w[k]; if (x <= 0) return Number(k); }
    return Number(last);
  }

  /* ============================================================
   * 四、盘面与「方块」基础
   *    方块 = 同一行里 gid 相同的一串连续格子
   * ============================================================ */

  function emptyBoard() {
    G.board = [];
    for (var r = 0; r < ROWS; r++) {
      var row = [];
      for (var c = 0; c < COLS; c++) row.push(null);
      G.board.push(row);
    }
  }

  function mkCell(t, gid) { return { id: G.nextId++, t: t, gid: gid }; }

  function newGid() { return G.gidSeq++; }

  // 第 r 行里包含列 col 的那条方块（按 gid 聚）
  function blockAt(r, col) {
    if (!G.board[r] || !G.board[r][col]) return null;
    var gid = G.board[r][col].gid, lo = col, hi = col;
    while (lo - 1 >= 0 && G.board[r][lo - 1] && G.board[r][lo - 1].gid === gid) lo--;
    while (hi + 1 < COLS && G.board[r][hi + 1] && G.board[r][hi + 1].gid === gid) hi++;
    return { r: r, lo: lo, hi: hi, len: hi - lo + 1, t: G.board[r][col].t, gid: gid };
  }

  // 这条方块左右各有几个连续空格
  function blockRange(b) {
    var m = 0, i;
    for (i = b.hi + 1; i < COLS && !G.board[b.r][i]; i++) m++;
    var maxOff = m;
    m = 0;
    for (i = b.lo - 1; i >= 0 && !G.board[b.r][i]; i--) m++;
    return { min: -m, max: maxOff };
  }

  // 把一条方块整体平移 n 格（撞到别的方块就停），返回实际移动格数
  function shiftBlock(b, dir, n) {
    var moved = 0, c;
    for (var k = 0; k < n; k++) {
      if (dir > 0) {
        if (b.hi + 1 >= COLS || G.board[b.r][b.hi + 1]) break;
        for (c = b.hi; c >= b.lo; c--) { G.board[b.r][c + 1] = G.board[b.r][c]; G.board[b.r][c] = null; }
        b.lo++; b.hi++;
      } else {
        if (b.lo - 1 < 0 || G.board[b.r][b.lo - 1]) break;
        for (c = b.lo; c <= b.hi; c++) { G.board[b.r][c - 1] = G.board[b.r][c]; G.board[b.r][c] = null; }
        b.lo--; b.hi--;
      }
      moved++;
    }
    return moved;
  }

  // 场上所有方块（按 gid 聚）
  function collectBlocks() {
    var map = {}, list = [], r, c, cell;
    for (r = 0; r < ROWS; r++) {
      for (c = 0; c < COLS; c++) {
        cell = G.board[r][c];
        if (!cell) continue;
        if (!map[cell.gid]) map[cell.gid] = { gid: cell.gid, t: cell.t, cells: [], maxR: 0 };
        map[cell.gid].cells.push({ r: r, c: c });
        if (r > map[cell.gid].maxR) map[cell.gid].maxR = r;
      }
    }
    for (var g in map) list.push(map[g]);
    list.sort(function (a, b) { return b.maxR - a.maxR; });   // 下面的先落
    return list;
  }

  // 整条刚体下落：所有格子下方都空才能落
  function blocksCanFall(b) {
    for (var i = 0; i < b.cells.length; i++) {
      var p = b.cells[i];
      if (p.r + 1 >= ROWS) return false;
      if (G.board[p.r + 1][p.c]) return false;
    }
    return true;
  }

  // 全场刚体下落（反复直到没有任何一条能落）
  function settle() {
    var moved = false, guard = 0;
    while (guard++ < 80) {
      var list = collectBlocks(), any = false;
      for (var i = 0; i < list.length; i++) {
        var b = list[i];
        if (!blocksCanFall(b)) continue;
        // 记录格子对象 → 整条下移 1 格
        var objs = [], j, p;
        for (j = 0; j < b.cells.length; j++) { p = b.cells[j]; objs.push(G.board[p.r][p.c]); }
        for (j = 0; j < b.cells.length; j++) { p = b.cells[j]; G.board[p.r][p.c] = null; }
        for (j = 0; j < b.cells.length; j++) { p = b.cells[j]; G.board[p.r + 1][p.c] = objs[j]; }
        any = true; moved = true;
      }
      if (!any) break;
    }
    return moved;
  }

  function fullRows() {
    var out = [];
    for (var r = 0; r < ROWS; r++) {
      var full = true;
      for (var c = 0; c < COLS; c++) if (!G.board[r][c]) { full = false; break; }
      if (full) out.push(r);
    }
    return out;
  }

  function colHeights() {
    var h = [];
    for (var c = 0; c < COLS; c++) {
      var n = 0;
      for (var r = 0; r < ROWS; r++) if (G.board[r][c]) n++;
      h.push(n);
    }
    return h;
  }
  function maxHeight() {
    var h = colHeights(), m = 0;
    for (var i = 0; i < h.length; i++) if (h[i] > m) m = h[i];
    return m;
  }
  // 场上有格子的行数
  function occupiedRowCount() {
    var n = 0;
    for (var r = 0; r < ROWS; r++) {
      for (var c = 0; c < COLS; c++) if (G.board[r][c]) { n++; break; }
    }
    return n;
  }
  function totalCells() {
    var n = 0;
    for (var r = 0; r < ROWS; r++) for (var c = 0; c < COLS; c++) if (G.board[r][c]) n++;
    return n;
  }
  // 场上还有没有任何一条能左右移动
  function hasMovableBlock() {
    for (var r = 0; r < ROWS; r++) {
      var c = 0;
      while (c < COLS) {
        if (!G.board[r][c]) { c++; continue; }
        var b = blockAt(r, c);
        var rg = blockRange(b);
        if (rg.min !== 0 || rg.max !== 0) return true;
        c = b.hi + 1;
      }
    }
    return false;
  }

  // 消除后如果场上「有格子的行数」不足 minRows，就从底部自动补行（补到够为止）
  function topUpRows() {
    var target = CFG.minRows | 0;
    if (target <= 0) return 0;                  // 0 = 关闭补行
    var added = 0, guard = 0;
    while (occupiedRowCount() < target && guard++ < 6) {
      var row = buildRow(-1, false, false);
      for (var r = 0; r < ROWS - 1; r++) G.board[r] = G.board[r + 1];
      var newRow = [];
      for (var i = 0; i < COLS; i++) newRow.push(null);
      G.board[ROWS - 1] = newRow;
      for (var k = 0; k < row.cells.length; k++) {
        var s = row.cells[k];
        if (s.t === T.ADV && G.advGroups[s.gid] == null) {
          var cnt = 0;
          for (var q = 0; q < row.cells.length; q++) if (row.cells[q].gid === s.gid) cnt++;
          G.advGroups[s.gid] = cnt;
        }
        G.board[ROWS - 1][s.c] = mkCell(s.t, s.gid);
      }
      G.cellsAdded += row.cells.length;
      settle();
      added++;
    }
    return added;
  }

  /* ============================================================
   * 五、涨行：生成「新的一行」
   *    一行 = 若干条方块 + 若干空格；空格数保证在 emptyMin~emptyMax
   * ============================================================ */

  function tideLevel() {
    if (!CFG.rampEvery) return 0;
    return Math.floor(G.tideCount / CFG.rampEvery);
  }
  // 后段难度：长条权重上升、困难行更频繁
  // ★ 每档用哪套权重**完全以这张表为准**（设置面板里可逐档编辑），不再走公式升档
  var DEFAULT_LEVEL_WEIGHTS = [
    [30, 30, 15, 10],   // 档位 0
    [25, 30, 20, 15],   // 档位 1
    [20, 25, 25, 20],   // 档位 2
    [15, 25, 30, 25],   // 档位 3
    [10, 20, 35, 30],   // 档位 4
    [5, 20, 40, 35]     // 档位 5（再往上的档位沿用这一行）
  ];
  function defaultLevelWeights() {
    return DEFAULT_LEVEL_WEIGHTS.map(function (r) { return r.slice(); });
  }
  function currentLevelWeights() {
    var t = CFG.levelWeights;
    if (!t || !t.length) return defaultLevelWeights();
    var out = [];
    for (var i = 0; i < t.length; i++) {
      var row = t[i] || [];
      out.push([
        Math.max(0, Number(row[0]) || 0), Math.max(0, Number(row[1]) || 0),
        Math.max(0, Number(row[2]) || 0), Math.max(0, Number(row[3]) || 0)
      ]);
    }
    return out;
  }
  function lenWeights() {
    var tbl = currentLevelWeights();
    var lv = Math.min(tideLevel(), tbl.length - 1);     // 超出表格就沿用最后一行
    var row = tbl[lv];
    return { 1: row[0], 2: row[1], 3: row[2], 4: row[3] };
  }
  function tideParams() {
    var lv = tideLevel();
    return {
      advEvery: Math.max(4, CFG.advEvery - lv * Math.max(0, CFG.advTighten || 0))   // 越到后面困难行越密
    };
  }

  // 新行的空格数：范围固定在 emptyMin~emptyMax；
  // 难度越高 → 越偏向「空格更少」那一端（行越满）
  function pickEmpty() {
    var lo = clamp(CFG.emptyMin | 0, 1, 8);
    var hi = clamp(CFG.emptyMax | 0, lo, 8);
    if (hi === lo) return lo;
    var lv = tideLevel(), w = {}, k;
    for (k = lo; k <= hi; k++) w[k] = 1 + lv * (hi - k) * CFG.emptyTilt;   // k 越小权重越高
    return weightedPick(w);
  }

  // 拼出一串长度、总和正好等于 fill 的方块（长度 1~4）
  // 只限制「长度 ≤ 剩余空间」，不做其它限制（相邻两条可以同长度）
  function makeLens(fill, w, forceFirst) {
    var lens = [], sum = 0, k;
    if (forceFirst) { lens.push(forceFirst); sum = forceFirst; }
    var guard = 0;
    while (sum < fill && guard++ < 60) {
      var room = fill - sum, ww = {};
      for (k in w) if (Number(k) <= room) ww[k] = w[k];
      if (!Object.keys(ww).length) break;
      var L = weightedPick(ww);
      if (!L) break;
      lens.push(L); sum += L;
    }
    return lens;
  }

  // 一行 = 若干条方块 + 若干空格
  // 刷新规则：空格数 ∈ [emptyMin, emptyMax]（难度越高越偏向多空格）；
  //          方块长度按难度权重抽（越后期长条越多）；相邻方块之间至少留 1 格
  function buildRow(rowIndex, isAdv, isSp) {
    var empty = pickEmpty();
    if (isAdv && empty > COLS - MAXLEN) empty = COLS - MAXLEN;   // 困难行必须塞得下 4 格块
    var fill = COLS - empty;
    if (fill < 1) fill = 1;

    var w = lenWeights();
    var force = isAdv ? 4 : (isSp ? 1 : 0);         // 困难行先放 4 格块，奖励行先放 1 格块
    if (force > fill) force = fill;
    var lens = makeLens(fill, w, force);
    var sum = 0, i, k;
    for (i = 0; i < lens.length; i++) sum += lens[i];
    if (sum > fill) { while (lens.length > 1 && sum > fill) sum -= lens.pop(); }
    if (sum < fill) lens.push(fill - sum);          // 兜底

    var gapCount = COLS - fill;
    var nb = lens.length;
    // 相邻方块之间至少 1 格：块数太多就合并（合并后长度仍然 ≤ 4，类型即长度）
    // 注意：第一条如果是金色/困难块，不能参与合并（会破坏它的长度）
    var mergeFrom = (isAdv || isSp) ? 1 : 0;
    var guard = 0;
    while (nb - 1 > gapCount && guard++ < 30) {
      var merged = false;
      for (i = mergeFrom; i < lens.length - 1; i++) {
        if (lens[i] + lens[i + 1] <= MAXLEN) {
          lens.splice(i, 2, lens[i] + lens[i + 1]);
          merged = true; break;
        }
      }
      if (!merged) break;
      nb = lens.length;
    }

    // 空格聚成 1~2 段放在方块之间（成段的空洞才可能被上面的方块整条落进来填掉）
    var slots = [];
    for (i = 0; i <= nb; i++) slots.push(i);
    for (i = slots.length - 1; i > 0; i--) {
      var ri = Math.floor(Math.random() * (i + 1));
      var tmp = slots[i]; slots[i] = slots[ri]; slots[ri] = tmp;
    }
    var runs = (gapCount >= 4 && Math.random() < 0.35) ? 2 : 1;
    if (runs > slots.length) runs = slots.length;
    var gaps = [];
    for (i = 0; i <= nb; i++) gaps.push(0);
    var remainG = gapCount;
    for (var rI = 0; rI < runs; rI++) {
      var take = (rI === runs - 1) ? remainG : randInt(1, Math.max(1, remainG - (runs - 1 - rI)));
      gaps[slots[rI]] = take; remainG -= take;
    }

    var cells = [], col = gaps[0];
    for (i = 0; i < nb; i++) {
      var len = lens[i];
      var t = (isAdv && i === 0) ? T.ADV : ((isSp && i === 0) ? T.SP : len);
      var gid = newGid();
      for (k = 0; k < len; k++) cells.push({ c: col + k, t: t, gid: gid });
      col += len + gaps[i + 1];
    }
    return { cells: cells, isAdv: isAdv, isSp: isSp };
  }

  function planNextRow() {
    var idx = G.tideCount + 1;
    var tp = tideParams();
    var isAdv = (idx >= CFG.advFirst && (idx - CFG.advFirst) % tp.advEvery === 0);
    var isSp = !isAdv && (idx % CFG.spEvery === 0);
    var row = buildRow(idx, isAdv, isSp);
    G.nextRow = { index: idx, cells: row.cells, isAdv: isAdv, isSp: isSp };
  }

  /* ============================================================
   * 六、初始地形（最下方 2 行）
   *    两行都满足空格 2~6；且第 8 行每一条方块都至少压住底行一格
   *    （只要压住一格，刚体规则下它就落不下去，不会出现悬空）
   * ============================================================ */

  // 一条长度序列（总格数 = 9 − 空格数，空格数在 emptyMin~emptyMax 内）
  function rowLens() {
    var fill = COLS - pickEmpty();
    var lens = makeLens(fill, lenWeights(), 0);
    var sum = 0, i;
    for (i = 0; i < lens.length; i++) sum += lens[i];
    while (sum > fill && lens.length > 1) sum -= lens.pop();
    if (sum < fill) lens.push(fill - sum);
    return lens;
  }

  // 回溯搜索：给每条方块找一个位置，要求「不重叠」且「至少压住一个支撑列」
  function placeOverSupport(lens, support) {
    var n = lens.length, used = [], res = [], i;
    for (i = 0; i < COLS; i++) used.push(false);
    function rec(idx) {
      if (idx === n) return true;
      var len = lens[idx], starts = [], s;
      for (s = 0; s + len <= COLS; s++) starts.push(s);
      for (s = starts.length - 1; s > 0; s--) {          // 随机顺序
        var k = Math.floor(Math.random() * (s + 1));
        var t = starts[s]; starts[s] = starts[k]; starts[k] = t;
      }
      for (var q = 0; q < starts.length; q++) {
        var st = starts[q], ok = true, sup = false;
        for (var c = st; c < st + len; c++) {
          if (used[c]) { ok = false; break; }
          if (support[c]) sup = true;
        }
        if (!ok || !sup) continue;
        for (var c2 = st; c2 < st + len; c2++) used[c2] = true;
        res[idx] = { lo: st, len: len };
        if (rec(idx + 1)) return true;
        for (var c3 = st; c3 < st + len; c3++) used[c3] = false;
      }
      return false;
    }
    return rec(0) ? res : null;
  }

  // 极罕见兜底：直接铺在底行有格子的那些列上（这样每格都有支撑）
  function fallbackUpper(supportList) {
    var cols = supportList.slice(), k;
    for (k = cols.length - 1; k > 0; k--) {
      var q = Math.floor(Math.random() * (k + 1));
      var t = cols[k]; cols[k] = cols[q]; cols[q] = t;
    }
    var n8 = randInt(Math.min(3, cols.length), Math.min(7, cols.length));
    cols = cols.slice(0, n8);
    cols.sort(function (a, b) { return a - b; });
    var i = 0;
    while (i < cols.length) {
      var lo = i;
      while (i + 1 < cols.length && cols[i + 1] === cols[i] + 1) i++;
      var runLen = i - lo + 1, off = 0;
      while (off < runLen) {
        var len = Math.min(MAXLEN, runLen - off);
        var gid = newGid();
        for (k = 0; k < len; k++) G.board[ROWS - 2][cols[lo + off + k]] = mkCell(len, gid);
        off += len;
      }
      i++;
    }
  }

  function initTerrain() {
    // 底行：按正常刷新规则生成
    var bottom = buildRow(-1, false, false);
    var support = {}, supportList = [], k, s;
    for (k = 0; k < bottom.cells.length; k++) {
      s = bottom.cells[k];
      G.board[ROWS - 1][s.c] = mkCell(s.t, s.gid);
      if (!support[s.c]) { support[s.c] = 1; supportList.push(s.c); }
    }

    // 第 8 行：重试直到「每条方块都压住底行至少一格」
    var placed = null, lens = null;
    for (var attempt = 0; attempt < 200 && !placed; attempt++) {
      lens = rowLens();
      if (lens.length > supportList.length) continue;
      placed = placeOverSupport(lens, support);
    }
    if (!placed) { fallbackUpper(supportList); return; }

    for (k = 0; k < placed.length; k++) {
      var gid = newGid();
      for (var c = placed[k].lo; c < placed[k].lo + placed[k].len; c++) {
        G.board[ROWS - 2][c] = mkCell(placed[k].len, gid);
      }
    }
  }

  /* ============================================================
   * 七、渲染
   * ============================================================ */

  var dom = {};

  function bootDom() {
    dom.board = $('board');
    dom.boardWrap = $('boardWrap');
    dom.score = $('score'); dom.best = $('best');
    dom.skill = $('skill'); dom.skillBar = $('skillBar');
    dom.cells = $('cells'); dom.rows = $('rows');
    dom.tide = $('tide'); dom.moves = $('moves'); dom.level = $('level');
    dom.nextStrip = $('nextStrip');
    dom.rhythm = $('rhythm');
    dom.skillInfo = $('skillInfo'); dom.btnSkill = $('btnSkill'); dom.costLabel = $('costLabel');
    dom.overlay = $('overlay'); dom.toast = $('toast');
    dom.heightBar = $('heightBar'); dom.passBtn = $('passBtn'); dom.dragTip = $('dragTip');
    dom.stage = document.querySelector('.stage');
  }

  function posStyle(r, c) {
    return 'translate(calc(var(--cell) * ' + c + '), calc(var(--cell) * ' + r + '))';
  }
  function cellInnerText(cell) {
    if (cell.t === T.SP) return '★';
    if (cell.t === T.ADV) return '<i>' + (G.advGroups[cell.gid] || 0) + '</i>';
    return '';
  }
  function sameGid(r, c, gid) {
    return r >= 0 && r < ROWS && c >= 0 && c < COLS && G.board[r][c] && G.board[r][c].gid === gid;
  }

  function cellClass(cell, r, c) {
    var d = G.drag;
    var inBlock = d && d.r === r && c >= d.lo && c <= d.hi;
    // 白框只画在「整条方块的外轮廓」上：哪一边的邻居不是同一条方块，哪一边就描边
    var edge =
      (sameGid(r, c - 1, cell.gid) ? '' : ' e-l') +
      (sameGid(r, c + 1, cell.gid) ? '' : ' e-r') +
      (sameGid(r - 1, c, cell.gid) ? '' : ' e-t') +
      (sameGid(r + 1, c, cell.gid) ? '' : ' e-b');
    return 'cell t' + cell.t +
      (cell.t === T.ADV ? ' adv' : '') +
      edge +
      (inBlock ? ' runsel' : '') +
      (G.sel && G.sel.r === r && G.sel.c === c ? ' sel' : '');
  }

  function syncBoard() {
    var present = {}, r, c, cell, d, cls, inner;
    for (r = 0; r < ROWS; r++) {
      for (c = 0; c < COLS; c++) {
        cell = G.board[r][c];
        if (!cell) continue;
        present[cell.id] = 1;
        cls = cellClass(cell, r, c);
        inner = cellInnerText(cell);
        d = G.cellMap[cell.id];
        if (!d) {
          d = document.createElement('div');
          d.className = cls;
          d.style.transform = posStyle(r, c);
          d.innerHTML = inner;
          d.__cid = cell.id;
          dom.board.appendChild(d);
          G.cellMap[cell.id] = d;
        } else {
          if (d.className !== cls) d.className = cls;
          d.style.transform = posStyle(r, c);
          if (d.innerHTML !== inner) d.innerHTML = inner;
        }
      }
    }
    for (var id in G.cellMap) {
      if (!present[id]) {
        d = G.cellMap[id];
        if (d && d.parentNode) d.parentNode.removeChild(d);
        delete G.cellMap[id];
      }
    }
    dom.boardWrap.classList.toggle('danger', (function () {
      for (var i = 0; i < COLS; i++) if (G.board[0][i]) return true;
      return false;
    })());
  }

  // 下一行预告：贴在棋盘底边的加粗色条（哪几列会顶上来）
  function syncNextStrip() {
    if (!dom.nextStrip) return;
    if (!CFG.preview || !G.nextRow) { dom.nextStrip.classList.add('off'); return; }
    dom.nextStrip.classList.remove('off');
    var map = {}, i;
    for (i = 0; i < G.nextRow.cells.length; i++) map[G.nextRow.cells[i].c] = G.nextRow.cells[i];
    var html = '';
    for (var c = 0; c < COLS; c++) {
      var s = map[c];
      if (!s) { html += '<div class="ncell"></div>'; continue; }
      var l = map[c - 1], r = map[c + 1];
      var e = (l && l.gid === s.gid ? '' : ' e-l') + (r && r.gid === s.gid ? '' : ' e-r');
      html += '<div class="ncell on t' + s.t + (s.t === T.ADV ? ' adv' : '') + e + '"></div>';
    }
    if (s_lastStrip !== html) { dom.nextStrip.innerHTML = html; s_lastStrip = html; }
    dom.nextStrip.title = '下一行：第 ' + G.nextRow.index + ' 行 · ' + G.nextRow.cells.length + ' 格 · ' +
      (G.nextRow.isAdv ? '困难行' : (G.nextRow.isSp ? '含金色奖励格 ★' : '普通行'));
  }
  var s_lastStrip = '';

  function renderHud() {
    dom.score.textContent = G.score;
    dom.best.textContent = BEST;
    dom.skill.textContent = G.skill;
    dom.cells.textContent = G.cellsCleared;
    dom.rows.textContent = G.rowsCleared;
    dom.tide.textContent = G.tideCount;
    dom.moves.textContent = G.moves;
    dom.level.textContent = tideLevel() + 1;

    var pct = Math.min(100, G.skill / Math.max(1, CFG.skillCost) * 100);
    dom.skillBar.style.width = pct + '%';
    dom.skillBar.classList.toggle('ready', G.skill >= CFG.skillCost);
    dom.costLabel.textContent = CFG.skillCost;

    var h = maxHeight();
    dom.heightBar.style.width = Math.min(100, h / ROWS * 100) + '%';
    dom.heightBar.classList.toggle('warn', h >= 7);

    var last = G.tideCount, k, dSp = '-', dAdv = '-';
    for (k = last + 1; k <= last + CFG.spEvery; k++) if (k % CFG.spEvery === 0) { dSp = k - last; break; }
    var tp = tideParams();
    for (k = last + 1; k <= last + CFG.advFirst + tp.advEvery; k++) {
      if (k >= CFG.advFirst && (k - CFG.advFirst) % tp.advEvery === 0) { dAdv = k - last; break; }
    }
    dom.rhythm.innerHTML = '金色奖励行 <b>' + dSp + '</b> 行后 · 困难行 <b>' + dAdv + '</b> 行后';
  }

  function renderSkillPanel() {
    var sel = G.sel;
    var cell = sel ? G.board[sel.r][sel.c] : null;
    if (!sel || !cell) {
      dom.skillInfo.innerHTML = '<span class="muted">点击场上的格子进行选择</span>';
      dom.btnSkill.disabled = true;
      return;
    }
    if (cell.t === T.SP) {
      dom.skillInfo.innerHTML = '<b class="c5">金色奖励格 ★</b><br>消除时提供 ' + CFG.spScore +
        ' 积分。该格<strong>无法使用技能</strong>。';
      dom.btnSkill.disabled = true; return;
    }
    if (cell.t === T.ADV) {
      dom.skillInfo.innerHTML = '<b class="c6">红色困难块</b><br>剩余 <b>' + (G.advGroups[cell.gid] || 0) +
        '</b> 格，每次被消除只减少 1 格。该格<strong>无法使用技能</strong>。';
      dom.btnSkill.disabled = true; return;
    }
    var s = SKILL[cell.t];
    dom.skillInfo.innerHTML = '<b class="c' + cell.t + '">' + s.name + '</b><br>' + s.short +
      '<br><span class="muted">消耗 ' + CFG.skillCost + ' 技能点</span>';
    dom.btnSkill.disabled = G.skill < CFG.skillCost || G.busy || G.over;
  }

  function render() {
    syncBoard();
    syncNextStrip();
    renderHud();
    renderSkillPanel();
  }

  function toast(msg) {
    if (!dom.toast) return;
    dom.toast.textContent = msg;
    dom.toast.classList.add('show');
    clearTimeout(G.toastTimer);
    G.toastTimer = setTimeout(function () { dom.toast.classList.remove('show'); }, 1700);
  }

  /* ============================================================
   * 八、主流程
   * ============================================================ */

  function newGame() {
    G.runId++;
    emptyBoard();
    G.sel = null; G.drag = null;
    G.score = 0; G.skill = 0; G.cellsCleared = 0; G.rowsCleared = 0;
    G.tideCount = 0; G.moves = 0; G.cellsAdded = 0; G.comboMax = 0;
    G.busy = false; G.over = false; G.running = true;
    G.nextId = 1; G.gidSeq = 1; G.advGroups = {};
    for (var id in G.cellMap) {
      var d = G.cellMap[id];
      if (d && d.parentNode) d.parentNode.removeChild(d);
      delete G.cellMap[id];
    }
    initTerrain();
    planNextRow();
    hideOverlay();
    render();
    updateStuck();
  }

  function updateStuck() {
    var stuck = !hasMovableBlock();
    if (dom.boardWrap) dom.boardWrap.classList.toggle('stuck', stuck);
    if (dom.passBtn) dom.passBtn.classList.toggle('attention', stuck);
    return stuck;
  }

  // 下落 → 消除（含连锁）。comboMode = 这次消除算不算「一次操作内的连击」
  function resolveAll(myRun, comboMode) {
    var moved = settle();
    if (moved) render();
    return sleep(moved ? 200 : 40).then(function () {
      if (myRun !== G.runId || G.over) return;
      return resolveBoard(comboMode);
    });
  }

  // 一次移动：把某条方块平移 offset 格（只算 1 次移动，只涨 1 行）
  function moveBlock(r, col, offset) {
    if (G.busy || G.over || !G.running) return false;
    if (!offset) return false;
    var b = blockAt(r, col);
    if (!b) return false;
    var dir = offset > 0 ? 1 : -1;
    var moved = shiftBlock(b, dir, Math.abs(offset));
    if (!moved) { render(); return false; }

    G.busy = true;
    G.moves++;
    var myRun = G.runId;
    render();
    toast((dir > 0 ? '右移 ' : '左移 ') + moved + ' 格');

    sleep(180).then(function () {
      if (myRun !== G.runId || G.over) return;
      return resolveAll(myRun, true);
    }).then(function () {
      if (myRun !== G.runId || G.over) return;
      return insertTideRow(220);
    }).then(function () {
      if (myRun !== G.runId || G.over) return;
      G.busy = false;
      render();
      updateStuck();
    });
    return true;
  }

  // 跳过本次移动
  function passTurn() {
    if (G.busy || G.over || !G.running) return;
    G.busy = true;
    G.moves++;
    var myRun = G.runId;
    toast('本次不移动，直接涨一行');
    resolveAll(myRun, true).then(function () {
      if (myRun !== G.runId || G.over) return;
      return insertTideRow(220);
    }).then(function () {
      if (myRun !== G.runId || G.over) return;
      G.busy = false;
      render();
      updateStuck();
    });
  }

  // 从底部插入新的一行：整体上移 1 格，新行放在最底行，然后立刻下落压实
  function insertTideRow(dur) {
    var myRun = G.runId;
    var topUsed = false;
    for (var c = 0; c < COLS; c++) if (G.board[0][c]) { topUsed = true; break; }
    if (topUsed) {
      return sleep(140).then(function () {
        if (myRun !== G.runId) return;
        gameOver('新的一行把最上面的格子顶出了屏幕');
      });
    }

    var next = G.nextRow;
    G.tideCount = next.index;

    for (var r = 0; r < ROWS - 1; r++) G.board[r] = G.board[r + 1];
    var newRow = [];
    for (var i = 0; i < COLS; i++) newRow.push(null);
    G.board[ROWS - 1] = newRow;

    for (var k = 0; k < next.cells.length; k++) {
      var s = next.cells[k];
      if (s.t === T.ADV && G.advGroups[s.gid] == null) {
        var cnt = 0;                                    // 血量 = 这一组实际有几格
        for (var q = 0; q < next.cells.length; q++) if (next.cells[q].gid === s.gid) cnt++;
        G.advGroups[s.gid] = cnt;
      }
      G.board[ROWS - 1][s.c] = mkCell(s.t, s.gid);
    }
    G.cellsAdded += next.cells.length;

    if (G.sel) {
      G.sel = { r: clamp(G.sel.r - 1, 0, ROWS - 1), c: G.sel.c };
      if (!G.board[G.sel.r][G.sel.c]) G.sel = null;
    }

    // 上推之后立刻让整盘下落压实（悬空的方块该落就落）
    settle();
    planNextRow();
    render();
    // 压实过程中可能又凑满某一行 → 立刻消除（这属于涨行带来的，不计入连击系数）
    return sleep(dur || 220).then(function () {
      if (myRun !== G.runId || G.over) return;
      return resolveBoard(false);
    });
  }

  /* ============================================================
   * 九、消除结算（含困难块与连锁）
   * ============================================================ */

  function gain(score, skill, cells) {
    G.score += score; G.skill += skill; G.cellsCleared += cells;
    if (G.score > BEST) { BEST = G.score; try { localStorage.setItem('tb_best2', String(BEST)); } catch (e) {} }
  }

  // 一次操作里消掉 N 行对应的积分系数
  function comboMul(rows) {
    if (rows >= 5) return CFG.combo5;
    if (rows === 4) return CFG.combo4;
    if (rows === 3) return CFG.combo3;
    if (rows === 2) return CFG.combo2;
    return 1;
  }

  function resolveBoard(comboMode) {
    var myRun = G.runId, chain = 0;
    var totalRows = 0, totalScore = 0;

    function step() {
      if (myRun !== G.runId) return Promise.resolve();
      var full = fullRows();
      if (!full.length) return Promise.resolve();
      chain++;
      

      var toRemove = {}, gainedScore = 0, gainedSkill = 0, gainedCells = 0;

      full.forEach(function (r) {
        // 困难块：本行每组只消耗 1 格血（取最右）
        var gids = {}, c, cell;
        for (c = 0; c < COLS; c++) {
          cell = G.board[r][c];
          if (cell && cell.t === T.ADV) gids[cell.gid] = 1;
        }
        for (var gid in gids) {
          if (!(gid in G.advGroups)) continue;
          var target = null;
          for (c = COLS - 1; c >= 0; c--) {
            cell = G.board[r][c];
            if (cell && cell.t === T.ADV && String(cell.gid) === String(gid)) { target = cell; break; }
          }
          if (!target) continue;
          G.advGroups[gid] = (G.advGroups[gid] || 1) - 1;
          toRemove[target.id] = 1;
          gainedScore += CFG.advScore; gainedSkill += CFG.advSkill; gainedCells += 1;

          if (G.advGroups[gid] <= 0) {
            for (var rr = 0; rr < ROWS; rr++) {
              for (var cx = 0; cx < COLS; cx++) {
                var c2 = G.board[rr][cx];
                if (c2 && c2.t === T.ADV && c2.gid === target.gid && !toRemove[c2.id]) {
                  toRemove[c2.id] = 1;
                  gainedScore += CFG.advScore; gainedSkill += CFG.advSkill; gainedCells += 1;
                }
              }
            }
            gainedScore += CFG.advFullScore; gainedSkill += CFG.advFullSkill;
            delete G.advGroups[gid];
          }
        }
        // 其余格子
        for (var c3 = 0; c3 < COLS; c3++) {
          var c4 = G.board[r][c3];
          if (!c4 || c4.t === T.ADV || toRemove[c4.id]) continue;
          toRemove[c4.id] = 1;
          if (c4.t === T.SP) { gainedScore += CFG.spScore; gainedSkill += CFG.spSkill; }
          else { gainedScore += CFG.scorePerCell; gainedSkill += CFG.skillPerCell; }
          gainedCells += 1;
        }
      });

      gain(gainedScore, gainedSkill, gainedCells);
      G.rowsCleared += full.length;
      totalRows += full.length;
      totalScore += gainedScore;

      for (var id in toRemove) { var d = G.cellMap[id]; if (d) d.classList.add('pop'); }
      render();

      return sleep(230).then(function () {
        if (myRun !== G.runId) return;
        for (var id2 in toRemove) {
          var d2 = G.cellMap[id2];
          if (d2 && d2.parentNode) d2.parentNode.removeChild(d2);
          delete G.cellMap[id2];
        }
        for (var r2 = 0; r2 < ROWS; r2++) {
          for (var c5 = 0; c5 < COLS; c5++) {
            var cc2 = G.board[r2][c5];
            if (cc2 && toRemove[cc2.id]) G.board[r2][c5] = null;
          }
        }
        settle();
        if (G.sel && !G.board[G.sel.r][G.sel.c]) G.sel = null;
        render();
        return sleep(200).then(step);
      });
    }
    return step().then(function () {
      if (myRun !== G.runId || G.over) return;
      // 连击系数：一次操作消掉多行时，整体积分 ×系数（向上取整）
      if (comboMode && totalRows >= 2 && totalScore > 0) {
        var mul = comboMul(totalRows);
        var finalScore = Math.ceil(totalScore * mul);
        var bonus = finalScore - totalScore;
        if (bonus > 0) {
          gain(bonus, 0, 0);
          if (totalRows > G.comboMax) G.comboMax = totalRows;
          toast('连击！一次消除 ' + totalRows + ' 行 → 积分 ×' + mul + '（+' + bonus + '）');
        }
      }
      // 消除后场上不足 minRows 行 → 自动补行
      if (topUpRows()) {
        render();
        return sleep(230);
      }
    });
  }

  /* ============================================================
   * 十、技能
   * ============================================================ */

  function skill1(r, c) {
    var add = 0, cc;
    for (cc = c - 1; cc >= 0; cc--) {
      if (G.board[r][cc]) break;
      G.board[r][cc] = mkCell(T.N1, newGid()); add++;
    }
    for (cc = c + 1; cc < COLS; cc++) {
      if (G.board[r][cc]) break;
      G.board[r][cc] = mkCell(T.N1, newGid()); add++;
    }
    return add;
  }
  function skill2() {
    var removed = {}, n = 0;
    for (var r = 0; r < ROWS; r++) for (var c = 0; c < COLS; c++) {
      var cell = G.board[r][c];
      if (cell && cell.t === T.N2) { removed[cell.id] = 1; G.board[r][c] = null; n++; }
    }
    return { removed: removed, count: n };
  }
  // 3 类型 → 拆成 3 个独立 1 类型
  function skill3() {
    var n = 0, cells = [];
    for (var r = 0; r < ROWS; r++) for (var c = 0; c < COLS; c++) {
      var cell = G.board[r][c];
      if (cell && cell.t === T.N3) cells.push(cell);
    }
    for (var i = 0; i < cells.length; i++) {
      cells[i].t = T.N1;
      cells[i].gid = newGid();
      n++;
    }
    return n;
  }
  function skill4() {
    var removed = {}, n = 0;
    if (CFG.skill4Mode === 'retag') {
      var cnt = 0;
      for (var r = 0; r < ROWS; r++) for (var c = 0; c < COLS; c++) {
        var cell = G.board[r][c];
        if (cell && cell.t === T.N4) { cell.t = T.N2; cnt++; }
      }
      return { removed: removed, count: 0, retagged: cnt };
    }
    for (var r2 = 0; r2 < ROWS; r2++) {
      var c2 = 0;
      while (c2 < COLS) {
        var cur = G.board[r2][c2];
        if (cur && cur.t === T.N4) {
          var gid = cur.gid, e = c2;
          while (e + 1 < COLS && G.board[r2][e + 1] && G.board[r2][e + 1].gid === gid) e++;
          var len = e - c2 + 1;
          var keep = Math.max(1, Math.floor(len / 2));
          for (var i = 0; i < keep; i++) G.board[r2][c2 + i].t = T.N2;
          for (var j = keep; j < len; j++) {
            removed[G.board[r2][c2 + j].id] = 1;
            G.board[r2][c2 + j] = null;
            n++;
          }
          c2 = e + 1;
        } else c2++;
      }
    }
    return { removed: removed, count: n };
  }

  function useSkill() {
    if (G.over || G.busy || !G.sel) return;
    var sel = G.sel;
    var cell = G.board[sel.r][sel.c];
    if (!cell || cell.t > 4) return;
    if (G.skill < CFG.skillCost) { toast('技能点不足（需要 ' + CFG.skillCost + '）'); return; }

    G.skill -= CFG.skillCost;
    G.busy = true;
    var myRun = G.runId;
    var type = cell.t, removed = {}, msg = '';

    if (type === 1) msg = '1 类型技能：铺展了 ' + skill1(sel.r, sel.c) + ' 个格子';
    else if (type === 2) { var r2 = skill2(); removed = r2.removed; msg = '2 类型技能：清除 ' + r2.count + ' 个 2 类型格子（不计分）'; }
    else if (type === 3) msg = '3 类型技能：' + skill3() + ' 个格子拆成独立 1 类型';
    else {
      var r4 = skill4(); removed = r4.removed;
      msg = CFG.skill4Mode === 'retag'
        ? '4 类型技能：' + r4.retagged + ' 个格子改标为 2 类型'
        : '4 类型技能：砍掉 ' + r4.count + ' 格，其余变成 2 类型';
    }

    G.sel = null;
    for (var id in removed) { var d = G.cellMap[id]; if (d) d.classList.add('pop'); }
    render();
    toast(msg);

    sleep(240).then(function () {
      if (myRun !== G.runId) return;
      for (var id2 in removed) {
        var d2 = G.cellMap[id2];
        if (d2 && d2.parentNode) d2.parentNode.removeChild(d2);
        delete G.cellMap[id2];
      }
      render();
      return resolveAll(myRun, true);
    }).then(function () {
      if (myRun !== G.runId || G.over) return;
      G.busy = false;
      render();
      updateStuck();
    });
  }

  /* ============================================================
   * 十一、结束 / 覆盖层
   * ============================================================ */

  function gameOver(reason) {
    if (G.over) return;
    G.over = true; G.running = false; G.busy = true;
    render();
    showOverlay(
      '<h2>游戏结束</h2>' +
      '<p class="muted">' + (reason || '') + '</p>' +
      '<div class="result">' +
      '<div><span>本局积分</span><b>' + G.score + '</b></div>' +
      '<div><span>最高分</span><b>' + BEST + '</b></div>' +
      '<div><span>消除格数</span><b>' + G.cellsCleared + '</b></div>' +
      '<div><span>消除行数</span><b>' + G.rowsCleared + '</b></div>' +
      '<div><span>移动次数</span><b>' + G.moves + '</b></div>' +
      '<div><span>最高连击</span><b>' + G.comboMax + ' 行</b></div>' +
      '<div><span>剩余技能点</span><b>' + G.skill + '</b></div>' +
      '</div>' +
      '<button class="primary big" data-act="restart">再来一局</button>'
    );
  }

  function showOverlay(html) {
    dom.overlay.innerHTML = '<div class="modal">' + html + '</div>';
    dom.overlay.classList.add('show');
  }
  function hideOverlay() { dom.overlay.classList.remove('show'); }

  function helpHtml() {
    return '<h2>土耳其方块 · 玩法</h2>' +
      '<div class="helpgrid">' +
      '<section><h4>基本玩法</h4><ul>' +
      '<li>棋盘 <b>10 行 × 9 列</b>，开局最下方 2 行已经有若干方块。</li>' +
      '<li>场上的每个方块都是<b>一行里连在一起的一整条</b>（长度 1~4），它是<b>不可拆的刚体</b>。</li>' +
      '<li><b>按住一条方块左右拖动</b>即可移动它，拖多远都行，但每次移动只算 1 次。</li>' +
      '<li>整条方块<b>所有格子下方都是空的</b>时，才会整体下落 1 格；只要有一格被挡，整条就停住。</li>' +
      '<li>填满 9 格的行立即消除；随后底部会<b>涨出新的一行</b>，整盘上移 1 格。</li>' +
      '<li>消除后如果场上<b>有格子的行数不足 ' + CFG.minRows + ' 行</b>，会自动从底部补行补到 ' + CFG.minRows + ' 行。</li>' +
      '<li>涨行时若有格子被顶出屏幕最上方 → <b>游戏结束</b>。</li>' +
      '</ul></section>' +
      '<section><h4>颜色与收益</h4><ul>' +
      '<li><span class="c1">绿色 = 1 类型</span> / <span class="c2">蓝色 = 2 类型</span> / <span class="c3">紫色 = 3 类型</span> / <span class="c4">橙色 = 4 类型</span>（类型 = 长度）</li>' +
      '<li><span class="c5">金色 ★</span> = 积分奖励格，消除时 <b>+200 积分</b>（每 ' + CFG.spEvery + ' 行 1 个）。</li>' +
      '<li><span class="c6">红色</span> = 困难块（4 格血），每次被消除只掉 1 格，4 格耗完额外 <b>+1000 积分</b>。</li>' +
      '<li>每消除 1 格：<b>+50 积分</b>、<b>+10 技能点</b>；攒满 <b>' + CFG.skillCost + ' 技能点</b>可发动技能。</li>' +
      '<li><b>连击系数</b>：一次操作里消掉 2 行 ×<b>' + CFG.combo2 + '</b>、3 行 ×<b>' + CFG.combo3 +
      '</b>、4 行 ×<b>' + CFG.combo4 + '</b>、5 行及以上 ×<b>' + CFG.combo5 + '</b>（对整次消除积分向上取整）。</li>' +
      '</ul></section>' +
      '<section><h4>技能</h4><ul>' +
      '<li><b>1 类型</b>：把该格左右两侧的连续空格全部铺成 1 类型。</li>' +
      '<li><b>2 类型</b>：移除场上所有 2 类型方块（不计分）。</li>' +
      '<li><b>3 类型</b>：场上所有 3 类型方块拆成 3 个独立的 1 类型方块。</li>' +
      '<li><b>4 类型</b>：场上所有 4 类型方块砍掉一半，剩下 2 格变成 2 类型。</li>' +
      '<li>金色奖励格与红色困难块<b>不能被技能选中，也不受技能影响</b>。</li>' +
      '</ul></section>' +
      '<section><h4>操作</h4><ul>' +
      '<li>按住一条方块左右拖动，松手生效；能拖多远拖多远，撞到别的方块就停在障碍前。</li>' +
      '<li>如果场上没有任何一条能移动，按「跳过本回合」直接涨一行继续。</li>' +
      '<li>难度会随涨行数提升：<b>长条更多、新行空洞更多、困难行更密</b>。</li>' +
      '</ul></section>' +
      '</div>' +
      '<button class="primary big" data-act="close">' + (G.running ? '返回游戏' : '开始游戏') + '</button>';
  }

  /* ---- 设置面板：每档位刷新权重表 ---- */

  var editWeights = null;          // 打开设置面板时用的权重表副本

  function weightRowsHtml() {
    var tbl = editWeights || currentLevelWeights();
    var h = '<div class="wrow whead"><span>档位</span><span>1 格</span><span>2 格</span><span>3 格</span><span>4 格</span><span></span></div>';
    for (var i = 0; i < tbl.length; i++) {
      h += '<div class="wrow"><span class="wlv">' + i + '</span>';
      for (var k = 0; k < 4; k++) {
        h += '<input type="number" min="0" step="1" data-wlv="' + i + '" data-wk="' + k +
          '" value="' + tbl[i][k] + '">';
      }
      h += '<button class="wdel" data-act="delwrow" data-lv="' + i + '"' +
        (tbl.length <= 1 ? ' disabled' : '') + ' title="删除这一档">×</button></div>';
    }
    return h;
  }
  function readWeightInputs() {
    if (!editWeights) return;
    var inputs = document.querySelectorAll ? document.querySelectorAll('[data-wlv]') : [];
    for (var i = 0; i < inputs.length; i++) {
      var el = inputs[i];
      var lv = Number(el.getAttribute('data-wlv')), wk = Number(el.getAttribute('data-wk'));
      if (editWeights[lv]) editWeights[lv][wk] = Math.max(0, Number(el.value) || 0);
    }
  }
  function refreshWeightTable() {
    var box = $('weightTable');
    if (box) box.innerHTML = weightRowsHtml();
  }

  function settingsHtml() {
    function num(id, label, val, step, min) {
      return '<label class="field"><span>' + label + '</span>' +
        '<input type="number" id="' + id + '" value="' + val + '" step="' + step + '" min="' + min + '"></label>';
    }
    return '<h2>数值设置</h2><p class="muted">点击「保存并重开」后立即生效。所有数值都存在浏览器本地。</p>' +
      '<h3 class="grp">格子刷新规则</h3>' +
      '<div class="fields">' +
      num('cfgEmptyMin', '新行最少空格数', CFG.emptyMin, 1, 1) +
      num('cfgEmptyMax', '新行最多空格数', CFG.emptyMax, 1, 1) +
      num('cfgEmptyTilt', '难度对空格的倾斜（越大后期行越满、空格越少）', CFG.emptyTilt, 0.05, 0) +
      num('cfgRamp', '难度提升间隔（涨行数，0=关闭）', CFG.rampEvery, 5, 0) +
      num('cfgMinRows', '最少保留行数（有格子的行）', CFG.minRows, 1, 0) +
      '</div>' +
      '<h3 class="grp">每个档位的格子权重</h3>' +
      '<p class="muted small" style="text-align:left;margin:0 0 4px">' +
      '每一行是一个难度档位的权重（1/2/3/4 格方块各占多少）。当前档位 <b>' + tideLevel() +
      '</b>（= 已涨行数 ÷ 难度提升间隔）；超出表格的档位自动沿用最后一行。</p>' +
      '<div class="wtable" id="weightTable">' + weightRowsHtml() + '</div>' +
      '<div class="btnrow" style="margin-top:10px">' +
      '<button data-act="addwrow">+ 增加一档</button>' +
      '<button data-act="resetw">恢复默认权重</button>' +
      '</div>' +
      '<h3 class="grp">特殊行出现频率</h3>' +
      '<div class="fields">' +
      num('cfgSpEvery', '金色奖励行：每 N 行 1 个', CFG.spEvery, 1, 1) +
      num('cfgAdvFirst', '困难行：第 N 行开始出现', CFG.advFirst, 1, 1) +
      num('cfgAdvEvery', '困难行：每 N 行 1 个', CFG.advEvery, 1, 1) +
      num('cfgAdvTighten', '每升 1 档困难行间隔缩短几行', CFG.advTighten, 1, 0) +
      '</div>' +
      '<h3 class="grp">连击系数（一次操作消掉 N 行的积分倍数）</h3>' +
      '<div class="fields">' +
      num('cfgCombo2', '消 2 行 ×', CFG.combo2, 0.1, 1) +
      num('cfgCombo3', '消 3 行 ×', CFG.combo3, 0.1, 1) +
      num('cfgCombo4', '消 4 行 ×', CFG.combo4, 0.1, 1) +
      num('cfgCombo5', '消 5 行及以上 ×', CFG.combo5, 0.1, 1) +
      '</div>' +
      '<h3 class="grp">计分与技能</h3>' +
      '<div class="fields">' +
      num('cfgCost', '技能点消耗 / 次', CFG.skillCost, 100, 0) +
      num('cfgScore', '每格积分', CFG.scorePerCell, 10, 0) +
      num('cfgSkill', '每格技能点', CFG.skillPerCell, 1, 0) +
      num('cfgSpScore', '金色奖励格积分', CFG.spScore, 50, 0) +
      num('cfgAdvScore', '困难块每掉 1 格血积分', CFG.advScore, 10, 0) +
      num('cfgAdvFull', '困难块 4 格耗完额外积分', CFG.advFullScore, 100, 0) +
      '<label class="field"><span>4 类型技能模式</span><select id="cfgSkill4">' +
      '<option value="shrink"' + (CFG.skill4Mode === 'shrink' ? ' selected' : '') + '>砍掉一半（4 格 → 2 格）</option>' +
      '<option value="retag"' + (CFG.skill4Mode === 'retag' ? ' selected' : '') + '>原地改标为 2 类型</option>' +
      '</select></label>' +
      '<label class="check"><input type="checkbox" id="cfgPreview"' + (CFG.preview ? ' checked' : '') + '> 预告下一行</label>' +
      '</div>' +
      '<h3 class="grp">数值导出 / 导入</h3>' +
      '<p class="muted small" style="text-align:left;margin:0 0 6px">' +
      '数值是存在<b>当前网址</b>的浏览器里的。把下面这段复制走，粘到别的浏览器 / 别的网址（比如从本地搬到线上），点「导入并重开」就能整套套用。</p>' +
      '<textarea id="cfgExport" class="cfgexport" spellcheck="false">' + JSON.stringify(CFG) + '</textarea>' +
      '<div class="btnrow" style="margin-top:8px">' +
      '<button data-act="copycfg">复制这段数值</button>' +
      '<button class="primary" data-act="importcfg">导入并重开</button>' +
      '</div>' +
      '<div class="btnrow">' +
      '<button class="primary" data-act="savecfg">保存并重开</button>' +
      '<button data-act="resetcfg">恢复默认</button>' +
      '<button data-act="close">取消</button>' +
      '</div>';
  }

  /* ============================================================
   * 十二、布局与输入
   * ============================================================ */

  function layout() {
    if (!dom.stage) return;
    var cellW = Math.floor((dom.stage.clientWidth - 8) / COLS);
    var availH = window.innerHeight - (window.innerWidth < 980 ? 300 : 180);
    var cellH = Math.floor(availH / ROWS);
    var cell = Math.max(20, Math.min(56, Math.min(cellW, cellH)));
    document.documentElement.style.setProperty('--cell', cell + 'px');
    dom.board.classList.add('noanim');
    setTimeout(function () { dom.board.classList.remove('noanim'); }, 60);
  }

  function findPosById(id) {
    for (var r = 0; r < ROWS; r++) for (var c = 0; c < COLS; c++) {
      var cell = G.board[r][c];
      if (cell && cell.id === id) return { r: r, c: c };
    }
    return null;
  }

  function bindInput() {
    document.addEventListener('click', function (e) {
      var t = e.target;
      var justDragged = G.suppressClick;
      G.suppressClick = false;
      var btn = t && t.closest ? t.closest('[data-act]') : null;
      if (btn) {
        var act = btn.getAttribute('data-act');
        if (act === 'pass') passTurn();
        else if (act === 'skill') useSkill();
        else if (act === 'restart') newGame();
        else if (act === 'help') showOverlay(helpHtml());
        else if (act === 'settings') {
          editWeights = currentLevelWeights();
          showOverlay(settingsHtml());
        }
        else if (act === 'addwrow') {
          if (editWeights) {
            readWeightInputs();
            editWeights.push(editWeights[editWeights.length - 1].slice());
            refreshWeightTable();
          }
        }
        else if (act === 'delwrow') {
          var dlv = Number(btn.getAttribute('data-lv'));
          if (editWeights && editWeights.length > 1 && dlv >= 0 && dlv < editWeights.length) {
            readWeightInputs();
            editWeights.splice(dlv, 1);
            refreshWeightTable();
          }
        }
        else if (act === 'resetw') {
          editWeights = defaultLevelWeights();
          refreshWeightTable();
        }
        else if (act === 'copycfg') {
          var ta = $('cfgExport');
          if (ta) {
            ta.focus(); ta.select();
            try { ta.setSelectionRange(0, 999999); } catch (e2) {}
            var done = false;
            try { done = document.execCommand('copy'); } catch (e3) {}
            toast(done ? '数值已复制到剪贴板' : '已全选，按 Ctrl+C 复制');
          }
        }
        else if (act === 'importcfg') {
          var box = $('cfgExport');
          var okImp = false;
          try {
            var o = JSON.parse(box.value);
            if (o && typeof o === 'object') {
              for (var kk in CFG) {
                if (!(kk in o)) continue;
                if (kk === 'levelWeights') {
                  if (o[kk] && typeof o[kk] === 'object') CFG[kk] = JSON.parse(JSON.stringify(o[kk]));
                } else if (typeof o[kk] === typeof CFG[kk]) {
                  CFG[kk] = o[kk];
                }
              }
              okImp = true;
            }
          } catch (e4) { okImp = false; }
          if (!okImp) { toast('这段数值格式不对，请整段复制粘贴'); return; }
          saveCfg(); hideOverlay(); newGame();
          toast('数值已导入，已按新数值重开');
        }
        else if (act === 'close') { if (G.running) hideOverlay(); else newGame(); }
        else if (act === 'resetcfg') { CFG = JSON.parse(JSON.stringify(DEFAULT_CFG)); saveCfg(); hideOverlay(); newGame(); }
        else if (act === 'savecfg') {
          CFG.emptyMin = clamp(Number($('cfgEmptyMin').value) || 2, 1, 8);
          CFG.emptyMax = clamp(Number($('cfgEmptyMax').value) || 6, CFG.emptyMin, 8);
          CFG.emptyTilt = Math.max(0, Number($('cfgEmptyTilt').value) || 0);
          readWeightInputs();
          CFG.levelWeights = (editWeights || currentLevelWeights()).map(function (row) { return row.slice(); });
          CFG.spEvery = Math.max(1, Number($('cfgSpEvery').value) || 1);
          CFG.advFirst = Math.max(1, Number($('cfgAdvFirst').value) || 1);
          CFG.advEvery = Math.max(1, Number($('cfgAdvEvery').value) || 1);
          CFG.advTighten = Math.max(0, Number($('cfgAdvTighten').value) || 0);
          CFG.rampEvery = Math.max(0, Number($('cfgRamp').value) || 0);
          CFG.minRows = Math.max(0, Number($('cfgMinRows').value) || 0);
          CFG.combo2 = Math.max(1, Number($('cfgCombo2').value) || 1);
          CFG.combo3 = Math.max(1, Number($('cfgCombo3').value) || 1);
          CFG.combo4 = Math.max(1, Number($('cfgCombo4').value) || 1);
          CFG.combo5 = Math.max(1, Number($('cfgCombo5').value) || 1);
          CFG.skillCost = Math.max(0, Number($('cfgCost').value) || 0);
          CFG.scorePerCell = Math.max(0, Number($('cfgScore').value) || 0);
          CFG.skillPerCell = Math.max(0, Number($('cfgSkill').value) || 0);
          CFG.spScore = Math.max(0, Number($('cfgSpScore').value) || 0);
          CFG.advScore = Math.max(0, Number($('cfgAdvScore').value) || 0);
          CFG.advFullScore = Math.max(0, Number($('cfgAdvFull').value) || 0);
          CFG.skill4Mode = $('cfgSkill4').value;
          CFG.preview = $('cfgPreview').checked;
          saveCfg(); hideOverlay(); newGame();
        }
        return;
      }
      var cellEl = t && t.closest ? t.closest('#board > .cell') : null;
      if (cellEl && cellEl.__cid != null && !justDragged) {
        var p = findPosById(cellEl.__cid);
        if (p) { G.sel = p; render(); }
      }
    });

    /* ---------- 拖拽：按住一条方块左右拖 ---------- */
    function cellPx() {
      return parseInt(getComputedStyle(document.documentElement).getPropertyValue('--cell'), 10) || 40;
    }
    function dragTip(d) {
      if (!dom.dragTip) return;
      if (!d || !d.offset) { dom.dragTip.classList.remove('show'); return; }
      dom.dragTip.innerHTML = '移动 ' + (d.hi - d.lo + 1) + ' 格方块 <b>' + Math.abs(d.offset) +
        '</b> 格' + (d.offset > 0 ? '（向右）' : '（向左）') + ' · 松开后涨 <b>1</b> 行';
      dom.dragTip.classList.add('show');
    }
    function previewBlock(d) {
      for (var c = d.lo; c <= d.hi; c++) {
        var cell = G.board[d.r][c];
        if (!cell) continue;
        var el = G.cellMap[cell.id];
        if (el) el.style.transform = posStyle(d.r, c + d.offset);
      }
    }

    dom.board.addEventListener('pointerdown', function (e) {
      if (G.busy || G.over || !G.running) return;
      var cellEl = e.target && e.target.closest ? e.target.closest('#board > .cell') : null;
      if (!cellEl || cellEl.__cid == null) return;
      var p = findPosById(cellEl.__cid);
      if (!p) return;
      var b = blockAt(p.r, p.c);
      if (!b) return;
      var range = blockRange(b);
      G.sel = p;
      G.drag = { r: p.r, lo: b.lo, hi: b.hi, startX: e.clientX, offset: 0, range: range };
      dom.board.classList.add('dragging');
      if (dom.board.setPointerCapture) { try { dom.board.setPointerCapture(e.pointerId); } catch (err) {} }
      render();
      if (range.min === 0 && range.max === 0) {
        if (dom.dragTip) {
          dom.dragTip.innerHTML = '这条方块两边都被挡住了，换一条拖';
          dom.dragTip.classList.add('show');
        }
      }
      e.preventDefault();
    });

    dom.board.addEventListener('pointermove', function (e) {
      var d = G.drag;
      if (!d) return;
      var off = clamp(Math.round((e.clientX - d.startX) / cellPx()), d.range.min, d.range.max);
      if (off === d.offset) return;
      d.offset = off;
      previewBlock(d);
      dragTip(d);
      e.preventDefault();
    });

    function endDrag(commit) {
      var d = G.drag;
      if (!d) return;
      G.drag = null;
      dom.board.classList.remove('dragging');
      dragTip(null);
      if (commit && d.offset !== 0) {
        G.suppressClick = true;
        moveBlock(d.r, d.lo, d.offset);
      } else {
        render();
      }
    }
    dom.board.addEventListener('pointerup', function (e) { endDrag(true); e.preventDefault(); });
    dom.board.addEventListener('pointercancel', function () { endDrag(false); });
    window.addEventListener('pointerup', function () { if (G.drag) endDrag(true); });
    window.addEventListener('resize', layout);
  }

  /* ============================================================
   * 十三、启动
   * ============================================================ */

  function boot() {
    bootDom();
    emptyBoard();
    layout();
    bindInput();
    render();
    window.TB = {
      get state() { return G; },
      get config() { return CFG; },
      constants: { ROWS: ROWS, COLS: COLS, T: T },
      newGame: newGame,
      moveBlock: function (r, col, offset) { return moveBlock(r, col, offset); },
      pass: passTurn,
      resolve: function (combo) { return resolveBoard(combo !== false); },
      useSkill: useSkill,
      settle: settle,
      render: render,
      buildRow: function (idx, adv, sp) { return buildRow(idx, adv, sp); },
      tideLevel: tideLevel,
      occupiedRowCount: occupiedRowCount
    };
    showOverlay(
      '<h2>土耳其方块</h2>' +
      '<p class="muted">10 行 × 9 列 · 拖动整条方块 · 悬空即整体下落 · 满行消除 · 底部不断涨行</p>' +
      '<div class="btnrow">' +
      '<button class="primary big" data-act="close">开始游戏</button>' +
      '<button data-act="help">查看完整规则</button>' +
      '</div>'
    );
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();

})();

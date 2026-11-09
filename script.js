/* ---------- CALCULATION LOGIC (works for 1 to 16 bits, uses BigInt) ---------- */
function calc(op, a, b, n) {
  if (!(n >= 1 && n <= 16) || Math.floor(n) !== n) return { err: "Bits must be a whole number from 1 to 16." };
  var L = [], one = 1n, N = BigInt(n);
  var mask = (one << N) - one, msb = one << (N - one), mx = msb - one;
  a = BigInt(a); b = BigInt(b);
  var bn = function (x, w) { w = w || n; return BigInt.asUintN(w, x).toString(2).padStart(w, "0"); };
  var twoSide = (op === "add2" || op === "sub2" || op === "mul" || op === "div");
  var lo = twoSide ? -msb : -mx;
  if (a < lo || a > mx || b < lo || b > mx) return { err: "Numbers must be between " + lo + " and " + mx + " for " + n + " bits." };
  var res = { lines: L, expr: "", val: "", bin: "", warn: "", bits: [], method: "", rule: "" };

  if (op === "add1" || op === "sub1") {
    var t1 = function (x) { return x >= 0n ? x : mask ^ (-x); };
    var A = t1(a), B = t1(b), sub = op === "sub1";
    L.push("A = " + a + "  ->  " + bn(A));
    L.push("B = " + b + "  ->  " + bn(B));
    if (sub) { B = mask ^ B; L.push("Subtraction: take 1's complement of B  ->  " + bn(B) + "  (this is -B)"); }
    var total = A + B, carry = total >> N, s = total & mask;
    L.push("Add: " + bn(A) + " + " + bn(B) + " = " + carry + " " + bn(s) + "   (carry = " + carry + ")");
    if (carry) { var s0 = s; s = s + one; L.push("Carry is 1, so add it back (end-around carry): " + bn(s0) + " + 1 = " + bn(s)); }
    else L.push("No carry out, so nothing to add back.");
    var neg = (s & msb) !== 0n, val = neg ? -(mask ^ s) : s;
    if (neg) L.push("MSB is 1, so answer is negative. Magnitude = 1's complement of " + bn(s) + " = " + bn(mask ^ s));
    L.push("Final answer = " + val);
    if ((A & msb) === (B & msb) && (s & msb) !== (A & msb)) res.warn = "Overflow: the answer does not fit in " + n + " bits.";
    res.bits = [["A", bn(A)], [sub ? "-B" : "B", bn(B)], ["Result", bn(s)]];
    res.expr = a + (sub ? " - " : " + ") + "(" + b + ")"; res.val = String(val); res.bin = bn(s);
  }
  else if (op === "add2" || op === "sub2") {
    var A2 = BigInt.asUintN(n, a), B2 = BigInt.asUintN(n, b), sb = op === "sub2";
    L.push("A = " + a + "  ->  " + bn(A2));
    L.push("B = " + b + "  ->  " + bn(B2));
    if (sb) {
      var inv = mask ^ B2;
      B2 = (inv + one) & mask;
      L.push("Subtraction: take 2's complement of B");
      L.push("1's complement of B = " + bn(inv) + ", add 1 -> " + bn(B2) + "  (this is -B)");
    }
    var sm = A2 + B2, cr = sm >> N, r = sm & mask;
    L.push("Add: " + bn(A2) + " + " + bn(B2) + " = " + cr + " " + bn(r) + "   (carry = " + cr + ")");
    L.push(cr ? "Carry out is 1. In 2's complement we ignore (discard) it." : "No carry out.");
    var ng = (r & msb) !== 0n, v = ng ? r - (one << N) : r;
    if (ng) L.push("MSB is 1, so answer is negative. Magnitude = 2's complement of " + bn(r) + " = " + bn(((mask ^ r) + one) & mask));
    L.push("Final answer = " + v);
    if ((A2 & msb) === (B2 & msb) && (r & msb) !== (A2 & msb)) res.warn = "Overflow: the answer does not fit in " + n + " bits.";
    res.bits = [["A", bn(A2)], [sb ? "-B" : "B", bn(B2)], ["Result", bn(r)]];
    res.expr = a + (sb ? " - " : " + ") + "(" + b + ")"; res.val = String(v); res.bin = bn(r);
  }
  else if (op === "mul") {
    var w = 2 * n, W = BigInt(w), wm = (one << W) - one, pr;
    if (a >= 0n && b >= 0n) {
      res.method = "Signed-operand multiplication (sign extension)";
      res.rule = "Both numbers are positive, so signed-operand multiplication with sign extension is used. A is sign-extended to double the bits. For every 1 in B, the extended A is shifted left and added. The sign bit of B is 0, so nothing is added for it.";
      L.push("Both numbers are positive, so signed-operand multiplication with sign extension is used.");
      L.push("A = " + a + "  ->  " + bn(a) + ", sign-extended to " + w + " bits  ->  " + bn(a, w));
      L.push("B = " + b + "  ->  " + bn(b) + "  (sign bit is 0)");
      var tot = 0n;
      for (var i = 0; i < n - 1; i++) {
        var I = BigInt(i);
        if (((b >> I) & one) === one) { var p = (a << I) & wm; tot = (tot + p) & wm; L.push("Bit " + i + " of B = 1: add A shifted left " + i + " = " + bn(p, w) + "   total = " + bn(tot, w) + " (" + tot + ")"); }
        else L.push("Bit " + i + " of B = 0: add 0   total = " + bn(tot, w) + " (" + tot + ")");
      }
      L.push("Bit " + (n - 1) + " of B is the sign bit = 0, so nothing is added for it.");
      pr = tot;
    } else {
      res.method = "Booth's algorithm";
      res.rule = "At least one number is negative, so Booth's algorithm is used. Look at Q0 and Q-1: 10 means A = A - M, 01 means A = A + M, 00 or 11 means no operation. Then shift A, Q and Q-1 right (arithmetic shift). Repeat for all bits.";
      var M = a, Aa = 0n, Qr = BigInt.asUintN(n, b), Qm = 0n;
      L.push("One number is negative, so Booth's algorithm is used.");
      L.push("M (multiplicand) = " + a + "  ->  " + bn(M));
      L.push("Q (multiplier) = " + b + "  ->  " + bn(Qr) + ",  A = " + bn(0n) + ",  Q-1 = 0,  count = " + n);
      for (var k = 1; k <= n; k++) {
        var q0 = Qr & one, pair = "" + q0 + Qm, act = "no operation";
        if (pair === "10") { Aa -= M; act = "A = A - M"; }
        else if (pair === "01") { Aa += M; act = "A = A + M"; }
        var shown = (Aa > mx || Aa < -msb) ? bn(Aa, n + 1) : bn(Aa);
        var ln = "Step " + k + ": Q0 Q-1 = " + q0 + " " + Qm + "  ->  " + act + (act === "no operation" ? "" : " = " + shown);
        var nq = Qr & one;
        Qr = (Qr >> one) | ((Aa & one) << (N - one));
        Aa = Aa >> one; Qm = nq;
        L.push(ln + "\n         shift right: A = " + bn(Aa) + ", Q = " + bn(Qr) + ", Q-1 = " + Qm);
      }
      pr = Aa * (one << N) + Qr;
      L.push("Join A and Q: " + bn(Aa) + " " + bn(Qr) + "  =  " + pr);
    }
    L.push("Final answer = " + pr);
    res.bits = [["Product", bn(pr, w)]];
    res.expr = a + " \u00d7 (" + b + ")"; res.val = String(pr); res.bin = bn(pr, w);
  }
  else if (op === "div") {
    if (b === 0n) return { err: "Division by zero is not possible." };
    var d1 = a < 0n ? -a : a, d2 = b < 0n ? -b : b, Ac = 0n, Q = d1;
    L.push("Restoring division on the magnitudes.");
    L.push("Dividend (Q) = " + d1 + " (" + bn(d1) + "),  Divisor (M) = " + d2 + " (" + bn(d2) + "),  A = 0");
    for (var j = 1; j <= n; j++) {
      Ac = (Ac << one) | ((Q >> (N - one)) & one);
      Q = (Q << one) & mask;
      var t = Ac - d2;
      if (t < 0n) L.push("Step " + j + ": shift left, A - M is negative, so restore A.  Q0 = 0.  A = " + bn(Ac, n + 1) + ", Q = " + bn(Q));
      else { Ac = t; Q = Q | one; L.push("Step " + j + ": shift left, A - M is not negative, so keep it.  Q0 = 1.  A = " + bn(Ac, n + 1) + ", Q = " + bn(Q)); }
    }
    var qs = ((a < 0n) !== (b < 0n) && Q !== 0n) ? -Q : Q, rs = (a < 0n && Ac !== 0n) ? -Ac : Ac;
    L.push("Quotient = Q = " + bn(Q) + " (" + Q + "), Remainder = A = " + Ac);
    L.push("Quotient is negative if the signs differ. Remainder takes the sign of the dividend.");
    L.push("Final answer: Quotient = " + qs + ", Remainder = " + rs);
    res.bits = [["Quotient", bn(Q)], ["Remainder", bn(Ac)]];
    res.expr = a + " \u00f7 (" + b + ")";
    res.val = "Quotient = " + qs + ", Remainder = " + rs;
    res.bin = "Quotient = " + bn(qs) + ",  Remainder = " + bn(rs);
  }
  return res;
}

/* ---------- PAGE CODE ---------- */
var OPS = [["add1", "+", "1's complement addition"], ["sub1", "\u2212", "1's complement subtraction"], ["add2", "+", "2's complement addition"],
           ["sub2", "\u2212", "2's complement subtraction"], ["mul", "\u00d7", "Multiplication"], ["div", "\u00f7", "Division"]];
var RULE = {
  add1: "1's complement: a negative number is made by flipping all the bits. If a carry comes out of the last bit, it is added back to the result (end-around carry).",
  sub1: "A - B is done as A + (1's complement of B). Then the end-around carry is added back.",
  add2: "2's complement: a negative number is made by flipping all the bits and adding 1. The carry out of the last bit is ignored.",
  sub2: "A - B is done as A + (2's complement of B). The carry out is ignored.",
  mul: "If both numbers are positive, signed-operand multiplication with sign extension is used. If any number is negative, Booth's algorithm is used.",
  div: "Restoring division: shift A and Q left and subtract M from A. If A becomes negative, restore it and set Q0 = 0, otherwise set Q0 = 1."
};
var op = "add2", timers = [], cur = null, shown = 0, D = 650;
function $(id) { return document.getElementById(id); }
function later(fn, ms) { timers.push(setTimeout(fn, ms)); }
function stop() { timers.forEach(clearTimeout); timers = []; }
function nameOf(o) { return OPS.filter(function (x) { return x[0] === o; })[0][2]; }
function numsOk() { return /^-?\d+$/.test($("a").value.trim()) && /^-?\d+$/.test($("b").value.trim()); }
function bitsVal() { var t = $("bitsN").value.trim(); if (!/^\d+$/.test(t)) return 0; var n = parseInt(t, 10); return (n >= 1 && n <= 16) ? n : 0; }

function rangeInfo() {
  var n = bitsVal();
  if (!n) { $("range").textContent = "Enter a number of bits from 1 to 16."; return; }
  var h = Math.pow(2, n - 1);
  $("range").innerHTML = "1's complement: " + (1 - h) + " to " + (h - 1) + "<br>2's complement: " + (-h) + " to " + (h - 1);
}

function group(s) {   // 11111110 -> 1111 1110 (groups of 4 from the right)
  var out = [];
  for (var i = s.length; i > 0; i -= 4) out.unshift(s.slice(Math.max(0, i - 4), i));
  return out.map(function (g) { return '<span class="nib">' + g + '</span>'; }).join("");
}

function buildOps() {
  $("ops").innerHTML = OPS.map(function (o) {
    return '<button class="op" id="op-' + o[0] + '"><span class="sym">' + o[1] + '</span>' + o[2] + '</button>';
  }).join("");
  OPS.forEach(function (o) {
    $("op-" + o[0]).addEventListener("click", function () { op = o[0]; markOps(); if (numsOk() && bitsVal()) run(); else idleInfo(); });
  });
  markOps(); idleInfo();
}
function markOps() { OPS.forEach(function (o) { $("op-" + o[0]).className = "op" + (o[0] === op ? " on" : ""); }); }
function idleInfo() { stop(); $("opname").textContent = nameOf(op); $("rule").textContent = RULE[op]; $("chip").textContent = ""; }

function message(t) {
  $("binout").innerHTML = '<span class="idle" style="color:#b3261e">' + t + '</span>';
  $("warn").textContent = ""; $("expr").innerHTML = "&nbsp;"; $("chip").textContent = "";
  $("regs").innerHTML = '<span class="idle">Bits will appear here.</span>'; $("steps").innerHTML = ""; $("fill").style.width = "0";
}

function regsHtml(bits) {
  var len = bits[0][1].length, cw = len > 16 ? 18 : 22, h = '<div class="row"><span class="nm"></span>';
  for (var i = 0; i < len; i++) { var pos = len - 1 - i; h += '<i class="rn' + (pos % 4 === 3 && i > 0 ? " g" : "") + '" style="width:' + cw + 'px">' + pos + '</i>'; }
  h += '</div>';
  bits.forEach(function (row, k) {
    h += '<div class="row pop" style="animation-delay:' + (k * 0.2) + 's"><span class="nm">' + row[0] + '</span>';
    row[1].split("").forEach(function (ch, i) {
      var pos = len - 1 - i;
      h += '<i class="cell c' + ch + (pos % 4 === 3 && i > 0 ? " g" : "") + '" style="width:' + cw + 'px">' + ch + '</i>';
    });
    h += '</div>';
  });
  return h;
}

function run() {
  stop(); cur = null; shown = 0;
  var n = bitsVal();
  $("opname").textContent = nameOf(op); $("rule").textContent = RULE[op]; rangeInfo();
  if (!n) { message("Number of bits must be a whole number from 1 to 16."); return; }
  if (!numsOk()) { message("Enter whole numbers in both A and B (negative numbers are allowed)."); return; }
  var a = parseInt($("a").value, 10), b = parseInt($("b").value, 10);
  var r = calc(op, a, b, n);
  if (r.err) { message(r.err); return; }
  cur = r;
  $("expr").textContent = r.expr + "     (" + n + " bits)";
  $("chip").textContent = r.method;
  $("rule").textContent = r.rule || RULE[op];
  $("warn").textContent = "";
  $("binout").innerHTML = '<span class="idle">Working...</span>';
  $("regs").innerHTML = regsHtml(r.bits);
  $("steps").innerHTML = ""; $("fill").style.width = "0";
  r.lines.forEach(function (line, i) { later(revealNext, 300 + i * D); });
}

function revealNext() {
  if (!cur || shown >= cur.lines.length) return;
  var box = $("steps"), old = box.querySelector(".cur"); if (old) old.className = "st";
  var d = document.createElement("div"); d.className = "st cur";
  d.innerHTML = '<span class="no"></span><span class="tx"></span>';
  d.querySelector(".no").textContent = (shown < 9 ? "0" : "") + (shown + 1);
  d.querySelector(".tx").textContent = cur.lines[shown];
  box.appendChild(d);
  shown++;
  $("fill").style.width = Math.round(shown / cur.lines.length * 100) + "%";
  if (shown === cur.lines.length) finish();
}

function finish() {
  var r = cur, h;
  if (op === "div") {
    h = '<div class="line"><span class="rowlab">Quotient</span>' + group(r.bits[0][1]) + '</div><div class="line"><span class="rowlab">Remainder</span>' + group(r.bits[1][1]) + '</div>';
    var q = r.bin.split(",")[0].replace("Quotient = ", ""), m = r.bin.split(",")[1].replace("Remainder = ", "").trim();
    h = '<div class="line"><span class="rowlab">Quotient</span>' + group(q) + '</div><div class="line"><span class="rowlab">Remainder</span>' + group(m) + '</div>';
  } else h = group(r.bin);
  $("binout").innerHTML = h;
  $("warn").textContent = r.warn || "";
}

$("go").addEventListener("click", run);
$("replay").addEventListener("click", function () { if (cur) run(); });
$("next").addEventListener("click", function () { if (!cur) return; stop(); revealNext(); });
$("showall").addEventListener("click", function () { if (!cur) return; stop(); while (shown < cur.lines.length) revealNext(); });

function syncBits(from) {
  var v = $(from).value; $(from === "bitsR" ? "bitsN" : "bitsR").value = v;
  rangeInfo(); if (numsOk() && bitsVal()) run();
}
$("bitsR").addEventListener("input", function () { syncBits("bitsR"); });
$("bitsN").addEventListener("input", function () { var n = bitsVal(); if (n) $("bitsR").value = n; rangeInfo(); if (numsOk() && n) run(); });
document.addEventListener("keydown", function (e) { if (e.key === "Enter") run(); });
buildOps(); rangeInfo();
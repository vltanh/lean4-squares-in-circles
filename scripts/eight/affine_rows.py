#!/usr/bin/env python3
"""Convert an affine table (JSON) into the integer data the Lean checker reads.

For a table NAME it writes, under data/eight/affine:

  NAME.rows   first line: den rows; then one row per line,
              edge source target axis k r lo hi lam mode [h1 c1 ... c(m-1) hm]
              (angles over den, lam over 10^8; mode 0 endpoints, 1 lower, 2 upper,
              3 circle; a circle row gives its m pieces: the parameters h_j, over 10^7, and
              the interior cuts c_j, over den). Rows are sorted by
              (source, target, axis, positive first, lo, hi). The rows of an excluded arc
              pair and axis (ExcludedArcs) are left out, and with --core those of two core
              arcs.
  NAME.arcs   first line: den arcs; seven lines `betaHalf.lo betaHalf.hi gamma.lo gamma.hi`;
              one line per arc: side positive, then the fixed-point intervals (lo hi) of
              c p q shift rho aLo bLo aHi bHi rLo rHi alpha; alpha is the arctangent
              interval of the arc from the integer bounds of AtanBounds.lean, exactly.

Fixed point: integers over 10^24, outward rounding, exactly as Arithmetic/Fixed.lean,
Bernstein11.lean, Bernstein7.lean, TrigLin.lean and RowCheck.lean. Every row and the angle
coverage are checked here with the same integer algorithm before anything is written; circle
rows are split into pieces whose AM-GM parameter h is sqrt V at the piece's midpoint. With
--enhance the rows are checked against the targets raised by the given millionths.

With --core markers the rows of two core arcs are left out and the table module proves their
costs from the markers of the core arcs (Candidate/GeometricCoreMarker.lean), and that no edge
joins two core squares (`no_adjacent_core`). With --core free they are left out and the charged
bound assumes that no edge joins two core squares.

With --lean MODULE it also writes the Lean modules of the table under
SquaresInCircles/Eight/Generated/Affine:

  MODULE/Meta.lean      the exact data of the table;
  MODULE/Context.lean   the arc boxes and arctangent intervals (in blocks), the scalars, the
                        state chains and the coverage data, checked against Meta.lean;
  MODULE/RowsNNN.lean   10000 rows each, in parts of 200 rows, one theorem per part;
  MODULE/Data.lean      all rows, as the list of parts;
  MODULE/CoverNN.lean   the coverage walk, in blocks of sources;
  MODULE.lean           all row claims, the coverage and the charged bound;
  MODULE/Enhanced.lean  with --enhance, the same for the enhanced targets.

  python3 -I scripts/eight/affine_rows.py PATH/NAME.json [--out DIR] [--lean MODULE]
      [--enhance e0,...,e6] [--core markers|free]
"""
import argparse
import fcntl
import hashlib
import json
import math
import sys
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path

UNIT = 10 ** 24
LAM_SCALE = 10 ** 8
H_SCALE = 10 ** 7

# ----------------------------------------------------------------- fixed point (Fixed.lean)


def fadd(I, J):
    return (I[0] + J[0], I[1] + J[1])


def fneg(I):
    return (-I[1], -I[0])


def fsub(I, J):
    return (I[0] - J[1], I[1] - J[0])


def fmul(I, J):
    a, b, c, d = I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1]
    return (min(min(a, b), min(c, d)) // UNIT, -((-max(max(a, b), max(c, d))) // UNIT))


def ofDiv(n, d):
    m = n * UNIT
    return (m // d, -((-m) // d))


def ofQ(q):
    q = F(q)
    return ofDiv(q.numerator, q.denominator)


def ofQI(lo, hi):
    return (ofQ(lo)[0], ofQ(hi)[1])


def scaleDiv(I, n, d):
    return ((I[0] * n) // d, -((-(I[1] * n)) // d))


def point(a):
    return (a, a)


ZERO = (0, 0)


def cdiv(a, b):
    return -((-a) // b)


# ----------------------------------------------------------------- trig test (TrigLin.lean)


def trigLower(c0, c1, c2, c3):
    return [c0[0] + c3[0], c1[0] + c2[0], (-c3[1]) // 2, (-c2[1]) // 6, c3[0] // 24,
            c2[0] // 120, (-c3[1]) // 720, (-c2[1]) // 5040, c3[0] // 40320,
            min(0, c2[0]) // 362880, min(0, -c3[1]) // 3628800]


def shift(den, l, d, p):
    b = [p[i] * den ** (10 - i) for i in range(11)]
    return [d ** j * sum(comb(i, j) * b[i] * l ** (i - j) for i in range(j, 11)) for j in range(11)]


BW = [[3628800 * comb(k, j) // comb(10, j) for j in range(11)] for k in range(11)]


def bern(q):
    return [sum(BW[k][j] * q[j] for j in range(k + 1)) for k in range(11)]


def lower6(c0, c1, c2, c3):
    """the lower polynomial of degree six for u in [0, 4/5] (TrigLin.lowerPN6)"""
    return [c0[0] + c3[0], c1[0] + c2[0], (-c3[1]) // 2, (-c2[1]) // 6, c3[0] // 24,
            c2[0] // 120, (-c3[1]) // 720 + (-max(0, c2[1])) // 6300 + min(0, c3[0]) // 63000]


def shift6(den, l, d, p):
    b = [p[i] * den ** (6 - i) for i in range(7)]
    return [d ** j * sum(comb(i, j) * b[i] * l ** (i - j) for i in range(j, 7)) for j in range(7)]


BW6 = [[720 * comb(k, j) // comb(6, j) for j in range(7)] for k in range(7)]


def bern6(q):
    return [sum(BW6[k][j] * q[j] for j in range(k + 1)) for k in range(7)]


def eval_at(den, x, c):
    """N7.evalAt / N11.evalAt: den^n c(x / den) for the degree n = len(c) - 1."""
    n = len(c) - 1
    return sum(c[i] * x ** i * den ** (n - i) for i in range(n + 1))


def trig_test6(den, l, h, c0, c1, c2, c3, strict):
    if not (den > 0 and l <= h and 5 * h <= 4 * den):
        return False
    p = lower6(c0, c1, c2, c3)
    P = [a if a > 0 else 0 for a in p]
    N = [-a if a < 0 else 0 for a in p]
    a, b = eval_at(den, h, N), eval_at(den, l, P)
    if (a < b) if strict else (a <= b):
        return True
    bp = bern6(shift6(den, l, h - l, P))
    bn = bern6(shift6(den, l, h - l, N))
    if strict:
        return all(x < y for x, y in zip(bn, bp))
    return all(x <= y for x, y in zip(bn, bp))


def trig_test3(den, l, h, c0, c1, c2, c3, strict):
    """TrigLin.mono3: the degree-three polynomial on [0, 1], by its two monotone parts."""
    if not (den > 0 and h <= den):
        return False
    a0, a1 = c0[0] + c3[0], c1[0] + c2[0]
    n2, n3 = (max(c3[0], 0) + 1) // 2, (max(c2[0], 0) + 5) // 6
    pos = max(a0, 0) * den ** 3 + max(a1, 0) * l * den ** 2
    neg = max(-a0, 0) * den ** 3 + max(-a1, 0) * h * den ** 2 + n2 * h * h * den + n3 * h ** 3
    return neg < pos if strict else neg <= pos


def trig_test(den, l, h, c0, c1, c2, c3, strict):
    """trigPositive / trigNonneg: degree three first, then six, then ten."""
    return (trig_test3(den, l, h, c0, c1, c2, c3, strict)
            or trig_test6(den, l, h, c0, c1, c2, c3, strict)
            or trig_test10(den, l, h, c0, c1, c2, c3, strict))


def trig_test10(den, l, h, c0, c1, c2, c3, strict):
    if not (den > 0 and l <= h):
        return False
    p = trigLower(c0, c1, c2, c3)
    P = [a if a > 0 else 0 for a in p]
    N = [-a if a < 0 else 0 for a in p]
    a, b = eval_at(den, h, N), eval_at(den, l, P)
    if (a < b) if strict else (a <= b):
        return True
    bp = bern(shift(den, l, h - l, P))
    bn = bern(shift(den, l, h - l, N))
    if strict:
        return all(x < y for x, y in zip(bn, bp))
    return all(x <= y for x, y in zip(bn, bp))


def pos3(den, l, h, c1, t):
    return trig_test(den, l, h, t[0], c1, t[1], t[2], True)


def mag(I):
    """Fixed.FI.mag: a bound of the absolute values of I, over unit."""
    return max(-I[0], I[1])


def nonneg3(den, l, h, t):
    """nonneg3: t0 >= |t1| + |t2| (crude3), or the trigonometric test."""
    return mag(t[1]) + mag(t[2]) <= t[0][0] or trig_test(den, l, h, t[0], ZERO, t[1], t[2], False)


# ----------------------------------------------------------------- rational intervals


def qadd(I, J):
    return (I[0] + J[0], I[1] + J[1])


def qneg(I):
    return (-I[1], -I[0])


def qmul(I, J):
    c = [I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1]]
    return (min(min(c[0], c[1]), min(c[2], c[3])), max(max(c[0], c[1]), max(c[2], c[3])))


def qinv(I):
    return (1 / I[1], 1 / I[0])


def qpoint(q):
    return (F(q), F(q))


def qpow(I, n):
    r = qpoint(1)
    for _ in range(n):
        r = qmul(r, I)
    return r


ROOT_SCALE = 10 ** 14


def rootBracket(x):
    x = F(x)
    num = x.numerator if x.numerator > 0 else 0
    k = isqrt((num * ROOT_SCALE ** 2) // x.denominator)
    return (F(k, ROOT_SCALE), F(k + 1, ROOT_SCALE))


def sqrt_valid(rng, J):
    return 0 <= rng[0] and 0 <= J[0] and J[0] ** 2 <= rng[0] and rng[1] <= J[1] ** 2 and 0 <= J[1]


# ----------------------------------------------------------------- arcs (PreparedArc.lean)


class Arc:
    pass


def is_side(a):
    return (not a.outer) and a.thi <= F(6, 7)


def shift_of(a):
    return F(-1, 2) if a.outer else F(1, 2)


def disc(a, Q, u):
    if a.outer:
        return (u + 1) ** 2 + 4 * (1 + u ** 2) * (Q - F(1, 2))
    return (u + 1) ** 2 - (1 + u ** 2) * F(71, 36)


def endpoint_range(a, Q, u, root):
    if is_side(a) or ((not a.outer) and u == F(6, 7)):
        return qpoint(F(7, 12)), True
    c = -(u + 1) if a.outer else u + 1
    ok = sqrt_valid(qpoint(disc(a, Q, u)), root)
    return qmul(qadd(qpoint(c), root), qinv(qpoint(2 * (1 + u ** 2)))), ok


def prepare(a, Q):
    """Ranges of the prepared arc (PreparedArc.ofArc) and its NumericValid."""
    if is_side(a):
        rootLo = rootHi = radiusRoot = (F(0), F(0))
    else:
        rootLo = rootBracket(disc(a, Q, a.tlo))
        rootHi = rootBracket(disc(a, Q, a.thi))
        radiusRoot = rootBracket(Q) if a.outer else (F(0), F(0))
    aLo, ok1 = endpoint_range(a, Q, a.tlo, rootLo)
    aHi, ok2 = endpoint_range(a, Q, a.thi, rootHi)
    bLo = qmul(qpoint(a.tlo), aLo)
    bHi = qmul(qpoint(a.thi), aHi)
    if a.outer:
        rho, ok3 = radiusRoot, sqrt_valid(qpoint(Q), radiusRoot)
    else:
        rho, ok3 = qpoint(F(1, 12)), True
    if is_side(a):
        rLo = rHi = qpoint(0)
        ok4 = True
    else:
        s = shift_of(a)
        dl = qadd(aLo, qneg(qpoint(s)))
        dh = qadd(aHi, qneg(qpoint(s)))
        ok4 = dl[0] > 0 and dh[0] > 0
        rLo = qmul(qadd(bLo, qneg(qpoint(s))), qinv(dl))
        rHi = qmul(qadd(bHi, qneg(qpoint(s))), qinv(dh))
    wf = 0 <= a.tlo <= a.thi <= 1 and (a.outer or a.thi <= F(6, 7) or F(6, 7) <= a.tlo)
    valid = wf and F(1, 2) < Q and ok1 and ok2 and ok3 and ok4
    return valid, dict(rho=rho, aLo=aLo, bLo=bLo, aHi=aHi, bHi=bHi, rLo=rLo, rHi=rHi)


# ----------------------------------------------------------------- arctangent endpoints


ANGLE_UNIT = 10 ** 20
ANCHOR_LO = [0, 6241880999595733145, 12435499454676140262, 18534794999569471987,
             24497866312686409976, 30288486837497134474, 35877067027057215554,
             41241044159738723967, 46364760900080604768, 51238946031073763745,
             55859931534356236641, 60228734613496411195, 64350110879328431699,
             68231655487474800840, 71882999962162443554, 75315128096219431964,
             78539816339744823972]
ANCHOR_HI = [0, 6241880999596249904, 12435499454677131384, 18534794999570863620,
             24497866312688113819, 30288486837499064224, 35877067027059298026,
             41241044159740903614, 46364760900082843060, 51238946031076035869,
             55859931534358527563, 60228734613498712249, 64350110879330738085,
             68231655487477109982, 71882999962164754102, 75315128096221743223,
             78539816339747135590]


def floorQ(q):
    q = F(q)
    return q.numerator // q.denominator


def ceilQ(q):
    return -floorQ(-q)


def atan_poly_lo(z):
    return z * (1 - z * z * (F(1, 3) - z * z * (F(1, 5) - z * z * (F(1, 7) - z * z * (F(1, 9)
                - z * z / 11)))))


def atan_poly_hi(z):
    return z * (1 - z * z * (F(1, 3) - z * z * (F(1, 5) - z * z * (F(1, 7) - z * z / 9))))


def series_lo(z):
    return floorQ(atan_poly_lo(z) * ANGLE_UNIT) if z >= 0 else -ceilQ(atan_poly_hi(-z) * ANGLE_UNIT)


def series_hi(z):
    return ceilQ(atan_poly_hi(z) * ANGLE_UNIT) if z >= 0 else -floorQ(atan_poly_lo(-z) * ANGLE_UNIT)


def anchor_index(x):
    return min(16, max(0, floorQ(16 * x + F(1, 2))))


def anchor_arg(x):
    j = anchor_index(x)
    return (x - F(j, 16)) / (1 + x * F(j, 16))


def atan_lo(x):
    """PairCover.atanLo: a lower bound of arctan x over 10^20, by the addition formula at the
    anchor j/16 nearest to x and the alternating series."""
    x = F(x)
    return ANCHOR_LO[anchor_index(x)] + series_lo(anchor_arg(x)) if x >= 0 else -2 * ANGLE_UNIT


def atan_hi(x):
    """PairCover.atanHi: an upper bound of arctan x over 10^20."""
    x = F(x)
    return ANCHOR_HI[anchor_index(x)] + series_hi(anchor_arg(x)) if x >= 0 else 2 * ANGLE_UNIT


def alpha_fi(a):
    """alphaFI in RowCover.lean: the arctangent interval of the arc, exactly in fixed point."""
    lo, hi = atan_lo(a.tlo) * 10 ** 4, atan_hi(a.thi) * 10 ** 4
    return (lo, hi) if a.positive else (-hi, -lo)


CORE = None   # --core: how the table bounds the costs of two core arcs


def excluded(aS, aT, axis):
    """excludedB / ExcludedArcs in RowCover.lean and AffineCoverage.lean: the arc pairs and axes
    that no feasible separator has."""
    zero = aS.role in (0, 2, 4)
    quarter = aS.role in (1, 3, 5, 6)
    return ((zero and ((axis == 2 and not aT.outer) or (axis == 4 and not aS.outer)))
            or (axis == 1 and not aS.positive and not aT.outer)
            or (axis == 3 and aT.positive and not aS.outer)
            or (quarter and not aS.outer and not aT.outer and aS.positive and not aT.positive))


def skipped(aS, aT, axis):
    """skipB in RowCover.lean: the excluded keys and, with --core, the pairs of two core arcs."""
    return excluded(aS, aT, axis) or (CORE is not None and not aS.outer and not aT.outer)


# ----------------------------------------------------------------- tables


def load_table(path):
    d = json.load(open(path))
    t = Arc()
    t.Q = F(d["Q"])
    t.arcs = []
    t.index = {}
    for i, a in enumerate(d["arcs"]):
        x = Arc()
        x.id, x.role = a["id"], a["role"]
        x.outer, x.positive = a["kind"] == "O", a["sign"] == 1
        x.tlo, x.thi = F(a["lo"]), F(a["hi"])
        x.c, x.p, x.q = F(a["c"]), F(a["p"]), F(a["q"])
        assert x.id not in t.index
        t.index[x.id] = i
        t.arcs.append(x)
    t.gamma = [F(g) for g in d["gamma"]]
    t.beta = [F(b) for b in d.get("beta", [0] * 7)]
    t.word = d.get("word", [0, 1, 0, 1, 0, 1, 1])
    t.diff = [tuple(F(v) for v in d.get("difference_ranges", {}).get(str(i), ["-7/10", "7/10"]))
              for i in range(7)]
    t.axes = [d.get("axis_domains", {}).get(str(i), [1, 2, 3, 4]) for i in range(7)]
    t.rows = d["rows"]
    return t


def make_box(a, Q):
    valid, r = prepare(a, Q)
    assert valid, "arc %d is not NumericValid" % a.id
    b = dict(side=is_side(a), positive=a.positive, c=ofQ(a.c), p=ofQ(a.p), q=ofQ(a.q),
             shift=ofQ(shift_of(a)))
    for k in ("rho", "aLo", "bLo", "aHi", "bHi", "rLo", "rHi"):
        b[k] = ofQI(*r[k])
    b["alpha"] = alpha_fi(a)
    return b


def reverse(b):
    r = dict(b)
    r["positive"] = not b["positive"]
    r["c"], r["p"], r["q"] = fneg(b["c"]), fneg(b["p"]), fneg(b["q"])
    return r


# ----------------------------------------------------------------- the row check (RowCheck.lean)

PI_HALF = (1570796326794896619000000, 1570796326794896619500000)


def newton(m, n, h):
    for _ in range(n):
        h = (m // h + h) // 2 if h != 0 else 0
    return h


def sqrtUp(V, guess):
    m = V[1] * UNIT
    h = max(1, newton(m, 5, guess))
    return cdiv(cdiv(m, h) + h, 2)


def source_lower(S, X, Y):
    atLo = fadd(fmul(X, S["aLo"]), fmul(Y, S["bLo"]))
    atHi = fadd(fmul(X, S["aHi"]), fmul(Y, S["bHi"]))
    if S["side"] or 0 <= X[0]:
        return min(atLo[0], atHi[0])
    dLo = fsub(Y, fmul(X, S["rLo"]))
    dHi = fsub(Y, fmul(X, S["rHi"]))
    if 0 <= dLo[0] and 0 <= dHi[0]:
        return atLo[0]
    if dLo[1] <= 0 and dHi[1] <= 0:
        return atHi[0]
    N = fadd(fmul(X, X), fmul(Y, Y))
    guess = abs(X[0]) + abs(X[1]) + abs(Y[0]) + abs(Y[1]) + 1000000000000
    w = (0, sqrtUp(N, guess))
    return fsub(fmul(S["shift"], fadd(X, Y)), fmul(S["rho"], w))[0]


def xaF(four, k1, flip, sgn, lam):
    if four:
        v = (fneg(lam) if sgn else lam) if k1 else lam
    else:
        v = fneg(lam) if k1 else (fneg(lam) if sgn else lam)
    return fneg(v) if flip else v


def yaF(four, k1, flip, sgn, tau, lam):
    if four:
        v = (lam if tau else fneg(lam)) if k1 else (lam if tau == sgn else fneg(lam))
    else:
        v = (fneg(lam) if tau == sgn else lam) if k1 else (lam if tau else fneg(lam))
    return fneg(v) if flip else v


def atPoint(b0, bT, x0, xa, y0, ya, A, B, xs):
    k0 = fadd(b0, fadd(fmul(x0, A), fmul(y0, B)))
    pa = fadd(bT, fmul(xa, A))
    pb = fadd(bT, fmul(ya, B))
    return (k0, pa, pb) if xs else (k0, pb, pa)


def slope(x0, xa, y0, ya, R, xs, neg):
    k0 = fsub(y0, fmul(x0, R))
    pa = fneg(fmul(xa, R))
    t = (k0, pa, ya) if xs else (k0, ya, pa)
    return tuple(fneg(c) for c in t) if neg else t


def xLin(x0, xa, xs):
    return (x0, xa, ZERO) if xs else (x0, ZERO, xa)


def circleCoeffs(b0, bT, x0, xa, y0, ya, lam, shift_, rho, hn, xs):
    w = scaleDiv(rho, 10000000, 2 * hn)
    rh = scaleDiv(rho, hn, 20000000)
    V0 = fadd(fadd(fmul(x0, x0), fmul(y0, y0)), fmul(lam, lam))
    Va = fadd(fmul(x0, xa), fmul(x0, xa))
    Vb = fadd(fmul(y0, ya), fmul(y0, ya))
    k0 = fadd(b0, fsub(fmul(shift_, fadd(x0, y0)), fadd(fmul(w, V0), rh)))
    pa = fadd(bT, fsub(fmul(shift_, xa), fmul(w, Va)))
    pb = fadd(bT, fsub(fmul(shift_, ya), fmul(w, Vb)))
    return (k0, pa, pb) if xs else (k0, pb, pa)


class Core:
    """The coefficient data of a row's core (coreCheck in RowCheck.lean)."""

    def __init__(self, ctx, x):
        S0, T0 = ctx["boxes"][x["source"]], ctx["boxes"][x["target"]]
        rev = x["axis"] in (2, 3)
        self.four = x["axis"] in (2, 4)
        self.k1 = x["k"] % 2 == 1
        self.flip = x["k"] // 2 == 1
        self.sgn = x["positive"]
        S = reverse(T0) if rev else S0
        T = reverse(S0) if rev else T0
        self.T = T
        self.lam = ofDiv(x["lam"], 100000000)
        lamHalf = ofDiv(x["lam"], 200000000)
        betaHalf, gamma = ctx["betaHalf"][x["edge"]], ctx["gamma"][x["edge"]]
        if self.four:
            X, Y = fsub(S["p"], self.lam), S["q"]
        else:
            X = S["p"]
            Y = fsub(S["q"], self.lam) if S["positive"] else fadd(S["q"], self.lam)
        SL = source_lower(S, X, Y)
        b0 = fsub(fadd(fadd(fadd(fsub(S["c"], T["c"]), lamHalf), betaHalf), point(SL)), gamma)
        k = x["k"]
        self.b0 = fadd(b0, (k * PI_HALF[0], k * PI_HALF[1])) if k != 0 else b0
        self.bT = fsub(lamHalf, betaHalf)
        self.c1 = point(UNIT) if self.sgn else point(-UNIT)
        self.x0, self.y0 = fneg(T["p"]), fneg(T["q"])
        self.xa = xaF(self.four, self.k1, self.flip, self.sgn, self.lam)
        self.ya = yaF(self.four, self.k1, self.flip, self.sgn, T["positive"], self.lam)
        self.xs = self.four == self.k1

    def at(self, A, B):
        return atPoint(self.b0, self.bT, self.x0, self.xa, self.y0, self.ya, A, B, self.xs)

    def slope(self, R, neg):
        return slope(self.x0, self.xa, self.y0, self.ya, R, self.xs, neg)

    def circle(self, hn):
        return circleCoeffs(self.b0, self.bT, self.x0, self.xa, self.y0, self.ya, self.lam,
                            self.T["shift"], self.T["rho"], hn, self.xs)

    def sqrtV(self, u):
        """float sqrt (X^2 + Y^2) at u (only to propose a piece parameter)."""
        m = lambda I: (I[0] + I[1]) / 2 / UNIT
        g, gp = (math.sin(u), math.cos(u)) if self.xs else (math.cos(u), math.sin(u))
        X = m(self.x0) + m(self.xa) * g
        Y = m(self.y0) + m(self.ya) * gp
        return math.sqrt(X * X + Y * Y)


def structural(ctx, x):
    return (x["edge"] < 7 and x["source"] < ctx["n"] and x["target"] < ctx["n"]
            and 1 <= x["axis"] <= 4 and x["k"] <= 3 and x["hi"] <= ctx["den"])


def check_row(ctx, x):
    """checkRow in RowCheck.lean."""
    if not structural(ctx, x):
        return False
    c = Core(ctx, x)
    den, lo, hi, T = ctx["den"], x["lo"], x["hi"], c.T
    m = x["mode"]
    if m == 0:
        return ((T["side"] or nonneg3(den, lo, hi, xLin(c.x0, c.xa, c.xs)))
                and pos3(den, lo, hi, c.c1, c.at(T["aLo"], T["bLo"]))
                and pos3(den, lo, hi, c.c1, c.at(T["aHi"], T["bHi"])))
    if m == 1:
        return (nonneg3(den, lo, hi, c.slope(T["rLo"], False))
                and nonneg3(den, lo, hi, c.slope(T["rHi"], False))
                and pos3(den, lo, hi, c.c1, c.at(T["aLo"], T["bLo"])))
    if m == 2:
        return (nonneg3(den, lo, hi, c.slope(T["rLo"], True))
                and nonneg3(den, lo, hi, c.slope(T["rHi"], True))
                and pos3(den, lo, hi, c.c1, c.at(T["aHi"], T["bHi"])))
    if T["side"] or not x["pieces"]:
        return False
    start = lo
    for hn, upto in x["pieces"]:
        if not (hn > 0 and pos3(den, start, upto, c.c1, c.circle(hn))):
            return False
        start = upto
    return hi <= start


def circle_pieces(ctx, x, maxdepth=16):
    """Pieces (h, upto) for a circle row: the row's own h on the whole interval if it passes,
    otherwise bisection with h = sqrt V at the midpoint of each piece."""
    c = Core(ctx, x)
    den, c1 = ctx["den"], c.c1
    if pos3(den, x["lo"], x["hi"], c1, c.circle(x["h"])):
        return [(x["h"], x["hi"])]
    out = []

    def go(l, h, depth):
        hn = max(1, round(c.sqrtV((l + h) / 2 / den) * H_SCALE))
        if pos3(den, l, h, c1, c.circle(hn)):
            out.append((hn, h))
            return True
        if depth >= maxdepth:
            return False
        m = (l + h) // 2
        return go(l, m, depth + 1) and go(m, h, depth + 1)
    if not go(x["lo"], x["hi"], 0):
        raise SystemExit("circle row without pieces: %r" % x)
    return out


# ----------------------------------------------------------------- coverage (RowCover.lean)

GAP = ofQI(F(19, 25), F(710, 113) - F(114, 25))
PI_BOX = (F(3141592653589793238, 10 ** 18), F(3141592653589793239, 10 ** 18))


def cover_check(t, ctx, rows):
    """For every (source, target, axis, sign) with consecutive roles, an allowed axis and no
    exclusion, the rows of that key, in data order, cover the required angles (integer form over
    unit * den)."""
    den = ctx["den"]
    L = UNIT * den
    keyed = {}
    for i, x in enumerate(rows):
        keyed.setdefault((x["source"], x["target"], x["axis"], x["positive"]), []).append(x)
    bad = 0
    for s, a in enumerate(t.arcs):
        i = a.role
        base = ofQI(*qmul(qpoint(F(t.word[i], 2)), PI_BOX))
        for u, b in enumerate(t.arcs):
            if b.role != (i + 1) % 7:
                continue
            phase = fadd(fsub(GAP, ctx["boxes"][s]["alpha"]), ctx["boxes"][u]["alpha"])
            for ax in t.axes[i]:
                if skipped(a, b, ax):
                    continue
                for r in (True, False):
                    raw = fsub(phase, base) if r else fsub(base, phase)
                    d = t.diff[i] if r else (-t.diff[i][1], -t.diff[i][0])
                    lo = max(raw[0] * den, int(d[0] * L), 0)
                    hi = min(raw[1] * den, int(d[1] * L), 7 * L // 10)
                    if hi < lo:
                        continue
                    cur, ok = lo, False
                    for x in keyed.get((s, u, ax, r), []):
                        if x["edge"] != i or x["k"] != t.word[i] or x["lo"] * UNIT > cur:
                            break
                        if hi <= x["hi"] * UNIT:
                            ok = True
                            break
                        cur = max(cur, x["hi"] * UNIT)
                    bad += not ok
    return bad


# ----------------------------------------------------------------- conversion


def scale_of(t):
    m = 8
    for r in t.rows:
        for k in ("lo", "hi"):
            if "." in r[k]:
                m = max(m, len(r[k].split(".")[1]))
    return 10 ** m


def exact(s, scale):
    q = F(s) * scale
    assert q.denominator == 1, (s, scale)
    return int(q)


MODES = {"endpoints": 0, "lower": 1, "upper": 2, "circle": 3}


# ----------------------------------------------------------------- Lean modules


def state_chains(t, cuts):
    """Per role, closed chains of the non-outer and of the outer arcs over the cut of the role
    (checked by StateChains.NumericValid)."""
    def signed(a):
        return (a.tlo, a.thi) if a.positive else (-a.thi, -a.tlo)

    def closed(lo, hi, ivs):
        if not ivs:
            return hi < lo
        I = ivs[0]
        return I[0] <= lo and (hi <= I[1] or (lo <= I[1] and closed(I[1], hi, ivs[1:])))
    out = []
    for role in range(7):
        per = []
        for outer in (False, True):
            items = sorted(((i, signed(a)) for i, a in enumerate(t.arcs)
                            if a.role == role and a.outer == outer), key=lambda p: p[1])
            lo, hi = cuts[role]
            chain = []
            for i, I in items:
                if hi < lo:
                    break
                if I[1] < lo:
                    continue
                chain.append(i)
                if hi <= I[1]:
                    break
                lo = max(lo, I[1])
            assert closed(cuts[role][0], cuts[role][1], [signed(t.arcs[i]) for i in chain])
            per.append(chain)
        out.append(per)
    return out


def wrap(items, indent, first="", sep=", ", width=100):
    """Join items with sep, breaking lines before width; continuation lines get indent."""
    lines, cur = [], first
    for i, it in enumerate(items):
        piece = it + (sep.rstrip() if i + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = " " * indent
        cur += piece + (" " if i + 1 < len(items) else "")
    lines.append(cur.rstrip())
    return "\n".join(lines)


def lean_q(q):
    q = F(q)
    return str(q.numerator) if q.denominator == 1 else "%d/%d" % (q.numerator, q.denominator)


HEADER = """module

{imports}

/-! {doc} -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.{module}
open Arithmetic

set_option maxRecDepth 100000
"""

FOOTER = """
end SquaresInCircles.Eight.Generated.Affine.{module}
"""

CHUNK, PART = 10000, 200          # rows per module, rows per theorem
BOX_BLOCK = 120                   # arc boxes per theorem
BOX_GROUP = 32                    # arc boxes per group of TableCtx.boxes (RowCheck.boxAt)
COVER_BUDGET, COVER_MODULE = 8000, 12  # combinations plus rows per theorem, theorems per module


def blocks_of(n, size):
    return [(a, min(size, n - a)) for a in range(0, n, size)]


def all_blocks(names, indent=4):
    """the proof of `AllBlocks p blocks` from the theorems `names`"""
    return ("by simp only [AllBlocks]; exact\n" +
            wrap(names + ["trivial"], indent, " " * indent + "⟨") + "⟩")


def right_nested(names, indent):
    """`a ++ (b ++ (c ++ d))`"""
    text = names[-1]
    for nm in reversed(names[:-1]):
        text = nm + " ++ " + ("(" + text + ")" if " ++ " in text else text)
    return wrap(text.split(" "), indent, " " * indent, sep=" ")


def write_meta(root, module, path):
    """MODULE/Meta.lean, the exact data of the table."""
    def q(x):
        f = F(str(x))
        return str(f.numerator) if f.denominator == 1 else "(%d/%d)" % (f.numerator, f.denominator)

    def iv(v):
        return "⟨" + q(v[0]) + "," + q(v[1]) + "⟩"

    def vec(v):
        return "![" + ", ".join(v) + "]"

    axis = [".one", ".two", ".three", ".four"]
    d = json.load(open(path))
    pre = "SquaresInCircles.Eight.Generated.Affine." + module
    lines = ["module", "", "public import SquaresInCircles.Eight.Arithmetic.AffineTableData", "",
             "@[expose] public section", "noncomputable section", "namespace " + pre,
             "open Arithmetic", "", "/-- Complete original arc data; schema eight-affine-v1. -/",
             "noncomputable def table : AffineTableMeta :=", "  { radius := " + q(d["Q"]), "    arcs := ["]
    for a in d["arcs"]:
        lines.append("      ⟨%d,%d,%s,%s,%s,⟨%s⟩⟩," % (
            a["id"], a["role"], str(a["kind"] == "O").lower(), str(a["sign"] == 1).lower(),
            iv([a["lo"], a["hi"]]), ",".join(q(a[k]) for k in ("c", "p", "q"))))
    lines[-1] = lines[-1].removesuffix(",") + "]"
    domains = d.get("axis_domains", {})
    lines += [
        "    cuts := " + vec([iv(d.get("cuts", {}).get(str(i), [-1, 1])) for i in range(7)]),
        "    word := " + vec([str(x) for x in d.get("word", [0, 1, 0, 1, 0, 1, 1])]),
        "    charge := " + vec([q(x) for x in d.get("beta", [0] * 7)]),
        "    target := " + vec([q(x) for x in d["gamma"]]),
        "    differenceRange := " + vec([iv(d.get("difference_ranges", {}).get(
            str(i), ["-7/10", "7/10"])) for i in range(7)]),
        "    allowedAxes := " + vec(["[" + ",".join(axis[int(j) - 1] for j in domains.get(
            str(i), [1, 2, 3, 4])) + "]" for i in range(7)]) + " }", ""]
    lines += ["end " + pre, ""]
    base = root / "SquaresInCircles" / "Eight" / "Generated" / "Affine"
    (base / module).mkdir(parents=True, exist_ok=True)
    (base / module / "Meta.lean").write_text("\n".join(lines))


def write_index(root, module, src, files, rows, arcs):
    """Record the provenance of the data files of a table and their hashes in
    Generated/Affine/generation_index.json: Lake does not track the data files."""
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def rel(path):
        path = path.resolve()
        return str(path.relative_to(root)) if path.is_relative_to(root) else str(path)

    path = root / "SquaresInCircles" / "Eight" / "Generated" / "Affine" / "generation_index.json"
    entry = {"module": module, "input": src.name, "sha256": sha(src), "rows": rows, "arcs": arcs,
             "data": [{"file": rel(f), "sha256": sha(f)} for f in files]}
    with open(path, "a+") as f:   # locked: tables may be converted in parallel
        fcntl.flock(f, fcntl.LOCK_EX)
        f.seek(0)
        text = f.read()
        index = json.loads(text) if text else {}
        if index.get("schema") != "eight-affine-rows-v1":
            index = {"schema": "eight-affine-rows-v1",
                     "source": "the JSON of each table, converted by scripts/eight/affine_rows.py",
                     "tables": []}
        tables = [e for e in index["tables"] if e["module"] != module] + [entry]
        index["tables"] = sorted(tables, key=lambda e: e["module"])
        f.seek(0)
        f.truncate()
        f.write(json.dumps(index, indent=2) + "\n")


def write_modules(root, module, name, t, cuts, ctx, rows, enhance):
    base = root / "SquaresInCircles" / "Eight" / "Generated" / "Affine"
    (base / module).mkdir(parents=True, exist_ok=True)
    for old in list((base / module).glob("Rows*.lean")) + list((base / module).glob("Atan*.lean")) \
            + list((base / module).glob("Cover[0-9]*.lean")):
        old.unlink()
    rel = "../../../../../data/eight/affine/" + name
    den, n = ctx["den"], ctx["n"]
    core = "false" if CORE is None else "true"
    L = UNIT * den
    pre = "SquaresInCircles.Eight.Generated.Affine." + module
    meta = "enhancedMeta" if enhance else "table"
    fi = lambda I: "⟨%d, %d⟩" % I
    # ------------------------------------------------------------ Context
    gap = ofQI(F(19, 25), F(710, 113) - F(114, 25))
    bases = [ofQI(*qmul(qpoint(F(w, 2)), PI_BOX)) for w in t.word]
    dlo = [int(d[0] * L) for d in t.diff]
    dhi = [int(d[1] * L) for d in t.diff]
    assert all(d[0] * L == x for d, x in zip(t.diff, dlo))
    assert all(d[1] * L == x for d, x in zip(t.diff, dhi))
    chains = state_chains(t, cuts)
    lines = []
    for r, per in enumerate(chains):
        for j, c in enumerate(per):
            first = ("  [[[" if r == 0 else "   [[") if j == 0 else "    ["
            last = j == len(per) - 1
            close = "]" + ("]" if last else "") + ("]" if last and r == len(chains) - 1 else ",")
            lines.append(wrap([str(v) for v in c], len(first), first, width=96) + close)
    states = "\n".join(lines)
    boxes = blocks_of(n, BOX_BLOCK)
    text = HEADER.format(
        imports="public import %s.Meta\npublic import SquaresInCircles.Eight.Arithmetic.RowCover\n"
                "public meta import SquaresInCircles.Eight.IntRows" % pre,
        doc="The fixed-point data of the table, checked against the exact data of `Meta`: the\n"
            "arc boxes and the arctangent intervals of the arcs (in blocks), the scalars, the\n"
            "state chains and the data of the angle coverage.",
        module=module)
    if enhance:
        text += f"""
/-- The margins added to the targets. -/
noncomputable def enhancement (i : Fin 7) : ℚ := (![{",".join(map(str, enhance))}] i) / 10^6

theorem enhancement_nonneg : ∀ i, 0 ≤ enhancement i := by decide +kernel

/-- The table with the enhanced targets; the rows are checked against these. -/
noncomputable def enhancedMeta : AffineTableMeta :=
  {{table with target := fun i => table.target i + enhancement i}}
"""
    groups = ",\n     ".join(
        f'int_rows% "{rel}.arcs" {8 + g} {8 + min(g + BOX_GROUP, n)} ↦\n        ArcBox.ofData'
        for g in range(0, n, BOX_GROUP))
    text += f"""
noncomputable def ctx : TableCtx :=
  ⟨{den}, {n},
    [{groups}],
    int_rows% "{rel}.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "{rel}.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars {meta} = true := by decide +kernel
"""
    for j, (a, c) in enumerate(boxes):
        text += f"""
theorem ctx_boxes_{j} :
    boxesRange {meta}.radius {meta}.arcs ctx.boxes {a} {c} = true := by
  decide +kernel
"""
    text += f"""
theorem ctx_valid : ctx.Valid {meta} :=
  TableCtx.valid_of ctx_scalars (blocks := {list(boxes)}) (by decide +kernel)
    ({all_blocks(["ctx_boxes_%d" % j for j in range(len(boxes))], 6)})

/-- Per role, the state chains of the non-outer and of the outer arcs. -/
noncomputable def stateData : List (List (List ℕ)) :=
{states}

noncomputable def cover : AffineCover := ⟨atanEnds table, chainsOf stateData⟩

theorem cover_states : cover.states.NumericValid table := by decide +kernel

noncomputable def coverCtx : CoverCtx :=
  ⟨ctx.den, {fi(gap)},
{wrap([fi(b) for b in bases], 5, "    [")}],
{wrap([str(x) for x in dlo], 5, "    [")}],
{wrap([str(x) for x in dhi], 5, "    [")}],
    int_rows% "{rel}.arcs" 8 {8 + n} ↦
      alphaOfData⟩

theorem coverCtx_scalars : coverCtx.checkScalars table = true := by decide +kernel
"""
    for j, (a, c) in enumerate(boxes):
        text += f"""
theorem coverCtx_alphas_{j} : alphasRange table.arcs coverCtx.alphas {a} {c} = true := by
  decide +kernel
"""
    blocks_text = wrap([str(b) for b in boxes], 5, "    [") + "]"
    text += f"""
/-- The fixed-point arctangent intervals of `coverCtx` enclose those of the arcs. -/
theorem coverCtx_alphas :
    AllBlocks (fun a c => alphasRange table.arcs coverCtx.alphas a c = true)
{blocks_text} :=
  {all_blocks(["coverCtx_alphas_%d" % j for j in range(len(boxes))])}

theorem coverCtx_valid :
    coverCtx.Valid cover table ∧ coverCtx.alphas.length = table.arcs.length :=
  CoverCtx.valid_of coverCtx_scalars (by decide +kernel) coverCtx_alphas
"""
    text += FOOTER.format(module=module)
    (base / module / "Context.lean").write_text(text)
    # ------------------------------------------------------------ rows
    nrows = len(rows)
    modules = []
    for c, start in enumerate(range(0, nrows, CHUNK)):
        count = min(CHUNK, nrows - start)
        parts = []
        text = HEADER.format(
            imports="public import %s.Context\n"
                    "public meta import SquaresInCircles.Eight.IntRows" % pre,
            doc="Rows %d to %d of the table, checked by `decide +kernel`, %d rows a theorem."
                % (start, start + count - 1, PART), module=module)
        for k, s0 in enumerate(range(start, start + count, PART)):
            m = min(PART, start + count - s0)
            nm = "rows%03d_%d" % (c, k)
            parts.append(nm)
            text += f"""
noncomputable def {nm} : List AffineRow :=
  nat_rows% "{rel}.rows" {1 + s0} {1 + s0 + m} ↦
    AffineRow.ofData

theorem {nm}_check : checkRows ctx {nm} = true := by decide +kernel
"""
        pn = "parts%03d" % c
        modules.append(pn)
        simps = wrap([pn, "List.all_cons", "List.all_nil"] + [q + "_check" for q in parts] +
                     ["Bool.and_true"], 4, "  simp only [")
        text += f"""
/-- Rows {start} to {start + count - 1}, in parts of {PART}. -/
noncomputable def {pn} : List (List AffineRow) :=
{wrap(parts, 3, "  [")}]

theorem {pn}_check : {pn}.all (checkRows ctx) = true := by
{simps}]
"""
        text += FOOTER.format(module=module)
        (base / module / ("Rows%03d.lean" % c)).write_text(text)
    # ------------------------------------------------------------ all rows
    imports = "\n".join("public import %s.Rows%03d" % (pre, c) for c in range(len(modules)))
    text = HEADER.format(imports=imports, doc="All rows of the table.", module=module)
    text += f"""
/-- The rows in parts of {PART}, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
{right_nested(modules, 2)}

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
{wrap(["data", "chunks", "checkRows_flatten", "List.all_append"] +
      [c + "_check" for c in modules] + ["Bool.and_true"], 4, "  simp only [")}]
"""
    text += FOOTER.format(module=module)
    (base / module / "Data.lean").write_text(text)
    # ------------------------------------------------------------ coverage blocks
    first = {}
    count_by_source = [0] * n
    for idx, x in enumerate(rows):
        first.setdefault(x["source"], idx)
        count_by_source[x["source"]] += 1
    cost = [2 * sum(1 for b in t.arcs if b.role == (a.role + 1) % 7
                    for ax in t.axes[a.role] if not skipped(a, b, ax)) + count_by_source[s]
            for s, a in enumerate(t.arcs)]
    assert CHUNK % PART == 0
    cover = []
    s0 = 0
    while s0 < n:
        s1, acc = s0, 0
        while s1 < n and (s1 == s0 or acc + cost[s1] <= COVER_BUDGET):
            acc += cost[s1]
            s1 += 1
        k = first.get(s0, next((first[s] for s in range(s0, n) if s in first), nrows))
        cover.append((s0, s1 - s0, k // PART, k % PART))
        s0 = s1
    cover_modules = []
    for m in range(0, len(cover), COVER_MODULE):
        mod = "Cover%02d" % (m // COVER_MODULE)
        cover_modules.append(mod)
        part = cover[m:m + COVER_MODULE]
        text = HEADER.format(
            imports="public import %s.Data" % pre,
            doc="The angle coverage for the source arcs %d to %d, checked by `decide +kernel`."
                % (part[0][0], part[-1][0] + part[-1][1] - 1), module=module)
        for j, (a, c, ck, o) in enumerate(part):
            text += f"""
theorem cover_{m + j} : coverBlock coverCtx table {core} {a} {c} {ck} {o} chunks = true := by
  decide +kernel
"""
        text += FOOTER.format(module=module)
        (base / module / (mod + ".lean")).write_text(text)
    # ------------------------------------------------------------ the table
    imports = "\n".join(["public import %s.Data" % pre] +
                        ["public import %s.%s" % (pre, mod) for mod in cover_modules] +
                        (["public import SquaresInCircles.Eight.Candidate.GeometricCoreMarker"]
                         if CORE == "markers" else []))
    core_bound = "(by simp)"
    core_theorems = ""
    core_hyp = ""
    if CORE == "free":
        core_bound = "(fun _ => hC.corePairBound F)"
        core_hyp = "\n    (hC : NoAdjacentCore C)"
    if CORE == "markers":
        core_bound = ("(fun _ => Candidate.GeometricCoreMarker.pair_bound cover_endpoints markers_valid\n"
                      "      budgets_valid C F)")
        core_theorems = """
theorem markers_valid : Candidate.GeometricCoreMarker.MarkersValid cover table := by
  decide +kernel

theorem budgets_valid : Candidate.GeometricCoreMarker.BudgetsValid table := by decide +kernel

theorem strong_budgets_valid :
    Candidate.GeometricCoreMarker.BudgetsValid {table with target := fun _ => 9/10} := by
  decide +kernel
"""
    claim = "checkRow_claim ctx_valid (checkRows_sound data_check x hx)"
    if enhance:
        claim = ("AffineRow.claim_of_target_le (le_add_of_nonneg_right (enhancement_nonneg _))\n"
                 "    (checkRow_claim ctx_valid (checkRows_sound data_check x hx))")
    text = HEADER.format(
        imports=imports,
        doc=f"# The affine table `{module}`\n\n"
            f"Each of its {nrows} rows passes `checkRow`, so it satisfies its claim\n"
            "(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs\n"
            "give the angle coverage (`coverBlocks_sound`). With the state chains and the\n"
            "arctangent intervals of the arcs they give the charged bound.",
        module=module)
    text += f"""
/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact {claim}

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table {core} a n c o chunks = true)
{wrap([str((a, c)) for a, c, _, _ in cover], 5, "    [")}] :=
  {all_blocks(["⟨%d, %d, cover_%d⟩" % (ck, o, j) for j, (a, c, ck, o) in enumerate(cover)])}

theorem cover_angles : cover.AngleCovers table rows {core} :=
  coverBlocks_sound coverCtx_valid.1 coverCtx_valid.2 (by decide +kernel) cover_blocks
{core_theorems}
theorem word_matches : ∀ i, (table.word i:ℝ)=(Candidate.word i:ℝ) := by
  have hw : table.word = ![{", ".join(map(str, t.word))}] := rfl
  intro i; rw [hw]; fin_cases i <;> norm_num [Candidate.word]

noncomputable def charged_bound (C : BoundaryCycle (table.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i){core_hyp} :
    Candidate.ChargedBound C F β (fun i => (table.target i:ℝ)) :=
  AffineCover.chargedBoundOf cover_endpoints cover_states cover_angles all_row_claims C F β
    word_matches hcharge hcuts hdiff haxes {core_bound}
"""
    if CORE == "markers":
        text += """
/-- No edge of a cycle with the cuts of the table joins two core squares. -/
theorem no_adjacent_core (C : BoundaryCycle (table.radius:ℝ)) (F : Candidate.Frame C) (β : ℝ)
    (hβ : 0 ≤ β) (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i) : NoAdjacentCore C :=
  Candidate.GeometricCoreMarker.no_adjacent_core cover_endpoints cover_states cover_angles
    all_row_claims markers_valid budgets_valid strong_budgets_valid (by decide +kernel)
    (by decide +kernel) C F β hβ word_matches hcharge hcuts hdiff haxes
"""
    text += FOOTER.format(module=module)
    (base / (module + ".lean")).write_text(text)
    # ------------------------------------------------------------ the enhanced targets
    if enhance:
        text = HEADER.format(
            imports="public import %s" % pre,
            doc="The same rows and coverage for the enhanced targets: the rows were checked\n"
                "against them, and the coverage walk does not involve the targets.",
            module=module)
        enhanced_bound = "(by simp)"
        enhanced_theorems = ""
        if CORE == "markers":
            enhanced_bound = ("(fun _ => Candidate.GeometricCoreMarker.pair_bound enhanced_endpoints\n"
                              "      enhanced_markers_valid enhanced_budgets_valid C F)")
            enhanced_theorems = """
theorem enhanced_markers_valid :
    Candidate.GeometricCoreMarker.MarkersValid enhancedCover enhancedMeta := by
  decide +kernel

theorem enhanced_budgets_valid : Candidate.GeometricCoreMarker.BudgetsValid enhancedMeta := by
  decide +kernel
"""
        text += """
/-- All rows of the table, with the enhanced targets. -/
noncomputable def enhancedRows : List AffineTableRow := data.map (·.toTableRow enhancedMeta ctx.den)

theorem enhanced_claims : ∀ r ∈ enhancedRows, r.Claim enhancedMeta := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

noncomputable def enhancedCover : AffineCover := ⟨atanEnds enhancedMeta, chainsOf stateData⟩

theorem enhanced_endpoints : enhancedCover.EndpointsValid enhancedMeta :=
  endpointsValid_atanEnds enhancedMeta _

theorem enhanced_states : enhancedCover.states.NumericValid enhancedMeta := by decide +kernel

theorem enhanced_coverCtx_valid : coverCtx.Valid enhancedCover enhancedMeta ∧
    coverCtx.alphas.length = enhancedMeta.arcs.length :=
  CoverCtx.valid_of (by decide +kernel) (by decide +kernel) coverCtx_alphas

theorem enhanced_angles : enhancedCover.AngleCovers enhancedMeta enhancedRows """ + core + """ :=
  coverBlocks_sound enhanced_coverCtx_valid.1 enhanced_coverCtx_valid.2 (by decide +kernel)
    (AllBlocks.imp (fun a n ⟨c, o, h⟩ =>
      ⟨c, o, (coverBlock_congr rfl rfl rfl _ a n c o chunks).trans h⟩) cover_blocks)
""" + enhanced_theorems + """
noncomputable def enhanced_charged_bound (C : BoundaryCycle (table.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (enhancedMeta.target i:ℝ)) :=
  AffineCover.chargedBoundOf enhanced_endpoints enhanced_states enhanced_angles enhanced_claims
    C F β word_matches hcharge hcuts hdiff haxes """ + enhanced_bound + """
"""
        text += FOOTER.format(module=module)
        (base / module / "Enhanced.lean").write_text(text)
    return dict(rows=len(modules), cover=len(cover_modules), cover_blocks=len(cover),
                box_blocks=len(boxes))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", type=Path)
    root = Path(__file__).resolve().parents[2]
    ap.add_argument("--out", type=Path, default=root / "data" / "eight" / "affine")
    ap.add_argument("--lean", metavar="MODULE")
    ap.add_argument("--enhance", help="millionths added to the seven targets, e.g. 15,13,...")
    ap.add_argument("--core", choices=["markers", "free"],
                    help="leave out the rows of two core arcs: bounded by the markers, or absent")
    args = ap.parse_args()
    global CORE
    CORE = args.core
    args.table = args.json.stem
    t = load_table(args.json)
    enhance = [int(v) for v in args.enhance.split(",")] if args.enhance else None
    targets = [g + F(e, 10 ** 6) for g, e in zip(t.gamma, enhance)] if enhance else t.gamma
    den = scale_of(t)
    ctx = dict(den=den, n=len(t.arcs), boxes=[make_box(a, t.Q) for a in t.arcs],
               betaHalf=[ofQ(b / 2) for b in t.beta], gamma=[ofQ(g) for g in targets])
    rows = []
    for r in t.rows:
        rows.append(dict(edge=r["edge"], source=t.index[r["source"]], target=t.index[r["target"]],
                         axis=r["axis"], k=r["k"], positive=r["r"] == 1,
                         lo=exact(r["lo"], den), hi=exact(r["hi"], den),
                         lam=exact(r["lambda"], LAM_SCALE), mode=MODES[r["mode"]],
                         h=exact(r.get("h", "1"), H_SCALE), pieces=[]))
    total = len(rows)
    rows = [x for x in rows if not skipped(t.arcs[x["source"]], t.arcs[x["target"]], x["axis"])]
    rows.sort(key=lambda x: (x["source"], x["target"], x["axis"], not x["positive"],
                             x["lo"], x["hi"]))
    pieces = 0
    for x in rows:
        if x["mode"] == 3:
            x["pieces"] = circle_pieces(ctx, x)
            pieces += len(x["pieces"])
        if not check_row(ctx, x):
            raise SystemExit("row fails the check: %r" % x)
    bad = cover_check(t, ctx, rows)
    if bad:
        raise SystemExit("%d uncovered angle intervals" % bad)
    args.out.mkdir(parents=True, exist_ok=True)
    with open(args.out / (args.table + ".rows"), "w") as f:
        f.write("%d %d\n" % (den, len(rows)))
        for x in rows:
            v = [x["edge"], x["source"], x["target"], x["axis"], x["k"], int(x["positive"]),
                 x["lo"], x["hi"], x["lam"], x["mode"]]
            if x["mode"] == 3:
                for j, (hn, upto) in enumerate(x["pieces"]):
                    v.append(hn)
                    if j + 1 < len(x["pieces"]):
                        v.append(upto)
            f.write(" ".join(map(str, v)) + "\n")
    with open(args.out / (args.table + ".arcs"), "w") as f:
        f.write("%d %d\n" % (den, len(t.arcs)))
        for b, g in zip(ctx["betaHalf"], ctx["gamma"]):
            f.write("%d %d %d %d\n" % (b + g))
        for b in ctx["boxes"]:
            v = [int(b["side"]), int(b["positive"])]
            for k in ("c", "p", "q", "shift", "rho", "aLo", "bLo", "aHi", "bHi", "rLo", "rHi",
                      "alpha"):
                v += list(b[k])
            f.write(" ".join(map(str, v)) + "\n")
    print("%s: %d of %d rows kept (%d circle pieces), %d arcs, den %d, coverage ok" %
          (args.table, len(rows), total, pieces, len(t.arcs), den))
    if args.lean:
        cuts = [tuple(F(v) for v in json.load(open(args.json)).get("cuts", {}).get(str(i), [-1, 1]))
                for i in range(7)]
        write_meta(root, args.lean, args.json)
        info = write_modules(root, args.lean, args.table, t, cuts, ctx, rows, enhance)
        write_index(root, args.lean, args.json,
                    [args.out / (args.table + ext) for ext in (".rows", ".arcs")],
                    len(rows), len(t.arcs))
        print("%s: modules %s" % (args.lean, info))


if __name__ == "__main__":
    main()

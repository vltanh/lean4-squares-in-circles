#!/usr/bin/env python3
"""Generate the pair tables of the n = 8 proof: affine rows with coverage trees.

Two families of finite inequalities are proved by the rows of Arithmetic/RowCheck.lean and the
coverage trees of Arithmetic/PairCover.lean:

* the four-type pair bounds `FourType.source_pair` (FourTypePairs.lean): 21 tables, one per
  ordered pair of charts (core side, core corner and the outer ranges low, middle, high) with an
  outer chart, each with the eight problems (σ, τ, axis one or four) on six halves (k, r, u⁺)
  of φ ∈ [-1, 4]; a pair of two core charts follows from `CorePairGeometry.core_cost`;
* the quarter-word pair bounds `common_pair` and `wrong_pair` (WordGeometry.lean): three tables
  of the common increments (quarter k = 0, 1, 2) for the pairs of kinds with an outer kind (a pair
  of two core kinds follows from `CorePairGeometry.core_cost`), and one table per edge of each
  of the two wrong words, each problem on the halves (k, ±, 7/10) of the frame difference; the
  kinds, signs and axes that no feasible separator has (`CoreSeparatorExcluded`) are left out.

A problem fixes the source and target ends (chart, tangent range, sign, label), the original
axis, the charge β and the target γ. A table module does not write its problems out: it maps the
statement's own problem function (`fourTypeProblem`, `commonPairProblem`, `wrongPairProblem`)
over the cases of the table (`fourTypeCases`, `commonCases k`, `wrongCases w i`), in the order
and with the filters of `tables()` below, so that the proofs find each problem in its table
without comparing rationals. The labels are read from the Lean sources. A label constant
with √(Q - 1/4), √(Q/2) or π carries a rational bracket; the quadratic labels of the word
0011011 are bounded on each arc by an affine label (Arithmetic/LabelRelax.lean): below for a
source arc, above for a target arc.

The box (source tangent) × (target tangent) × (angle u) of each half is subdivided adaptively.
A cell is closed by the gap, when the angles it allows (integer arctangent bounds,
Arithmetic/AtanBounds.lean) are empty or a proper subinterval (a trim), or by a row: a
multiplier λ from a float Lagrangian search, a target support mode, and the exact integer tests
of RowCheck (`affine_rows.check_row`). Before anything is written, every row, every arc label
and every tree is checked again with the integer algorithms of the Lean checks.

For each table NAME it writes
  data/eight/pairs/NAME.rows   the rows, in the order the trees consume them (affine_rows format)
  data/eight/pairs/NAME.arcs   the arc boxes (affine_rows format; the arctangent field is unused)
  data/eight/pairs/NAME.trees  one tree per problem half, in prefix order (PairData.lean)
and the modules SquaresInCircles/Eight/Generated/Pairs/MODULE{.lean,/Data.lean,/RowsNNN.lean}.

  python3 -I scripts/eight/pair_tables.py [--jobs N] [--only NAME ...] [--no-write]
"""
import argparse
import math
import multiprocessing as mp
import re
import sys
import textwrap
import time
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import affine_rows as ar  # noqa: E402

EIGHT = ROOT / "SquaresInCircles" / "Eight"
UNIT = ar.UNIT
DEN = 10 ** 8                  # angles over DEN
LAM_SCALE = ar.LAM_SCALE       # multipliers over 10^8
H_SCALE = ar.H_SCALE           # circle parameters over 10^7
GRID = 10 ** 15                # relaxed labels on this grid

# ----------------------------------------------------------------- the Lean sources


def lean_text(rel):
    return (EIGHT / rel).read_text()


def parse_array(text, name):
    m = re.search(r"def %s : [^\n]*\n\s*(!\[.*?\])\n" % name, text, re.S)
    assert m, name
    return eval(m.group(1).replace("![", "["), {"__builtins__": {}})


def require(text, *pieces):
    for p in pieces:
        assert p in text, "the Lean source no longer contains %r" % p


MODEL = lean_text("Model.lean")
require(MODEL, "def Q0 : ℝ := 9789 / 2500")
Q = F(9789, 2500)

FRAMES = lean_text("Frames.lean")
HAND_GAMMA = parse_array(FRAMES, "handGammaNumerator")

FOUR = lean_text("Arithmetic/FourTypePairs.lean")
require(FOUR,
        "| .coreSide | .coreCorner => (7506931/1000000)*(7/12-a)+(269343/250000)*b",
        "| .low => (3231/8000)*(a-a0)+(217813/200000)*b",
        "| .middle => -85723/40000+(1489593/1000000)*a+(1580219/1000000)*b",
        "| .high => Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)",
        "noncomputable def a0 : ℝ := Real.sqrt (Q0-1/4)-1/2",
        "noncomputable def c0 : ℝ := Real.sqrt (Q0/2)-1/2")

WORDS = lean_text("Arithmetic/WordProblems.lean")
SHORT = parse_array(WORDS, "shortCoefficients")
SECOND = parse_array(WORDS, "secondCoefficients")
require(WORDS, "def commonGamma (k : Fin 3) : ℚ := ![391/400,157/200,163/200] k",
        "if w=.short ∧ i=2 then 359/400 else 17953/20000",
        "| .short => ![0,0,1,0,1,1,1]", "| .second => ![0,0,1,1,0,1,1]")
require(WORDS, "(k=0 ∧ ((j=1 ∧ kt≠.outer) ∨ (j=3 ∧ ks≠.outer))) ∨",
        "(j=0 ∧ σ=false ∧ kt≠.outer) ∨ (j=2 ∧ τ=true ∧ ks≠.outer) ∨",
        "(k=1 ∧ ks≠.outer ∧ kt≠.outer ∧ σ=true ∧ τ=false)",
        "(i=0→σ=true) ∧ (i=2→σ=false) ∧", "(next i=0→τ=true) ∧ (next i=2→τ=false) ∧",
        "(wrongWord w i=0→¬(σ=false ∧ τ=true))",
        "def wordCases : List (RadialKind × RadialKind × Bool × Bool × Fin 4) :=\n"
        "  [.outer, .coreSide, .coreCorner] ×ˢ [.outer, .coreSide, .coreCorner] ×ˢ [false, true] ×ˢ\n"
        "    [false, true] ×ˢ [0, 1, 2, 3]",
        "wordCases.filter fun c => decide ((c.1 = .outer ∨ c.2.1 = .outer) ∧\n"
        "    ¬ CoreSeparatorExcluded k c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)",
        "wordCases.filter fun c => decide (allowed w i c.2.2.1 c.2.2.2.1 ∧\n"
        "    ¬ CoreSeparatorExcluded (wrongWord w i) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)")
COMMON_GAMMA = [F(391, 400), F(157, 200), F(163, 200)]
WORD = {"short": [0, 0, 1, 0, 1, 1, 1], "second": [0, 0, 1, 1, 0, 1, 1]}

FOUR_PROBLEMS = lean_text("Arithmetic/FourTypeProblems.lean")
require(FOUR_PROBLEMS, "def fourTypeCases : List (Bool × Bool × Bool) :=\n"
        "  [false, true] ×ˢ [false, true] ×ˢ [false, true]")

GEOM = lean_text("WordGeometry.lean")
require(GEOM, "(if kind=.outer then -9/100+(13/200)*a+(203/200)*b",
        "else (73/10)*(7/12-a)+(291/250)*b)")

# ----------------------------------------------------------------- label constants

PI_LO = F(3141592653589793238, 10 ** 18)
PI_HI = F(3141592653589793239, 10 ** 18)
ROOT_DIGITS = 10 ** 20


def sqrt_bracket(x):
    """[s, s + 10^-20] with s on the 10^-20 grid and s² ≤ x ≤ (s + 10^-20)²."""
    s = math.isqrt(x.numerator * ROOT_DIGITS ** 2 // x.denominator)
    lo, hi = F(s, ROOT_DIGITS), F(s + 1, ROOT_DIGITS)
    assert lo * lo <= x <= hi * hi
    return lo, hi


A0_ROOT = sqrt_bracket(Q - F(1, 4))     # a0 = √(Q - 1/4) - 1/2
C0_ROOT = sqrt_bracket(Q / 2)           # c0 = √(Q/2) - 1/2


class Quad:
    """QuadLabel: c + p a + q b + r b² + s a b with c ∈ [cLo, cHi]."""
    __slots__ = ("cLo", "cHi", "p", "q", "r", "s")

    def __init__(self, cLo, cHi, p, q, r=0, s=0):
        self.cLo, self.cHi, self.p, self.q, self.r, self.s = map(F, (cLo, cHi, p, q, r, s))

    def key(self):
        return (self.cLo, self.cHi, self.p, self.q, self.r, self.s)

    def neg(self):
        return Quad(-self.cHi, -self.cLo, -self.p, -self.q, -self.r, -self.s)

    def scale(self, sig):
        return self if sig == 1 else self.neg()

    def __eq__(self, o):
        return self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def floats(self):
        return [float(x) for x in self.key()]


def four_type_label(branch):
    """the positive label of a branch of FourTypePairs.label"""
    if branch in ("coreSide", "coreCorner"):
        k = F(7506931, 1000000)
        return Quad(k * F(7, 12), k * F(7, 12), -k, F(269343, 250000))
    if branch == "low":       # (3231/8000)(a - a0) + (217813/200000) b
        m = F(3231, 8000)
        return Quad(-m * (A0_ROOT[1] - F(1, 2)), -m * (A0_ROOT[0] - F(1, 2)), m,
                    F(217813, 200000))
    if branch == "middle":
        return Quad(F(-85723, 40000), F(-85723, 40000), F(1489593, 1000000),
                    F(1580219, 1000000))
    if branch == "high":      # π/4 + (8898/15625 - 195443/500000) c0 - (8898/15625) a + ...
        m = F(8898, 15625) - F(195443, 500000)
        return Quad(PI_LO / 4 + m * (C0_ROOT[0] - F(1, 2)), PI_HI / 4 + m * (C0_ROOT[1] - F(1, 2)),
                    -F(8898, 15625), F(195443, 500000))
    raise ValueError(branch)


def common_label(kind):
    if kind == "outer":
        return Quad(F(-9, 100), F(-9, 100), F(13, 200), F(203, 200))
    k = F(73, 10)
    return Quad(k * F(7, 12), k * F(7, 12), -k, F(291, 250))


def wrong_label(w, i, kind, sig):
    v = (SHORT if w == "short" else SECOND)[i][0 if kind == "outer" else 1][1 if sig == 1 else 0]
    if w == "short":       # v0 + v1 a + σ v2 b
        return Quad(F(v[0], 100000), F(v[0], 100000), F(v[1], 100000), sig * F(v[2], 100000))
    return Quad(F(v[0], 100000), F(v[0], 100000), F(v[1], 100000), F(v[2], 100000),
                F(v[3], 100000), F(v[4], 100000)).scale(sig)


# ----------------------------------------------------------------- problems and tables

CHART_OF_BRANCH = {"coreSide": ("side", F(0), F(6, 7)), "coreCorner": ("corner", F(6, 7), F(1)),
                   "low": ("outer", F(0), F(1, 4)), "middle": ("outer", F(1, 4), F(3, 7)),
                   "high": ("outer", F(3, 7), F(1))}
CHART_OF_KIND = {"outer": ("outer", F(0), F(1)), "coreSide": ("side", F(0), F(6, 7)),
                 "coreCorner": ("corner", F(6, 7), F(1))}
TYPE_OF_BRANCH = {"coreSide": 0, "coreCorner": 0, "low": 1, "middle": 2, "high": 3}
BRANCHES = ["coreSide", "coreCorner", "low", "middle", "high"]
KINDS = ["outer", "coreSide", "coreCorner"]
FOUR_HALVES = [(0, False, DEN), (0, True, 4 * DEN // 5), (1, False, 4 * DEN // 5),
               (1, True, 4 * DEN // 5), (2, False, 4 * DEN // 5), (2, True, 86 * DEN // 100)]


class End:
    """PairEnd: chart, tangent range, sign, label, and the role of its arcs."""

    def __init__(self, chart, lo, hi, positive, label, role):
        self.chart, self.lo, self.hi, self.positive, self.label, self.role = \
            chart, lo, hi, positive, label, role

    @property
    def sig(self):
        return 1 if self.positive else -1


class Problem:
    def __init__(self, name, src, tgt, axis, beta, gamma, halves):
        self.name, self.src, self.tgt, self.axis = name, src, tgt, axis
        self.beta, self.gamma, self.halves = F(beta), F(gamma), halves


class Table:
    """A table; `lean` = (the module of its problem function, the docstring and the Lean term of
    its problems: the problem function mapped over its cases, in the order of `problems`)."""

    def __init__(self, name, module, edge, beta, gamma, problems, lean):
        self.name, self.module, self.edge = name, module, edge
        self.beta, self.gamma, self.problems = F(beta), F(gamma), problems
        self.lean = lean


def camel(s):
    return s[0].upper() + s[1:]


# The modules of the problem functions and case lists, and the fields (ks, kt, σ, τ, j) of a case
# of a word table (FourTypeProblems.lean, WordProblems.lean).
FOUR_MODULE = "SquaresInCircles.Eight.Arithmetic.FourTypeProblems"
WORDS_MODULE = "SquaresInCircles.Eight.Arithmetic.WordProblems"
CASE_FIELDS = "c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2"


def core_separator_excluded(k, sk, tk, p, r, ax):
    """WordProblems.CoreSeparatorExcluded (the axis numbered 1 to 4): the kinds, signs and axes
    that no feasible separator has (WordGeometry.original_not_core_excluded)."""
    return ((k == 0 and ((ax == 2 and tk != "outer") or (ax == 4 and sk != "outer")))
            or (ax == 1 and not p and tk != "outer") or (ax == 3 and r and sk != "outer")
            or (k == 1 and sk != "outer" and tk != "outer" and p and not r))


def tables():
    out = []
    for s in BRANCHES:
        for t in BRANCHES:
            if TYPE_OF_BRANCH[s] == 0 and TYPE_OF_BRANCH[t] == 0:
                continue
            probs = []
            for p in (False, True):
                for r in (False, True):
                    for four in (False, True):
                        sig, tau = (1 if p else -1), (1 if r else -1)
                        src = End(*CHART_OF_BRANCH[s], p, four_type_label(s).scale(sig), 0)
                        tgt = End(*CHART_OF_BRANCH[t], r, four_type_label(t).scale(tau), 1)
                        probs.append(Problem("%s_%s_%d%d_%s" % (s, t, p, r, "four" if four else "one"),
                                             src, tgt, 4 if four else 1, F(9, 50),
                                             F(HAND_GAMMA[TYPE_OF_BRANCH[s]][TYPE_OF_BRANCH[t]], 10000),
                                             FOUR_HALVES))
            name = "four_type_%s_%s" % (re.sub(r"([A-Z])", r"_\1", s).lower(),
                                         re.sub(r"([A-Z])", r"_\1", t).lower())
            lean = (FOUR_MODULE,
                    "`fourTypeProblem .%s .%s σ τ four` for the cases\n`(σ, τ, four)` of "
                    "`fourTypeCases`" % (s, t),
                    "FourType.fourTypeCases.map fun c =>\n"
                    "    FourType.fourTypeProblem .%s .%s c.1 c.2.1 c.2.2" % (s, t))
            out.append(Table(name, "FourType" + camel(s) + camel(t), 0, F(9, 50), probs[0].gamma,
                             probs, lean))
    seven = 7 * DEN // 10
    for k in range(3):
        probs = []
        for sk in KINDS:
            for tk in KINDS:
                if sk != "outer" and tk != "outer":
                    continue
                for p in (False, True):
                    for r in (False, True):
                        for ax in (1, 2, 3, 4):
                            if core_separator_excluded(k, sk, tk, p, r, ax):
                                continue
                            sig, tau = (1 if p else -1), (1 if r else -1)
                            src = End(*CHART_OF_KIND[sk], p, common_label(sk).scale(sig), 0)
                            tgt = End(*CHART_OF_KIND[tk], r, common_label(tk).scale(tau), 1)
                            probs.append(Problem("common_%d_%s_%s_%d%d_%d" % (k, sk, tk, p, r, ax),
                                                 src, tgt, ax, 0, COMMON_GAMMA[k],
                                                 [(k, True, seven), (k, False, seven)]))
        lean = (WORDS_MODULE,
                "`commonPairProblem %d ks kt σ τ j` for the cases\n`(ks, kt, σ, τ, j)` of "
                "`commonCases %d`" % (k, k),
                "(WordGeometry.commonCases %d).map fun c =>\n"
                "    WordGeometry.commonPairProblem %d %s" % (k, k, CASE_FIELDS))
        out.append(Table("common_%d" % k, "Common%d" % k, 0, 0, COMMON_GAMMA[k], probs, lean))
    for w in ("short", "second"):
        for i in range(7):
            nx = (i + 1) % 7
            k = WORD[w][i]
            gamma = F(359, 400) if (w == "short" and i == 2) else F(17953, 20000)
            probs = []
            for sk in KINDS:
                for tk in KINDS:
                    for p in (False, True):
                        for r in (False, True):
                            if (i == 0 and not p) or (i == 2 and p) or (nx == 0 and not r) or \
                                    (nx == 2 and r) or (k == 0 and not p and r):
                                continue
                            for ax in (1, 2, 3, 4):
                                if core_separator_excluded(k, sk, tk, p, r, ax):
                                    continue
                                sig, tau = (1 if p else -1), (1 if r else -1)
                                src = End(*CHART_OF_KIND[sk], p, wrong_label(w, i, sk, sig), i)
                                tgt = End(*CHART_OF_KIND[tk], r, wrong_label(w, nx, tk, tau), nx)
                                probs.append(Problem("%s_%d_%s_%s_%d%d_%d" % (w, i, sk, tk, p, r, ax),
                                                     src, tgt, ax, 0, gamma,
                                                     [(k, True, seven), (k, False, seven)]))
            lean = (WORDS_MODULE,
                    "`wrongPairProblem .%s %d ks kt σ τ j` for the cases\n`(ks, kt, σ, τ, j)` of "
                    "`wrongCases .%s %d`" % (w, i, w, i),
                    "(WordGeometry.wrongCases .%s %d).map fun c =>\n"
                    "    WordGeometry.wrongPairProblem .%s %d %s" % (w, i, w, i, CASE_FIELDS))
            out.append(Table("%s_%d" % (w, i), camel(w) + str(i), i, 0, gamma, probs, lean))
    return out


# ----------------------------------------------------------------- arctangent bounds and gap
# (Arithmetic/AtanBounds.lean and Arithmetic/PairCover.lean)

ANGLE_UNIT = 10 ** 20


def floorQ(q):
    return q.numerator // q.denominator


def ceilQ(q):
    return -floorQ(-q)


def atan_poly_lo(z):
    w = z * z
    return z * (1 - w * (F(1, 3) - w * (F(1, 5) - w * (F(1, 7) - w * (F(1, 9) - w / 11)))))


def atan_poly_hi(z):
    w = z * z
    return z * (1 - w * (F(1, 3) - w * (F(1, 5) - w * (F(1, 7) - w / 9))))


def anchors():
    lo, hi = [0], [0]
    for j in range(16):
        z = F(16, 256 + j * (j + 1))
        lo.append(lo[-1] + floorQ(atan_poly_lo(z) * ANGLE_UNIT))
        hi.append(hi[-1] + ceilQ(atan_poly_hi(z) * ANGLE_UNIT))
    return lo, hi


ANCHOR_LO, ANCHOR_HI = anchors()
_atan_src = lean_text("Arithmetic/AtanBounds.lean")


def _lean_int_list(text, name):
    m = re.search(r"def %s : List Int :=\s*\[(.*?)\]" % name, text, re.S)
    return [int(x) for x in m.group(1).replace("\n", " ").split(",")]


assert _lean_int_list(_atan_src, "anchorLo") == ANCHOR_LO
assert _lean_int_list(_atan_src, "anchorHi") == ANCHOR_HI


def series_lo(z):
    return floorQ(atan_poly_lo(z) * ANGLE_UNIT) if z >= 0 else -ceilQ(atan_poly_hi(-z) * ANGLE_UNIT)


def series_hi(z):
    return ceilQ(atan_poly_hi(z) * ANGLE_UNIT) if z >= 0 else -floorQ(atan_poly_lo(-z) * ANGLE_UNIT)


def anchor_index(x):
    return min(16, max(0, floorQ(16 * x + F(1, 2))))


def anchor_arg(x):
    c = F(anchor_index(x), 16)
    return (x - c) / (1 + x * c)


@lru_cache(maxsize=None)
def atan_lo(x):
    return ANCHOR_LO[anchor_index(x)] + series_lo(anchor_arg(x)) if x >= 0 else -2 * ANGLE_UNIT


@lru_cache(maxsize=None)
def atan_hi(x):
    return ANCHOR_HI[anchor_index(x)] + series_hi(anchor_arg(x)) if x >= 0 else 2 * ANGLE_UNIT


GAP_LO = 76000000000000000000
GAP_HI = 235619449019234492925
PI_HALF_LO = 157079632679489661900
PI_HALF_HI = 157079632679489661950


def alpha_lo(sig, S):
    return atan_lo(S[0]) if sig else -atan_hi(S[1])


def alpha_hi(sig, S):
    return atan_hi(S[1]) if sig else -atan_lo(S[0])


def u_lo(k, r, sig, tau, S, T):
    if r:
        return GAP_LO - alpha_hi(sig, S) + alpha_lo(tau, T) - k * PI_HALF_HI
    return k * PI_HALF_LO - (GAP_HI - alpha_lo(sig, S) + alpha_hi(tau, T))


def u_hi(k, r, sig, tau, S, T):
    if r:
        return GAP_HI - alpha_lo(sig, S) + alpha_hi(tau, T) - k * PI_HALF_LO
    return k * PI_HALF_HI - (GAP_LO - alpha_hi(sig, S) + alpha_lo(tau, T))


def gap_empty(l, h, lo, hi):
    return min(h * ANGLE_UNIT, hi * DEN) < max(l * ANGLE_UNIT, lo * DEN)


def trim_ok(l, h, lo2, hi2, lo, hi):
    return lo2 * ANGLE_UNIT <= max(l * ANGLE_UNIT, lo * DEN) and \
        min(h * ANGLE_UNIT, hi * DEN) <= hi2 * ANGLE_UNIT


# ----------------------------------------------------------------- arcs and boxes


@lru_cache(maxsize=None)
def geo_box(chart, t1, t2):
    """The geometric part of the arc box (AffineCertificate.prepareArc, RowCheck.ArcBox)."""
    a = ar.Arc()
    a.outer, a.tlo, a.thi = chart == "outer", t1, t2
    assert ar.is_side(a) == (chart == "side")
    valid, r = ar.prepare(a, Q)
    assert valid, (chart, t1, t2)
    b = dict(side=ar.is_side(a), shift=ar.ofQ(ar.shift_of(a)))
    for k in ("rho", "aLo", "bLo", "aHi", "bHi", "rLo", "rHi"):
        b[k] = ar.ofQI(*r[k])
    return b


def full_box(chart, t1, t2, positive, label):
    b = dict(geo_box(chart, t1, t2))
    b["positive"] = positive
    b["c"], b["p"], b["q"] = (ar.ofQ(x) for x in label)
    return b


# ----------------------------------------------------------------- labels (LabelRelax.lean)


def box_lower(B, x, y):
    return F(ar.source_lower(B, ar.point(x * UNIT), ar.point(y * UNIT)), UNIT)


@lru_cache(maxsize=None)
def ranges(chart, t1, t2):
    B = geo_box(chart, t1, t2)
    return (box_lower(B, 1, 0), -box_lower(B, -1, 0), box_lower(B, 0, 1), -box_lower(B, 0, -1),
            box_lower(B, 1, 1), -box_lower(B, -1, -1), box_lower(B, 1, -1), -box_lower(B, -1, 1))


def side_remainder(R, d0, d1, d2, r, s):
    aL, aH, bL, bH = R[:4]
    if r <= 0:
        return (d0 + F(7, 12) * d1 - r * (bL * bH), d2 + F(7, 12) * s + r * (bL + bH))
    return (d0 + F(7, 12) * d1 - r * ((bL + bH) / 2) ** 2, d2 + F(7, 12) * s + r * (bL + bH))


def circle_remainder(R, k0, k1, d0, d1, d2, r, s):
    aL, aH, bL, bH, sL, sH, dL, dH = R
    ma, mb, md, ms = max(r, F(0)), max(-r, F(0)), max(s, F(0)) / 2, max(-s, F(0)) / 2
    nu = ma + md + ms
    return (d0 + ma * (aL * aH) + mb * (bL * bH) + ms * (sL * sH) + md * (dL * dH) + nu * k0,
            d1 - ma * (aL + aH) - ms * (sL + sH) - md * (dL + dH) + nu * k1,
            d2 - mb * (bL + bH) - ms * (sL + sH) + md * (dL + dH) + nu * k1)


def kappa(chart):
    return (Q - F(1, 2), F(-1)) if chart == "outer" else (F(-71, 144), F(1))


def lower_check(chart, R, L, ell):
    """lowerCheck: ell = (c, p, q) ≤ L on the arc."""
    d = (L.cLo - ell[0], L.p - ell[1], L.q - ell[2])
    if chart == "side":
        e = side_remainder(R, *d, L.r, L.s)
        return 0 <= e[0] + min(e[1] * R[2], e[1] * R[3])
    e = circle_remainder(R, *kappa(chart), *d, L.r, L.s)
    return 0 <= e[0] + min(e[1] * R[0], e[1] * R[1]) + min(e[2] * R[2], e[2] * R[3])


def label_check(chart, t1, t2, L, lower, ell):
    R = ranges(chart, t1, t2)
    if lower:
        return lower_check(chart, R, L, ell)
    return lower_check(chart, R, L.neg(), tuple(-x for x in ell))


def grid_down(x):
    return F(floorQ(x * GRID), GRID)


def grid_round(x):
    return F(round(x * GRID), GRID)


def lower_label(chart, t1, t2, L):
    """An affine label (c, p, q) ≤ L on the arc, from the remainder of L."""
    if L.r == 0 and L.s == 0 and L.cLo == L.cHi:
        return (L.cLo, L.p, L.q)
    if L.r == 0 and L.s == 0:
        return (grid_down(L.cLo), L.p, L.q)
    R = ranges(chart, t1, t2)
    aL, aH, bL, bH = R[:4]
    if chart == "side":
        e0, e1 = side_remainder(R, L.cLo, L.p, L.q, L.r, L.s)
        q = grid_round(e1)
        return (grid_down(e0 + min((e1 - q) * bL, (e1 - q) * bH)), F(0), q)
    e0, e1, e2 = circle_remainder(R, *kappa(chart), L.cLo, L.p, L.q, L.r, L.s)
    p, q = grid_round(e1), grid_round(e2)
    return (grid_down(e0 + min((e1 - p) * aL, (e1 - p) * aH) + min((e2 - q) * bL, (e2 - q) * bH)),
            p, q)


@lru_cache(maxsize=None)
def arc_label(chart, t1, t2, L, lower):
    if lower:
        ell = lower_label(chart, t1, t2, L)
    else:
        ell = tuple(-x for x in lower_label(chart, t1, t2, L.neg()))
    assert label_check(chart, t1, t2, L, lower, ell)
    return ell


# ----------------------------------------------------------------- float model of a piece

QF = float(Q)
SQRTQ = math.sqrt(QF)


def endpoint_float(chart, u):
    u = float(u)
    if chart == "side":
        return 7 / 12
    if chart == "outer":
        return (-(u + 1) + math.sqrt((u + 1) ** 2 + 4 * (1 + u * u) * (QF - 0.5))) / (2 * (1 + u * u))
    d = (u + 1) ** 2 - (1 + u * u) * 71 / 36
    return ((u + 1) + math.sqrt(max(d, 0.0))) / (2 * (1 + u * u))


class Piece:
    __slots__ = ("chart", "t1", "t2", "side", "aLo", "bLo", "aHi", "bHi", "rLo", "rHi", "v", "rho")


@lru_cache(maxsize=None)
def piece(chart, t1, t2):
    P = Piece()
    P.chart, P.t1, P.t2, P.side = chart, t1, t2, chart == "side"
    P.aLo, P.aHi = endpoint_float(chart, t1), endpoint_float(chart, t2)
    P.bLo, P.bHi = float(t1) * P.aLo, float(t2) * P.aHi
    P.v = -0.5 if chart == "outer" else 0.5
    P.rho = SQRTQ if chart == "outer" else 1 / 12
    if P.side:
        P.rLo = P.rHi = 0.0
    else:
        P.rLo = (P.bLo - P.v) / (P.aLo - P.v)
        P.rHi = (P.bHi - P.v) / (P.aHi - P.v)
    return P


def piece_min(P, X, Y):
    """min over the piece of X a + Y b (floats or arrays)."""
    m = np.minimum(X * P.aLo + Y * P.bLo, X * P.aHi + Y * P.bHi)
    if P.side:
        return m
    n = np.hypot(X, Y)
    n = np.where(n > 0, n, 1.0)
    bc = P.v - P.rho * Y / n
    inside = (X < 0) & (bc >= P.bLo) & (bc <= P.bHi)
    return np.where(inside, np.minimum(m, P.v * (X + Y) - P.rho * n), m)


# ----------------------------------------------------------------- the reduced cell


def trig_map(k, s):
    """sin φ and cos φ of φ = k π/2 + s u as (coefficient of sin u, of cos u)."""
    k %= 4
    if k == 0:
        return (s, 0), (0, 1)
    if k == 1:
        return (0, 1), (-s, 0)
    if k == 2:
        return (-s, 0), (0, -1)
    return (0, -1), (s, 0)


class Red:
    """A cell reduced to axis one or four (margin_reverse, charge_reverse)."""
    __slots__ = ("Ps", "sig", "cs", "ps", "qs", "Pt", "tau", "ct", "pt", "qt", "ax", "k", "s",
                 "beta", "gamma")


def reduce_cell(prob, S, T, k, r):
    Ls = arc_label(*S, prob.src.label, True)
    Lt = arc_label(*T, prob.tgt.label, False)
    R = Red()
    if prob.axis in (1, 4):
        R.Ps, R.sig, (R.cs, R.ps, R.qs) = piece(*S), prob.src.sig, Ls
        R.Pt, R.tau, (R.ct, R.pt, R.qt) = piece(*T), prob.tgt.sig, Lt
        R.ax = prob.axis
    else:
        R.Ps, R.sig, (R.cs, R.ps, R.qs) = piece(*T), -prob.tgt.sig, tuple(-x for x in Lt)
        R.Pt, R.tau, (R.ct, R.pt, R.qt) = piece(*S), -prob.src.sig, tuple(-x for x in Ls)
        R.ax = 4 if prob.axis == 2 else 1
    R.k, R.s = k, (1 if r else -1)
    R.beta, R.gamma = prob.beta, prob.gamma
    return R


def target_coeffs(R, lam):
    (eSS, eSC), (eCS, eCC) = trig_map(R.k, R.s)
    x0, y0, t = -float(R.pt), -float(R.qt), R.tau
    if R.ax == 1:
        return x0, -lam * eSS, -lam * eSC, y0, lam * t * eCS, lam * t * eCC
    return x0, lam * eCS, lam * eCC, y0, lam * t * eSS, lam * t * eSC


def lagr_bound(R, lams, us):
    lams = np.asarray(lams, dtype=float)[:, None]
    us = np.asarray(us, dtype=float)[None, :]
    S, C = np.sin(us), np.cos(us)
    ps, qs = float(R.ps), float(R.qs)
    if R.ax == 4:
        Xs, Ys = ps - lams, qs + 0 * lams
    else:
        Xs, Ys = ps + 0 * lams, qs - lams * R.sig
    ms = piece_min(R.Ps, Xs, Ys)
    x0, xS, xC, y0, yS, yC = target_coeffs(R, lams)
    mt = piece_min(R.Pt, x0 + xS * S + xC * C, y0 + yS * S + yC * C)
    b = (R.k * math.pi / 2 + R.s * us + float(R.cs - R.ct) + lams * (1 + S + C) / 2
         - float(R.beta) * (S + C - 1) / 2)
    return (b + ms + mt).min(axis=1) - float(R.gamma)


LAM_GRID = np.concatenate([[0.0], np.geomspace(1e-3, 200.0, 47)])


def best_lambda(R, u1, u2, nu=9):
    us = np.linspace(u1, u2, nu)
    g = lagr_bound(R, LAM_GRID, us)
    i = int(np.argmax(g))
    lo, hi = LAM_GRID[max(i - 1, 0)], LAM_GRID[min(i + 1, len(LAM_GRID) - 1)]
    best_l, best_g = LAM_GRID[i], g[i]
    for _ in range(3):
        grid = np.linspace(lo, hi, 13)
        gg = lagr_bound(R, grid, us)
        j = int(np.argmax(gg))
        if gg[j] > best_g:
            best_g, best_l = gg[j], grid[j]
        step = (hi - lo) / 12
        lo, hi = max(best_l - step, 0.0), best_l + step
    return best_l, best_g


def choose_modes(R, lam, u1, u2, nu=9):
    Pt = R.Pt
    if Pt.side:
        return [(0, None)]
    us = np.linspace(u1, u2, nu)
    S, C = np.sin(us), np.cos(us)
    x0, xS, xC, y0, yS, yC = target_coeffs(R, lam)
    X, Y = x0 + xS * S + xC * C, y0 + yS * S + yC * C
    dlo, dhi = Y - X * Pt.rLo, Y - X * Pt.rHi
    um = (u1 + u2) / 2
    Xm = x0 + xS * math.sin(um) + xC * math.cos(um)
    Ym = y0 + yS * math.sin(um) + yC * math.cos(um)
    hN = max(1, int(round(math.hypot(Xm, Ym) * H_SCALE)))
    out = []
    if X.min() >= 0:
        out.append((0, None))
    if dlo.min() >= 0 and dhi.min() >= 0:
        out.append((1, None))
    if dlo.max() <= 0 and dhi.max() <= 0:
        out.append((2, None))
    out.append((3, hN))
    if X.min() < 0 and X.max() > -1e-9 and (0, None) not in out:
        out.append((0, None))
    return out


# ----------------------------------------------------------------- the exact row test


def cell_ctx(prob, S, T):
    return dict(den=DEN, n=2,
                boxes=[full_box(*S, prob.src.positive, arc_label(*S, prob.src.label, True)),
                       full_box(*T, prob.tgt.positive, arc_label(*T, prob.tgt.label, False))],
                betaHalf=[ar.ofQ(prob.beta / 2)] * 7, gamma=[ar.ofQ(prob.gamma)] * 7)


def circle_pieces(ctx, x, maxdepth=12):
    """Circle pieces (h, upto): one piece if the row's h passes, else bisection with h = √V at
    the midpoint of each piece (as affine_rows.circle_pieces); None if that fails."""
    c = ar.Core(ctx, x)
    if ar.pos3(DEN, x["lo"], x["hi"], c.c1, c.circle(x["h"])):
        return [(x["h"], x["hi"])]
    out = []

    def go(l, h, depth):
        hn = max(1, round(c.sqrtV((l + h) / 2 / DEN) * H_SCALE))
        if ar.pos3(DEN, l, h, c.c1, c.circle(hn)):
            out.append((hn, h))
            return True
        if depth >= maxdepth or h - l < 2:
            return False
        m = (l + h) // 2
        return go(l, m, depth + 1) and go(m, h, depth + 1)
    return out if go(x["lo"], x["hi"], 0) else None


def try_row(prob, S, T, k, r, l, h, ctx):
    """A row on the cell, or None; also the float bound."""
    R = reduce_cell(prob, S, T, k, r)
    lam, g = best_lambda(R, l / DEN, h / DEN)
    if g <= 0:
        return None, g
    lamN = int(round(lam * LAM_SCALE))
    for mode, hN in choose_modes(R, lam, l / DEN, h / DEN):
        x = dict(edge=0, source=0, target=1, axis=prob.axis, k=k, positive=r, lo=l, hi=h,
                 lam=lamN, mode=mode, h=hN or 0, pieces=[])
        if mode == 3:
            x["pieces"] = circle_pieces(ctx, x)
            if x["pieces"] is None:
                continue
        if ar.check_row(ctx, x):
            return x, g
    return None, g


# ----------------------------------------------------------------- the adaptive subdivision

MIN_T = F(1, 2 ** 12)
MIN_U = 2
MAX_CELLS = 200000


def child_bound(prob, S, T, k, r, l, h):
    lo = u_lo(k, r, prob.src.positive, prob.tgt.positive, S[1:], T[1:])
    hi = u_hi(k, r, prob.src.positive, prob.tgt.positive, S[1:], T[1:])
    if gap_empty(l, h, lo, hi):
        return 1e9
    L, H = max(l * ANGLE_UNIT, lo * DEN), min(h * ANGLE_UNIT, hi * DEN)
    l2, h2 = L // ANGLE_UNIT, -((-H) // ANGLE_UNIT)
    return best_lambda(reduce_cell(prob, S, T, k, r), l2 / DEN, h2 / DEN)[1]


def halves_of(S):
    m = (S[1] + S[2]) / 2
    return (S[0], S[1], m), (S[0], m, S[2])


def solve_half(prob, k, r, umaxN, rows, stats):
    """The tree of one half (nested lists); rows are appended in the order of the leaves."""
    src, tgt = prob.src, prob.tgt
    root = []
    stack = [((src.chart, src.lo, src.hi), (tgt.chart, tgt.lo, tgt.hi), 0, umaxN, root)]
    while stack:
        S, T, l, h, node = stack.pop()
        stats["cells"] += 1
        if stats["cells"] > MAX_CELLS:
            raise RuntimeError("%s: too many cells" % prob.name)
        lo = u_lo(k, r, src.positive, tgt.positive, S[1:], T[1:])
        hi = u_hi(k, r, src.positive, tgt.positive, S[1:], T[1:])
        if gap_empty(l, h, lo, hi):
            node.append("gap")
            continue
        L, H = max(l * ANGLE_UNIT, lo * DEN), min(h * ANGLE_UNIT, hi * DEN)
        l2, h2 = L // ANGLE_UNIT, -((-H) // ANGLE_UNIT)
        if (l2, h2) != (l, h):
            assert trim_ok(l, h, l2, h2, lo, hi)
            sub = []
            node.extend(["trim", l2, h2, sub])
            node, l, h = sub, l2, h2
        ctx = cell_ctx(prob, S, T)
        row, g = try_row(prob, S, T, k, r, l, h, ctx)
        if row is not None:
            rows.append((S, T, row))
            node.append("row")
            continue
        dims = [d for d, ok in ((2, h - l > MIN_U), (1, T[2] - T[1] > MIN_T),
                                (0, S[2] - S[1] > MIN_T)) if ok]
        if not dims:
            raise RuntimeError("%s: no row on %s %s [%d, %d]" % (prob.name, S, T, l, h))
        best = None
        for d in dims:
            if d == 2:
                m = (l + h) // 2
                b1 = child_bound(prob, S, T, k, r, l, m)
                b2 = child_bound(prob, S, T, k, r, m, h)
            elif d == 1:
                A_, B_ = halves_of(T)
                b1 = child_bound(prob, S, A_, k, r, l, h)
                b2 = child_bound(prob, S, B_, k, r, l, h)
            else:
                A_, B_ = halves_of(S)
                b1 = child_bound(prob, A_, T, k, r, l, h)
                b2 = child_bound(prob, B_, T, k, r, l, h)
            if g > 0:
                # the float bound is positive: the exact loss (Taylor, Bernstein, AM-GM) scales
                # like the square of the angle width, so halving the angle quarters it
                score = 0.75 * g if d == 2 else min(b1, b2) - g
            else:
                score = min(b1, 2e-3) + min(b2, 2e-3)
            if best is None or score > best[0] + 1e-12:
                best = (score, d)
        d = best[1]
        left, right = [], []
        if d == 2:
            m = (l + h) // 2
            node.extend(["angle", left, right])
            stack.append((S, T, m, h, right))
            stack.append((S, T, l, m, left))
        elif d == 1:
            A_, B_ = halves_of(T)
            node.extend(["target", left, right])
            stack.append((S, B_, l, h, right))
            stack.append((S, A_, l, h, left))
        else:
            A_, B_ = halves_of(S)
            node.extend(["source", left, right])
            stack.append((B_, T, l, h, right))
            stack.append((A_, T, l, h, left))
    return root


def solve_problem(args):
    ti, pi = args
    prob = TABLES[ti].problems[pi]
    t0 = time.time()
    rows, trees = [], []
    stats = {"cells": 0}
    for (k, r, umaxN) in prob.halves:
        trees.append(solve_half(prob, k, r, umaxN, rows, stats))
    return ti, pi, rows, trees, stats["cells"], time.time() - t0


TABLES = tables()

# ----------------------------------------------------------------- assembling and checking


def tree_tokens(t):
    out = []

    def go(n):
        tag = n[0]
        if tag == "gap":
            out.append(0)
        elif tag == "trim":
            out.extend([1, n[1], n[2]])
            go(n[3])
        elif tag in ("source", "target", "angle"):
            out.append({"source": 2, "target": 3, "angle": 4}[tag])
            go(n[1])
            go(n[2])
        else:
            assert tag == "row"
            out.append(5)
    go(t)
    return out


def assemble(tab, results):
    """Arcs, rows and trees of a table from the solved problems (in problem order)."""
    arcs, index, rows, trees = [], {}, [], []
    for pi, prob in enumerate(tab.problems):
        prows, ptrees = results[pi]
        for S, T, x in prows:
            ids = []
            for P, end, lower in ((S, prob.src, True), (T, prob.tgt, False)):
                key = (end.role, P, end.positive, end.label, lower)
                if key not in index:
                    index[key] = len(arcs)
                    arcs.append(dict(role=end.role, chart=P[0], t1=P[1], t2=P[2],
                                     positive=end.positive, spec=end.label, lower=lower,
                                     label=arc_label(*P, end.label, lower)))
                ids.append(index[key])
            y = dict(x)
            y["edge"], y["source"], y["target"] = tab.edge, ids[0], ids[1]
            rows.append(y)
        trees.extend(ptrees)
    return arcs, rows, trees


def table_ctx(tab, arcs):
    return dict(den=DEN, n=len(arcs),
                boxes=[full_box(a["chart"], a["t1"], a["t2"], a["positive"], a["label"]) for a in arcs],
                betaHalf=[ar.ofQ(tab.beta / 2)] * 7, gamma=[ar.ofQ(tab.gamma)] * 7)


def arc_fits(a, end, S):
    return (a["chart"] == "outer") == (end.chart == "outer") and \
        (a["chart"] == "side") == (end.chart == "side") and a["positive"] == end.positive and \
        a["t1"] <= S[0] and S[1] <= a["t2"]


def check_table(tab, arcs, rows, trees):
    """The integer checks of TableCtx/RowCheck, LabelRelax and PairCover, from the data alone."""
    ctx = table_ctx(tab, arcs)
    for i, x in enumerate(rows):
        assert ar.check_row(ctx, x), (tab.name, "row", i)
    for i, a in enumerate(arcs):
        assert label_check(a["chart"], a["t1"], a["t2"], a["spec"], a["lower"], a["label"]), \
            (tab.name, "label", i)
    pos = [0]
    ti = iter(trees)

    def leaf(prob, k, r, S, T, l, h):
        x = rows[pos[0]]
        pos[0] += 1
        sa, ta = arcs[x["source"]], arcs[x["target"]]
        return (x["source"] < len(arcs) and x["target"] < len(arcs) and x["axis"] == prob.axis
                and x["k"] == k and x["positive"] == r and x["lo"] <= l and h <= x["hi"]
                and arc_fits(sa, prob.src, S) and arc_fits(ta, prob.tgt, T)
                and (sa["spec"], sa["lower"]) == (prob.src.label, True)
                and (ta["spec"], ta["lower"]) == (prob.tgt.label, False)
                and prob.gamma <= tab.gamma and tab.beta == prob.beta)

    def tree(prob, k, r, t, S, T, l, h):
        tag = t[0]
        lo = u_lo(k, r, prob.src.positive, prob.tgt.positive, S, T)
        hi = u_hi(k, r, prob.src.positive, prob.tgt.positive, S, T)
        if tag == "gap":
            return gap_empty(l, h, lo, hi)
        if tag == "trim":
            return trim_ok(l, h, t[1], t[2], lo, hi) and tree(prob, k, r, t[3], S, T, t[1], t[2])
        if tag == "source":
            m = (S[0] + S[1]) / 2
            return tree(prob, k, r, t[1], (S[0], m), T, l, h) and \
                tree(prob, k, r, t[2], (m, S[1]), T, l, h)
        if tag == "target":
            m = (T[0] + T[1]) / 2
            return tree(prob, k, r, t[1], S, (T[0], m), l, h) and \
                tree(prob, k, r, t[2], S, (m, T[1]), l, h)
        if tag == "angle":
            m = (l + h) // 2
            return tree(prob, k, r, t[1], S, T, l, m) and tree(prob, k, r, t[2], S, T, m, h)
        return pos[0] < len(rows) and leaf(prob, k, r, S, T, l, h)

    for prob in tab.problems:
        for (k, r, umaxN) in prob.halves:
            t = next(ti)
            assert tree(prob, k, r, t, (prob.src.lo, prob.src.hi), (prob.tgt.lo, prob.tgt.hi),
                        0, umaxN), (tab.name, prob.name)
    assert pos[0] == len(rows), (tab.name, "unused rows")
    return ctx


# ----------------------------------------------------------------- writing


def frac(q):
    q = F(q)
    return str(q.numerator) if q.denominator == 1 else "%d/%d" % (q.numerator, q.denominator)


def lean_q(q):
    q = F(q)
    if q.denominator == 1:
        return str(q.numerator)
    return "(%d/%d)" % (q.numerator, q.denominator)


def write_data(out, tab, arcs, rows, trees, ctx):
    out.mkdir(parents=True, exist_ok=True)
    with open(out / (tab.name + ".rows"), "w") as f:
        f.write("%d %d\n" % (DEN, len(rows)))
        for x in rows:
            v = [x["edge"], x["source"], x["target"], x["axis"], x["k"], int(x["positive"]),
                 x["lo"], x["hi"], x["lam"], x["mode"]]
            if x["mode"] == 3:
                for j, (hn, upto) in enumerate(x["pieces"]):
                    v.append(hn)
                    if j + 1 < len(x["pieces"]):
                        v.append(upto)
            f.write(" ".join(map(str, v)) + "\n")
    with open(out / (tab.name + ".arcs"), "w") as f:
        f.write("%d %d\n" % (DEN, len(arcs)))
        for b, g in zip(ctx["betaHalf"], ctx["gamma"]):
            f.write("%d %d %d %d\n" % (b + g))
        for b in ctx["boxes"]:
            v = [int(b["side"]), int(b["positive"])]
            for k in ("c", "p", "q", "shift", "rho", "aLo", "bLo", "aHi", "bHi", "rLo", "rHi"):
                v += list(b[k])
            v += [0, 0]
            f.write(" ".join(map(str, v)) + "\n")
    with open(out / (tab.name + ".trees"), "w") as f:
        for t in trees:
            f.write(" ".join(map(str, tree_tokens(t))) + "\n")


HEADER = """module

{imports}

/-! {doc} -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.{module}
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000
"""

FOOTER = """
end SquaresInCircles.Eight.Generated.Pairs.{module}
"""

def lean_quad(L):
    return "⟨%s⟩" % ", ".join(lean_q(x) for x in L.key())


def write_lean(root, tab, arcs, rows, trees, chunk=2000, part=100):
    base = root / "SquaresInCircles" / "Eight" / "Generated" / "Pairs"
    mod = tab.module
    (base / mod).mkdir(parents=True, exist_ok=True)
    for old in (base / mod).glob("*.lean"):
        old.unlink()
    pre = "SquaresInCircles.Eight.Generated.Pairs." + mod
    rel5 = "../../../../../data/eight/pairs/" + tab.name
    rel4 = "../../../../data/eight/pairs/" + tab.name
    arc_lines = ",\n".join(
        "      ⟨%d, %d, %s, %s, ⟨%s, %s⟩, ⟨%s, %s, %s⟩⟩" % (
            i, a["role"], "true" if a["chart"] == "outer" else "false",
            "true" if a["positive"] else "false", lean_q(a["t1"]), lean_q(a["t2"]),
            *(lean_q(x) for x in a["label"])) for i, a in enumerate(arcs))
    spec_lines = ",\n".join("  (%s, %s)" % (lean_quad(a["spec"]), "true" if a["lower"] else "false")
                            for a in arcs)
    problem_module, problem_doc, problem_term = tab.lean
    groups = ",\n     ".join(
        f'int_rows% "{rel5}.arcs" {8 + g} {8 + min(g + ar.BOX_GROUP, len(arcs))} ↦\n'
        '        ArcBox.ofData'
        for g in range(0, len(arcs), ar.BOX_GROUP))
    boxes = ar.blocks_of(len(arcs), ar.BOX_BLOCK)
    box_thms = "".join(f"""
theorem ctx_boxes_{j} : boxesRange table.radius table.arcs ctx.boxes {a} {c} = true := by
  decide +kernel
""" for j, (a, c) in enumerate(boxes))
    text = HEADER.format(
        imports="public import %s\n"
                "public meta import SquaresInCircles.Eight.IntRows" % problem_module,
        doc="The data of the pair table `%s`: its arcs, the quadratic label of each arc with its\n"
            "side, its problems and its fixed-point context, checked once." % mod, module=mod)
    text += f"""
/-- The arcs of the table. The fields `cuts`, `word`, `differenceRange` and `allowedAxes` serve
the state and angle covers of the affine tables; the pair tables use coverage trees instead. -/
def table : AffineTableMeta :=
  {{ radius := {lean_q(Q)}
    arcs := [
{arc_lines}]
    cuts := fun _ => ⟨0, 1⟩
    word := fun _ => 0
    charge := fun _ => {lean_q(tab.beta)}
    target := fun _ => {lean_q(tab.gamma)}
    differenceRange := fun _ => ⟨0, 1⟩
    allowedAxes := fun _ => [] }}

/-- For each arc, the quadratic label its affine label bounds: below (`true`, a source arc) or
above (`false`, a target arc). -/
def specs : List (QuadLabel × Bool) := [
{spec_lines}]

/-- The problems of the table: {problem_doc}, in order. -/
def problems : List PairProblem :=
  {problem_term}

def ctx : TableCtx :=
  ⟨{DEN}, {len(arcs)},
    [{groups}],
    int_rows% "{rel5}.arcs" 1 8 ↦
      fun (a b _c _d : Int) => (⟨a, b⟩ : Fixed.FI),
    int_rows% "{rel5}.arcs" 1 8 ↦
      fun (_a _b c d : Int) => (⟨c, d⟩ : Fixed.FI)⟩

theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel
{box_thms}
theorem ctx_valid : ctx.Valid table :=
  TableCtx.valid_of ctx_scalars (blocks := {list(boxes)}) (by decide +kernel)
    ({ar.all_blocks(["ctx_boxes_%d" % j for j in range(len(boxes))], 6)})

theorem labels_check : labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
  decide +kernel
"""
    text += FOOTER.format(module=mod)
    (base / mod / "Data.lean").write_text(text)
    chunks = []
    for c, start in enumerate(range(0, len(rows), chunk)):
        count = min(chunk, len(rows) - start)
        parts = []
        text = HEADER.format(
            imports="public import %s.Data\npublic meta import SquaresInCircles.Eight.IntRows" % pre,
            doc="Rows %d to %d of the table, checked by `decide +kernel`, a hundred rows a theorem."
                % (start, start + count - 1), module=mod)
        for k, s0 in enumerate(range(start, start + count, part)):
            n = min(part, start + count - s0)
            nm = "rows%03d_%d" % (c, k)
            parts.append(nm)
            text += f"""
def {nm} : List AffineRow :=
  nat_rows% "{rel5}.rows" {s0 + 1} {s0 + 1 + n} ↦ AffineRow.ofData

theorem {nm}_check : checkRows ctx {nm} = true := by decide +kernel
"""
        cn = "chunk%03d" % c
        chunks.append(cn)
        joined = ar.wrap(parts, 4, "  ", sep=" ++ ")
        simps = ar.wrap([cn, "checkRows_append"] + [p + "_check" for p in parts] + ["Bool.and_true"],
                        4, "  simp only [")
        text += f"""
/-- Rows {start} to {start + count - 1}. -/
def {cn} : List AffineRow :=
{joined}

theorem {cn}_check : checkRows ctx {cn} = true := by
{simps}]
"""
        text += FOOTER.format(module=mod)
        (base / mod / ("Rows%03d.lean" % c)).write_text(text)
    imports = "\n".join(["public import %s.Rows%03d" % (pre, c) for c in range(len(chunks))] +
                        ["public meta import SquaresInCircles.Eight.PairData"])
    text = HEADER.format(
        imports=imports,
        doc=f"# The pair table `{mod}`\n\n" + textwrap.fill(
            f"Each of its {len(rows)} rows passes `checkRow`, so it satisfies its claim; the "
            f"labels of its {len(arcs)} arcs pass `labelsCheck`; the trees of its "
            f"{len(tab.problems)} problems pass `problemsCheck`. So every problem holds.", 96),
        module=mod)
    text += f"""
/-- All rows, in the order the trees consume them. -/
def data : List AffineRow :=
  {(" ++" + chr(10) + "    ").join(chunks)}

theorem data_check : checkRows ctx data = true := by
{ar.wrap(["data", "checkRows_append"] + [c + "_check" for c in chunks] + ["Bool.and_true"], 4, "  simp only [")}]

theorem all_row_claims : ∀ x ∈ data, (x.toTableRow table ctx.den).Claim table :=
  fun x hx => checkRow_claim ctx_valid (checkRows_sound data_check x hx)

/-- The trees of the halves of the problems, in order. -/
def trees : List PairTree := pair_trees% "{rel4}.trees"

theorem trees_check : problemsCheck table ctx specs problems trees data = true := by
  decide +kernel

theorem sound : ∀ P ∈ problems, P.Holds table.radius ctx.den :=
  table_sound ctx_valid labels_check all_row_claims trees_check
"""
    text += FOOTER.format(module=mod)
    (base / (mod + ".lean")).write_text(text)
    return len(chunks)


def write_umbrellas(root, tabs):
    base = root / "SquaresInCircles" / "Eight" / "Generated" / "Pairs"
    for name, doc, sel in (("FourType", "pair tables of the four-type pair bounds",
                            lambda t: t.name.startswith("four_type")),
                           ("Words", "pair tables of the quarter-word pair bounds",
                            lambda t: not t.name.startswith("four_type"))):
        mods = [t.module for t in tabs if sel(t)]
        text = "module\n\n" + "\n".join("public import SquaresInCircles.Eight.Generated.Pairs.%s" % m
                                        for m in mods) + "\n\n/-! The %d %s. -/\n" % (len(mods), doc)
        (base.parent / ("Pairs%s.lean" % name)).write_text(text)


# ----------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--only", nargs="*", help="table names (default: all)")
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args()
    sel = [i for i, t in enumerate(TABLES) if not args.only or t.name in args.only]
    jobs = [(ti, pi) for ti in sel for pi in range(len(TABLES[ti].problems))]
    jobs.sort(key=lambda j: -len(TABLES[j[0]].problems[j[1]].halves))
    results = {ti: {} for ti in sel}
    t0 = time.time()
    cells = 0
    with mp.Pool(args.jobs) as pool:
        for ti, pi, rows, trees, nc, dt in pool.imap_unordered(solve_problem, jobs, chunksize=1):
            results[ti][pi] = (rows, trees)
            cells += nc
    print("solved %d problems in %.1f s (%d cells)" % (len(jobs), time.time() - t0, cells))
    total_rows = total_arcs = 0
    for ti in sel:
        tab = TABLES[ti]
        arcs, rows, trees = assemble(tab, [results[ti][pi] for pi in range(len(tab.problems))])
        ctx = check_table(tab, arcs, rows, trees)
        total_rows += len(rows)
        total_arcs += len(arcs)
        nodes = sum(len(tree_tokens(t)) for t in trees)
        print("%-28s rows %5d arcs %4d trees %4d tokens %6d  checked" %
              (tab.name, len(rows), len(arcs), len(trees), nodes))
        if not args.no_write:
            write_data(ROOT / "data" / "eight" / "pairs", tab, arcs, rows, trees, ctx)
            write_lean(ROOT, tab, arcs, rows, trees)
    if not args.no_write and not args.only:
        write_umbrellas(ROOT, TABLES)
    print("total rows %d arcs %d, %.1f s" % (total_rows, total_arcs, time.time() - t0))


if __name__ == "__main__":
    main()

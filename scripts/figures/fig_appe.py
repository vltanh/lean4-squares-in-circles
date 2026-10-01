#!/usr/bin/env python3
"""Draw the figures of Appendix E (docs/proof/appendix-e.md), six squares: the
tails and the stress of the model, in docs/proof/figures/appendix-e/.

    python3 scripts/figures/fig_appe.py

Every figure is computed from the functions and constants of the appendix:
the stresses of the two tails and their minorants (evaluated at the corners
with the Taylor polynomials, in exact rational arithmetic, as in the tables),
the value and the gap of the pair N, W of Definition 9.48, the forces along
the lines of the sweep, the support of the turned square D, the vertex
minorant and the remainder of Definition 9.51. The configuration at the edge
of the west tail is solved from the separating inequalities of Lemma E.1.
"""
import math
from fractions import Fraction as Fr

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, u, shift, sb)
from fig_front import arrow, polyline, word, outside_disk_pieces

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN = COLORS[:6]
RED = '#dc2626'

# The constants of Lemma 9.2 and Proposition 9.27.
H = math.sqrt(2) / 2
A_STAR = (1466 + 1940 * H) / 267
B_STAR = (327 + 432 * H) / 712
S_STAR = 2 * B_STAR / (A_STAR + math.sqrt(A_STAR ** 2 - 4 * B_STAR))
T_STAR = (30 * H - 20) * S_STAR + 3.5 - 4.5 * H
Q_STAR = 2 * S_STAR ** 2 + 4 * S_STAR + 2.5
R6 = math.sqrt(Q_STAR)
RHO = math.sqrt(Q_STAR - 0.25) - 0.5
R_STAR = (S_STAR + 0.5) / (S_STAR + 1.5)
M_STAR = (1 + R_STAR) * (T_STAR + 0.5) / (1.5 - S_STAR)
K_STAR = 2 * H * M_STAR
BETA_STAR = M_STAR * (0.5 - T_STAR)
# The ceiling of Definition 9.4 and its decimals.
Q0 = 2.85118
R0 = math.sqrt(Q0)
RHO0 = math.sqrt(Q0 - 0.25) - 0.5
C0 = RHO0 - 1
RBAR, RHOBAR, CBAR = Fr(16886, 10000), Fr(111282, 100000), Fr(11282, 100000)

# The colours of the squares in Chapter 9.
STYLE = {'C': (GREY, FAINT), 'N': (FILLS[1], ORANGE), 'E': (FILLS[2], GREEN),
         'W': (FILLS[3], PURPLE), 'S': (FILLS[4], PINK),
         'D': (FILLS[5], CYAN)}


def save(f, name, title):
    """Save a figure of this appendix, in its directory."""
    assert name.startswith('appendix-e/'), name
    f.save(name, title)


def tau(t):
    return 0.5 + (abs(math.cos(t)) + abs(math.sin(t))) / 2


def deg(t):
    return t * 180 / PI


def dot2(p, q):
    return p[0] * q[0] + p[1] * q[1]


def scale(p, k):
    return (k * p[0], k * p[1])


def add(*ps):
    return (sum(p[0] for p in ps), sum(p[1] for p in ps))


# ---------------------------------------------------------------------------
# The Taylor polynomials, in exact arithmetic, as in the tables.

def c6(x):
    x = Fr(x)
    return 1 - x ** 2 / 2 + x ** 4 / 24 - x ** 6 / 720


def c4(x):
    x = Fr(x)
    return 1 - x ** 2 / 2 + x ** 4 / 24


def s7(x):
    x = Fr(x)
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def s5(x):
    x = Fr(x)
    return x - x ** 3 / 6 + x ** 5 / 120


def sin_below(x):
    return s7(x) if x >= 0 else s5(x)


def sin_above(x):
    return s5(x) if x >= 0 else s7(x)


# ---------------------------------------------------------------------------
# Small drawing helpers.

class Panel:
    """A graph in a figure drawn in pixels: the data point (x, y) goes to
    (x0 + (x - a) w / (b - a), y0 + (y - c) h / (d - c))."""

    def __init__(self, f, x0, y0, w, h, xlim, ylim):
        self.f, self.x0, self.y0, self.w, self.h = f, x0, y0, w, h
        self.xlim, self.ylim = xlim, ylim

    def P(self, x, y):
        (a, b), (c, d) = self.xlim, self.ylim
        return (self.x0 + (x - a) / (b - a) * self.w,
                self.y0 + (y - c) / (d - c) * self.h)

    def curve(self, fn, a, b, n=240, **kw):
        """The graph of fn on [a, b], cut where it leaves the panel."""
        lo, hi = self.ylim
        run = []
        for k in range(n + 1):
            x = a + (b - a) * k / n
            y = fn(x)
            if lo <= y <= hi:
                run.append(self.P(x, y))
            else:
                if len(run) > 1:
                    polyline(self.f, run, **kw)
                run = []
        if len(run) > 1:
            polyline(self.f, run, **kw)

    def frame(self, xticks, yticks, xlabel='', ylabel='', size=12):
        f = self.f
        (a, b), (c, d) = self.xlim, self.ylim
        f.polygon([self.P(a, c), self.P(b, c), self.P(b, d), self.P(a, d)],
                  stroke=INK, width=1)
        for x, s in xticks:
            p = self.P(x, c)
            f.line(p, shift(p, (0, 5)), width=1)
            word(f, shift(p, (0, -14)), s, size=size)
        for y, s in yticks:
            p = self.P(a, y)
            f.line(p, shift(p, (5, 0)), width=1)
            word(f, shift(p, (-6, 0)), s, size=size, anchor='end')
        if xlabel:
            f.text(shift(self.P((a + b) / 2, c), (0, -32)), xlabel, size=14)
        if ylabel:
            f.text(shift(self.P(a, d), (0, 14)), ylabel, size=14)


def esym(f, pos, base, sub, sup, size=13, color=INK):
    """An italic letter with a subscript and a superscript stacked after it,
    such as e^W_1, starting at pos in a figure drawn in pixels; three plain
    text elements, which every renderer places alike."""
    f.text(pos, base, size=size, anchor='start', color=color)
    small = 0.68 * size
    x = 0.52 * size + 1
    f.text(shift(pos, (x, -0.32 * size)), sub, size=small, anchor='start',
           italic=False, color=color)
    f.text(shift(pos, (x, 0.42 * size)), sup, size=small, anchor='start',
           color=color)


def labelled(f, pos, text, symbol, size=13, gap=1):
    """Upright text ending at pos, followed by a symbol such as e^W_1."""
    f.text(pos, text, size=size, anchor='end')
    esym(f, shift(pos, (gap, 0)), *symbol, size=size)


def blend(c0, c1, t):
    a = [int(c0[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    return '#' + ''.join(f'{round(x + (y - x) * t):02x}' for x, y in zip(a, b))


def heat(panel, fn, nx, ny, top, levels, low='#ffffff', high='#3b82f6',
         bands=10):
    """Shade the panel by the values of fn on an nx by ny grid of cells, in
    `bands` shades from `low` to `high` (by the square root of value/top);
    cells of one shade are merged into rectangles. Then draw the contour
    lines of fn at `levels`."""
    (a, b), (c, d) = panel.xlim, panel.ylim
    dx, dy = (b - a) / nx, (d - c) / ny
    rows = []
    for j in range(ny):
        y = c + (j + 0.5) * dy
        shades = [min(bands - 1, int(bands * math.sqrt(
            max(fn(a + (i + 0.5) * dx, y), 0.0) / top))) for i in range(nx)]
        runs, start = [], 0
        for i in range(1, nx + 1):
            if i == nx or shades[i] != shades[start]:
                runs.append((start, i, shades[start]))
                start = i
        rows.append(runs)
    open_rects = {}

    def emit(key, j0, j1):
        i0, i1, k = key
        (x0, y0), (x1, y1) = (panel.f.p(*panel.P(a + i0 * dx, c + j1 * dy)),
                              panel.f.p(*panel.P(a + i1 * dx, c + j0 * dy)))
        panel.f.add(f'<rect x="{x0:.1f}" y="{y0:.1f}" '
                    f'width="{x1 - x0 + 0.3:.1f}" height="{y1 - y0 + 0.3:.1f}" '
                    f'fill="{blend(low, high, k / (bands - 1))}"/>')
    for j, runs in enumerate(rows + [[]]):
        keys = set(runs)
        for key in list(open_rects):
            if key not in keys:
                emit(key, open_rects.pop(key), j)
        for key in runs:
            open_rects.setdefault(key, j)
    # contour lines by marching squares on the nodes
    vals = [[fn(a + i * dx, c + j * dy) for i in range(nx + 1)]
            for j in range(ny + 1)]
    for lev in levels:
        segs = []
        for j in range(ny):
            for i in range(nx):
                corners = [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)]
                pts = []
                for k in range(4):
                    p, q = corners[k], corners[(k + 1) % 4]
                    vp, vq = vals[p[1]][p[0]], vals[q[1]][q[0]]
                    if (vp - lev) * (vq - lev) < 0:
                        s = (lev - vp) / (vq - vp)
                        pts.append((a + (p[0] + s * (q[0] - p[0])) * dx,
                                    c + (p[1] + s * (q[1] - p[1])) * dy))
                if len(pts) == 2:
                    segs.append((pts[0], pts[1]))
                elif len(pts) == 4:
                    segs.append((pts[0], pts[1]))
                    segs.append((pts[2], pts[3]))
        for chain in chains(segs):
            polyline(panel.f, [panel.P(*q) for q in chain], stroke=INK,
                     width=0.8)


def chains(segs):
    """Join segments that share end points into polylines."""
    key = lambda p: (round(p[0], 9), round(p[1], 9))
    ends = {}
    for k, (p, q) in enumerate(segs):
        ends.setdefault(key(p), []).append(k)
        ends.setdefault(key(q), []).append(k)
    used = [False] * len(segs)
    out = []
    for k in range(len(segs)):
        if used[k]:
            continue
        used[k] = True
        chain = [segs[k][0], segs[k][1]]
        for forward in (True, False):
            while True:
                tip = chain[-1] if forward else chain[0]
                nxt = [m for m in ends.get(key(tip), []) if not used[m]]
                if not nxt:
                    break
                m = nxt[0]
                used[m] = True
                p, q = segs[m]
                other = q if key(p) == key(tip) else p
                if forward:
                    chain.append(other)
                else:
                    chain.insert(0, other)
        out.append(chain)
    return out


# ---------------------------------------------------------------------------
# Figure E.1: the edge of the west tail.

def oriented(t, a, b):
    """The centre of Q_t(a, b)."""
    return add(scale(u(t), a), scale(u(t + PI / 2), b))


def west_tail_configuration(v=11 / 25, s=1 / 20, d=PI / 4):
    """C at (c0, 0); W and S separated from C along their own axes (tight),
    with their far vertices on the circle of radius R0; D separated from W
    along the secondary axis of W and from S along that of S (tight)."""
    cx, cy = C0, 0.0
    aW = tau(v) - cx * math.cos(v) + cy * math.sin(v)
    bW = -(math.sqrt(Q0 - (aW + 0.5) ** 2) - 0.5)
    aS = tau(s) + cx * math.sin(s) - cy * math.cos(s)
    bS = math.sqrt(Q0 - (aS + 0.5) ** 2) - 0.5
    # a sin(v+d) + b cos(v+d) = tau(v+d) + bW; a cos(d-s) - b sin(d-s) = tau(d-s) - bS
    m11, m12, r1 = math.sin(v + d), math.cos(v + d), tau(v + d) + bW
    m21, m22, r2 = math.cos(d - s), -math.sin(d - s), tau(d - s) - bS
    det = m11 * m22 - m12 * m21
    aD = (r1 * m22 - m12 * r2) / det
    bD = (m11 * r2 - m21 * r1) / det
    # the four separations of Lemma E.1, all tight
    checks = [aW + cx * math.cos(v) - cy * math.sin(v) - tau(v),
              aS - cx * math.sin(s) + cy * math.cos(s) - tau(s),
              aD * math.sin(v + d) + bD * math.cos(v + d) - bW - tau(v + d),
              bS + aD * math.cos(d - s) - bD * math.sin(d - s) - tau(d - s)]
    assert max(abs(x) for x in checks) < 1e-12
    return (cx, cy), (aW, bW), (aD, bD), (aS, bS)


def west_tail():
    v, s, d = 11 / 25, 1 / 20, PI / 4
    c, (aW, bW), (aD, bD), (aS, bS) = west_tail_configuration(v, s, d)
    tW, tD, tS = PI - v, PI + d, 1.5 * PI + s
    cW, cD, cS = oriented(tW, aW, bW), oriented(tD, aD, bD), oriented(tS, aS, bS)
    far = max(square_corners(cD, deg(tD)), key=lambda p: math.hypot(*p))
    rfar = math.hypot(*far)
    assert 1.78 < rfar < 1.80 and rfar > R0
    for p in square_corners(cW, deg(tW)) + square_corners(cS, deg(tS)):
        assert math.hypot(*p) < R0 + 1e-9
    f = Figure(-2.0, 1.95, -2.0, 1.85, 118)
    f.circle((0, 0), R0, stroke=FAINT, width=1.3)
    for name, cen, t in (('C', c, 0.0), ('W', cW, tW), ('S', cS, tS),
                         ('D', cD, tD)):
        fill, stroke = STYLE[name]
        f.square(cen, deg(t), fill=fill, stroke=stroke, width=1.6)
    for piece in outside_disk_pieces(square_corners(cD, deg(tD)), R0):
        f.polygon(piece, fill=RED, stroke='none', width=0, opacity=0.45)
    # the separating lines, through the contact sides
    e1W, e2W, e1S, e2S = u(tW), u(tW + PI / 2), u(tS), u(tS + PI / 2)

    def sep(normal, level, along, around, half=0.62):
        foot = scale(normal, level)
        base = add(foot, scale(along, dot2(around, along)))
        f.line(add(base, scale(along, -half)), add(base, scale(along, half)),
               stroke=INK, width=1.3, dash='6 4')
    sep(e1W, dot2(e1W, cW) - 0.5, e2W, cW)
    sep(e2W, dot2(e2W, cW) + 0.5, e1W, cW)
    sep(e2S, dot2(e2S, cS) - 0.5, e1S, cS)
    sep(e1S, dot2(e1S, cS) - 0.5, e2S, cS)
    # the forces of the stress
    l1, l2, l3, l4 = 8 / 15, 1 / 5, 1 / 6, 1 / 10
    forces = {'W': add(scale(e1W, l1), scale(e2W, -l3)),
              'D': add(scale(e2W, l3), scale(e2S, -l4)),
              'S': add(scale(e1S, l2), scale(e2S, l4)),
              'C': add(scale(e1W, -l1), scale(e1S, -l2))}
    k = 1.15
    for name, cen in (('C', c), ('W', cW), ('D', cD), ('S', cS)):
        F = forces[name]
        arrow(f, cen, add(cen, scale(F, k)), color=INK, width=1.6)
        f.dot(cen, r=2.6)
    f.dot((0, 0), r=2.4, fill=FAINT)
    f.text((-0.05, 0.12), 'o', size=14, color=FAINT)
    f.dot(far, r=4, fill=RED)
    f.text(shift(far, (-0.1, -0.17)), f'{rfar:.2f}', size=13, color=RED,
           italic=False, anchor='middle')
    f.text(shift(c, (0.25, 0.3)), 'C', size=17)
    f.text(shift(cW, (-0.12, 0.28)), 'W', size=17, color=PURPLE)
    f.text(shift(cS, (0.3, -0.18)), 'S', size=17, color=PINK)
    f.text(shift(cD, (-0.32, 0.05)), 'D', size=17, color=CYAN)
    f.text((1.27, 1.44), sb('R', '0'), size=16, color=FAINT)
    f.text((-1.95, -1.88), 'v = 11/25,  s = 1/20,  d = π/4', size=13,
           anchor='start')
    save(f, 'appendix-e/west-tail', 'C, W, S and D at the edge of the west tail: W '
         'and S touch C along their own axes and the circle of radius R0 '
         'with their far vertices, D touches W and S along their secondary '
         'axes, and the far vertex of D lies outside the circle; arrows show '
         'the forces of the stress')


# ---------------------------------------------------------------------------
# Figure E.2: the boxes of the west minorant.

def west_minorant_lower(k, v, x, d):
    """The Taylor lower bound of m_k(v, x, d) (Lemma E.3, Table E.1)."""
    be, ga, mu, nu = Fr(8, 15), Fr(1, 5), Fr(1, 6), Fr(1, 10)
    sNU = (ga ** 2 + nu ** 2 + Fr(2, 9) ** 2) / (2 * Fr(2, 9))
    dI = (mu ** 2 + nu ** 2 + Fr(6, 25) ** 2) / (2 * Fr(6, 25))
    dS = mu * nu / Fr(6, 25)
    K = 1 - RBAR * (Fr(5588, 10000) + sNU) - RHOBAR * dI
    sig = [1, 1, -1][k]
    g = [ga / 2, ga, ga][k]
    hh = [ga * (Fr(1, 2) + Fr(1128, 10000)), Fr(9, 100) * RBAR,
          ga - Fr(9, 100) * RBAR][k]
    off = [0, -ga / 2, -ga / 2][k]
    v, x, d = Fr(v), Fr(x), Fr(d)
    return (K + off + be * (Fr(1, 2) - CBAR) * c6(v) + be / 2 * sin_below(v)
            + g * c6(x) + hh * sin_below(x)
            + mu / 2 * (c6(v + d) + sin_below(v + d))
            + nu / 2 * (c6(d - sig * x) + sin_below(d - sig * x))
            - RHOBAR * dS * sin_above(v + sig * x))


def west_box():
    W, Hh = 980, 330
    f = Figure(0, W, 0, Hh, 1, pad=6)
    vs, ds = (Fr(11, 25), Fr(2, 3)), (Fr(1, 2), Fr(11, 14))
    xmax = [Fr(3, 5), Fr(3, 5), Fr(2, 5)]
    titles = ['k = 0: own axis', 'k = 1: south side, s ≥ 0',
              'k = 2: south side, s ≤ 0']
    low = None
    for k in range(3):
        ox, oy = 72 + 306 * k, 70

        def P(p, q, r):
            return (ox + 150 * p + 62 * q, oy + 165 * r + 52 * q)
        vals = {}
        for i, v in enumerate(vs):
            for j, x in enumerate((Fr(0), xmax[k])):
                for l, d in enumerate(ds):
                    val = west_minorant_lower(k, v, x, d)
                    assert val > 0
                    vals[(i, j, l)] = float(val)
                    if low is None or val < low[0]:
                        low = (val, k, i, j, l)
        # the twelve edges; the three at the hidden corner (0, 1, 0) dashed
        for a in range(2):
            for b in range(2):
                for axis in range(3):
                    p0 = [a, b]
                    p0.insert(axis, 0)
                    p1 = [a, b]
                    p1.insert(axis, 1)
                    hidden = [0, 1, 0] in (p0, p1)
                    f.line(P(*p0), P(*p1), stroke=INK, width=1.3,
                           dash='4 3' if hidden else None)
        for (i, j, l), val in vals.items():
            p = P(i, j, l)
            tight = (i, j, l) == (1, 0, 1)
            f.dot(p, r=3.6, fill=ORANGE if tight else INK)
            dxp = 10 if i == 1 else -10
            anchor = 'start' if i == 1 else 'end'
            dyp = 11 if l == 1 else -11
            if tight:
                dyp = -13
            f.text(shift(p, (dxp, dyp)), f'{math.floor(val * 1e5) / 1e5:.5f}',
                   size=12, italic=False, anchor=anchor,
                   color=ORANGE if tight else INK)
        word(f, (ox + 105, 22), titles[k], size=13)
        f.text(shift(P(0.5, 0, 0), (0, -16)), 'v', size=14)
        f.text(shift(P(1, 0.5, 0), (12, -4)), 'x', size=14, anchor='start')
        f.text(shift(P(0, 0, 0.5), (-10, 0)), 'd', size=14, anchor='end')
    assert low[1:] == (0, 1, 0, 1)
    save(f, 'appendix-e/west-box', 'The three boxes of the west minorant with the '
         'Taylor lower bounds at their corners, all positive; the corner '
         'v = 2/3, x = 0, d = 11/14 is the tight one')


# ---------------------------------------------------------------------------
# Figure E.3: the tangents of the length of the force on W.

def south_tangents():
    W, Hh = 580, 480
    f = Figure(0, W, 0, Hh, 1, pad=4)
    length = lambda v: math.sqrt(13 / 25 - 12 / 25 * math.sin(v))
    tangent = lambda c: (lambda v: (13 / 25 - 12 / 25 * math.sin(v) + c * c)
                         / (2 * c))
    t1, t2 = tangent(18 / 25), tangent(21 / 25)
    used = lambda v: t2(v) if v < -0.15 else t1(v)
    ticks = [(-0.4, '−2/5'), (-0.15, '−3/20'), (0, '0'), (0.4, '2/5')]
    top = Panel(f, 70, 220, 470, 230, (-0.4, 0.4), (0.55, 0.88))
    top.frame(ticks, [(0.6, '0.6'), (0.7, '0.7'), (0.8, '0.8')])
    top.curve(t1, -0.4, 0.4, stroke=ORANGE, width=1.2, dash='6 4')
    top.curve(t2, -0.4, 0.4, stroke=GREEN, width=1.2, dash='6 4')
    top.curve(used, -0.4, -0.1501, stroke=ORANGE, width=3.0)
    top.curve(used, -0.15, 0.4, stroke=ORANGE, width=3.0)
    top.curve(length, -0.4, 0.4, stroke=BLUE, width=1.8)
    f.line(top.P(-0.15, 0.55), top.P(-0.15, 0.88), stroke=FAINT, width=1,
           dash='2 3')
    # legend
    lx, ly = top.P(0.08, 0.86)
    entries = [(BLUE, None, 1.8, 'the length'),
               (ORANGE, '6 4', 1.2, 'tangent at c = 18/25'),
               (GREEN, '6 4', 1.2, 'tangent at c = 21/25'),
               (ORANGE, None, 3.0, 'the bound used')]
    for k, (col, dash, wd, text) in enumerate(entries):
        y = ly - 9 - 19 * k
        f.line((lx, y), (lx + 34, y), stroke=col, width=wd, dash=dash)
        word(f, (lx + 42, y), text, size=12, anchor='start')
    bot = Panel(f, 70, 45, 470, 125, (-0.4, 0.4), (0, 16))
    bot.frame(ticks, [(0, '0'), (5, '5'), (10, '10'), (15, '15')],
              xlabel='v')
    bot.curve(lambda v: 1e3 * (t1(v) - length(v)), -0.4, 0.4, stroke=ORANGE,
              width=1.2, dash='6 4')
    bot.curve(lambda v: 1e3 * (t2(v) - length(v)), -0.4, 0.4, stroke=GREEN,
              width=1.2, dash='6 4')
    bot.curve(lambda v: 1e3 * (used(v) - length(v)), -0.4, -0.1501,
              stroke=ORANGE, width=3.0)
    bot.curve(lambda v: 1e3 * (used(v) - length(v)), -0.15, 0.4,
              stroke=ORANGE, width=3.0)
    f.line(bot.P(-0.15, 0), bot.P(-0.15, 16), stroke=FAINT, width=1,
           dash='2 3')
    word(f, shift(bot.P(-0.4, 16), (0, 13)), 'excess of the tangents over '
         'the length, times 1000', size=12, anchor='start')
    assert abs(t1(-0.4) - length(-0.4) - 0.0101) < 1e-4
    assert max(used(-0.4 + 0.8 * k / 400) - length(-0.4 + 0.8 * k / 400)
               for k in range(401)) < 0.0143
    save(f, 'appendix-e/south-tangents', 'The length of the force on W in the '
         'south tail against its tangent majorants at c = 18/25 and c = 21/25, '
         'and their excess; the bound used switches at v = -3/20')


# ---------------------------------------------------------------------------
# Figure E.4: the narrow cone at the corner v = s = 11/25.

def south_cone():
    g = 11 / 25
    A1 = 0.4 * math.sin(g) + 0.3 * math.cos(g)
    B1 = 0.4 * math.cos(g) + 0.3 * math.sin(g)
    UV = lambda d: (A1 * math.cos(d) + B1 * math.sin(d),
                    B1 * math.cos(d) - A1 * math.sin(d))
    ds = [0.5 + (11 / 14 - 0.5) * k / 100 for k in range(101)]
    for d in ds:
        U, V = UV(d)
        assert 0.6 <= U <= 0.7 and 0 <= V <= 0.4 * U
    W, Hh = 520, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 60, 40, 430, 270, (0, 0.8), (-0.1, 0.4))
    # the part of the cone used
    p_band = [p.P(0.6, -0.1), p.P(0.7, -0.1), p.P(0.7, 0.28), p.P(0.6, 0.24)]
    f.polygon(p_band, fill=FILLS[5], stroke='none', width=0)
    polyline(f, [p.P(0, 0), p.P(0.8, 0.32)], stroke=CYAN, width=1.3,
             dash='6 4')
    polyline(f, [p.P(0, 0), p.P(0.25, -0.1)], stroke=CYAN, width=1.3,
             dash='6 4')
    p.frame([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (0.6, '3/5'),
             (0.7, '7/10')], [(-0.1, '−0.1'), (0, '0'), (0.2, '0.2'),
                              (0.4, '0.4')], xlabel='U')
    f.line(p.P(0, 0), p.P(0.8, 0), stroke=FAINT, width=1)
    for x in (0.6, 0.7):
        f.line(p.P(x, -0.1), p.P(x, 0.4), stroke=FAINT, width=1, dash='3 3')
    polyline(f, [p.P(*UV(d)) for d in ds], stroke=BLUE, width=3)
    for d, s, off in ((0.5, 'd = 1/2', (-9, -16)), (11 / 14, 'd = 11/14',
                                                      (10, -6))):
        q = p.P(*UV(d))
        f.dot(q, r=3.4, fill=BLUE)
        f.text(shift(q, off), s, size=12, color=BLUE,
               anchor='end' if off[0] < 0 else 'start')
    f.text(p.P(0.33, 0.215), 'V = 2U/5', size=12, color=CYAN)
    f.text(shift(p.P(0, 0.4), (14, 10)), 'V', size=14)
    save(f, 'appendix-e/south-cone', 'The force (U, V) on D at the corner '
         'v = s = 11/25 of the south tail, for d from 1/2 to 11/14, inside '
         'the part of the narrow cone |V| at most 2U/5 with U between 3/5 '
         'and 7/10')


# ---------------------------------------------------------------------------
# The value and the gap of the pair N, W (Definition 9.48).

MODEL_FACETS = ('wF', 'nS')


def pair_forces(no, wo, f, n, w):
    q = n - w
    kN = (1.0, 0.0) if no else (math.cos(n), -math.sin(n))
    kW = (1.0, 0.0) if wo else (math.cos(w), -math.sin(w))
    phi = {'wF': (-math.sin(q), -math.cos(q)), 'wS': (math.cos(q), -math.sin(q)),
           'nF': (1.0, 0.0), 'nS': (0.0, -1.0)}[f]
    psi = {'wF': (1.0, 0.0), 'wS': (0.0, 1.0), 'nF': (-math.sin(q), math.cos(q)),
           'nS': (math.cos(q), math.sin(q))}[f]
    FN = add(kN, scale(phi, R_STAR))
    FW = add(kW, scale(psi, R_STAR), (0.0, -M_STAR))
    return FN, FW


def line_l(w):
    return 18 / 25 * max(-w, 0) - 13 / 50 * max(w, 0)


def pair_gap(no, wo, f, n, w):
    FN, FW = pair_forces(no, wo, f, n, w)
    V = lambda F: R6 * math.hypot(*F) - (F[0] - F[1]) / 2
    BN = V(FN) if f in MODEL_FACETS else RHO * math.hypot(*FN)
    P = ((C0 * (max(math.sin(n), 0) + 1 - math.cos(n)) if no else 0)
         + (C0 * max(math.sin(w), 0) if wo else 0))
    value = tau(n) + tau(w) + R_STAR * tau(n - w) + M_STAR / 2 - BN - V(FW) - P
    return value - BETA_STAR - line_l(w) - abs(n) / 1000


def pair_domain_bounds(no, wo):
    n0, n1 = (-3 / 10, 5 / 12) if no else (-1 / 4, 1 / 4)
    w0, w1 = (-11 / 25, 0.0) if wo else (-2 / 5, 2 / 5)
    return n0, n1, w0, w1


# Figure E.5: the forces along lines.

def pair_turning():
    W, Hh = 820, 430
    f = Figure(0, W, 0, Hh, 1, pad=4)
    # left: F_W along a line in w, W on its matching side, facet -e^W_1
    s1, o1 = 200, (80, 370)
    P1 = lambda p: (o1[0] + s1 * p[0], o1[1] + s1 * p[1])
    base = (R_STAR, -M_STAR)
    ws = [-0.4 + 0.8 * k / 120 for k in range(121)]
    tips = [add(base, u(-w)) for w in ws]
    lens = [math.hypot(*q) for q in tips]
    for w in ws:
        FN, FW = pair_forces(False, False, 'wF', 0.0, w)
        assert math.dist(FW, add(base, u(-w))) < 1e-12
    polyline(f, [P1(add(base, u(-w))) for w in
                 [-0.85 + 1.7 * k / 120 for k in range(121)]], stroke=FAINT,
             width=1, dash='3 3')
    polyline(f, [P1(q) for q in tips], stroke=PURPLE, width=3)
    arrow(f, P1((0, 0)), P1(base), color=FAINT, width=1.6)
    for w, lab in ((-0.4, 'w = −2/5'), (0.0, 'w = 0'), (0.4, 'w = 2/5')):
        q = add(base, u(-w))
        arrow(f, P1(base), P1(q), color=PURPLE, width=1.2)
        arrow(f, P1((0, 0)), P1(q), color=INK, width=1.4)
        f.dot(P1(q), r=3, fill=PURPLE)
        f.text(shift(P1(q), (9, 0)), lab, size=12, anchor='start',
               color=PURPLE)
    f.dot(P1((0, 0)), r=3)
    word(f, shift(P1((0, 0)), (8, 12)), 'centre of W', size=12,
         anchor='start')
    f.text(shift(P1(base), (-9, 0)), '(r*, −m*)', size=12, anchor='end',
           color=FAINT)
    labelled(f, (o1[0] + 270, 40), 'line in w, W on its matching side, '
             'facet −', ('e', '1', 'W'))
    word(f, (o1[0] + 160, 18), f'the length runs from {min(lens):.2f} to '
         f'{max(lens):.2f}', size=12)
    # right: F_W along a line in n, W on its own axis, facet e^N_1
    s2, o2 = 250, (455, 385)
    P2 = lambda p: (o2[0] + s2 * p[0], o2[1] + s2 * p[1])
    w0 = -0.2
    base2 = (1.0, -M_STAR)
    ns = [-0.3 + (5 / 12 + 0.3) * k / 120 for k in range(121)]
    turn = lambda n: scale(u(PI / 2 + n - w0), R_STAR)
    for n in ns:
        FN, FW = pair_forces(True, True, 'nF', n, w0)
        assert math.dist(FW, add(base2, turn(n))) < 1e-12
        assert dot2(base2, turn(n)) <= -R_STAR ** 2
    f.circle(P2(base2), s2 * R_STAR, stroke=FAINT, width=1, dash='3 3')
    polyline(f, [P2(add(base2, turn(n))) for n in ns], stroke=PURPLE, width=3)
    arrow(f, P2((0, 0)), P2(base2), color=FAINT, width=1.6)
    for n, lab in ((-0.3, 'n = −3/10'), (5 / 12, 'n = 5/12')):
        q = add(base2, turn(n))
        arrow(f, P2(base2), P2(q), color=PURPLE, width=1.2)
        arrow(f, P2((0, 0)), P2(q), color=INK, width=1.4)
        f.dot(P2(q), r=3, fill=PURPLE)
        f.text(shift(P2(q), (10, 6) if n < 0 else (-18, 12)), lab, size=12,
               anchor='start' if n < 0 else 'end', color=PURPLE)
    f.dot(P2((0, 0)), r=3)
    word(f, shift(P2((0, 0)), (8, 12)), 'centre of W', size=12,
         anchor='start')
    f.text(shift(P2(base2), (10, -10)), '(1, −m*)', size=12,
           anchor='start', color=FAINT)
    labelled(f, (o2[0] + 262, 40), 'line in n, W on its own axis, facet',
             ('e', '1', 'N'), gap=5)
    word(f, (o2[0] + 170, 18), 'the turning part points against the '
         'constant part', size=12)
    save(f, 'appendix-e/pair-turning', 'Two forces on W along lines of the sweep: '
         'a constant vector plus a turning vector, whose tip runs on a circle; '
         'on the right the turning part points against the constant part')


# Figure E.6: the domains, the sectors and the sweep.

def pair_domain():
    W, Hh = 640, 530
    f = Figure(0, W, 0, Hh, 1, pad=4)
    k = 280
    cells = [((True, False), (80, 255)), ((False, False), (410, 255)),
             ((True, True), (80, 55)), ((False, True), (410, 55))]
    names = {True: 'own', False: 'side'}
    for (no, wo), (ox, oy) in cells:
        n0, n1, w0, w1 = pair_domain_bounds(no, wo)
        P = lambda x, y: (ox + k * (x - n0), oy + k * (y - w0))
        rect = [P(n0, w0), P(n1, w0), P(n1, w1), P(n0, w1)]
        f.polygon(rect, fill='#f8fafc', stroke=INK, width=1.2)
        # sector boundaries
        f.line(P(0, w0), P(0, w1), stroke=FAINT, width=1, dash='4 3')
        f.line(P(n0, 0), P(n1, 0), stroke=FAINT, width=1, dash='4 3')
        z0, z1 = max(n0, w0), min(n1, w1)
        # the diagonal n = w, dashed outside the segment drawn thick
        f.line(P(z0, z0), P(z1, z1), stroke=INK, width=3)
        # the three lines in w
        for x in (n0, 0.0, n1):
            f.line(P(x, w0), P(x, w1), stroke=BLUE, width=2.2)
        # one line in n, with its cut points
        y = w0 + 0.62 * (w1 - w0)
        f.line(P(n0, y), P(n1, y), stroke=ORANGE, width=2.2)
        for x in (0.0, y):
            if n0 <= x <= n1:
                f.line(shift(P(x, y), (0, -6)), shift(P(x, y), (0, 6)),
                       stroke=ORANGE, width=2)
        pts = {(x, yy) for x in (n0, 0.0, n1) for yy in (w0, 0.0, w1)}
        pts |= {(z0, z0), (z1, z1)}
        for p in pts:
            f.dot(P(*p), r=3.6)
        f.text(shift(P((n0 + n1) / 2, w1), (0, 16)),
               f'N {names[no]}, W {names[wo]}', size=13)
        f.text(shift(P(n1, 0), (8, 0)), 'w = 0', size=11, anchor='start',
               color=FAINT)
        f.text(shift(P(0, w0), (0, -12)), 'n = 0', size=11, color=FAINT)
    save(f, 'appendix-e/pair-domain', 'The four domains of the pair estimate, cut '
         'into sign sectors by n = 0, w = 0 and n = w, with the diagonal, the '
         'three lines in w and a line in n of the sweep, and the points where '
         'the gap is checked')


# Figure E.7: the gap of the facets of the model.

def pair_gap_figure():
    W, Hh = 820, 320
    f = Figure(0, W, 0, Hh, 1, pad=4)
    no, wo = True, True
    n0, n1, w0, w1 = pair_domain_bounds(no, wo)
    levels = [0.01, 0.02, 0.04, 0.08, 0.16, 0.32]
    for idx, (fac, title) in enumerate((('wF', ('e', '1', 'W')),
                                        ('nS', ('e', '2', 'N')))):
        ox = 70 + 400 * idx
        pw = 320
        ph = pw * (w1 - w0) / (n1 - n0)
        p = Panel(f, ox, 60, pw, ph, (n0, n1), (w0, w1))
        fn = lambda x, y, fac=fac: pair_gap(no, wo, fac, x, y)
        heat(p, fn, 64, 40, 0.36, levels)
        p.frame([(-0.3, '−3/10'), (0, '0'), (5 / 12, '5/12')],
                [(-0.44, '−11/25'), (0, '0')], xlabel='n')
        f.text(shift(p.P(n0, w1), (-30, 12)), 'w', size=14)
        f.dot(p.P(0, 0), r=4, fill=RED)
        if fac == 'nS':
            g = pair_gap(no, wo, fac, 0.0, -11 / 25)
            assert 6.5e-4 < g < 6.7e-4
            f.dot(p.P(0, -11 / 25), r=4, fill=ORANGE)
            f.text(shift(p.P(0, -11 / 25), (10, 14)), f'G = {g:.5f}',
                   size=12, anchor='start')
        labelled(f, shift(p.P((n0 + n1) / 2, w1), (12, 20)), 'facet −',
                 title)
    # the gap is nonnegative on a finer grid and zero at the origin
    for fac in MODEL_FACETS:
        assert abs(pair_gap(no, wo, fac, 0.0, 0.0)) < 1e-12
        assert min(pair_gap(no, wo, fac, n0 + (n1 - n0) * i / 40,
                            w0 + (w1 - w0) * j / 40)
                   for i in range(41) for j in range(41)) > -1e-12
    save(f, 'appendix-e/pair-gap', 'The gap of the pair for N and W on their own '
         'axes, for the two facets of the model, as shaded maps with contour '
         'lines; it vanishes at the origin and nearly at n = 0, w = -11/25 '
         'for the second facet')


# ---------------------------------------------------------------------------
# Figure E.8: the support of the force on D.

def centre_region(n=90):
    """The boundary of the region (|a| + 1/2)^2 + (|b| + 1/2)^2 <= R6^2."""
    pts = []
    th0 = math.asin(0.5 / R6)
    for quad in range(4):
        sa = 1 if quad in (0, 3) else -1
        sb_ = 1 if quad in (0, 1) else -1
        for k in range(n + 1):
            t = th0 + (PI / 2 - 2 * th0) * k / n
            a, b = R6 * math.cos(t) - 0.5, R6 * math.sin(t) - 0.5
            pts.append((sa * a, sb_ * b))
    # order the points by angle about the origin
    pts.sort(key=lambda p: math.atan2(p[1], p[0]))
    return pts


def diagonal_support():
    W, Hh = 860, 430
    f = Figure(0, W, 0, Hh, 1, pad=4)
    s = 108
    alpha = math.asin(1 / (2 * R6))
    region = centre_region()
    cases = ((0.15, 'the cap case'), (0.5, 'the vertex case'))
    for idx, (delta, title) in enumerate(cases):
        o = (215 + 420 * idx, 215)
        P = lambda p: (o[0] + s * p[0], o[1] + s * p[1])
        f.circle(P((0, 0)), R6 * s, stroke=FAINT, width=1.2)
        f.polygon([P(q) for q in region], fill=GREY, stroke=FAINT, width=1)
        word(f, P((-0.55, 0.42)), 'centres', size=12, color=FAINT)
        f.line(P((-1.75, 0)), P((1.85, 0)), stroke=FAINT, width=0.8)
        corner = (RHO, 0.0)
        F = (math.cos(delta), -math.sin(delta))
        if 2 * R6 * abs(math.sin(delta)) <= 1:
            centre = corner
            work = RHO * math.cos(delta)
        else:
            centre = (R6 * math.cos(delta) - 0.5,
                      -(R6 * abs(math.sin(delta)) - 0.5))
            work = R6 - (math.cos(delta) + abs(math.sin(delta))) / 2
        # the support is attained at the centre drawn: check on the region
        best = max(dot2(F, q) for q in centre_region(400))
        assert abs(best - work) < 2e-5
        f.polygon([P(q) for q in square_corners(centre)], fill=FILLS[5],
                  stroke=CYAN, width=1.6, opacity=0.75)
        # the normals of the two arcs at the corner (rho*, 0)
        for tt in (-alpha, alpha):
            f.line(P(corner), P(add(corner, scale(u(tt), 0.6))), stroke=INK,
                   width=1, dash='4 3')
        f.dot(P(centre), r=3.4)
        arrow(f, P(centre), P(add(centre, scale(F, 0.8))), color=INK,
              width=1.8)
        if 2 * R6 * abs(math.sin(delta)) > 1:
            far = (centre[0] + 0.5, centre[1] - 0.5)
            assert abs(math.hypot(*far) - R6) < 1e-9
            f.dot(P(far), r=4, fill=RED)
        else:
            for q in ((centre[0] + 0.5, 0.5), (centre[0] + 0.5, -0.5)):
                assert abs(math.hypot(*q) - R6) < 1e-9
                f.dot(P(q), r=4, fill=RED)
        f.dot(P((0, 0)), r=2.6)
        f.text(shift(P((0, 0)), (-6, -12)), 'o', size=13)
        f.text(shift(P(corner), (-10, -11)), '(ρ*, 0)', size=12,
               anchor='end')
        f.text(shift(P(add(centre, scale(F, 0.8))), (6, -12)),
               f'δ = {delta:g}', size=12, anchor='start')
        word(f, (o[0], 408), title, size=13)
    save(f, 'appendix-e/diagonal-support', 'The support of the force on D in its '
         'frame: the region of possible centres, the force, and the best '
         'position of D, at the corner (rho*, 0) in the cap case and with a '
         'far vertex on the circle in the vertex case')


# ---------------------------------------------------------------------------
# Figure E.9: the vertex minorant.

def phi_min(t):
    """The least value of Phi(x, y, t) over y >= 0, x + y <= 11/25,
    x >= t - 2/7."""
    x0 = t - 2 / 7
    p = 0.919 - (math.cos(t) + math.sin(t)) / 2
    base = 1.5 * math.cos(t) + 0.5 * math.sin(t) - 1.577
    best = None
    for i in range(201):
        x = x0 + (11 / 25 - x0) * i / 200
        for y in (0.0, min(x, 11 / 25 - x), 11 / 25 - x):
            val = base + 9 / 25 * max(x, y) - p * y
            best = val if best is None else min(best, val)
    return best


def vertex_minorant():
    W, Hh = 600, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 70, 50, 500, 250, (0.29, 0.75), (-0.002, 0.06))
    p.frame([(0.29, '0.29'), (0.44, '0.44'), (0.5, '0.5'), (0.75, '0.75')],
            [(0, '0'), (0.02, '0.02'), (0.04, '0.04'), (0.06, '0.06')],
            xlabel='t')
    f.line(p.P(0.29, 0), p.P(0.75, 0), stroke=FAINT, width=1)
    pf = lambda l: 0.919 - (math.cos(l) + math.sin(l)) / 2
    base = lambda t: 1.5 * math.cos(t) + 0.5 * math.sin(t) - 1.577
    pieces = [(0.29, 0.44, lambda t, l=0.29: base(t) + (0.36 - pf(l)) *
               (t - 2 / 7)),
              (0.44, 0.5, lambda t, l=0.44: base(t) + (0.36 - pf(l)) *
               (t - 2 / 7)),
              (0.5, 0.75, lambda t, l=0.5: base(t) + (0.36 + pf(l)) *
               (t - 2 / 7) - 0.44 * pf(l))]
    p.curve(phi_min, 0.29, 2 / 7 + 11 / 25, stroke=BLUE, width=2)
    for a, b, F in pieces:
        p.curve(F, a, b, stroke=ORANGE, width=2.2)
        for t in (a, b):
            assert F(t) > 0
            f.dot(p.P(t, F(t)), r=3.2, fill=ORANGE)
        f.line(p.P(a, -0.002), p.P(a, 0.06), stroke=FAINT, width=0.8,
               dash='2 3')
        for k in range(41):
            t = a + (b - a) * k / 40
            if t <= 2 / 7 + 11 / 25:
                assert F(t) <= phi_min(t) + 1e-9
    word(f, p.P(0.62, 0.047), 'least value of Φ', size=12, color=BLUE)
    word(f, p.P(0.66, 0.012), 'the bounds F', size=12, color=ORANGE)
    save(f, 'appendix-e/vertex-minorant', 'The least value of the vertex minorant '
         'over the admissible x and y, against the three concave lower bounds '
         'of Lemma E.20 on their pieces, all positive')


# ---------------------------------------------------------------------------
# Figure E.10: the remainder of the turned square.

def remainder(w, s, d):
    b = (w - s) / 2
    dl = d - PI / 4 - (w + s) / 2
    L = K_STAR * (math.cos(b) - math.sin(b))
    if 2 * R6 * abs(math.sin(dl)) <= 1:
        sig = RHO * L * math.cos(dl)
    else:
        sig = L * (R6 - (math.cos(dl) + abs(math.sin(dl))) / 2)
    om = lambda t: (abs(math.cos(t)) + abs(math.sin(t))) / 2
    Delta = M_STAR * (om(d - w) + om(d - s)) - sig
    return line_l(w) + line_l(-s) + Delta + 2 * BETA_STAR


def diagonal_remainder():
    W, Hh = 900, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    d0 = math.asin(1 / (2 * R6))
    for idx, (d, title) in enumerate(((PI / 4, 'd = π/4'), (0.65, 'd = 0.65'),
                                      (0.5, 'd = 1/2'))):
        ox = 55 + 290 * idx
        p = Panel(f, ox, 50, 240, 240, (-0.44, 0.4), (-0.4, 0.44))
        fn = lambda w, s, d=d: remainder(w, s, d)
        heat(p, fn, 42, 42, 0.5, [0.05 * j for j in range(1, 10)])
        # the cap band |delta| <= d0: w + s = 2 (d - pi/4 -+ d0)
        for sgn in (1, -1):
            c = 2 * (d - PI / 4 - sgn * d0)
            pts = []
            for k in range(201):
                w = -0.44 + 0.84 * k / 200
                s = c - w
                if -0.4 <= s <= 0.44:
                    pts.append(p.P(w, s))
            if len(pts) > 1:
                polyline(f, pts, stroke=RED, width=1.4, dash='6 4')
        p.frame([(-0.44, '−11/25'), (0, '0'), (0.4, '2/5')],
                [(-0.4, '−2/5'), (0, '0'), (0.44, '11/25')], xlabel='w')
        f.text(shift(p.P(-0.44, 0.44), (-26, 12)), 's', size=14)
        if abs(d - PI / 4) < 1e-12:
            assert abs(remainder(0, 0, d)) < 1e-12
            f.dot(p.P(0, 0), r=4, fill=RED)
        f.text(shift(p.P(-0.02, 0.44), (0, 18)), title, size=13)
        mn = min(remainder(-0.44 + 0.84 * i / 60, -0.4 + 0.84 * j / 60, d)
                 for i in range(61) for j in range(61))
        assert mn > -1e-12
    save(f, 'appendix-e/diagonal-remainder', 'The remainder of the turned square '
         'over w and s for three values of d, as shaded maps with contour '
         'lines and the dashed boundaries of the cap case; it vanishes only '
         'at the model')


def main():
    west_tail()
    west_box()
    south_tangents()
    south_cone()
    pair_turning()
    pair_domain()
    pair_gap_figure()
    diagonal_support()
    vertex_minorant()
    diagonal_remainder()


if __name__ == '__main__':
    main()

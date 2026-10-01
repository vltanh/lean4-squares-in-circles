#!/usr/bin/env python3
"""Draw the figures of Appendix E (docs/proof/appendix-e.md), six squares: the
tails and the stress of the model, in docs/proof/figures/appendix-e/.

    python3 scripts/figures/fig_appe.py

Every figure is computed from the functions and constants of the appendix:
the cases of the tails, the stresses of the two tails at their edges (solved
from the separating inequalities of Lemma E.1) and their minorants (evaluated
at the corners with the Taylor polynomials, in exact rational arithmetic, as
in the tables), the bounds at the hardest corner of the south tail, the
edges, the value and the gap of the pair N, W of Definition 9.48, the forces
and the gap along the lines of the sweep, the errors of the Taylor
polynomials, the force on the turned square D and its support, the cap case
along one line, the vertex minorant and the remainder of Definition 9.51.
Shaded maps are drawn as one path per contour level, so the files stay small.
"""
import math
import re
from fractions import Fraction as Fr

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, u, shift, sb, subsup)
from fig_front import (arrow, polyline, word, outside_disk_pieces, it,
                       open_dot, interiors_meet, vtext)

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


def labelled(f, pos, text, symbol, size=15):
    """A title centred at pos: upright text (italic variables marked with
    it()) followed by a symbol such as e^W_1, given as ('e', '1', 'W')."""
    base, sub, sup = symbol
    word(f, pos, text + subsup(it(base), sub, it(sup), size), size=size)


def text_width(markup, size):
    """Estimated width in pixels of a label with tspans (0.52 em per
    character, each run at its own font size)."""
    width = 0.0
    for m in re.finditer(r'<tspan([^>]*)>([^<]*)</tspan>|([^<]+)', markup):
        attrs, inner, plain = m.groups()
        if plain is not None:
            width += 0.52 * size * len(plain)
        else:
            fs = re.search(r'font-size="([0-9.]+)"', attrs)
            width += 0.52 * (float(fs.group(1)) if fs else size) * len(inner)
    return width


def star(base, after='', size=13):
    """An italic letter with the subscript *, such as r_*, as markup for
    upright text; `after` is set on the base line after it."""
    return sb(it(base), '*', after, size)


def blend(c0, c1, t):
    a = [int(c0[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    return '#' + ''.join(f'{round(x + (y - x) * t):02x}' for x, y in zip(a, b))


def band_colour(k, levels, low='#ffffff', high='#3b82f6'):
    """The colour of band k (values between levels[k-1] and levels[k])."""
    return blend(low, high, k / len(levels))


def region_loops(tris, lev):
    """The boundary of the region where the linear interpolant is >= lev,
    over triangles given counterclockwise as points (x, y, value): the
    edges of the pieces of the triangles in the region, less the edges
    shared by two pieces, chained into closed loops (counterclockwise
    around the region, clockwise around its holes)."""
    key = lambda p: (round(p[0], 9), round(p[1], 9))
    edges = {}
    for tri in tris:
        if max(t[2] for t in tri) < lev:
            continue
        poly = []
        for m in range(3):
            p, r = tri[m], tri[(m + 1) % 3]
            if p[2] >= lev:
                poly.append(p)
            if (p[2] >= lev) != (r[2] >= lev):
                s = (lev - p[2]) / (r[2] - p[2])
                poly.append((p[0] + s * (r[0] - p[0]),
                             p[1] + s * (r[1] - p[1]), lev))
        pts = []
        for p in poly:
            if not pts or key(p) != key(pts[-1]):
                pts.append(p)
        if len(pts) > 1 and key(pts[0]) == key(pts[-1]):
            pts.pop()
        for m in range(len(pts)):
            p, r = pts[m], pts[(m + 1) % len(pts)]
            back = (key(r), key(p))
            if back in edges:
                del edges[back]
            else:
                edges[(key(p), key(r))] = (p, r)
    out = {}
    for (kp, kr), (p, r) in edges.items():
        out.setdefault(kp, []).append((kr, p))
    loops = []
    while out:
        k0 = next(iter(out))
        loop, k = [], k0
        while k in out:
            kr, p = out[k].pop()
            if not out[k]:
                del out[k]
            loop.append(p)
            k = kr
        # drop the points in the middle of straight runs
        simple = []
        for m, p in enumerate(loop):
            a, r = loop[m - 1], loop[(m + 1) % len(loop)]
            cross = (p[0] - a[0]) * (r[1] - p[1]) - (p[1] - a[1]) * (r[0] - p[0])
            if abs(cross) > 1e-12:
                simple.append(p)
        if len(simple) >= 3:
            loops.append(simple)
    return loops


def heat(panel, fn, nx, ny, levels):
    """Shade the panel by the bands of fn between the contour `levels`
    (band k holds the values between levels[k-1] and levels[k]) and draw
    the contour lines, on an nx by ny grid of cells cut into triangles,
    with fn interpolated linearly on each. The bands are painted in turn:
    the region where fn >= levels[k-1], in the colour of band k, over the
    previous ones; so the shading meets the contour lines."""
    (a, b), (c, d) = panel.xlim, panel.ylim
    dx, dy = (b - a) / nx, (d - c) / ny
    vals = [[fn(a + i * dx, c + j * dy) for i in range(nx + 1)]
            for j in range(ny + 1)]
    f = panel.f
    q = lambda x, y: f.p(*panel.P(x, y))
    (x0, y0), (x1, y1) = q(a, d), q(b, c)
    f.add(f'<rect x="{x0:.1f}" y="{y0:.1f}" width="{x1 - x0:.1f}" '
          f'height="{y1 - y0:.1f}" fill="{band_colour(0, levels)}"/>')
    corner = lambda i, j: (a + i * dx, c + j * dy, vals[j][i])
    tris = []
    for j in range(ny):
        for i in range(nx):
            tris.append((corner(i, j), corner(i + 1, j), corner(i + 1, j + 1)))
            tris.append((corner(i, j), corner(i + 1, j + 1), corner(i, j + 1)))
    for k, lev in enumerate(levels, 1):
        loops = region_loops(tris, lev)
        if loops:
            col = band_colour(k, levels)
            d_attr = ''.join('M' + 'L'.join('{:.1f} {:.1f}'.format(*q(x, y))
                                            for x, y, _ in loop) + 'Z'
                             for loop in loops)
            f.add(f'<path d="{d_attr}" fill="{col}" stroke="{col}" '
                  f'stroke-width="0.4" stroke-linejoin="round"/>')
    # the contour lines, on the same triangles: in each triangle the level
    # set of the linear interpolant is one segment
    for lev in levels:
        segs = []
        for j in range(ny):
            for i in range(nx):
                for tri in (((i, j), (i + 1, j), (i + 1, j + 1)),
                            ((i, j), (i + 1, j + 1), (i, j + 1))):
                    pts = []
                    for k in range(3):
                        p, q = tri[k], tri[(k + 1) % 3]
                        vp, vq = vals[p[1]][p[0]], vals[q[1]][q[0]]
                        if (vp - lev) * (vq - lev) < 0:
                            s = (lev - vp) / (vq - vp)
                            pts.append((a + (p[0] + s * (q[0] - p[0])) * dx,
                                        c + (p[1] + s * (q[1] - p[1])) * dy))
                    if len(pts) == 2:
                        segs.append((pts[0], pts[1]))
        for chain in chains(segs):
            polyline(panel.f, [panel.P(*q) for q in chain], stroke=INK,
                     width=0.8)


def heat_legend(f, x0, y0, levels, size=12, cell=34, fmt='{:g}'):
    """A row of the band colours of heat(), left to right from x0 at
    height y0, with the levels written at the boundaries between them."""
    for k in range(len(levels) + 1):
        f.polygon([(x0 + k * cell, y0), (x0 + (k + 1) * cell, y0),
                   (x0 + (k + 1) * cell, y0 + 12), (x0 + k * cell, y0 + 12)],
                  fill=band_colour(k, levels), stroke=FAINT, width=0.6)
    for k, lev in enumerate(levels):
        f.text((x0 + (k + 1) * cell, y0 - 10), fmt.format(lev), size=size,
               italic=False)


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
# The cases of Section E.1 in the plane of the angles v and s.

def tails_map():
    W, Hh = 700, 372
    f = Figure(0, W, 0, Hh, 1, pad=4)
    lim = (-0.48, 0.74)
    sticks = [(-0.4, '−2/5'), (0, '0'), (0.44, '11/25'), (2 / 3, '2/3')]
    panels = (('on its own axis', (0, 2 / 3),
               [(0, '0'), (0.44, '11/25'), (2 / 3, '2/3')],
               [((11 / 25, 2 / 3), (-2 / 5, 3 / 5), 1, 'E.4'),
                ((0, 11 / 25), (11 / 25, 2 / 3), 3, 'E.6')]),
              ('on the west side', (-2 / 5, 2 / 5),
               [(-0.4, '−2/5'), (0, '0'), (0.4, '2/5')],
               [((-2 / 5, 2 / 5), (11 / 25, 2 / 3), 2, 'E.5')]))
    for idx, (words, vr, vticks, boxes) in enumerate(panels):
        p = Panel(f, 64 + 350 * idx, 52, 280, 280, lim, lim)
        # what remains after the tails: the angles of Sections E.2 and E.3
        rest = [p.P(vr[0], -0.4), p.P(min(vr[1], 11 / 25), -0.4),
                p.P(min(vr[1], 11 / 25), 11 / 25), p.P(vr[0], 11 / 25)]
        f.polygon(rest, fill=GREY, stroke=FAINT, width=1)
        f.line(p.P(lim[0], 0), p.P(lim[1], 0), stroke=FAINT, width=0.8)
        f.line(p.P(0, lim[0]), p.P(0, lim[1]), stroke=FAINT, width=0.8)
        for (v0, v1), (s0, s1), col, name in boxes:
            f.polygon([p.P(v0, s0), p.P(v1, s0), p.P(v1, s1), p.P(v0, s1)],
                      fill=FILLS[col], stroke=COLORS[col], width=1.6)
            if v1 - v0 < 0.3:
                vtext(f, p.P((v0 + v1) / 2, (s0 + s1) / 2), f'Lemma {name}',
                      size=13, color=COLORS[col], italic=False)
            else:
                word(f, p.P((v0 + v1) / 2, (s0 + s1) / 2), f'Lemma {name}',
                     size=13, color=COLORS[col])
        p.frame(vticks, sticks, xlabel='v')
        f.text(shift(p.P(lim[0], lim[1]), (-28, 12)), 's', size=14)
        word(f, shift(p.P(0.13, lim[1]), (0, 16)), f'{it("W")} {words}',
             size=13)
    save(f, 'appendix-e/tails-map', 'The angles v and s of W and S, for W on its '
         'own axis and on the west side: the tails excluded by Lemmas E.4, '
         'E.5 and E.6 and the rectangle that remains')


# ---------------------------------------------------------------------------
# The edges of the west tail (Lemma E.4) and of the south tail (Lemma E.5).

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


def draw_tail(f, c, sqs, w_side, weights, k, far):
    """C, W, D and S (sqs: name -> (centre, phase)), the dashed circle of
    radius R0, the part of D outside it, the four separating lines (W from
    C along its own axis or along the west side of C, S from C along its
    own axis, and the two wings) and the forces of the stress with the
    weights (C-W, C-S, W-D, D-S), drawn k times their length."""
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    for name in ('C', 'W', 'S', 'D'):
        cen, t = sqs[name]
        fill, stroke = STYLE[name]
        f.square(cen, deg(t), fill=fill, stroke=stroke, width=1.6)
    cD, tD = sqs['D']
    for piece in outside_disk_pieces(square_corners(cD, deg(tD)), R0):
        f.polygon(piece, fill=RED, stroke='none', width=0, opacity=0.45)
    (cW, tW), (cS, tS) = sqs['W'], sqs['S']
    e1W, e2W, e1S, e2S = u(tW), u(tW + PI / 2), u(tS), u(tS + PI / 2)

    def sep(normal, level, along, around, half=0.62):
        foot = scale(normal, level)
        base = add(foot, scale(along, dot2(around, along)))
        f.line(add(base, scale(along, -half)), add(base, scale(along, half)),
               stroke=INK, width=1.3, dash='6 4')
    if w_side:
        sep((-1.0, 0.0), 0.5 - c[0], (0.0, 1.0), cW)
    else:
        sep(e1W, dot2(e1W, cW) - 0.5, e2W, cW)
    sep(e2W, dot2(e2W, cW) + 0.5, e1W, cW)
    sep(e2S, dot2(e2S, cS) - 0.5, e1S, cS)
    sep(e1S, dot2(e1S, cS) - 0.5, e2S, cS)
    l1, l2, l3, l4 = weights
    nW = (-1.0, 0.0) if w_side else e1W
    forces = {'W': add(scale(nW, l1), scale(e2W, -l3)),
              'D': add(scale(e2W, l3), scale(e2S, -l4)),
              'S': add(scale(e1S, l2), scale(e2S, l4)),
              'C': add(scale(nW, -l1), scale(e1S, -l2))}
    assert math.hypot(*add(*forces.values())) < 1e-12
    for name, cen in (('C', c), ('W', cW), ('D', cD), ('S', cS)):
        arrow(f, cen, add(cen, scale(forces[name], k)), color=INK, width=1.6)
        f.dot(cen, r=2.6)
    f.dot((0, 0), r=2.4, fill=FAINT)
    f.dot(far, r=4, fill=RED)


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
    draw_tail(f, c, {'C': (c, 0.0), 'W': (cW, tW), 'D': (cD, tD),
                     'S': (cS, tS)}, False, (8 / 15, 1 / 5, 1 / 6, 1 / 10),
              1.15, far)
    f.text((-0.05, 0.12), 'o', size=14, color=FAINT)
    f.text(shift(far, (-0.1, -0.17)), f'{rfar:.2f}', size=13, color=RED,
           italic=False, anchor='middle')
    f.text(shift(c, (0.25, 0.3)), 'C', size=17)
    f.text(shift(cW, (-0.12, 0.28)), 'W', size=17, color=PURPLE)
    f.text(shift(cS, (0.3, -0.18)), 'S', size=17, color=PINK)
    f.text(shift(cD, (-0.32, 0.05)), 'D', size=17, color=CYAN)
    word(f, (1.27, 1.44), sb(it('R'), '0', size=16), size=16)
    word(f, (-1.95, -1.88), f'{it("v")} = 11/25,  {it("s")} = 1/20,  '
         f'{it("d")} = π/4', size=13, anchor='start')
    save(f, 'appendix-e/west-tail', 'C, W, S and D at the edge of the west tail: W '
         'and S touch C along their own axes and the circle of radius R0 '
         'with their far vertices, D touches W and S along their secondary '
         'axes, and the far vertex of D lies outside the circle; arrows show '
         'the forces of the stress')


def south_tail():
    """The edge of the south tail with W on the west side (Lemma E.5): C at
    (0, c0); W separated from C along the west side and S along its own
    axis (tight), both with their far vertices on the circle of radius R0;
    D tight against both wings."""
    v, s, d = 0.0, 11 / 25, PI / 4
    cx, cy = 0.0, C0
    # W: c_x + a cos v + b sin v = tau(v), far vertex on the circle, b < 0
    aW = tau(v) - cx
    bW = -(math.sqrt(Q0 - (aW + 0.5) ** 2) - 0.5)
    aS = tau(s) + cx * math.sin(s) - cy * math.cos(s)
    bS = math.sqrt(Q0 - (aS + 0.5) ** 2) - 0.5
    m11, m12, r1 = math.sin(v + d), math.cos(v + d), tau(v + d) + bW
    m21, m22, r2 = math.cos(d - s), -math.sin(d - s), tau(d - s) - bS
    det = m11 * m22 - m12 * m21
    aD, bD = (r1 * m22 - m12 * r2) / det, (m11 * r2 - m21 * r1) / det
    checks = [aW * math.cos(v) + bW * math.sin(v) + cx - tau(v),
              aS - cx * math.sin(s) + cy * math.cos(s) - tau(s),
              aD * math.sin(v + d) + bD * math.cos(v + d) - bW - tau(v + d),
              bS + aD * math.cos(d - s) - bD * math.sin(d - s) - tau(d - s)]
    assert max(abs(x) for x in checks) < 1e-12
    tW, tD, tS = PI - v, PI + d, 1.5 * PI + s
    cW, cD, cS = oriented(tW, aW, bW), oriented(tD, aD, bD), oriented(tS, aS, bS)
    sqs = {'C': ((cx, cy), 0.0), 'W': (cW, tW), 'D': (cD, tD), 'S': (cS, tS)}
    corners = {k: square_corners(p, deg(t)) for k, (p, t) in sqs.items()}
    for a_ in corners:
        for b_ in corners:
            if a_ < b_:
                assert not interiors_meet(corners[a_], corners[b_]), (a_, b_)
    for p in corners['W'] + corners['S']:
        assert math.hypot(*p) < R0 + 1e-9
    far = max(corners['D'], key=lambda p: math.hypot(*p))
    rfar = math.hypot(*far)
    assert 1.76 < rfar < 1.78
    f = Figure(-2.0, 1.95, -2.0, 1.85, 118)
    draw_tail(f, (cx, cy), sqs, True, (3 / 5, 1, 2 / 5, 3 / 10), 0.62, far)
    f.text((-0.07, -0.13), 'o', size=14, color=FAINT)
    f.text(shift(far, (0.1, -0.06)), f'{rfar:.2f}', size=13, color=RED,
           italic=False, anchor='start')
    f.text(shift((cx, cy), (0.28, 0.3)), 'C', size=17)
    f.text(shift(cW, (-0.28, -0.25)), 'W', size=17, color=PURPLE)
    f.text(shift(cS, (-0.22, 0.25)), 'S', size=17, color=PINK)
    f.text(shift(cD, (-0.3, 0.12)), 'D', size=17, color=CYAN)
    word(f, (1.27, 1.44), sb(it('R'), '0', size=16), size=16)
    word(f, (-1.95, -1.88), f'{it("v")} = 0,  {it("s")} = 11/25,  '
         f'{it("d")} = π/4', size=13, anchor='start')
    save(f, 'appendix-e/south-tail', 'C, W, S and D at the edge of the south tail: '
         'W touches the west side of C and S touches C along its own axis, '
         'both reach the circle of radius R0 with their far vertices, D '
         'touches W and S along their secondary axes, and the far vertex of '
         'D lies outside the circle; arrows show the forces of the stress')


# ---------------------------------------------------------------------------
# Lemma E.3: the boxes of the west minorant.

def west_minorant_lower(k, v, x, d):
    """The Taylor lower bound of m_k(v, x, d) (Lemma E.3, Table E.1)."""
    be, ga, mu, nu = Fr(8, 15), Fr(1, 5), Fr(1, 6), Fr(1, 10)
    sNU = (ga ** 2 + nu ** 2 + Fr(2, 9) ** 2) / (2 * Fr(2, 9))
    dI = (mu ** 2 + nu ** 2 + Fr(6, 25) ** 2) / (2 * Fr(6, 25))
    assert dI == Fr(1073, 5400)
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
    W, Hh = 850, 300
    f = Figure(0, W, 0, Hh, 1, pad=6)
    vs, ds = (Fr(11, 25), Fr(2, 3)), (Fr(1, 2), Fr(11, 14))
    xmax = [Fr(3, 5), Fr(3, 5), Fr(2, 5)]
    titles = [f'{it("k")} = 0: {it("S")} on its own axis',
              f'{it("k")} = 1: {it("S")} on the south side, {it("s")} ≥ 0',
              f'{it("k")} = 2: {it("S")} on the south side, {it("s")} ≤ 0']
    low = None
    for k in range(3):
        ox, oy = 62 + 284 * k, 64

        def P(p, q, r):
            return (ox + 112 * p + 46 * q, oy + 150 * r + 40 * q)
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
            dxp, anchor = (9, 'start') if i == 1 else (-9, 'end')
            dyp = 11 if l == 1 else -11
            if tight:
                # inside the front face, clear of the edges
                dxp, dyp, anchor = -9, -13, 'end'
            if (i, j, l) == (0, 1, 0):
                # the hidden corner: inside the box, clear of its edges
                dxp, dyp, anchor = 6, 10, 'start'
            f.text(shift(p, (dxp, dyp)), f'{math.floor(val * 1e5) / 1e5:.5f}',
                   size=12, italic=False, anchor=anchor,
                   color=ORANGE if tight else INK)
        word(f, (ox + 79, 18), titles[k], size=13)
        f.text(shift(P(0.5, 0, 0), (0, -16)), 'v', size=15)
        f.text(shift(P(1, 0.5, 0), (10, -6)), 'x', size=15, anchor='start')
        f.text(shift(P(0, 0, 0.5), (-9, 0)), 'd', size=15, anchor='end')
    assert low[1:] == (0, 1, 0, 1)
    save(f, 'appendix-e/west-box', 'The three boxes of the west minorant with the '
         'Taylor lower bounds at their corners, all positive; the corner '
         'v = 2/3, x = 0, d = 11/14 is the tight one')


# ---------------------------------------------------------------------------
# Lemma E.5: the tangents of the length of the force on W.

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
               (ORANGE, '6 4', 1.2, f'tangent at {it("c")} = 18/25'),
               (GREEN, '6 4', 1.2, f'tangent at {it("c")} = 21/25'),
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
# Lemma E.6: the corner v = s = 11/25, its two bounds and the narrow cone.

def south_corner():
    """Lemma E.6 (3): at v = s = 11/25, the least value of q over the centres
    of D allowed by the lemma, the far-vertex bound q-hat and the cone bound
    P, as functions of d, for y = 0 and y = c-bar."""
    g, Rb, cb = 11 / 25, float(RBAR), float(CBAR)
    head = lambda y: (93 / 40 - (0.7421 + 1.0441) * Rb
                      + 5 / 8 * (0.5 - y) * math.cos(g)
                      + 5 / 8 * (0.5 + cb) * math.sin(g)
                      + (0.5 - cb) * math.cos(g) + (0.5 + y) * math.sin(g))
    qhat = lambda y, d: (head(y) + 2 / 5 * (math.cos(d + g) + math.sin(d + g))
                         + 3 / 10 * math.cos(d - g) - Rb / 5 * math.sin(2 * g)
                         - 61 / 120 * Rb)
    P = lambda y, d: (head(y) - 1 / 160 + 1 / 5 * math.cos(d + g)
                      - 2 / 5 * (0.5 + cb) * math.sin(d + g)
                      - 3 / 10 * (0.5 + cb) * math.cos(d - g)
                      + 3 / 20 * math.sin(d - g))
    # the centres of D: charts in the ceiling with |b| <= 23/100
    centres = [(0.5 + 0.62 * i / 300, -0.23 + 0.46 * j / 46)
               for i in range(301) for j in range(47)]
    centres = [(a, b) for a, b in centres
               if (a + 0.5) ** 2 + (abs(b) + 0.5) ** 2 <= Q0]

    def least(y, d):
        U = 2 / 5 * math.sin(d + g) + 3 / 10 * math.cos(d - g)
        V = 2 / 5 * math.cos(d + g) - 3 / 10 * math.sin(d - g)
        work = max(U * a + V * b for a, b in centres)
        return (head(y) + 0.2 * (math.cos(d + g) + math.sin(d + g))
                + 0.15 * (math.cos(d - g) + math.sin(d - g)) - work)
    W, Hh = 820, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    d1 = 11 / 14
    for idx, y in enumerate((0.0, cb)):
        p = Panel(f, 72 + 400 * idx, 62, 320, 230, (0.5, d1), (-0.03, 0.07))
        p.frame([(0.5, '1/2'), (0.6, '0.6'), (0.7, '0.7'), (d1, '11/14')],
                [(-0.02, '−0.02'), (0, '0'), (0.02, '0.02'), (0.04, '0.04'),
                 (0.06, '0.06')], xlabel='d')
        f.line(p.P(0.5, 0), p.P(d1, 0), stroke=FAINT, width=1)
        ds = [0.5 + (d1 - 0.5) * k / 60 for k in range(61)]
        lv = [least(y, d) for d in ds]
        polyline(f, [p.P(d, v) for d, v in zip(ds, lv)], stroke=FAINT,
                 width=2.2)
        p.curve(lambda d: qhat(y, d), 0.5, d1, stroke=ORANGE, width=2)
        p.curve(lambda d: P(y, d), 0.5, d1, stroke=BLUE, width=2)
        for d, v in zip(ds, lv):
            assert P(y, d) <= v + 1e-9 and qhat(y, d) <= v + 1e-9
            assert P(y, d) > 0
        assert qhat(y, d1) < 0
        for fn, col, dy in ((qhat, ORANGE, -13), (P, BLUE, 13)):
            f.dot(p.P(d1, fn(y, d1)), r=3.4, fill=col)
            f.text(shift(p.P(d1, fn(y, d1)), (-4, dy)),
                   f'{fn(y, d1):.4f}'.replace('-', '−'), size=12,
                   italic=False, anchor='end', color=col)
        word(f, shift(p.P((0.5 + d1) / 2, 0.07), (0, 16)),
             f'{it("y")} = ' + (it('c̄') if y else '0'), size=13)
    # legend, in the first panel
    p = Panel(f, 72, 62, 320, 230, (0.5, d1), (-0.03, 0.07))
    entries = [(FAINT, 2.2, 'least value of ' + it('q')),
               (ORANGE, 2, 'far-vertex bound ' + it('q̂')),
               (BLUE, 2, 'cone bound ' + it('P'))]
    lx, ly = p.P(0.52, -0.005)
    for k, (col, wd, text) in enumerate(entries):
        yy = ly - 17 * k
        f.line((lx, yy), (lx + 26, yy), stroke=col, width=wd)
        word(f, (lx + 32, yy), text, size=12, anchor='start')
    save(f, 'appendix-e/south-corner', 'At the corner v = s = 11/25 of Lemma E.6, '
         'for y = 0 and y = c-bar: the least value of q over the centres of '
         'D, the far-vertex bound, which turns negative near d = 11/14, and '
         'the cone bound, which stays positive')


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
    W, Hh = 520, 420
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 60, 46, 430, 365, (0, 0.8), (-0.34, 0.34))
    # the part of the narrow cone used: 3/5 <= U <= 7/10, |V| <= 2U/5
    f.polygon([p.P(0.6, -0.24), p.P(0.7, -0.28), p.P(0.7, 0.28),
               p.P(0.6, 0.24)], fill=FILLS[5], stroke='none', width=0)
    for sgn in (1, -1):
        polyline(f, [p.P(0, 0), p.P(0.8, sgn * 0.32)], stroke=CYAN,
                 width=1.3, dash='6 4')
    p.frame([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (0.6, '3/5'),
             (0.7, '7/10')], [(-0.3, '−0.3'), (-0.2, '−0.2'), (-0.1, '−0.1'),
                              (0, '0'), (0.1, '0.1'), (0.2, '0.2'),
                              (0.3, '0.3')], xlabel='U')
    f.line(p.P(0, 0), p.P(0.8, 0), stroke=FAINT, width=1)
    for x in (0.6, 0.7):
        f.line(p.P(x, -0.34), p.P(x, 0.34), stroke=FAINT, width=1, dash='3 3')
    polyline(f, [p.P(*UV(d)) for d in ds], stroke=BLUE, width=3)
    for d, s in ((0.5, f'{it("d")} = 1/2'), (11 / 14, f'{it("d")} = 11/14')):
        q = p.P(*UV(d))
        f.dot(q, r=3.4, fill=BLUE)
        # right of the band, level with the dot
        word(f, (p.P(0.7, 0)[0] + 7, q[1]), s, size=12, color=BLUE,
             anchor='start')
    for sgn in (1, -1):
        word(f, shift(p.P(0.3, sgn * 0.12), (0, 26 * sgn)),
             f'{it("V")} = {"" if sgn > 0 else "−"}2{it("U")}/5', size=12,
             color=CYAN)
    f.text(shift(p.P(0, 0.34), (-22, 0)), 'V', size=14)
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


# Lemma E.9: the forces along lines.

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
                 [-0.8 + 1.35 * k / 120 for k in range(121)]], stroke=FAINT,
             width=1, dash='3 3')
    polyline(f, [P1(q) for q in tips], stroke=PURPLE, width=3)
    arrow(f, P1((0, 0)), P1(base), color=FAINT, width=1.6)
    for w, lab in ((-0.4, '−2/5'), (0.0, '0'), (0.4, '2/5')):
        q = add(base, u(-w))
        arrow(f, P1(base), P1(q), color=PURPLE, width=1.2)
        arrow(f, P1((0, 0)), P1(q), color=INK, width=1.4)
        f.dot(P1(q), r=3, fill=PURPLE)
        word(f, shift(P1(q), (9, 0)), f'{it("w")} = {lab}', size=12,
             anchor='start', color=PURPLE)
    f.dot(P1((0, 0)), r=3)
    word(f, shift(P1((0, 0)), (8, 12)), f'centre of {it("W")}', size=12,
         anchor='start')
    word(f, shift(P1(base), (-9, 0)),
         '(' + star('r', ', −', 12) + star('m', ')', 12), size=12,
         anchor='end')
    labelled(f, (o1[0] + 160, 40), f'line in {it("w")}, {it("W")} on its '
             'matching side, facet −', ('e', '1', 'W'))
    word(f, (o1[0] + 160, 16), f'the length runs from {min(lens):.2f} to '
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
    # the force itself at one end only: its length hardly changes
    arrow(f, P2((0, 0)), P2(add(base2, turn(-0.3))), color=INK, width=1.4)
    for n, lab, off, anchor in ((-0.3, '−3/10', (10, 2), 'start'),
                                (5 / 12, '5/12', (0, 16), 'middle')):
        q = add(base2, turn(n))
        arrow(f, P2(base2), P2(q), color=PURPLE, width=1.2)
        f.dot(P2(q), r=3, fill=PURPLE)
        word(f, shift(P2(q), off), f'{it("n")} = {lab}', size=12,
             anchor=anchor, color=PURPLE)
    f.dot(P2((0, 0)), r=3)
    word(f, shift(P2((0, 0)), (8, 12)), f'centre of {it("W")}', size=12,
         anchor='start')
    word(f, shift(P2(base2), (10, -10)), '(1, −' + star('m', ')', 12),
         size=12, anchor='start')
    labelled(f, (o2[0] + 170, 40), f'line in {it("n")}, {it("W")} on its '
             'own axis, facet ', ('e', '1', 'N'))
    word(f, (o2[0] + 170, 16), 'the turning part points against the '
         'constant part', size=12)
    save(f, 'appendix-e/pair-turning', 'Two forces on W along lines of the sweep: '
         'a constant vector plus a turning vector, whose tip runs on a circle; '
         'on the right the turning part points against the constant part')


# The edges of the pair, the gap along lines (Lemmas E.11 and E.12), the
# Taylor errors (Lemma E.13), and the domains, sectors and sweep.

def pair_stress():
    """The edges of Definition 9.48 at the angles n = -1/10, w = -1/5, for N
    and W on their own axes and the facet -e^W_1: C = Q(0, 0), the three
    separations tight, W with its far vertex on the circle of radius R6,
    and the forces F_N and F_W (with the half edge from W to D)."""
    n, w, c = -0.1, -0.2, (0.0, 0.0)
    tN, tW = PI / 2 + n, PI + w
    e1N, e2N, e1W, e2W = u(tN), u(tN + PI / 2), u(tW), u(tW + PI / 2)
    aN, aW = tau(n) + dot2(c, e1N), tau(w) + dot2(c, e1W)
    bW = -(math.sqrt(R6 ** 2 - (aW + 0.5) ** 2) - 0.5)
    cW = oriented(tW, aW, bW)
    facet = u(w)                     # -e^W_1, from W to N
    bN = ((tau(n - w) - dot2(facet, add(scale(e1N, aN), scale(cW, -1))))
          / dot2(facet, e2N))
    cN = oriented(tN, aN, bN)
    sq = {'C': square_corners(c), 'N': square_corners(cN, deg(tN)),
          'W': square_corners(cW, deg(tW))}
    for a_ in sq:
        for b_ in sq:
            if a_ < b_:
                assert not interiors_meet(sq[a_], sq[b_])
    assert max(math.hypot(*p) for p in sq['N'] + sq['W']) < R6 + 1e-9
    # the three separations are tight
    assert abs(dot2(e1N, add(cN, scale(c, -1))) - tau(n)) < 1e-12
    assert abs(dot2(e1W, add(cW, scale(c, -1))) - tau(w)) < 1e-12
    assert abs(dot2(facet, add(cN, scale(cW, -1))) - tau(n - w)) < 1e-12
    FN = add(e1N, scale(facet, R_STAR))
    FW = add(e1W, scale(facet, -R_STAR), scale(e2W, -M_STAR))
    # in the frames of N and W these are the forces of Definition 9.48
    loc = lambda F, e1, e2: (dot2(F, e1), dot2(F, e2))
    FN0, FW0 = pair_forces(True, True, 'wF', n, w)
    assert math.dist(loc(FN, e1N, e2N), FN0) < 1e-12
    assert math.dist(loc(FW, e1W, e2W), FW0) < 1e-12
    f = Figure(-1.95, 1.4, -0.75, 1.95, 140)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    for name, cen, t in (('C', c, 0.0), ('N', cN, tN), ('W', cW, tW)):
        fill, stroke = STYLE[name]
        f.square(cen, deg(t), fill=fill, stroke=stroke, width=1.6)

    def sep(normal, level, around, half=0.75):
        along = (-normal[1], normal[0])
        base = add(scale(normal, level), scale(along, dot2(around, along)))
        f.line(add(base, scale(along, -half)), add(base, scale(along, half)),
               stroke=INK, width=1.3, dash='6 4')
    sep(e1N, dot2(e1N, cN) - 0.5, cN, half=0.62)
    sep(e1W, dot2(e1W, cW) - 0.5, cW)
    sep(facet, dot2(facet, cW) + 0.5, add(cW, (0.25, 0.75)), half=0.55)
    for name, cen, F in (('N', cN, FN), ('W', cW, FW)):
        arrow(f, cen, add(cen, scale(F, 0.5)), color=INK, width=2.2)
        f.dot(cen, r=2.8)
    f.dot((0, 0), r=2.4, fill=FAINT)
    f.text((0.08, -0.1), 'o', size=14, color=FAINT)
    f.text((0.3, -0.3), 'C', size=17)
    f.text(shift(cN, (0.3, -0.28)), 'N', size=17, color=ORANGE)
    f.text(shift(cW, (0.25, -0.3)), 'W', size=17, color=PURPLE)
    word(f, shift(add(cN, scale(FN, 0.5)), (0.1, 0.06)),
         sb(it('F'), it('N'), size=15), size=15, anchor='start')
    word(f, shift(add(cW, scale(FW, 0.5)), (-0.08, 0.08)),
         sb(it('F'), it('W'), size=15), size=15, anchor='end')
    word(f, (1.05, 1.42), sb(it('R'), '6', size=16), size=16)
    word(f, (-1.9, 1.85), f'{it("n")} = −1/10,  {it("w")} = −1/5', size=13,
         anchor='start')
    save(f, 'appendix-e/pair-stress', 'C, N and W at the angles n = -1/10 and '
         'w = -1/5, N and W on their own axes and separated from each other '
         'along the facet -e^W_1, with the three separating lines dashed and '
         'the forces F_N and F_W of the pair drawn as arrows at the centres')


def pair_lines():
    """Lemmas E.11 and E.12: the gap along three lines in w, for N and W on
    their matching sides and the facet -e^W_1, with its values at the ends
    and where the line crosses w = 0 and n = w, and the chords between."""
    no, wo, fac = False, False, 'wF'
    n0, n1, w0, w1 = pair_domain_bounds(no, wo)
    W, Hh = 536, 360
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 70, 50, 440, 280, (w0, w1), (-0.02, 0.46))
    p.frame([(-0.4, '−2/5'), (-0.25, '−1/4'), (0, '0'), (0.25, '1/4'),
             (0.4, '2/5')], [(0, '0'), (0.1, '0.1'), (0.2, '0.2'),
                             (0.3, '0.3'), (0.4, '0.4')], xlabel='w')
    f.text(shift(p.P(w0, 0.46), (-30, 12)), 'G', size=14)
    f.line(p.P(w0, 0), p.P(w1, 0), stroke=FAINT, width=1)
    lines = ((-0.25, '−1/4', BLUE), (0.0, '0', GREEN), (0.25, '1/4', ORANGE))
    for n, lab, col in lines:
        G = lambda w, n=n: pair_gap(no, wo, fac, n, w)
        cuts = sorted({w0, 0.0, n, w1})
        # concave between the cuts: above the chord, as Lemma A.10 says
        for a, b in zip(cuts, cuts[1:]):
            for k in range(1, 40):
                w = a + (b - a) * k / 40
                chord = G(a) + (G(b) - G(a)) * (w - a) / (b - a)
                assert G(w) >= chord - 1e-12
        polyline(f, [p.P(w, G(w)) for w in cuts], stroke=col, width=1.1,
                 dash='4 3')
        p.curve(G, w0, w1, n=400, stroke=col, width=2.2)
        for w in cuts:
            f.dot(p.P(w, G(w)), r=3.4, fill=col)
    for k, (n, lab, col) in enumerate(reversed(lines)):
        x, y = p.P(0.16, 0.42 - 0.035 * k)
        f.line((x, y), (x + 26, y), stroke=col, width=2.2)
        word(f, (x + 32, y), f'{it("n")} = {lab}', size=12, anchor='start')
    assert abs(pair_gap(no, wo, fac, 0.0, 0.0)) < 1e-12
    save(f, 'appendix-e/pair-lines', 'The gap along the lines in w at n = -1/4, 0 '
         'and 1/4, for N and W on their matching sides and the facet of the '
         'model -e^W_1: concave between the points where a line crosses w = 0 '
         'or n = w, and above the chords through its values there and at '
         'the ends')


def taylor_error():
    """Lemma E.13: the errors cos t - C_6(t) and sin t - S_7(t) on
    [-6/7, 6/7], in units of 10^-6, below their bounds t^8/8! and
    |t|^9/9! and far below 10^-5."""
    W, Hh = 600, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    T = 6 / 7
    p = Panel(f, 70, 50, 480, 250, (-T, T), (-2, 11))
    p.frame([(-T, '−6/7'), (-0.5, '−0.5'), (0, '0'), (0.5, '0.5'),
             (T, '6/7')], [(-2, '−2'), (0, '0'), (2, '2'), (4, '4'), (6, '6'),
                           (8, '8'), (10, '10')], xlabel='t')
    word(f, shift(p.P(-T, 11), (0, 14)), 'units of 10⁻⁶', size=12,
         anchor='start')
    f.line(p.P(-T, 0), p.P(T, 0), stroke=FAINT, width=1)
    f.line(p.P(-T, 10), p.P(T, 10), stroke=RED, width=1.2, dash='6 4')
    word(f, shift(p.P(0, 10), (0, -11)), '10⁻⁵', size=12, color=RED)
    cos_err = lambda t: 1e6 * (math.cos(t) - float(c6(Fr(t))))
    sin_err = lambda t: 1e6 * (math.sin(t) - float(s7(Fr(t))))
    p.curve(cos_err, -T, T, stroke=BLUE, width=2.2)
    p.curve(sin_err, -T, T, stroke=ORANGE, width=2.2)
    for k in range(-60, 61):
        t = T * k / 60
        assert 0 <= cos_err(t) <= 1e6 * t ** 8 / 40320 + 1e-9 < 7.3
        assert abs(sin_err(t)) <= 1e6 * abs(t) ** 9 / 362880 + 1e-9 < 0.7
    for t in (-T, T):
        f.dot(p.P(t, cos_err(t)), r=3.2, fill=BLUE)
    word(f, shift(p.P(T, cos_err(T)), (-8, 4)), f'{cos_err(T):.2f}', size=12,
         color=BLUE, anchor='end')
    f.dot(p.P(T, sin_err(T)), r=3.2, fill=ORANGE)
    word(f, shift(p.P(T, sin_err(T)), (-8, 10)), f'{sin_err(T):.2f}',
         size=12, color=ORANGE, anchor='end')
    entries = [(BLUE, 'cos ' + it('t') + ' − ' +
                sb(it('C'), '6', '(', size=12) + it('t') + ')'),
               (ORANGE, 'sin ' + it('t') + ' − ' +
                sb(it('S'), '7', '(', size=12) + it('t') + ')')]
    for k, (col, text) in enumerate(entries):
        x, y = p.P(-0.3, 7.6 - 1.3 * k)
        f.line((x, y), (x + 26, y), stroke=col, width=2.2)
        word(f, (x + 32, y), text, size=12, anchor='start')
    save(f, 'appendix-e/taylor-error', 'The errors of the Taylor polynomials C6 '
         'and S7 on t from -6/7 to 6/7, in millionths: the cosine error rises '
         'to 7.2 at the ends and the sine error stays within 0.7, both far '
         'below 10^-5')


FRACTIONS = {-3 / 10: '−3/10', 5 / 12: '5/12', -1 / 4: '−1/4', 1 / 4: '1/4',
             -11 / 25: '−11/25', -2 / 5: '−2/5', 2 / 5: '2/5', 0.0: '0'}


def pair_domain():
    W, Hh = 560, 520
    f = Figure(0, W, 0, Hh, 1, pad=4)
    k = 280
    cells = [((True, False), (72, 262)), ((False, False), (388, 262)),
             ((True, True), (72, 50)), ((False, True), (388, 50))]
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
        # the segment of the diagonal n = w
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
        for p in {(x, yy) for x in (n0, 0.0, n1) for yy in (w0, 0.0, w1)}:
            f.dot(P(*p), r=3.6)
        for p in ((z0, z0), (z1, z1)):
            if p != (0.0, 0.0):
                open_dot(f, P(*p), r=4.2, width=1.6)
        # ticks: the bounds of the domain and 0
        for x in (n0, 0.0, n1):
            f.text(shift(P(x, w0), (0, -15)), FRACTIONS[x], size=12,
                   italic=False)
        for yy in sorted({w0, 0.0, w1}):
            f.text(shift(P(n0, yy), (-8, 0)), FRACTIONS[yy], size=12,
                   italic=False, anchor='end')
        f.text(shift(P((n0 + n1) / 2, w0), (0, -33)), 'n', size=15)
        f.text(shift(P(n0, w1), (-12, 16)), 'w', size=15, anchor='end')
        word(f, shift(P((n0 + n1) / 2, w1), (0, 17)),
             f'{it("N")} {names[no]}, {it("W")} {names[wo]}', size=13)
    save(f, 'appendix-e/pair-domain', 'The four domains of the pair estimate, cut '
         'into sign sectors by n = 0, w = 0 and n = w, with the diagonal, the '
         'three lines in w and a line in n of the sweep, and the points where '
         'the gap is checked')


# The gap of the facets of the model (Lemma E.16).

def white_box(f, pos, width, height=16):
    """A white rectangle behind a label that starts at pos."""
    x, y = pos
    f.polygon([(x - 3, y - height / 2), (x + width + 3, y - height / 2),
               (x + width + 3, y + height / 2), (x - 3, y + height / 2)],
              fill='#ffffff', stroke='none', width=0, opacity=0.9)


def pair_gap_figure():
    W, Hh = 820, 326
    f = Figure(0, W, 0, Hh, 1, pad=4)
    no, wo = True, True
    n0, n1, w0, w1 = pair_domain_bounds(no, wo)
    levels = [0.01, 0.02, 0.04, 0.08, 0.16, 0.32]
    for idx, (fac, title) in enumerate((('wF', ('e', '1', 'W')),
                                        ('nS', ('e', '2', 'N')))):
        ox = 70 + 400 * idx
        pw = 320
        ph = pw * (w1 - w0) / (n1 - n0)
        p = Panel(f, ox, 92, pw, ph, (n0, n1), (w0, w1))
        fn = lambda x, y, fac=fac: pair_gap(no, wo, fac, x, y)
        heat(p, fn, 96, 60, levels)
        p.frame([(-0.3, '−3/10'), (0, '0'), (5 / 12, '5/12')],
                [(-0.44, '−11/25'), (0, '0')], xlabel='n')
        f.text(shift(p.P(n0, w1), (-30, 12)), 'w', size=14)
        f.dot(p.P(0, 0), r=4, fill=RED)
        if fac == 'nS':
            g = pair_gap(no, wo, fac, 0.0, -11 / 25)
            assert 6.5e-4 < g < 6.7e-4
            f.dot(p.P(0, -11 / 25), r=4, fill=ORANGE)
            label = f'{it("G")} = {g:.5f}'
            at = shift(p.P(0, -11 / 25), (12, 14))
            white_box(f, at, text_width(label, 12))
            word(f, at, label, size=12, anchor='start')
        labelled(f, shift(p.P((n0 + n1) / 2, w1), (0, 20)), 'facet −',
                 title)
    x0 = 410 - 7 * 34 / 2
    heat_legend(f, x0, 20, levels)
    word(f, (x0 - 10, 26), f'the gap {it("G")}', size=12, anchor='end')
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
# Section E.3: the force on D and its support (Lemma E.17).

def diagonal_force():
    """Lemma E.17 (3): the force of the stress of the model on D, the sum of
    m* e^W_2 and -m* e^S_2, makes the angle -delta with the primary axis of
    D. Here w = -7/20, s = -3/20, d = 3/4: beta = -1/10, delta = 0.215;
    W and S sit at their places in the model, D touches both wings."""
    w, s, d = -0.35, -0.15, 0.75
    beta, delta = (w - s) / 2, d - PI / 4 - (w + s) / 2
    aW, bW, aS, bS = 1 - S_STAR, -T_STAR, 1 - S_STAR, T_STAR
    tW, tS, tD = PI + w, 1.5 * PI + s, PI + d
    m11, m12, r1 = math.sin(d - w), math.cos(d - w), tau(d - w) + bW
    m21, m22, r2 = math.cos(d - s), -math.sin(d - s), tau(d - s) - bS
    det = m11 * m22 - m12 * m21
    aD, bD = (r1 * m22 - m12 * r2) / det, (m11 * r2 - m21 * r1) / det
    cW, cS, cD = oriented(tW, aW, bW), oriented(tS, aS, bS), oriented(tD, aD, bD)
    e2W, e2S, e1D, e2D = u(tW + PI / 2), u(tS + PI / 2), u(tD), u(tD + PI / 2)
    # the wings are tight
    assert abs(dot2(e2W, add(cD, scale(cW, -1))) - tau(d - w)) < 1e-12
    assert abs(dot2(e2S, add(cS, scale(cD, -1))) - tau(d - s)) < 1e-12
    sq = {k: square_corners(p, deg(t)) for k, (p, t) in
          (('W', (cW, tW)), ('S', (cS, tS)), ('D', (cD, tD)))}
    assert not interiors_meet(sq['W'], sq['D'])
    assert not interiors_meet(sq['S'], sq['D'])
    FW, FS = scale(e2W, M_STAR), scale(e2S, -M_STAR)
    F = add(FW, FS)
    L = K_STAR * (math.cos(beta) - math.sin(beta))
    assert abs(dot2(F, e1D) - L * math.cos(delta)) < 1e-12
    assert abs(dot2(F, e2D) + L * math.sin(delta)) < 1e-12
    pts = sq['W'] + sq['S'] + sq['D'] + [(0.0, 0.0)]
    x0, x1 = min(p[0] for p in pts) - 0.25, max(p[0] for p in pts) + 0.1
    y0 = min(min(p[1] for p in pts), -R6) - 0.22
    y1 = max(p[1] for p in pts) + 0.2
    f = Figure(x0, x1, y0, y1, 120)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    for name, cen, t in (('W', cW, tW), ('S', cS, tS), ('D', cD, tD)):
        fill, stroke = STYLE[name]
        f.square(cen, deg(t), fill=fill, stroke=stroke, width=1.6)
    for normal, level, around in ((e2W, dot2(e2W, cW) + 0.5, cW),
                                  (e2S, dot2(e2S, cS) - 0.5, cS)):
        along = (-normal[1], normal[0])
        base = add(scale(normal, level), scale(along, dot2(around, along)))
        f.line(add(base, scale(along, -0.65)), add(base, scale(along, 0.65)),
               stroke=INK, width=1.3, dash='6 4')
    k = 0.55
    # the primary axis of D, and the force between the two wings
    f.line(cD, add(cD, scale(e1D, 1.12)), stroke=CYAN, width=1.2, dash='5 4')
    arrow(f, cD, add(cD, scale(FW, k)), color=PURPLE, width=1.6)
    arrow(f, cD, add(cD, scale(FS, k)), color=PINK, width=1.6)
    for a_, b_ in ((FW, FS), (FS, FW)):
        f.line(add(cD, scale(a_, k)), add(cD, scale(F, k)), stroke=FAINT,
               width=1, dash='3 3')
    arrow(f, cD, add(cD, scale(F, k)), color=INK, width=2.4)
    f.dot(cD, r=2.8)
    # the angle from the force to the axis
    a0 = math.atan2(F[1], F[0])
    a1 = a0 + math.remainder(tD - a0, 2 * PI)
    assert abs(abs(a1 - a0) - abs(delta)) < 1e-12
    f.line(add(cD, scale(F, k)), add(cD, scale(u(a0), 1.05)), stroke=INK,
           width=1, dash='2 3')
    polyline(f, [add(cD, scale(u(a0 + (a1 - a0) * j / 30), 0.92))
                 for j in range(31)], stroke=INK, width=1.2)
    mid = add(cD, scale(u((a0 + a1) / 2), 1.06))
    f.text(mid, 'δ', size=15)
    f.dot((0, 0), r=2.4, fill=FAINT)
    f.text((0.08, -0.1), 'o', size=14, color=FAINT)
    f.text(shift(cW, (-0.05, 0.22)), 'W', size=17, color=PURPLE)
    f.text(shift(cS, (0.2, -0.25)), 'S', size=17, color=PINK)
    f.text(shift(cD, (0.18, 0.22)), 'D', size=17, color=CYAN)
    tip = add(cD, scale(e1D, 1.12))
    word(f, shift(tip, (0.06, -0.08)), subsup(it('e'), '1', it('D'), 15),
         size=15, anchor='start')
    word(f, (x0 + 0.05, y0 + 0.08), f'{it("w")} = −7/20,  {it("s")} = −3/20,  '
         f'{it("d")} = 3/4', size=13, anchor='start')
    save(f, 'appendix-e/diagonal-force', 'The turned square D between W and S, '
         'separated from them along their secondary axes (dashed): the forces '
         'of the two wings on the centre of D and their sum, which makes the '
         'angle minus delta with the primary axis of D (dashed)')


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
    cond = f'2{sb(it("R"), "6", "|sin ", size=13)}{it("δ")}|'
    cases = ((0.15, f'the cap case, {cond} ≤ 1'),
             (0.5, f'the vertex case, {cond} > 1'))
    for idx, (delta, title) in enumerate(cases):
        o = (215 + 420 * idx, 215)
        P = lambda p: (o[0] + s * p[0], o[1] + s * p[1])
        f.circle(P((0, 0)), R6 * s, stroke=INK, width=1.0, dash='6 4')
        word(f, shift(P(scale(u(PI / 4), R6)), (6, 8)),
             sb(it('R'), '6', size=14), size=14, anchor='start')
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
        arrow(f, P(centre), P(add(centre, scale(F, 0.62))), color=INK,
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
        word(f, shift(P(corner), (-10, -11)), '(' + star('ρ', ', 0)', 12),
             size=12, anchor='end')
        word(f, shift(P(add(centre, scale(F, 0.62))), (6, -12)),
             f'{it("δ")} = {delta:g}', size=12, anchor='start')
        f.text(P(add(centre, (-0.3, 0.3 if idx == 0 else -0.3))), 'D',
               size=15, color=CYAN)
        word(f, (o[0], 410), title, size=13)
    save(f, 'appendix-e/diagonal-support', 'The support of the force on D in its '
         'frame: the region of possible centres, the force, and the best '
         'position of D, at the corner (rho*, 0) in the cap case and with a '
         'far vertex on the circle in the vertex case')


# ---------------------------------------------------------------------------
# Lemma E.20: the vertex minorant.

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
    W, Hh = 600, 350
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 70, 50, 500, 270, (0.29, 0.75), (-0.012, 0.06))
    p.frame([(0.29, '29/100'), (0.44, '11/25'), (0.5, '1/2'), (0.75, '3/4')],
            [(-0.01, '−0.01'), (0, '0'), (0.02, '0.02'), (0.04, '0.04'),
             (0.06, '0.06')], xlabel='t')
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
    for k, (a, b, F) in enumerate(pieces):
        # the bound beyond its piece, dashed, until it turns negative
        if k < 2:
            p.curve(F, b, 0.75, stroke=ORANGE, width=1.2, dash='5 4')
            assert F(b + 0.03) < 0
        else:
            p.curve(F, 0.29, a, stroke=ORANGE, width=1.2, dash='5 4')
            assert F(a - 0.01) < 0
        p.curve(F, a, b, stroke=ORANGE, width=2.2)
        for t in (a, b):
            assert F(t) > 0
            f.dot(p.P(t, F(t)), r=3.2, fill=ORANGE)
        if k:
            f.line(p.P(a, -0.012), p.P(a, 0.06), stroke=FAINT, width=0.8,
                   dash='2 3')
        for j in range(41):
            t = a + (b - a) * j / 40
            if t <= 2 / 7 + 11 / 25:
                assert F(t) <= phi_min(t) + 1e-9
    word(f, p.P(0.62, 0.049), f'least value of Φ', size=12, color=BLUE)
    word(f, p.P(0.69, 0.011), 'the bounds ' + sb(it('F'), it('l'), size=12),
         size=12, color=ORANGE)
    save(f, 'appendix-e/vertex-minorant', 'The least value of the vertex minorant '
         'over the admissible x and y, against the three concave lower bounds '
         'of Lemma E.20 on their pieces, all positive')


# ---------------------------------------------------------------------------
# The cap case along one line (Lemma E.19) and the remainder of the turned
# square.

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


def cap_line():
    """Lemma E.19 along the line s = -w at d = pi/4, where delta = 0 (the cap
    case) and beta = w: the remainder against the bounds of the proof,
    3/200 Z for beta <= 0 and 23/100 Z for beta >= 0, with Z = 2|w|."""
    W, Hh = 560, 330
    f = Figure(0, W, 0, Hh, 1, pad=4)
    p = Panel(f, 70, 50, 440, 250, (-0.44, 0.4), (0, 0.1))
    p.frame([(-0.44, '−11/25'), (-0.2, '−0.2'), (0, '0'), (0.2, '0.2'),
             (0.4, '2/5')], [(0, '0'), (0.02, '0.02'), (0.04, '0.04'),
                             (0.06, '0.06'), (0.08, '0.08'), (0.1, '0.1')],
            xlabel='w')
    R = lambda w: remainder(w, -w, PI / 4)
    for k in range(-44, 41):
        w = k / 100
        assert 2 * R6 * abs(math.sin(PI / 4 - PI / 4 - 0)) <= 1
        assert R(w) >= 3 / 200 * 2 * abs(w) - 1e-12
        if w >= 0:
            assert R(w) >= 23 / 100 * 2 * w - 1e-12
    p.curve(lambda w: 3 / 100 * abs(w), -0.44, 0.4, stroke=ORANGE, width=1.6,
            dash='6 4')
    p.curve(lambda w: 46 / 100 * w, 0, 0.4, stroke=ORANGE, width=1.6,
            dash='6 4')
    p.curve(R, -0.44, 0.4, n=300, stroke=BLUE, width=2.2)
    f.dot(p.P(0, 0), r=4, fill=RED)
    word(f, p.P(-0.43, 0.0035), '3/200 (|' + it('w') + '| + |' + it('s') +
         '|)', size=12, color=ORANGE, anchor='start')
    word(f, p.P(0.235, 0.092), '23/100 (|' + it('w') + '| + |' + it('s') +
         '|)', size=12, color=ORANGE, anchor='start')
    word(f, p.P(-0.14, 0.03), 'the remainder', size=12, color=BLUE)
    word(f, p.P(-0.22, 0.09), f'{it("β")} = {it("w")} ≤ 0', size=12)
    word(f, p.P(0.33, 0.06), f'{it("β")} ≥ 0', size=12)
    f.line(p.P(0, 0), p.P(0, 0.1), stroke=FAINT, width=1, dash='2 3')
    save(f, 'appendix-e/cap-line', 'The remainder along the line s = -w at '
         'd = pi/4, in the cap case, against the bounds of Lemma E.19: for w '
         'below 0 it stays above 3/200 (|w| + |s|), for w above 0 it rises '
         'steeply above 23/100 (|w| + |s|); it vanishes at the model')


def diagonal_remainder():
    W, Hh = 860, 342
    f = Figure(0, W, 0, Hh, 1, pad=4)
    d0 = math.asin(1 / (2 * R6))
    levels = [round(0.05 * j, 2) for j in range(1, 10)]
    for idx, (d, title) in enumerate(((PI / 4, 'π/4'), (0.65, '0.65'),
                                      (0.5, '1/2'))):
        ox = 58 + 280 * idx
        p = Panel(f, ox, 92, 220, 220, (-0.44, 0.4), (-0.4, 0.44))
        fn = lambda w, s, d=d: remainder(w, s, d)
        heat(p, fn, 56, 56, levels)
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
        word(f, shift(p.P(-0.02, 0.44), (0, 18)), f'{it("d")} = {title}',
             size=13)
        mn = min(remainder(-0.44 + 0.84 * i / 60, -0.4 + 0.84 * j / 60, d)
                 for i in range(61) for j in range(61))
        assert mn > -1e-12
    x0 = 448 - 10 * 34 / 2
    heat_legend(f, x0, 20, levels)
    word(f, (x0 - 10, 26), 'the remainder', size=12, anchor='end')
    save(f, 'appendix-e/diagonal-remainder', 'The remainder of the turned square '
         'over w and s for three values of d, as shaded maps with contour '
         'lines and the dashed boundaries of the cap case; it vanishes only '
         'at the model')


def main():
    tails_map()
    west_tail()
    south_tail()
    west_box()
    south_tangents()
    south_corner()
    south_cone()
    pair_stress()
    pair_turning()
    pair_lines()
    pair_domain()
    taylor_error()
    pair_gap_figure()
    diagonal_force()
    diagonal_support()
    cap_line()
    vertex_minorant()
    diagonal_remainder()


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw the figures of Appendix C (docs/proof/appendix-c.md), six squares: the
separators, in docs/proof/figures/appendix-c/.

    python3 scripts/figures/fig_appc.py

Every figure is computed from the definitions of the appendix: the model of
Theorem 9.1, the margins of the exterior squares against the central square,
the separating inequalities of the pairs W, D and D, S, the stresses of
Proposition 9.39 and Lemma 9.42 with their forces, the lower bounds of the
proofs at the vertices of their domains, and the profiles of Lemma 9.40.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY, SERIF,
                           square_corners, u, shift)

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN = COLORS[:6]
FW, FD, FS = FILLS[0], FILLS[3], FILLS[2]

# The ceiling (Definition 9.4).
Q0 = 2.85118
R0 = math.sqrt(Q0)
RHO0 = math.sqrt(Q0 - 0.25) - 0.5
C0 = RHO0 - 1
A0 = 2 - RHO0
U0 = math.sqrt(Q0 - (2.5 - RHO0) ** 2) - 0.5

# The model (Theorem 9.1).
H = math.sqrt(2) / 2
AS = (1466 + 1940 * H) / 267
BS = (327 + 432 * H) / 712
S_STAR = (AS - math.sqrt(AS * AS - 4 * BS)) / 2
T_STAR = (30 * H - 20) * S_STAR + 3.5 - 4.5 * H
D_STAR = 0.5 + H - T_STAR
R6 = math.sqrt(2 * S_STAR ** 2 + 4 * S_STAR + 2.5)


def save(f, name, title):
    assert name.startswith('appendix-c/'), name
    f.save(name, title)


# ---------------------------------------------------------------------------
# Geometry of squares in a frame (Definition 9.9) and their margins.

def omega(x):
    return (abs(math.cos(x)) + abs(math.sin(x))) / 2


def tau(x):
    return 0.5 + omega(x)


def centre(t, a, b):
    return (a * math.cos(t) - b * math.sin(t),
            a * math.sin(t) + b * math.cos(t))


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def half_width(t, n):
    """The half-width of a unit square of phase t along the unit vector n."""
    return (abs(dot(n, u(t))) + abs(dot(n, u(t + PI / 2)))) / 2


def chart_excess(a, b):
    """(a + 1/2)^2 + (|b| + 1/2)^2 - Q0: positive when the far corner of the
    square leaves the disk of radius R0."""
    return (a + 0.5) ** 2 + (abs(b) + 0.5) ** 2 - Q0


def own_radial(t, c):
    """The radial coordinate for which the own margin against Q(c) vanishes:
    a - <c, u(t)> - tau(t) = 0."""
    return tau(t) + dot(c, u(t))


def far_corner(t, a, b):
    """The vertex of Q_t(a, b) farthest from the origin."""
    sb_ = 1 if b >= 0 else -1
    return centre(t, a + 0.5, b + 0.5 * sb_)


def arrow(f, p, q, color=ORANGE, width=2.2, head=0.075):
    """An arrow from p to q with a filled head of the given length."""
    d = (q[0] - p[0], q[1] - p[1])
    L = math.hypot(*d)
    if L < 1e-9:
        return
    e = (d[0] / L, d[1] / L)
    n = (-e[1], e[0])
    base = shift(q, e, -head)
    f.line(p, base, stroke=color, width=width)
    f.polygon([q, shift(base, n, 0.45 * head), shift(base, n, -0.45 * head)],
              fill=color, stroke=color, width=1)


def contact_line(f, o, p, n, polys, margin=0.22, **kw):
    """The line through p with the normal n, drawn over the vertices of the
    given polygons that lie on it, and p, with a margin at both ends."""
    m = (-n[1], n[0])
    ts = [0.0]
    for poly in polys:
        for v in poly:
            if abs(dot(n, shift(v, p, -1))) < 1e-6:
                ts.append(dot(m, shift(v, p, -1)))
    lo, hi = min(ts) - margin, max(ts) + margin
    f.line(shift(o, shift(p, m, lo)), shift(o, shift(p, m, hi)), **kw)


def polyline(f, pts, stroke=INK, width=1.6, dash=None, opacity=1):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-opacity="{opacity}" '
          f'stroke-linejoin="round"{extra}/>')


def label(f, c, base, sub='', sup='', size=15, color=INK, italic=True):
    """A symbol with a subscript and a superscript, centred at c. The parts
    are separate text elements that meet at one point, so that the label does
    not depend on how a renderer places tspans."""
    x, y = f.p(*c)
    small = 0.7 * size
    wb = 0.5 * size * len(base)
    ws = 0.5 * small * max(len(sub), len(sup))
    xj = x - (wb + ws) / 2 + wb
    style = ' font-style="italic"' if italic else ''
    common = f'font-family="{SERIF}" fill="{color}" dominant-baseline="middle"'
    f.add(f'<text x="{xj:.1f}" y="{y:.1f}" font-size="{size}" {common} '
          f'text-anchor="end"{style}>{base}</text>')
    if sub:
        f.add(f'<text x="{xj + 0.6:.1f}" y="{y + 0.32 * size:.1f}" '
              f'font-size="{small:.1f}" {common} text-anchor="start">{sub}'
              '</text>')
    if sup:
        f.add(f'<text x="{xj + 0.6:.1f}" y="{y - 0.42 * size:.1f}" '
              f'font-size="{small:.1f}" {common} text-anchor="start"{style}>'
              f'{sup}</text>')


def C6(x):
    return 1 - x ** 2 / 2 + x ** 4 / 24 - x ** 6 / 720


def C4(x):
    return 1 - x ** 2 / 2 + x ** 4 / 24


def S7(x):
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def S5(x):
    return x - x ** 3 / 6 + x ** 5 / 120


# ---------------------------------------------------------------------------
# Graphs with separate scales on the two axes, drawn in pixel units.

class Plot:
    """A graph panel inside a Figure drawn in pixel units: the data box
    xr x yr is mapped onto the pixel box at (x0, y0) of size w x h."""

    def __init__(self, f, x0, y0, w, h, xr, yr):
        self.f, self.x0, self.y0, self.w, self.h = f, x0, y0, w, h
        self.xr, self.yr = xr, yr

    def q(self, x, y):
        sx = (x - self.xr[0]) / (self.xr[1] - self.xr[0])
        sy = (y - self.yr[0]) / (self.yr[1] - self.yr[0])
        return (self.x0 + sx * self.w, self.y0 + sy * self.h)

    def curve(self, fn, a, b, n=300, **kw):
        xs = [a + (b - a) * k / n for k in range(n + 1)]
        polyline(self.f, [self.q(x, fn(x)) for x in xs], **kw)

    def points(self, pts, **kw):
        polyline(self.f, [self.q(x, y) for x, y in pts], **kw)

    def polygon(self, pts, **kw):
        self.f.polygon([self.q(x, y) for x, y in pts], **kw)

    def dot(self, x, y, r=3.2, fill=INK):
        self.f.dot(self.q(x, y), r=r, fill=fill)

    def text(self, x, y, s, dx=0, dy=0, **kw):
        self.f.text(self.q(x, y), s, dx=dx, dy=dy, **kw)

    def line(self, a, b, **kw):
        self.f.line(self.q(*a), self.q(*b), **kw)

    def vline(self, x, stroke=FAINT, dash='4 4', width=1, lo=None, hi=None):
        lo = self.yr[0] if lo is None else lo
        hi = self.yr[1] if hi is None else hi
        self.f.line(self.q(x, lo), self.q(x, hi), stroke=stroke, dash=dash,
                    width=width)

    def hline(self, y, stroke=FAINT, dash='4 4', width=1, a=None, b=None):
        a = self.xr[0] if a is None else a
        b = self.xr[1] if b is None else b
        self.f.line(self.q(a, y), self.q(b, y), stroke=stroke, dash=dash,
                    width=width)

    def axes(self, xticks, yticks, xlabel='', ylabel='', y_axis_at=None):
        f = self.f
        y0 = self.yr[0] if y_axis_at is None else y_axis_at
        f.line(self.q(self.xr[0], y0), self.q(self.xr[1], y0), width=1,
               arrow=True)
        f.line(self.q(self.xr[0], self.yr[0]), self.q(self.xr[0], self.yr[1]),
               width=1, arrow=True)
        for x, s in xticks:
            f.line(shift(self.q(x, y0), (0, -3)), shift(self.q(x, y0), (0, 3)),
                   width=1)
            f.text(self.q(x, y0), s, size=12, italic=False, dy=14)
        for y, s in yticks:
            f.line(shift(self.q(self.xr[0], y), (-3, 0)),
                   shift(self.q(self.xr[0], y), (3, 0)), width=1)
            f.text(self.q(self.xr[0], y), s, size=12, italic=False,
                   anchor='end', dx=-6)
        if xlabel:
            f.text(self.q(self.xr[1], y0), xlabel, anchor='end', dy=-10)
        if ylabel:
            f.text(self.q(self.xr[0], self.yr[1]), ylabel, anchor='start',
                   dx=8, dy=4)


def pixel_figure(width, height):
    """A Figure whose units are pixels, with the origin at the lower left."""
    return Figure(0, width, 0, height, 1, pad=0)


# ---------------------------------------------------------------------------
# Figure C.1: the model, the frames of W, D and S and the two wings.

def model_frames():
    f = Figure(-1.95, 1.95, -1.95, 1.9, 128)
    f.circle((0, 0), R6, stroke=INK, width=1.2, dash='6 4')
    squares = [((S_STAR, S_STAR), 0, GREY, FAINT, 'C'),
               ((S_STAR + 1, S_STAR), 0, GREY, FAINT, 'E'),
               ((S_STAR, S_STAR + 1), 0, GREY, FAINT, 'N'),
               ((S_STAR - 1, T_STAR), 0, FW, BLUE, 'W'),
               ((-D_STAR, -D_STAR), 45, FD, PURPLE, 'D'),
               ((T_STAR, S_STAR - 1), 0, FS, GREEN, 'S')]
    for c, deg, fill, stroke, name in squares:
        f.square(c, deg, fill=fill, stroke=stroke, opacity=0.9)
    # Phase rays of W, D and S.
    for t, s in ((PI, 'π'), (5 * PI / 4, '5π/4'), (3 * PI / 2, '3π/2')):
        f.line((0, 0), shift((0, 0), u(t), R6 + 0.08), stroke=FAINT, width=1,
               dash='2 4')
        f.text(shift((0, 0), u(t), R6 + 0.17), s, size=13, italic=False,
               color=FAINT)
    # The wings: W-D along e2 of W (the line y = t* - 1/2) and D-S along e2
    # of S (the line x = t* - 1/2).
    yw = T_STAR - 0.5
    f.line((-1.62, yw), (-0.18, yw), stroke=BLUE, width=1.4, dash='6 4')
    f.line((yw, -1.62), (yw, -0.18), stroke=GREEN, width=1.4, dash='6 4')
    # Frames.
    frames = [((S_STAR - 1, T_STAR), PI, 'W', (0, 0.13), (0.17, 0.06)),
              ((-D_STAR, -D_STAR), 5 * PI / 4, 'D', (-0.15, 0.08),
               (0.12, 0.1)),
              ((T_STAR, S_STAR - 1), 3 * PI / 2, 'S', (0.17, 0.05),
               (0.0, 0.14))]
    for c, t, name, o1, o2 in frames:
        e1, e2 = u(t), u(t + PI / 2)
        arrow(f, c, shift(c, e1, 0.42), color=INK, width=1.6, head=0.08)
        arrow(f, c, shift(c, e2, 0.42), color=INK, width=1.6, head=0.08)
        label(f, shift(shift(c, e1, 0.42), o1), 'e', '1', name, size=15)
        label(f, shift(shift(c, e2, 0.42), o2), 'e', '2', name, size=15)
        f.dot(c, r=2.6)
    for c, deg, fill, stroke, name in squares:
        if name in 'CEN':
            f.text(shift(c, (0.2, 0.22)), name, size=16, color=INK)
    f.text((S_STAR - 1 + 0.2, T_STAR + 0.25), 'W', size=17, color=BLUE)
    f.text((-D_STAR - 0.26, -D_STAR - 0.02), 'D', size=17, color=PURPLE)
    f.text((T_STAR + 0.26, S_STAR - 1 - 0.18), 'S', size=17, color=GREEN)
    f.dot((0, 0), r=2.6)
    f.text((0.05, -0.08), 'o', size=14, anchor='start')
    save(f, 'appendix-c/frames', 'The model of six squares in the circle of radius '
         'R6, with the frames e1, e2 of W, D and S at their centres, the rays '
         'of their phases pi, 5 pi/4 and 3 pi/2, and the two wings: the line '
         'of the lower side of W, which D touches, and the line of the left '
         'side of S, which D touches')


# ---------------------------------------------------------------------------
# Figure C.2: the dominance of the secondary axes (Lemma C.3).

def inward_excess(q):
    """The largest inward primary projection rho0 - a0 cos q + U0 sin q,
    less the threshold tau(q)."""
    return RHO0 - A0 * math.cos(q) + U0 * math.sin(q) - tau(q)


def secondary_lead(q):
    """The least excess of the secondary projection over the inward primary
    one: (a0 - U0) cos q - (rho0 + U0)(1 - sin q)."""
    return (A0 - U0) * math.cos(q) - (RHO0 + U0) * (1 - math.sin(q))


def root(fn, lo, hi):
    for _ in range(80):
        mid = (lo + hi) / 2
        if (fn(lo) < 0) == (fn(mid) < 0):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def dominance():
    W_, H_ = 600, 340
    f = pixel_figure(W_, H_)
    g = Plot(f, 62, 48, 500, 262, (0, PI / 2 + 0.03), (-1.25, 0.72))
    g.polygon([(1.1, -1.25), (PI / 2, -1.25), (PI / 2, 0.72), (1.1, 0.72)],
              fill=FILLS[6], stroke='none', opacity=0.8)
    g.hline(0, stroke=INK, dash=None, width=0.8)
    g.curve(inward_excess, 0, PI / 2, stroke=ORANGE, width=2.2)
    g.curve(secondary_lead, 0, PI / 2, stroke=BLUE, width=2.2)
    q1 = root(inward_excess, 1.0, 1.3)
    q2 = root(secondary_lead, 0.8, 1.2)
    assert 1.1 < q1 < 1.15 and q2 < 1.1
    assert all(secondary_lead(1.1 + (PI / 2 - 1.1) * k / 200) >= -1e-12
               for k in range(201))
    g.dot(q1, 0, r=3.6, fill=ORANGE)
    g.dot(q2, 0, r=3.6, fill=BLUE)
    g.text(q1, 0, f'{q1:.2f}', size=12, italic=False, color=ORANGE, dx=4,
           dy=14, anchor='start')
    g.text(0.86, inward_excess(0.86), 'p(q) − τ(q)', size=15, color=ORANGE,
           dx=8, dy=16, anchor='start')
    g.text(0.72, secondary_lead(0.72), 'δ(q)', size=15, color=BLUE, dx=-8,
           dy=-14, anchor='end')
    g.axes([(0, '0'), (0.5, '1/2'), (1, '1'), (1.1, '11/10'),
            (PI / 2, 'π/2')],
           [(-1, '−1'), (-0.5, '−0.5'), (0, '0'), (0.5, '0.5')],
           xlabel='q')
    g.text(1.335, 0.62, 'q ≥ 11/10', size=13, italic=False, color=INK)
    save(f, 'appendix-c/dominance', 'Two functions of the phase gap q on zero to '
         'pi over 2: in orange the largest inward primary projection less the '
         'threshold, negative up to about 1.14 and rising to about 0.58; in '
         'blue the least excess of the secondary projection over the inward '
         'primary one, from about minus 1.15 up to zero near 1.05 and '
         'nonnegative beyond; the band from 11/10 to pi over 2 is shaded')


# ---------------------------------------------------------------------------
# Figure C.3: W on its own axis but not on the west side (Lemma 9.38).

def circle_arc(f, o, r, t0, t1, steps=160, **kw):
    polyline(f, [shift(o, u(t0 + (t1 - t0) * k / steps), r)
                 for k in range(steps + 1)], **kw)


def corner_position(w, c):
    """The chart (a, b) of W = Q_(pi + w)(a, b) with both its own margin and
    its west margin against Q(c) equal to zero."""
    a = tau(w) - c[0] * math.cos(w) - c[1] * math.sin(w)
    b = (c[0] - tau(w) + a * math.cos(w)) / math.sin(w)
    return a, b


def own_west_margins(w, a, b, c):
    t = PI + w
    own = a - dot(c, u(t)) - tau(t)
    x = a * math.cos(t) - b * math.sin(t)
    west = c[0] - x - tau(t)
    return own, west


def turn_panel(f, ox, w, title):
    o = (ox, 0)
    c = (C0, C0)
    t = PI + w
    a, b = corner_position(w, c)
    own, west = own_west_margins(w, a, b, c)
    assert abs(own) < 1e-12 and abs(west) < 1e-12
    circle_arc(f, o, R0, 0.62 * PI, 1.47 * PI, stroke=INK, width=1.1,
               dash='6 4')
    f.square(shift(o, c), 0, fill=GREY, stroke=FAINT, opacity=0.9)
    f.text(shift(o, (c[0] + 0.12, c[1] + 0.12)), 'C', size=16)
    # The west line x = c_x - 1/2 and the own line of W through the corner.
    xw = c[0] - 0.5
    f.line(shift(o, (xw, -1.45)), shift(o, (xw, 1.2)), stroke=INK, width=1.1,
           dash='5 4')
    n = u(t)
    P = (xw, c[1] - 0.5 if w > 0 else c[1] + 0.5)
    m = (-n[1], n[0])
    f.line(shift(o, shift(P, m, -1.25)), shift(o, shift(P, m, 1.25)),
           stroke=BLUE, width=1.3, dash='5 4')
    # D's own line through the lower-left corner and the pin of D.
    nd = u(PI + 0.65)
    md = (-nd[1], nd[0])
    Pd = (xw, c[1] - 0.5)
    f.line(shift(o, shift(Pd, md, -1.15)), shift(o, shift(Pd, md, 0.9)),
           stroke=PURPLE, width=1.2, dash='2 3')
    pd = shift((0, 0), u(5 * PI / 4), 0.9)
    # W at the corner position, and slid along its own line.
    slide = 0.32 if w > 0 else -0.32
    f.square(shift(o, centre(t, a, b + slide)), math.degrees(t), fill=FW,
             stroke=BLUE, opacity=0.35, width=1.2)
    f.square(shift(o, centre(t, a, b)), math.degrees(t), fill='none',
             stroke=BLUE, width=1.8)
    cw = centre(t, a, b)
    arrow(f, shift(o, cw), shift(o, centre(t, a, b + slide)), color=BLUE,
          width=1.8, head=0.08)
    f.dot(shift(o, P), r=3.4)
    f.dot(shift(o, pd), r=4, fill=PURPLE)
    label(f, shift(o, shift(pd, (0.04, -0.15))), 'p', 'D', '', size=15,
          color=PURPLE)
    f.text(shift(o, shift(cw, (-0.32, 0.36 if w < 0 else 0.3))), 'W',
           size=17, color=BLUE)
    f.text(shift(o, (-1.35, -1.47)), title, size=14, italic=False)


def turn():
    f = Figure(-1.95, 4.0, -1.55, 1.45, 118)
    turn_panel(f, 0.0, -0.3, '(a)  w = −0.3')
    turn_panel(f, 2.95, 0.3, '(b)  w = 0.3')
    save(f, 'appendix-c/turn', 'Two panels with the central square C, the line of '
         'its west side (dashed, vertical) and the line of its side across '
         'which W is separated along its own axis (blue, dashed), both '
         'through a corner of C; W is drawn at the corner position, where '
         'both margins vanish, and slid along its own line to where it is '
         'separated along its own axis but not along the west side. In (a), '
         'with w negative, W slides upwards, away from the pin of D; in (b), '
         'with w positive, it slides downwards, towards the pin of D and '
         'across the purple line beyond which D lies')


# ---------------------------------------------------------------------------
# Figures C.4 and C.5: the stresses at D of Proposition 9.39, drawn at a
# configuration where every separating inequality of the stress holds with
# equality; the far corners of W and D then leave the disk of radius R0.

def solve_free(excess_pair, lo=-0.5, hi=0.5, steps=2000):
    """The parameter in [lo, hi] that minimises the larger of two excesses."""
    best = None
    for k in range(steps + 1):
        t = lo + (hi - lo) * k / steps
        m = max(excess_pair(t))
        if best is None or m < best[0]:
            best = (m, t)
    return best[1]


def stress_configuration(tw, td, along_d, west, c):
    """Charts (aW, bW, aD, bD) of W = Q_tw and D = Q_td with the separations
    of the stress at equality: W from C along its own axis (or along the west
    side if `west`), D from C along its own axis, and W, D along the secondary
    axis of D (if `along_d`) or of W."""
    q = td - tw
    aD = own_radial(td, c)

    def charts(bw):
        if west:
            w = tw - PI
            aw = (tau(w) - c[0] + bw * math.sin(w)) / math.cos(w)
        else:
            aw = own_radial(tw, c)
        if along_d:
            bd = tau(q) - aw * math.sin(q) + bw * math.cos(q)
        else:
            bd = (tau(q) + bw - aD * math.sin(q)) / math.cos(q)
        return aw, bw, aD, bd

    bw = solve_free(lambda t: (chart_excess(*charts(t)[:2]),
                               chart_excess(*charts(t)[2:])))
    return charts(bw)


def stress_panel(f, o, tw, td, along_d, west, weights, title):
    """One configuration of the stress at D with its forces."""
    c = (C0, C0)
    al, be, mu = weights
    aw, bw, ad, bd = stress_configuration(tw, td, along_d, west, c)
    q = td - tw
    cw, cd = centre(tw, aw, bw), centre(td, ad, bd)
    # Check the separations of the stress.
    nW = (-1.0, 0.0) if west else u(tw)
    assert abs(dot(nW, shift(cw, c, -1)) - tau(tw)) < 1e-9
    assert abs(dot(u(td), shift(cd, c, -1)) - tau(td)) < 1e-9
    nWD = u(td + PI / 2) if along_d else u(tw + PI / 2)
    assert abs(dot(nWD, shift(cd, cw, -1)) - tau(q)) < 1e-9
    circle_arc(f, o, R0, 0.55 * PI, 1.55 * PI, stroke=INK, width=1.1,
               dash='6 4')
    f.square(shift(o, c), 0, fill=GREY, stroke=FAINT, opacity=0.9)
    f.text(shift(o, (c[0] + 0.13, c[1] + 0.13)), 'C', size=16)
    draw = lambda t, a, b, fill, stroke: f.square(
        shift(o, centre(t, a, b)), math.degrees(t), fill=fill, stroke=stroke,
        opacity=0.8, width=1.6)
    draw(tw, aw, bw, FW, BLUE)
    draw(td, ad, bd, FD, PURPLE)
    # Separating lines: of C towards W and towards D, and between W and D.
    Wpoly = square_corners(cw, math.degrees(tw))
    Dpoly = square_corners(cd, math.degrees(td))
    Cpoly = square_corners(c, 0)
    for n, poly, col in ((nW, Wpoly, BLUE), (u(td), Dpoly, PURPLE)):
        p = shift(c, n, half_width(0.0, n))
        contact_line(f, o, p, n, [Cpoly, poly], stroke=col, width=1.2,
                     dash='5 4')
    p = shift(cw, nWD, half_width(tw, nWD))
    contact_line(f, o, p, nWD, [Wpoly, Dpoly], stroke=INK, width=1.2,
                 dash='2 3')
    for t, a, b in ((tw, aw, bw), (td, ad, bd)):
        v = far_corner(t, a, b)
        r = math.hypot(*v)
        if r > R0:
            f.line(shift(o, shift((0, 0), v, R0 / r)), shift(o, v),
                   stroke=PINK, width=3.2)
            f.dot(shift(o, v), r=4.2, fill=PINK)
    # Forces, in Cartesian coordinates.
    if west:
        FWc = shift(shift((0, 0), nW, be), nWD, -mu)
    else:
        FWc = shift(shift((0, 0), u(tw), be), nWD, -mu)
    FDc = shift(shift((0, 0), u(td), al), nWD, mu)
    FCc = shift(shift((0, 0), nW, -be), u(td), -al)
    k = 1.25
    for p0, F in ((cw, FWc), (cd, FDc), (c, FCc)):
        arrow(f, shift(o, p0), shift(o, shift(p0, F, k)), color=ORANGE,
              width=2.4, head=0.09)
    for p0, F, name, extra in ((cw, FWc, 'W', (0.1, 0.06)),
                               (cd, FDc, 'D', (-0.1, 0.06)),
                               (c, FCc, 'C', (0.08, 0.0))):
        L = math.hypot(*F)
        tip = shift(p0, F, k)
        label(f, shift(o, shift(shift(tip, F, 0.16 / L), extra)), 'F', name,
              size=15, color=ORANGE)
    f.text(shift(o, shift(cw, (0.22, -0.14))), 'W', size=17, color=BLUE)
    f.text(shift(o, shift(cd, (0.2, 0.2))), 'D', size=17, color=PURPLE)
    f.dot(shift(o, (0, 0)), r=2.5)
    f.text(shift(o, (-1.55, 1.42)), title, size=15, italic=False,
           anchor='start')
    return aw, bw, ad, bd


def own_stress():
    f = Figure(-1.95, 4.5, -1.78, 1.62, 108)
    v, d = 0.3, 0.3
    stress_panel(f, (0, 0), PI - v, PI + d, False, False,
                 (0.31, 0.44, 0.25), '(a)')
    stress_panel(f, (3.2, 0), PI - v, PI + d, True, False,
                 (0.42, 0.37, 0.21), '(b)')
    save(f, 'appendix-c/own-stress', 'The stress at D with W on its own axis, at '
         'v = d = 0.3, with every separating inequality of the stress at '
         'equality: W touches the line of C across which it is separated '
         'along its own axis, D the corresponding line for D, and D the line '
         'of the side of W (a) or W the line of the side of D (b); the far '
         'vertices of W and D, marked, leave the dashed circle of radius R0, '
         'and the forces on W, D and C are drawn as arrows')


def west_stress():
    f = Figure(-1.95, 4.5, -1.78, 1.62, 108)
    w, d = -0.2, 0.35
    stress_panel(f, (0, 0), PI + w, PI + d, False, True,
                 (0.35, 0.40, 0.25), '(a)')
    stress_panel(f, (3.2, 0), PI + w, PI + d, True, True,
                 (0.43, 0.30, 0.27), '(b)')
    save(f, 'appendix-c/west-stress', 'The stress at D with W on the west side of '
         'C, at w = -0.2 and d = 0.35, with every separating inequality of '
         'the stress at equality: W touches the line of the west side of C, '
         'D the line of C across which it is separated along its own axis, '
         'and D the line of the side of W (a) or W the line of the side of D '
         '(b); the far vertices of W and D, marked, leave the dashed circle '
         'of radius R0, and the forces on W, D and C are drawn as arrows')


# ---------------------------------------------------------------------------
# Figure C.6: the domains of the two stresses, with the lower bounds of the
# slack at their vertices (Tables C.3 and C.6).

# Brackets of cos x and sin x from the Taylor polynomials of Lemma A.8,
# rounded outward to five decimals (Table C.1).
BRACKETS = {
    '0': ((1.0, 1.0), (0.0, 0.0)),
    '1/10': ((0.99500, 0.99501), (0.09983, 0.09984)),
    '2/5': ((0.92106, 0.92107), (0.38941, 0.38942)),
    '1/2': ((0.87758, 0.87761), (0.47942, 0.47943)),
    '2/3': ((0.78588, 0.78601), (0.61836, 0.61839)),
    '9/10': ((0.62159, 0.62234), (0.78332, 0.78343)),
    '7/6': ((0.39313, 0.39664), (0.91943, 0.92002)),
}
VALUE = {'0': 0.0, '1/10': 0.1, '2/5': 0.4, '1/2': 0.5, '2/3': 2 / 3,
         '9/10': 0.9, '7/6': 7 / 6}


def check_brackets():
    for key, ((cl, cu), (sl, su)) in BRACKETS.items():
        x = VALUE[key]
        assert cl <= C6(x) <= math.cos(x) <= C4(x) <= cu or x == 0
        assert sl <= S7(x) <= math.sin(x) <= S5(x) <= su or x == 0


def trig_box(*args):
    """All combinations of bracket ends for the cosines and sines of the
    signed angles given as (key, sign)."""
    out = [()]
    for key, sign in args:
        (cl, cu), (sl, su) = BRACKETS[key]
        sines = (sl, su) if sign > 0 else (-su, -sl)
        out = [o + ((c, s_),) for o in out for c in (cl, cu) for s_ in sines]
    return out


OWN_WEIGHTS = {False: (0.31, 0.44, 0.25), True: (0.42, 0.37, 0.21)}
OWN_L0 = {False: 0.5061, True: 0.4696}
OWN_L = {(False, '0'): 0.3983, (True, '0'): 0.4255,
         (False, '1/2'): 0.4827, (True, '1/2'): 0.5056,
         (False, '2/3'): 0.5046, (True, '2/3'): 0.5265}


def floor6(x):
    """Round down to six decimals; the rounding to nine decimals first removes
    the floating-point error of values that are exact decimals."""
    return math.floor(round(x * 1e6, 3)) / 1e6


def ceil6(x):
    return math.ceil(round(x * 1e6, 3)) / 1e6


def own_corner_bound(vk, dk, along_d):
    """The lower bound of Table C.3 for the slack of the own-axis stress at a
    corner: the positive part with the lower ends of the brackets (the upper
    end of sin q where it has a negative coefficient), less the work bound and
    the bound of the work on C with the upper ends."""
    al, be, mu = OWN_WEIGHTS[along_d]
    source = al if along_d else be
    target = be if along_d else al
    qk = {('0', '0'): '0', ('0', '1/2'): '1/2', ('2/3', '0'): '2/3',
          ('2/3', '1/2'): '7/6'}[(vk, dk)]
    (cvl, cvu), (svl, svu) = BRACKETS[vk]
    (cdl, cdu), (sdl, sdu) = BRACKETS[dk]
    (cql, cqu), (sql, squ) = BRACKETS[qk]
    X = be * cvu + al * cdu
    Y = max(al * sdu - be * svl, 0.0)
    if qk != '7/6':
        L = OWN_L[(along_d, qk)]
        assert target ** 2 + mu ** 2 + 2 * target * mu * squ <= L ** 2
        P = (1 + be / 2 * (cvl + svl) + al / 2 * (cdl + sdl)
             + mu * (cql + sql))
        work = 1.689 * (OWN_L0[along_d] + L)
    else:
        assert (RHO0 + 0.5) * mu * cqu <= (target + mu * sql) / 2
        P = ((1 + source + mu) / 2 + be / 2 * (cvl + svl)
             + al / 2 * (cdl + sdl) + mu / 2 * cql - 0.613 * mu * squ)
        work = 1.689 * OWN_L0[along_d] + 1.113 * target
    assert source ** 2 + mu ** 2 <= OWN_L0[along_d] ** 2
    return floor6(P) - ceil6(work) - ceil6(0.113 * (X + Y))


SIDE_WEIGHTS = {False: (0.35, 0.40, 0.25), True: (0.43, 0.30, 0.27)}


def rot_tangent(p, q, c, s_):
    return (p * p + q * q + 2 * p * q * s_ + c * c) / (2 * c)


def side_terms(along_d, w, sw, cw, d, sd, cd, sq, cq):
    """The constant and the terms in w, d and q = d - w of the lower bound of
    the slack of the west-side stress."""
    al, be, mu = SIDE_WEIGHTS[along_d]
    K = 1 - 0.613 * be - (1.689 * 0.51 if along_d else 0)
    Wt = be * cw + (be * sw if w >= 0 else 0) - (
        0 if along_d else 1.689 * rot_tangent(0.40, 0.25, 12 / 25, sw))
    Dt = 0.387 * al * (cd + sd) - (
        1.689 * rot_tangent(0.30, 0.27, 9 / 20, sd) if along_d else 0)
    Qt = mu * (cq + sq) - (
        0 if along_d else 1.689 * rot_tangent(0.35, 0.25, 0.5, sq))
    return K, Wt, Dt, Qt


SIDE_VERTICES = [('2/5', -1, '0'), ('2/5', -1, '1/2'), ('0', 1, '0'),
                 ('0', 1, '1/2'), ('2/5', 1, '2/5'), ('2/5', 1, '1/2')]


def side_term_bound(along_d, kind, key, sign=1):
    """The lower bound of Table C.5 for one term of the west-side bound: the
    least value over the ends of the brackets, rounded down."""
    (cl, cu), (sl, su) = BRACKETS[key]
    sines = (sl, su) if sign > 0 else (-su, -sl)
    vals = []
    for c_ in (cl, cu):
        for s_ in sines:
            if kind == 'W':
                w = sign * VALUE[key]
                vals.append(side_terms(along_d, w, s_, c_, 0, 0, 1, 0, 1)[1])
            elif kind == 'D':
                vals.append(side_terms(along_d, 0, 0, 1, 0, s_, c_, 0, 1)[2])
            else:
                vals.append(side_terms(along_d, 0, 0, 1, 0, 0, 1, s_, c_)[3])
    return floor6(min(vals))


def side_vertex_bound(wk, ws, dk, along_d):
    w = ws * VALUE[wk]
    d = VALUE[dk]
    q = d - w
    qk = min(VALUE, key=lambda k: abs(VALUE[k] - q))
    assert abs(VALUE[qk] - q) < 1e-12
    K = side_terms(along_d, 0, 0, 1, 0, 0, 1, 0, 1)[0]
    total = (K + side_term_bound(along_d, 'W', wk, ws)
             + side_term_bound(along_d, 'D', dk)
             + side_term_bound(along_d, 'Q', qk))
    # The joint minimum over the brackets is at least the sum of the terms.
    best = min(sum(side_terms(along_d, w, sw, cw, d, sd, cd, sq, cq))
               for (cw, sw), (cd, sd), (cq, sq) in trig_box((wk, ws), (dk, 1),
                                                           (qk, 1)))
    assert best >= total - 1e-12
    return total


def domain_panel(f, g, region, verts, title, divider=None):
    g.polygon([(-2 / 3, 0), (5 / 8, 0), (5 / 8, PI / 4), (-2 / 3, PI / 4)],
              fill='none', stroke=FAINT, width=1, dash='4 4')
    g.polygon([(-2 / 3, 0.5), (5 / 8, 0.5), (5 / 8, PI / 4), (-2 / 3, PI / 4)],
              fill=FILLS[2], stroke='none', opacity=0.45)
    g.polygon(region, fill=FILLS[1], stroke=ORANGE, width=1.6)
    if divider:
        g.line(*divider, stroke=ORANGE, width=1, dash='3 3')
    g.hline(0.5, stroke=INK, dash='5 4', width=1, a=-2 / 3, b=5 / 8)
    g.axes([(-2 / 3, '−2/3'), (-0.4, '−2/5'), (0, '0'), (0.4, '2/5'),
            (5 / 8, '5/8')],
           [(0, '0'), (0.5, '1/2'), (PI / 4, 'π/4')], xlabel='w',
           ylabel='d')
    for (x, y), (v1, v2), (dx, dy, anchor) in verts:
        g.dot(x, y, r=3.4, fill=ORANGE)
        t1 = math.floor(v1 * 1e4) / 1e4
        t2 = math.floor(v2 * 1e4) / 1e4
        g.text(x, y, f'{t1:.4f}', size=12, italic=False, color=BLUE, dx=dx,
               dy=dy, anchor=anchor)
        g.text(x, y, f'{t2:.4f}', size=12, italic=False, color=PURPLE, dx=dx,
               dy=dy + 14, anchor=anchor)
    g.text(-2 / 3, PI / 4, title, size=15, italic=False, dx=4, dy=28,
           anchor='start')


def domains():
    check_brackets()
    W_, H_ = 900, 330
    f = pixel_figure(W_, H_)
    xr, yr = (-0.78, 0.72), (-0.06, 0.92)
    g1 = Plot(f, 50, 42, 380, 255, xr, yr)
    g2 = Plot(f, 500, 42, 380, 255, xr, yr)
    own = {}
    for vk, dk in (('0', '0'), ('0', '1/2'), ('2/3', '0'), ('2/3', '1/2')):
        own[(vk, dk)] = tuple(own_corner_bound(vk, dk, ad)
                              for ad in (False, True))
        assert min(own[(vk, dk)]) > 0
    v = lambda k: VALUE[k]
    verts1 = [((-v(vk), v(dk)), own[(vk, dk)],
               (8 if vk == '0' else -8, -28, 'start' if vk == '0' else 'end'))
              for vk, dk in own]
    domain_panel(f, g1, [(-2 / 3, 0), (0, 0), (0, 0.5), (-2 / 3, 0.5)],
                 verts1, '(a) W on its own axis')
    verts2 = []
    for wk, ws, dk in SIDE_VERTICES:
        vals = tuple(side_vertex_bound(wk, ws, dk, ad)
                     for ad in (False, True))
        assert min(vals) > 0
        x, y = ws * v(wk), v(dk)
        place = {(-0.4, 0.0): (-8, -28, 'end'), (-0.4, 0.5): (-8, -28, 'end'),
                 (0.0, 0.0): (-8, -28, 'end'), (0.0, 0.5): (0, -28, 'middle'),
                 (0.4, 0.4): (8, -6, 'start'), (0.4, 0.5): (8, -28, 'start')}
        verts2.append(((x, y), vals, place[(round(x, 3), round(y, 3))]))
    domain_panel(f, g2, [(-0.4, 0), (0, 0), (0.4, 0.4), (0.4, 0.5),
                         (-0.4, 0.5)], verts2, '(b) W on the west side',
                 divider=((0, 0), (0, 0.5)))
    save(f, 'appendix-c/domains', 'Two panels in the plane of the angles w and d, '
         'each with the window of the angles (dashed) and the band d above '
         '1/2 shaded. (a) The rectangle of the stress with W on its own axis, '
         'w from minus 2/3 to 0 and d from 0 to 1/2; (b) the domain of the '
         'stress with W on the west side, w from minus 2/5 to 2/5, d from 0 '
         'to 1/2 and w at most d, split at w = 0. At each vertex the lower '
         'bounds of the slack for the two separators of W and D are written, '
         'the first for the secondary axis of W and the second for that of D')


# ---------------------------------------------------------------------------
# Figure C.7: the transverse profiles of Lemma 9.40 against their bounds.

def disk_transverse(front):
    """The largest |b| of a chart in the ceiling with a + 1/2 >= front."""
    return math.sqrt(Q0 - front * front) - 0.5


def diagonal_profile(d):
    """The largest |b_D| for D on its own axis at the phase pi + d, with the
    centre of C at the corner (c0, c0) of its box."""
    return disk_transverse(1 + (0.5 - C0) * (math.cos(d) + math.sin(d)))


def west_side_profile(v):
    """The largest -b_W for W on the west side of C at the phase pi - v,
    with c_x = c0: the margin gives a >= (K + beta sin v)/cos v."""
    K = 0.5 - C0 + (math.cos(v) + math.sin(v)) / 2

    def feasible(beta):
        a = max((K + beta * math.sin(v)) / math.cos(v), 0.5)
        return (a + 0.5) ** 2 + (abs(beta) + 0.5) ** 2 <= Q0

    ok = [k / 1000 for k in range(-500, 501) if feasible(k / 1000)]
    if not ok:
        return None
    lo = max(ok)
    hi = lo + 0.001
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if feasible(mid) else (lo, mid)
    return lo


def own_west_profile(v):
    """The largest |b_W| for W on its own axis at the phase pi - v, with
    c = (c0, 0)."""
    return disk_transverse(1 + (0.5 - C0) * math.cos(v) + 0.5 * math.sin(v))


def own_west_cubic_profile(v):
    P = 1 + 0.387 * (1 - v * v / 2) + (v - v ** 3 / 6) / 2
    return disk_transverse(P)


def profiles():
    W_, H_ = 960, 300
    f = pixel_figure(W_, H_)
    panels = [
        (Plot(f, 48, 46, 250, 210, (0, PI / 4 + 0.04), (0, 0.52)),
         diagonal_profile, 0, PI / 4,
         [(lambda d: 0.97 - (math.cos(d) + math.sin(d)) / 2, 0, PI / 4,
           GREEN, '0.97 − (cos d + sin d)/2'),
          (lambda d: 0.31 - 0.17 * d, 0.5, PI / 4, ORANGE,
           '31/100 − 17d/100')],
         [(0, '0'), (0.5, '1/2'), (PI / 4, 'π/4')], 'd', '(a)  D, |b|'),
        (Plot(f, 368, 46, 250, 210, (0, 0.42), (0, 0.52)),
         west_side_profile, 0, 0.4,
         [(lambda v: 0.47 - 2 * v / 3, 0, 0.4, ORANGE, '47/100 − 2v/3')],
         [(0, '0'), (0.2, '1/5'), (0.4, '2/5')], 'v', '(b)  W on the west '
         'side, −b'),
        (Plot(f, 688, 46, 250, 210, (0, 0.52), (0, 0.52)),
         own_west_profile, 0, 0.5,
         [(lambda v: 233 / 500 - 0.73 * v, 0, 0.5, ORANGE,
           '233/500 − 73v/100')],
         [(0, '0'), (0.25, '1/4'), (0.5, '1/2')], 'v', '(c)  W on its own '
         'axis, |b|'),
    ]
    vmax = root(lambda v: west_side_profile(v)
                if west_side_profile(v) is not None else -1, 0.2, 0.4)
    panels[1] = panels[1][:3] + (vmax,) + panels[1][4:]
    for g, fn, a, b, bounds, xticks, xname, title in panels:
        g.axes(xticks, [(0, '0'), (0.25, '1/4'), (0.5, '1/2')], xlabel=xname)
        g.curve(fn, a, b, stroke=BLUE, width=2.4)
        for bf, ba, bb, col, name in bounds:
            g.curve(bf, ba, bb, stroke=col, width=1.8, dash='6 4')
            for k in range(201):
                x = ba + (bb - ba) * k / 200
                if fn(x) is not None and x <= b:
                    assert bf(x) > fn(x)
        g.text(g.xr[0], g.yr[1], title, size=14, italic=False, dx=10, dy=8,
               anchor='start')
    g1, g2, g3 = (p[0] for p in panels)
    g1.text(0.12, 0.97 - (math.cos(0.12) + math.sin(0.12)) / 2, '0.97 − ω',
            size=12, italic=False, color=GREEN, dx=4, dy=-14,
            anchor='start')
    g1.text(PI / 4, 0.31 - 0.17 * PI / 4, '0.31 − 0.17d', size=12,
            italic=False, color=ORANGE, dx=-4, dy=-22, anchor='end')
    g3.curve(own_west_cubic_profile, 0, 0.5, stroke=PURPLE, width=1.4,
             dash='2 3')
    g2.dot(vmax, west_side_profile(vmax), r=3.2, fill=BLUE)
    save(f, 'appendix-c/profiles', 'Three graphs. (a) For D on its own axis, the '
         'largest transverse coordinate allowed by the disk, falling from '
         'about 0.46 at d = 0 to about 0.18 at pi over 4, below the bound '
         '0.97 minus (cos d + sin d)/2 of Lemma C.5 and, on 1/2 to pi over 4, '
         'just below the line 31/100 minus 17d/100, which it nearly touches '
         'at both ends. (b) For W on the west side, the largest value of '
         'minus b, below the line 47/100 minus 2v/3. (c) For W on its own '
         'axis, the largest value of |b|, below the line 233/500 minus '
         '73v/100, which it nearly touches at v = 1/2; the dotted curve is '
         'the bound obtained from the Taylor polynomials')


# ---------------------------------------------------------------------------
# Figure C.8: the coupled reserve of D and S on the triangle (Lemma C.12).

def coupled_reserve(d, s_):
    return (0.387 * math.cos(s_ - d) + math.sin(s_) * math.cos(d)
            - 0.613 * math.cos(d) - (0.557 + (s_ - d) / 3) * math.sin(s_))


def contour_segments(fn, x0, x1, y0, y1, level, n=80):
    """The segments of the level set fn = level, by marching squares."""
    segs = []
    xs = [x0 + (x1 - x0) * i / n for i in range(n + 1)]
    ys = [y0 + (y1 - y0) * j / n for j in range(n + 1)]
    val = [[fn(x, y) - level for y in ys] for x in xs]
    for i in range(n):
        for j in range(n):
            corners = [(xs[i], ys[j], val[i][j]),
                       (xs[i + 1], ys[j], val[i + 1][j]),
                       (xs[i + 1], ys[j + 1], val[i + 1][j + 1]),
                       (xs[i], ys[j + 1], val[i][j + 1])]
            pts = []
            for k in range(4):
                (ax, ay, av), (bx, by, bv) = corners[k], corners[(k + 1) % 4]
                if (av < 0) != (bv < 0):
                    t = av / (av - bv)
                    pts.append((ax + t * (bx - ax), ay + t * (by - ay)))
            if len(pts) == 2:
                segs.append(tuple(pts))
            elif len(pts) == 4:
                segs += [(pts[0], pts[1]), (pts[2], pts[3])]
    return segs


def overtake():
    W_, H_ = 470, 400
    f = pixel_figure(W_, H_)
    lo, hi = 0.5, 2 / 3
    g = Plot(f, 70, 52, 330, 300, (0.48, 0.69), (0.48, 0.69))
    tri = [(lo, lo), (lo, hi), (hi, hi)]
    g.polygon(tri, fill=FILLS[2], stroke=GREEN, width=1.8)
    for level in (0.005, 0.01, 0.02, 0.03, 0.04):
        for a, b in contour_segments(coupled_reserve, lo, hi, lo, hi, level):
            m = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
            if m[0] <= m[1] + 1e-12:
                g.line(a, b, stroke=GREEN, width=1)
    vals = {p: coupled_reserve(*p) for p in ((lo, lo), (lo, hi), (hi, hi))}
    assert min(vals.values()) > 0.0027
    for (x, y), val, (dx, dy, anc) in (((lo, lo), vals[(lo, lo)],
                                        (8, 16, 'start')),
                                       ((lo, hi), vals[(lo, hi)],
                                        (8, -12, 'start')),
                                       ((hi, hi), vals[(hi, hi)],
                                        (8, 2, 'start'))):
        g.dot(x, y, r=3.6, fill=GREEN)
        g.text(x, y, f'{val:.5f}', size=13, italic=False, color=INK, dx=dx,
               dy=dy, anchor=anc)
    g.line((0.48, 0.48), (0.69, 0.69), stroke=FAINT, width=1, dash='4 4')
    g.axes([(lo, '1/2'), (0.6, '0.6'), (hi, '2/3')],
           [(lo, '1/2'), (0.6, '0.6'), (hi, '2/3')], xlabel='d', ylabel='s')
    g.text(0.615, 0.585, 's = d', size=13, italic=False, color=FAINT)
    save(f, 'appendix-c/overtake', 'The triangle of the angles d and s with d '
         'from 1/2 to s and s up to 2/3, in green, with level lines of the '
         'reserve of Lemma C.12 at 0.005, 0.01, 0.02, 0.03 and 0.04; the '
         'reserve is about 0.0027 at the vertex (1/2, 1/2), 0.0076 at '
         '(1/2, 2/3) and 0.047 at (2/3, 2/3)')


# ---------------------------------------------------------------------------
# Figure C.9: the walls in the plane of the angles (Lemma 9.42 (1)).

def walls():
    W_, H_ = 860, 330
    f = pixel_figure(W_, H_)
    xr = (0.44, 0.84)
    for k, (yr, name, lo_, hi_, below) in enumerate((
            ((-0.75, 0.72), 'w', -2 / 3, 5 / 8, True),
            ((-0.72, 0.75), 's', -5 / 8, 2 / 3, False))):
        g = Plot(f, 60 + 430 * k, 42, 340, 262, xr, yr)
        box = [(0.5, lo_), (PI / 4, lo_), (PI / 4, hi_), (0.5, hi_)]
        g.polygon(box, fill='none', stroke=FAINT, width=1, dash='4 4')
        wall = [(0.5, 0.5 - PI / 4), (PI / 4, 0.0)]
        if below:
            region = [(0.5, lo_), (PI / 4, lo_), (PI / 4, 0.0),
                      (0.5, 0.5 - PI / 4)]
        else:
            region = [(0.5, 0.5 - PI / 4), (PI / 4, 0.0), (PI / 4, hi_),
                      (0.5, hi_)]
        g.polygon(region, fill=FILLS[3], stroke='none', opacity=0.8)
        g.line(*wall, stroke=PURPLE, width=2.2)
        g.dot(PI / 4, 0.0, r=4, fill=INK)
        g.text(PI / 4, 0.0, 'model', size=12, italic=False, dx=-8, dy=-12,
               anchor='end')
        g.axes([(0.5, '1/2'), (PI / 4, 'π/4')],
               [(lo_, '−2/3' if k == 0 else '−5/8'), (0, '0'),
                (hi_, '5/8' if k == 0 else '2/3')], xlabel='d',
               ylabel=name)
        g.hline(0, stroke=FAINT, dash='2 4', width=1, a=0.5, b=PI / 4)
        txt = 'w = d − π/4' if k == 0 else 's = d − π/4'
        g.text(0.58, 0.58 - PI / 4, txt, size=13, italic=False,
               color=PURPLE, dx=0, dy=-24 if k == 0 else 24, anchor='start')
        g.text(0.8, yr[1], '(a)' if k == 0 else '(b)', size=14, italic=False,
               dx=0, dy=12, anchor='start')
    save(f, 'appendix-c/walls', 'Two panels in the plane of the angles. (a) d from '
         '1/2 to pi over 4 against w in its window from minus 2/3 to 5/8: the '
         'wall w = d minus pi over 4 runs from about (1/2, -0.29) to the '
         'model point (pi over 4, 0); W and D can be separated along the '
         'secondary axis of D only below it, in the shaded region. (b) The '
         'same for s, with the wall s = d minus pi over 4: D and S can be '
         'separated along the secondary axis of D only above it')


# ---------------------------------------------------------------------------
# Figure C.11: the double separation at D (Lemma 9.42 (2)).

def double_configuration(w, s_, d, c):
    """W and S on their own axes and D on its own axis, all at equality, with
    W, D and D, S separated along the secondary axis of D at equality; the
    transverse coordinate of D balances the excesses of W and S."""
    tw, td, ts = PI + w, PI + d, 1.5 * PI + s_
    aw, as_, ad = own_radial(tw, c), own_radial(ts, c), own_radial(td, c)
    q1, q2 = d - w, d - s_

    def charts(bd):
        bw = (bd + aw * math.sin(q1) - tau(q1)) / math.cos(q1)
        bs = (tau(q2) + bd - as_ * math.cos(q2)) / math.sin(q2)
        return aw, bw, ad, bd, as_, bs

    bd = solve_free(lambda t: (chart_excess(*charts(t)[:2]),
                               chart_excess(*charts(t)[4:])), -0.2, 0.2)
    return charts(bd)


def double():
    c = (C0, C0)
    w, s_, d = -0.35, 0.35, PI / 4
    tw, td, ts = PI + w, PI + d, 1.5 * PI + s_
    aw, bw, ad, bd, as_, bs = double_configuration(w, s_, d, c)
    cw, cd, cs = centre(tw, aw, bw), centre(td, ad, bd), centre(ts, as_, bs)
    e2 = u(td + PI / 2)
    assert abs(dot(e2, shift(cd, cw, -1)) - tau(d - w)) < 1e-9
    assert abs(dot(e2, shift(cs, cd, -1)) - tau(PI / 2 + s_ - d)) < 1e-9
    FWc = shift(u(tw), e2, -1)
    FSc = shift(u(ts), e2, 1)
    FCc = shift(shift((0, 0), u(tw), -1), u(ts), -1)
    k = 0.42
    pts = [q for t, a, b in ((tw, aw, bw), (ts, as_, bs), (td, ad, bd))
           for q in square_corners(centre(t, a, b), math.degrees(t))]
    pts += [shift(cw, FWc, k + 0.3), shift(cs, FSc, k + 0.3)]
    xmin = min(min(x for x, y in pts), -R0) - 0.08
    ymin = min(min(y for x, y in pts), -R0) - 0.08
    xmax = max(max(x for x, y in pts), R0) + 0.08
    ymax = max(max(y for x, y in pts), R0) + 0.08
    f = Figure(xmin, xmax, ymin, ymax, 112)
    f.circle((0, 0), R0, stroke=INK, width=1.1, dash='6 4')
    f.square(c, 0, fill=GREY, stroke=FAINT, opacity=0.9)
    f.text((c[0] - 0.22, c[1] + 0.24), 'C', size=16)
    for t, a, b, fill, stroke in ((tw, aw, bw, FW, BLUE),
                                  (ts, as_, bs, FS, GREEN),
                                  (td, ad, bd, FD, PURPLE)):
        f.square(centre(t, a, b), math.degrees(t), fill=fill, stroke=stroke,
                 opacity=0.8, width=1.6)
    # The two lines of the sides of D across which W and S are separated.
    m = u(td)
    for sgn in (-1, 1):
        p = shift(cd, e2, 0.5 * sgn)
        f.line(shift(p, m, -1.25), shift(p, m, 1.0), stroke=PURPLE,
               width=1.2, dash='5 4')
    for t, a, b in ((tw, aw, bw), (ts, as_, bs)):
        v = far_corner(t, a, b)
        r = math.hypot(*v)
        assert r > R0
        f.line(shift((0, 0), v, R0 / r), v, stroke=PINK, width=3.2)
        f.dot(v, r=4.2, fill=PINK)
    # Forces: on W, n_W - e2; on S, n_S + e2; on D, e2 - e2 = 0; on C.
    for p0, F, name, extra in ((cw, FWc, 'W', (0.0, 0.12)),
                               (cs, FSc, 'S', (0.14, 0.0)),
                               (c, FCc, 'C', (0.1, 0.08))):
        tip = shift(p0, F, k)
        arrow(f, p0, tip, color=ORANGE, width=2.4, head=0.09)
        L = math.hypot(*F)
        label(f, shift(shift(tip, F, 0.17 / L), extra), 'F', name, size=15,
              color=ORANGE)
    for sgn in (-1, 1):
        arrow(f, cd, shift(cd, e2, 0.36 * sgn), color=ORANGE, width=1.6,
              head=0.07)
    label(f, shift(cd, e2, 0.58), 'e', '2', 'D', size=14, color=ORANGE)
    label(f, shift(cd, e2, -0.6), '−e', '2', 'D', size=14, color=ORANGE)
    f.text(shift(cw, (-0.2, 0.28)), 'W', size=17, color=BLUE)
    f.text(shift(cs, (0.3, -0.22)), 'S', size=17, color=GREEN)
    f.text(shift(cd, (-0.36, -0.08)), 'D', size=17, color=PURPLE)
    f.dot((0, 0), r=2.5)
    save(f, 'appendix-c/double', 'The double separation at D, at w = -0.35, '
         'd = pi over 4 and s = 0.35, with W and S separated from C along '
         'their own axes and from D across the two sides of D parallel to its '
         'primary axis (dashed), all at equality; the far vertices of W and S '
         'leave the dashed circle of radius R0. The two unit forces on D, '
         'plus and minus its secondary axis, cancel; the forces on W, S and C '
         'are drawn as arrows')


# ---------------------------------------------------------------------------
# Figure C.10: the cost of a wing (Lemma C.17).

def chart_support(U, V, steps=4000):
    """The largest U a + V b over the charts in the ceiling, for U > 0: it is
    taken on the arc of the circle where (a + 1/2, |b| + 1/2) lies, with b of
    the sign of V."""
    t0 = math.asin(0.5 / R0)
    best = -1e9
    for k in range(steps + 1):
        t = t0 + (PI / 4 - t0) * k / steps
        a = R0 * math.cos(t) - 0.5
        b = R0 * math.sin(t) - 0.5
        best = max(best, U * a + abs(V) * b)
    return best


def wing_cost(q):
    return omega(q) - chart_support(1 + math.sin(q), math.cos(q))


def folded(q):
    return PI / 2 - abs(q - PI / 2)


def cost():
    W_, H_ = 640, 330
    f = pixel_figure(W_, H_)
    g = Plot(f, 66, 46, 540, 252, (0.45, PI - 0.45), (0, 0.04))
    line_ = lambda q: -0.73 - 0.65 * folded(q)
    vertex = lambda q: omega(q) - (1.689 * (81 / 56 + 4 / 7 * math.sin(q))
                                   - (1 + math.sin(q) + abs(math.cos(q))) / 2)
    capb = lambda q: omega(q) - 1.113 * (1 + math.sin(q))
    g.curve(lambda q: wing_cost(q) - line_(q), 0.5, PI - 0.5, stroke=BLUE,
            width=2.4, n=220)
    for a, b, fn, col in ((0.5, 1, vertex, GREEN), (1, PI / 2, capb, PURPLE),
                          (PI / 2, PI - 1, capb, PURPLE),
                          (PI - 1, PI - 0.5, vertex, GREEN)):
        g.curve(lambda q, fn=fn: fn(q) - line_(q), a, b, stroke=col,
                width=1.8, dash='6 4')
    for k in range(201):
        q = 0.5 + (PI - 1) * k / 200
        lower = vertex(q) if (q <= 1 or q >= PI - 1) else capb(q)
        assert wing_cost(q) >= lower - 1e-9
        assert lower > line_(q)
    for x in (1, PI / 2, PI - 1):
        g.vline(x, lo=0, hi=0.04)
    g.axes([(0.5, '1/2'), (1, '1'), (PI / 2, 'π/2'), (PI - 1, 'π − 1'),
            (PI - 0.5, 'π − 1/2')],
           [(0, '0'), (0.01, '0.01'), (0.02, '0.02'), (0.03, '0.03')],
           xlabel='q')
    g.text(0.75, 0.0115, 'far vertex', size=12, italic=False, color=GREEN)
    g.text(1.29, 0.0172, 'cap', size=12, italic=False, color=PURPLE)
    g.text(1.43, 0.0265, 'least cost', size=12, italic=False, color=BLUE,
           anchor='end')
    save(f, 'appendix-c/cost', 'The cost of a wing less the folded line minus 0.73 '
         'minus 0.65 times the folded angle, for the phase gap q from 1/2 to '
         'pi minus 1/2, symmetric about pi over 2: in blue for the least cost '
         'over the charts in the ceiling, dashed for the lower bounds of the '
         'proof, from the far vertex with the tangent of the square root up '
         'to 1 and from the cap between 1 and pi over 2; all are positive, '
         'the bounds of the proof by at least 0.004')


# ---------------------------------------------------------------------------
# Figure C.12: S on its own axis at a negative angle (Lemma 9.43 (1)).

def south_defect(d, v):
    U = 0.31 - 0.17 * d
    A = RHO0 - 0.31 * (U + U * U)
    th = d + v
    return (C0 + RHO0 * math.tan(v / 2) - 0.5 + (A - 0.5) * math.cos(th)
            + (U - 0.5) * math.sin(th))


def south_sign():
    W_, H_ = 900, 320
    f = pixel_figure(W_, H_)
    g1 = Plot(f, 66, 46, 330, 238, (0.5, PI / 4 + 0.01), (-0.22, 0.02))
    g2 = Plot(f, 526, 46, 340, 238, (0, 0.65), (-0.27, 0.02))
    # (a) the separation along the secondary axis of D.
    g1.hline(0, stroke=INK, dash=None, width=0.8)
    bd = lambda d: math.cos(d) / 2 - 0.387 * math.sin(d) - 11 / 40
    g1.curve(bd, 0.5, PI / 4, stroke=BLUE, width=2.4)
    g1.dot(0.5, bd(0.5), r=3.4, fill=BLUE)
    g1.text(0.5, bd(0.5), f'{bd(0.5):.4f}', size=12, italic=False,
            color=BLUE, dx=8, dy=-10, anchor='start')
    g1.axes([(0.5, '1/2'), (0.6, '0.6'), (0.7, '0.7'), (PI / 4, 'π/4')],
            [(-0.2, '−0.2'), (-0.1, '−0.1'), (0, '0')], xlabel='d')
    g1.text(0.5, 0.02, '(a)', size=14, italic=False, dx=10, dy=10,
            anchor='start')
    # (b) the separation along the secondary axis of S.
    g2.hline(0, stroke=INK, dash=None, width=0.8)
    for d, col in ((0.5, BLUE), (PI / 4, CYAN)):
        g2.curve(lambda v, d=d: south_defect(d, v), 0, 0.625, stroke=col,
                 width=2.4 if d == 0.5 else 1.6)
    g2.curve(lambda v: -0.387 + 1.113 * 0.55 * v + 0.34 * math.cos(v)
             - 0.49 * math.sin(v), 0, 0.625, stroke=ORANGE, width=1.6,
             dash='6 4')
    g2.curve(lambda v: -0.047 + 0.12215 * v - 0.1134 * v * v, 0, 0.625,
             stroke=PURPLE, width=1.6, dash='2 3')
    for k in range(101):
        v = 0.625 * k / 100
        assert south_defect(PI / 4, v) <= south_defect(0.5, v) <= (
            -0.387 + 1.113 * 0.55 * v + 0.34 * math.cos(v)
            - 0.49 * math.sin(v)) <= (-0.047 + 0.12215 * v - 0.1134 * v * v
                                     + 1e-12) < 0
    g2.axes([(0, '0'), (0.25, '1/4'), (0.5, '1/2'), (0.625, '5/8')],
            [(-0.2, '−0.2'), (-0.1, '−0.1'), (0, '0')], xlabel='v')
    g2.text(0, 0.02, '(b)', size=14, italic=False, dx=10, dy=10,
            anchor='start')
    g2.text(0.05, south_defect(0.5, 0.05), 'd = 1/2', size=12, italic=False,
            color=BLUE, dx=0, dy=16, anchor='start')
    g2.text(0.33, south_defect(PI / 4, 0.33), 'd = π/4', size=12,
            italic=False, color=CYAN, dx=0, dy=-12, anchor='start')
    save(f, 'appendix-c/south-sign', 'Two graphs below zero. (a) For d from 1/2 to '
         'pi over 4, the bound (cos d - sin d)/2 + c0 sin d - 11/40 of the '
         'separation of D and S along the secondary axis of D, in blue, and '
         'the bound cos d/2 - 0.387 sin d - 11/40, dashed, both negative. '
         '(b) For v from 0 to 5/8, the bound of the separation along the '
         'secondary axis of S at d = 1/2 and at d = pi over 4, below its '
         'trigonometric upper bound at d = 1/2, dashed, and the quadratic '
         'upper bound, dotted, all negative')


# ---------------------------------------------------------------------------
# Figure C.13: two own wings (Lemma 9.43 (2)).

def own_wings():
    W_, H_ = 880, 330
    f = pixel_figure(W_, H_)
    g1 = Plot(f, 66, 46, 330, 250, (0, 0.7), (0.85, 1.22))
    profile = lambda x: 0.5 + 0.387 * math.cos(x) + 0.61 * math.sin(x)
    line_ = lambda x: RHO0 + 9 / 25 * (x - 12 / 25)
    lo, hi = 22 / 75, 2 / 3
    g1.polygon([(lo, 0.85), (hi, 0.85), (hi, 1.22), (lo, 1.22)],
               fill=FILLS[6], stroke='none', opacity=0.8)
    g1.curve(profile, 0, 0.7, stroke=BLUE, width=2.4)
    g1.curve(line_, 0, 0.7, stroke=ORANGE, width=1.6, dash='6 4')
    g1.hline(RHO0, stroke=FAINT, dash='3 3', width=1)
    for k in range(101):
        x = lo + (hi - lo) * k / 100
        assert profile(x) > line_(x)
    g1.dot(12 / 25, RHO0, r=3.4, fill=ORANGE)
    g1.axes([(0, '0'), (lo, '22/75'), (12 / 25, '12/25'), (hi, '2/3')],
            [(0.9, '0.9'), (1.0, '1'), (1.2, '1.2')], xlabel='x')
    label(f, shift(g1.q(0, RHO0), (-14, 0)), 'ρ', '0', '', size=14)
    g1.text(0.03, profile(0.03), 'profile', size=12, italic=False,
            color=BLUE, dx=2, dy=16, anchor='start')
    g1.text(0.02, line_(0.02), 'line', size=12, italic=False, color=ORANGE,
            dx=0, dy=-12, anchor='start')
    g1.text(0, 1.22, '(a)', size=14, italic=False, dx=10, dy=10,
            anchor='start')
    # (b) The plane of the angles w and s of two own wings.
    g2 = Plot(f, 526, 46, 300, 250, (-0.75, 0.1), (-0.1, 0.75))
    g2.polygon([(-2 / 3, 0), (0, 0), (0, 2 / 3), (-2 / 3, 2 / 3)],
               fill='none', stroke=FAINT, width=1, dash='4 4')
    g2.polygon([(-2 / 3, 22 / 75 + 0 * 0), (-22 / 75, 2 / 3), (-2 / 3, 2 / 3)],
               fill=FILLS[4], stroke=PINK, width=1.6)
    g2.line((-2 / 3, 22 / 75), (-22 / 75, 2 / 3), stroke=PINK, width=2)
    g2.dot(0, 0, r=4, fill=INK)
    g2.text(0, 0, 'model', size=12, italic=False, dx=-6, dy=14, anchor='end')
    g2.axes([(-2 / 3, '−2/3'), (-22 / 75, '−22/75'), (0, '0')],
            [(0, '0'), (22 / 75, '22/75'), (2 / 3, '2/3')], xlabel='w',
            ylabel='s')
    g2.text(-0.56, 0.6, 's − w ≥ 24/25', size=13, italic=False, color=PINK,
            dx=0, dy=0, anchor='middle')
    g2.text(-0.75, 0.75, '(b)', size=14, italic=False, dx=36, dy=10,
            anchor='start')
    save(f, 'appendix-c/own-wings', 'Two panels. (a) The profile one half plus '
         '0.387 cos x plus 0.61 sin x, in blue, above the dashed line of '
         'slope 9/25 through rho0 at 12/25 on the shaded interval from 22/75 '
         'to 2/3. (b) The square of the angles w from minus 2/3 to 0 and s '
         'from 0 to 2/3 of two own wings, with the corner triangle where s '
         'minus w is at least 24/25, which the lemma excludes')


def main():
    model_frames()
    dominance()
    turn()
    own_stress()
    west_stress()
    domains()
    profiles()
    overtake()
    walls()
    cost()
    double()
    south_sign()
    own_wings()


if __name__ == '__main__':
    main()

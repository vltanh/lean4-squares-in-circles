#!/usr/bin/env python3
"""Draw the figures of Appendix H (docs/proof/appendix-h.md), seven squares:
the critical gap, the inward axis, in docs/proof/figures/appendix-h/.

    python3 scripts/figures/fig_apph.py

Every figure is computed from the functions and states of the appendix: the
canonical pairs from the labels and the relative phase, the graphs and the
bounds of the proofs by sampling the functions, and the label regions by
clipping the admissible region with the lines of the labels. The boundary
curves are those of Definitions G.9 and G.13: circle_a is gamma, tie_line is
lambda, axial_top is chi, tie_a is alpha, diagonal is delta and side_top is the
top (a-hat, u-hat) of a side label.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           sb, clip)
from fig_front import sbn, it

PI = math.pi
SQRT3 = math.sqrt(3)
BLUE, ORANGE, GREEN, PURPLE, PINK = COLORS[:5]

# ---------------------------------------------------------------------------
# The states, labels and boundary functions of Chapter 10 and Appendix G.


def axial(u_):
    return 5 * u_ / 4


def side(a, u_):
    return PI / 6 + (u_ - 0.5) / 3 + 3 * (1 - a) / 4


def label(a, u_):
    return min(axial(u_), side(a, u_), PI / 4)


def phi(a, u_):
    return (a + 0.5) ** 2 + (u_ + 0.5) ** 2


def remainder(a, u_):
    return 4 - 3 * a - 2 * u_


def admissible(a, u_, tol=1e-9):
    return (-tol <= u_ <= a + tol and a >= 0.5 - tol
            and phi(a, u_) <= 13 / 4 + tol)


def circle_a(w):
    """gamma(w): the circle phi = 13/4 as a graph over the second
    coordinate."""
    return math.sqrt(13 / 4 - (w + 0.5) ** 2) - 0.5


def tie_line(w):
    """lambda(w): the tie line as a graph over the second coordinate."""
    return (2 * PI + 7 - 11 * w) / 9


def axial_top(w):
    """chi(w): the top of the axial region."""
    return min(circle_a(w), tie_line(w))


def tie_a(x):
    """alpha(x): the first coordinate of the tie state of label x."""
    return (2 * PI + 7) / 9 - 44 / 45 * x


def diagonal(x):
    return (2 * PI + 7 - 12 * x) / 5


M = 2 * PI + 17
JJ = math.sqrt(202 * 13 / 4 - M ** 2)
A0 = (9 * M + 11 * JJ) / 202 - 0.5
U0 = (11 * M - 9 * JJ) / 202 - 0.5
S0 = 5 / 4 * U0
RD = math.sqrt(13 / 8) - 0.5
TD = PI / 6 + 7 / 12 - 5 / 12 * RD
THD = TD + S0 - PI / 6                  # theta_d of Lemma G.19


def side_top(x):
    """(a-hat(x), u-hat(x)): the upper end of the segment of side label x."""
    if x > TD:
        return diagonal(x), diagonal(x)
    n = 97 / 144
    d = PI / 6 + 19 / 24 - x
    z = math.sqrt(n * 13 / 4 - d * d)
    X = (0.75 * d + z / 3) / n
    Y = (-d / 3 + 0.75 * z) / n
    return X - 0.5, Y - 0.5


def J(a, A, v, e):
    return 0.5 - a - A * math.sin(e) + abs(math.sin(e)) / 2 + \
        (v + 0.5) * math.cos(e)


def upper(z, x):
    """U(z, x) of Definition H.21."""
    nu = 0.8 * (z + PI / 6 - x)
    return J(side_top(x)[0], axial_top(nu), nu, z)


def polyline(f, pts, stroke=INK, width=1.6, dash=None):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')


def open_dot(f, c, r=3.6, stroke=INK):
    x, y = f.p(*c)
    f.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="#ffffff" '
          f'stroke="{stroke}" stroke-width="1.6"/>')


# ---------------------------------------------------------------------------
# Graphs of one-variable functions, with separate scales on the two axes.


class Graph:
    """A graph with its own scales on the two axes. It fills a Figure of its
    own, or is a panel of the Figure `fig` with its origin at the pixel
    `at`."""

    def __init__(self, x0, x1, y0, y1, width=520, height=280, left=58,
                 right=24, top=18, bottom=44, fig=None, at=(0, 0)):
        self.x0, self.x1, self.y0, self.y1 = x0, x1, y0, y1
        self.kx = width / (x1 - x0)
        self.ky = height / (y1 - y0)
        self.width, self.height = width, height
        self.at = at
        self.f = fig if fig is not None else Figure(
            -left, width + right, -bottom, height + top, 1, pad=0)

    def q(self, x, y):
        return (self.at[0] + (x - self.x0) * self.kx,
                self.at[1] + (y - self.y0) * self.ky)

    def axes(self, xticks, yticks, xname='', yname=''):
        f = self.f
        f.line(self.q(self.x0, self.y0), self.q(self.x1, self.y0), width=1)
        f.line(self.q(self.x0, self.y0), self.q(self.x0, self.y1), width=1)
        for x, s in xticks:
            p = self.q(x, self.y0)
            f.line(p, (p[0], p[1] - 5), width=1)
            f.text((p[0], p[1] - 16), s, size=13, italic=False)
        for y, s in yticks:
            p = self.q(self.x0, y)
            f.line(p, (p[0] - 5, p[1]), width=1)
            f.text((p[0] - 8, p[1]), s, size=13, italic=False, anchor='end')
        if xname:
            p = self.q(self.x1, self.y0)
            f.text((p[0] + 4, p[1] - 30), xname, size=15, anchor='end')
        if yname:
            p = self.q(self.x0, self.y1)
            f.text((p[0] + 8, p[1] - 4), yname, size=15, anchor='start')

    def curve(self, fn, a=None, b=None, n=400, **kw):
        a = self.x0 if a is None else a
        b = self.x1 if b is None else b
        pts = [self.q(a + (b - a) * k / n, fn(a + (b - a) * k / n))
               for k in range(n + 1)]
        polyline(self.f, pts, **kw)

    def points(self, pts, **kw):
        polyline(self.f, [self.q(x, y) for x, y in pts], **kw)

    def dot(self, x, y, r=3.2, fill=INK):
        self.f.dot(self.q(x, y), r=r, fill=fill)

    def text(self, x, y, s, **kw):
        self.f.text(self.q(x, y), s, **kw)

    def hline(self, y, **kw):
        self.f.line(self.q(self.x0, y), self.q(self.x1, y), **kw)

    def legend(self, rows, x, y, dy, length, size=13):
        """Rows (markup, colour, dash, italic) downwards from the data point
        (x, y), dy apart: a short line of that colour and dash, then the
        text; the dash 'band' draws a shaded box instead of a line."""
        for k, (s, color, dash, italic) in enumerate(rows):
            yk = y - k * dy
            if dash == 'band':
                h = 0.28 * dy
                self.f.polygon([self.q(x, yk - h), self.q(x + length, yk - h),
                                self.q(x + length, yk + h),
                                self.q(x, yk + h)],
                               fill=FILLS[3], stroke='none')
                color = PURPLE
            else:
                self.points([(x, yk), (x + length, yk)], stroke=color,
                            width=2.2 if dash is None else 1.8, dash=dash)
            self.text(x + length, yk, s, color=color, size=size,
                      italic=italic, anchor='start', dx=8)


# ---------------------------------------------------------------------------
# Figure H.1: the canonical pair on the inward axis in four sectors.


def canonical_pair(a, uu, A, v, s, t):
    """The squares S and T of the canonical pair at the gap pi/3, in the chart
    of S: centres, turning angles (degrees), and the two markers."""
    l1, l2 = label(a, uu), label(A, v)
    d = PI / 3 + s * l1 - t * l2
    cs = (a, s * uu)
    ct = (A * math.cos(d) - t * v * math.sin(d),
          A * math.sin(d) + t * v * math.cos(d))
    return cs, ct, math.degrees(d), s * l1, s * l1 + PI / 3


def pair_panel(f, off, title, a, uu, A, v, s, t, y_sh=-1.28):
    def P(p):
        return (p[0] + off[0], p[1] + off[1])

    cs, ct, ddeg, m1, m2 = canonical_pair(a, uu, A, v, s, t)
    S = square_corners(cs)
    T = square_corners(ct, ddeg)
    f.circle(P((0, 0)), 1, stroke=FAINT, dash='4 4')
    f.polygon([P(q) for q in S], fill=FILLS[0], stroke=BLUE, opacity=0.7)
    f.polygon([P(q) for q in T], fill=FILLS[2], stroke=GREEN, opacity=0.6)
    f.polygon([P(q) for q in S], stroke=BLUE)
    for c, deg, color in ((cs, 0.0, BLUE), (ct, ddeg, GREEN)):
        for t0, t1 in arcs_in(lambda q: in_open_square(q, c, deg), 1):
            f.arc(P((0, 0)), 1, t0, t1, color, width=4)
    for m, color in ((m1, BLUE), (m2, GREEN)):
        f.line(P((0, 0)), P(u(m)), stroke=color, width=1, dash='3 3')
        f.dot(P(u(m)), r=4.2, fill=color)
    f.dot(P((0, 0)))
    f.text(P((-0.07, -0.1)), 'o', anchor='end')
    f.text(P(shift(cs, (0.3, -0.33))), 'S', size=16, color=BLUE)
    # T in the outer part of the square, clear of the arc of the unit circle
    rt = math.hypot(*ct)
    f.text(P(shift(ct, (ct[0] / rt, ct[1] / rt), 0.3)), 'T', size=16,
           color=GREEN)
    # Shadows on the line of n_2.
    s_lo, s_hi = a - 0.5, a + 0.5
    t_lo = min(q[0] for q in T)
    t_hi = max(q[0] for q in T)
    sigma = t_hi - s_lo
    # the closed form (H.1) of the inward sum, for s = +1
    e = label(a, uu) - t * label(A, v) - PI / 6
    closed = (0.5 - a - A * math.sin(e) + abs(math.sin(e)) / 2
              + (0.5 - t * v) * math.cos(e))
    assert s == 1 and abs(sigma - closed) < 1e-12
    f.line(P((-1.15, y_sh)), P((1.72, y_sh)), width=1)
    f.line(P((-0.75, y_sh + 0.2)), P((-1.1, y_sh + 0.2)), width=1.4,
           arrow=True)
    f.text(P((-0.93, y_sh + 0.33)), sb('n', '2'), size=14)
    f.line(P((s_lo, y_sh + 0.05)), P((s_hi, y_sh + 0.05)), stroke=BLUE,
           width=5)
    f.line(P((t_lo, y_sh - 0.05)), P((t_hi, y_sh - 0.05)), stroke=GREEN,
           width=5)
    f.line(P((s_lo, cs[1] - 0.5)), P((s_lo, y_sh + 0.05)), stroke=BLUE,
           width=1, dash='3 3')
    xt = max(T, key=lambda q: q[0])
    f.line(P(xt), P((xt[0], y_sh - 0.05)), stroke=GREEN, width=1, dash='3 3')
    if sigma > 1e-9:
        f.line(P((s_lo, y_sh - 0.15)), P((t_hi, y_sh - 0.15)), stroke=ORANGE,
               width=4)
    f.text(P(((s_lo + max(t_hi, s_lo + 0.3)) / 2, y_sh - 0.32)),
           sbn('σ', '2', f' = {sigma:.2f}' if sigma > 1e-9 else ' = 0', 13),
           size=13, color=ORANGE)
    f.text(P((0.25, 2.12)), title, size=14, italic=False)
    return sigma


def inward_sectors():
    w, h = 3.05, 4.05
    f = Figure(-1.25, -1.25 + 2 * w, -1.72 - h, 2.22, 100)
    panels = [
        ((0, 0), '(a) axial, axial; (+, +)', (1.05, 0.2, 0.95, 0.15, 1, 1)),
        ((w, 0), '(b) a contact; (+, +)', (1.0, 0.5, 1.0, 0.0, 1, 1)),
        ((0, -h), '(c) side target; (+, +)', (1.1, 0.1, 1.0, 0.5, 1, 1)),
        ((w, -h), '(d) opposite signs; (+, −)', (1.0, 0.5, 1.0, 0.1, 1, -1)),
    ]
    for off, title, (a, uu, A, v, s, t) in panels:
        assert admissible(a, uu) and admissible(A, v)
        sigma = pair_panel(f, off, title, a, uu, A, v, s, t)
        assert sigma >= -1e-12
    f.save('appendix-h/inward-sectors', 'The canonical pair on the inward axis in '
           'four sectors, with the shadows of the two squares on the line of '
           'n_2')


# ---------------------------------------------------------------------------
# Section H.2: the turn profiles.


def profile(z):
    return math.sin(z) - 0.8 * z * math.cos(z) - 0.75 * (1 - math.cos(z))


def quintic(z):
    """q: the Taylor bounds give p(z) >= z q(z)."""
    return (1 / 5 - 3 * z / 8 + 7 * z ** 2 / 30 + z ** 3 / 32 - z ** 4 / 30
            - z ** 5 / 960)


def quadratic(z):
    """The quadratic part (9z^2 - 15z + 8)/40 of q."""
    return (9 * z ** 2 - 15 * z + 8) / 40


def factored_error(z):
    """q(z) - quadratic(z), nonnegative for 0 <= z <= 1."""
    return z ** 2 / 960 * (5 + (1 - z) * (z ** 2 + 33 * z + 3))


def check_profile_bounds():
    """The identity and the inequalities of the proof of Lemma H.2."""
    for k in range(158):
        z = k / 100
        assert abs(quintic(z) - quadratic(z) - factored_error(z)) < 1e-15
        assert abs(9 * z ** 2 - 15 * z + 8 - (3 * z - 2.5) ** 2 - 7 / 4) \
            < 1e-12
        if z <= 1:
            assert factored_error(z) >= 0
            assert profile(z) >= z * quintic(z) - 1e-15
            assert z * quadratic(z) >= z / 40
        else:
            assert profile(z) - z / 20 >= profile(z - 0.01) - (z - 0.01) / 20
    assert abs(quadratic(1) - 1 / 20) < 1e-15


def turn_profile():
    check_profile_bounds()
    g = Graph(0, PI / 2, 0, 0.26)
    g.axes([(0, '0'), (0.5, '0.5'), (1, '1'), (PI / 2, 'π/2')],
           [(0, '0'), (0.1, '0.1'), (0.2, '0.2')], xname='z')
    g.curve(lambda z: z / 40, stroke=FAINT, width=1.6)
    g.curve(lambda z: z * quadratic(z), 0, 1, stroke=ORANGE, width=1.8,
            dash='6 4')
    g.curve(lambda z: z / 20, 1, PI / 2, stroke=GREEN, width=1.8,
            dash='6 4')
    g.curve(profile, stroke=BLUE, width=2.2)
    g.dot(1, 1 / 20)
    g.legend([('p(z)', BLUE, None, True),
              ('z(9z² − 15z + 8)/40,  0 ≤ z ≤ 1', ORANGE, '6 4', True),
              ('z/20,  1 ≤ z ≤ π/2', GREEN, '6 4', True),
              ('z/40', FAINT, None, True)], 0.05, 0.245, 0.024, 0.14)
    g.f.save('appendix-h/turn-profile', 'The turn profile p above the line z/40, '
             'with the lower bounds of the proof: the bound of part (1) on '
             '[0, 1] and the line z/20 on [1, pi/2], which meet at z = 1')


def profile_split():
    W, H, gap = 300, 230, 84
    f = Figure(-58, 2 * W + gap + 24, -44, H + 46, 1, pad=0)
    # (a) 0 <= z <= 1: the Taylor bound z q(z) is the cubic z quadratic(z)
    # plus the factored error.
    a = Graph(0, 1, 0, 0.07, width=W, height=H, fig=f)
    a.axes([(0, '0'), (0.5, '0.5'), (1, '1')],
           [(0, '0'), (0.02, '0.02'), (0.04, '0.04'), (0.06, '0.06')],
           xname='z')
    zs = [k / 200 for k in range(201)]
    f.polygon([a.q(z, z * quadratic(z)) for z in zs]
              + [a.q(z, z * quintic(z)) for z in reversed(zs)],
              fill=FILLS[3], stroke='none')
    a.curve(lambda z: z * quintic(z), stroke=PURPLE, width=1.6, dash='6 4')
    a.curve(lambda z: z * quadratic(z), stroke=ORANGE, width=1.8,
            dash='6 4')
    a.curve(profile, stroke=BLUE, width=2.2)
    a.dot(1, quadratic(1), fill=ORANGE)
    # a legend in the empty upper left corner
    a.legend([('p(z)', BLUE, None, True),
              ('z q(z)', PURPLE, '6 4', True),
              ('z(9z² − 15z + 8)/40', ORANGE, '6 4', True),
              ('factored error', None, 'band', False)],
             0.03, 0.0669, 0.00588, 0.08)
    f.text((W / 2, H + 30), '(a) 0 ≤ ' + it('z') + ' ≤ 1', size=14,
           italic=False)
    # (b) 1 <= z <= pi/2: the profile less z/20 increases.
    b = Graph(1, PI / 2, 0, 0.18, width=W, height=H, fig=f, at=(W + gap, 0))
    b.axes([(1, '1'), (1.25, '1.25'), (PI / 2, 'π/2')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')],
           xname='z')
    b.curve(lambda z: profile(z) - z / 20, stroke=BLUE, width=2.2)
    b.dot(1, profile(1) - 1 / 20, fill=BLUE)
    b.text(1.33, profile(1.33) - 1.33 / 20 + 0.011, 'p(z) − z/20',
           color=BLUE, size=14, anchor='end')
    f.text((W + gap + W / 2, H + 30), '(b) 1 ≤ ' + it('z') + ' ≤ π/2',
           size=14, italic=False)
    f.save('appendix-h/profile-split', 'The two parts of the proof of the turn '
           'profile bound: on [0, 1] the profile above its Taylor bound '
           'z q(z), which is a cubic plus a factored error; on [1, pi/2] the '
           'profile less z/20, increasing')


def positive_turn():
    A = SQRT3 - 0.5

    def lhs(e):
        return 0.8 * e - A * math.sin(e) + 0.5 * math.sin(e) - \
            0.5 * (1 - math.cos(e))

    def bound(e):
        return e * (9 / 5 - SQRT3 - e / 4)
    g = Graph(0, PI / 12, 0, 0.0055, height=260)
    g.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (PI / 12, 'π/12')],
           [(0, '0'), (0.001, '0.001'), (0.002, '0.002'), (0.003, '0.003'),
            (0.004, '0.004'), (0.005, '0.005')], xname='e')
    g.curve(lambda e: e / 840, stroke=FAINT, width=1.6)
    g.curve(bound, stroke=ORANGE, width=1.8, dash='6 4')
    g.curve(lhs, stroke=BLUE, width=2.2)
    for k in range(101):
        e = PI / 12 * k / 100
        assert lhs(e) >= bound(e) - 1e-15 and bound(e) >= e / 840 - 1e-15
    assert 9 / 5 - 26 / 15 - 11 / 168 == 1 / 840 or \
        abs(9 / 5 - 26 / 15 - 11 / 168 - 1 / 840) < 1e-15
    g.text(0.2, lhs(0.2) + 0.00045, 'A = √3 − ½, v = 0', color=BLUE,
           size=14, anchor='start')
    g.text(0.168, 0.00125, 'e(9/5 − √3 − e/4)', color=ORANGE, size=14)
    g.text(0.236, 0.236 / 840 + 0.0002, 'e/840', color=FAINT, size=14)
    g.f.save('appendix-h/positive-turn', 'The left side of the bound for a '
             'nonnegative turn in its worst case, above the bound '
             'e(9/5 - sqrt3 - e/4) of the proof and the line e/840')


# ---------------------------------------------------------------------------
# Section H.3: a side source and an axial target.


def side_axial_least(l1, e):
    """The least inward sum, for the signs (+, +), of the source at the top of
    the side label l1 and the targets with the axial label l1 - pi/6 - e;
    and the bound of Proposition H.7."""
    a, uu = side_top(l1)
    l2 = l1 - PI / 6 - e
    v = 0.8 * l2
    # (H.1) is affine in A: decreasing for e > 0, increasing for e < 0
    A = axial_top(v) if e >= 0 else max(0.5, v)
    assert admissible(A, v) and abs(label(A, v) - l2) < 1e-9
    sigma = (0.5 - a - A * math.sin(e) + abs(math.sin(e)) / 2
             + (0.5 - v) * math.cos(e))
    return sigma, 2 / 15 * remainder(a, uu) + abs(e) / 840


def side_axial():
    lo, hi = -0.4, 0.25
    g = Graph(lo, hi, 0, 0.09, height=280)
    g.axes([(-0.4, '−0.4'), (-0.2, '−0.2'), (0, '0'), (0.2, '0.2')],
           [(0, '0'), (0.02, '0.02'), (0.04, '0.04'), (0.06, '0.06'),
            (0.08, '0.08')], xname='e', yname=sb('σ', '2'))
    f = g.f
    f.line(g.q(0, 0), g.q(0, 0.09), stroke=FAINT, width=1, dash='3 3')
    sources = [(PI / 6, BLUE), (0.6, ORANGE), (0.75, GREEN)]
    for l1, color in sources:
        a, uu = side_top(l1)
        assert admissible(a, uu) and abs(label(a, uu) - l1) < 1e-9
        e0, e1 = max(lo, l1 - 5 * PI / 12), l1 - PI / 6
        for k in range(401):
            e = e0 + (e1 - e0) * k / 400
            s, b = side_axial_least(l1, e)
            assert s >= b - 1e-12
        # at e = 0 the bound is attained: sigma_2 = 2 r / 15, by (H.3)
        s, b = side_axial_least(l1, 0.0)
        assert abs(s - b) < 1e-12
        g.curve(lambda e: side_axial_least(l1, e)[1], e0, e1, stroke=color,
                width=1.4, dash='5 4')
        g.curve(lambda e: side_axial_least(l1, e)[0], e0, e1, stroke=color,
                width=2.2)
        g.dot(0, b, r=3.6, fill=color)
    g.legend([('side state, ' + it('ℓ') + ' = π/6', BLUE, None, False),
              (it('ℓ') + ' = 0.6', ORANGE, None, False),
              (it('ℓ') + ' = 0.75', GREEN, None, False),
              ('bound 2' + it('r') + '/15 + |' + it('e') + '|/840', INK,
               '5 4', False)],
             0.022, 0.083, 0.0075, 0.045)
    g.f.save('appendix-h/side-axial', 'The least inward sum with signs (+, +) '
             'of three side sources and an axial target, as a function of the '
             'turn, above the bound of Proposition H.7, which it attains at '
             'turn 0')


# ---------------------------------------------------------------------------
# Section H.4: the side target.


def target_arc():
    A, v = 1.0, 0.5
    l2 = label(A, v)
    x = PI / 8
    psi = PI / 3 + x - l2
    n = u(-psi)
    tv = (-n[1], n[0])
    H = (A + 0.5) * math.cos(psi) + (0.5 - v) * math.sin(psi)
    corners = square_corners((A, v))
    assert abs(max(q[0] * n[0] + q[1] * n[1] for q in corners) - H) < 1e-12
    pt = u(l2 - 0.5)
    proj = math.cos(PI / 3 + x - 0.5)
    assert abs(pt[0] * n[0] + pt[1] * n[1] - proj) < 1e-12 and proj > 0
    f = Figure(-1.2, 1.75, -1.42, 1.2, 170)
    f.circle((0, 0), 1, stroke=FAINT, dash='4 4')
    f.square((A, v), fill=FILLS[2], stroke=GREEN)
    f.text((1.3, 0.85), 'T', size=17, color=GREEN)
    f.arc((0, 0), 1, l2 - 0.5, l2 + 0.5, GREEN, width=5)
    f.line((0, 0), u(l2), stroke=GREEN, width=1, dash='3 3')
    f.dot(u(l2), r=4, fill=GREEN)
    f.text(shift(u(l2), (0.05, 0.08)), 'ℓ′', color=GREEN, anchor='start',
           size=15)
    # The direction u(-psi), the support line of T and the line through the
    # point u(l2 - 1/2) perpendicular to it.
    f.line((0, 0), shift((0, 0), n, 1.42), width=1.6, arrow=True)
    f.text(shift((0, 0), n, 1.55), 'u(−ψ)', size=14)
    for dist, style, color in ((H, None, INK), (proj, '5 4', ORANGE)):
        base = shift((0, 0), n, dist)
        f.line(shift(base, tv, -0.55), shift(base, tv, 1.35),
               stroke=color, width=1.4, dash=style)
    f.dot(shift((0, 0), n, H), r=3)
    f.dot(shift((0, 0), n, proj), r=3, fill=ORANGE)
    f.line(pt, shift((0, 0), n, proj), stroke=ORANGE, width=1, dash='2 3')
    f.dot(pt, r=4.5, fill=ORANGE)
    f.text((0.83, -0.08), 'u(ℓ′ − ½)', color=ORANGE, size=14,
           anchor='end')
    # the distance H(x) of the support line from o, beside the arrow
    off = -0.2
    p0, p1 = shift((0, 0), tv, off), shift(shift((0, 0), n, H), tv, off)
    f.line(p0, p1, width=1)
    for p in (p0, p1):
        f.line(shift(p, tv, -0.04), shift(p, tv, 0.04), width=1)
    f.text(shift(shift((0, 0), n, H / 2), tv, off - 0.12), 'H(x)', size=14)
    f.dot((0, 0))
    f.text((-0.06, 0.06), 'o', anchor='end')
    f.save('appendix-h/target-arc', 'The side target in its own chart: its '
           'marker arc, the point u(ell prime - 1/2) on it, and the support '
           'line of T in the direction minus psi, beyond the projection of '
           'that point')


def quarter(d):
    y = 5 * PI / 12 - d
    return 1.5 * math.cos(y) - d * (0.8 * math.cos(y) + 1.2 * math.sin(y))


def quarter_profile():
    lo, hi = -1 / 6, PI / 12
    g = Graph(lo, hi, 0.3, 0.4, height=240)
    g.axes([(lo, '−1/6'), (0, '0'), (0.1, '0.1'), (hi, 'π/12')],
           [(0.3, '0.3'), (1 / 3, '1/3'), (0.4, '0.4')], xname='D')
    g.hline(1 / 3, stroke=FAINT, width=1.4, dash='5 4')
    g.curve(quarter, stroke=BLUE, width=2.2)
    g.dot(lo, quarter(lo), fill=BLUE)
    g.dot(hi, quarter(hi), fill=BLUE)
    g.text(0.02, quarter(0.02) + 0.007, 'P(D)', color=BLUE)
    for k in range(101):
        assert quarter(lo + (hi - lo) * k / 100) > 1 / 3
    # the bounds of the proof of Lemma H.10
    eps = PI / 12 - 1 / 6
    assert 7 / 6 * 0.5 - 6 / 5 * 0.8 < 0 and PI / 12 < 1 / 3
    assert (3.14 - 2) / 12 >= 0.095 - 1e-15 and (22 / 7 - 2) / 12 < 0.1
    assert math.sin(eps) >= eps - eps ** 3 / 6 and 0.095 - 0.1 ** 3 / 6 > 0.094
    assert math.cos(eps) >= 1 - eps ** 2 / 2 and 1 - 0.1 ** 2 / 2 >= 0.995
    assert 49 / 30 * 0.094 > 0.153 and 0.153 + 0.995 / 5 > 1 / 3
    assert abs(quarter(lo) - 49 / 30 * math.sin(eps) - math.cos(eps) / 5) \
        < 1e-12
    assert 1 / 30 + SQRT3 / 20 < 1 / 8 and 3 / 4 - 22 / 7 / 8 > 1 / 3
    g.f.save('appendix-h/quarter-profile', 'The concave quarter profile P above the '
             'line at one third')


def side_target():
    targets = [((1.0, 0.5), 'side state (1, ½)', BLUE),
               ((A0, U0), 'transition state ' + it(sbn('(a', '0', ', ', 13)
                                                    + sbn('u', '0', ')', 13)),
                ORANGE),
               ((RD, RD), 'diagonal corner ' + it(sbn('(r', 'd', ', ', 13)
                                                  + sbn('r', 'd', ')', 13)),
                GREEN),
               ((tie_a(PI / 4), PI / 5), 'tie state (' + it('α') + '(π/4), '
                'π/5)', PURPLE)]
    g = Graph(0, PI / 4, 0, 0.5, height=280)
    g.axes([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6'),
            (PI / 4, 'π/4')],
           [(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '0.3'), (0.4, '0.4'),
            (0.5, '0.5')], xname='ℓ')
    # the lower bounds of f at the two ends, from Lemmas H.9 and H.11
    b0, b1 = 0.5 - 2 * PI / 15, PI / 15 - 1 / 6
    g.points([(0, b0), (0.07, b0)], stroke=INK, width=1.4, dash='4 3')
    g.points([(PI / 4 - 0.07, b1), (PI / 4, b1)], stroke=INK, width=1.4,
             dash='4 3')
    g.text(0.006, b0 - 0.024, '½ − 2π/15', size=13, italic=False,
           anchor='start')
    g.text(PI / 4 - 0.006, b1 + 0.022, 'π/15 − 1/6', size=13, italic=False,
           anchor='end')
    rows = []
    for (A, v), name, color in targets:
        assert admissible(A, v)
        l2 = side(A, v)
        assert abs(label(A, v) - l2) < 1e-9

        def fx(x, A=A, v=v, l2=l2):
            psi = PI / 3 + x - l2
            return (-0.5 - 2 * PI / 15 + 0.8 * x
                    + (A + 0.5) * math.cos(psi) + (0.5 - v) * math.sin(psi))
        for j in range(101):
            assert fx(PI / 4 * j / 100) > 0
        assert fx(0) > b0 and fx(PI / 4) > b1
        g.curve(fx, stroke=color, width=2)
        g.dot(0, fx(0), fill=color)
        g.dot(PI / 4, fx(PI / 4), fill=color)
        rows.append((name, color, None, False))
    g.legend(rows, 0.11, 0.212, 0.036, 0.06)
    # the bounds of the proof of Lemma H.9 at the left end
    assert 7 / 9 + 8 * 3.14 / 135 > 5 / 6 and 22 / 21 - 9 / 25 < 0.7
    assert 1 - 0.7 ** 2 / 2 > 3 / 4 and tie_a(PI / 6) > 5 / 6
    assert (30 * 3.14 + 17) / 135 > 4 / 5 and abs(
        tie_a(2 / 3) - (30 * PI + 17) / 135) < 1e-12
    assert SQRT3 / 2 > 0.865 and 1.3 * 0.865 - 0.1 > 1
    assert 8 / 21 < 0.381 and 1 - 0.381 ** 2 / 2 > 0.927
    assert 1.2 * 0.927 - 0.275 * 0.381 > 1
    g.f.save('appendix-h/side-target', 'The concave lower bound f of the inward sum '
             'with a side target, as a function of the source label, for four '
             'side targets, above the bounds of its end values')


# ---------------------------------------------------------------------------
# Section H.5: opposite signs, a nonpositive turn.


def negative_least(z, l1, A):
    """sigma_2 - 2 r(a, u)/15 for a side source of label l1 and an axial
    target (A, v), signs (+, -), turn -z (Lemma H.13 (2))."""
    v = 0.8 * (PI / 6 - z - l1)
    return -0.8 * z + (A + 0.5) * math.sin(z) - (v + 0.5) * (1 - math.cos(z))


def negative_turn():
    hi = 1 / 6
    zmax = PI / 6 - S0          # the largest turn: source label s0, v = 0

    def least(z):
        """The least of sigma_2 - 2 r(a, u)/15 at the turn -z, divided by z:
        it is increasing in A and decreasing in v, so it is least at A = 1/2
        and at the source label s0 (the transition state)."""
        if z == 0:
            return 0.2
        return negative_least(z, S0, 0.5) / z

    def poly(z):
        return 1 / 5 - 3 * z / 5 - z ** 2 / 6
    for k in range(1, 201):
        z = zmax * k / 200
        # brute force over the source labels and the targets of the turn
        for j in range(21):
            l1 = S0 + (PI / 6 - z - S0) * j / 20
            v = 0.8 * (PI / 6 - z - l1)
            for A in (max(0.5, v), axial_top(v)):
                assert admissible(A, v) and abs(label(A, v) - axial(v)) < 1e-9
                assert negative_least(z, l1, A) >= least(z) * z - 1e-15
        assert least(z) >= poly(z) >= 1 / 12
    assert zmax < hi
    assert 3 / 5 * hi + hi ** 2 / 6 <= 1 / 10 + 1 / 216 < 1 / 5 - 1 / 12
    assert PI / 6 - 9 / 25 < 1 / 6 and PI / 5 + 0.5 < 6 / 5
    g = Graph(0, hi, 0.06, 0.21, height=240)
    g.axes([(0, '0'), (0.05, '0.05'), (0.1, '0.1'), (hi, '1/6')],
           [(1 / 12, '1/12'), (0.1, '0.1'), (0.15, '0.15'), (0.2, '0.2')],
           xname='z')
    g.hline(1 / 12, stroke=FAINT, width=1.4, dash='5 4')
    g.curve(poly, stroke=ORANGE, width=1.8, dash='6 4')
    g.curve(least, 0, zmax, stroke=BLUE, width=2.2)
    g.dot(zmax, least(zmax), fill=BLUE)
    g.legend([('least value, divided by ' + it('z'), BLUE, None, False),
              ('1/5 − 3' + it('z') + '/5 − ' + it('z') + '²/6', ORANGE,
               '6 4', False),
              ('1/12', FAINT, '5 4', False)], 0.006, 0.124, 0.0125, 0.012)
    g.f.save('appendix-h/negative-turn', 'For a side source and an axial target '
             'with opposite signs and the turn minus z: the least value of the '
             'sum less 2r/15, divided by z, above the bound of the proof and '
             'above 1/12')


# ---------------------------------------------------------------------------
# Section H.6: the label regions and their boundary.


def admissible_polygon(steps=200):
    t0 = math.asin(0.5 / math.sqrt(13 / 4))       # the point (sqrt3 - 1/2, 0)
    t1 = PI / 4                                     # the diagonal corner
    R = math.sqrt(13 / 4)
    arc = [(-0.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
            -0.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
           for k in range(steps + 1)]
    return [(0.5, 0.0)] + arc + [(0.5, 0.5)]


def label_regions():
    adm = admissible_polygon()
    k = 2 * PI + 7
    axial_region = clip(clip(adm, 9, 11, k), 0, 1, PI / 5)
    side_region = clip(clip(adm, -9, -11, -k), -9, 4, -(7 - PI))
    cap_region = clip(clip(adm, 0, -1, -PI / 5), 9, -4, 7 - PI)
    return adm, axial_region, side_region, cap_region


def label_boundary():
    adm, axial_region, side_region, cap_region = label_regions()
    f = Figure(0.4, 1.36, -0.08, 0.86, 560)
    f.polygon(axial_region, fill=FILLS[0], stroke='none')
    f.polygon(side_region, fill=FILLS[1], stroke='none')
    f.polygon(cap_region, fill=GREY, stroke='none')
    f.polygon(adm, stroke=INK, width=1.2)
    # axes
    f.line((0.42, 0), (1.34, 0), width=1, arrow=True)
    f.line((0.45, -0.05), (0.45, 0.84), width=1, arrow=True)
    f.text((1.34, -0.035), 'a', anchor='end')
    f.text((0.435, 0.83), 'u', anchor='end')
    for x in (0.5, 1.0):
        f.line((x, -0.008), (x, 0.008), width=1)
        f.text((x, -0.035), f'{x:g}', size=13, italic=False)
    for y in (0.5,):
        f.line((0.442, y), (0.458, y), width=1)
        f.text((0.435, y), f'{y:g}', size=13, italic=False, anchor='end')
    # the top of the axial region: the circle below the transition state,
    # then the tie line
    top = [(axial_top(w), w) for w in [PI / 5 * j / 200 for j in range(201)]]
    polyline(f, top, stroke=BLUE, width=3.4)
    # the tops of the side labels: the circle from the transition state to
    # the diagonal corner
    stop = [side_top(S0 + (PI / 4 - S0) * j / 300) for j in range(301)]
    polyline(f, stop, stroke=ORANGE, width=3.4)
    # an axial segment of a target, least at its right end
    v = 0.2
    f.line((0.5, v), (axial_top(v) - 0.02, v), stroke=BLUE, width=1.6,
           arrow=True)
    f.dot((axial_top(v), v), r=4.5, fill=BLUE)
    f.text((0.62, v + 0.025), 'axial segment', size=13, italic=False,
           color=BLUE)
    # a side segment of a source, least at its top
    x = 0.45
    tp, st = (tie_a(x), 0.8 * x), side_top(x)
    assert abs(side(*tp) - x) < 1e-12 and abs(side(*st) - x) < 1e-9
    f.line(tp, shift(st, (tp[0] - st[0], tp[1] - st[1]), 0.06),
           stroke=ORANGE, width=1.6, arrow=True)
    f.dot(st, r=4.5, fill=ORANGE)
    f.text(shift(tp, (-0.03, -0.022)), 'source', size=13, italic=False,
           color=ORANGE, anchor='end')
    # a side segment of a target, least at its tie state
    x = 0.65
    tp, st = (tie_a(x), 0.8 * x), side_top(x)
    f.line(st, shift(tp, (st[0] - tp[0], st[1] - tp[1]), 0.08),
           stroke=ORANGE, width=1.6, arrow=True)
    open_dot(f, tp, stroke=ORANGE)
    f.text(shift(tp, (-0.02, 0.0)), 'target', size=13, italic=False,
           color=ORANGE, anchor='end')
    # special states
    for p, s, dx, dy in (((A0, U0), sbn('(a', '0', ', ', 14) +
                          sbn('u', '0', ')', 14), 0.02, -0.03),
                         ((RD, RD), sbn('(r', 'd', ', ', 14) +
                          sbn('r', 'd', ')', 14), 0.02, 0.025),
                         ((1.0, 0.5), '(1, ½)', 0.02, 0.0)):
        f.dot(p, r=3.6)
        f.text(shift(p, (dx, dy)), s, size=14, anchor='start')
    f.text((0.75, 0.12), 'axial', size=15, italic=False, color=BLUE)
    f.text((0.99, 0.62), 'side', size=15, italic=False, color=ORANGE)
    f.text((0.66, 0.72), 'capped', size=13, italic=False, color=FAINT)
    f.text((1.215, 0.12), 'φ = 13/4', size=14, anchor='start')
    f.text((0.9, 0.42), 'tie line', size=13, italic=False, anchor='end')
    f.save('appendix-h/label-boundary', 'The admissible region in the (a, u)-plane '
           'with its axial, side and capped parts, the top of the axial region '
           'and the tops of the side labels, and the ends of label segments '
           'where the inward sum with opposite signs is least')


# ---------------------------------------------------------------------------
# Section H.7: two circles.


def lowered_tangent(w):
    return SQRT3 - 1 - SQRT3 / 6 * w - 5 / 16 * w ** 2


def circle_bound():
    hi = 0.3
    for k in range(301):
        w = hi * k / 300
        assert circle_a(w) - 0.5 <= lowered_tangent(w) + 1e-15
        assert abs(13 / 4 - (w + 0.5) ** 2 - (3 - w - w * w)) < 1e-12
    assert 1.73 * 19 / 20 - 5 / 16 * 9 / 100 > 0 and 13 / 12 > 5 / 8 * 1.733
    W, H, gap = 300, 230, 84
    f = Figure(-58, 2 * W + gap + 24, -44, H + 46, 1, pad=0)
    # (a) the circle below its tangent, and the tangent lowered by 5w^2/16
    a = Graph(0, hi, 0.6, 0.74, width=W, height=H, fig=f)
    a.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '3/10')],
           [(0.6, '0.6'), (0.65, '0.65'), (SQRT3 - 1, '√3 − 1')], xname='w')
    a.curve(lambda w: SQRT3 - 1 - SQRT3 / 6 * w, stroke=FAINT, width=1.6,
            dash='5 4')
    a.curve(lowered_tangent, stroke=ORANGE, width=1.8, dash='6 4')
    a.curve(lambda w: circle_a(w) - 0.5, stroke=BLUE, width=2.2)
    a.legend([(it('γ') + '(' + it('w') + ') − ½', BLUE, None, False),
              ('tangent at 0', FAINT, '5 4', False),
              ('tangent − 5' + it('w') + '²/16', ORANGE, '6 4', False)],
             0.012, 0.645, 0.0125, 0.03)
    f.text((W / 2, H + 30), '(a) the circle and its tangent', size=14,
           italic=False)
    # (b) the gap below the tangent, divided by w^2, against 5/16
    b = Graph(0, hi, 0.31, 0.335, width=W, height=H, fig=f, at=(W + gap, 0))
    b.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '3/10')],
           [(5 / 16, '5/16'), (0.32, '0.32'), (0.33, '0.33')], xname='w')

    def quotient(w):
        if w == 0:
            return 13 * SQRT3 / 72
        return (SQRT3 - 1 - SQRT3 / 6 * w - (circle_a(w) - 0.5)) / w ** 2
    assert abs(quotient(1e-3) - quotient(0)) < 1e-3
    b.hline(5 / 16, stroke=ORANGE, width=1.8, dash='6 4')
    b.curve(quotient, stroke=BLUE, width=2.2)
    b.dot(0, quotient(0), fill=BLUE)
    b.text(0.015, 0.331, '(tangent − ' + it('γ') + '(' + it('w') + ') + ½)/'
           + it('w') + '²', color=BLUE, size=13, italic=False,
           anchor='start')
    f.text((W + gap + W / 2, H + 30), '(b) the gap below the tangent',
           size=14, italic=False)
    f.save('appendix-h/circle-bound', 'The circle phi = 13/4 as a graph over '
           'the second coordinate, below its tangent at 0 lowered by 5w^2/16; '
           'the gap below the tangent divided by w^2 stays above 5/16')


def radial_form(z, v):
    """E(z, v) of Definition H.16."""
    return (4 / 5 * z + 6 / 25 * (z - 5 * v / 4) ** 2
            - (SQRT3 - 1 - SQRT3 / 6 * v - 5 / 16 * v ** 2) * math.sin(z)
            - (v + 0.5) * (1 - math.cos(z)))


def radial_beta(z):
    return 3 / 8 + 5 / 16 * math.sin(z)


def radial_affine(z, v):
    """L(v) = E(z, v) - beta(z) (v - z/2)^2 of Lemma H.18."""
    return radial_form(z, v) - radial_beta(z) * (v - z / 2) ** 2


def end_bound0(z):
    """The lower bound of L(0) in the proof of Lemma H.17."""
    return (z * (9 / 5 - SQRT3 - (1 / 100 + 3 / 32) * z)
            + z ** 3 * ((SQRT3 - 1) * (1 / 6 - z ** 2 / 120) - 5 / 64))


def top_second(z):
    """F''(z) of the proof of Lemma H.17."""
    rho = SQRT3 - 1 - SQRT3 / 6 * 0.3 - 5 / 16 * 0.09
    return (12 / 25 - 3 / 16
            + math.sin(z) * (rho - 5 / 32 + 5 / 16 * (0.3 - z / 2) ** 2)
            - math.cos(z) * (4 / 5 - 5 / 8 * (0.3 - z / 2)))


def radial_ends():
    c = 5 / 8
    rho = SQRT3 - 1 - SQRT3 / 6 * 0.3 - 5 / 16 * 0.09
    for k in range(1, 201):
        z = c * k / 200
        # Lemma H.17 at v = 0: the bound is positive and below L(0).
        assert 0 < end_bound0(z) <= radial_affine(z, 0)
        # Lemma H.17 at v = 3/10: F'' is negative, below the cubic bound.
        cubic = -3 / 10 + 3 / 16 * z + 3 / 10 * z ** 2 + 5 / 32 * z ** 3
        h = 1e-4
        fd = (radial_affine(z + h, 0.3) - 2 * radial_affine(z, 0.3)
              + radial_affine(z - h, 0.3)) / h ** 2
        assert abs(fd - top_second(z)) < 1e-5 and top_second(z) < cubic < 0
        # Lemma H.18: L is affine in v, so E is positive between the heights.
        for j in range(31):
            v = 0.3 * j / 30
            d = ((1 - 10 * v / 3) * radial_affine(z, 0)
                 + 10 * v / 3 * radial_affine(z, 0.3))
            assert abs(radial_affine(z, v) - d) < 1e-12
            assert radial_form(z, v) > 0
    # the decimal bounds of the proof of Lemma H.17
    assert 1800 - 1733 == 67 and 1 / 100 + 3 / 32 < 0.104
    assert 0.067 - c * 0.104 > 0 and 1 / 6 - c ** 2 / 120 > 0.163
    assert 0.73 * 0.163 - 0.079 > 0 and 5 / 64 < 0.079
    assert 19 / 20 * 1.733 - 1 - 9 / 320 < 0.6183 and rho < 0.6183
    assert 0.6183 - 5 / 32 + 5 / 16 * 0.09 < 0.5 and 12 / 25 - 3 / 16 < 0.3
    assert 3 / 16 * c < 0.118 and 3 / 10 * c ** 2 < 0.118
    assert 5 / 32 * c ** 3 < 0.039 and -0.3 + 0.118 + 0.118 + 0.039 < 0
    assert math.sin(c) <= c - c ** 3 / 6 + c ** 5 / 120 < 0.5852
    assert math.cos(c) >= 1 - c ** 2 / 2 + c ** 4 / 24 - c ** 6 / 720 > 0.8109
    assert radial_affine(c, 0.3) > 0.515 - 0.6183 * 0.5852 - 0.8 * 0.1891 \
        - 0.0002 > 0.0016
    W, H, gap = 300, 230, 84
    f = Figure(-58, 2 * W + gap + 24, -44, H + 46, 1, pad=0)
    # (a) At z = 5/8, E is a square plus the affine L, positive at both ends.
    vmax = 0.36
    a = Graph(0, vmax, 0, 0.08, width=W, height=H, fig=f)
    a.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '3/10')],
           [(0, '0'), (0.02, '0.02'), (0.04, '0.04'), (0.06, '0.06'),
            (0.08, '0.08')], xname='v')
    f.line(a.q(0.3, 0), a.q(0.3, 0.08), stroke=FAINT, width=1, dash='4 3')
    a.curve(lambda v: radial_beta(c) * (v - c / 2) ** 2, stroke=ORANGE,
            width=2.2)
    a.curve(lambda v: radial_affine(c, v), 0, 0.3, stroke=GREEN, width=2.2)
    a.curve(lambda v: radial_form(c, v), stroke=BLUE, width=2.2)
    for v in (0, 0.3):
        a.dot(v, radial_affine(c, v), fill=GREEN)
    a.legend([('E(5/8, v)', BLUE, None, True),
              ('β(5/8)(v − 5/16)²', ORANGE, None, True),
              ('L(v)', GREEN, None, True)], 0.15, 0.074, 0.0085, 0.03)
    f.text((W / 2, H + 30), '(a) the radial form at ' + it('z') + ' = 5/8',
           size=14, italic=False)
    # (b) The two heights: L(0) positive, F concave above its chord.
    b = Graph(0, c, 0, 0.02, width=W, height=H, fig=f, at=(W + gap, 0))
    b.axes([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (c, '5/8')],
           [(0, '0'), (0.01, '0.01'), (0.02, '0.02')], xname='z')
    b.points([(0, 0), (c, radial_affine(c, 0.3))], stroke=BLUE, width=1.2,
             dash='5 4')
    b.curve(lambda z: radial_affine(z, 0), stroke=ORANGE, width=2.2)
    b.curve(lambda z: radial_affine(z, 0.3), stroke=BLUE, width=2.2)
    b.dot(c, radial_affine(c, 0.3), fill=BLUE)
    b.text(0.5, radial_affine(0.5, 0) + 0.0016, 'L(0)', color=ORANGE,
           size=14, anchor='end')
    b.text(0.22, radial_affine(0.22, 0.3) + 0.0016, 'F = L(3/10)', color=BLUE,
           size=14, anchor='middle')
    f.text((W + gap + W / 2, H + 30), '(b) the two heights', size=14,
           italic=False)
    f.save('appendix-h/radial-ends', 'The radial form at z = 5/8 as a square plus '
           'an affine function of v that is positive at v = 0 and v = 3/10; '
           'the two heights on [0, 5/8], the one at v = 3/10 concave and '
           'above its chord')


def circular_pair():
    l1, l2 = 0.45, 0.3
    a, uu = side_top(l1)
    v = 0.8 * l2
    A = axial_top(v)
    assert abs(label(a, uu) - l1) < 1e-9 and abs(label(A, v) - l2) < 1e-9
    assert abs(phi(a, uu) - 13 / 4) < 1e-9 and abs(phi(A, v) - 13 / 4) < 1e-9
    cs, ct, ddeg, m1, m2 = canonical_pair(a, uu, A, v, 1, -1)
    z = l1 + l2 - PI / 6
    Jv = J(a, A, v, z)
    S = square_corners(cs)
    T = square_corners(ct, ddeg)
    R = math.sqrt(13) / 2
    assert abs(max(math.hypot(*q) for q in S) - R) < 1e-9
    assert abs(max(math.hypot(*q) for q in T) - R) < 1e-9
    t_hi = max(q[0] for q in T)
    assert abs((t_hi - (a - 0.5)) - Jv) < 1e-9 and Jv > 0
    f = Figure(-1.95, 1.95, -2.45, 1.95, 125)
    f.circle((0, 0), R, stroke=INK, dash='6 4')
    f.circle((0, 0), 1, stroke=FAINT, dash='3 4')
    f.polygon(S, fill=FILLS[0], stroke=BLUE, opacity=0.7)
    f.polygon(T, fill=FILLS[2], stroke=GREEN, opacity=0.6)
    f.polygon(S, stroke=BLUE)
    for q in (max(S, key=lambda q: math.hypot(*q)),
              max(T, key=lambda q: math.hypot(*q))):
        f.dot(q, r=4.2, fill=ORANGE)
    for m, color in ((m1, BLUE), (m2, GREEN)):
        f.line((0, 0), u(m), stroke=color, width=1, dash='3 3')
        f.dot(u(m), r=4, fill=color)
    f.dot((0, 0))
    f.text((-0.07, -0.1), 'o', anchor='end')
    f.text(shift(cs, (0.3, -0.3)), 'S', size=17, color=BLUE)
    f.text(shift(ct, u(math.radians(ddeg) + PI / 2), -0.18), 'T', size=17,
           color=GREEN)
    f.text((-1.45, 1.45), 'radius √13/2', size=13, italic=False,
           anchor='middle')
    y_sh = -2.1
    f.line((-1.3, y_sh), (1.75, y_sh), width=1)
    f.line((-0.95, y_sh + 0.18), (-1.3, y_sh + 0.18), width=1.4, arrow=True)
    f.text((-1.12, y_sh + 0.31), sb('n', '2'), size=14)
    f.line((a - 0.5, y_sh + 0.05), (a + 0.5, y_sh + 0.05), stroke=BLUE,
           width=5)
    f.line((min(q[0] for q in T), y_sh - 0.05), (t_hi, y_sh - 0.05),
           stroke=GREEN, width=5)
    f.line((a - 0.5, y_sh - 0.14), (t_hi, y_sh - 0.14), stroke=ORANGE,
           width=4)
    f.text((a - 0.4, y_sh - 0.28), sbn('σ', '2', f' = {Jv:.3f}', 13),
           size=13, color=ORANGE, anchor='start')
    f.line((a - 0.5, cs[1] - 0.5), (a - 0.5, y_sh + 0.05), stroke=BLUE,
           width=1, dash='3 3')
    xt = max(T, key=lambda q: q[0])
    f.line(xt, (xt[0], y_sh - 0.05), stroke=GREEN, width=1, dash='3 3')
    f.save('appendix-h/circular-pair', 'A canonical pair with opposite signs whose '
           'two states lie on the circle phi = 13/4: both squares have a '
           'corner on the circle of radius root 13 over 2')


# ---------------------------------------------------------------------------
# Section H.8: minima on the boundary.


def turn_margin():
    lo, hi = 0.2, PI / 3
    g = Graph(lo, hi, 0.88, 1.3, height=240)
    g.axes([(lo, '1/5'), (0.4, '0.4'), (0.6, '0.6'), (0.8, '0.8'),
            (hi, 'π/3')],
           [(12 / 13, '12/13'), (1.0, '1'), (1.1, '1.1'), (1.2, '1.2'),
            (1.3, '1.3')], xname='z')
    g.hline(12 / 13, stroke=FAINT, width=1.4, dash='5 4')

    def m(z):
        return 44 / 45 * math.sin(z) + 0.8 * math.cos(z)
    g.curve(m, stroke=BLUE, width=2.2)
    g.dot(lo, m(lo), fill=BLUE)
    g.dot(hi, m(hi), fill=BLUE)
    g.text(0.62, 1.05, '(44/45) sin ' + it('z') + ' + (4/5) cos ' + it('z'),
           color=BLUE, size=14, italic=False, anchor='start')
    # the bounds of the proof of Lemma H.20 at the two ends
    assert math.sin(lo) >= lo - lo ** 3 / 6 > 0.18
    assert math.cos(lo) >= 1 - lo ** 2 / 2 and abs(1 - lo ** 2 / 2 - 0.98) < 1e-12
    assert abs(44 / 45 * 0.18 + 0.8 * 0.98 - 0.96) < 1e-12 and 0.96 > 12 / 13
    assert SQRT3 / 2 > 0.865 and 44 / 45 * 0.865 + 0.4 > 1.2 > 12 / 13
    # Proposition H.28: a target on the tie line needs a turn above 1/5
    assert abs(2.5 * 0.29136 - 0.7284) < 1e-12 and PI / 6 < 0.5239
    assert 2 * S0 - PI / 6 > 0.7284 - 0.5239 > lo
    g.f.save('appendix-h/turn-margin', 'The concave turn margin above the line at '
             '12/13')


def upper_profile():
    turns = [(0.3, '0.3', BLUE), (0.5, '0.5', ORANGE),
             (THD, it(sbn('θ', 'd', '', 13)), GREEN), (0.8, '0.8', PURPLE),
             (1.0, '1', PINK)]
    g = Graph(S0, PI / 4, 0, 0.18, height=280)
    g.axes([(S0, it(sb('s', '0', '', 13))), (0.5, '0.5'), (0.6, '0.6'),
            (0.7, '0.7'), (PI / 4, 'π/4')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')],
           xname='x')
    for z, name, color in turns:
        x0 = max(S0, z - PI / 12)
        xs = [x0 + (PI / 4 - x0) * k / 400 for k in range(401)]
        vals = [upper(z, x) for x in xs]
        assert min(vals) > 0
        # left of x = z + pi/6 - s0 the target is on the tie line, and U
        # decreases as x increases (Lemma H.27)
        xm = z + PI / 6 - S0
        for k in range(1, 401):
            if xs[k] <= min(xm, TD):
                assert vals[k] <= vals[k - 1] + 1e-12
        if z >= THD - 1e-12:
            assert min(vals) >= upper(z, TD) - 1e-9
        g.curve(lambda x: upper(z, x), x0, PI / 4, stroke=color, width=2.2)
        if xm < TD:
            g.dot(xm, upper(z, xm), r=3.6, fill=color)
        g.text(x0, upper(z, x0), it('z') + ' = ' + name, color=color,
               size=13, italic=False, anchor='start', dx=6, dy=-10)
    g.dot(TD, upper(THD, TD), r=3.6, fill=INK)
    assert abs(upper(THD, TD) - junction_g(THD)) < 1e-12
    assert abs(upper(THD, TD) - 0.0046) < 1e-4
    g.f.save('appendix-h/upper-profile', 'The upper profile U(z, x) along five '
             'lines of constant turn, as a function of the source label x, '
             'positive, decreasing while the target lies on the tie line, and '
             'least at the junction for large turns')


def junction_g(y):
    mu = y + PI / 6 - TD
    return (0.5 - RD - (tie_a(mu) - 0.5) * math.sin(y)
            + (0.8 * mu + 0.5) * math.cos(y))


def junction():
    lo, hi = THD, TD + PI / 12
    g = Graph(0.6, 1.06, 0, 0.12, height=240)
    g.axes([(lo, it(sbn('θ', 'd', '', 13))), (0.7, '0.7'), (0.8, '0.8'),
            (0.9, '0.9'), (1.0, '1')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1')], xname='y')
    g.curve(junction_g, lo, hi, stroke=BLUE, width=2.2)
    for k in range(101):
        y = lo + (hi - lo) * k / 100
        assert junction_g(y) > 0
        if k:
            assert junction_g(y) > junction_g(lo + (hi - lo) * (k - 1) / 100)
    g.dot(lo, junction_g(lo), fill=BLUE)
    g.text(0.606, 0.03, sbn('g(θ', 'd', f') ≈ {junction_g(lo):.4f}', 13),
           size=13, color=BLUE, anchor='start')
    g.points([(lo, junction_g(lo) + 0.004), (lo + 0.004, 0.024)],
             stroke=BLUE, width=1)
    g.text(0.93, junction_g(0.93) + 0.012, 'g(y)', color=BLUE, anchor='end')
    g.f.save('appendix-h/junction', 'The diagonal junction g, increasing from a '
             'small positive value at theta_d')


def upper_cases():
    x0, x1 = S0, PI / 4
    k = 700
    f = Figure(x0 - 0.1, x1 + 0.2, -0.09, PI / 4 + 0.05, k)
    # regions
    f.polygon([(x0, 0), (x1, 0), (x1, S0), (x0, S0)], fill=FILLS[2],
              stroke='none')
    f.polygon([(x0, S0), (x1, S0), (x1, PI / 4), (x0, PI / 4)],
              fill=FILLS[0], stroke='none')
    f.polygon([(TD, 0), (x1, 0), (x1, PI / 4), (TD, PI / 4)], fill=FILLS[1],
              stroke=ORANGE, width=1)
    # z <= 0: below the line x + m = pi/6
    f.polygon([(x0, 0), (PI / 6, 0), (x0, PI / 6 - x0)], fill=GREY,
              stroke='none')
    f.polygon([(x0, 0), (x1, 0), (x1, PI / 4), (x0, PI / 4)], stroke=INK,
              width=1.2)
    f.line((x0, S0), (x1, S0), width=1.2)
    # lines of constant turn and the moves along them
    for z in (0.3, 0.6, 0.9):
        c = z + PI / 6
        pa = (max(x0, c - PI / 4), c - max(x0, c - PI / 4))
        pb = (min(x1, c), c - min(x1, c))
        f.line(pa, pb, stroke=FAINT, width=1, dash='4 3')
        start = (c - PI / 4 + 0.02, PI / 4 - 0.02) if c - PI / 4 >= x0 \
            else (x0 + 0.02, c - x0 - 0.02)
        if start[1] > S0 + 0.03:
            end_x = min(TD, c - S0)
            end = (end_x - 0.004, c - end_x + 0.004)
            f.line(start, end, stroke=BLUE, width=1.6, arrow=True)
            f.dot(start, r=3, fill=BLUE)
    f.text((x0 - 0.012, S0), sbn('s', '0', '', 14), size=14, anchor='end')
    f.text((x0 - 0.012, 0), '0', size=13, italic=False, anchor='end')
    f.text((x0 - 0.012, PI / 4), 'π/4', size=13, italic=False, anchor='end')
    f.text((x0, -0.035), sbn('s', '0', '', 14), size=14)
    f.text((x1 + 0.005, -0.035), sbn('t', 'd', ' ≈ π/4', 13), size=13,
           anchor='start')
    f.text(((x0 + x1) / 2, -0.07), 'source label ' + it('x'), size=13,
           italic=False)
    f.text((x0 - 0.085, (S0 + PI / 4) / 2), 'm', size=16)
    f.text((0.52, 0.165), 'both on the circle:', size=13, italic=False,
           color=GREEN)
    f.text((0.52, 0.137), 'Lemma H.22', size=13, italic=False, color=GREEN)
    f.text((0.474, 0.52), 'target on the tie line:', size=13, italic=False,
           color=BLUE)
    f.text((0.474, 0.492), 'Lemma H.27', size=13, italic=False, color=BLUE)
    f.line((x1 + 0.004, 0.45), (x1 + 0.03, 0.45), stroke=ORANGE, width=1)
    for j, s in enumerate(('diagonal sources', '(width 0.0013):',
                           'Lemma H.26, then', 'H.23 or H.25')):
        f.text((x1 + 0.035, 0.45 - 0.026 * j), s, size=13, italic=False,
               color=ORANGE, anchor='start')
    f.line((x1 + 0.004, 0.62), (x1 + 0.03, 0.62), width=1)
    for j, s in enumerate((it('x') + ' = ' + it(sbn('t', 'd', '', 13)) + ':',
                           'Lemma H.25')):
        f.text((x1 + 0.035, 0.62 - 0.026 * j), s, size=13, italic=False,
               anchor='start')
    f.text((0.395, 0.03), it('z') + ' ≤ 0', size=13, italic=False, color=INK,
           anchor='start')
    f.save('appendix-h/upper-cases', 'The plane of the source label x and the '
           'target label m, split into the cases of the positivity of the '
           'upper profile, with lines of constant turn and the moves along '
           'them')


# ---------------------------------------------------------------------------
# Section H.9: two axial labels with opposite signs.


def transition_shift():
    uu, v = 0.15, 0.59                  # the source and target heights
    a = 1.16                            # an axial source with a > a0
    A = axial_top(v) - 0.06             # an axial target below its top
    z = 1.25 * (uu + v) - PI / 6
    vp = v - (U0 - uu)
    Ap = axial_top(vp)
    for (x, y) in ((a, uu), (A, v), (Ap, vp)):
        assert admissible(x, y) and abs(label(x, y) - axial(y)) < 1e-12
    assert z > 0 and uu < U0 and 0 < vp <= v <= PI / 5
    assert abs(S0 + 1.25 * vp - PI / 6 - z) < 1e-12
    diff = J(a, A, v, z) - J(A0, Ap, vp, z)
    assert abs(diff - ((A0 - a) + (Ap - A) * math.sin(z)
                       + (U0 - uu) * math.cos(z))) < 1e-12 and diff >= 0
    assert A0 < a <= circle_a(uu) <= A0 + 0.5 * (U0 - uu)
    assert A <= axial_top(v) <= Ap and J(A0, Ap, vp, z) > 0
    lo, hi, top = 0.56, 1.46, 0.66
    f = Figure(lo, hi, -0.08, top, 560)
    adm, axial_region, side_region, cap_region = label_regions()
    for poly, fill in ((axial_region, FILLS[0]), (side_region, FILLS[1])):
        part = poly
        for (pa, pb, pc) in ((1, 0, hi), (-1, 0, -lo), (0, 1, top)):
            part = clip(part, pa, pb, pc)
        f.polygon(part, fill=fill, stroke='none')
    f.line((lo, 0), (hi, 0), width=1, arrow=True)
    f.text((hi, -0.035), 'a', anchor='end')
    for x in (0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3):
        f.line((x, -0.006), (x, 0.006), width=1)
        f.text((x, -0.035), f'{x:g}', size=13, italic=False)
    # the circle, and the top of the axial region: the circle up to the
    # transition state, then the tie line
    ws = [top * j / 300 for j in range(301)]
    polyline(f, [(circle_a(w), w) for w in ws], stroke=FAINT, width=1.2)
    polyline(f, [(axial_top(w), w) for w in ws if w <= PI / 5],
             stroke=BLUE, width=2.4)
    # the bound a <= a0 + (u0 - w)/2 below the transition state
    f.line((A0, U0), (A0 + 0.5 * U0, 0), stroke=INK, width=1, dash='4 3')
    # the moves: the source up to the transition state, the target down by
    # the same amount and out to the top of the axial region
    f.line((a, uu), shift((A0, U0), (a - A0, uu - U0), 0.06), stroke=INK,
           width=1.5, arrow=True)
    f.line((A, v), shift((Ap, vp), (A - Ap, v - vp), 0.06), stroke=INK,
           width=1.5, arrow=True)
    f.dot((a, uu), r=4.5, fill=BLUE)
    f.dot((A, v), r=4.5, fill=GREEN)
    open_dot(f, (A0, U0), r=4.5, stroke=BLUE)
    open_dot(f, (Ap, vp), r=4.5, stroke=GREEN)
    f.text((a - 0.016, uu - 0.032), '(a, u)', size=14, anchor='end')
    f.text((A0 + 0.018, U0 + 0.014), sbn('(a', '0', ', ', 14)
           + sbn('u', '0', ')', 14), size=14, anchor='start')
    f.text((A - 0.016, v), '(A, v)', size=14, anchor='end')
    f.text((Ap + 0.018, vp + 0.014), '(χ(v′), v′)', size=14, anchor='start')
    # the two equal shifts, on the right
    xb = 1.36
    for (y0, y1, color, p0, p1) in ((uu, U0, BLUE, (a, uu), (A0, U0)),
                                    (vp, v, GREEN, (Ap, vp), (A, v))):
        for p in (p0, p1):
            f.line(p, (xb, p[1]), stroke=color, width=0.8, dash='2 3')
        f.line((xb, y0), (xb, y1), stroke=color, width=1.2)
        for yy in (y0, y1):
            f.line((xb - 0.008, yy), (xb + 0.008, yy), stroke=color,
                   width=1.2)
        f.text((xb + 0.014, (y0 + y1) / 2), sbn('u', '0', ' − ', 13)
               + it('u'), size=13, color=color, anchor='start')
    f.text((0.85, 0.12), 'axial', size=14, italic=False, color=BLUE)
    f.text((1.08, 0.6), 'side', size=14, italic=False, color=ORANGE)
    f.save('appendix-h/transition-shift', 'Two axial labels with opposite signs '
           'and a source label below s_0: the source moves up to the '
           'transition state and the target moves down by the same amount '
           'u_0 - u and out to the top of the axial region, which keeps the '
           'turn')


def main():
    inward_sectors()
    turn_profile()
    profile_split()
    positive_turn()
    side_axial()
    target_arc()
    quarter_profile()
    side_target()
    negative_turn()
    label_boundary()
    circle_bound()
    radial_ends()
    circular_pair()
    turn_margin()
    upper_profile()
    junction()
    upper_cases()
    transition_shift()


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw the figures of Appendix C (the inward axis) in docs/proof/figures/.

    python3 scripts/figures/fig_appc.py

Every figure is computed from the functions and states of the appendix: the
canonical pairs from the labels and the relative phase, the graphs by sampling
the functions, the control polygons from the Bernstein coefficients, and the
label regions by clipping the admissible region with the lines of the labels.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           sb, clip)

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]

# ---------------------------------------------------------------------------
# The states, labels and boundary functions of Chapter 9 and Appendix B.


def axial(u_):
    return 5 * u_ / 4


def side(a, u_):
    return PI / 6 + (u_ - 0.5) / 3 + 3 * (1 - a) / 4


def label(a, u_):
    return min(axial(u_), side(a, u_), PI / 4)


def phi(a, u_):
    return (a + 0.5) ** 2 + (u_ + 0.5) ** 2


def admissible(a, u_, tol=1e-9):
    return (-tol <= u_ <= a + tol and a >= 0.5 - tol
            and phi(a, u_) <= 13 / 4 + tol)


def circle_a(w):
    """c(w): the circle phi = 13/4 as a graph over the second coordinate."""
    return math.sqrt(13 / 4 - (w + 0.5) ** 2) - 0.5


def tie_line(w):
    return (2 * PI + 7 - 11 * w) / 9


def axial_top(w):
    return min(circle_a(w), tie_line(w))


def tie_a(x):
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
ZD = TD + S0 - PI / 6


def side_top(x):
    """(a+(x), u+(x)): the upper end of the segment of side label x."""
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


def bernstein(coeffs, c):
    """The polynomial with these Bernstein coefficients on [0, c]."""
    n = len(coeffs) - 1

    def p(z):
        t = z / c
        return sum(b * math.comb(n, i) * t ** i * (1 - t) ** (n - i)
                   for i, b in enumerate(coeffs))
    return p


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
    def __init__(self, x0, x1, y0, y1, width=520, height=280, left=58,
                 right=24, top=18, bottom=44):
        self.x0, self.x1, self.y0, self.y1 = x0, x1, y0, y1
        self.kx = width / (x1 - x0)
        self.ky = height / (y1 - y0)
        self.width, self.height = width, height
        self.f = Figure(-left, width + right, -bottom, height + top, 1, pad=0)

    def q(self, x, y):
        return ((x - self.x0) * self.kx, (y - self.y0) * self.ky)

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


# ---------------------------------------------------------------------------
# Figure C.1: the canonical pair on the inward axis in four sectors.


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
    f.text(P(shift(ct, u(math.radians(ddeg) + PI / 2), 0.25)), 'T', size=16,
           color=GREEN)
    # Shadows on the line of n_2.
    s_lo, s_hi = a - 0.5, a + 0.5
    t_lo = min(q[0] for q in T)
    t_hi = max(q[0] for q in T)
    sigma = t_hi - s_lo
    # the closed form (C.1) of the inward sum, for s = +1
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
        f.text(P(((s_lo + t_hi) / 2, y_sh - 0.3)),
               sb('σ', '2') + f' = {sigma:.2f}', size=13, color=ORANGE)
    else:
        f.text(P((s_lo, y_sh - 0.3)), sb('σ', '2') + ' = 0', size=13,
               color=ORANGE)
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
    f.save('appc-inward-sectors', 'The canonical pair on the inward axis in '
           'four sectors, with the shadows of the two squares on the line of '
           'n_2')


# ---------------------------------------------------------------------------
# Section C.2: the turn profiles.


def profile(z):
    return math.sin(z) - 0.8 * z * math.cos(z) - 0.75 * (1 - math.cos(z))


def quintic(z):
    return (9 / 50 - 3 * z / 8 + 7 * z ** 2 / 30 + z ** 3 / 32 - z ** 4 / 30
            - z ** 5 / 960)


Q_COEFFS = [9 / 50, 123 / 2000, 937 / 750000, 462959 / 40000000,
            237199301 / 3750000000, 22578739001 / 300000000000]


def turn_profile():
    g = Graph(0, PI / 2, 0, 0.26)
    g.axes([(0, '0'), (0.5, '0.5'), (1, '1'), (PI / 2, 'π/2')],
           [(0, '0'), (0.1, '0.1'), (0.2, '0.2')], xname='z')
    g.curve(lambda z: z / 50, stroke=FAINT, width=1.6)
    g.curve(lambda z: z / 50 + z * quintic(z), stroke=ORANGE, width=1.6,
            dash='6 4')
    g.curve(profile, stroke=BLUE, width=2.2)
    g.text(1.28, profile(1.28) + 0.018, 'p(z)', color=BLUE, anchor='end')
    g.text(0.78, 0.07, 'z/50 + z q(z)', color=ORANGE, size=14)
    g.text(1.35, 1.35 / 50 - 0.014, 'z/50', color=FAINT, size=14)
    for k in range(0, 158, 2):
        z = k / 100
        assert profile(z) >= z / 50 + z * quintic(z) - 1e-12
    g.f.save('appc-turn-profile', 'The turn profile p, its polynomial lower '
             'bound z/50 + z q(z), and the line z/50')


def profile_bernstein():
    c = 79 / 50
    g = Graph(0, c, 0, 0.2)
    g.axes([(0, '0'), (0.5, '0.5'), (1, '1'), (c, '79/50')],
           [(0, '0'), (0.1, '0.1'), (0.2, '0.2')], xname='z')
    pts = [(c * i / 5, b) for i, b in enumerate(Q_COEFFS)]
    g.points(pts, stroke=ORANGE, width=1.4, dash='5 4')
    for x, y in pts:
        g.dot(x, y, r=3.6, fill=ORANGE)
    p = bernstein(Q_COEFFS, c)
    for k in range(101):
        z = c * k / 100
        assert abs(p(z) - quintic(z)) < 1e-12
    g.curve(quintic, stroke=BLUE, width=2.2)
    g.text(0.2, 0.15, 'q', color=BLUE, size=16)
    g.text(pts[2][0], pts[2][1] + 0.014, sb('b', '2'), color=ORANGE, size=14)
    g.text(pts[3][0] + 0.02, pts[3][1] - 0.012, sb('b', '3'), color=ORANGE,
           size=14, anchor='start')
    g.text(pts[0][0] + 0.04, pts[0][1] + 0.006, sb('b', '0'), color=ORANGE,
           size=14, anchor='start')
    g.text(pts[5][0] - 0.03, pts[5][1] + 0.012, sb('b', '5'), color=ORANGE,
           size=14, anchor='end')
    g.f.save('appc-profile-bernstein', 'The quintic q on the interval from 0 '
             'to 79/50 and its control polygon through the Bernstein '
             'coefficients')


def positive_turn():
    A = math.sqrt(3) - 0.5

    def lhs(e):
        return 0.8 * e - A * math.sin(e) + 0.5 * math.sin(e) - \
            0.5 * (1 - math.cos(e))
    g = Graph(0, PI / 12, 0, 0.0055, height=260)
    g.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (PI / 12, 'π/12')],
           [(0, '0'), (0.001, '0.001'), (0.002, '0.002'), (0.003, '0.003'),
            (0.004, '0.004'), (0.005, '0.005')], xname='e')
    g.curve(lambda e: e / 840, stroke=FAINT, width=1.6)
    g.curve(lhs, stroke=BLUE, width=2.2)
    for k in range(101):
        e = PI / 12 * k / 100
        assert lhs(e) >= e / 840 - 1e-15
    g.text(0.2, lhs(0.2) + 0.00045, 'A = √3 − ½, v = 0', color=BLUE,
           size=14, anchor='start')
    g.text(0.24, 0.24 / 840 + 0.00017, 'e/840', color=FAINT, size=14)
    g.f.save('appc-positive-turn', 'The left side of the bound for a '
             'nonnegative turn in its worst case, against e/840')


# ---------------------------------------------------------------------------
# Section C.4: the side target.


def target_arc():
    A, v = 1.0, 0.5
    l2 = label(A, v)
    x = PI / 8
    psi = PI / 3 + x - l2
    n = u(-psi)
    H = (A + 0.5) * math.cos(psi) + (0.5 - v) * math.sin(psi)
    corners = square_corners((A, v))
    assert abs(max(q[0] * n[0] + q[1] * n[1] for q in corners) - H) < 1e-12
    pt = u(l2 - 0.5)
    proj = math.cos(PI / 3 + x - 0.5)
    assert abs(pt[0] * n[0] + pt[1] * n[1] - proj) < 1e-12
    f = Figure(-1.2, 1.75, -1.35, 1.2, 170)
    f.circle((0, 0), 1, stroke=FAINT, dash='4 4')
    f.square((A, v), fill=FILLS[2], stroke=GREEN)
    f.text((1.3, 0.85), 'T', size=17, color=GREEN)
    w = 801 / 1600
    f.arc((0, 0), 1, l2 - w, l2 + w, GREEN, width=5)
    f.line((0, 0), u(l2), stroke=GREEN, width=1, dash='3 3')
    f.dot(u(l2), r=4, fill=GREEN)
    f.text(shift(u(l2), (0.05, 0.08)), sb('ℓ', '2'), color=GREEN,
           anchor='start', size=14)
    f.dot(pt, r=4.5, fill=ORANGE)
    f.text(shift(pt, (0.06, 0.07)), 'p', color=ORANGE, anchor='start')
    # The direction u(-psi) and the two lines perpendicular to it.
    f.line((0, 0), shift((0, 0), n, 1.15), width=1.6, arrow=True)
    f.text(shift((0, 0), n, 1.27), 'u(−ψ)', size=14)
    tvec = (-n[1], n[0])
    for dist, style, color in ((H, None, INK), (proj, '5 4', ORANGE)):
        base = shift((0, 0), n, dist)
        f.line(shift(base, tvec, -0.55), shift(base, tvec, 1.35),
               stroke=color, width=1.4, dash=style)
    f.dot(shift((0, 0), n, H), r=3)
    f.dot(shift((0, 0), n, proj), r=3, fill=ORANGE)
    f.line(pt, shift((0, 0), n, proj), stroke=ORANGE, width=1, dash='2 3')
    f.text(shift(shift((0, 0), n, H), tvec, -0.5), 'H(x)', size=14,
           anchor='start', dx=6)
    f.dot((0, 0))
    f.text((-0.06, 0.06), 'o', anchor='end')
    f.save('appc-target-arc', 'The side target in its own chart: its marker '
           'arc, the point p in the direction ell_2 minus one half, and the '
           'support line of T in the direction minus psi, beyond the '
           'projection of p')


def quarter(d):
    y = 5 * PI / 12 - d
    return 1.5 * math.cos(y) - d * (0.8 * math.cos(y) + 1.2 * math.sin(y))


def quarter_profile():
    lo, hi = -1 / 6, PI / 12
    g = Graph(lo, hi, 0.3, 0.4, height=240)
    g.axes([(lo, '−1/6'), (0, '0'), (0.1, '0.1'), (hi, 'π/12')],
           [(0.3, '0.3'), (1 / 3, '1/3'), (0.4, '0.4')], xname='d')
    g.hline(1 / 3, stroke=FAINT, width=1.4, dash='5 4')
    g.curve(quarter, stroke=BLUE, width=2.2)
    g.dot(lo, quarter(lo), fill=BLUE)
    g.dot(hi, quarter(hi), fill=BLUE)
    g.text(0.02, quarter(0.02) + 0.007, 'Q(d)', color=BLUE)
    for k in range(101):
        assert quarter(lo + (hi - lo) * k / 100) > 1 / 3
    g.f.save('appc-quarter-profile', 'The concave quarter profile Q above the '
             'line at one third')


def side_target():
    targets = [((1.0, 0.5), 'side state (1, ½)', BLUE),
               ((A0, U0), sb('(a', '0', ', ') + sb('u', '0', ')'), ORANGE),
               ((RD, RD), sb('(r', 'd', ', ') + sb('r', 'd', ')'), GREEN),
               ((tie_a(PI / 4), PI / 5), 'tie state of label π/4', PURPLE)]
    g = Graph(0, PI / 4, 0, 0.5, height=280)
    g.axes([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6'),
            (PI / 4, 'π/4')],
           [(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '0.3'), (0.4, '0.4'),
            (0.5, '0.5')], xname=sb('ℓ', '1'))
    for k, ((A, v), name, color) in enumerate(targets):
        assert admissible(A, v)
        l2 = side(A, v)
        assert abs(label(A, v) - l2) < 1e-9

        def fx(x, A=A, v=v, l2=l2):
            psi = PI / 3 + x - l2
            return (-0.5 - 2 * PI / 15 + 0.8 * x
                    + (A + 0.5) * math.cos(psi) + (0.5 - v) * math.sin(psi))
        for j in range(101):
            assert fx(PI / 4 * j / 100) > 0
        g.curve(fx, stroke=color, width=2)
        g.dot(0, fx(0), fill=color)
        g.dot(PI / 4, fx(PI / 4), fill=color)
        y = 0.19 - 0.04 * k
        g.points([(0.03, y), (0.09, y)], stroke=color, width=2)
        g.text(0.1, y, name, color=color, size=13, anchor='start')
    g.f.save('appc-side-target', 'The concave lower bound f of the inward sum '
             'with a side target, as a function of the source label, for four '
             'side targets')


# ---------------------------------------------------------------------------
# Section C.6: the label regions and their boundary.


def admissible_polygon(steps=200):
    t0 = math.asin(0.5 / math.sqrt(13 / 4))       # the point (sqrt3 - 1/2, 0)
    t1 = PI / 4                                     # the diagonal corner
    R = math.sqrt(13 / 4)
    arc = [(-0.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
            -0.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
           for k in range(steps + 1)]
    return [(0.5, 0.0)] + arc + [(0.5, 0.5)]


def label_boundary():
    adm = admissible_polygon()
    k = 2 * PI + 7
    axial_region = clip(clip(adm, 9, 11, k), 0, 1, PI / 5)
    side_region = clip(clip(adm, -9, -11, -k), -9, 4, -(7 - PI))
    cap_region = clip(clip(adm, 0, -1, -PI / 5), 9, -4, 7 - PI)
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
        f.text((x, -0.035), f'{x:g}', size=12, italic=False)
    for y in (0.5,):
        f.line((0.442, y), (0.458, y), width=1)
        f.text((0.435, y), f'{y:g}', size=12, italic=False, anchor='end')
    # the tie line inside the region
    f.line((A0, U0), ((7 - PI / 5) / 9, PI / 5), stroke=INK, width=1,
           dash='4 3')
    # the axial top: the circle below the transition state, then the tie line
    top = [(axial_top(w), w) for w in [PI / 5 * j / 200 for j in range(201)]]
    polyline(f, top, stroke=BLUE, width=3.4)
    # the side top: the circle from the transition state to the diagonal
    stop = [side_top(S0 + (PI / 4 - S0) * j / 300) for j in range(301)]
    polyline(f, stop, stroke=ORANGE, width=3.4)
    # an axial segment of a target, minimised at its right end
    v = 0.2
    f.line((0.5, v), (axial_top(v) - 0.02, v), stroke=BLUE, width=1.6,
           arrow=True)
    f.dot((axial_top(v), v), r=4.5, fill=BLUE)
    f.text((0.62, v + 0.025), 'axial segment', size=13, italic=False,
           color=BLUE)
    # a side segment of a source, minimised at its top
    x = 0.45
    tp, st = (tie_a(x), 0.8 * x), side_top(x)
    assert abs(side(*tp) - x) < 1e-12 and abs(side(*st) - x) < 1e-9
    f.line(tp, shift(st, (tp[0] - st[0], tp[1] - st[1]), 0.06),
           stroke=ORANGE, width=1.6, arrow=True)
    f.dot(st, r=4.5, fill=ORANGE)
    f.text(shift(tp, (0.03, -0.02)), 'source', size=13, italic=False,
           color=ORANGE, anchor='start')
    # a side segment of a target, minimised at its tie point
    x = 0.65
    tp, st = (tie_a(x), 0.8 * x), side_top(x)
    f.line(st, shift(tp, (st[0] - tp[0], st[1] - tp[1]), 0.08),
           stroke=ORANGE, width=1.6, arrow=True)
    open_dot(f, tp, stroke=ORANGE)
    f.text(shift(tp, (-0.02, 0.0)), 'target', size=13, italic=False,
           color=ORANGE, anchor='end')
    # special states
    for p, s, dx, dy, anchor in (((A0, U0), sb('(a', '0', ', ') +
                                  sb('u', '0', ')'), 0.02, -0.03, 'start'),
                                 ((RD, RD), sb('(r', 'd', ', ') +
                                  sb('r', 'd', ')'), 0.02, 0.025, 'start'),
                                 ((1.0, 0.5), '(1, ½)', 0.02, 0.0, 'start')):
        f.dot(p, r=3.6)
        f.text(shift(p, (dx, dy)), s, size=14, anchor=anchor)
    f.text((0.75, 0.12), 'axial', size=15, italic=False, color=BLUE)
    f.text((0.99, 0.62), 'side', size=15, italic=False, color=ORANGE)
    f.text((0.66, 0.72), 'capped', size=13, italic=False, color=FAINT)
    f.text((1.23, 0.26), 'φ = 13/4', size=14, anchor='start')
    f.text((0.975, 0.375), 'tie line', size=12, italic=False, anchor='end')
    f.save('appc-label-boundary', 'The admissible region in the (a, u)-plane '
           'with its axial, side and capped parts, the axial top and the side '
           'top, and the ends of label segments where the inward sum with '
           'opposite signs is least')


# ---------------------------------------------------------------------------
# Section C.7: two circles.


P_COEFFS = [201 / 2000, 61767947 / 624624000, 160355527 / 1665664000,
            22183121153 / 239855616000, 1341122208527 / 15350759424000,
            44622066127207 / 552627339264000,
            23358801914587 / 322365947904000,
            4410162763554631 / 70736299425792000,
            1523041486356419 / 30315556896768000,
            4524018740302909 / 125753421201408000,
            406318644428659 / 20958903533568000,
            125352005285647 / 418089296461824000]


def radial_poly(z):
    return (201 / 2000 - 201353 / 7098000 * z - 3091 / 21840 * z ** 2
            - 1571239 / 14196000 * z ** 3 - 23103 / 7280000 * z ** 4
            + 977419 / 182520000 * z ** 5 - 13 / 6300 * z ** 6
            - 364297 / 196560000 * z ** 7 + z ** 8 / 90720 + z ** 9 / 8640
            - z ** 11 / 518400)


def radial_bernstein():
    c = 5 / 8
    g = Graph(0, c, 0, 0.11, height=260)
    g.axes([(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (c, '5/8')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1')], xname='z')
    p = bernstein(P_COEFFS, c)
    for k in range(101):
        z = c * k / 100
        assert abs(p(z) - radial_poly(z)) < 1e-12
    pts = [(c * i / 11, b) for i, b in enumerate(P_COEFFS)]
    g.points(pts, stroke=ORANGE, width=1.4, dash='5 4')
    for x, y in pts:
        g.dot(x, y, r=3.2, fill=ORANGE)
    g.curve(radial_poly, stroke=BLUE, width=2.2)
    g.text(0.3, radial_poly(0.3) - 0.012, 'P', color=BLUE, size=16)
    g.text(pts[11][0] - 0.01, pts[11][1] + 0.01, sb('b', '11'),
           color=ORANGE, size=14, anchor='end')
    g.text(pts[0][0] + 0.012, pts[0][1] + 0.006, sb('b', '0'), color=ORANGE,
           size=14, anchor='start')
    g.f.save('appc-radial-bernstein', 'The polynomial P of degree 11 on the '
             'interval from 0 to 5/8 and its control polygon through the '
             'Bernstein coefficients')


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
    f.text((a - 0.4, y_sh - 0.28), sb('σ', '2') + f' = {Jv:.3f}', size=13,
           color=ORANGE, anchor='start')
    f.line((a - 0.5, cs[1] - 0.5), (a - 0.5, y_sh + 0.05), stroke=BLUE,
           width=1, dash='3 3')
    xt = max(T, key=lambda q: q[0])
    f.line(xt, (xt[0], y_sh - 0.05), stroke=GREEN, width=1, dash='3 3')
    f.save('appc-circular-pair', 'A canonical pair with opposite signs whose '
           'two states lie on the circle phi = 13/4: both squares have a '
           'corner on the circle of radius root 13 over 2')


# ---------------------------------------------------------------------------
# Section C.8: minima on the boundary.


def turn_margin():
    lo, hi = 0.19, PI / 3
    g = Graph(lo, hi, 0.88, 1.3, height=240)
    g.axes([(lo, '0.19'), (0.4, '0.4'), (0.6, '0.6'), (0.8, '0.8'),
            (hi, 'π/3')],
           [(12 / 13, '12/13'), (1.0, '1'), (1.1, '1.1'), (1.2, '1.2'),
            (1.3, '1.3')], xname='z')
    g.hline(12 / 13, stroke=FAINT, width=1.4, dash='5 4')

    def m(z):
        return 44 / 45 * math.sin(z) + 0.8 * math.cos(z)
    g.curve(m, stroke=BLUE, width=2.2)
    g.dot(lo, m(lo), fill=BLUE)
    g.dot(hi, m(hi), fill=BLUE)
    g.text(0.62, 1.05, '(44/45) sin z + (4/5) cos z', color=BLUE, size=14,
           anchor='start')
    g.f.save('appc-turn-margin', 'The concave turn margin above the line at '
             '12/13')


def junction_g(y):
    mu = y + PI / 6 - TD
    return (0.5 - RD - (tie_a(mu) - 0.5) * math.sin(y)
            + (0.8 * mu + 0.5) * math.cos(y))


def junction():
    lo, hi = ZD, TD + PI / 12
    g = Graph(0.6, 1.06, 0, 0.12, height=240)
    g.axes([(lo, sb('z', 'd')), (0.7, '0.7'), (0.8, '0.8'), (0.9, '0.9'),
            (1.0, '1')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1')], xname='y')
    g.curve(junction_g, lo, hi, stroke=BLUE, width=2.2)
    for k in range(101):
        y = lo + (hi - lo) * k / 100
        assert junction_g(y) > 0
        if k:
            assert junction_g(y) > junction_g(lo + (hi - lo) * (k - 1) / 100)
    g.dot(lo, junction_g(lo), fill=BLUE)
    g.text(lo + 0.01, junction_g(lo) + 0.012,
           sb('g(z', 'd', f') ≈ {junction_g(lo):.4f}', 13), size=13,
           color=BLUE, anchor='start')
    g.text(0.93, junction_g(0.93) + 0.012, 'g(y)', color=BLUE, anchor='end')
    g.f.save('appc-junction', 'The diagonal junction g, increasing from a '
             'small positive value at z_d')


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
    # z <= 0: below the line x + mu = pi/6
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
    f.text((x0 - 0.012, S0), sb('s', '0'), size=14, anchor='end')
    f.text((x0 - 0.012, 0), '0', size=13, italic=False, anchor='end')
    f.text((x0 - 0.012, PI / 4), 'π/4', size=13, italic=False, anchor='end')
    f.text((x0, -0.035), sb('s', '0'), size=14)
    f.text((x1 + 0.005, -0.035), sb('t', 'd') + ' ≈ π/4', size=13,
           anchor='start')
    f.text(((x0 + x1) / 2, -0.07), 'source label x', size=13, italic=False)
    f.text((x0 - 0.085, (S0 + PI / 4) / 2), 'μ', size=16)
    f.text((0.52, 0.165), 'both on the circle:', size=13, italic=False,
           color=GREEN)
    f.text((0.52, 0.137), 'Lemma C.22', size=13, italic=False, color=GREEN)
    f.text((0.474, 0.52), 'target on the tie line:', size=13, italic=False,
           color=BLUE)
    f.text((0.474, 0.492), 'Lemma C.27', size=13, italic=False, color=BLUE)
    f.line((x1 + 0.004, 0.45), (x1 + 0.03, 0.45), stroke=ORANGE, width=1)
    for j, s in enumerate(('diagonal sources', '(width 0.0013):',
                           'Lemma C.26, then', 'C.23 or C.25')):
        f.text((x1 + 0.035, 0.45 - 0.026 * j), s, size=12, italic=False,
               color=ORANGE, anchor='start')
    f.line((x1 + 0.004, 0.62), (x1 + 0.03, 0.62), width=1)
    for j, s in enumerate(('x = ' + sb('t', 'd', '', 12) + ':', 'Lemma C.25')):
        f.text((x1 + 0.035, 0.62 - 0.026 * j), s, size=12, italic=False,
               anchor='start')
    f.text((0.395, 0.03), 'z ≤ 0', size=12, italic=False, color=INK,
           anchor='start')
    f.save('appc-upper-cases', 'The plane of the source label x and the '
           'target label mu, split into the cases of the positivity of the '
           'upper profile, with lines of constant turn and the moves along '
           'them')


def main():
    inward_sectors()
    turn_profile()
    profile_bernstein()
    positive_turn()
    target_arc()
    quarter_profile()
    side_target()
    label_boundary()
    radial_bernstein()
    circular_pair()
    turn_margin()
    junction()
    upper_cases()


if __name__ == '__main__':
    main()

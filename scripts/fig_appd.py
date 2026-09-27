#!/usr/bin/env python3
"""Draw the figures of Appendix D (the forward axis of the critical gap).

    python3 scripts/fig_appd.py

Every figure is computed from the definitions of the proof: the labels, the
canonical pair, the support function, the boundary curves of the label
regions, and the one-variable profiles with their certified lower bounds.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY, clip, sb,
                           shift, square_corners, u)

PI = math.pi
R2 = 13 / 4
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN = COLORS[:6]


# The labels, the transition state and the boundary of the label regions.

def axial(v):
    return 1.25 * v


def side(A, v):
    return PI / 6 + (v - 0.5) / 3 + 0.75 * (1 - A)


def label(A, v):
    return min(axial(v), side(A, v), PI / 4)


def admissible(A, v):
    return A >= 0.5 and 0 <= v <= A and (A + .5) ** 2 + (v + .5) ** 2 <= R2


M_ = 2 * PI + 17
J_ = math.sqrt(202 * R2 - M_ ** 2)
X0 = (9 * M_ + 11 * J_) / 202
Y0 = (11 * M_ - 9 * J_) / 202
A0, U0 = X0 - .5, Y0 - .5
S0 = 1.25 * U0
RD = math.sqrt(13 / 8) - .5
TD = PI / 6 + 7 / 12 - 5 / 12 * RD
PSI = math.atan(9 / 4)
KAPPA = math.sqrt(3) - 1


def tie(t):
    return (2 * PI + 7) / 9 - 44 / 45 * t


def diag(t):
    return (2 * PI + 7 - 12 * t) / 5


def circ(v):
    return math.sqrt(R2 - (v + .5) ** 2) - .5


def line(v):
    return (2 * PI + 7 - 11 * v) / 9


def circle_state(t):
    """The state of the circle with side label t, and Z, D."""
    N = 97 / 144
    D = PI / 6 + 19 / 24 - t
    Z = math.sqrt(R2 * N - D * D)
    X = (0.75 * D + Z / 3) / N
    Y = (-D / 3 + 0.75 * Z) / N
    return X - .5, Y - .5


def top(t):
    return circle_state(t) if t <= TD else (diag(t), diag(t))


def G(delta, A, v):
    return -(A - .5) * math.sin(delta) + (v + .5) * math.cos(delta)


def sw(l):
    return PSI - PI / 3 + l


def admissible_polygon(steps=160):
    """The admissible region in the (A, v)-plane, a convex polygon."""
    R = math.sqrt(R2)
    t0 = math.asin(.5 / R)
    t1 = PI / 4
    arc = [(-.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
            -.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
           for k in range(steps + 1)]
    return [(.5, 0)] + arc + [(.5, .5)]


def regions():
    """The parts of the admissible region with axial, side, capped label."""
    P = admissible_polygon()
    c = 2 * PI + 7
    ax = clip(clip(P, 9, 11, c), 0, 1, PI / 5)
    sd = clip(clip(P, -9, -11, -c), -9, 4, -(7 - PI))
    cap = clip(clip(P, 0, -1, -PI / 5), 9, -4, 7 - PI)
    return P, ax, sd, cap


def circle_arc(t0, t1, steps=120):
    R = math.sqrt(R2)
    return [(-.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
             -.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
            for k in range(steps + 1)]


# Drawing helpers.

def polyline(f, pts, stroke=INK, width=1.5, dash=None, opacity=1):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-opacity="{opacity}" '
          f'stroke-linejoin="round"{extra}/>')


def seg_in_window(a, b, c, box):
    """The part of the line a x + b y = c inside the box (x0, x1, y0, y1)."""
    x0, x1, y0, y1 = box
    pts = []
    if abs(b) > 1e-12:
        for x in (x0, x1):
            y = (c - a * x) / b
            if y0 - 1e-9 <= y <= y1 + 1e-9:
                pts.append((x, y))
    if abs(a) > 1e-12:
        for y in (y0, y1):
            x = (c - b * y) / a
            if x0 - 1e-9 <= x <= x1 + 1e-9:
                pts.append((x, y))
    pts = sorted(set((round(x, 9), round(y, 9)) for x, y in pts))
    return (pts[0], pts[-1]) if len(pts) >= 2 else None


def av_axes(f, box, ticks_a=(), ticks_v=(), name=('A', 'v')):
    x0, x1, y0, y1 = box
    f.line((x0, 0), (x1, 0), stroke=FAINT, width=1, arrow=True)
    f.line((x0, y0), (x0, y1), stroke=FAINT, width=1, arrow=True)
    f.text((x1, 0.035 * (y1 - y0)), name[0], anchor='end', color=FAINT)
    f.text((x0 + 0.025 * (x1 - x0), y1), name[1], anchor='start', color=FAINT)
    for a in ticks_a:
        f.line((a, -0.008 * (y1 - y0)), (a, 0.008 * (y1 - y0)), stroke=FAINT)
        f.text((a, -0.04 * (y1 - y0)), a if isinstance(a, str) else
               f'{a:g}', size=11, italic=False, color=FAINT)
    for v in ticks_v:
        f.line((x0 - 0.006 * (x1 - x0), v), (x0 + 0.006 * (x1 - x0), v),
               stroke=FAINT)
        f.text((x0 - 0.012 * (x1 - x0), v), f'{v:g}', size=11, italic=False,
               color=FAINT, anchor='end')


class Plot:
    """A graph panel inside a Figure drawn in pixel units."""

    def __init__(self, f, x0, y0, w, h, xr, yr):
        self.f, self.x0, self.y0, self.w, self.h = f, x0, y0, w, h
        self.xr, self.yr = xr, yr

    def q(self, x, y):
        return (self.x0 + (x - self.xr[0]) / (self.xr[1] - self.xr[0]) * self.w,
                self.y0 + (y - self.yr[0]) / (self.yr[1] - self.yr[0]) * self.h)

    def curve(self, fn, a, b, n=300, **kw):
        xs = [a + (b - a) * k / n for k in range(n + 1)]
        polyline(self.f, [self.q(x, fn(x)) for x in xs], **kw)

    def points(self, pts, **kw):
        polyline(self.f, [self.q(x, y) for x, y in pts], **kw)

    def dot(self, x, y, r=3.2, fill=INK):
        self.f.dot(self.q(x, y), r=r, fill=fill)

    def text(self, x, y, s, dx=0, dy=0, **kw):
        self.f.text(self.q(x, y), s, dx=dx, dy=dy, **kw)

    def vline(self, x, stroke=FAINT, dash='4 4', width=1):
        self.f.line(self.q(x, self.yr[0]), self.q(x, self.yr[1]),
                    stroke=stroke, dash=dash, width=width)

    def hline(self, y, stroke=FAINT, dash='4 4', width=1, a=None, b=None):
        a = self.xr[0] if a is None else a
        b = self.xr[1] if b is None else b
        self.f.line(self.q(a, y), self.q(b, y), stroke=stroke, dash=dash,
                    width=width)

    def axes(self, xticks, yticks, xlabel='', ylabel='', zero=True):
        f = self.f
        y0 = max(self.yr[0], 0) if zero else self.yr[0]
        f.line(self.q(self.xr[0], y0), self.q(self.xr[1], y0), width=1,
               arrow=True)
        f.line(self.q(self.xr[0], self.yr[0]), self.q(self.xr[0], self.yr[1]),
               width=1, arrow=True)
        for x, s in xticks:
            f.line(shift(self.q(x, y0), (0, -3)), shift(self.q(x, y0), (0, 3)),
                   width=1)
            f.text(self.q(x, y0), s, size=11, italic=False, dy=13)
        for y, s in yticks:
            f.line(shift(self.q(self.xr[0], y), (-3, 0)),
                   shift(self.q(self.xr[0], y), (3, 0)), width=1)
            f.text(self.q(self.xr[0], y), s, size=11, italic=False,
                   anchor='end', dx=-5)
        if xlabel:
            f.text(self.q(self.xr[1], y0), xlabel, anchor='end', dy=-9)
        if ylabel:
            f.text(self.q(self.xr[0], self.yr[1]), ylabel, anchor='start',
                   dx=7, dy=4)


def taylor_s(n, x):
    return sum((-1) ** k * x ** (2 * k + 1) / math.factorial(2 * k + 1)
               for k in range((n + 1) // 2))


def taylor_c(n, x):
    return sum((-1) ** k * x ** (2 * k) / math.factorial(2 * k)
               for k in range(n // 2 + 1))


def poly(coeffs):
    return lambda x: sum(c * x ** k for k, c in enumerate(coeffs))


def bernstein_values(c, x0, x1):
    n = len(c) - 1
    return [(x0 + (x1 - x0) * i / n, ci) for i, ci in enumerate(c)]


# Figure D.1: the canonical pairs on the forward axis.

def canonical(a, us, A, v, s, t):
    l, L = label(a, us), label(A, v)
    d = PI / 3 + s * l - t * L
    cS = (a, s * us)
    cT = (A * math.cos(d) - t * v * math.sin(d),
          A * math.sin(d) + t * v * math.cos(d))
    return cS, cT, d, s * l, d + t * L


def unit_arc(f, o, t0, t1, steps=90):
    polyline(f, [shift(o, u(t0 + (t1 - t0) * k / steps)) for k in
                 range(steps + 1)], stroke=FAINT, width=1)


def forward_pairs():
    cases = [((1.0, 0.0, 1.0, 0.5, 1, -1), '(1, −1)', ' = 0'),
             ((1.0, 0.5, 1.0, 0.5, -1, 1), '(−1, 1)', ' = 0'),
             ((1.0, 0.5, 1.0, 0.0, -1, -1), '(−1, −1)', ' ≈ 0.18')]
    width = 3.05
    f = Figure(-0.55, 3 * width - 0.6, -1.45, 1.95, 78)
    for k, (st, name, value) in enumerate(cases):
        ox = k * width
        o = (ox, 0.0)
        cS, cT, d, mS, mT = canonical(*st)
        cS, cT = shift(cS, o), shift(cT, o)
        unit_arc(f, o, -1.1, 1.75)
        f.square(cS, 0, fill=FILLS[0], stroke=BLUE, opacity=0.85)
        f.square(cT, math.degrees(d), fill=FILLS[2], stroke=GREEN,
                 opacity=0.85)
        for m, col in ((mS, BLUE), (mT, GREEN)):
            f.line(o, shift(o, u(m), 1.32), stroke=col, width=1.2, dash='5 3')
            f.dot(shift(o, u(m), 1.0), r=3, fill=col)
        f.arc(o, 0.3, mS, mT, INK, width=1.1)
        f.text(shift(o, u((mS + mT) / 2), 0.46), 'π/3', size=12,
               italic=False)
        f.dot(o, r=2.8)
        f.text(shift(o, (-0.06, -0.1)), 'o', size=13, anchor='end')
        f.text(shift(cS, (0.05, -0.2)), 'S', size=16, color=BLUE)
        f.text(shift(cT, (0.0, 0.05)), 'T', size=16, color=GREEN)
        # The forward axis and the two shadows.
        xa = ox + 2.05
        topS = cS[1] + 0.5
        lowS = cS[1] - 0.5
        wT = (abs(math.cos(d)) + abs(math.sin(d))) / 2
        lowT, topT = cT[1] - wT, cT[1] + wT
        f.line((xa, -1.4), (xa, 1.72), width=1.2, arrow=True)
        f.text((xa + 0.08, 1.66), sb('n', '1', size=14), size=14,
               anchor='start')
        f.line((xa - 0.06, lowS), (xa - 0.06, topS), stroke=BLUE, width=5)
        f.line((xa + 0.06, lowT), (xa + 0.06, topT), stroke=GREEN, width=5)
        f.line((cS[0] + 0.5, topS), (xa - 0.06, topS), stroke=BLUE,
               width=0.9, dash='2 3')
        low = min(square_corners(cT, math.degrees(d)), key=lambda q: q[1])
        f.line((low[0], lowT), (xa + 0.06, lowT), stroke=GREEN, width=0.9,
               dash='2 3')
        f.text((ox + 0.9, 1.87), 'signs ' + name, size=14, italic=False)
        f.text((xa - 0.12, -1.3), sb('σ', '1', value, 14), size=14,
               anchor='end')
    f.save('appd-forward-pairs', 'Three canonical pairs in the chart of S '
           'with the forward axis n1 and the shadows of S and T on it: the '
           'contact of an axial state with a side state for the signs 1 and '
           'minus 1, the contact of two side states for the signs minus 1 and '
           '1, and an overlapping pair for the signs minus 1 and minus 1')


# Figure D.2: the admissible region and Cauchy–Schwarz on the disk.

def region_frame(f, width=1.3):
    """The admissible region, filled by the kind of its label."""
    P, ax, sd, cap = regions()
    f.polygon(ax, fill=FILLS[0], stroke='none')
    f.polygon(sd, fill=FILLS[2], stroke='none')
    f.polygon(cap, fill=GREY, stroke='none')
    f.polygon(P, stroke=INK, width=width)


def disk_support():
    box = (0.34, 1.46, -0.13, 1.05)
    f = Figure(box[0], box[1], box[2], box[3], 380)
    av_axes(f, box, ticks_a=(0.5, 1.0), ticks_v=(0.5,))
    R = math.sqrt(R2)
    polyline(f, circle_arc(math.asin(0.37 / R), math.acos(0.84 / R)),
             stroke=INK, width=1, dash='6 4')
    region_frame(f)
    # The tie line inside the region.
    c = 2 * PI + 7
    polyline(f, [(A0, U0), ((c - 11 * PI / 5) / 9, PI / 5)], stroke=INK,
             width=1.2, dash='4 3')
    # Level lines of 3A + 2v and the supporting one, r = 0.
    for level in (3.0, 3.5):
        s = seg_in_window(3, 2, level, box)
        f.line(s[0], s[1], stroke=ORANGE, width=1, dash='3 4')
    s = seg_in_window(3, 2, 4, box)
    f.line(s[0], s[1], stroke=ORANGE, width=2.2)
    f.line((1, .5), shift((1, .5), (3 / math.sqrt(13), 2 / math.sqrt(13)),
                          0.2), width=1.5, arrow=True)
    f.text((1.2, 0.69), '(3, 2)', size=13, italic=False, anchor='start')
    f.text((0.73, 0.99), 'r(A, v) = 0', size=13, italic=False,
           color=ORANGE, anchor='start')
    f.dot((1, .5), r=4)
    f.text((0.98, 0.48), '(1, ½)', size=13, italic=False, anchor='end')
    f.dot((A0, U0), r=3.5)
    f.text((A0 - 0.03, U0 - 0.06), sb('(a', '0', ', ', 13) +
           sb('u', '0', ')', 13), size=13, italic=False, anchor='end')
    f.text((0.72, 0.17), 'axial', size=14, italic=False, color=BLUE)
    f.text((0.86, 0.55), 'side', size=14, italic=False, color=GREEN)
    f.text((0.64, 0.73), 'capped', size=12, italic=False, color=INK,
           anchor='end')
    f.line((0.645, 0.72), (0.7, 0.665), width=0.8)
    f.text((1.27, -0.09), 'φ = 13/4', size=13, italic=False, anchor='start')
    f.save('appd-disk-support', 'The admissible states in the (A, v)-plane '
           'with their axial, side and capped labels, bounded by the circle '
           'phi = 13/4; the line r = 0 supports the disk at the side state '
           '(1, 1/2), and parallel level lines of the same linear form cut '
           'the disk')


# Figure D.3: Bernstein certificates.

def bernstein_panels():
    P = [113 / 168, 673 / 250, -1 / 2, -291 / 500, 1 / 24, 291 / 10000,
         -1 / 720, -97 / 140000]
    U = [109 / 800, 221 / 200, 48 / 25, -1841 / 1200, -377 / 800,
         8321 / 24000, 1373 / 24000, -29921 / 1008000, 0, 3 / 3200]
    fP, fU = poly(P), poly(U)
    Q = lambda z: fP(z) ** 2 - 13 / 4 * fU(z)
    cQ = [13553 / 1411200, 72827 / 7056000, 393747163 / 34398000000,
          2710739309 / 206388000000, 9910498733 / 638512875000,
          153072314621 / 8172964800000, 47296571468413 / 2068781715000000,
          3708166534047959 / 132402029760000000,
          188854262621881 / 5516751240000000,
          6257753867831 / 150456852000000,
          6998517462046433 / 139642765762500000,
          48606823214392757 / 812467000800000000,
          29832818108969789 / 421857865800000000,
          34918908326684453 / 421857865800000000,
          80964059146525129 / 843715731600000000]
    R = poly([-197 / 1500, 19 / 40, -29 / 160, -17 / 320, 269 / 7680,
              17 / 25600, -1 / 720, -17 / 4300800])
    cR = [27834859 / 5225472000, 21646979107 / 329204736000,
          85094698273 / 768144384000, 83663391929 / 597445632000,
          650018406713 / 4182119424000, 224217116981 / 1394039808000,
          1222825127771 / 7589772288000, 8516973787387 / 53128406016000]
    H = poly([26 / 75, -653 / 300, 23 / 45, 349 / 720, -47 / 900,
              -1069 / 21600, -13 / 37800])
    cH = [26 / 75, 3091 / 10800, 11017 / 48600, 523261 / 3110400,
          3882011 / 34992000, 55351163 / 1007769600, 1001149 / 3527193600]
    p5 = poly([17 / 105, 1 / 20, -1 / 4, 7 / 60, 0, -1 / 160])
    c5 = [17 / 105, 3631 / 21000, 12907 / 84000, 502669 / 4200000,
          22711 / 262500, 20033129 / 336000000]
    panels = [(Q, cQ, 0, 1 / 3, 0.11, 'Q, degree 14, Lemma D.2',
               [(0, '0'), (1 / 3, '1/3')], [(0.05, '0.05'), (0.1, '0.1')]),
              (R, cR, 1 / 3, 11 / 7, 0.19, 'R, degree 7, Lemma D.2',
               [(1 / 3, '1/3'), (11 / 7, '11/7')], [(0.1, '0.1')]),
              (H, cH, 0, 1 / 6, 0.38, 'H, degree 6, Lemma D.6',
               [(0, '0'), (1 / 6, '1/6')], [(0.1, '0.1'), (0.3, '0.3')]),
              (p5, c5, 0, 11 / 10, 0.19,
               sb('p', '5', ', degree 5, Lemma D.12', 13),
               [(0, '0'), (11 / 10, '11/10')], [(0.1, '0.1')])]
    W, Hh = 290, 170
    f = Figure(0, 2 * W + 90, 0, 2 * Hh + 110, 1)
    for k, (fn, c, x0, x1, ymax, title, xt, yt) in enumerate(panels):
        px = 55 + (k % 2) * (W + 30)
        py = 40 + (1 - k // 2) * (Hh + 50)
        pl = Plot(f, px, py, W - 30, Hh - 20, (x0, x1), (0, ymax))
        pl.axes(xt, yt)
        pts = bernstein_values(c, x0, x1)
        pl.points(pts, stroke=ORANGE, width=1.2, dash='4 3')
        for x, y in pts:
            pl.dot(x, y, r=2.6, fill=ORANGE)
        pl.curve(fn, x0, x1, stroke=INK, width=1.8)
        f.text((px + (W - 30) / 2, py + Hh + 6), title, size=13,
               italic=False)
    f.save('appd-bernstein', 'The four polynomial certificates of Appendix D '
           'on their intervals, each with its Bernstein control polygon: all '
           'control points are positive, and the graph lies in their convex '
           'hull')


# Figure D.4: the profile of an axial target at a negative turn.

def axial_region_points(n=120):
    pts = []
    for i in range(n + 1):
        for j in range(n + 1):
            A = 0.5 + (math.sqrt(3) - 1) * i / n
            v = 0.63 * j / n
            if admissible(A, v) and abs(label(A, v) - axial(v)) < 1e-12:
                pts.append((A, v))
    # add the corners of the boundary
    for k in range(200):
        v = U0 * k / 199
        pts.append((circ(v), v))
    return pts


def axial_profile():
    pts = axial_region_points()
    Lam = lambda z: 1 + 2 * PI / 15 - 0.8 * z + math.cos(z)
    E = lambda z: min(Lam(z) - (A + .5) * math.cos(z) - (v + .5) *
                      (1 - math.sin(z)) for A, v in pts)
    P = poly([113 / 168, 673 / 250, -1 / 2, -291 / 500, 1 / 24, 291 / 10000,
              -1 / 720, -97 / 140000])
    U = poly([109 / 800, 221 / 200, 48 / 25, -1841 / 1200, -377 / 800,
              8321 / 24000, 1373 / 24000, -29921 / 1008000, 0, 3 / 3200])
    R = poly([-197 / 1500, 19 / 40, -29 / 160, -17 / 320, 269 / 7680,
              17 / 25600, -1 / 720, -17 / 4300800])
    cs = lambda z: Lam(z) - 2.55 * (math.cos(z / 2) - math.sin(z / 2))
    f = Figure(0, 560, 0, 300, 1)
    pl = Plot(f, 60, 45, 470, 225, (0, PI / 2), (0, 0.2))
    pl.axes([(0, '0'), (1 / 3, '1/3'), (1, '1'), (PI / 2, 'π/2')],
            [(0.1, '0.1'), (0.2, '0.2')], xlabel='z')
    pl.vline(1 / 3)
    pl.curve(E, 0, PI / 2, n=160, stroke=BLUE, width=2.2)
    pl.curve(lambda z: P(z) - math.sqrt(R2 * U(z)), 0, 1 / 3, stroke=ORANGE,
             width=1.6)
    pl.curve(cs, 1 / 3, PI / 2, stroke=GREEN, width=1.6)
    pl.curve(R, 1 / 3, PI / 2, stroke=ORANGE, width=1.6, dash='5 3')
    pl.text(0.36, 0.178, 'least value over the axial states', size=12,
            italic=False, color=BLUE, anchor='start')
    pl.text(0.03, 0.05, 'P − √(13U/4)', size=12, italic=False,
            color=ORANGE, anchor='start')
    pl.text(1.36, 0.14, 'R (dashed)', size=12, italic=False, color=ORANGE)
    pl.text(1.08, 0.105, 'Cauchy–Schwarz', size=12, italic=False,
            color=GREEN, anchor='start')
    f.save('appd-axial-profile', 'The left side of Lemma D.2 minimised over '
           'the admissible states with axial label, as a function of z, above '
           'the two certified lower bounds: P minus the root of 13U/4 on '
           '[0, 1/3] and R on [1/3, pi/2], with the Cauchy–Schwarz bound '
           'between them')


# Figure D.5: the tangent at the transition state.

def transition_tangent():
    box = (0.62, 1.24, 0.2, 0.84)
    f = Figure(box[0], box[1], box[2], box[3], 560)
    sd = regions()[2]
    f.polygon(sd, fill=FILLS[2], stroke=GREEN, width=1)
    R = math.sqrt(R2)
    polyline(f, circle_arc(math.asin(0.62 / R), math.acos(1.1 / R)),
             stroke=INK, width=1.3)
    c = 2 * PI + 7
    s = seg_in_window(9, 11, c, box)
    f.line(s[0], s[1], width=1.2, dash='4 3')
    # the tangent at the transition state and the quarter plane
    s = seg_in_window(X0, Y0, X0 * A0 + Y0 * U0, box)
    f.line(s[0], s[1], stroke=ORANGE, width=2)
    f.line((box[0], U0), (box[1], U0), stroke=FAINT, width=1, dash='2 3')
    f.line((A0, box[2]), (A0, box[3]), stroke=FAINT, width=1, dash='2 3')
    f.dot((A0, U0), r=4)
    f.text((A0 + 0.025, U0 - 0.05), sb('(a', '0', ', ', 14) +
           sb('u', '0', ')', 14), size=14, italic=False, anchor='start')
    f.text((0.8, 0.6), 'side labels', size=14, italic=False, color=GREEN)
    f.text((0.66, 0.25), 'tie line', size=12, italic=False, anchor='start')
    f.text((1.03, 0.62), 'tangent', size=13, italic=False, color=ORANGE,
           anchor='start')
    f.text((0.64, U0 + 0.014), sb('v = u', '0', size=12), size=12,
           italic=False, color=FAINT, anchor='start')
    f.text((A0 - 0.008, 0.82), sb('A = a', '0', size=12), size=12,
           italic=False, color=FAINT, anchor='end')
    f.save('appd-transition-tangent', 'The states with side label lie in '
           'the quarter plane v at least u0, A at most a0, and on the inner '
           'side of the tangent of the circle at the transition state')


# Figure D.6: the profile of a side target at a negative turn.

def side_region_points(n=140):
    pts = []
    for i in range(n + 1):
        for j in range(n + 1):
            A = 0.6 + 0.55 * i / n
            v = 0.25 + 0.55 * j / n
            if admissible(A, v) and abs(label(A, v) - side(A, v)) < 1e-12:
                pts.append((A, v))
    for k in range(120):
        t = S0 + (PI / 4 - S0) * k / 119
        pts.append(top(t))
        pts.append((tie(t), 0.8 * t))
    return pts


def side_profile():
    pts = side_region_points()
    E = lambda z, A, v: (math.cos(z) - 2 / 15 - 0.8 * z + (0.6 - math.cos(z)) *
                         (A + .5) + (math.sin(z) - 4 / 15) * (v + .5))
    m = lambda z: min(E(z, A, v) for A, v in pts)
    L0 = lambda z: math.cos(z) - 2 / 15 - 0.8 * z
    cs = lambda z: L0(z) - math.sqrt(R2 * ((0.6 - math.cos(z)) ** 2 +
                                           (math.sin(z) - 4 / 15) ** 2))
    f = Figure(0, 560, 0, 300, 1)
    pl = Plot(f, 60, 45, 470, 225, (0, 1), (0, 0.17))
    pl.axes([(0, '0'), (1 / 6, '1/6'), (math.acos(0.6), 'arccos 3/5'),
             (1, '1')], [(0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')],
            xlabel='z')
    pl.vline(1 / 6)
    pl.vline(math.acos(0.6))
    pl.curve(lambda z: E(z, A0, U0), 0, 1, stroke=GREEN, width=1.6,
             dash='5 3')
    pl.curve(m, 0, 1, n=160, stroke=BLUE, width=2.2)
    pl.curve(cs, 0, 0.19, stroke=ORANGE, width=1.8)
    pl.text(0.3, 0.12, 'least value over the side states', size=12,
            italic=False, color=BLUE, anchor='start')
    pl.text(0.2, 0.045, 'value at the transition state (dashed)', size=12,
            italic=False, color=GREEN, anchor='start')
    pl.f.line(pl.q(0.19, 0.042), pl.q(0.05, 0.0095), stroke=GREEN,
              width=0.8)
    pl.text(0.2, 0.004, 'Cauchy–Schwarz', size=12, italic=False,
            color=ORANGE, anchor='start', dy=-8)
    pl.text(0.083, 0.163, 'step 1', size=11, italic=False, color=FAINT)
    pl.text(0.55, 0.163, 'steps 2 and 3', size=11, italic=False,
            color=FAINT)
    pl.text(0.965, 0.163, '4', size=11, italic=False, color=FAINT)
    f.save('appd-side-profile', 'The expression of Lemma D.6 minimised over '
           'the admissible states with side label, as a function of z, with '
           'its value at the transition state and the Cauchy–Schwarz bound '
           'used for z up to 1/6')


# Figure D.7: the side margin and the lines B(w) = 0.

def M_w(w):
    return 19 / 20 + math.cos(w) - min(math.sin(w), 0) - 1.2 * w


def margin400(w):
    return 400 * (M_w(w) ** 2 - R2 * ((math.sin(w) - 0.9) ** 2 +
                                      (0.4 - math.cos(w)) ** 2))


def side_side():
    f = Figure(0, 470, 0, 360, 1)
    pl = Plot(f, 60, 50, 380, 270, (-PI / 3, PI / 6), (0, 1100))
    pl.axes([(-PI / 3, '−π/3'), (0, '0'), (PI / 6, 'π/6')],
            [(500, '500'), (1000, '1000')], xlabel='w')
    pl.curve(lambda w: w * (468 - 724 * w + 90 * w * w - 40 * w ** 4), 0,
             PI / 6, stroke=ORANGE, width=1.6, dash='5 3')
    pl.curve(lambda w: -w * (212 - 636 * w + 160 * w ** 3), -PI / 3, 0,
             stroke=ORANGE, width=1.6, dash='5 3')
    pl.curve(margin400, -PI / 3, PI / 6, stroke=BLUE, width=2.2)
    pl.dot(0, 0, r=3.5)
    pl.text(0.03, 950, '400 × margin', size=12, italic=False, color=BLUE,
            anchor='start')
    pl.text(0.03, 850, 'polynomial bounds', size=12, italic=False,
            color=ORANGE, anchor='start')
    # Right panel: the disk and the lines B(w) = 0 in the (A, v)-plane,
    # each drawn near its point closest to the disk.
    box = (0.45, 1.72, -0.42, 1.05)
    g = Figure(box[0], box[1], box[2], box[3], 230)
    R = math.sqrt(R2)
    g.polygon(regions()[0], fill=FILLS[2], stroke=INK, width=1)
    polyline(g, circle_arc(math.asin(0.08 / R), math.acos(0.95 / R)),
             stroke=INK, width=1.2, dash='6 4')
    for w, col in ((-0.8, CYAN), (-0.4, PURPLE), (0.0, ORANGE),
                   (0.4, PINK)):
        p, q = math.sin(w) - 0.9, 0.4 - math.cos(w)
        n = math.hypot(p, q)
        foot = (-.5 - p / n * M_w(w) / n, -.5 - q / n * M_w(w) / n)
        along = (q / n, -p / n)
        g.line(shift(foot, along, -0.28), shift(foot, along, 0.28),
               stroke=col, width=2.2 if w == 0 else 1.6)
        lab = shift(shift(foot, (-p / n, -q / n), 0.06), along, 0.1)
        g.text(lab, ('w = ' + f'{w:g}').replace('-', '−'), size=12,
               italic=False, color=col, anchor='start')
    g.dot((1, .5), r=3.5)
    g.text((0.97, 0.47), '(1, ½)', size=12, italic=False, anchor='end')
    g.text((0.52, 0.86), 'φ ≤ 13/4', size=12, italic=False, anchor='start')
    f.add('<g transform="translate(470,0)">')
    for item in g.items:
        f.add(item)
    f.add('</g>')
    f.w = 470 + g.w
    f.h = max(f.h, g.h)
    f.save('appd-side-side', 'Left: 400 times the margin of Lemma D.9 as a '
           'function of the turn w, positive except at w = 0, above its '
           'polynomial lower bounds. Right: the lines B(w) = 0 for several '
           'turns; only the one for w = 0 touches the disk phi at most 13/4, '
           'at the side state (1, 1/2)')


# Figure D.8: the lower bounds of the opposite-sign sector in the turn.

def opposite_profiles():
    base = lambda w: math.sin(w) - 0.8 * w - 0.5 * (1 - math.cos(w))
    aa_neg = lambda z: (1 - 4 * PI / 15 + 0.8 * z - KAPPA * math.sin(z) -
                        0.5 * (1 - math.cos(z)))
    psi = lambda z: (0.5 - PI / 5 + 1.2 * z - KAPPA * math.sin(z) -
                     0.5 * (1 - math.cos(z)))
    f = Figure(0, 600, 0, 320, 1)
    pl = Plot(f, 60, 45, 510, 245, (-PI / 3, PI / 6), (0, 0.24))
    pl.axes([(-PI / 3, '−π/3'), (-0.7, '−7/10'), (-1 / 3, '−1/3'),
             (0, '0'), (PI / 6, 'π/6')], [(0.1, '0.1'), (0.2, '0.2')],
            xlabel='w')
    pl.vline(-0.7)
    pl.vline(-1 / 3)
    pl.curve(lambda w: 1 - 4 * PI / 15 + base(w), 0, PI / 6, stroke=BLUE,
             width=2)
    pl.curve(lambda w: aa_neg(-w), -PI / 3, 0, stroke=BLUE, width=2)
    pl.curve(lambda w: 1 / 170 + base(w), 0, PI / 6, stroke=GREEN,
             width=2)
    pl.curve(lambda w: 1 / 170 - w * (7 / 40 + w / 4), -0.7, 0,
             stroke=GREEN, width=2)
    pl.curve(lambda w: 1 / 170 + w / 60 - w * (1 / 3 + w) / 4, -1 / 3, 0,
             stroke=PINK, width=2, dash='5 3')
    pl.curve(lambda w: psi(-w), -0.7, -1 / 3, stroke=PINK, width=2,
             dash='5 3')
    pl.text(-0.95, 0.2, 'both axial, Lemma D.12', size=12,
            italic=False, color=BLUE, anchor='start')
    pl.text(0.03, 0.058, 'axial, side: D.14', size=12,
            italic=False, color=GREEN, anchor='start')
    pl.text(-1.02, 0.045, 'side, axial: D.15', size=12,
            italic=False, color=PINK, anchor='start')
    f.save('appd-opposite-profiles', 'The lower bounds for the support sum '
           'with opposite signs as functions of the turn w, for two axial '
           'labels and for the two mixed pairs of labels; all are positive')


# Figure D.9: the marker point of Lemma D.17.

def clip_box(poly, box):
    x0, x1, y0, y1 = box
    for a, b, c in ((1, 0, x1), (-1, 0, -x0), (0, 1, y1), (0, -1, -y0)):
        poly = clip(poly, a, b, c)
    return poly


def marker_inset(f, box, frame, cS, cT, d, p, theta):
    """Draw the part of the picture inside box, magnified into frame."""
    x0, x1, y0, y1 = box
    X0f, X1f, Y0f, Y1f = frame
    k = (X1f - X0f) / (x1 - x0)
    m = lambda q: (X0f + (q[0] - x0) * k, Y0f + (q[1] - y0) * k)
    f.polygon([m(q) for q in clip_box(square_corners(cS, 0), box)],
              fill=FILLS[0], stroke='none')
    f.polygon([m(q) for q in clip_box(square_corners(cT, math.degrees(d)),
                                      box)], fill=FILLS[2], stroke='none',
              opacity=0.85)
    topS = cS[1] + 0.5
    f.line(m((x0, topS)), m((x1, topS)), stroke=BLUE, width=1.6)
    corners = square_corners(cT, math.degrees(d))
    for i in range(4):
        seg = clip_box([corners[i], corners[(i + 1) % 4]], box)
        if len(seg) >= 2:
            f.line(m(seg[0]), m(seg[-1]), stroke=GREEN, width=1.6)
    arc = [u(theta - 0.02 + 0.3 * j / 60) for j in range(61)]
    arc = [q for q in arc if x0 <= q[0] <= x1 and y0 <= q[1] <= y1]
    polyline(f, [m(q) for q in arc], stroke=GREEN, width=4)
    f.line(m((x0, p[1])), m((x1, p[1])), stroke=ORANGE, width=1,
           dash='3 3')
    f.dot(m(p), r=4, fill=ORANGE)
    xg = x1 - 0.2 * (x1 - x0)
    f.line(m((xg, p[1])), m((xg, topS)), width=1.4)
    f.text(shift(m((xg, (p[1] + topS) / 2)), (0.04, 0)), 'gap', size=12,
           italic=False, anchor='start')
    f.polygon([(X0f, Y0f), (X1f, Y0f), (X1f, Y1f), (X0f, Y1f)], stroke=INK,
              width=1)


def marker_point():
    a, us = A0, U0
    cS, cT, d, _, mT = canonical(a, us, 1.0, 0.5, -1, -1)
    theta = mT - 0.5
    p = u(theta)
    f = Figure(-0.25, 2.75, -0.95, 1.45, 240)
    f.circle((0, 0), 1.0, stroke=FAINT, width=1)
    f.square(cS, 0, fill=FILLS[0], stroke=BLUE, opacity=0.85)
    f.square(cT, math.degrees(d), fill=FILLS[2], stroke=GREEN, opacity=0.85)
    f.arc((0, 0), 1.0, mT - 801 / 1600, mT + 801 / 1600, GREEN, width=5)
    f.line((0, 0), u(mT), stroke=GREEN, width=1.2, dash='5 3')
    f.line((0, 0), p, stroke=INK, width=1)
    f.arc((0, 0), 0.32, 0, theta, INK, width=1.1)
    f.text(shift((0, 0), u(theta / 2), 0.42), 'θ', size=14)
    f.dot(p, r=4, fill=ORANGE)
    f.text(shift(p, (-0.1, -0.09)), 'u(θ)', size=14, color=ORANGE,
           anchor='end')
    topS = cS[1] + 0.5
    f.text((0.12, 0.62), 'marker arc of T', size=12, italic=False,
           color=GREEN, anchor='end')
    # the magnified neighbourhood of u(theta)
    box = (p[0] - 0.07, p[0] + 0.13, p[1] - 0.06, p[1] + 0.07)
    frame = (1.8, 2.7, 0.35, 0.35 + 0.9 * (box[3] - box[2]) /
             (box[1] - box[0]))
    f.polygon([(box[0], box[2]), (box[1], box[2]), (box[1], box[3]),
               (box[0], box[3])], stroke=INK, width=0.8)
    f.line((box[1], box[3]), (frame[0], frame[3]), stroke=FAINT, width=0.8)
    f.line((box[1], box[2]), (frame[0], frame[2]), stroke=FAINT, width=0.8)
    marker_inset(f, box, frame, cS, cT, d, p, theta)
    f.text((2.25, frame[3] + 0.08), 'magnified', size=12, italic=False,
           color=FAINT)
    k = (frame[1] - frame[0]) / (box[1] - box[0])
    f.text((frame[0] + 0.03, frame[2] + (topS - box[2]) * k + 0.05),
           'top of S at ½ − u', size=12, italic=False, color=BLUE,
           anchor='start')
    f.text((frame[0] + 0.03, frame[2] + (p[1] - box[2]) * k - 0.06),
           'height sin θ', size=12, italic=False, color=ORANGE,
           anchor='start')
    f.dot((0, 0), r=2.8)
    f.text((-0.05, -0.08), 'o', size=13, anchor='end')
    f.text(shift(cS, (0.05, -0.1)), 'S', size=16, color=BLUE)
    f.text(shift(cT, (0.05, 0.15)), 'T', size=16, color=GREEN)
    f.save('appd-marker-point', 'A canonical pair for the signs minus 1 and '
           'minus 1 with a side source of small label: the point u(theta) of '
           'the marker arc of T, half a radian behind its marker, lies in T '
           'and below the top edge of S')


# Figure D.10: segments of constant label and where the support is least.

def segments():
    box = (0.44, 1.3, -0.06, 0.86)
    f = Figure(box[0], box[1], box[2], box[3], 470)
    av_axes(f, box, ticks_a=(0.5, 1.0), ticks_v=(0.5,))
    region_frame(f, width=1.2)
    ell = 0.55
    delta = lambda t: PI / 3 - ell + t
    for k in range(9):
        t = PI / 4 * k / 8
        v = 0.8 * t
        a1 = min(circ(v), line(v))
        f.line((max(0.5, v), v), (a1, v), stroke=BLUE, width=1.3)
        f.dot((a1, v), r=3.4, fill=ORANGE)
    for k in range(8):
        t = S0 + (PI / 4 - S0) * k / 7
        p0, p1 = (tie(t), 0.8 * t), top(t)
        f.line(p0, p1, stroke=GREEN, width=1.3)
        g0, g1 = G(delta(t), *p0), G(delta(t), *p1)
        f.dot(p0 if g0 <= g1 else p1, r=3.4, fill=ORANGE)
    t = sw(ell)
    f.line((tie(t), 0.8 * t), top(t), stroke=ORANGE, width=1.4, dash='4 3')
    c = 2 * PI + 7
    f.line((A0, U0), ((c - 11 * PI / 5) / 9, PI / 5), width=1, dash='4 3')
    f.dot((A0, U0), r=3.5)
    f.text((A0 + 0.015, U0 - 0.02), sb('(a', '0', ', ', 13) +
           sb('u', '0', ')', 13), size=13, italic=False, anchor='start')
    f.dot((RD, RD), r=3.5)
    f.text((RD + 0.015, RD + 0.02), sb('(r', 'd', ', ', 13) +
           sb('r', 'd', ')', 13), size=13, italic=False, anchor='start')
    f.text((0.76, 0.1), 'axial', size=14, italic=False, color=BLUE)
    f.text((0.905, 0.585), 'side', size=14, italic=False, color=GREEN)
    tp = top(t)
    f.text((tp[0] + 0.025, tp[1] + 0.035), 'τ = sw(ℓ)', size=12,
           italic=False, color=ORANGE, anchor='start')
    f.save('appd-segments', 'The admissible states in the (A, v)-plane cut '
           'into segments of constant label: horizontal for axial labels, of '
           'slope 9/4 for side labels. For the source label 0.55 the orange '
           'dots mark the end of each segment where the target support is '
           'least: the circle or tie line for axial labels, the tie line '
           'below the switch and the circle or diagonal above it')


# Figure D.11: the target support along the ends of the side segments.

def circle_profile():
    ell = 0.5
    us = top(ell)[1]
    delta = lambda t: PI / 3 - ell + t
    gtie = lambda t: 0.5 - us + G(delta(t), tie(t), 0.8 * t)
    gtop = lambda t: 0.5 - us + G(delta(t), *top(t))
    gax = 0.5 - us + G(delta(S0), A0, U0)
    f = Figure(0, 560, 0, 300, 1)
    lo, hi = S0, PI / 4
    pl = Plot(f, 60, 45, 470, 225, (lo, hi), (0, 0.1))
    pl.axes([(S0, sb('s', '0', size=11)), (sw(ell), 'sw(ℓ)'),
             (hi, 'π/4')], [(0.05, '0.05'), (0.1, '0.1')], xlabel='τ')
    pl.vline(sw(ell))
    pl.curve(gtie, lo, hi, stroke=PURPLE, width=1.6, dash='5 3')
    pl.curve(gtop, lo, hi, stroke=GREEN, width=1.6, dash='5 3')
    pl.curve(gtie, lo, sw(ell), stroke=PURPLE, width=2.4)
    pl.curve(gtop, sw(ell), hi, stroke=GREEN, width=2.4)
    pl.hline(gax, stroke=ORANGE, dash='2 3', width=1.4, a=lo, b=sw(ell))
    pl.text(0.73, 0.095, 'at the tie state', size=12, italic=False,
            color=PURPLE, anchor='start')
    pl.text(0.68, 0.052, 'at the top', size=12, italic=False,
            color=GREEN, anchor='start')
    pl.text(0.37, gax, 'value at the transition state, (D.4)', size=11,
            italic=False, color=ORANGE, anchor='start', dy=9)
    f.save('appd-circle-profile', 'For the source label 0.5 and the largest '
           'u, one half minus u plus the target support at the two ends of '
           'the side segment of label tau: the least of the two is the tie '
           'end below the switch and the top end above it; both parts are '
           'positive')


def main():
    forward_pairs()
    disk_support()
    bernstein_panels()
    axial_profile()
    transition_tangent()
    side_profile()
    side_side()
    opposite_profiles()
    marker_point()
    segments()
    circle_profile()


if __name__ == '__main__':
    main()

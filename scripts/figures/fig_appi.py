#!/usr/bin/env python3
"""Draw the figures of Appendix I (docs/proof/appendix-i.md), seven squares:
the critical gap, the forward axis, in docs/proof/figures/appendix-i/.

    python3 scripts/figures/fig_appi.py

Every figure is computed from the definitions of the proof: the labels, the
canonical pair, the support function, the boundary curves of the label
regions, and the one-variable profiles with the lower bounds of the proofs.
The numbers that the captions quote are asserted here.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY, SERIF,
                           clip, shift, square_corners, u)
from fig_appa import clip_runs
from fig_front import arrow

PI = math.pi
R2 = 13 / 4
R = math.sqrt(R2)
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN = COLORS[:6]


# Labels. A label is a string in which *x* is set in italics, _c or _{cd} is
# a subscript (in italics if it is a letter, as in r_d) and ^{cd} an upright
# superscript.

def runs(s):
    """The markup s as runs (text, italic, kind), kind '', 'sub' or 'sup'."""
    out, buf, italic, i = [], '', False, 0
    while i < len(s):
        c = s[i]
        if c == '*':
            if buf:
                out.append((buf, italic, ''))
            buf, italic, i = '', not italic, i + 1
        elif c in '_^':
            if buf:
                out.append((buf, italic, ''))
            buf = ''
            if s[i + 1] == '{':
                j = s.index('}', i)
                part, i = s[i + 2:j], j + 1
            else:
                part, i = s[i + 1], i + 2
            if c == '_':
                out.append((part, part.isalpha(), 'sub'))
            else:
                out.append((part, False, 'sup'))
        else:
            buf += c
            i += 1
    if buf:
        out.append((buf, italic, ''))
    return out


def label(f, pos, s, size=13, color=INK, anchor='start', dx=0.0, dy=0.0):
    """Write the label s at the point pos (in the coordinates of f)."""
    x, y = f.p(*pos)
    shifts = {'': 0.0, 'sub': 0.3 * size, 'sup': -0.38 * size}
    off, parts = 0.0, []
    for t, italic, kind in runs(s):
        t = t.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        attrs = ''
        if shifts[kind] != off:
            attrs += f' dy="{shifts[kind] - off:.1f}"'
            off = shifts[kind]
        if kind:
            attrs += f' font-size="{0.68 * size:.1f}"'
        if italic:
            attrs += ' font-style="italic"'
        parts.append(f'<tspan{attrs}>{t}</tspan>')
    f.add(f'<text x="{x + dx:.1f}" y="{y + dy:.1f}" font-size="{size}" '
          f'font-family="{SERIF}" fill="{color}" text-anchor="{anchor}" '
          f'dominant-baseline="middle">{"".join(parts)}</text>')


# The labels, the transition state and the boundary of the label regions,
# in the notation of Appendix G.

def axial(v):
    return 1.25 * v


def side(A, v):
    return PI / 6 + (v - 0.5) / 3 + 0.75 * (1 - A)


def ell(A, v):
    """The label of the state (A, v)."""
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
OMEGA = math.atan(9 / 4)
KAPPA = math.sqrt(3) - 1


def alpha(t):
    """The first coordinate of the tie state of label t."""
    return (2 * PI + 7) / 9 - 44 / 45 * t


def delta(t):
    return (2 * PI + 7 - 12 * t) / 5


def gamma(v):
    """The circle over v."""
    return math.sqrt(R2 - (v + .5) ** 2) - .5


def lam(v):
    """The tie line over v."""
    return (2 * PI + 7 - 11 * v) / 9


def chi(v):
    """The top of the axial region over v."""
    return min(gamma(v), lam(v))


def circle_xyzd(t):
    """X, Y, Z, D of the circle parametrized by the side label t."""
    N = 97 / 144
    D = PI / 6 + 19 / 24 - t
    Z = math.sqrt(R2 * N - D * D)
    return (0.75 * D + Z / 3) / N, (-D / 3 + 0.75 * Z) / N, Z, D


def top(t):
    """The top of the side label t."""
    if t <= TD:
        X, Y, _, _ = circle_xyzd(t)
        return X - .5, Y - .5
    return delta(t), delta(t)


def G(d, A, v):
    """The target support G_d(A, v)."""
    return -(A - .5) * math.sin(d) + (v + .5) * math.cos(d)


def sw(l):
    """The switch label of l."""
    return OMEGA - PI / 3 + l


def admissible_polygon(steps=160):
    """The admissible region in the (A, v)-plane, a convex polygon."""
    t0, t1 = math.asin(.5 / R), PI / 4
    return [(.5, 0)] + circle_arc(t0, t1, steps) + [(.5, .5)]


def regions():
    """The parts of the admissible region with axial, side, capped label."""
    P = admissible_polygon()
    c = 2 * PI + 7
    ax = clip(clip(P, 9, 11, c), 0, 1, PI / 5)
    sd = clip(clip(P, -9, -11, -c), -9, 4, -(7 - PI))
    cap = clip(clip(P, 0, -1, -PI / 5), 9, -4, 7 - PI)
    return P, ax, sd, cap


def circle_arc(t0, t1, steps=120):
    """The arc of the circle phi = 13/4 between the angles t0 and t1."""
    return [(-.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
             -.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
            for k in range(steps + 1)]


def circle_in_box(box, steps=160, t_max=PI / 2):
    """The part of the circle phi = 13/4 inside the box, from the bottom or
    right edge up to the top or left edge, or up to the angle t_max."""
    x0, x1, y0, y1 = box
    ts = [k / 4000 * t_max for k in range(4001)]
    inside = [t for t in ts if x0 <= -.5 + R * math.cos(t) <= x1
              and y0 <= -.5 + R * math.sin(t) <= y1]
    return circle_arc(min(inside), max(inside), steps)


def clip_box(poly, box):
    x0, x1, y0, y1 = box
    for a, b, c in ((1, 0, x1), (-1, 0, -x0), (0, 1, y1), (0, -1, -y0)):
        poly = clip(poly, a, b, c)
    return poly


def side_region_points(n=140):
    """Admissible states with side label, with the ends of their segments."""
    pts = []
    for i in range(n + 1):
        for j in range(n + 1):
            A, v = 0.6 + 0.55 * i / n, 0.25 + 0.55 * j / n
            if admissible(A, v) and abs(ell(A, v) - side(A, v)) < 1e-12:
                pts.append((A, v))
    for k in range(120):
        t = S0 + (PI / 4 - S0) * k / 119
        pts.append(top(t))
        pts.append((alpha(t), 0.8 * t))
    return pts


def axial_region_points(n=120):
    """Admissible states with axial label, with the upper boundary."""
    pts = []
    for i in range(n + 1):
        for j in range(n + 1):
            A, v = 0.5 + KAPPA * i / n, 0.63 * j / n
            if admissible(A, v) and abs(ell(A, v) - axial(v)) < 1e-12:
                pts.append((A, v))
    for k in range(200):
        v = PI / 5 * k / 199
        pts.append((chi(v), v))
    pts.append((A0, U0))
    return pts


# Drawing helpers.

def polyline(f, pts, stroke=INK, width=1.5, dash=None, opacity=1):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-opacity="{opacity}" '
          f'stroke-linejoin="round"{extra}/>')


def ring(f, c, r=6, stroke=ORANGE, width=2):
    x, y = f.p(*c)
    f.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="none" '
          f'stroke="{stroke}" stroke-width="{width}"/>')


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


def av_axes(f, x0, x1, y0, y1, ticks_a=(), ticks_v=(), names=('A', 'v')):
    """Axes of the (A, v)-plane in the box [x0, x1] x [y0, y1], with ticks
    and the names; the A-axis lies at v = 0 if the box contains it."""
    k = 1 / f.s
    ya = 0 if y0 <= 0 <= y1 else y0
    f.line((x0, ya), (x1, ya), stroke=FAINT, width=1, arrow=True)
    f.line((x0, y0), (x0, y1), stroke=FAINT, width=1, arrow=True)
    label(f, (x1, ya), f'*{names[0]}*', size=15, color=FAINT, dx=6)
    label(f, (x0, y1), f'*{names[1]}*', size=15, color=FAINT, anchor='middle',
          dy=-11)
    for a in ticks_a:
        f.line((a, ya - 3 * k), (a, ya + 3 * k), stroke=FAINT, width=1)
        label(f, (a, ya), f'{a:g}', size=12, color=FAINT, anchor='middle',
              dy=13)
    for v in ticks_v:
        f.line((x0 - 3 * k, v), (x0 + 3 * k, v), stroke=FAINT, width=1)
        label(f, (x0, v), f'{v:g}', size=12, color=FAINT, anchor='end', dx=-6)


def side_by_side(panels, gap=0, top=0):
    """One figure made of the figures `panels` placed left to right."""
    f = Figure(0, 1, 0, 1, 1)
    f.items, x = [], 0
    for g, dy in panels:
        f.add(f'<g transform="translate({x:.1f},{top + dy:.1f})">')
        f.items += g.items
        f.add('</g>')
        x += g.w + gap
    f.w = x - gap
    f.h = max(g.h + top + dy for g, dy in panels)
    return f


class Plot:
    """A graph panel inside a Figure drawn in pixel units."""

    def __init__(self, f, x0, y0, w, h, xr, yr):
        self.f, self.x0, self.y0, self.w, self.h = f, x0, y0, w, h
        self.xr, self.yr = xr, yr

    def q(self, x, y):
        return (self.x0 + (x - self.xr[0]) / (self.xr[1] - self.xr[0]) * self.w,
                self.y0 + (y - self.yr[0]) / (self.yr[1] - self.yr[0]) * self.h)

    def curve(self, fn, a, b, n=300, clipped=True, **kw):
        """The graph of fn on [a, b], cut where it leaves the panel."""
        pts = [(a + (b - a) * k / n, fn(a + (b - a) * k / n))
               for k in range(n + 1)]
        for run in clip_runs(pts, self.yr if clipped else None):
            polyline(self.f, [self.q(x, y) for x, y in run], **kw)

    def points(self, pts, **kw):
        polyline(self.f, [self.q(x, y) for x, y in pts], **kw)

    def dot(self, x, y, r=3.2, fill=INK):
        self.f.dot(self.q(x, y), r=r, fill=fill)

    def label(self, x, y, s, **kw):
        label(self.f, self.q(x, y), s, **kw)

    def vline(self, x, stroke=FAINT, dash='4 4', width=1, a=None, b=None):
        a = self.yr[0] if a is None else a
        b = self.yr[1] if b is None else b
        self.f.line(self.q(x, a), self.q(x, b), stroke=stroke, dash=dash,
                    width=width)

    def hline(self, y, stroke=FAINT, dash='4 4', width=1, a=None, b=None):
        a = self.xr[0] if a is None else a
        b = self.xr[1] if b is None else b
        self.f.line(self.q(a, y), self.q(b, y), stroke=stroke, dash=dash,
                    width=width)

    def axes(self, xticks, yticks, xlabel='', ylabel='', at=None, over=14,
             tick_dy=14):
        """Axes with an arrow beyond the last tick on each; the x-axis lies
        at the height `at` (by default 0, or the bottom if 0 is not in the
        panel), and the labels of the axes sit beyond the arrowheads."""
        f = self.f
        if at is None:
            at = 0 if self.yr[0] <= 0 <= self.yr[1] else self.yr[0]
        a, b = self.q(self.xr[0], at), self.q(self.xr[1], at)
        f.line(a, (b[0] + over, b[1]), width=1, arrow=True)
        c, d = self.q(self.xr[0], self.yr[0]), self.q(self.xr[0], self.yr[1])
        f.line(c, (d[0], d[1] + over), width=1, arrow=True)
        for x, s in xticks:
            p = self.q(x, at)
            f.line(shift(p, (0, -3)), shift(p, (0, 3)), width=1)
            label(f, p, s, size=12, anchor='middle', dy=tick_dy)
        for y, s in yticks:
            p = self.q(self.xr[0], y)
            f.line(shift(p, (-3, 0)), shift(p, (3, 0)), width=1)
            label(f, p, s, size=12, anchor='end', dx=-6)
        if xlabel:
            label(f, (b[0] + over, b[1]), xlabel, size=15, dx=5)
        if ylabel:
            label(f, (d[0], d[1] + over), ylabel, size=15, anchor='middle',
                  dy=-12)

    def frame(self, stroke=FAINT, width=1):
        self.f.polygon([self.q(self.xr[0], self.yr[0]),
                        self.q(self.xr[1], self.yr[0]),
                        self.q(self.xr[1], self.yr[1]),
                        self.q(self.xr[0], self.yr[1])], stroke=stroke,
                       width=width)


def root(fn, lo, hi):
    """A zero of fn between lo and hi, where fn changes sign."""
    for _ in range(60):
        mid = (lo + hi) / 2
        if (fn(lo) < 0) == (fn(mid) < 0):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def argmin(fn, lo, hi, n=2000):
    xs = [lo + (hi - lo) * k / n for k in range(n + 1)]
    return min(xs, key=fn)


# The canonical pair on the forward axis.

def canonical(a, us, A, v, s, t):
    """Centre of S, centre of T, turn d, markers of S and T."""
    l, L = ell(a, us), ell(A, v)
    d = PI / 3 + s * l - t * L
    cS = (a, s * us)
    cT = (A * math.cos(d) - t * v * math.sin(d),
          A * math.sin(d) + t * v * math.cos(d))
    return cS, cT, d, s * l, d + t * L


def unit_arc(f, o, t0, t1, steps=90):
    polyline(f, [shift(o, u(t0 + (t1 - t0) * k / steps)) for k in
                 range(steps + 1)], stroke=FAINT, width=1)


def forward_pairs():
    cases = [((1.0, 0.0, 1.0, 0.5, 1, -1), '(1, −1)', 0.0),
             ((1.0, 0.5, 1.0, 0.5, -1, 1), '(−1, 1)', 0.0),
             ((1.0, 0.5, 1.0, 0.0, -1, -1), '(−1, −1)', (math.sqrt(3) - 1) / 4)]
    width = 3.3
    f = Figure(-0.55, 3 * width - 0.4, -1.42, 1.95, 78)
    for k, (st, name, sigma) in enumerate(cases):
        ox = k * width
        o = (ox, 0.0)
        cS, cT, d, mS, mT = canonical(*st)
        cS, cT = shift(cS, o), shift(cT, o)
        assert abs(mT - mS - PI / 3) < 1e-12
        unit_arc(f, o, -1.1, 1.75)
        f.square(cS, 0, fill=FILLS[0], stroke=BLUE, opacity=0.85)
        f.square(cT, math.degrees(d), fill=FILLS[2], stroke=GREEN,
                 opacity=0.85)
        for m, col in ((mS, BLUE), (mT, GREEN)):
            f.line(o, shift(o, u(m), 1.32), stroke=col, width=1.2, dash='5 3')
            f.dot(shift(o, u(m), 1.0), r=3, fill=col)
        f.arc(o, 0.2, mS, mT, INK, width=1.1)
        f.text(shift(o, u((mS + mT) / 2), 0.34), 'π/3', size=12,
               italic=False)
        f.dot(o, r=2.8)
        label(f, shift(o, (-0.07, -0.1)), '*o*', size=14, anchor='end')
        label(f, shift(cS, (-0.22, -0.3)), '*S*', size=16, color=BLUE,
              anchor='middle')
        label(f, shift(cT, (-0.2, 0.28)), '*T*', size=16, color=GREEN,
              anchor='middle')
        # The forward axis, the two shadows and their overlap.
        xa = ox + 2.05
        topS, lowS = cS[1] + 0.5, cS[1] - 0.5
        wT = (abs(math.cos(d)) + abs(math.sin(d))) / 2
        lowT, topT = cT[1] - wT, cT[1] + wT
        assert abs(topS - lowT - sigma) < 1e-12
        f.line((xa, -1.4), (xa, 1.72), width=1.2, arrow=True)
        label(f, (xa + 0.08, 1.66), '*n*_1', size=15)
        f.line((xa - 0.06, lowS), (xa - 0.06, topS), stroke=BLUE, width=5)
        f.line((xa + 0.06, lowT), (xa + 0.06, topT), stroke=GREEN, width=5)
        f.line((cS[0] + 0.5, topS), (xa - 0.06, topS), stroke=BLUE,
               width=0.9, dash='2 3')
        low = min(square_corners(cT, math.degrees(d)), key=lambda q: q[1])
        f.line((low[0], lowT), (xa + 0.06, lowT), stroke=GREEN, width=0.9,
               dash='2 3')
        xs = xa + 0.19
        if sigma > 0:
            f.line((xs, lowT), (xs, topS), stroke=ORANGE, width=2.5)
            for y in (lowT, topS):
                f.line((xs - 0.05, y), (xs + 0.05, y), stroke=ORANGE,
                       width=1.5)
            label(f, (xs + 0.08, (lowT + topS) / 2), '*σ*_1 ≈ 0.18', size=14,
                  color=ORANGE)
        else:
            f.dot((xs, topS), r=3.5, fill=ORANGE)
            label(f, (xs + 0.08, topS), '*σ*_1 = 0', size=14, color=ORANGE)
        f.text((ox + 0.9, 1.87), 'signs ' + name, size=14, italic=False)
    f.save('appendix-i/forward-pairs', 'Three canonical pairs in the chart of '
           'S with the forward axis n1, the shadows of S and T on it and their '
           'overlap sigma1: the contact of an axial state with a side state for '
           'the signs 1 and minus 1, the contact of two side states for the '
           'signs minus 1 and 1, and an overlapping pair for the signs minus 1 '
           'and minus 1')


# Figure: the admissible region and Cauchy–Schwarz on the disk.

def region_frame(f, width=1.3):
    """The admissible region, filled by the kind of its label."""
    P, ax, sd, cap = regions()
    f.polygon(ax, fill=FILLS[0], stroke='none')
    f.polygon(sd, fill=FILLS[2], stroke='none')
    f.polygon(cap, fill=GREY, stroke='none')
    f.polygon(P, stroke=INK, width=width)


def tie_segment(f, width=1.2):
    """The tie line between the transition state and the capped corner."""
    c = 2 * PI + 7
    polyline(f, [(A0, U0), ((c - 11 * PI / 5) / 9, PI / 5)], stroke=INK,
             width=width, dash='4 3')


def disk_support():
    box = (0.34, 1.46, -0.13, 1.05)
    f = Figure(0.25, 1.53, -0.2, 1.1, 380)
    av_axes(f, 0.34, 1.46, -0.13, 1.05, ticks_a=(0.5, 1.0), ticks_v=(0.5,))
    polyline(f, circle_in_box(box), stroke=INK, width=1, dash='6 4')
    region_frame(f)
    tie_segment(f)
    # Level lines of 3A + 2v and the supporting one, r = 0.
    for level in (3.0, 3.5):
        s = seg_in_window(3, 2, level, box)
        f.line(s[0], s[1], stroke=ORANGE, width=1, dash='3 4')
    s = seg_in_window(3, 2, 4, box)
    f.line(s[0], s[1], stroke=ORANGE, width=2.2)
    n = (3 / math.sqrt(13), 2 / math.sqrt(13))
    tip = shift((1, .5), n, 0.2)
    f.line((1, .5), tip, width=1.5, arrow=True)
    label(f, tip, '(3, 2)', size=13, dx=6, dy=-4)
    label(f, (0.79, 0.99), '*r*(*A*, *v*) = 0', size=14, color=ORANGE)
    f.dot((1, .5), r=4)
    label(f, (1.065, 0.465), '(1, ½)', size=13)
    f.dot((A0, U0), r=3.5)
    label(f, (A0 + 0.035, U0 - 0.012), '(*a*_0, *u*_0)', size=13)
    f.text((0.72, 0.17), 'axial', size=14, italic=False, color=BLUE)
    f.text((0.86, 0.6), 'side', size=14, italic=False, color=GREEN)
    f.text((0.64, 0.73), 'capped', size=13, italic=False, color=INK,
           anchor='end')
    f.line((0.645, 0.72), (0.7, 0.665), width=0.8)
    label(f, (1.29, -0.08), '*φ* = 13/4', size=13)
    f.save('appendix-i/disk-support', 'The admissible states in the (A, v)-plane '
           'with their axial, side and capped labels, bounded by the circle '
           'phi = 13/4; the line r = 0 supports the disk at the side state '
           '(1, 1/2), and parallel level lines of the same linear form cut '
           'the disk')


# Figure: the boundary of the side region and the switch.

def switch_panel(l, tau, title, names):
    """The side region, the side segment of label tau and the level lines of
    the target support for the source label l."""
    box = (0.655, 1.17, 0.255, 0.83)
    f = Figure(box[0], box[1], box[2], box[3] + 0.06, 470, pad=14)
    _, ax, sd, cap = regions()
    f.polygon(clip_box(ax, box), fill=FILLS[0], stroke='none')
    f.polygon(clip_box(sd, box), fill=FILLS[2], stroke='none')
    f.polygon(clip_box(cap, box), fill=GREY, stroke='none')
    polyline(f, circle_in_box(box, t_max=PI / 4), width=1.3)
    tie_segment(f, width=1.1)
    f.line((box[0], box[0]), (RD, RD), width=1.1)
    d = PI / 3 - l + tau
    p0, p1 = (alpha(tau), 0.8 * tau), top(tau)
    g0, g1 = G(d, *p0), G(d, *p1)
    # level lines of G_d through the two ends and one step beyond each
    step = g1 - g0
    for k in range(-1, 3):
        level = g0 + k * step
        # -(A - 1/2) sin d + (v + 1/2) cos d = level
        sg = seg_in_window(-math.sin(d), math.cos(d),
                           level - 0.5 * math.sin(d) - 0.5 * math.cos(d), box)
        if sg:
            f.line(sg[0], sg[1], stroke=ORANGE, width=1.1, dash='5 3')
    f.line(p0, p1, width=3)
    f.dot(p0, r=4)
    f.dot(p1, r=4)
    least = p0 if g0 < g1 else p1
    ring(f, least, r=8)
    # the direction in which G_d grows
    base = (1.04, 0.73)
    arrow(f, base, shift(base, (-math.sin(d), math.cos(d)), 0.07),
          color=ORANGE, width=1.6)
    label(f, (base[0] + 0.012, base[1] - 0.022), 'growing *G*_d', size=13,
          color=ORANGE)
    f.dot((A0, U0), r=3.5)
    f.dot((RD, RD), r=3.5)
    if names:
        label(f, (A0 - 0.015, U0 - 0.022), '(*a*_0, *u*_0)', size=13,
              anchor='end')
        label(f, (RD + 0.02, RD + 0.015), '(*r*_d, *r*_d)', size=13)
        label(f, (0.92, 0.36), 'tie line', size=13, anchor='middle')
        label(f, (1.01, 0.58), 'circle', size=13)
        label(f, (p0[0] - 0.018, p0[1] - 0.006), 'tie state', size=13,
              anchor='end')
        label(f, (p1[0] - 0.016, p1[1] + 0.014), 'top', size=13,
              anchor='end')
        label(f, (0.668, 0.282), 'level lines of *G*_d', size=13,
              color=ORANGE)
    label(f, ((box[0] + box[1]) / 2, box[3] + 0.03), title, size=14,
          anchor='middle')
    return f, d, least is p0


def switch_figure():
    tau = 0.7
    # the source labels pi/4 and 2/5: d below and above the switch angle
    left, d1, tie1 = switch_panel(PI / 4, tau, '*ℓ* = π/4: *d* < *ω*', True)
    right, d2, tie2 = switch_panel(0.4, tau, '*ℓ* = 2/5: *d* > *ω*', False)
    assert d1 < OMEGA < d2 and tie1 and not tie2
    assert abs(math.atan2(9, 4) - OMEGA) < 1e-15
    f = side_by_side([(left, 0), (right, 0)], gap=24)
    f.save('appendix-i/switch', 'Two copies of the side region of the '
           '(A, v)-plane between the dashed tie line, the circle and the '
           'diagonal, with the side segment of label 0.7 from its tie state '
           'on the tie line to its top on the circle, and dashed level lines '
           'of the target support; on the left the level lines are less steep '
           'than the segment and the support is least at the tie state, on '
           'the right they are steeper and it is least at the top')


# Figure: at small turns the form is largest at the transition state.

def force(z):
    return math.cos(z), 1 - math.sin(z)


def transition_split(z):
    """P and Q of Lemma I.2, with (11 X0 - 9 Y0) times the force equal to
    P (X0, Y0) + Q (9, 11)."""
    p, q = force(z)
    return 11 * p - 9 * q, X0 * q - Y0 * p


def transition_force():
    D = 11 * X0 - 9 * Y0
    for k in range(101):
        z = PI / 6 * k / 100
        P, Q = transition_split(z)
        p, q = force(z)
        assert abs(P * X0 + Q * 9 - D * p) < 1e-12
        assert abs(P * Y0 + Q * 11 - D * q) < 1e-12
        assert P > 11 * 5 / 6 - 9 > 0 and Q >= X0 / 2 - Y0 > 0
    assert X0 > 8 / 5 and Y0 < 4 / 5 and D > 0
    assert abs(Y0 / X0 - 0.49) < 0.005
    f = Figure(0, 370, 0, 340, 1)
    # Left: the plane of forces and the cone of the two normals.
    pl = Plot(f, 45, 45, 265, 265, (0, 1.15), (0, 1.15))
    pl.axes([(0.5, '0.5'), (1, '1')], [(0.5, '0.5'), (1, '1')],
            xlabel='*p*', ylabel='*q*')
    top = 1.15
    ends = [(top, top * Y0 / X0), (top * 9 / 11, top)]
    f.polygon([pl.q(0, 0), pl.q(*ends[0]), pl.q(top, top), pl.q(*ends[1])],
              fill=FILLS[1], stroke='none')
    for e in ends:
        f.line(pl.q(0, 0), pl.q(*e), stroke=ORANGE, width=1.3)
    pl.label(*ends[0], '(*X*_0, *Y*_0)', size=13, color=ORANGE, dx=5)
    pl.label(*ends[1], '(9, 11)', size=13, color=ORANGE, dx=5, dy=8)
    zq = root(lambda z: transition_split(z)[1], PI / 6, PI / 2)
    assert abs(zq - 0.66) < 0.005
    pl.points([force(PI / 6 + PI / 3 * k / 80) for k in range(81)],
              stroke=INK, width=1.4, dash='2 3')
    pl.points([force(PI / 6 * k / 60) for k in range(61)], stroke=INK,
              width=2.4)
    for z in (0, PI / 6):
        pl.dot(*force(z), r=3.4)
    pl.dot(*force(zq), r=2.6, fill=FAINT)
    pl.label(1.0, 1.0, '*z* = 0', size=13, dx=7, dy=-2)
    pl.label(*force(PI / 6), '*z* = π/6', size=13, anchor='end', dx=-7,
             dy=-2)
    pl.label(*force(zq), '*z* ≈ 0.66', size=13, color=FAINT, dx=6, dy=5)
    pl.label(0.93, 0.8, '(cos *z*, 1 − sin *z*)', size=13, anchor='end',
             dx=-6)
    pl.label(0.78, 1.08, 'cone', size=13, color=ORANGE, anchor='middle')
    # Right: the (A, v)-plane near the transition state; the level lines of
    # the form through it leave the axial states on their lower side.
    box = (0.9, 1.24, 0.12, 0.5)
    g = Figure(0.86, 1.25, 0.08, 0.53, 640)
    _, ax, sd, _ = regions()
    g.polygon(clip_box(ax, box), fill=FILLS[0], stroke='none')
    g.polygon(clip_box(sd, box), fill=FILLS[2], stroke='none')
    polyline(g, circle_in_box(box), width=1.3)
    c = 2 * PI + 7
    s0 = seg_in_window(9, 11, c, box)
    g.line(s0[0], s0[1], width=1.1, dash='4 3')
    for z, name in ((0, '*z* = 0'), (PI / 6, '*z* = π/6')):
        p, q = force(z)
        seg = seg_in_window(p, q, p * A0 + q * U0, box)
        g.line(seg[0], seg[1], stroke=ORANGE, width=1.8)
        hi = max(seg, key=lambda t: t[1])
        label(g, hi, name, size=13, color=ORANGE, anchor='middle', dy=-10)
        # the axial states lie on the lower side of the line
        assert all(p * A + q * v <= p * A0 + q * U0 + 1e-9
                   for A, v in axial_region_points(60))
    g.dot((A0, U0), r=4)
    label(g, (A0 - 0.012, U0 - 0.018), '(*a*_0, *u*_0)', size=13,
          anchor='end')
    g.text((1.0, 0.2), 'axial', size=14, italic=False, color=BLUE)
    g.text((1.11, 0.47), 'side', size=14, italic=False, color=GREEN,
           anchor='start')
    g.line((1.105, 0.466), (0.997, 0.446), stroke=GREEN, width=0.8)
    label(g, (1.238, 0.3), 'tie line', size=13, anchor='end')
    label(g, (1.13, 0.145), 'circle', size=13, anchor='end')
    g.polygon([(box[0], box[2]), (box[1], box[2]), (box[1], box[3]),
               (box[0], box[3])], stroke=FAINT, width=1)
    k = 1 / g.s
    for a in (1.0, 1.1, 1.2):
        g.line((a, box[2]), (a, box[2] + 4 * k), stroke=FAINT, width=1)
        label(g, (a, box[2]), f'{a:g}', size=12, color=FAINT, anchor='middle',
              dy=13)
    for v in (0.2, 0.3, 0.4):
        g.line((box[0], v), (box[0] + 4 * k, v), stroke=FAINT, width=1)
        label(g, (box[0], v), f'{v:g}', size=12, color=FAINT, anchor='end',
              dx=-5)
    label(g, (box[1], box[2]), '*A*', size=15, color=FAINT, dx=-2, dy=13)
    label(g, (box[0], box[3] - 0.025), '*v*', size=15, color=FAINT,
          anchor='end', dx=-5)
    f = side_by_side([(f, 0), (g, 8)], gap=6)
    f.save('appendix-i/transition-force', 'Left: the plane of forces. For '
           'turns z from 0 to pi/6 the force (cos z, 1 - sin z) lies in the '
           'cone spanned by the normals (X0, Y0) of the circle and (9, 11) of '
           'the tie line at the transition state. Right: the level lines of '
           'the form through the transition state leave the states with axial '
           'label on their lower side')


# Figure: the profile of an axial target at a negative turn.

def axial_margins():
    """Lambda, the bounds f (small turns) and m2 (large turns) of Lemma I.2."""
    lam_ = lambda z: 1 + 2 * PI / 15 - 0.8 * z + math.cos(z)
    f0 = lambda z: lam_(z) - X0 * math.cos(z) - Y0 * (1 - math.sin(z))
    m2 = lambda z: lam_(z) - 2.55 * (math.cos(z / 2) - math.sin(z / 2))
    return lam_, f0, m2


def axial_profile():
    pts = axial_region_points()
    lam_, f0, m2 = axial_margins()
    E = lambda z: min(lam_(z) - (A + .5) * math.cos(z) - (v + .5) *
                      (1 - math.sin(z)) for A, v in pts)
    tangent = lambda z: f0(0) + (Y0 - 0.8) * z
    # the decimal bounds of the proof of Lemma I.2
    assert 1.11979 < A0 < 1.1198 and 0.29136 < U0 < 0.29137
    assert 2 + 2 * 3.1415 / 15 > 2.4188 and 2.4188 - 1.6198 - 0.79137 > 0.0076
    assert 0.8 - 0.79136 < 0.0087 and PI / 6 < 0.53
    assert 0.0076 - 0.0087 * 0.53 > 0
    assert 3 / 5 * 5 / 6 - 4 / 5 / 2 > 0
    assert 13 / 2 < 6.5025 and abs((51 / 20) ** 2 - 6.5025) < 1e-12
    assert math.sqrt(3) / 2 > 0.865 and 1.865 - 51 / 28 > 0
    for k in range(101):
        z = PI / 6 * k / 100
        assert (X0 - 1) * math.cos(z) - Y0 * math.sin(z) > 0
        assert f0(z) >= tangent(z) > 0 and abs(E(z) - f0(z)) < 1e-9
    zs = root(m2, 0.2, 0.5)
    assert abs(zs - 0.32) < 0.005 and abs(f0(0) - 0.0077) < 1e-4
    assert abs(tangent(PI / 6) - 0.0032) < 1e-4
    zmax = argmin(lambda z: -E(z), 0.8, PI / 2, 200)
    assert abs(E(zmax) - 0.167) < 0.002 and abs(m2(PI / 2) - 0.162) < 0.001
    lo, hi = PI / 6, PI / 2
    chord = lambda z: m2(lo) + (m2(hi) - m2(lo)) * (z - lo) / (hi - lo)
    f = Figure(0, 700, 0, 315, 1)
    # Left: the whole range of turns.
    pl = Plot(f, 55, 45, 330, 225, (0, PI / 2), (0, 0.2))
    pl.axes([(0, '0'), (PI / 6, 'π/6'), (1, '1'), (PI / 2, 'π/2')],
            [(0.1, '0.1'), (0.2, '0.2')], xlabel='*z*')
    pl.vline(PI / 6, a=0.07, b=0.17)
    pl.points([(0, 0.07), (PI / 6, 0.07), (PI / 6, 0)], stroke=FAINT,
              width=1, dash='2 3')
    pl.curve(m2, zs, PI / 6, stroke=GREEN, width=1.4, dash='1 3')
    pl.curve(chord, lo, hi, stroke=GREEN, width=1.2, dash='5 3')
    pl.curve(E, 0, PI / 2, n=160, stroke=BLUE, width=2.2)
    pl.curve(f0, 0, PI / 6, stroke=ORANGE, width=1.8)
    pl.curve(m2, PI / 6, PI / 2, stroke=GREEN, width=1.8)
    pl.label(0.05, 0.19, 'least value over the axial states', size=13,
             color=BLUE)
    pl.label(1.3, 0.182, '*m*_2', size=14, color=GREEN, anchor='middle')
    pl.label(1.2, 0.108, 'chord', size=13, color=GREEN)
    pl.label(0.2, 0.045, '*f*', size=15, color=ORANGE, anchor='middle')
    # Right: the small turns, magnified.
    pr = Plot(f, 460, 45, 190, 225, (0, 0.58), (0, 0.07))
    pr.axes([(0, '0'), (0.25, '0.25'), (PI / 6, 'π/6')],
            [(0.03, '0.03'), (0.06, '0.06')], xlabel='*z*')
    pr.curve(E, 0, PI / 6, n=120, stroke=BLUE, width=2.2)
    pr.curve(f0, 0, PI / 6, stroke=ORANGE, width=1.8)
    pr.curve(tangent, 0, PI / 6, stroke=ORANGE, width=1.6, dash='5 3')
    pr.dot(PI / 6, tangent(PI / 6), r=3, fill=ORANGE)
    pr.label(0.05, 0.045, '*f*, the least value', size=13, color=ORANGE)
    pr.label(0.27, 0.0135, 'tangent at 0', size=13, color=ORANGE)
    f.save('appendix-i/axial-profile', 'The left side of Lemma I.2 minimized '
           'over the admissible states with axial label, as a function of z, '
           'with the two lower bounds of the proof: up to pi/6 its value f at '
           'the transition state, which is the least value there and lies '
           'above its tangent at 0, and the concave m2 from pi/6 to pi/2, '
           'which lies above its chord; the right panel magnifies the small '
           'turns')


# Figure: the tangent at the transition state.

def transition_tangent():
    box = (0.62, 1.24, 0.2, 0.84)
    f = Figure(box[0], box[1], box[2], box[3], 560)
    sd = regions()[2]
    f.polygon(sd, fill=FILLS[2], stroke=GREEN, width=1)
    polyline(f, circle_in_box(box), width=1.3)
    c = 2 * PI + 7
    s = seg_in_window(9, 11, c, box)
    f.line(s[0], s[1], width=1.2, dash='4 3')
    # the tangent at the transition state and the quarter plane
    s = seg_in_window(X0, Y0, X0 * A0 + Y0 * U0, box)
    f.line(s[0], s[1], stroke=ORANGE, width=2)
    f.line((box[0], U0), (box[1], U0), stroke=FAINT, width=1, dash='2 3')
    f.line((A0, box[2]), (A0, box[3]), stroke=FAINT, width=1, dash='2 3')
    # every state with side label lies in the quarter plane, on the inner
    # side of the tangent and of the line of slope -25/12
    for A, v in side_region_points(60):
        assert v >= U0 - 1e-9 and A <= A0 + 1e-9
        assert X0 * (A - A0) + Y0 * (v - U0) <= 1e-9
        assert 12 / 25 * (v - U0) <= A0 - A + 1e-9
    f.dot((A0, U0), r=4)
    label(f, (A0 - 0.02, U0 - 0.035), '(*a*_0, *u*_0)', size=14,
          anchor='end')
    f.text((0.885, 0.55), 'side labels', size=14, italic=False, color=GREEN)
    label(f, (0.665, 0.565), 'tie line', size=13)
    label(f, (1.105, 0.62), 'tangent', size=14, color=ORANGE, anchor='end')
    label(f, (0.64, U0), '*v* = *u*_0', size=13, color=FAINT, dy=-10)
    label(f, (A0, 0.82), '*A* = *a*_0', size=13, color=FAINT, dx=6)
    f.save('appendix-i/transition-tangent', 'The states with side label lie in '
           'the quarter plane v at least u0, A at most a0, and on the inner '
           'side of the tangent of the circle at the transition state')


# Figure: the profile of a side target at a negative turn.

def tangent_rate(z):
    """The rate k(z) of Lemma I.6 along the line of Lemma I.4."""
    return 12 / 25 * (math.cos(z) - 0.6) + math.sin(z) - 4 / 15


def disk_bound(z):
    """g(z) of Lemma I.6: the side target is at least g(z) on the disk."""
    return math.sin(z) - 0.8 * z - 13 / 4 * (1 - math.cos(z))


def side_E(z, A, v):
    return (math.cos(z) - 2 / 15 - 0.8 * z + (0.6 - math.cos(z)) * (A + .5)
            + (math.sin(z) - 4 / 15) * (v + .5))


def side_profile():
    pts = side_region_points()
    m = lambda z: min(side_E(z, A, v) for A, v in pts)
    # the identity and the bounds of the proof of Lemma I.6
    for k in range(1, 100):
        z = k / 1000
        for A, v in ((1, .5), (A0, U0), (0.7, 0.6), (1.2, 0.1)):
            sq = ((A - 1 + 15 / 4 * (1 - math.cos(z))) ** 2 +
                  (v - .5 + 15 / 4 * math.sin(z)) ** 2)
            phi = (A + .5) ** 2 + (v + .5) ** 2
            rhs = disk_bound(z) + 2 / 15 * (R2 - phi) + 2 / 15 * sq
            assert abs(side_E(z, A, v) - rhs) < 1e-12
        assert disk_bound(z) >= z * (1 / 5 - 13 / 8 * z - z * z / 6) \
            > z * (1 / 5 - 2 * z) > 0
    z = 0.1
    k_low = 12 / 25 * (1 - z * z / 2 - 0.6) + z - z ** 3 / 6 - 4 / 15
    assert k_low <= tangent_rate(z) and abs(1 - z * z / 2 - 0.6 - 0.395) < 1e-12
    assert abs(12 / 25 - 0.48) < 1e-15 and z - z ** 3 / 6 > 0.0998
    assert 4 / 15 < 0.2667 and 0.48 * 0.395 + 0.0998 - 0.2667 > 0
    assert 2 / 15 + 1 / 40 < 3 / 10 - 1 / 8 and 0.1 / 8 > 1 / 100
    assert U0 + 0.5 > 4 / 5 - 1 / 100 and A0 - 0.5 > 3 / 5
    zk = root(tangent_rate, 0, 1)
    zc = math.acos(0.6)
    zg = root(disk_bound, 0.1, 0.2)
    assert abs(zk - 0.076) < 0.001 and abs(zg - 0.12) < 0.003
    assert abs(tangent_rate(0) + 0.075) < 0.001
    assert abs(tangent_rate(1) - 0.55) < 0.005 and abs(m(1) - 0.16) < 0.003
    # where k >= 0 the least value is the value at the transition state
    for z in (0.08, 0.1, 0.3, 0.6, 0.9, 0.95, 1.0):
        assert abs(m(z) - side_E(z, A0, U0)) < 1e-9
    for z in (0.01, 0.03, 0.05):
        assert side_E(z, A0, U0) > m(z) + 1e-5
    f = Figure(0, 600, 0, 430, 1)
    # Top: the least value and its bounds, with the small turns magnified.
    pl = Plot(f, 60, 205, 480, 190, (0, 1), (0, 0.17))
    pl.axes([(0, '0'), (0.1, ''), (zc, ''), (1, '1')],
            [(0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')], xlabel='*z*')
    for x in (0.1, zc):
        pl.vline(x)
    pl.curve(lambda z: side_E(z, A0, U0), 0, 1, stroke=GREEN, width=1.6,
             dash='5 3')
    pl.curve(m, 0, 1, n=160, stroke=BLUE, width=2.2)
    pl.curve(disk_bound, 0, zg, stroke=ORANGE, width=1.8)
    pl.label(0.6, 0.04, 'least value', size=13, color=BLUE)
    for x, t in ((0.05, '1'), ((0.1 + zc) / 2, '2'), ((zc + 1) / 2, '3')):
        pl.label(x, 0.175, t, size=13, color=FAINT, anchor='middle')
    # the inset: [0, 0.15] x [0, 0.012]
    zin = (0, 0.15)
    pi_ = Plot(f, 125, 285, 190, 95, zin, (0, 0.012))
    pl.points([(zin[0], 0), (zin[1], 0), (zin[1], 0.012), (zin[0], 0.012),
               (zin[0], 0)], stroke=FAINT, width=0.8, dash='2 2')
    pi_.frame()
    f.line(pl.q(zin[1], 0.012), pi_.q(zin[1], 0), stroke=FAINT, width=0.8)
    f.line(pl.q(zin[0], 0.012), pi_.q(zin[0], 0), stroke=FAINT, width=0.8)
    pi_.vline(0.1)
    pi_.vline(zk, stroke=PURPLE, dash='2 3')
    pi_.curve(lambda z: side_E(z, A0, U0), 0, 0.15, stroke=GREEN, width=1.6,
              dash='5 3')
    pi_.curve(m, 0, 0.15, n=120, stroke=BLUE, width=2.2)
    pi_.curve(disk_bound, 0, zg, stroke=ORANGE, width=1.8)
    pi_.label(0.004, 0.0105, 'transition state', size=12, color=GREEN)
    pi_.label(0.06, 0.003, '*g*', size=14, color=ORANGE, anchor='middle')
    pi_.label(0.1, 0, '1/10', size=12, color=FAINT, anchor='middle', dy=11)
    pi_.label(zk, 0.012, '*k* = 0', size=12, color=PURPLE, anchor='middle',
              dy=-9)
    # Bottom: the rate k along the line of Lemma I.4.
    pb = Plot(f, 60, 45, 480, 110, (0, 1), (-0.1, 0.6))
    pb.axes([(0, ''), (0.1, '1/10'), (zc, ''), (1, '1')],
            [(0, '0'), (0.5, '0.5')], xlabel='*z*', at=-0.1)
    pb.label(zc, -0.1, 'arccos 3/5', size=12, anchor='end', dx=8, dy=14)
    pb.hline(0, stroke=INK, dash=None, width=0.8)
    for x in (0.1, zc):
        pb.vline(x)
    pb.curve(tangent_rate, 0, 1, stroke=PURPLE, width=2)
    pb.dot(0, tangent_rate(0), r=3, fill=PURPLE)
    pb.dot(zk, 0, r=3, fill=PURPLE)
    pb.label(0.12, -0.055, '*k*(0) ≈ −0.075', size=13, color=PURPLE)
    pb.label(0.45, 0.42, '*k*(*z*)', size=14, color=PURPLE, anchor='end')
    f.save('appendix-i/side-profile', 'Top: the expression of Lemma I.6 '
           'minimized over the admissible states with side label, as a '
           'function of z, with its value at the transition state and the '
           'bound g from the disk alone used below 1/10, and an inset '
           'magnifying the small turns. Bottom: the rate k(z), increasing, '
           'negative only below about 0.076; the three cases of the proof '
           'are cut at 1/10 and where cos z = 3/5')


# Figure: the support sum for target sign negative, over the turn.

def beta_axial(A, v, e):
    """beta(A, v; e, rho) for an axial target, Lemma I.3."""
    return (0.5 + 2 * PI / 15 + 0.8 * e - (A - .5) * math.cos(e) -
            v * (1 + math.sin(e)) + 0.5 * abs(math.sin(e)))


def beta_side(A, v, e):
    """beta_side(A, v; e) of Lemma I.5."""
    return (0.8 * e + 2 / 15 * (4 - 3 * A - 2 * v) + (A - .5) * (1 - math.cos(e))
            - v * math.sin(e) + 0.5 * abs(math.sin(e)))


def negative_target():
    axp, sdp = axial_region_points(90), side_region_points(110)
    ma = lambda e: min(beta_axial(A, v, e) for A, v in axp)
    ms = lambda e: min(beta_side(A, v, e) for A, v in sdp)
    e_lo, e_hi, e_side = -5 * PI / 12, PI / 3, 9 / 25 - 5 * PI / 12
    assert -1 < e_side < -0.94
    assert abs(beta_side(1, .5, 0)) < 1e-12 and abs(ma(0) - 0.0077) < 1e-4
    for k in range(41):
        e = e_hi * k / 40
        assert ms(e) >= 21 / 40 * e - 1e-12
    # between the two crossings of the cones both are attained at the
    # transition state, which has both labels
    for e in (-0.64, -0.5, -0.3, -0.15, -0.08):
        assert abs(ma(e) - ms(e)) < 1e-9
        assert abs(ma(e) - beta_side(A0, U0, e)) < 1e-9
    assert ma(-0.7) < ms(-0.7) - 1e-4 and ms(-0.07) < ma(-0.07) - 1e-6
    f = Figure(0, 640, 0, 345, 1)
    pl = Plot(f, 60, 45, 520, 250, (e_lo, e_hi), (0, 0.6))
    pl.axes([(e_lo, '−5π/12'), (-1, '−1'), (-0.5, '−0.5'), (0, '0'),
             (0.5, '0.5'), (e_hi, 'π/3')],
            [(0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6')], xlabel='*e*')
    pl.curve(ma, e_lo, e_hi, n=200, stroke=BLUE, width=2.2)
    pl.curve(ms, e_side, e_hi, n=200, stroke=GREEN, width=2.2, dash='7 4')
    pl.curve(lambda e: 21 / 40 * e, 0, e_hi, stroke=GREEN, width=1.2,
             dash='2 3')
    pl.label(0.58, 0.55, 'axial target', size=13, color=BLUE, anchor='end')
    pl.label(0.62, 0.22, 'side target', size=13, color=GREEN)
    pl.label(0.93, 0.44, '21*e*/40', size=13, color=GREEN)
    # the inset near the contact
    ein, yin = (-0.12, 0.12), (0, 0.024)
    pi_ = Plot(f, 140, 150, 195, 115, ein, yin)
    pl.points([(ein[0], 0), (ein[1], 0), (ein[1], yin[1]), (ein[0], yin[1]),
               (ein[0], 0)], stroke=FAINT, width=0.8, dash='2 2')
    pi_.frame()
    f.line(pl.q(ein[0], yin[1]), pi_.q(ein[0], 0), stroke=FAINT, width=0.8)
    f.line(pl.q(ein[1], yin[1]), pi_.q(ein[1], 0), stroke=FAINT, width=0.8)
    pi_.curve(ma, ein[0], ein[1], n=120, stroke=BLUE, width=2.2)
    pi_.curve(ms, ein[0], ein[1], n=120, stroke=GREEN, width=2.2, dash='7 4')
    pi_.dot(0, 0, r=3.5, fill=ORANGE)
    pi_.label(0.006, 0.0018, 'contact', size=12, color=ORANGE)
    pi_.label(0, ma(0), '0.0077', size=12, color=BLUE, anchor='end', dx=-4,
              dy=-9)
    f.save('appendix-i/negative-target', 'Graph over the turn e of the least '
           'value of the lower bound of Lemma I.1 over the axial targets and '
           'over the side targets; both are positive except the side curve at '
           'e = 0, where it touches zero at the contact, magnified in an inset; '
           'for negative turns the two curves coincide')


# Figures: the side margin and the lines B(w) = 0.

def M_w(w):
    return 19 / 20 + math.cos(w) - min(math.sin(w), 0) - 1.2 * w


def margin400(w):
    return 400 * (M_w(w) ** 2 - R2 * ((math.sin(w) - 0.9) ** 2 +
                                      (0.4 - math.cos(w)) ** 2))


def side_margin():
    poly_pos = lambda w: w * (468 - 724 * w + 90 * w * w - 40 * w ** 4)
    poly_neg = lambda w: -w * (212 - 636 * w + 160 * w ** 3)
    for k in range(1, 101):
        w = PI / 6 * k / 100
        assert margin400(w) >= poly_pos(w) > 0
        w = -PI / 3 * k / 100
        assert margin400(w) >= poly_neg(w) > 0
    assert abs(margin400(0)) < 1e-9
    f = Figure(0, 560, 0, 330, 1)
    pl = Plot(f, 65, 45, 440, 245, (-PI / 3, PI / 6), (0, 1100))
    pl.axes([(-PI / 3, '−π/3'), (-0.5, '−0.5'), (0, '0'), (PI / 6, 'π/6')],
            [(500, '500'), (1000, '1000')], xlabel='*w*')
    pl.curve(poly_pos, 0, PI / 6, stroke=ORANGE, width=1.6, dash='5 3')
    pl.curve(poly_neg, -PI / 3, 0, stroke=ORANGE, width=1.6, dash='5 3')
    pl.curve(margin400, -PI / 3, PI / 6, stroke=BLUE, width=2.2)
    pl.dot(0, 0, r=3.5)
    pl.label(-0.62, 860, '400 × margin', size=13, color=BLUE)
    pl.label(-1.0, 300, 'lower bounds', size=13, color=ORANGE)
    f.save('appendix-i/side-margin', 'Graph over the turn w from minus pi/3 '
           'to pi/6 of 400 times the margin of Lemma I.9, zero only at w = 0, '
           'where it has a corner, above its two polynomial lower bounds')


def side_side():
    box = (0.45, 1.5, -0.05, 1.0)
    f = Figure(0.37, 1.58, -0.12, 1.05, 380)
    av_axes(f, 0.45, 1.5, -0.05, 1.0, ticks_a=(0.5, 1.0), ticks_v=(0.5,))
    P, _, sd, _ = regions()
    f.polygon(P, fill='none', stroke=INK, width=1)
    f.polygon(sd, fill=FILLS[2], stroke=GREEN, width=1)
    polyline(f, circle_in_box(box), stroke=INK, width=1.2, dash='6 4')
    ws = ((-0.3, CYAN), (-0.15, PURPLE), (0.0, ORANGE), (0.15, PINK),
          (0.3, BLUE))
    lo_w, hi_w = 2 * S0 - PI / 3, PI / 6
    for w, col in ws:
        assert lo_w <= w <= hi_w
        p, q = math.sin(w) - 0.9, 0.4 - math.cos(w)
        n = math.hypot(p, q)
        # the point of the line B(w) = 0 closest to the centre of the disk
        foot = (-.5 - p / n * M_w(w) / n, -.5 - q / n * M_w(w) / n)
        gap = M_w(w) / n - R
        assert (gap > 0) == (w != 0) and gap > -1e-12
        along = (q / n, -p / n)
        f.line(shift(foot, along, -0.2), shift(foot, along, 0.2),
               stroke=col, width=2.4 if w == 0 else 1.7)
    # the legend, in the empty corner beyond the disk
    for i, (w, col) in enumerate(reversed(ws)):
        y = 0.93 - 0.055 * i
        f.line((1.2, y), (1.27, y), stroke=col, width=2.4 if w == 0 else 1.7)
        label(f, (1.29, y), f'*w* = {w:g}'.replace('-', '−'), size=13,
              color=col)
    f.dot((1, .5), r=3.5)
    label(f, (0.97, 0.52), '(1, ½)', size=13, anchor='end')
    label(f, (0.85, 0.585), 'side', size=13, color=GREEN, anchor='middle')
    label(f, (1.33, 0.07), '*φ* = 13/4', size=13)
    f.save('appendix-i/side-side', 'The (A, v)-plane with the admissible region, '
           'its states with side label (green) and the dashed circle '
           'phi = 13/4, and short pieces of the lines B(w) = 0 for w = -0.3, '
           '-0.15, 0, 0.15 and 0.3 near their points closest to the disk; '
           'only the line for w = 0 touches the circle, at the side state '
           '(1, 1/2)')


# Figure: the mixed clearance.

def clearance():
    form = lambda A, v: 0.6 * (A + .5) + 11 / 15 * (v + .5)
    # the form is largest on the side region at the diagonal corner
    assert max(form(A, v) for A, v in side_region_points(160)) \
        <= form(RD, RD) + 1e-12
    ts = [S0 + (PI / 4 - S0) * k / 4000 for k in range(4001)]
    assert abs(max(ts, key=lambda t: form(*top(t))) - TD) < 1e-3
    assert form(RD, RD) < 17 / 10 and 17 / 10 - form(RD, RD) < 4e-4
    assert abs(form(31 / 40, 31 / 40) - 17 / 10) < 1e-12
    assert 2 * RD < 31 / 20
    box = (0.62, 1.22, 0.24, 0.92)
    f = Figure(0.55, 1.26, 0.17, 0.96, 470)
    av_axes(f, 0.62, 1.22, 0.24, 0.92, ticks_a=(0.75, 1.0), ticks_v=(0.5, 0.75))
    _, _, sd, cap = regions()
    f.polygon(clip_box(regions()[0], box), fill='none', stroke=FAINT, width=1)
    f.polygon(sd, fill=FILLS[2], stroke=GREEN, width=1)
    f.polygon(cap, fill=GREY, stroke='none')
    polyline(f, circle_in_box(box), width=1.2, dash='6 4')
    f.line((0.62, 0.62), (0.92, 0.92), width=0.9, stroke=FAINT)
    # the bound 17/10 of the form, and A + v = 31/20
    s = seg_in_window(0.6, 11 / 15, 17 / 10 - 0.6 / 2 - 11 / 30, box)
    f.line(s[0], s[1], stroke=ORANGE, width=2.2)
    s = seg_in_window(1, 1, 31 / 20, box)
    f.line(s[0], s[1], stroke=PURPLE, width=1.4, dash='7 4')
    f.dot((RD, RD), r=4)
    label(f, (RD + 0.02, RD + 0.03), '(*r*_d, *r*_d)', size=13)
    label(f, (0.96, 0.47), 'side', size=13, color=GREEN, anchor='middle')
    label(f, (0.63, 0.74), '*v* = *A*', size=13, color=FAINT)
    for i, (col, dash, wd, text) in enumerate((
            (ORANGE, None, 2.2, 'form = 17/10'),
            (PURPLE, '7 4', 1.4, '*A* + *v* = 31/20'))):
        y = 0.9 - 0.045 * i
        f.line((0.95, y), (1.0, y), stroke=col, width=wd, dash=dash)
        label(f, (1.015, y), text, size=13, color=col)
    label(f, (1.14, 0.28), '*φ* = 13/4', size=13)
    f.save('appendix-i/clearance', 'The (A, v)-plane near the side region '
           '(green): the orange line where the form 3/5 (A + 1/2) + 11/15 '
           '(v + 1/2) equals 17/10, and the dashed purple line '
           'A + v = 31/20; both lines cross the '
           'diagonal v = A just beyond the diagonal corner (rd, rd), the state '
           'with side label where the form is largest')


# Figure: the lower bounds of the opposite-sign sector in the turn.

def opposite_profiles():
    base = lambda w: math.sin(w) - 0.8 * w - 0.5 * (1 - math.cos(w))
    aa_neg = lambda z: (1 - 4 * PI / 15 + 0.8 * z - KAPPA * math.sin(z) -
                        0.5 * (1 - math.cos(z)))
    psi = lambda z: (0.5 - PI / 5 + 1.2 * z - KAPPA * math.sin(z) -
                     0.5 * (1 - math.cos(z)))
    # the bounds of the proofs of Lemmas I.13 and I.15
    assert 13 / 30 - 2 * PI / 15 > 13 / 30 - 44 / 105 > 1 / 70 - 1e-15
    assert max(0.6 * (A + .5) + 11 / 15 * (v + .5)
               for A, v in side_region_points()) < 17 / 10
    assert 22 / 35 < 0.6286 and 22 / 75 < 0.2934
    assert 0.5 + 12 / 25 - 1 / 25 - 0.6286 - 0.2934 > 0 and psi(0.4) > 0
    assert 6 / 5 - 11 / 15 - 7 / 20 > 0 and 1 / 70 - 1 / 75 > 0
    assert PI / 3 - 9 / 25 < 7 / 10
    f = Figure(0, 640, 0, 340, 1)
    pl = Plot(f, 60, 50, 520, 250, (-PI / 3, PI / 6), (0, 0.24))
    pl.axes([(-PI / 3, '−π/3'), (-0.7, '−7/10'), (-0.4, '−2/5'),
             (0, '0'), (PI / 6, 'π/6')],
            [(1 / 70, '1/70'), (0.1, '0.1'), (0.2, '0.2')], xlabel='*w*')
    pl.vline(-0.7, b=0.18)
    pl.vline(-0.4, b=0.18)
    pl.curve(lambda w: 1 - 4 * PI / 15 + base(w), 0, PI / 6, stroke=BLUE,
             width=2)
    pl.curve(lambda w: aa_neg(-w), -PI / 3, 0, stroke=BLUE, width=2)
    pl.curve(lambda w: 1 - 4 * PI / 15 + w / 10, -PI / 3, 0, stroke=BLUE,
             width=1.2, dash='5 3')
    pl.curve(lambda w: 1 / 70 + base(w), 0, PI / 6, stroke=GREEN, width=2)
    pl.curve(lambda w: 1 / 70 - w * (7 / 40 + w / 4), -0.7, 0, stroke=GREEN,
             width=2)
    pl.curve(lambda w: 1 / 70 - w / 15 - w * w / 4, -0.4, 0, stroke=PINK,
             width=2, dash='5 3')
    pl.curve(lambda w: psi(-w), -0.7, -0.4, stroke=PINK, width=2, dash='5 3')
    legend = ((BLUE, None, 'two axial labels: Lemma I.12'),
              (GREEN, None, 'axial source, side target: Lemma I.14'),
              (PINK, '5 3', 'side source, axial target: Lemma I.15'))
    for i, (col, dash, text) in enumerate(legend):
        y = 0.233 - 0.016 * i
        pl.points([(-1.0, y), (-0.88, y)], stroke=col, width=2, dash=dash)
        pl.label(-0.85, y, text, size=13, color=col)
    f.save('appendix-i/opposite-profiles', 'The lower bounds for the support '
           'sum with opposite signs as functions of the turn w, for two axial '
           'labels, above a line of slope 1/10 for negative turns, and for '
           'the two mixed pairs of labels; all are positive')


# Figure: the marker point of Lemma I.17.

def marker_inset(f, box, frame, cS, cT, d, p, theta):
    """Draw the part of the picture inside box, magnified into frame."""
    x0, x1, y0, y1 = box
    X0f, X1f, Y0f, Y1f = frame
    k = (X1f - X0f) / (x1 - x0)
    m = lambda q: (X0f + (q[0] - x0) * k, Y0f + (q[1] - y0) * k)
    f.polygon([(X0f, Y0f), (X1f, Y0f), (X1f, Y1f), (X0f, Y1f)], fill='#ffffff',
              stroke='none')
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
    label(f, shift(m((xg, (p[1] + topS) / 2)), (0.04, 0)), 'gap', size=13)
    f.polygon([(X0f, Y0f), (X1f, Y0f), (X1f, Y1f), (X0f, Y1f)], stroke=INK,
              width=1)
    return m


def marker_point():
    a, us = A0, U0
    cS, cT, d, _, mT = canonical(a, us, 1.0, 0.5, -1, -1)
    theta = mT - 0.5
    assert abs(theta - (PI / 3 - S0 - 0.5)) < 1e-12
    assert 0 < math.sin(theta) < 0.5 - us
    assert abs(math.degrees(d) - 69) < 1
    p = u(theta)
    f = Figure(-0.25, 2.8, -0.92, 1.45, 215)
    f.circle((0, 0), 1.0, stroke=FAINT, width=1)
    f.square(cS, 0, fill=FILLS[0], stroke=BLUE, opacity=0.85)
    f.square(cT, math.degrees(d), fill=FILLS[2], stroke=GREEN, opacity=0.85)
    f.arc((0, 0), 1.0, mT - 1 / 2, mT + 1 / 2, GREEN, width=5)
    f.line((0, 0), u(mT), stroke=GREEN, width=1.2, dash='5 3')
    f.line((0, 0), p, stroke=INK, width=1)
    f.arc((0, 0), 0.32, 0, theta, INK, width=1.1)
    label(f, shift((0, 0), u(theta / 2), 0.42), '*θ*', size=15,
          anchor='middle')
    f.dot(p, r=4, fill=ORANGE)
    label(f, shift(p, (-0.1, -0.09)), '*u*(*θ*)', size=15, color=ORANGE,
          anchor='end')
    topS = cS[1] + 0.5
    label(f, (0.15, 0.62), 'marker arc of *T*', size=13, color=GREEN,
          anchor='end')
    # the magnified neighbourhood of u(theta)
    box = (p[0] - 0.07, p[0] + 0.13, p[1] - 0.06, p[1] + 0.07)
    frame = (1.85, 2.75, 0.33, 0.33 + 0.9 * (box[3] - box[2]) /
             (box[1] - box[0]))
    f.polygon([(box[0], box[2]), (box[1], box[2]), (box[1], box[3]),
               (box[0], box[3])], stroke=INK, width=0.8)
    f.line((box[1], box[3]), (frame[0], frame[3]), stroke=FAINT, width=0.8)
    f.line((box[1], box[2]), (frame[0], frame[2]), stroke=FAINT, width=0.8)
    m = marker_inset(f, box, frame, cS, cT, d, p, theta)
    f.text((2.3, frame[3] + 0.08), 'magnified', size=13, italic=False,
           color=FAINT)
    label(f, (frame[0], m((0, topS))[1]), 'top of *S*: ½ − *u*', size=13,
          color=BLUE, anchor='end', dx=-6)
    label(f, (frame[0], m(p)[1]), 'height sin *θ*', size=13, color=ORANGE,
          anchor='end', dx=-6)
    f.dot((0, 0), r=2.8)
    label(f, (-0.05, -0.08), '*o*', size=14, anchor='end')
    label(f, shift(cS, (0.05, -0.1)), '*S*', size=16, color=BLUE,
          anchor='middle')
    label(f, shift(cT, (0.05, 0.15)), '*T*', size=16, color=GREEN,
          anchor='middle')
    f.save('appendix-i/marker-point', 'A canonical pair for the signs minus 1 '
           'and minus 1 with a side source of small label: the point u(theta) '
           'of the marker arc of T, half a radian behind its marker, lies in T '
           'and below the top edge of S')


# Figure: segments of constant label and where the support is least.

def segments():
    box = (0.44, 1.3, -0.06, 0.86)
    f = Figure(0.37, 1.36, -0.13, 0.9, 470)
    av_axes(f, 0.44, 1.3, -0.06, 0.86, ticks_a=(0.5, 1.0), ticks_v=(0.5,))
    region_frame(f, width=1.2)
    l = 0.55
    dd = lambda t: PI / 3 - l + t
    for k in range(9):
        t = PI / 4 * k / 8
        v = 0.8 * t
        a1 = chi(v)
        f.line((max(0.5, v), v), (a1, v), stroke=BLUE, width=1.3)
        f.dot((a1, v), r=3.4, fill=ORANGE)
    for k in range(8):
        t = S0 + (PI / 4 - S0) * k / 7
        p0, p1 = (alpha(t), 0.8 * t), top(t)
        f.line(p0, p1, stroke=GREEN, width=1.3)
        g0, g1 = G(dd(t), *p0), G(dd(t), *p1)
        assert (g0 <= g1) == (t <= sw(l))
        f.dot(p0 if g0 <= g1 else p1, r=3.4, fill=ORANGE)
    t = sw(l)
    assert abs(t - 0.655) < 0.001
    f.line((alpha(t), 0.8 * t), top(t), stroke=ORANGE, width=1.4, dash='4 3')
    tie_segment(f, width=1)
    f.dot((A0, U0), r=3.5)
    label(f, (A0 + 0.015, U0 - 0.02), '(*a*_0, *u*_0)', size=13)
    f.dot((RD, RD), r=3.5)
    label(f, (RD + 0.015, RD + 0.025), '(*r*_d, *r*_d)', size=13)
    f.text((0.76, 0.1), 'axial', size=14, italic=False, color=BLUE)
    f.text((0.932, 0.5), 'side', size=14, italic=False, color=GREEN)
    tp = top(t)
    label(f, (tp[0] + 0.025, tp[1] + 0.035), '*τ* = sw(*ℓ*)', size=13,
          color=ORANGE)
    f.save('appendix-i/segments', 'The admissible states in the (A, v)-plane '
           'cut into segments of constant label: horizontal for axial labels, '
           'of slope 9/4 for side labels. For the source label 0.55 the orange '
           'dots mark the end of each segment where the target support is '
           'least: the circle or tie line for axial labels, the tie line '
           'below the switch and the circle or diagonal above it')


# Figure: the second derivative along the circle.

def circle_second(l, t):
    X, Y, Z, D = circle_xyzd(t)
    d = PI / 3 - l + t
    return (-math.sin(d) - D / Z ** 3 * (X * math.cos(d) + Y * math.sin(d))
            - (1 / Z - 1) ** 2 * (Y * math.cos(d) - X * math.sin(d)))


def circle_second_bound(l, t):
    _, _, Z, _ = circle_xyzd(t)
    return -math.sin(PI / 3 - l + t) + 2 * (1 / Z - 1) ** 2


def circle_concave():
    l = 0.4
    s = sw(l)
    assert S0 < s < TD
    ts = [S0 + (TD - S0) * k / 400 for k in range(401)]
    for t in ts:
        _, _, Z, _ = circle_xyzd(t)
        assert 1 < Z < 1.4
        assert circle_second(l, t) <= circle_second_bound(l, t) < 0
        if t >= s:
            assert circle_second_bound(l, t) < -4 / 5 + 8 / 49
    # the derivatives of Lemma I.19, by finite differences
    H = lambda t: G(PI / 3 - l + t, *top(t)) if t <= TD else None
    for t in (0.45, 0.6, 0.7):
        h = 1e-4
        second = (H(t + h) - 2 * H(t) + H(t - h)) / h ** 2
        assert abs(second - circle_second(l, t)) < 1e-4
    f = Figure(0, 600, 0, 320, 1)
    pl = Plot(f, 70, 40, 470, 240, (S0, TD), (-2, 0))
    pl.axes([(S0, ''), (s, 'sw(*ℓ*)'), (TD, '*t*_d')],
            [(-2, '−2'), (-1, '−1'), (-4 / 5 + 8 / 49, '−0.64')],
            xlabel='*τ*', at=0, tick_dy=-13)
    pl.label(S0, 0, '*s*_0', size=12, dx=8, dy=-13)
    pl.f.polygon([pl.q(s, -2), pl.q(TD, -2), pl.q(TD, 0), pl.q(s, 0)],
                 fill=FILLS[1], stroke='none', opacity=0.6)
    pl.hline(-4 / 5 + 8 / 49, stroke=FAINT, dash='2 3')
    pl.vline(s)
    pl.curve(lambda t: -math.sin(PI / 3 - l + t), S0, TD, stroke=ORANGE,
             width=1.4, dash='2 3')
    pl.curve(lambda t: circle_second_bound(l, t), S0, TD, stroke=GREEN,
             width=1.8, dash='6 3')
    pl.curve(lambda t: circle_second(l, t), S0, TD, stroke=BLUE, width=2.2)
    pl.label(0.45, -1.42, '*H*^{circ}_2(*ℓ*, *τ*)', size=13, color=BLUE)
    pl.label(0.38, -0.74, 'bound of the proof', size=13, color=GREEN)
    pl.label(0.62, -1.06, '−sin *d*', size=13, color=ORANGE)
    pl.label((s + TD) / 2, -1.9, 'Lemma I.20', size=13, color=ORANGE,
             anchor='middle')
    f.save('appendix-i/circle-concave', 'Graph over the side label tau from s0 '
           'to td, for the source label 2/5, of the second derivative of the '
           'target support along the circle (blue), well below the bound of '
           'the proof of Lemma I.20 (dashed green) and its main term minus '
           'sin d (dotted orange); the shaded part from the switch label to '
           'td is the range of the lemma, where the bound is below '
           'minus 4/5 plus 8/49')


# Figure: the least target support over the targets of each label.

def circle_profile():
    l = 0.5
    us = top(l)[1]
    assert abs(us - (0.5 + 1.2 * (l - PI / 6))) < 1e-3
    dd = lambda t: PI / 3 - l + t
    xi = lambda t: math.sqrt(R2 - (0.5 + 0.8 * t) ** 2)
    gc = lambda t: 0.5 - us - (xi(t) - 1) * math.sin(dd(t)) + \
        (0.5 + 0.8 * t) * math.cos(dd(t))
    gtie = lambda t: 0.5 - us + G(dd(t), alpha(t), 0.8 * t)
    gtop = lambda t: 0.5 - us + G(dd(t), *top(t))
    g4 = 0.5 - us + G(dd(S0), A0, U0)
    s = sw(l)
    assert abs(gc(S0) - g4) < 1e-12 and abs(gtie(S0) - g4) < 1e-12
    assert abs(gtop(S0) - g4) < 1e-12 and abs(gtie(s) - gtop(s)) < 1e-12
    for k in range(101):
        t = S0 * k / 100
        assert gc(t) >= g4 - 1e-12
        t = S0 + (s - S0) * k / 100
        assert gtop(t) >= gtie(t) - 1e-12 and gtie(t) >= g4 - 1e-12
        t = s + (PI / 4 - s) * k / 100
        assert gtie(t) >= gtop(t) - 1e-12 and gtop(t) > 0
    assert abs(g4 - 0.0236) < 1e-4
    f = Figure(0, 620, 0, 320, 1)
    lo, hi = 0, PI / 4
    pl = Plot(f, 60, 45, 490, 235, (lo, hi), (0, 0.12))
    pl.axes([(0, '0'), (S0, '*s*_0'), (s, 'sw(*ℓ*)'), (hi, 'π/4')],
            [(0.05, '0.05'), (0.1, '0.1')], xlabel='*τ*')
    pl.vline(S0, b=0.11)
    pl.vline(s, b=0.11)
    pl.curve(gtie, S0, hi, stroke=PURPLE, width=1.6, dash='5 3')
    pl.curve(gtop, S0, hi, stroke=GREEN, width=1.6, dash='5 3')
    pl.curve(gc, lo, S0, stroke=BLUE, width=2.4)
    pl.curve(gtie, S0, s, stroke=PURPLE, width=2.4)
    pl.curve(gtop, s, hi, stroke=GREEN, width=2.4)
    pl.hline(g4, stroke=ORANGE, dash='2 3', width=1.4)
    pl.dot(S0, g4, r=3.5)
    pl.label(0.03, 0.105, 'axial labels, on the circle', size=13, color=BLUE)
    pl.label(0.43, 0.1, 'tie states', size=13, color=PURPLE)
    pl.label(0.64, 0.055, 'tops', size=13, color=GREEN)
    pl.label(0.03, g4, '(I.4): the transition state', size=13, color=ORANGE,
             dy=-10)
    f.save('appendix-i/circle-profile', 'Graph over the target label tau from '
           '0 to pi/4, for the source label 0.5, of one half minus u plus the '
           'target support: on the axial states of the circle up to s0 '
           '(blue, decreasing), and beyond s0 at the tie state (purple) and at '
           'the top (green) of the side segment of label tau, the lower of the '
           'two drawn solid; they meet at the switch label. The least value is '
           'at s0, the transition state, marked by an orange line')


# Figure: the least forward sum for both signs negative.

def both_negative():
    xi0 = lambda l: 0.5 - top(l)[1] + G(PI / 3 - l + S0, A0, U0)
    # for sources at the top of their segment, the least sum over the active
    # targets is at the transition state
    tg = []
    n = 70
    for i in range(n + 1):
        for j in range(n + 1):
            A, v = 0.5 + KAPPA * i / n, 0.8 * j / n
            if admissible(A, v) and ell(A, v) < PI / 4 - 1e-12:
                tg.append((A, v))
    for k in range(200):
        t = PI / 4 * k / 199
        tg.append((chi(0.8 * t), 0.8 * t))
        if t >= S0:
            tg.append(top(t))
    sig = lambda l, A, v: (0.5 - top(l)[1] + G(PI / 3 - l + ell(A, v), A, v))
    for l in (0.37, 0.4, 0.5, 0.6, 0.7, 0.72, 0.75, PI / 4):
        assert min(sig(l, A, v) for A, v in tg) >= xi0(l) - 1e-12
    lmin = argmin(xi0, 0.6, PI / 4, 1000)
    assert abs(lmin - 0.72) < 0.01 and 7e-4 < xi0(lmin) < 9e-4
    b17 = lambda l: 0.5 - l / 5 - 2 * PI / 15
    assert b17(0.4) > 0 and abs(b17(0.4) - 0.0011) < 1e-4
    for k in range(101):
        l = S0 + (0.4 - S0) * k / 100
        assert xi0(l) > b17(l) > 0
    f = Figure(0, 620, 0, 320, 1)
    pl = Plot(f, 60, 45, 490, 235, (S0, PI / 4), (0, 0.07))
    pl.axes([(S0, '*s*_0'), (0.4, '2/5'), (0.6, '0.6'), (TD, '*t*_d')],
            [(0.03, '0.03'), (0.06, '0.06')], xlabel='*ℓ*')
    pl.vline(0.4)
    pl.curve(xi0, S0, PI / 4, n=400, stroke=BLUE, width=2.2)
    pl.curve(b17, S0, 0.4, stroke=ORANGE, width=1.8, dash='6 3')
    pl.dot(lmin, xi0(lmin), r=3.5)
    pl.label(lmin, xi0(lmin), '≈ 0.0008', size=12, anchor='middle', dy=-12)
    pl.label(0.47, 0.05, 'least value over the targets', size=13,
             color=BLUE)
    pl.label(0.405, 0.006, 'Lemma I.17', size=13, color=ORANGE)
    f.save('appendix-i/both-negative', 'Graph over the source label from s0 '
           'to pi/4 of the least forward sum for the signs minus 1 and minus 1 '
           'over all targets, with the source at the top of its segment; it '
           'is attained at the transition state and falls to about 0.0008 '
           'near 0.72, while the bound of Lemma I.17 is positive up to 2/5')


def main():
    forward_pairs()
    disk_support()
    switch_figure()
    transition_force()
    axial_profile()
    transition_tangent()
    side_profile()
    negative_target()
    side_margin()
    side_side()
    clearance()
    opposite_profiles()
    marker_point()
    segments()
    circle_concave()
    circle_profile()
    both_negative()


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw the figures of Appendix A (docs/proof/appendix-a.md) in
docs/proof/figures/appendix-a/.

    python3 scripts/figures/fig_appa.py

Every curve is sampled from the function it shows, and every point is
computed from the formulas of the appendix.
"""
import math

from proof_figures import (Figure, Graph, INK, FAINT, COLORS, FILLS, GREY,
                           shift, u)
from fig_front import NB, it, word, arrow, thin_arc, polyline as fpoly

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
PI = math.pi


class Plot:
    """A figure for graphs: the point (x, y) of the data is drawn at
    (kx x, ky y), so that the two axes can have different scales."""

    def __init__(self, xmin, xmax, ymin, ymax, kx, ky, pad=22):
        self.kx, self.ky = kx, ky
        self.f = Figure(xmin * kx, xmax * kx, ymin * ky, ymax * ky, 1, pad)

    def q(self, x, y):
        return (x * self.kx, y * self.ky)

    def polyline(self, pts, stroke=INK, width=1.8, dash=None):
        d = ' '.join(f'{x:.1f},{y:.1f}'
                     for x, y in (self.f.p(*self.q(*p)) for p in pts))
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
                   f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')

    def curve(self, fn, x0, x1, ylim=None, n=400, **kw):
        """The graph of fn on [x0, x1], cut where it leaves ylim."""
        pts = [(x0 + (x1 - x0) * k / n, fn(x0 + (x1 - x0) * k / n))
               for k in range(n + 1)]
        for run in clip_runs(pts, ylim):
            self.polyline(run, **kw)

    def polygon(self, pts, **kw):
        self.f.polygon([self.q(*p) for p in pts], **kw)

    def line(self, a, b, **kw):
        self.f.line(self.q(*a), self.q(*b), **kw)

    def dot(self, p, **kw):
        self.f.dot(self.q(*p), **kw)

    def text(self, p, s, **kw):
        self.f.text(self.q(*p), s, **kw)

    def save(self, name, title):
        self.f.save(name, title)


def clip_runs(pts, ylim):
    """The maximal runs of a sampled curve inside the band ylim, with the
    crossings of the band's edges added by linear interpolation."""
    if ylim is None:
        return [pts]
    lo, hi = ylim
    runs, run = [], []
    for k, (x, y) in enumerate(pts):
        inside = lo <= y <= hi
        if k and (inside != (lo <= pts[k - 1][1] <= hi)):
            (x0, y0) = pts[k - 1]
            edge = hi if max(y, y0) > hi else lo
            s = (edge - y0) / (y - y0)
            cross = (x0 + s * (x - x0), edge)
            run.append(cross)
            if not inside:
                runs.append(run)
                run = []
        if inside:
            run.append((x, y))
    if run:
        runs.append(run)
    return [r for r in runs if len(r) > 1]


def is_letter(name):
    """Whether a tick label is a variable, set in italics."""
    return len(name) == 1 and name.isalpha()


def x_axis(p, x0, x1, y=0.0, ticks=(), label='', size=13):
    p.line((x0, y), (x1, y), width=1, arrow=True)
    for x, name in ticks:
        a, b = p.q(x, y)
        p.f.line((a, b - 4), (a, b + 4), width=1)
        p.f.text((a, b), name, size=size + is_letter(name) * 2,
                 italic=is_letter(name), dy=15)
    if label:
        p.text((x1, y), label, size=15, anchor='end', dy=-12)


def y_axis(p, y0, y1, x=0.0, ticks=(), label='', size=13):
    p.line((x, y0), (x, y1), width=1, arrow=True)
    for y, name in ticks:
        a, b = p.q(x, y)
        p.f.line((a - 4, b), (a + 4, b), width=1)
        p.f.text((a, b), name, size=size + is_letter(name) * 2,
                 italic=is_letter(name), anchor='end', dx=-7)
    if label:
        p.text((x, y1), label, size=15, anchor='start', dx=8, dy=4)


def vtick(p, x, y, name, size=13, color=INK, dy=15):
    a, b = p.q(x, y)
    p.f.line((a, b - 4), (a, b + 4), stroke=color, width=1)
    p.f.text((a, b), name, size=size, italic=False, color=color, dy=dy)


# Text markup: function names upright inside italic mathematics. A space next
# to a tspan is a non-breaking space, which every renderer keeps.

def up(s):
    return f'<tspan font-style="normal">{s}</tspan>'


SIN, COS = up('sin'), up('cos')


# The curvature criterion (Lemmas A.2 and A.3).

def curvature():
    t, v, d, kappa = 0.4, 0.6, -0.5, 0.4
    # f = tangent parabola + a convex excess vanishing to second order at t.
    f = lambda x: (v + d * (x - t) + 0.45 * (x - t) ** 2
                   + 0.05 * (x - t) ** 3)
    ddf = lambda x: 0.9 + 0.3 * (x - t)
    l, r = 0.0, 2.0
    assert all(ddf(l + (r - l) * k / 100) >= kappa for k in range(101))
    assert d * d < 2 * kappa * v
    par = lambda x: v + d * (x - t) + kappa / 2 * (x - t) ** 2
    xm = t - d / kappa
    ym = par(xm)
    assert l <= xm <= r and ym > 0
    assert all(par(l + (r - l) * k / 100) <= f(l + (r - l) * k / 100) + 1e-12
               for k in range(101))
    p = Plot(-0.12, 2.3, -0.2, 1.22, 230, 230)
    x_axis(p, -0.1, 2.27, ticks=((l, 'l'), (t, 't'), (r, 'u')), label='x')
    p.line((l, 0), (l, f(l)), stroke=FAINT, width=1, dash='3 3')
    p.line((r, 0), (r, f(r)), stroke=FAINT, width=1, dash='3 3')
    p.line((t, 0), (t, v), stroke=FAINT, width=1, dash='3 3')
    p.curve(par, l, r, stroke=ORANGE, width=2, dash='7 4')
    p.curve(f, l, r, stroke=BLUE, width=2.4)
    p.dot((t, v), fill=INK)
    p.line((xm, 0), (xm, ym), stroke=GREEN, width=2.4)
    p.dot((xm, ym), fill=GREEN)
    p.text((xm, ym / 2), 'f(t) − d(t)²/2κ &gt; 0', size=14,
           anchor='start', color=GREEN, dx=7)
    p.text((1.9, f(1.9)), 'f', size=17, color=BLUE, anchor='end', dx=-8,
           dy=-4)
    p.text((t, v), '(t, f(t))', size=14, anchor='start', dx=8, dy=-12)
    p.text((1.0, par(1.0)), 'tangent parabola', size=13, italic=False,
           color=ORANGE, anchor='end', dy=18)
    p.text((1.0, par(1.0)), 'of curvature' + NB + it('κ') + NB + 'at' + NB
           + it('t'), size=13, italic=False, color=ORANGE, anchor='end',
           dy=34)
    p.save('appendix-a/curvature', 'A function f with second derivative at '
           'least kappa on [l, u] lies above its tangent parabola of curvature '
           'kappa at t, whose lowest value f(t) minus d(t) squared over 2 kappa '
           'is positive')


# Positivity from concavity (Lemmas A.4 and A.5).

def concave():
    alpha, A, B = -0.2, 1.0, 1.0
    F = lambda y: alpha * y + A * math.sin(y) + B * math.cos(y)
    l, r, m = 0.2, 1.4, 0.8
    assert m < F(l) and m < F(r)
    top = math.pi / 2
    p = Plot(-0.1, 1.75, -0.12, 1.42, 250, 250)
    x_axis(p, -0.05, 1.72, ticks=((0, '0'), (l, 'l'), (r, 'u'),
                                  (top, 'π/2')), label='y')
    y_axis(p, -0.05, 1.4, ticks=((m, 'm'), (1, '1')))
    p.line((0, m), (1.66, m), stroke=INK, width=1.2, dash='6 4')
    for x in (l, r):
        p.line((x, 0), (x, F(x)), stroke=FAINT, width=1, dash='3 3')
    p.curve(F, 0, top, stroke=FAINT, width=1.6)
    p.curve(F, l, r, stroke=BLUE, width=2.6)
    p.line((l, F(l)), (r, F(r)), stroke=ORANGE, width=2)
    p.dot((l, F(l)), fill=ORANGE)
    p.dot((r, F(r)), fill=ORANGE)
    p.text((0.75, F(0.75)), 'αy + A' + NB + SIN + NB + 'y + B' + NB + COS
           + NB + 'y', size=14, color=BLUE, dy=-16)
    p.text((0.8, F(l) + (F(r) - F(l)) * (0.8 - l) / (r - l)), 'chord',
           size=13, italic=False, color=ORANGE, dy=14)
    p.save('appendix-a/concave', 'The concave function alpha y plus A sin y '
           'plus B cos y on an interval [l, u] inside [0, pi/2] lies above its '
           'chord, so above any level m below both end values')


# Sine and cosine compared (Lemma A.6).

def sin_cos():
    top = math.pi / 2
    p = Plot(-0.1, 1.72, -0.12, 1.1, 230, 230)
    x_axis(p, -0.05, 1.7, ticks=((0, '0'), (math.pi / 4, 'π/4'),
                                 (math.pi / 3, 'π/3'), (top, 'π/2')),
           label='x')
    y_axis(p, -0.05, 1.08, ticks=((0.5, '½'), (1, '1')))
    p.line((0, 0.5), (math.pi / 3, 0.5), stroke=FAINT, width=1, dash='4 3')
    p.line((math.pi / 3, 0), (math.pi / 3, 0.5), stroke=FAINT, width=1,
           dash='4 3')
    p.line((math.pi / 4, 0), (math.pi / 4, math.sqrt(0.5)), stroke=FAINT,
           width=1, dash='4 3')
    p.curve(math.sin, 0, top, stroke=BLUE, width=2.2)
    p.curve(math.cos, 0, top, stroke=ORANGE, width=2.2)
    p.dot((math.pi / 4, math.sqrt(0.5)))
    p.dot((math.pi / 3, 0.5))
    p.text((1.3, math.sin(1.3)), 'sin', size=15, italic=False, color=BLUE,
           dy=-14)
    p.text((0.3, math.cos(0.3)), 'cos', size=15, italic=False, color=ORANGE,
           dy=-14)
    p.save('appendix-a/sin-cos', 'Sine and cosine on [0, pi/2]: they cross at '
           'pi/4, and the cosine stays at least one half up to pi/3')


# Taylor bounds (Lemma A.7).

def taylor():
    c4 = lambda x: 1 - x ** 2 / 2 + x ** 4 / 24
    c6 = lambda x: c4(x) - x ** 6 / 720
    s5 = lambda x: x - x ** 3 / 6 + x ** 5 / 120
    s7 = lambda x: s5(x) - x ** 7 / 5040
    for k in range(1, 321):
        x = k / 100
        assert c6(x) <= math.cos(x) <= c4(x)
        assert s7(x) <= math.sin(x) <= s5(x)
    X, gap, bottom = 3.2, 0.95, -1.5
    p = Plot(-0.32, 2 * X + gap + 0.36, bottom - 0.3, 1.42, 88, 88)
    panels = ((0.0, math.cos, 'cos', c4, c6, ((2.45, -0.25), (2.55, -1.25)),
               (1.2, 'end', -6, 8)),
              (X + gap, math.sin, 'sin', s5, s7,
               ((2.95, 0.8), (2.95, -0.3)), (1.2, 'end', -6, -8)))
    for off, main, name, up_, low, (pu, pl), (xn, an, dxn, dyn) in panels:
        sh = lambda g, o=off: (lambda x: g(x - o))
        # where the bounds are mostly used
        p.polygon([(off, bottom), (off + PI / 2, bottom), (off + PI / 2, 1.3),
                   (off, 1.3)], fill=GREY, stroke='none', opacity=0.55)
        p.line((off, 0), (off + X + 0.05, 0), stroke=FAINT, width=1)
        x_axis(p, off - 0.05, off + X + 0.3, y=bottom, label='x')
        for x, tick in ((off, '0'), (off + PI / 2, 'π/2'), (off + PI, 'π')):
            vtick(p, x, bottom, tick)
        y_axis(p, bottom, 1.36, x=off,
               ticks=((1, '1'), (0, '0'), (-1, '−1')))
        p.curve(sh(up_), off, off + X, ylim=(-1.3, 1.25), stroke=ORANGE,
                width=1.8, dash='6 3')
        p.curve(sh(low), off, off + X, ylim=(-1.3, 1.25), stroke=GREEN,
                width=1.8, dash='6 3')
        p.curve(sh(main), off, off + X, stroke=BLUE, width=2.4)
        p.text((off + xn, main(xn)), name, size=15, italic=False, color=BLUE,
               anchor=an, dx=dxn, dy=dyn)
        deg_u, deg_l = ('4', '6') if name == 'cos' else ('5', '7')
        p.text((off + pu[0], pu[1]), 'degree ' + deg_u, size=13,
               italic=False, color=ORANGE)
        p.text((off + pl[0], pl[1]), 'degree ' + deg_l, size=13,
               italic=False, color=GREEN)
    p.save('appendix-a/taylor', 'Left: the cosine between its Taylor '
           'polynomials of degrees 6 (below) and 4 (above). Right: the sine '
           'between its Taylor polynomials of degrees 7 (below) and 5 (above). '
           'On the shaded interval [0, pi/2] they cannot be told apart')


# A peak (Lemma A.9).

def peak():
    """Lemma A.9 for f(y) = y^3/3 - y^4/4, whose derivative d(y) = y^2 (1 - y)
    is nonnegative on [l, c] = [-0.35, 1], with a double zero at 0, and
    nonpositive on [c, u] = [1, 1.25]: f is largest at c, although it is not
    concave."""
    l, c, r = -0.35, 1.0, 1.25
    f = lambda y: y ** 3 / 3 - y ** 4 / 4
    d = lambda y: y * y * (1 - y)
    for k in range(401):
        y = l + (r - l) * k / 400
        e = 1e-6
        assert abs((f(y + e) - f(y - e)) / (2 * e) - d(y)) < 1e-8
        assert d(y) >= 0 if y <= c else d(y) <= 0
        assert f(y) <= f(c)
    # f is drawn above, d below, each at its own vertical scale.
    above = lambda y: 1.25 + 15 * f(y)
    below = lambda y: 2.4 * d(y)
    lo, hi = -1.08, 2.78
    pl = Plot(l - 0.2, r + 0.12, lo - 0.3, hi + 0.06, 300, 100)
    pl.polygon([(l, lo), (c, lo), (c, hi), (l, hi)], fill=FILLS[2],
               stroke='none', opacity=0.55)
    pl.polygon([(c, lo), (r, lo), (r, hi), (c, hi)], fill=FILLS[1],
               stroke='none', opacity=0.55)
    for y, name in ((l, 'l'), (c, 'c'), (r, 'u')):
        a, b = pl.q(y, lo)
        pl.f.line((a, b - 4), (a, b + 4), width=1)
        pl.f.text((a, b), name, size=15, dy=15)
    pl.line((l, lo), (r, lo), width=1)
    # Above: f and its value at the peak.
    pl.line((l, above(c)), (r, above(c)), stroke=INK, width=1.3, dash='6 4')
    pl.text((l, above(c)), 'f(c)', size=14, anchor='end', dx=-6)
    pl.curve(above, l, r, stroke=BLUE, width=2.4)
    pl.dot((c, above(c)), fill=BLUE)
    pl.text((-0.2, above(-0.2)), 'f', size=17, color=BLUE, dy=-14)
    # The flat point of f, where d touches zero.
    pl.line((0, 0), (0, above(0)), stroke=FAINT, width=1, dash='3 3')
    pl.dot((0, above(0)), r=2.6, fill=BLUE)
    pl.dot((0, 0), r=2.6, fill=PURPLE)
    # Below: d and its zero line.
    pl.line((l, 0), (r, 0), width=1)
    pl.text((l, 0), '0', size=13, italic=False, anchor='end', dx=-6)
    pl.curve(below, l, r, stroke=PURPLE, width=2.2)
    pl.text((0.62, below(0.62)), 'd', size=17, color=PURPLE, dy=-14)
    pl.text(((l + c) / 2, -0.55), it('d') + NB + '≥ 0', size=14,
            italic=False, color=GREEN)
    pl.text(((c + r) / 2, 0.45), it('d') + NB + '≤ 0', size=14,
            italic=False, color=ORANGE)
    pl.save('appendix-a/peak', 'Lemma A.9 for f(y) = y cubed/3 - y to the '
            'fourth/4 on [-0.35, 1.25]: its derivative d(y) = y squared '
            '(1 - y) is nonnegative up to c = 1, vanishing at 0, and '
            'nonpositive after it, so f stays below its value at c')


# A function concave in each variable on a rectangle (Lemma A.10 (4)).

def rect_f(x, y):
    X, Y = x - 0.5, y - 0.5
    return 1.35 - X * X - Y * Y + 3 * X * Y


def level_runs(level, n=600):
    """The level curve rect_f = level in [0, 1]^2, as runs of points: with
    X = x - 1/2, Y = y - 1/2 it is the conic X^2 + Y^2 - 3XY = 1.35 - level,
    whose two branches are Y = (3X +- sqrt(5X^2 + 4m)) / 2."""
    m = 1.35 - level
    runs = []
    for sign in (1, -1):
        run = []
        for k in range(n + 1):
            X = -0.5 + k / n
            disc = 5 * X * X + 4 * m
            Y = (3 * X + sign * math.sqrt(disc)) / 2 if disc >= 0 else None
            if Y is not None and abs(Y) <= 0.5:
                run.append((X + 0.5, Y + 0.5))
            elif run:
                runs.append(run)
                run = []
        if run:
            runs.append(run)
    return [r for r in runs if len(r) > 1]


def rectangle():
    """Lemma A.10 (4) for f(x, y) = 27/20 - X^2 - Y^2 + 3XY on [0, 1]^2,
    X = x - 1/2, Y = y - 1/2: concave in x and in y, not concave (a saddle
    at the centre), positive at the corners and so on the whole square."""
    corners = {(0, 0): 1.6, (1, 1): 1.6, (0, 1): 0.1, (1, 0): 0.1}
    for (x, y), val in corners.items():
        assert abs(rect_f(x, y) - val) < 1e-12
    grid = [rect_f(i / 60, j / 60) for i in range(61) for j in range(61)]
    assert min(grid) >= 0.1 - 1e-12
    y0, xs, dx = 0.7, 0.62, 1.72
    f = Figure(-0.36, dx + 1.2, -0.25, 1.15, 210)
    # Left: the square with level curves.
    f.polygon([(0, 0), (1, 0), (1, 1), (0, 1)], fill=FILLS[0], stroke='none',
              opacity=0.45)
    for lev in (0.25, 0.5, 0.75, 1.0, 1.25, 1.5):
        for run in level_runs(lev):
            fpoly(f, run, stroke=FAINT, width=1)
    for lev, target in ((1.0, (0.7, 0.2)), (1.5, (0.15, 0.1))):
        pts = [q for run in level_runs(lev) for q in run]
        x, y = min(pts, key=lambda q: math.hypot(q[0] - target[0],
                                                 q[1] - target[1]))
        word(f, (x + 0.035, y), f'{lev:g}', size=12, color=INK,
             anchor='start')
    f.line((0, 0), (1, 0), stroke=INK, width=1.2)
    f.line((0, 1), (1, 1), stroke=INK, width=1.2)
    f.line((0, 0), (0, 1), stroke=BLUE, width=3)
    f.line((1, 0), (1, 1), stroke=BLUE, width=3)
    f.line((0, y0), (1, y0), stroke=ORANGE, width=2, dash='6 4')
    for (x, y), val in corners.items():
        f.dot((x, y), r=3.8, fill=INK)
        word(f, (x + (0.06 if x else -0.06), y + (0.05 if y else -0.05)),
             f'{val:g}', size=13, anchor='start' if x else 'end')
    for x in (0, 1):
        f.dot((x, y0), r=3.4, fill=ORANGE)
    f.dot((xs, y0), r=3.4, fill=INK)
    f.text((xs, y0 + 0.07), '(x, y)', size=14)
    f.text((-0.05, 0.5), 'x = l', size=14, anchor='end')
    f.text((1.05, 0.5), 'x = u', size=14, anchor='start')
    f.text((0.5, -0.08), 'y = L', size=14)
    f.text((0.5, 1.07), 'y = U', size=14)
    # Right: f along the segment, above its chord.
    g = lambda x: rect_f(x, y0)
    p = Graph(f, 1.0, 0.62, x0=0.0, y0=0.0, dx=dx, dy=0.0)
    p.x_axis(0, 1.1, ticks=((0, ''), (1, '')), label='')
    p.y_axis(0, 1.55, ticks=((0, '0'), (g(0), f'{g(0):.2f}'),
                             (g(1), f'{g(1):.2f}')))
    for x, name in ((0, 'l'), (1, 'u')):
        p.text((x, 0), name, size=15, dy=16)
    p.text((1.1, 0), 'x', size=15, anchor='end', dy=-11)
    p.line((0, g(0)), (1, g(1)), stroke=ORANGE, width=1.8, dash='6 4')
    p.curve(g, 0, 1, stroke=BLUE, width=2.6)
    for x in (0, 1):
        p.dot((x, g(x)), r=3.4, fill=ORANGE)
    p.dot((xs, g(xs)), r=3.4, fill=INK)
    p.text((0.5, 1.5), 'f(x, y) for y = 0.7', size=14)
    save_a(f, 'rectangle', 'Left: the square [l, u] by [L, U] = [0, 1] by '
           '[0, 1] with level curves of f(x, y) = 27/20 - (x - 1/2)^2 - '
           '(y - 1/2)^2 + 3(x - 1/2)(y - 1/2), a saddle; f is 1.6 at two '
           'corners and 0.1 at the other two; its vertical edges are drawn '
           'thick blue and a dashed orange segment at height 0.7 joins them. '
           'Right: f along that segment, a concave arc above its dashed chord, '
           'from 0.76 to 1.36')


# A first harmonic (Lemma A.11).

def harmonic():
    f = Figure(-0.25, 3.45, -1.55, 1.75, 92)
    A, B = 0.6, 0.8
    H = lambda x: A * math.cos(x) + B * math.sin(x)
    p = Graph(f, 0.5, 1.15, x0=-PI, y0=0.0, dx=0.0, dy=0.0)
    p.x_axis(-PI, PI + 0.25, ticks=((-PI, '−π'), (-PI / 2, '−π/2'),
                                    (0, '0'), (PI / 2, 'π/2'), (PI, 'π')),
             label='x')
    z0 = math.atan2(-A, B)            # H(z0) = 0, H rising there
    z1 = z0 + PI
    xs = [-PI + 2 * PI * k / 400 for k in range(401)]
    p.polyline([(x, H(x)) for x in xs if x <= z0], stroke=FAINT, width=2)
    p.polyline([(x, H(x)) for x in xs if x >= z1], stroke=FAINT, width=2)
    p.polyline([(x, H(x)) for x in xs if z0 <= x <= z1], stroke=BLUE,
               width=2.6)
    l, r = z0 + 0.35, z1 - 0.6
    p.line((l, H(l)), (r, H(r)), stroke=ORANGE, width=1.8, dash='6 4')
    for x in (l, r):
        p.dot((x, H(x)), r=3.4, fill=ORANGE)
    p.text((0.75, 1.12), it('H') + NB + '≥ 0: concave', size=13,
           italic=False, color=BLUE, anchor='start')
    p.text((-2.21, -1.22), it('H') + NB + '&lt; 0: convex', size=13,
           italic=False, color=FAINT)
    p.text((-PI, 1.45), 'H(x) = 0.6' + NB + COS + NB + 'x + 0.8' + NB + SIN
           + NB + 'x', size=14, anchor='start')
    save_a(f, 'harmonic', 'The first harmonic H(x) = 0.6 cos x + 0.8 sin x '
           'on minus pi to pi, concave and drawn in blue where it is '
           'nonnegative, convex and grey where it is negative, with a dashed '
           'chord below the blue arc')


# A turning vector (Lemma A.13).

def turning():
    """Lemma A.13 for a = 2/5 and b = 1: Lambda(x) = 29/25 + 4/5 cos x, the
    squared length of (a, 0) + b u(x)."""
    a, b = 0.4, 1.0
    L = lambda x: math.sqrt(a * a + b * b + 2 * a * b * math.cos(x))
    k = a * b / (a + b)
    xc = math.acos(-a / b)           # L = sqrt(b^2 - a^2) there
    assert abs(L(xc) - math.sqrt(b * b - a * a)) < 1e-12
    for j in range(1, 400):
        x = -PI + 2 * PI * j / 400
        e = 1e-4
        d2 = (L(x + e) - 2 * L(x) + L(x - e)) / e ** 2
        assert d2 >= -k - 1e-6                      # (2)
        assert (d2 >= -1e-6) == (abs(x) >= xc) or abs(abs(x) - xc) < 0.02
        assert L(x) >= a + b - k * x * x / 2 - 1e-12  # Lemma A.2
    f = Figure(-0.78, 4.62, -1.2, 1.28, 125)
    # Left: the vectors.
    A = (a, 0.0)
    f.circle(A, b, stroke=FAINT, width=1.2, dash='5 4')
    f.line((0, -1.14), (0, 1.14), stroke=FAINT, width=1, dash='2 3')
    near = [shift(A, u(t), b) for t in
            [xc + (2 * PI - 2 * xc) * j / 120 for j in range(121)]]
    fpoly(f, near, stroke=ORANGE, width=3.2)
    x = 2.25
    P = shift(A, u(x), b)
    assert P[0] < 0
    f.line((0, 0), P, stroke=INK, width=2.6)
    arrow(f, (0, 0), A, color=INK, width=1.8, size=10)
    arrow(f, A, P, color=BLUE, width=1.8, size=10)
    f.line(A, shift(A, (1.0, 0.0), 0.34), stroke=FAINT, width=1)
    thin_arc(f, A, 0.18, 0, x, color=INK, width=1.1)
    f.text(shift(A, u(x / 2), 0.27), 'x', size=15)
    f.dot((0, 0), r=3)
    f.text((-0.04, -0.09), 'o', size=15, anchor='end')
    f.text((a / 2, -0.1), 'a', size=15)
    f.text(shift(A, u(x), 0.55 * b), 'b', size=15, color=BLUE, dx=10, dy=-4)
    f.text((P[0] / 2, P[1] / 2), 'L', size=15, dx=-11)
    # Right: the length L(x).
    g = Graph(f, 0.36, 1.75, x0=-PI, y0=0.45, dx=2.12, dy=-0.95)
    for lev in (a + b, b - a, math.sqrt(b * b - a * a)):
        g.line((-PI, lev), (PI, lev), stroke=FAINT, width=1, dash='4 3')
    g.x_axis(-PI, PI + 0.4, y=0.45, ticks=((-PI, '−π'), (0, '0'), (PI, 'π')),
             label='x')
    g.y_axis(0.45, 1.55, x=-PI, ticks=(
        (a + b, it('a') + NB + '+' + NB + it('b')),
        (math.sqrt(b * b - a * a),
         '√(' + it('b') + '²' + NB + '−' + NB + it('a') + '²)'),
        (b - a, it('b') + NB + '−' + NB + it('a'))))
    par = lambda x: a + b - k * x * x / 2
    xp = math.sqrt(2 * (a + b - 0.5) / k)
    g.curve(par, -xp, xp, stroke=GREEN, width=1.8, dash='7 4')
    xs = [-PI + 2 * PI * j / 400 for j in range(401)]
    g.polyline([(x, L(x)) for x in xs if x <= -xc], stroke=ORANGE, width=3)
    g.polyline([(x, L(x)) for x in xs if x >= xc], stroke=ORANGE, width=3)
    g.polyline([(x, L(x)) for x in xs if -xc <= x <= xc], stroke=BLUE,
               width=2.6)
    g.dot((0, a + b), r=3.4, fill=INK)
    g.text((0.95, L(0.95)), 'L(x)', size=15, color=BLUE, anchor='start',
           dx=8, dy=-6)
    g.text((-1.0, par(-1.0)), '(2)', size=13, italic=False, color=GREEN,
           anchor='end', dx=-12)
    g.text((2.75, L(2.75)), '(3)', size=13, italic=False, color=ORANGE,
           dy=-14)
    save_a(f, 'turning', 'Left: from o, a constant vector of length a = 2/5 '
           'and, from its tip, a vector of length b = 1 turned by the angle '
           'x; the tip of their sum runs on the dashed circle of radius b, '
           'and its distance L from o is drawn thick. The part of the circle '
           'behind the dotted line through o perpendicular to the constant '
           'vector is orange. Right: L as a function of x on minus pi to pi, '
           'between b - a and a + b, with its peak touched from below by a '
           'dashed green parabola, and orange where L is at most the square '
           'root of b squared minus a squared')


# The tangents of the square root (Lemma A.14).

def root():
    f = Figure(-0.42, 3.62, -0.3, 2.78, 92)
    c = 0.4
    q = Graph(f, 9.0, 4.4, x0=0.0, y0=0.0, dx=0.0, dy=0.0)
    q.x_axis(0, 0.36, ticks=((0.1, '0.1'), (c * c, it('c') + '² = 0.16'),
                             (0.3, '0.3')), label='y')
    q.y_axis(0, 0.66, ticks=((0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6')))
    q.curve(math.sqrt, 0, 0.34, stroke=BLUE, width=2.6)
    q.curve(lambda y: (y + c * c) / (2 * c), 0, 0.34, stroke=ORANGE,
            width=2, dash='7 4')
    q.dot((c * c, c), r=3.6, fill=INK)
    q.line((c * c, 0), (c * c, c), stroke=FAINT, width=1, dash='3 3')
    q.text((0.215, 0.615), '(y + c²)/2c', size=14, color=ORANGE,
           anchor='start')
    q.text((0.245, 0.43), '√y', size=15, color=BLUE, anchor='start')
    save_a(f, 'root', 'The square root of y and its tangent line at y = c '
           'squared = 0.16, which lies above it and touches it there')


# Small angles (Lemma A.15).

def small_angles():
    om = lambda t: 0.5 * (abs(math.cos(t)) + abs(math.sin(t)))
    lo = lambda t: 0.5 * (math.cos(t) + math.sin(t))
    for j in range(801):
        t = -PI + 2 * PI * j / 800
        assert om(t) >= 0.5 - 1e-12 and om(t) >= lo(t) - 1e-12
        for s in (-t, PI + t, PI / 2 + t, PI / 2 - t):
            assert abs(om(s) - om(t)) < 1e-12
        assert math.cos(t) <= 1 - t * t / 5 + 1e-12
    f = Figure(-0.62, 6.5, -1.42, 1.1, 100)
    # Left: the width and its lower bounds.
    g = Graph(f, 0.45, 1.25, x0=-PI, y0=0.0, dx=0.0, dy=0.0)
    g.x_axis(-PI, PI + 0.4, ticks=((-PI, '−π'), (-PI / 2, '−π/2'), (0, '0'),
                                    (PI / 2, 'π/2'), (PI, 'π')), label='t')
    g.line((-PI, 0.5), (PI, 0.5), stroke=INK, width=1.1, dash='5 4')
    g.text((-PI, 0.5), '½', size=13, italic=False, anchor='end', dx=-6)
    g.curve(om, -PI, PI, n=800, stroke=BLUE, width=2.4)
    g.curve(lo, -PI, PI, n=400, stroke=ORANGE, width=1.8, dash='7 4')
    g.text((-2.3, om(-2.3)), 'ω(t)', size=15, color=BLUE, dy=-15)
    g.text((-2.05, lo(-2.05)), '½(' + COS + NB + 't + ' + SIN + NB + 't)',
           size=13, color=ORANGE, anchor='start', dx=8, dy=6)
    # Right: the cosine between two parabolas.
    h = Graph(f, 0.45, 0.62, x0=-PI, y0=0.0, dx=3.45, dy=0.0)
    h.x_axis(-PI, PI + 0.4, ticks=((-PI, '−π'), (0, '0'), (PI, 'π')),
             label='t')
    for y, name in ((1, '1'), (-1, '−1')):
        h.line((-PI, y), (PI, y), stroke=FAINT, width=0.8, dash='2 3')
        h.text((-PI, y), name, size=13, italic=False, anchor='end', dx=-6)
    h.curve(lambda t: 1 - t * t / 5, -PI, PI, stroke=ORANGE, width=1.8,
            dash='7 4')
    lim = math.sqrt(2 * 2.3)
    h.curve(lambda t: 1 - t * t / 2, -lim, lim, stroke=GREEN, width=1.8,
            dash='7 4')
    h.curve(math.cos, -PI, PI, stroke=BLUE, width=2.4)
    for j, (name, color, dash) in enumerate(
            ((COS + NB + 't', BLUE, None), ('1 − t²/5', ORANGE, '7 4'),
             ('1 − t²/2', GREEN, '7 4'))):
        x0 = 3.45 + 0.98 * j
        f.line((x0, -1.2), (x0 + 0.28, -1.2), stroke=color,
               width=2.4 if dash is None else 1.8, dash=dash)
        f.text((x0 + 0.36, -1.2), name, size=14, anchor='start')
    save_a(f, 'small-angles', 'Left: the width omega(t), half the sum of '
           'the absolute values of cos t and sin t, on minus pi to pi: a '
           'curve of period pi/2 between one half and the square root of 2 '
           'over 2, above the dashed level one half and above the dashed '
           'curve (cos t + sin t)/2, which it meets on [0, pi/2]. Right: cos t '
           'on minus pi to pi between the parabolas 1 - t^2/2 below and '
           '1 - t^2/5 above; all three meet at 0, and at plus and minus pi '
           'the upper parabola passes just above -1')


# Half angles (Lemma A.16).

def half_angles():
    t = 0.8
    T = math.sin(t) / (1 + math.cos(t))
    assert abs(T - math.tan(t / 2)) < 1e-12
    ratio = lambda s: math.tan(s / 2) / s
    for j in range(1, 401):
        s = 0.8 * j / 400
        assert 0.5 <= ratio(s) <= 0.55
    f = Figure(-1.22, 4.29, -0.42, 1.32, 145)
    # Left: the unit circle and the chord from (-1, 0).
    E, F0, P = (-1.0, 0.0), (1.0, 0.0), u(t)
    Q = (P[0], 0.0)
    thin_arc(f, (0, 0), 1.0, 0, PI, color=FAINT, width=1.2)
    f.line((-1.12, 0), (1.15, 0), stroke=INK, width=1)
    f.line((0, -0.06), (0, 1.12), stroke=FAINT, width=1, dash='2 3')
    f.line(E, P, stroke=BLUE, width=2)
    f.line(P, F0, stroke=ORANGE, width=2)
    f.line((0, 0), P, stroke=FAINT, width=1.2)
    f.line(Q, P, stroke=INK, width=1.2, dash='4 3')
    # the right angle at P (Thales)
    e1 = ((E[0] - P[0]), (E[1] - P[1]))
    e2 = ((F0[0] - P[0]), (F0[1] - P[1]))
    n1, n2 = math.hypot(*e1), math.hypot(*e2)
    assert abs(e1[0] * e2[0] + e1[1] * e2[1]) < 1e-12
    s = 0.07
    c1 = shift(P, (e1[0] / n1, e1[1] / n1), s)
    c2 = shift(P, (e2[0] / n2, e2[1] / n2), s)
    fpoly(f, [c1, shift(c1, (e2[0] / n2, e2[1] / n2), s), c2], stroke=INK,
          width=1)
    thin_arc(f, (0, 0), 0.2, 0, t, color=INK, width=1.1)
    f.text(shift((0, 0), u(t / 2), 0.29), 't', size=15)
    thin_arc(f, E, 0.36, 0, t / 2, color=INK, width=1.1)
    f.text(shift(E, u(t / 4), 0.47), 't/2', size=14)
    f.line((0, 0), (0, T), stroke=GREEN, width=3)
    f.dot((0, T), r=3.4, fill=GREEN)
    f.text((0, T), up('tan') + '(t/2)', size=14, color=GREEN, anchor='end',
           dx=-8, dy=-10)
    f.text((P[0], P[1] / 2), SIN + NB + 't', size=14, anchor='end', dx=-6)
    for pt, name in ((E, '−1'), (F0, '1')):
        word(f, shift(pt, (0, -0.11)), name, size=13)
    f.dot((0, 0), r=2.8)
    f.text((0.02, -0.1), 'o', size=14, anchor='start')
    f.dot(P, r=3.2)
    f.text(P, 'u(t)', size=14, anchor='start', dx=6, dy=-10)
    # Right: tan(t/2)/t between 1/2 and 11/20.
    g = Graph(f, 2.6, 22.0, x0=0.0, y0=0.49, dx=1.75, dy=-0.15)
    g.x_axis(0, 0.88, y=0.49, ticks=((0, '0'), (0.4, '2/5'), (0.8, '4/5')),
             label='t')
    g.y_axis(0.49, 0.555, ticks=((0.5, '½'), (0.55, '11/20')))
    g.line((0, 0.55), (0.8, 0.55), stroke=ORANGE, width=1.6, dash='6 4')
    g.line((0, 0.5), (0.8, 0.5), stroke=ORANGE, width=1.6, dash='6 4')
    g.curve(ratio, 0.002, 0.8, stroke=BLUE, width=2.6)
    g.line((0.8, 0.49), (0.8, ratio(0.8)), stroke=FAINT, width=1, dash='3 3')
    g.text((0.3, ratio(0.3)), up('tan') + '(t/2)' + NB + '/' + NB + 't',
           size=14, color=BLUE, dy=-16)
    save_a(f, 'half-angles', 'Left: the upper half of the unit circle about '
           'o with the point u(t) for t = 4/5; the chord from (-1, 0) to u(t), '
           'blue, makes the angle t/2 with the axis and crosses the vertical '
           'line through o at the height tan(t/2), marked green; the chord '
           'from u(t) to (1, 0), orange, is perpendicular to it. Right: '
           'tan(t/2)/t for t from 0 to 4/5, rising from one half and staying '
           'below 11/20, both levels dashed')


def save_a(f, name, title):
    """Save a figure of this appendix, in its directory."""
    f.save('appendix-a/' + name, title)


def main():
    curvature()
    concave()
    sin_cos()
    taylor()
    peak()
    rectangle()
    harmonic()
    turning()
    root()
    small_angles()
    half_angles()


if __name__ == '__main__':
    main()

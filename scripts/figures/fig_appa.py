#!/usr/bin/env python3
"""Draw the figures of Appendix A (docs/proof/appendix-a.md).

    python3 scripts/figures/fig_appa.py

Every curve is sampled from the function it shows, and every point is
computed from the formulas of the appendix.
"""
import math

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb, shift, u

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
HALF_WIDTH = 801 / 1600
TARGET = 13 / 4


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
    p.text((1.0, par(1.0)), 'of curvature κ at t', size=13, italic=False,
           color=ORANGE, anchor='end', dy=34)
    p.save('appa-curvature', 'A function f with second derivative at least '
           'kappa on [l, u] lies above its tangent parabola of curvature kappa '
           'at t, whose lowest value f(t) minus d(t) squared over 2 kappa is '
           'positive')


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
    p.text((0.75, F(0.75)), 'αy + A sin y + B cos y', size=14,
           color=BLUE, dy=-16)
    p.text((0.8, F(l) + (F(r) - F(l)) * (0.8 - l) / (r - l)), 'chord',
           size=13, italic=False, color=ORANGE, dy=14)
    p.save('appa-concave', 'The concave function alpha y plus A sin y plus B '
           'cos y on an interval [l, u] inside [0, pi/2] lies above its chord, '
           'so above any level m below both end values')


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
    p.save('appa-sin-cos', 'Sine and cosine on [0, pi/2]: they cross at pi/4, '
           'and the cosine stays at least one half up to pi/3')


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
    X, gap = 3.2, 0.85
    ylim = (-1.3, 1.25)
    p = Plot(-0.25, 2 * X + gap + 0.3, -1.42, 1.38, 80, 80)
    for off, main, name, up, low, nu, nl in (
            (0.0, math.cos, 'cos', c4, c6, 'degree 4', 'degree 6'),
            (X + gap, math.sin, 'sin', s5, s7, 'degree 5', 'degree 7')):
        sh = lambda g, o=off: (lambda x: g(x - o))
        p.line((off, -1.3), (off, 1.3), width=1, arrow=True)
        x_axis(p, off - 0.05, off + X + 0.28, ticks=(
            (off + math.pi / 2, 'π/2'), (off + 3, '3')), label='x')
        for y, s in ((1, '1'), (-1, '−1')):
            a, b = p.q(off, y)
            p.f.line((a - 4, b), (a + 4, b), width=1)
            p.f.text((a, b), s, size=13, italic=False, anchor='end', dx=-7)
        p.curve(sh(up), off, off + X, ylim=ylim, stroke=ORANGE, width=1.8,
                dash='6 3')
        p.curve(sh(low), off, off + X, ylim=ylim, stroke=GREEN, width=1.8,
                dash='6 3')
        p.curve(sh(main), off, off + X, stroke=BLUE, width=2.4)
        p.text((off + 1.2, main(1.2)), name, size=15, italic=False,
               color=BLUE, anchor='end', dx=-6, dy=-8 if name == 'sin' else 8)
        if name == 'cos':
            p.text((off + 2.75, up(2.75)), nu, size=13, italic=False,
                   color=ORANGE, anchor='end', dx=-8, dy=-6)
            p.text((off + 2.95, low(2.95)), nl, size=13, italic=False,
                   color=GREEN, anchor='end', dx=-10, dy=8)
        else:
            p.text((off + X, up(X)), nu, size=13, italic=False,
                   color=ORANGE, anchor='end', dx=-2, dy=-14)
            p.text((off + X, low(X)), nl, size=13, italic=False,
                   color=GREEN, anchor='end', dx=-4, dy=16)
    p.save('appa-taylor', 'Left: the cosine between its Taylor polynomials of '
           'degrees 6 (below) and 4 (above). Right: the sine between its '
           'Taylor polynomials of degrees 7 (below) and 5 (above). The bounds '
           'hold on [0, infinity) and are tight near 0')


# The Bernstein basis (Definition A.9).

def bernstein_basis():
    n = 4
    p = Plot(-0.12, 1.12, -0.16, 1.12, 380, 250)
    x_axis(p, -0.05, 1.1, ticks=((0, 'l'), (1, 'u')), label='x')
    y_axis(p, 0, 1.1, ticks=((1, '1'),))
    p.line((0, 1), (1, 1), stroke=FAINT, width=1.4, dash='6 4')
    for i in range(n + 1):
        b = lambda x, i=i: math.comb(n, i) * x ** i * (1 - x) ** (n - i)
        p.curve(b, 0, 1, stroke=COLORS[i], width=2.2)
        if i == 0:
            p.text((0.1, b(0.1)), sb('b', '4,0', size=15), size=15,
                   color=COLORS[i], anchor='start', dx=8, dy=-4)
        elif i == n:
            p.text((0.9, b(0.9)), sb('b', '4,4', size=15), size=15,
                   color=COLORS[i], anchor='end', dx=-8, dy=-4)
        else:
            p.text((i / n, b(i / n)), sb('b', f'4,{i}', size=15), size=15,
                   color=COLORS[i], dy=-14)
    p.text((0.5, 1), 'the sum is 1', size=13, italic=False, color=FAINT,
           dy=-11)
    p.save('appa-bernstein-basis', 'The five Bernstein basis polynomials of '
           'degree 4 on an interval [l, u]: they are nonnegative there and add '
           'up to 1')


# The marker arc in the chart (section A.4).

def label(a, uu):
    side = math.pi / 6 + (uu - 0.5) / 3 + 3 * (1 - a) / 4
    return min(1.25 * uu, side, math.pi / 4)


def admissible(a, uu):
    return 0.5 <= a and 0 <= uu <= a and (a + 0.5) ** 2 + (uu + 0.5) ** 2 <= TARGET


def marker_arc():
    states = [(1.0, 0.5, '(1, ½)'), (0.9, 0.3, '(0.9, 0.3)')]
    panel = 2.15
    f = Figure(-0.3, panel + 1.72, -1.02, 1.3, 150)
    for k, (a, uu, name) in enumerate(states):
        assert admissible(a, uu)
        o = (k * panel, 0.0)
        ell = label(a, uu)
        lo, hi = ell - HALF_WIDTH, ell + HALF_WIDTH
        # The part of the circle in the closed square, and the arc inside it.
        enter = max(math.asin(uu - 0.5), -math.acos(a - 0.5))
        leave = min(math.acos(a - 0.5), math.asin(min(1.0, uu + 0.5)))
        assert enter < lo and hi < leave
        for j in range(201):
            t = lo + (hi - lo) * j / 200
            assert abs(math.cos(t) - a) <= 0.5 and abs(math.sin(t) - uu) <= 0.5
        c = shift(o, (a, uu))
        f.line(shift(o, (-0.25, 0)), shift(o, (1.7, 0)), stroke=FAINT, width=1)
        f.text(shift(o, (1.7, 0)), 't = 0', size=12, italic=False,
               anchor='end', color=FAINT, dy=11)
        f.square(c, fill=FILLS[0], stroke=BLUE)
        for x0, y0, x1, y1 in ((a - 0.5, -0.98, a - 0.5, 1.12),
                               (a + 0.5, -0.98, a + 0.5, 1.12),
                               (-0.25, uu - 0.5, 1.7, uu - 0.5),
                               (-0.25, uu + 0.5, 1.7, uu + 0.5)):
            f.line(shift(o, (x0, y0)), shift(o, (x1, y1)), width=1, dash='4 4')
        f.text(shift(o, (a - 0.5, -0.98)), 'near', size=12, italic=False,
               anchor='end', dx=-4, dy=4)
        f.text(shift(o, (a + 0.5, -0.98)), 'far', size=12, italic=False,
               anchor='start', dx=4, dy=4)
        f.text(shift(o, (-0.25, uu - 0.5)), 'lower', size=12, italic=False,
               anchor='start', dy=-9)
        f.text(shift(o, (-0.25, uu + 0.5)), 'upper', size=12, italic=False,
               anchor='start', dy=-9)
        f.arc(o, 1.0, -math.pi / 2 - 0.05, math.pi / 2 + 0.3, FAINT,
              width=1.2)
        f.arc(o, 1.0, enter, leave, BLUE, width=2)
        f.arc(o, 1.0, lo, hi, ORANGE, width=5)
        for t in (enter, leave):
            f.dot(shift(o, u(t), 1.0), r=3.4, fill=BLUE)
        f.line(o, shift(o, u(ell), 1.22), width=1, dash='3 3', arrow=True)
        f.text(shift(o, u(ell), 1.3), 'ℓ', size=16)
        for t in (lo, hi):
            f.line(o, shift(o, u(t), 1.0), stroke=ORANGE, width=1)
        f.arc(o, 0.3, ell, hi, INK, width=1.2)
        f.dot(c, fill=BLUE)
        f.text(shift(o, (a, uu + 0.5)), '(a, u) = ' + name, size=13,
               color=BLUE, dy=-10)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.07)), 'o', anchor='end')
        f.text(shift(o, (-0.16, -0.92)), sb('Γ', '1', size=16), size=16,
               color=FAINT)
    f.save('appa-marker-arc', 'Two admissible squares in their charts, with '
           'the lines of their four edges and the arc of the unit circle of '
           'half-width 801/1600 about the label; left the side state (1, 1/2), '
           'whose arc nearly fills the part of the circle inside the square, '
           'right the state (0.9, 0.3), with an axial label')


def admissible_region():
    root = math.sqrt(TARGET)
    corner = math.sqrt(TARGET / 2) - 0.5
    t0, t1 = math.atan2(0.5, math.sqrt(3)), math.pi / 4
    arc = [(-0.5 + root * math.cos(t0 + (t1 - t0) * k / 80),
            -0.5 + root * math.sin(t0 + (t1 - t0) * k / 80))
           for k in range(81)]
    region = [(0.5, 0.0)] + arc + [(0.5, 0.5)]
    assert abs(arc[-1][0] - corner) < 1e-12
    for a, uu in region:
        assert (a + 0.5) ** 2 + (uu + 0.5) ** 2 <= TARGET + 1e-9
    # The line of the Cauchy-Schwarz bound, 3/4 (a + 1/2) + 2/3 (u + 1/2)
    # = 2171/1200, and its nearest point to the disk.
    L = 2171 / 1200
    norm = math.hypot(0.75, 2 / 3)
    touch = (-0.5 + root * 0.75 / norm, -0.5 + root * (2 / 3) / norm)
    assert 0.75 * (touch[0] + 0.5) + (2 / 3) * (touch[1] + 0.5) < L
    line_u = lambda a: (L - 0.75 * (a + 0.5)) / (2 / 3) - 0.5
    x = 0.4
    top = math.sqrt(TARGET - (x + 1) ** 2) - 0.5
    p = Plot(0.3, 1.42, -0.1, 0.98, 330, 330)
    x_axis(p, 0.35, 1.4, ticks=((0.5, '½'), (1, '1'), (math.sqrt(3) - 0.5,
                                                       '√3 − ½')), label='a')
    y_axis(p, -0.02, 0.96, x=0.35, ticks=((0.5, '½'),), label='u')
    p.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    p.curve(lambda a: math.sqrt(max(0.0, TARGET - (a + 0.5) ** 2)) - 0.5,
            0.36, math.sqrt(3) - 0.5, ylim=(-0.02, 0.96), stroke=BLUE,
            width=1, dash='4 3')
    p.line((0.62, line_u(0.62)), (1.12, line_u(1.12)), stroke=ORANGE,
           width=1.6)
    p.dot(touch, fill=ORANGE)
    p.line((x + 0.5, 0), (x + 0.5, top), stroke=GREEN, width=2.4)
    p.dot((x + 0.5, top), fill=GREEN)
    p.dot((1.0, 0.5), fill=INK)
    p.text((1.0, 0.5), '(1, ½)', size=13, italic=False, anchor='start',
           dx=7, dy=4)
    p.text((1.17, 0.26), 'φ = 13/4', size=13, color=BLUE, anchor='start')
    p.text((0.7, line_u(0.7)), 'Cauchy–Schwarz', size=13, italic=False,
           color=ORANGE, anchor='start', dx=10, dy=-6)
    p.text((x + 0.5, top / 2), 'a = x + ½', size=13, color=GREEN,
           anchor='end', dx=-6)
    p.text((0.66, 0.2), 'admissible', size=13, italic=False, color=BLUE)
    p.save('appa-admissible', 'The admissible states in the (a, u)-plane: '
           'a at least 1/2, u between 0 and a, and phi at most 13/4. The line '
           'of the Cauchy-Schwarz bound passes just outside the disk, and at '
           'a = x + 1/2 the circle bounds u')


# A line against the arcsine (Lemma A.11).

def asin_line():
    g = lambda y: 1.25 * y - math.asin(max(-1.0, min(1.0, y)))
    p = Plot(-1.12, 1.18, -0.42, 0.4, 220, 480)
    # The ranges used by the two transverse edges.
    y1, y2 = -0.5, 11 / 40
    p.polygon([(y1, -0.35), (y2, -0.35), (y2, 0.35), (y1, 0.35)],
              fill=FILLS[1], stroke='none', opacity=0.55)
    p.polygon([(0.5, -0.35), (1, -0.35), (1, 0.35), (0.5, 0.35)],
              fill=FILLS[2], stroke='none', opacity=0.55)
    x_axis(p, -1.08, 1.15, ticks=((-1, '−1'), (-0.6, '−3/5'), (-0.5, ''),
                                  (0.6, '3/5'), (1, '1')), label='y')
    p.line((0, -0.38), (0, 0.38), width=1, arrow=True)
    p.line((y1, g(y1)), (y2, g(y1)), stroke=ORANGE, width=1.4, dash='5 3')
    p.line((0.5, g(0.6)), (1, g(0.6)), stroke=GREEN, width=1.4, dash='5 3')
    p.curve(g, -1, 1, n=800, stroke=BLUE, width=2.4)
    p.dot((y1, g(y1)), fill=ORANGE)
    p.dot((0.6, g(0.6)), fill=GREEN)
    p.dot((-0.6, g(-0.6)), fill=BLUE)
    p.text((y1, g(y1)), 'π/6 − 5/8', size=13, italic=False, color=ORANGE,
           anchor='end', dx=-6, dy=14)
    p.text((0.6, g(0.6)), '3/4 − arcsin 3/5', size=13, italic=False,
           color=GREEN, dy=-13)
    p.text((-0.12, 0.3), 'lower edge', size=12, italic=False, color=ORANGE)
    p.text((0.75, -0.3), 'upper edge', size=12, italic=False, color=GREEN)
    p.text((-0.95, g(-0.95)), 'g', size=17, color=BLUE, anchor='start',
           dx=8, dy=-6)
    p.save('appa-asin-line', 'The function g(y) = 5/4 y minus arcsin y on '
           '[-1, 1]: it increases on [-3/5, 3/5] and decreases on [3/5, 1]. '
           'On the range of the lower edge it stays above its value at -1/2; '
           'on the range of the upper edge it stays below its value at 3/5')


# The label between the transverse edges (Lemmas A.12 and A.13).

def transverse():
    umax = math.sqrt(TARGET / 2) - 0.5

    def amax(uu):
        return math.sqrt(TARGET - (uu + 0.5) ** 2) - 0.5

    n = 400
    us = [umax * k / n for k in range(n + 1)]
    low = [label(amax(uu), uu) for uu in us]
    high = [label(max(0.5, uu), uu) for uu in us]
    lower_edge = lambda uu: math.asin(uu - 0.5) + HALF_WIDTH
    upper_edge = lambda uu: math.asin(min(1.0, uu + 0.5)) - HALF_WIDTH
    # Lemmas A.12 and A.13 on a grid of admissible states.
    for i in range(0, n + 1, 4):
        uu = us[i]
        for j in range(41):
            a = max(0.5, uu) + (amax(uu) - max(0.5, uu)) * j / 40
            if admissible(a, uu):
                assert lower_edge(uu) < label(a, uu)
                if uu <= 0.5:
                    assert label(a, uu) < upper_edge(uu)
    p = Plot(-0.08, 0.86, -0.16, 1.16, 440, 300)
    x_axis(p, -0.03, 0.84, ticks=((0, '0'), (0.5, '½'), (0.775, '31/40')),
           label='u')
    y_axis(p, -0.12, 1.14, ticks=((math.pi / 4, 'π/4'), (math.pi / 6, 'π/6')))
    for y in (math.pi / 4, math.pi / 6):
        p.line((0, y), (0.8, y), stroke=FAINT, width=1, dash='3 3')
    p.polygon(list(zip(us, low)) + list(zip(reversed(us), reversed(high))),
              fill=FILLS[0], stroke=BLUE, width=1.2)
    p.polyline([(x, lower_edge(x)) for x in us], stroke=ORANGE, width=2.2)
    top = [x for x in us if x <= 0.5] + [0.5]
    p.polyline([(x, upper_edge(x)) for x in top], stroke=GREEN, width=2.2)
    p.line((0.5, 0), (0.5, upper_edge(0.5)), stroke=FAINT, width=1,
           dash='3 3')
    p.text((0.6, 0.69), 'ℓ(a, u)', size=13, color=BLUE)
    p.text((0.33, 0.17), 'arcsin(u − ½) + 801/1600', size=13,
           color=ORANGE, anchor='start')
    p.text((0.06, 1.0), 'arcsin(u + ½) − 801/1600', size=13,
           color=GREEN, anchor='start')
    p.save('appa-transverse', 'For each u, the labels of the admissible '
           'states (a, u) form the shaded interval. It lies above the curve '
           'arcsin(u - 1/2) + 801/1600 of the lower edge, and for u at most '
           '1/2 below the curve arcsin(u + 1/2) - 801/1600 of the upper edge')


# The envelope (Definition A.14 and Lemmas A.15 to A.17).

def envelope(x):
    return (1 / 24 + math.sqrt(TARGET - (x + 1) ** 2) / 3 + math.asin(x)
            - 0.75 * x)


def envelope_band():
    xe = math.sqrt(3) - 1
    n = 300
    xs = [xe * k / n for k in range(n + 1)]
    side_plus = lambda x, uu: (uu - 0.5) / 3 + 0.75 * (0.5 - x) + math.asin(x)

    def umax(x):
        a = x + 0.5
        return min(a, math.sqrt(TARGET - (x + 1) ** 2) - 0.5)

    low = [side_plus(x, 0) for x in xs]
    high = [side_plus(x, umax(x)) for x in xs]
    for x, h in zip(xs, high):
        assert h <= envelope(x) + 1e-12
    level = math.pi / 3 - HALF_WIDTH
    p = Plot(-0.06, 0.84, 0.1, 0.64, 470, 620)
    x_axis(p, -0.03, 0.82, y=0.13, ticks=((0, '0'), (0.25, '¼'), (0.5, '½'),
                                          (0.75, '¾')), label='x')
    p.line((xe, 0.13), (xe, high[-1]), stroke=FAINT, width=1, dash='3 3')
    y_axis(p, 0.13, 0.62, x=0, ticks=((0.2, '0.2'), (0.3, '0.3'),
                                      (0.4, '0.4'), (0.5, '0.5')))
    p.polygon(list(zip(xs, low)) + list(zip(reversed(xs), reversed(high))),
              fill=FILLS[0], stroke=BLUE, width=1)
    p.line((0, level), (0.78, level), stroke=INK, width=1.2, dash='6 4')
    p.text((0.78, level), 'π/3 − 801/1600', size=13, italic=False,
           anchor='end', dy=-10)
    p.curve(envelope, 0, 0.75, stroke=ORANGE, width=2.4)
    p.text((0.66, envelope(0.66)), 'E(x) − π/6', size=14, color=ORANGE,
           anchor='start', dx=8, dy=-2)
    p.text((0.33, 0.36), 'side(a, u) + arcsin x − π/6', size=13,
           color=BLUE)
    p.save('appa-envelope-band', 'For each x = a - 1/2, the values of side(a, '
           'u) + arcsin x - pi/6 over the admissible states (a, u) fill the '
           'shaded interval, which lies below the graph of E(x) - pi/6 and '
           'touches it where the disk bounds u')


def curvature_polynomial():
    P = lambda x: 676 * (1 - x * x) ** 3 - 9 * x * x * (9 - 8 * x - 4 * x * x) ** 3
    c = [676, 676, 32221 / 64, 64997 / 224, 327833 / 2240, 14627 / 128,
         3921235 / 28672, 402967 / 4096, 13945 / 256]
    w = 0.75
    for k in range(101):
        x = w * k / 100
        s = sum(c[i] * math.comb(8, i) * x ** i * (w - x) ** (8 - i)
                for i in range(9)) / w ** 8
        assert abs(s - P(x)) < 1e-8 * 676
    pts = [(w * i / 8, c[i]) for i in range(9)]
    p = Plot(-0.07, 0.83, -60, 740, 560, 0.4)
    x_axis(p, -0.02, 0.81, ticks=((0, '0'), (w, '¾')), label='x')
    y_axis(p, -20, 730, ticks=((100, '100'), (300, '300'), (500, '500'),
                               (676, '676')))
    p.line((0, min(c)), (w, min(c)), stroke=ORANGE, width=1, dash='3 3')
    p.polyline(pts, stroke=FAINT, width=1.4, dash='5 3')
    p.curve(P, 0, w, stroke=BLUE, width=2.4)
    for i, q in enumerate(pts):
        p.dot(q, r=4, fill=ORANGE)
        p.text(q, sb('c', str(i), size=13), size=13, color=ORANGE, dy=-12)
    p.text((0.36, P(0.36)), 'P', size=17, color=BLUE, anchor='end', dx=-10,
           dy=-6)
    p.save('appa-bernstein', 'The curvature polynomial P on [0, 3/4] and its '
           'nine Bernstein coefficients of degree 8, drawn as a control '
           'polygon at the points 3i/32; all of them are positive')


def envelope_tangent():
    t = 1 / 8
    d = 1 / math.sqrt(1 - t * t) - 0.75 - (t + 1) / (
        3 * math.sqrt(TARGET - (t + 1) ** 2))
    tan = lambda x: envelope(t) + d * (x - t)
    for k in range(101):
        x = 0.75 * k / 100
        assert envelope(x) <= tan(x) + 1e-12 and envelope(x) <= 0.5443
    level = math.pi / 3 - HALF_WIDTH
    p = Plot(-0.07, 0.84, 0.455, 0.565, 520, 3000)
    x_axis(p, -0.02, 0.82, y=0.46, ticks=((0, '0'), (t, '1/8'), (0.75, '¾')),
           label='x')
    y_axis(p, 0.46, 0.562, x=0, ticks=((0.48, '0.48'), (0.5, '0.50'),
                                       (0.52, '0.52'), (0.54, '0.54')))
    p.line((0, level), (0.8, level), stroke=INK, width=1.3)
    p.text((0.8, level), 'π/3 − 801/1600', size=13, italic=False,
           anchor='end', dy=-10)
    p.line((0, 0.5443), (0.8, 0.5443), stroke=GREEN, width=1.3, dash='6 4')
    p.text((0.8, 0.5443), '0.5443', size=13, italic=False, color=GREEN,
           anchor='end', dy=11)
    p.line((0, tan(0)), (0.75, tan(0.75)), stroke=PURPLE, width=1.6,
           dash='7 4')
    p.line((t, 0.46), (t, envelope(t)), stroke=FAINT, width=1, dash='3 3')
    p.curve(envelope, 0, 0.75, stroke=ORANGE, width=2.4)
    p.dot((t, envelope(t)), fill=PURPLE)
    p.text((0.45, tan(0.45)), 'tangent at 1/8', size=13, italic=False,
           color=PURPLE, dy=13)
    p.text((0.55, envelope(0.55)), 'E(x) − π/6', size=14, color=ORANGE,
           anchor='end', dx=-10, dy=6)
    p.save('appa-envelope', 'The envelope minus pi/6 on [0, 3/4], below its '
           'tangent at 1/8, which is nearly flat; both stay below 0.5443, '
           'itself below pi/3 - 801/1600')


def main():
    curvature()
    concave()
    sin_cos()
    taylor()
    bernstein_basis()
    admissible_region()
    marker_arc()
    asin_line()
    transverse()
    envelope_band()
    curvature_polynomial()
    envelope_tangent()


if __name__ == '__main__':
    main()

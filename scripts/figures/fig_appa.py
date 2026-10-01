#!/usr/bin/env python3
"""Draw the figures of Appendix A (docs/proof/appendix-a.md) in
docs/proof/figures/appendix-a/.

    python3 scripts/figures/fig_appa.py

Every curve is sampled from the function it shows, and every point is
computed from the formulas of the appendix.
"""
import math

from proof_figures import Figure, Graph, INK, FAINT, COLORS, FILLS, sb, shift, u

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
    p.save('appendix-a/curvature', 'A function f with second derivative at least '
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
    p.save('appendix-a/concave', 'The concave function alpha y plus A sin y plus B '
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
    p.save('appendix-a/sin-cos', 'Sine and cosine on [0, pi/2]: they cross at pi/4, '
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
    p.save('appendix-a/taylor', 'Left: the cosine between its Taylor polynomials of '
           'degrees 6 (below) and 4 (above). Right: the sine between its '
           'Taylor polynomials of degrees 7 (below) and 5 (above). The bounds '
           'hold on [0, infinity) and are tight near 0')


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
    pl.text(((l + c) / 2, -0.55), 'd ≥ 0', size=14, color=GREEN)
    pl.text(((c + r) / 2, 0.45), 'd ≤ 0', size=14, color=ORANGE)
    pl.save('appendix-a/peak', 'Lemma A.9 for f(y) = y cubed/3 - y to the '
            'fourth/4 on [-0.35, 1.25]: its derivative d(y) = y squared '
            '(1 - y) is nonnegative up to c = 1, vanishing at 0, and '
            'nonpositive after it, so f stays below its value at c')


# The marker arc in the chart (section F.1).


# ---------------------------------------------------------------------------
# Figure A.6: a first harmonic and a tangent of the square root
# (Lemmas A.11 and A.14).

def harmonic_and_root():
    f = Figure(-0.25, 7.55, -1.55, 1.75, 92)
    # Left: a first harmonic, concave where it is nonnegative.
    A, B = 0.6, 0.8
    H = lambda x: A * math.cos(x) + B * math.sin(x)
    p = Graph(f, 0.5, 1.15, x0=-PI, y0=0.0, dx=0.0, dy=0.0)
    p.x_axis(-PI, PI + 0.25, ticks=((-PI, '−π'), (-PI / 2, '−π/2'),
                                    (0, '0'), (PI / 2, 'π/2'), (PI, 'π')),
             label='x')
    z0 = math.atan2(-A, B)            # H(z0) = 0, H rising there
    z1 = z0 + PI
    xs = [-PI + 2 * PI * k / 400 for k in range(401)]
    pos = [(x, H(x)) for x in xs if z0 <= x <= z1]
    neg_l = [(x, H(x)) for x in xs if x <= z0]
    neg_r = [(x, H(x)) for x in xs if x >= z1]
    p.polyline(neg_l, stroke=FAINT, width=2)
    p.polyline(neg_r, stroke=FAINT, width=2)
    p.polyline(pos, stroke=BLUE, width=2.6)
    l, r = z0 + 0.35, z1 - 0.6
    p.line((l, H(l)), (r, H(r)), stroke=ORANGE, width=1.8, dash='6 4')
    for x in (l, r):
        p.dot((x, H(x)), r=3.4, fill=ORANGE)
    p.text((0.75, 1.12), 'H ≥ 0: concave', size=13, italic=False,
           color=BLUE, anchor='start')
    p.text((-2.21, -1.22), 'H &lt; 0: convex', size=13, italic=False,
           color=FAINT)
    p.text((-PI, 1.45), 'H(x) = 0.6 cos x + 0.8 sin x', size=14,
           anchor='start')
    # Right: the square root below its tangent at c^2.
    c = 0.4
    q = Graph(f, 9.0, 4.4, x0=0.0, y0=0.0, dx=4.25, dy=-1.25)
    q.x_axis(0, 0.36, ticks=((0.1, '0.1'), (c * c, 'c² = 0.16'),
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
    f.save('appendix-a/tools', 'Left: a first harmonic H(x) = 3/5 cos x + 4/5 '
         'sin x on minus pi to pi, concave and drawn in blue where it is '
         'nonnegative, convex and grey where it is negative, with a chord '
         'below the blue arc. Right: the square root of y and its tangent '
         'line at y = c squared = 0.16, which lies above it and touches it '
         'there')


def main():
    curvature()
    concave()
    sin_cos()
    taylor()
    peak()
    harmonic_and_root()


if __name__ == '__main__':
    main()

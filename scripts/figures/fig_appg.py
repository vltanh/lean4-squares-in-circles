#!/usr/bin/env python3
"""Draw the figures of Appendix G (docs/proof/appendix-g.md), seven squares:
the critical gap, set-up and the easy axes, in docs/proof/figures/appendix-g/.

    python3 scripts/figures/fig_appg.py

The label regions, their boundary pieces, the profiles and the canonical pairs
are computed from the same formulas as the text: the labels of a state, the
circle phi = 13/4, the transition state and the diagonal corner, and the
support sums of a canonical pair at the gap pi/3. Each figure asserts the
facts its caption states.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, u, shift)
from fig_front import it, polyline, arrow, arc_points

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]


# The labels and the boundary of the label regions.

def axial(v):
    return 5 * v / 4


def side(a, v):
    return PI / 6 + (v - 0.5) / 3 + 3 * (1 - a) / 4


def label(a, v):
    return min(axial(v), side(a, v), PI / 4)


def admissible(a, v):
    return (a >= 0.5 and 0 <= v <= a
            and (a + 0.5) ** 2 + (v + 0.5) ** 2 <= 13 / 4)


def support(x, y, z):
    """h(x, y, z) of Definition 10.10."""
    return (x * math.cos(z) + y * math.sin(z)
            + (abs(math.cos(z)) + abs(math.sin(z))) / 2)


M = 2 * PI + 17
J = math.sqrt(202 * 13 / 4 - M ** 2)
X0, Y0 = (9 * M + 11 * J) / 202, (11 * M - 9 * J) / 202
A0, U0 = X0 - 0.5, Y0 - 0.5
S0 = 5 * U0 / 4
RD = math.sqrt(13 / 8) - 0.5
TD = PI / 6 + 7 / 12 - 5 * RD / 12
NN = 97 / 144
ROOT3 = math.sqrt(3)
OMEGA = math.atan(9 / 4)
CAP = [(PI / 5, PI / 5), ((7 - PI / 5) / 9, PI / 5),
       ((7 - PI) / 5, (7 - PI) / 5)]


def circle(v):
    return math.sqrt(13 / 4 - (v + 0.5) ** 2) - 0.5


def axial_line(v):
    return (2 * PI + 7 - 11 * v) / 9


def axial_top(v):
    return min(circle(v), axial_line(v))


def tie_a(t):
    return (2 * PI + 7) / 9 - 44 * t / 45


def diagonal(t):
    return (2 * PI + 7 - 12 * t) / 5


def D(t):
    return PI / 6 + 19 / 24 - t


def Z(t):
    return math.sqrt(NN * 13 / 4 - D(t) ** 2)


def X(t):
    return (0.75 * D(t) + Z(t) / 3) / NN


def Y(t):
    return (-D(t) / 3 + 0.75 * Z(t)) / NN


def side_top(t):
    if t <= TD:
        return (X(t) - 0.5, Y(t) - 0.5)
    return (diagonal(t), diagonal(t))


def grid(lo, hi, n=120):
    return [lo + (hi - lo) * k / n for k in range(n + 1)]


# Labels.

def mtext(f, pos, s, size=13, color=INK, anchor='start', italic=False, dx=0,
          dy=0):
    """A label, upright unless italic; mathematics is marked up with it()."""
    f.text(pos, s, size=size, anchor=anchor, color=color, italic=italic,
           dx=dx, dy=dy)


def lab(*parts):
    """The parts of a label, joined."""
    return ''.join(parts)


def sub(base, s, after='', size=13):
    """An italic letter with a subscript (italic if it is a letter), and the
    text after it, back on the base line; for a label of the given size."""
    d, small = 0.3 * size, 0.72 * size
    s = it(s) if s.isalpha() else s
    out = (it(base) + f'<tspan dy="{d:.1f}" font-size="{small:.1f}">{s}'
           '</tspan>')
    if after:
        out += f'<tspan dy="{-d:.1f}">{after}</tspan>'
    return out


# Drawing helpers.

class Shifted:
    """The drawing calls of a Figure, with every point shifted by (dx, dy)."""

    def __init__(self, f, dx, dy):
        self.f, self.dx, self.dy = f, dx, dy

    def q(self, p):
        return (p[0] + self.dx, p[1] + self.dy)

    def polygon(self, pts, **kw):
        self.f.polygon([self.q(p) for p in pts], **kw)

    def line(self, a, b, **kw):
        self.f.line(self.q(a), self.q(b), **kw)

    def circle(self, c, r, **kw):
        self.f.circle(self.q(c), r, **kw)

    def dot(self, c, **kw):
        self.f.dot(self.q(c), **kw)

    def arc(self, c, r, t0, t1, stroke, width=4.0):
        self.f.arc(self.q(c), r, t0, t1, stroke, width)

    def text(self, c, s, **kw):
        mtext(self.f, self.q(c), s, **kw)


class Plot:
    """A graph: data coordinates mapped affinely into a box of a Figure."""

    def __init__(self, f, box, xr, yr):
        self.f = f
        self.left, self.bottom, self.width, self.height = box
        (self.x0, self.x1), (self.y0, self.y1) = xr, yr

    def P(self, x, y):
        return (self.left + (x - self.x0) / (self.x1 - self.x0) * self.width,
                self.bottom + (y - self.y0) / (self.y1 - self.y0)
                * self.height)

    def curve(self, pts, stroke=INK, width=1.8, dash=None):
        polyline(self.f, [self.P(*p) for p in pts], stroke=stroke,
                 width=width, dash=dash)

    def graph(self, g, a, b, n=200, **kw):
        self.curve([(x, g(x)) for x in grid(a, b, n)], **kw)

    def hline(self, y, a=None, b=None, stroke=FAINT, width=1, dash='4 3'):
        a = self.x0 if a is None else a
        b = self.x1 if b is None else b
        self.f.line(self.P(a, y), self.P(b, y), stroke=stroke, width=width,
                    dash=dash)

    def vline(self, x, a=None, b=None, stroke=FAINT, width=1, dash='2 3'):
        a = self.y0 if a is None else a
        b = self.y1 if b is None else b
        self.f.line(self.P(x, a), self.P(x, b), stroke=stroke, width=width,
                    dash=dash)

    def axes(self, xticks, yticks, xlabel, ylabel='', size=12):
        f = self.f
        f.line(self.P(self.x0, self.y0),
               shift(self.P(self.x1, self.y0), (0.22, 0)), width=1,
               arrow=True)
        f.line(self.P(self.x0, self.y0),
               shift(self.P(self.x0, self.y1), (0, 0.3)), width=1,
               arrow=True)
        k = 4 / f.s
        for x, s in xticks:
            p = self.P(x, self.y0)
            f.line(shift(p, (0, -k)), shift(p, (0, k)), width=1)
            mtext(f, p, s, size=size, anchor='middle', dy=15)
        for y, s in yticks:
            p = self.P(self.x0, y)
            f.line(shift(p, (-k, 0)), shift(p, (k, 0)), width=1)
            mtext(f, p, s, size=size, anchor='end', dx=-7)
        mtext(f, shift(self.P(self.x1, self.y0), (0.22, 0)), xlabel, size=15,
              anchor='end', dy=-12, italic='<' not in xlabel)
        if ylabel:
            mtext(f, shift(self.P(self.x0, self.y1), (0, 0.3)), ylabel,
                  size=15, dx=9, dy=5, italic='<' not in ylabel)

    def title(self, s, size=13):
        mtext(self.f, self.P(self.x0, self.y1), s, size=size, dy=-44)


def bracket(f, p, q, normal, text, color=ORANGE, size=15, off=0.15):
    """A measured interval from p to q with end ticks and a label beside it."""
    f.line(p, q, stroke=color, width=2.6)
    for r in (p, q):
        f.line(shift(r, normal, 0.07), shift(r, normal, -0.07), stroke=color,
               width=1.6)
    mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
    mtext(f, shift(mid, normal, off), text, size=size, color=color,
          anchor='middle')


def canonical(a, v, s, A, w, t, gap=PI / 3):
    """The canonical pair: the centre of S, the centre of T and its turn d."""
    d = gap + s * label(a, v) - t * label(A, w)
    c = (A * math.cos(d) - t * w * math.sin(d),
         A * math.sin(d) + t * w * math.cos(d))
    return (a, s * v), c, d


def sums(S, T):
    """The support sums sigma_k of two convex polygons, k = 0, 1, 2, 3."""
    out = []
    for k in range(4):
        n = u(k * PI / 2)
        out.append(max(p[0] * n[0] + p[1] * n[1] for p in S)
                   - min(p[0] * n[0] + p[1] * n[1] for p in T))
    return out


def draw_pair(g, cs, ct, d):
    S, T = square_corners(cs), square_corners(ct, math.degrees(d))
    g.arc((0, 0), 1.0, -0.5, 2.1, GREY, width=1.2)
    g.polygon(S, fill=FILLS[0], stroke=BLUE, opacity=0.85)
    g.polygon(T, fill=FILLS[2], stroke=GREEN, opacity=0.85)
    g.dot((0, 0))
    g.text((-0.06, -0.09), 'o', anchor='end', size=14, italic=True)
    return S, T


def level_line(f, z, level, t0, t1, stroke, dash='5 3', width=1.4):
    """The segment of the line <., u(z)> = level between the parameters t0
    and t1 along u(z + pi/2), measured from the axis of u(z)."""
    c, e = shift((0, 0), u(z), level), u(z + PI / 2)
    p, q = shift(c, e, t0), shift(c, e, t1)
    f.line(p, q, stroke=stroke, width=width, dash=dash)
    return p, q


# Figure: the four support sums of a canonical pair.

def pair_axes():
    a, v, A, w = 0.95, 0.35, 1.0, 0.2
    cs, ct, d = canonical(a, v, 1, A, w, 1)
    assert abs(math.degrees(d) - 71) < 1
    ls, lt = label(a, v), d + label(A, w)
    names = ['outward', 'forward', 'inward', 'backward']
    W, H = 3.15, 3.1
    f = Figure(0, 2 * W, 0, 2 * H, 108)
    for k in range(4):
        col, row = k % 2, 1 - k // 2
        g = Shifted(f, col * W + 1.45, row * H + 1.05)
        n = u(k * PI / 2)
        S, T = draw_pair(g, cs, ct, d)
        for ang, color in ((ls, BLUE), (lt, GREEN)):
            g.line((0, 0), u(ang), stroke=color, width=1, dash='3 3')
            g.dot(u(ang), r=2.6, fill=color)
        g.text((cs[0] + 0.3, cs[1] - 0.3), 'S', size=16, color=BLUE,
               anchor='middle', italic=True)
        g.text((ct[0] - 0.02, ct[1] + 0.2), 'T', size=16, color=GREEN,
               anchor='middle', italic=True)
        proj = lambda p: p[0] * n[0] + p[1] * n[1]
        ps, pt = [proj(p) for p in S], [proj(p) for p in T]
        assert abs((max(ps) - min(pt)) - sums(S, T)[k]) < 1e-12
        horizontal = k % 2 == 0
        base = -0.52 if horizontal else -0.82
        sgn = n[0] + n[1]

        def at(val, off=0.0):
            x = val * sgn
            return (x, base + off) if horizontal else (base + off, x)
        ends = (-0.65, 1.65) if horizontal else (-0.35, 1.8)
        e0 = (ends[0], base) if horizontal else (base, ends[0])
        e1 = (ends[1], base) if horizontal else (base, ends[1])
        g.line(e0, e1, stroke=FAINT, width=1)
        g.line(at(min(ps), 0.06), at(max(ps), 0.06), stroke=BLUE, width=4.5)
        g.line(at(min(pt), -0.06), at(max(pt), -0.06), stroke=GREEN,
               width=4.5)
        far = max(ps + pt)
        g.line(at(far + 0.08), at(far + 0.4), width=1.6, arrow=True)
        side_dir = (0, 1) if horizontal else (1, 0)
        g.text(shift(at(far + 0.3), side_dir, 0.17), sub('n', str(k), size=14),
               size=14, anchor='middle')
        lo, hi = min(pt), max(ps)
        normal = (0, -1) if horizontal else (-1, 0)
        bracket(f, g.q(at(lo, -0.22)), g.q(at(hi, -0.22)), normal,
                sub('σ', str(k), size=15), off=0.18)
        pS = max(S, key=proj)
        pT = min(T, key=proj)
        for r, color in ((pS, BLUE), (pT, GREEN)):
            g.line(r, at(proj(r), -0.22), stroke=color, width=0.9, dash='2 3')
        g.text((0.2, 1.95), lab(it('k'), f' = {k}: {names[k]} axis'),
               size=13, anchor='middle')
    f.save('appendix-g/pair-axes', 'A canonical pair of squares S and T at the gap '
           'pi/3, drawn once for each axis; in each panel the shadows of S '
           'and T on the line of the normal n_k, and the support sum sigma_k, '
           'the length from the lowest point of T to the highest point of S '
           'along n_k')


# Figure: the lower bounds for the support (Lemma G.4).

def support_bounds():
    W = 3.3
    f = Figure(-1.45, W + 1.8, -1.36, 1.7, 112)
    # (a) A square with (a, |b|) admissible, centre within root 3 - 1/2.
    a, b, z = 1.0, -0.4, 5 * PI / 6
    assert admissible(a, abs(b)) and math.hypot(a, b) <= ROOT3 - 0.5
    h = support(a, b, z)
    assert h > -37 / 50 and abs(h + 0.383) < 1e-3
    Q = square_corners((a, b))
    top = max(Q, key=lambda p: p[0] * u(z)[0] + p[1] * u(z)[1])
    assert abs(top[0] * u(z)[0] + top[1] * u(z)[1] - h) < 1e-12
    f.circle((0, 0), ROOT3 - 0.5, stroke=FAINT, width=1.2, dash='5 4')
    f.line(shift((0, 0), u(z), -1.0), shift((0, 0), u(z), 1.15),
           stroke=FAINT, width=1)
    f.polygon(Q, fill=FILLS[0], stroke=BLUE)
    f.dot((a, b), r=2.6, fill=BLUE)
    hi, _ = level_line(f, z, h, -0.75, 0.75, BLUE)
    _, lo = level_line(f, z, -37 / 50, -0.75, 0.75, ORANGE)
    f.dot(top, r=3.4, fill=BLUE)
    arrow(f, (0, 0), shift((0, 0), u(z), 0.62), width=1.6, size=9)
    mtext(f, shift((0, 0), u(z), 0.62), lab(it('u'), '(', it('z'), ')'),
          size=14, anchor='middle', dx=6, dy=-16)
    f.dot((0, 0))
    mtext(f, (0, 0), 'o', size=14, italic=True, dx=4, dy=13)
    mtext(f, hi, lab(it('h'), '(', it('a'), ', ', it('b'), ', ', it('z'),
                     ')'), size=13, color=BLUE, anchor='end', dx=-9, dy=-7)
    mtext(f, lo, '−37/50', size=13, color=ORANGE, anchor='end', dx=-6,
          dy=6)
    mtext(f, (a, b), lab('(', it('a'), ', ', it('b'), ')'), size=13,
          color=BLUE, dx=6, dy=10)
    mtext(f, (-1.0, -0.45), 'radius √3 − ½', size=12, color=FAINT)
    mtext(f, (-1.4, 1.6), '(a) the bound −37/50', size=13)
    # (b) The marker arc lies in the square, so it is below the support.
    g = Shifted(f, W, 0)
    a, v, s = 1.0, 0.5, 1
    ell = label(a, v)
    x, z = ell + 0.4, 1.25
    assert abs(x - s * ell) <= 0.5
    for t in grid(ell - 0.5, ell + 0.5, 50):
        assert abs(math.cos(t) - a) <= 0.5 and abs(math.sin(t) - v) <= 0.5
    hz = support(a, s * v, z)
    assert hz > math.cos(z - x)
    Q = square_corners((a, s * v))
    top = max(Q, key=lambda p: p[0] * u(z)[0] + p[1] * u(z)[1])
    g.arc((0, 0), 1.0, -0.62, 1.5, GREY, width=1.4)
    g.line(shift((0, 0), u(z), -0.55), shift((0, 0), u(z), 1.62),
           stroke=FAINT, width=1)
    g.polygon(Q, fill=FILLS[0], stroke=BLUE)
    g.arc((0, 0), 1.0, ell - 0.5, ell + 0.5, BLUE, width=4.5)
    g.line((0, 0), u(ell), stroke=BLUE, width=1, dash='3 3')
    g.dot(u(ell), r=2.8, fill=BLUE)
    _, hi = level_line(g, z, hz, -1.3, 0.3, BLUE)
    _, lo = level_line(g, z, math.cos(z - x), -1.3, 0.3, ORANGE)
    g.dot(top, r=3.4, fill=BLUE)
    g.dot(u(x), r=3.6, fill=ORANGE)
    g.text(u(x), lab(it('u'), '(', it('x'), ')'), size=14, color=ORANGE,
           dx=6, dy=-8)
    arrow(f, g.q((0, 0)), g.q(shift((0, 0), u(z), 0.6)), width=1.6, size=9)
    g.text(shift((0, 0), u(z), 0.6), lab(it('u'), '(', it('z'), ')'),
           size=14, anchor='end', dx=-6, dy=-2)
    g.dot((0, 0))
    g.text((0, 0), 'o', size=14, italic=True, dx=4, dy=13)
    g.text(hi, lab(it('h'), '(', it('a'), ', ', it('su'), ', ', it('z'),
                   ')'), size=13, color=BLUE, anchor='end', dx=-6)
    g.text(lo, lab('cos(', it('z'), ' − ', it('x'), ')'), size=13,
           color=ORANGE, anchor='end', dx=-6)
    g.text((1.05, 0.15), lab(it('Q'), '(', it('a'), ', ', it('su'), ')'),
           size=13, color=BLUE)
    g.text((-0.6, 1.62), '(b) the marker arc', size=13)
    f.save('appendix-g/support-bounds', 'Left: a square Q(a, b) with its centre in '
           'the dashed disk of radius root 3 minus 1/2 about o; for a '
           'direction u(z) its support line, at the level h(a, b, z), lies '
           'beyond the line at the level -37/50. Right: the square of the side '
           'state contains its marker arc; its support line in a direction '
           'u(z) lies beyond the parallel line through a point u(x) of the '
           'arc, at the level cos(z - x)')


# Figure: the label regions.

def region_polygons():
    low = [(circle(v), v) for v in grid(0, U0, 60)]
    high = [(circle(v), v) for v in grid(U0, RD, 60)]
    axial_reg = [(0.5, 0.0)] + low + [CAP[1], CAP[0], (0.5, 0.5)]
    side_reg = high + [CAP[2], CAP[1]]
    return axial_reg, side_reg, list(CAP)


def regions():
    axial_reg, side_reg, cap = region_polygons()
    f = Figure(0.34, 1.34, -0.09, 0.88, 560)
    f.polygon(axial_reg, fill=FILLS[0], stroke='none')
    f.polygon(side_reg, fill=FILLS[2], stroke='none')
    f.polygon(cap, fill=FILLS[1], stroke='none')
    pts = [(circle(v), v) for v in grid(0, RD, 160)]
    polyline(f, pts, width=1.5)
    f.line((0.5, 0), (0.5, 0.5), width=1.5)
    f.line((0.5, 0.5), (RD, RD), width=1.5)
    f.line((A0, U0), cap[1], stroke=PURPLE, width=1.8)
    f.line(cap[0], cap[1], stroke=ORANGE, width=1.5, dash='5 3')
    f.line(cap[1], cap[2], stroke=ORANGE, width=1.5, dash='5 3')
    f.line((0.5, 0), (ROOT3 - 0.5, 0), stroke=BLUE, width=4.5)
    f.line((0.36, 0), (1.32, 0), width=1, arrow=True)
    mtext(f, (1.32, -0.035), 'a', size=15, anchor='end', italic=True)
    f.line((0.4, -0.06), (0.4, 0.86), width=1, arrow=True)
    mtext(f, (0.385, 0.85), 'u', size=15, anchor='end', italic=True)
    for x, s in ((0.5, '½'), (1.0, '1'), (ROOT3 - 0.5, '√3 − ½')):
        f.line((x, 0), (x, -0.012), width=1)
        mtext(f, (x, -0.042), s, size=12, anchor='middle')
    f.line((0.4, 0.5), (0.412, 0.5), width=1)
    mtext(f, (0.39, 0.5), '½', size=12, anchor='end')
    f.line((0.412, 0.5), (0.5, 0.5), stroke=FAINT, width=0.8, dash='2 3')
    f.dot((A0, U0), r=4, fill=PURPLE)
    mtext(f, (A0 + 0.018, U0 + 0.012), lab('(', sub('a', '0', ', '),
                                           sub('u', '0', ')')),
          size=13, color=PURPLE)
    f.dot((RD, RD), r=4.4)
    mtext(f, (RD + 0.018, RD + 0.006), lab('(', sub('r', 'd', ', '),
                                           sub('r', 'd', ')')), size=13)
    f.dot((1.0, 0.5), r=4, fill=GREEN)
    mtext(f, (1.016, 0.512), '(1, ½)', size=13, color=GREEN)
    for k, (p, off, anchor) in enumerate(((cap[0], (-0.016, 0.014), 'end'),
                                          (cap[1], (0.0, -0.032), 'middle'),
                                          (cap[2], (-0.02, 0.0), 'end'))):
        f.dot(p, r=3.4 if k < 2 else 2.4, fill=ORANGE)
        mtext(f, shift(p, off), sub('V', str(k), size=14), size=14,
              anchor=anchor, color=ORANGE)
    mtext(f, (0.8, 0.22), 'axial', size=16, color=BLUE, anchor='middle')
    mtext(f, (0.975, 0.6), 'side', size=16, color=GREEN, anchor='middle')
    mtext(f, (0.57, 0.8), 'capped', size=14, color=ORANGE, anchor='middle')
    f.line((0.6, 0.785), (0.68, 0.7), stroke=ORANGE, width=0.8)
    mtext(f, (0.6, 0.025), lab('axial states (', it('a'), ', 0)'), size=12,
          color=BLUE)
    mtext(f, (1.17, 0.38), lab(it('φ'), ' = 13/4'), size=13)
    mtext(f, (0.535, 0.56), lab(it('u'), ' = ', it('a')), size=12,
          anchor='end')
    mtext(f, (0.905, 0.4), lab('9', it('a'), ' + 11', it('u'), ' = 2π + 7'),
          size=12, color=PURPLE, anchor='end')
    f.save('appendix-g/regions', 'The admissible states in the (a, u)-plane, split '
           'into the axial, side and capped label regions by the tie line '
           '9a + 11u = 2 pi + 7 and the cap lines u = pi/5 and '
           '9a - 4u = 7 - pi, with the transition state (a0, u0), the '
           'diagonal corner (rd, rd), the side state (1, 1/2), the axial '
           'states (a, 0) and the vertices V0, V1, V2 of the capped triangle')


# Figure: the transition state and the diagonal corner (Definition G.9).

def transition():
    R = math.sqrt(13) / 2
    f = Figure(-0.22, 2.0, -0.2, 1.98, 250)
    # The admissible states in the coordinates X = a + 1/2, Y = u + 1/2.
    region = ([(1.0, 0.5), (ROOT3, 0.5)]
              + [(math.sqrt(R * R - y * y), y) for y in grid(0.5, RD + 0.5)]
              + [(1.0, 1.0)])
    f.polygon(region, fill=GREY, stroke='none')
    polyline(f, arc_points((0, 0), R, 0, PI / 2, 120), width=1.4)
    f.line((0, 0), (1.92, 1.92), stroke=FAINT, width=1, dash='4 3')
    foot = (9 * M / 202, 11 * M / 202)
    e = (11 / math.sqrt(202), -9 / math.sqrt(202))
    ends = [shift(foot, (11, -9), y) for y in (J / 202, -J / 202)]
    assert abs(math.hypot(*ends[0]) - R) < 1e-12
    assert abs(ends[0][0] - X0) < 1e-12 and abs(ends[0][1] - Y0) < 1e-12
    assert abs(math.hypot(*ends[1]) - R) < 1e-12
    f.line(shift(ends[1], e, -0.12), shift(ends[0], e, 0.16), stroke=PURPLE,
           width=1.8)
    f.line((0, 0), foot, stroke=INK, width=1.1, dash='5 3')
    n = (9 / math.sqrt(202), 11 / math.sqrt(202))
    k = 0.05
    polyline(f, [shift(foot, n, -k), shift(shift(foot, n, -k), e, k),
                 shift(foot, e, k)], width=1)
    arrow(f, foot, shift(foot, e, 0.3), color=PURPLE, width=1.4, size=8)
    mtext(f, shift(foot, e, 0.3), '(11, −9)', size=12, color=PURPLE, dx=4,
          dy=10)
    f.dot(foot, r=3.2, fill=PURPLE)
    mtext(f, foot, lab(it('y'), ' = 0'), size=13, color=PURPLE, anchor='end',
          dx=-8, dy=-4)
    f.dot(ends[0], r=4, fill=PURPLE)
    mtext(f, ends[0], lab('(', sub('X', '0', ', '), sub('Y', '0', ')')),
          size=13, color=PURPLE, dx=9, dy=-2)
    mtext(f, ends[0], lab(it('y'), ' = ', it('J'), '/202'), size=13,
          color=PURPLE, anchor='end', dx=-6, dy=16)
    f.dot(ends[1], r=3.2, fill=PURPLE)
    mtext(f, ends[1], lab(it('y'), ' = −', it('J'), '/202'), size=13,
          color=PURPLE, dx=9, dy=-6)
    mtext(f, shift((0, 0), n, 0.95), lab(it('M'), '/√202'), size=13,
          anchor='end', dx=-12, dy=-2)
    c = (RD + 0.5, RD + 0.5)
    f.dot(c, r=4)
    mtext(f, c, lab('(', sub('r', 'd', ' + ½, '), sub('r', 'd', ' + ½)')),
          size=13, dx=10, dy=-12)
    mtext(f, shift(ends[0], e, 0.16), lab('9', it('X'), ' + 11', it('Y'),
                                          ' = ', it('M')),
          size=13, color=PURPLE, dx=-4, dy=16)
    mtext(f, (1.88, 1.9), lab(it('X'), ' = ', it('Y')), size=12, color=FAINT,
          anchor='end', dx=-8)
    mtext(f, (1.3, 0.58), 'admissible', size=12, color=FAINT,
          anchor='middle')
    mtext(f, (1.36, 0.25), lab(it('X'), '² + ', it('Y'), '² = 13/4'),
          size=13)
    f.line((-0.2, 0), (1.98, 0), stroke=INK, width=1, arrow=True)
    f.line((0, -0.18), (0, 1.96), stroke=INK, width=1, arrow=True)
    mtext(f, (1.98, 0), 'X', size=15, italic=True, anchor='end', dy=14)
    mtext(f, (0, 1.96), 'Y', size=15, italic=True, dx=8, dy=4)
    f.dot((0, 0))
    mtext(f, (0, 0), '0', size=13, anchor='end', dx=-5, dy=11)
    f.save('appendix-g/transition', 'The quarter circle X squared plus Y squared '
           'equals 13/4 in the coordinates X = a + 1/2, Y = u + 1/2, with the '
           'admissible states shaded; the tie line 9X + 11Y = M, the dashed '
           'perpendicular from 0 to its point y = 0, the direction (11, -9) '
           'along it, and its two points on the circle, y = J/202 at the '
           'transition state (X0, Y0) and y = -J/202; the dashed diagonal '
           'X = Y meets the circle at the diagonal corner')


# Figure: the circle and the tie line over the u-axis (Lemma G.12).

def axial_top_figure():
    f = Figure(0, 7.4, 0, 4.6, 80)
    g = Plot(f, (0.9, 0.7, 6.0, 3.5), (0, 0.84), (0.45, 1.55))
    # The axial region: 1/2 <= a, u <= a, a <= chi(u), u <= pi/5.
    top = [(v, axial_top(v)) for v in grid(0, PI / 5, 120)]
    region = ([(0, 0.5), (0.5, 0.5), (PI / 5, PI / 5)] + top[::-1])
    f.polygon([g.P(*p) for p in region], fill=FILLS[0], stroke='none')
    for v in grid(0, U0, 60):
        assert circle(v) <= axial_line(v) + 1e-12
        assert circle(v) <= A0 + (U0 - v) / 2 + 1e-12
    for v in grid(U0, RD, 60):
        assert axial_line(v) <= circle(v) + 1e-12
    g.axes([(0, '0'), (U0, sub('u', '0')), (PI / 5, 'π/5'),
            (RD, sub('r', 'd'))],
           [(0.5, '½'), (A0, sub('a', '0')), (ROOT3 - 0.5, '√3 − ½')],
           'u', 'a')
    g.vline(U0, 0.45, A0)
    g.hline(A0, 0, U0)
    g.vline(PI / 5, PI / 5, axial_top(PI / 5))
    g.graph(lambda v: v, 0.45, 0.82, stroke=FAINT, width=1, dash='4 3')
    g.graph(lambda v: A0 + (U0 - v) / 2, 0, U0, stroke=ORANGE, width=1.4,
            dash='6 3')
    g.graph(circle, 0, RD, stroke=INK, width=1.4)
    g.graph(axial_line, 0, RD, stroke=PURPLE, width=1.4)
    g.graph(axial_top, 0, RD, n=300, stroke=BLUE, width=3.2)
    f.dot(g.P(U0, A0), r=3.6, fill=PURPLE)
    mtext(f, g.P(0.7, circle(0.7)), it('γ'), size=16, dy=-14)
    mtext(f, g.P(0.06, axial_line(0.06)), it('λ'), size=16, color=PURPLE,
          dx=-4, dy=-12)
    mtext(f, g.P(0.47, axial_top(0.47)), it('χ'), size=16, color=BLUE,
          dx=2, dy=18)
    mtext(f, g.P(0.01, 1.29), 'slope −½', size=12, color=ORANGE)
    mtext(f, g.P(0.75, 0.75), lab(it('a'), ' = ', it('u')), size=12,
          color=FAINT, dx=8, dy=6)
    mtext(f, g.P(0.2, 0.75), 'axial', size=15, color=BLUE, anchor='middle')
    f.save('appendix-g/axial-top', 'Graphs over u from 0 to rd: the circle gamma '
           'decreasing from root 3 minus 1/2 to rd, the tie line lambda, '
           'crossing it at u0 at the height a0, and their minimum chi in bold, '
           'which follows the circle up to u0 and the tie line beyond; below '
           'it the shaded axial region up to u = pi/5, and a dashed line of '
           'slope -1/2 through (u0, a0) above the circle on [0, u0]')


# Figure: the circle parametrized by the side label.

def parametrization():
    R = math.sqrt(13) / 2
    rn = math.sqrt(NN)
    e = (0.75 / rn, -1 / (3 * rn))
    g = (1 / (3 * rn), 0.75 / rn)
    f = Figure(-0.35, 2.02, -0.72, 1.98, 230)
    t = 0.6
    assert S0 < t < TD
    P = (X(t), Y(t))
    assert abs(math.hypot(*P) - R) < 1e-12
    foot = shift((0, 0), e, D(t) / rn)
    assert abs(math.hypot(*shift(foot, g, Z(t) / rn)) - R) < 1e-12
    polyline(f, arc_points((0, 0), R, 0, PI / 2, 120), width=1.3)
    t0, t1 = math.atan2(Y0, X0), PI / 4
    f.arc((0, 0), R, t0, t1, GREEN, width=5)
    f.line((0, 0), (1.95, 1.95), stroke=FAINT, width=1, dash='4 3')
    mtext(f, (1.9, 1.95), lab(it('X'), ' = ', it('Y')), size=12, color=FAINT,
          anchor='end', dx=-8)
    # the line of side label t: 3X/4 - Y/3 = D(t)
    lo, hi = shift(foot, g, -0.3), shift(foot, g, 2.0)
    f.line(lo, hi, stroke=PURPLE, width=1.6)
    mtext(f, lo, lab('3', it('X'), '/4 − ', it('Y'), '/3 = ', it('D'), '(',
                     it('τ'), ')'), size=13, color=PURPLE, dx=8, dy=2)
    # the coordinates of P in the orthogonal frame
    f.line((0, 0), foot, stroke=ORANGE, width=2.6)
    f.line(foot, P, stroke=BLUE, width=2.6)
    k = 0.05
    polyline(f, [shift(foot, e, -k), shift(shift(foot, e, -k), g, k),
                 shift(foot, g, k)], width=1)
    arrow(f, (0, 0), shift((0, 0), e, 0.3), width=1.5, size=9)
    arrow(f, (0, 0), shift((0, 0), g, 0.3), width=1.5, size=9)
    mtext(f, shift((0, 0), e, 0.3), '(3/4, −1/3)', size=12, anchor='end',
          dx=-2, dy=18)
    mtext(f, shift((0, 0), g, 0.3), '(1/3, 3/4)', size=12, anchor='end',
          dx=-8)
    mtext(f, shift(shift((0, 0), e, D(t) / rn / 2 + 0.1), g, -0.1),
          lab(it('D'), '(', it('τ'), ')/√', it('N')), size=13, color=ORANGE,
          anchor='middle')
    mtext(f, shift(shift(foot, g, Z(t) / rn / 2), e, 0.08),
          lab(it('Z'), '(', it('τ'), ')/√', it('N')), size=13, color=BLUE)
    f.dot(P, r=4, fill=GREEN)
    mtext(f, shift(P, (0.05, 0.05)), lab('(', it('X'), '(', it('τ'), '), ',
                                          it('Y'), '(', it('τ'), '))'),
          size=13)
    f.dot((X0, Y0), r=3.6, fill=PURPLE)
    mtext(f, (X0 + 0.05, Y0 - 0.06), lab('(', sub('X', '0', ', '),
                                         sub('Y', '0', ')')),
          size=13, color=PURPLE)
    f.dot((RD + 0.5, RD + 0.5), r=3.6)
    mtext(f, (RD + 0.5, RD + 0.5), lab('(', sub('r', 'd', ' + ½, '),
                                       sub('r', 'd', ' + ½)')),
          size=13, anchor='end', dx=-44, dy=16)
    f.dot((0, 0))
    mtext(f, (0, 0), '0', size=13, anchor='end', dx=-6, dy=13)
    f.line((-0.3, 0), (2.0, 0), stroke=INK, width=1, arrow=True)
    f.line((0, -0.7), (0, 1.95), stroke=INK, width=1, arrow=True)
    mtext(f, (2.0, 0), 'X', size=15, italic=True, anchor='end', dy=15)
    mtext(f, (0, 1.95), 'Y', size=15, italic=True, dx=9, dy=4)
    mtext(f, (1.0, 1.66), lab(it('X'), '² + ', it('Y'), '² = 13/4'),
          size=13)
    f.save('appendix-g/parametrization', 'The circle X^2 + Y^2 = 13/4 in the '
           'coordinates X = a + 1/2, Y = u + 1/2, a line of constant side '
           'label, 3X/4 - Y/3 = D(tau), and the orthogonal frame of the '
           'vectors (3/4, -1/3) and (1/3, 3/4); the point (X(tau), Y(tau)) '
           'where the line meets the circle, with its coordinates D/root N '
           'and Z/root N in that frame; the arc it sweeps as tau runs from s0 '
           'to td, from (X0, Y0) to the diagonal')


# Figure: the functions of the parametrization (Lemma G.14).

def circle_functions():
    f = Figure(0, 7.2, 0, 4.6, 80)
    g = Plot(f, (0.9, 0.65, 5.4, 3.55), (0.34, 0.81), (0.4, 1.72))
    for t in grid(S0, TD, 200):
        assert 0.5 < D(t) < 1 and 1 < Z(t) < 1.4
        assert Y0 - 1e-12 <= Y(t) <= X(t) + 1e-12 and 1.25 < X(t) <= X0
    g.axes([(S0, sub('s', '0')), (0.5, '0.5'), (0.6, '0.6'), (0.7, '0.7'),
            (TD, sub('t', 'd'))],
           [(0.5, '½'), (Y0, sub('Y', '0')), (1, '1'), (1.25, '5/4'),
            (1.4, '7/5'), (X0, sub('X', '0'))], 'τ')
    for y in (0.5, 1, 1.25, 1.4):
        g.hline(y, S0, 0.8)
    g.vline(TD, 0.4, 1.7)
    g.vline(S0, 0.4, 1.7)
    for fn, color, name, t, dy in ((X, BLUE, 'X', 0.47, -12),
                                   (Z, PURPLE, 'Z', 0.47, 16),
                                   (Y, GREEN, 'Y', 0.62, -12),
                                   (D, ORANGE, 'D', 0.62, 16)):
        g.graph(fn, S0, TD, stroke=color, width=2.4)
        mtext(f, g.P(t, fn(t)), name, size=15, color=color, italic=True,
              anchor='middle', dy=dy)
    f.dot(g.P(TD, X(TD)), r=3.4)
    for fn, color in ((X, BLUE), (Y, GREEN)):
        f.dot(g.P(S0, fn(S0)), r=3.2, fill=color)
    f.save('appendix-g/circle-functions', 'Graphs over the label tau from s0 to td: '
           'X decreasing from X0 to rd + 1/2 and staying above 5/4, Y '
           'increasing from Y0 to the same value, where the two meet, Z '
           'increasing between 1 and 7/5, and D decreasing with slope -1 '
           'between 1/2 and 1')


# Figure: segments of constant side label.

def segments():
    _, side_reg, cap = region_polygons()
    f = Figure(0.62, 1.3, 0.2, 0.83, 740)
    f.polygon(side_reg, fill=FILLS[2], stroke='none')
    f.polygon(cap, fill=FILLS[1], stroke='none')
    pts = [(circle(v), v) for v in grid(0.24, RD, 160)]
    polyline(f, pts, width=1.5)
    f.line((0.635, 0.635), (RD, RD), width=1.5)
    f.line((A0, U0), cap[1], stroke=PURPLE, width=1.8)
    f.line((A0, U0), (axial_line(0.25), 0.25), stroke=PURPLE, width=1,
           dash='2 3')
    f.line(cap[0], cap[1], stroke=ORANGE, width=1.5, dash='5 3')
    taus = [(0.42, '0.42'), (0.48, '0.48'), (PI / 6, 'π/6'), (0.6, '0.6'),
            (0.66, '0.66'), (0.72, '0.72'), (0.76, None), (TD, None),
            (PI / 4, 'π/4')]
    for t, s in taus:
        p, q = (tie_a(t), 0.8 * t), side_top(t)
        assert abs(side(*p) - t) < 1e-12 and abs(side(*q) - t) < 1e-12
        assert abs(axial(p[1]) - t) < 1e-12
        f.line(p, q, stroke=GREEN if t < PI / 4 else ORANGE,
               width=1.6 if t < PI / 4 else 2)
        f.dot(p, r=2.6, fill=PURPLE)
        f.dot(q, r=2.6, fill=INK)
        if s and t < PI / 4:
            mtext(f, shift(p, (-0.012, -0.012)), s, size=12, anchor='end',
                  color=GREEN)
    top = side_top(PI / 6)
    assert abs(top[0] - 1) < 1e-12 and abs(top[1] - 0.5) < 1e-12
    mtext(f, (0.705, 0.668), 'π/4', size=12, anchor='middle', color=ORANGE)
    f.dot((A0, U0), r=4.2, fill=PURPLE)
    mtext(f, (A0 + 0.014, U0 + 0.004), lab('(', sub('a', '0', ', '),
                                           sub('u', '0', '),'), ' ', it('τ'),
                                           ' = ', sub('s', '0')),
          size=13, color=PURPLE)
    f.dot((RD, RD), r=4.4)
    f.dot(cap[2], r=2.4, fill=ORANGE)
    mtext(f, (RD + 0.014, RD + 0.004), lab('(', sub('r', 'd', ', '),
                                           sub('r', 'd', '),'), ' ', it('τ'),
                                           ' = ', sub('t', 'd')), size=13)
    f.dot((1.0, 0.5), r=4.2, fill=GREEN)
    mtext(f, (1.014, 0.505), '(1, ½)', size=13, color=GREEN)
    mtext(f, (1.12, 0.62), lab(it('φ'), ' = 13/4'), size=13)
    mtext(f, (0.69, 0.75), lab(it('u'), ' = ', it('a')), size=12,
          anchor='end')
    mtext(f, (0.9, 0.3), lab('tie line 9', it('a'), ' + 11', it('u'),
                             ' = 2π + 7'), size=12, color=PURPLE)
    mtext(f, (CAP[1][0] - 0.008, CAP[1][1] - 0.02), sub('V', '1', size=14),
          size=14, color=ORANGE, anchor='end')
    mtext(f, (CAP[2][0] - 0.014, CAP[2][1] + 0.008), sub('V', '2', size=14),
          size=14, color=ORANGE, anchor='end')
    f.line((0.63, 0.25), (1.29, 0.25), width=1, arrow=True)
    mtext(f, (1.29, 0.232), 'a', size=15, anchor='end', italic=True)
    f.line((0.64, 0.24), (0.64, 0.82), width=1, arrow=True)
    mtext(f, (0.652, 0.815), 'u', size=15, italic=True)
    for x in (0.8, 1.0, 1.2):
        f.line((x, 0.25), (x, 0.244), width=1)
        mtext(f, (x, 0.25), f'{x:g}', size=12, anchor='middle', dy=14)
    for y in (0.4, 0.6):
        f.line((0.64, y), (0.634, y), width=1)
        mtext(f, (0.64, y), f'{y:g}', size=12, anchor='end', dx=-8)
    f.save('appendix-g/segments', 'The side region foliated by the segments of '
           'constant side label tau, of slope 9/4 in the (a, u)-plane; each '
           'runs from the tie line up to the circle phi = 13/4 or, beyond the '
           'diagonal corner, to the diagonal u = a; the segment of label '
           'pi/6 ends at the side state (1, 1/2) and the segment of label '
           'pi/4 is the edge V1 V2 of the capped triangle')


# Figure: the slope along the tie line (Lemma G.17).

def tie_slope(t, x):
    return ((43 / 90 - 0.8 * t) * math.sin(x)
            + (13 / 10 - tie_a(t)) * math.cos(x))


def slope():
    f = Figure(0, 7.4, 0, 4.5, 80)
    g = Plot(f, (0.9, 0.7, 5.4, 3.4), (0, 1.3), (0, 0.68))
    bound = 115 / 72 - 77 * PI / 180
    taus = [(S0, sub('s', '0')), (0.5, '0.5'), (0.6, '0.6'), (0.7, '0.7'),
            (PI / 4, 'π/4')]
    for t, _ in taus:
        for x in grid(0, OMEGA, 200):
            assert tie_slope(t, x) > 0
            if 43 / 90 - 0.8 * t < 0:
                assert tie_slope(t, x) >= bound * math.cos(x) - 1e-12
    assert abs(tie_slope(PI / 4, OMEGA) - bound * math.cos(OMEGA)) < 1e-12
    g.axes([(0, '0'), (0.5, '0.5'), (1, '1'), (OMEGA, it('ω'))],
           [(0, '0'), (0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6')], 'x')
    g.vline(OMEGA, 0, 0.66)
    g.graph(lambda x: bound * math.cos(x), 0, OMEGA, stroke=INK, width=1.4,
            dash='6 3')
    for k, (t, name) in enumerate(taus):
        color = COLORS[[0, 5, 2, 3, 1][k]]
        g.graph(lambda x: tie_slope(t, x), 0, OMEGA, stroke=color, width=2.2)
        mtext(f, g.P(OMEGA, tie_slope(t, OMEGA)), lab(it('τ'), ' = ', name),
              size=12, color=color, dx=8, dy=4)
    f.dot(g.P(OMEGA, tie_slope(PI / 4, OMEGA)), r=3.2, fill=ORANGE)
    mtext(f, g.P(0.3, 0.12), lab('(115/72 − 77π/180) cos ', it('x')),
          size=12)
    f.save('appendix-g/slope', 'Graphs over x from 0 to omega of the left side '
           'of Lemma G.17 for the labels s0, 0.5, 0.6, 0.7 and pi/4, all '
           'positive; for pi/4 the dashed lower bound (115/72 - 77 pi/180) '
           'cos x of the proof, which it meets at omega')


# Figure: the pair at the minimum of the transition profile (Lemma G.18).

def transition_F(t):
    ang = PI / 3 - t + S0
    top = Y(t) if t <= TD else diagonal(t) + 0.5
    return 1 - top - (A0 - 0.5) * math.sin(ang) + Y0 * math.cos(ang)


def transition_dF(t):
    """F' on [s0, td], as in Lemma G.18."""
    ang = PI / 3 - t + S0
    return -X(t) / Z(t) + (A0 - 0.5) * math.cos(ang) + Y0 * math.sin(ang)


def transition_ddF(t):
    """F'' on [s0, td], as in Lemma G.18."""
    ang = PI / 3 - t + S0
    return (39 / (16 * Z(t) ** 3) + (A0 - 0.5) * math.sin(ang)
            - Y0 * math.cos(ang))


def transition_min():
    ts = grid(0.7, 0.74, 4000)
    return min(ts, key=transition_F)


def transition_pair():
    tau = transition_min()
    assert abs(tau - 0.7227) < 1e-3 and abs(transition_F(tau) - 8e-4) < 1e-5
    a, v = side_top(tau)
    assert abs(label(a, v) - tau) < 1e-12 and abs(label(A0, U0) - S0) < 1e-12
    cs, ct, d = canonical(a, v, -1, A0, U0, -1)
    S, T = square_corners(cs), square_corners(ct, math.degrees(d))
    sig = sums(S, T)
    assert abs(sig[1] - transition_F(tau)) < 1e-12 and min(sig) > 0
    low = min(T, key=lambda p: p[1])
    assert min(p[0] for p in S) < low[0] < max(p[0] for p in S)
    f = Figure(-0.45, 3.45, -1.32, 1.42, 150)
    f.arc((0, 0), 1.0, -1.1, 1.2, GREY, width=1.2)
    f.polygon(S, fill=FILLS[0], stroke=BLUE, opacity=0.85)
    f.polygon(T, fill=FILLS[2], stroke=GREEN, opacity=0.85)
    for ang, color in ((-tau, BLUE), (d - S0, GREEN)):
        f.line((0, 0), u(ang), stroke=color, width=1, dash='3 3')
        f.dot(u(ang), r=2.6, fill=color)
    assert abs((d - S0) - (-tau) - PI / 3) < 1e-12
    f.line((-0.3, 0), (1.85, 0), stroke=FAINT, width=0.8)
    f.dot((0, 0))
    mtext(f, (0, 0), 'o', size=14, italic=True, anchor='end', dx=-6, dy=10)
    mtext(f, shift(cs, (0.18, -0.2)), 'S', size=16, color=BLUE, italic=True)
    mtext(f, shift(ct, (0.05, 0.12)), 'T', size=16, color=GREEN, italic=True)
    f.line((-0.32, cs[1] + 0.5), (1.6, cs[1] + 0.5), stroke=BLUE, width=0.9,
           dash='3 3')
    mtext(f, (-0.32, cs[1] + 0.5), lab(it('y'), ' = ½ − ', it('u')),
          size=12, color=BLUE, dy=12)
    arrow(f, (1.5, cs[1] - 0.2), (1.5, cs[1] + 0.25), width=1.5, size=9)
    mtext(f, (1.5, cs[1] + 0.25), sub('n', '1', size=14), size=14, dx=6,
          dy=6)
    # The inset: the corner of T near the top edge of S, magnified.
    mag = 250.0
    box = (2.05, -1.18, 1.3, 1.3)
    cx, cy = box[0] + box[2] / 2, box[1] + box[3] / 2
    zoom = lambda p: (cx + mag * (p[0] - low[0]),
                      cy + mag * (p[1] - (cs[1] + 0.5)) - 0.1)
    rect = [(box[0], box[1]), (box[0] + box[2], box[1]),
            (box[0] + box[2], box[1] + box[3]), (box[0], box[1] + box[3])]
    f.polygon(rect, fill='#ffffff', stroke=FAINT, width=1)
    edge_y = zoom((0, cs[1] + 0.5))[1]
    f.polygon([(box[0], box[1]), (box[0] + box[2], box[1]),
               (box[0] + box[2], edge_y), (box[0], edge_y)],
              fill=FILLS[0], stroke='none', opacity=0.85)
    f.line((box[0], edge_y), (box[0] + box[2], edge_y), stroke=BLUE, width=1.5)
    k = T.index(low)
    nb = [T[k - 1], T[(k + 1) % 4]]
    tip = zoom(low)
    pieces = []
    for q in nb:
        dvec = (q[0] - low[0], q[1] - low[1])
        n = math.hypot(*dvec)
        far = zoom(shift(low, dvec, 0.75 / mag / n * 1.0))
        pieces.append(far)
    f.polygon([pieces[0], tip, pieces[1]], fill=FILLS[2], stroke='none',
              opacity=0.85)
    polyline(f, [pieces[0], tip, pieces[1]], stroke=GREEN, width=1.6)
    f.line((tip[0] + 0.16, edge_y), (tip[0] + 0.16, tip[1]), stroke=ORANGE,
           width=2.2)
    mtext(f, (tip[0] + 0.22, (edge_y + tip[1]) / 2),
          sub('σ', '1', ' ≈ 0.0008'), size=13, color=ORANGE, dy=2)
    mtext(f, (box[0] + 0.05, box[1] + box[3] - 0.08), '×250', size=12,
          color=FAINT)
    src = (low[0], cs[1] + 0.5)
    f.circle(src, 0.05, stroke=FAINT, width=1)
    f.line(shift(src, (0.05, 0)), (box[0], cy), stroke=FAINT, width=0.8,
           dash='2 3')
    f.save('appendix-g/transition-pair', 'A canonical pair with both signs -1 at '
           'the gap pi/3: the source S below the axis, at the top of its side '
           'segment on the circle, and the target T at the transition state, '
           'turned by about 39 degrees; the lowest corner of T touches the top '
           'edge of S, and a magnified inset shows that it lies only about '
           '0.0008 below that edge')


# Figure: the transition profile (Lemma G.18).

def transition_profile():
    th1 = PI / 3 - TD + S0
    F0, F1 = transition_F(TD), transition_dF(TD)
    assert 0.6272 < th1 < 0.6273
    assert 0.5868 < math.sin(th1) < 0.587 and 0.8096 < math.cos(th1) < 0.8098
    assert F0 > 0.002 and 0 < F1 < 0.044 and 0.044 ** 2 < 0.002
    assert abs(X(TD) / Z(TD) - 12 / 13) < 1e-12
    assert all(transition_ddF(x) > 0.5 for x in grid(0.4, TD, 300))
    par = lambda x: F0 + F1 * (x - TD) + (x - TD) ** 2 / 4
    assert all(par(x) <= transition_F(x) + 1e-12 for x in grid(0.4, TD, 300))
    pmin = F0 - F1 ** 2
    assert abs(pmin - 3e-4) < 1e-4
    tau = transition_min()
    f = Figure(0, 7.4, 0, 4.5, 80)
    g = Plot(f, (0.9, 0.7, 5.4, 3.3), (0.38, 0.81), (-0.004, 0.056))
    g.axes([(0.4, '2/5'), (0.5, '0.5'), (0.6, '0.6'), (0.7, '0.7'),
            (PI / 4, 'π/4')],
           [(0, '0'), (0.02, '0.02'), (0.04, '0.04')], 'τ')
    g.hline(0, 0.38, 0.81, stroke=INK, width=0.8, dash=None)
    g.vline(TD, -0.004, 0.05)
    mtext(f, g.P(TD, 0.05), sub('t', 'd'), size=13, anchor='middle', dy=-10)
    g.graph(par, 0.4, TD, stroke=ORANGE, width=1.5, dash='6 3')
    g.graph(transition_F, 0.4, TD, stroke=BLUE, width=2.4)
    g.graph(transition_F, TD, PI / 4, n=20, stroke=GREEN, width=3)
    f.dot(g.P(TD, F0), r=3.4)
    f.dot(g.P(tau, transition_F(tau)), r=3, fill=BLUE)
    mtext(f, g.P(0.47, transition_F(0.47)), it('F'), size=16, color=BLUE,
          dx=8, dy=-6)
    mtext(f, g.P(0.4, 0.008), 'parabola', size=12, color=ORANGE)
    mtext(f, g.P(PI / 4, transition_F(PI / 4)), it('G'), size=15,
          color=GREEN, dx=8, dy=-4)
    mtext(f, g.P(tau, transition_F(tau)), lab('minimum ≈ 0.0008'), size=12,
          color=BLUE, anchor='middle', dy=-14)
    f.save('appendix-g/transition-profile', 'The transition profile F on the '
           'interval from 2/5 to td, a convex blue curve falling from about '
           '0.053 to a minimum of about 0.0008 near 0.72 and rising slightly '
           'up to td, continued by a short green piece G on the tiny interval '
           'from td to pi/4, above a dashed orange parabola that touches the '
           'curve at the black dot at td and dips nearly to 0 near 0.7')


# Figure: the diagonal profile (Lemma G.20).

def diagonal_K(t):
    return (6 / 5 * (PI / 6 - t) + 51 / 40 * math.cos(7 * PI / 12 - t)
            - 11 / 40 * math.sin(7 * PI / 12 - t))


def diagonal_slope(x):
    return 51 / 40 * math.sin(x) + 11 / 40 * math.cos(x)


def diagonal_profile():
    x1 = 7 * PI / 12 - 0.4
    assert diagonal_slope(PI / 3) > 1.2 and diagonal_slope(x1) > 1.2
    assert all(diagonal_slope(x) > 1.2 for x in grid(PI / 3, x1))
    assert all(diagonal_K(x) < diagonal_K(y) for x, y in
               zip(grid(0.4, PI / 4), grid(0.4, PI / 4)[1:]))
    assert abs(-12 / 25 + 51 / 40 * 2 / 15 - 11 / 40 + 0.585) < 1e-12
    assert diagonal_K(0.4) > PI / 5 - 0.585 > 0
    f = Figure(0, 10.0, 0, 4.35, 70)
    g = Plot(f, (0.9, 0.7, 3.9, 2.9), (0.0, 1.62), (0.8, 1.36))
    g.axes([(0, '0'), (PI / 3, 'π/3'), (x1, sub('x', '1')),
            (PI / 2, 'π/2')],
           [(1.0, '1'), (1.2, '6/5'), (1.3, '1.3')], 'x')
    g.hline(1.2, 0, 1.6, stroke=ORANGE, width=1.4, dash='6 3')
    g.vline(PI / 3, 0.8, diagonal_slope(PI / 3))
    g.vline(x1, 0.8, diagonal_slope(x1))
    g.graph(diagonal_slope, 0.46, PI / 2, stroke=FAINT, width=1.6)
    g.graph(diagonal_slope, PI / 3, x1, stroke=BLUE, width=2.6)
    for x in (PI / 3, x1):
        f.dot(g.P(x, diagonal_slope(x)), r=3.2, fill=BLUE)
    g.title(lab('(a) (51/40) sin ', it('x'), ' + (11/40) cos ', it('x'),
                ' &gt; 6/5'))
    h = Plot(f, (6.0, 0.7, 3.3, 2.9), (0.38, 0.81), (0.0, 0.1))
    h.axes([(0.4, '2/5'), (0.6, '0.6'), (PI / 4, 'π/4')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1')], 'ℓ')
    h.graph(diagonal_K, 0.4, PI / 4, stroke=BLUE, width=2.4)
    f.dot(h.P(0.4, diagonal_K(0.4)), r=3.4, fill=BLUE)
    f.line(h.P(0.38, PI / 5 - 0.585), h.P(0.43, PI / 5 - 0.585),
           stroke=ORANGE, width=2)
    mtext(f, h.P(0.43, PI / 5 - 0.585), 'π/5 − 0.585', size=12,
          color=ORANGE, dx=4, dy=4)
    mtext(f, h.P(0.62, diagonal_K(0.62)), it('K'), size=16, color=BLUE,
          dy=-12)
    h.title(lab('(b) part (2): the profile ', it('K')))
    f.save('appendix-g/diagonal-profile', 'Left: the concave function 51/40 sin '
           'x + 11/40 cos x on [pi/3, x1] with x1 = 7 pi/12 - 2/5, above the '
           'dashed level 6/5, with its continuation in grey. Right: the '
           'profile K on [2/5, pi/4], increasing from about 0.052 at 2/5, '
           'above the bound pi/5 - 0.585 marked there, to about 0.085')


# Figure: the target support on the axial boundary.

def xi(s):
    return math.sqrt(13 / 4 - (0.5 + 0.8 * s) ** 2)


def zeta(s):
    return 0.5 + 0.8 * s


def circle_target(t, s):
    ang = PI / 3 - t + s
    return -(xi(s) - 1) * math.sin(ang) + zeta(s) * math.cos(ang)


def line_target(t, s):
    ang = PI / 3 - t + s
    return -(tie_a(s) - 0.5) * math.sin(ang) + (0.8 * s + 0.5) * math.cos(ang)


def targets():
    f = Figure(0, 7.8, 0, 4.9, 80)
    g = Plot(f, (0.8, 0.75, 5.6, 3.75), (0, 0.82), (-0.14, 0.42))
    g.axes([(0, '0'), (S0, sub('s', '0')), (PI / 4, 'π/4')],
           [(0, '0'), (0.2, '0.2'), (0.4, '0.4')], 'ℓ′')
    g.vline(S0, -0.14, 0.4)
    g.hline(0, 0, 0.82, dash=None, width=0.8)
    for k, (t, name) in enumerate(((0.4, '2/5'), (0.55, '0.55'),
                                   (0.7, '0.7'), (PI / 4, 'π/4'))):
        color = COLORS[k]
        top = min(PI / 4, OMEGA - PI / 3 + t)
        cs = [circle_target(t, s) for s in grid(0, S0, 80)]
        ls = [line_target(t, s) for s in grid(S0, top, 80)]
        assert all(x >= y - 1e-12 for x, y in zip(cs, cs[1:]))
        assert all(x <= y + 1e-12 for x, y in zip(ls, ls[1:]))
        assert abs(cs[-1] - ls[0]) < 1e-12 and max(ls) < 0.4
        g.curve(list(zip(grid(0, S0, 80), cs)), stroke=color, width=2.2)
        g.curve(list(zip(grid(S0, top, 80), ls)), stroke=color, width=2.2,
                dash='7 4')
        f.dot(g.P(S0, cs[-1]), r=3.2, fill=color)
        f.dot(g.P(top, ls[-1]), r=2.6, fill=color)
        mtext(f, g.P(top, ls[-1]), lab(it('ℓ'), ' = ', name), size=12,
              color=color, dx=8, dy=4)
    for x, name in ((0.18, 'C'), (0.58, 'L')):
        mtext(f, g.P(x, -0.115), lab(it(name), '(', it('ℓ'), ', ', it('ℓ′'),
                                     ')'), size=13, anchor='middle')
    f.save('appendix-g/targets', 'The target support along the axial boundary as '
           'a function of the target label, for four source labels: '
           'decreasing along the circular piece up to s0 (solid) and '
           'increasing along the tie line from s0 up to the switch label or '
           'pi/4 (dashed)')


# Figures: the derivative ratio and the quintic (Lemma G.22).

def quintic(x):
    return (-500 * x ** 5 + 800 * x ** 4 + 1705 * x ** 3 - 3900 * x ** 2
            + 3120 * x - 1872)


def ratio_rho(s):
    return xi(s) * (9 / 5 - xi(s)) / (zeta(s) * (xi(s) - 4 / 5))


def ratio():
    assert ratio_rho(0) < 2 - ROOT3
    assert all(ratio_rho(s) < math.tan(PI / 12 + s) for s in grid(0, S0))
    f = Figure(0, 6.6, 0, 4.2, 80)
    h = Plot(f, (0.9, 0.7, 4.4, 3.1), (0, 0.42), (0.2, 0.8))
    h.axes([(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (0.3, '0.3'),
            (S0, sub('s', '0'))],
           [(0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6'), (0.8, '0.8')], 'ℓ′')
    h.vline(S0, 0.2, math.tan(PI / 12 + S0))
    h.graph(lambda s: math.tan(PI / 12 + s), 0, S0, stroke=ORANGE, width=2.2)
    h.graph(ratio_rho, 0, S0, stroke=BLUE, width=2.2)
    f.dot(h.P(0, 2 - ROOT3), r=3.2, fill=ORANGE)
    f.dot(h.P(0, ratio_rho(0)), r=3.2, fill=BLUE)
    mtext(f, h.P(0, 2 - ROOT3), '2 − √3', size=12, color=ORANGE,
          anchor='end', dx=-8, dy=-5)
    mtext(f, h.P(0, ratio_rho(0)), lab(it('ρ'), '(0)'), size=12, color=BLUE,
          dx=10, dy=12)
    mtext(f, h.P(S0, math.tan(PI / 12 + S0)), lab('tan ', it('d')), size=13,
          color=ORANGE, dx=8)
    mtext(f, h.P(S0, ratio_rho(S0)), it('ρ'), size=15, color=BLUE, dx=8)
    f.save('appendix-g/ratio', 'For the source label pi/4, graphs over the target '
           'label from 0 to s0 of the ratio rho, increasing from rho(0), '
           'about 0.25, to about 0.45, and of tan d with d = pi/12 + l′, which '
           'starts just above it at 2 - root 3 = tan(pi/12), about 0.27, and '
           'rises to about 0.72')


def quintic_figure():
    lo, hi = 8 / 5, 7 / 4

    def chord(x):
        return ((hi - x) * quintic(lo) + (x - lo) * quintic(hi)) / (hi - lo)
    assert abs(quintic(lo) - 119.68) < 1e-9 and quintic(hi) > 78.5
    assert all(quintic(x) > chord(x) - 1e-9 for x in grid(lo, hi, 300))
    f = Figure(0, 6.6, 0, 4.2, 80)
    g = Plot(f, (0.9, 0.7, 4.4, 3.1), (1.56, 1.8), (0, 150))
    g.axes([(lo, '8/5'), (1.65, '1.65'), (1.7, '1.7'), (hi, '7/4')],
           [(0, '0'), (50, '50'), (100, '100'), (150, '150')], 'X')
    for x in (lo, hi):
        g.vline(x, 0, quintic(x))
    g.graph(quintic, 1.57, lo, n=20, stroke=FAINT, width=1.6)
    g.graph(quintic, hi, 1.78, n=20, stroke=FAINT, width=1.6)
    g.curve([(lo, quintic(lo)), (hi, quintic(hi))], stroke=ORANGE, width=2)
    g.graph(quintic, lo, hi, stroke=BLUE, width=2.4)
    for x, s, dx, anchor in ((lo, '119.68', 6, 'start'),
                             (hi, '78.57', -6, 'end')):
        f.dot(g.P(x, quintic(x)), r=3.4, fill=ORANGE)
        mtext(f, g.P(x, quintic(x)), s, size=12, color=ORANGE, anchor=anchor,
              dx=dx, dy=22)
    mtext(f, g.P(1.675, quintic(1.675)), it('P'), size=16, color=BLUE,
          anchor='middle', dy=-12)
    mtext(f, g.P(1.675, (quintic(lo) + quintic(hi)) / 2), 'chord', size=12,
          color=ORANGE, anchor='middle', dy=16)
    f.save('appendix-g/quintic', 'The quintic P on the interval from 8/5 to 7/4, a '
           'concave blue arch from 119.68 at 8/5 up to about 132 and down to '
           'about 78.6 at 7/4, continued in grey beyond both ends, above the '
           'orange chord joining its two end points and far above the axis')


# Figure: the easy sectors.

def easy():
    W, H = 3.25, 3.35
    f = Figure(0, 2 * W, 0, 2 * H, 104)
    titles = [lab('(a) outward axis'),
              lab('(b) backward axis, ', it('s'), ' = 1'),
              lab('(c) inward axis, ', it('s'), ' = −1'),
              lab('(d) forward axis, ', it('s'), ' = ', it('t'), ' = 1')]
    configs = [((1.0, 0.5, 1), (1.0, 0.0, 1)), ((1.0, 0.5, 1), (1.0, 0.0, 1)),
               ((1.0, 0.5, -1), (1.0, 0.5, 1)),
               ((0.95, 0.35, 1), (1.0, 0.2, 1))]
    for k, ((a, v, s), (A, w, t)) in enumerate(configs):
        col, row = k % 2, 1 - k // 2
        g = Shifted(f, col * W + 1.5, row * H + 1.4)
        cs, ct, d = canonical(a, v, s, A, w, t)
        S, T = draw_pair(g, cs, ct, d)
        sig = sums(S, T)
        ls, lt = s * label(a, v), d + t * label(A, w)
        g.text(shift(cs, (0.32, -0.3)), 'S', size=15, color=BLUE,
               anchor='middle', italic=True)
        g.text((0.2, 1.78), titles[k], size=13, anchor='middle')
        if k == 0:
            assert sig[0] > 13 / 50
            g.text(shift(ct, (-0.3, 0.3)), 'T', size=15, color=GREEN,
                   anchor='middle', italic=True)
            g.circle((0, 0), 31 / 25, stroke=INK, width=1, dash='5 4')
            g.line((37 / 50, -1.2), (37 / 50, 1.55), stroke=ORANGE, width=1.2,
                   dash='4 3')
            g.text((37 / 50 + 0.04, -1.15), lab(it('x'), ' = 37/50'),
                   size=12, color=ORANGE)
            g.line((a + 0.5, -1.2), (a + 0.5, 1.2), stroke=BLUE, width=1.2,
                   dash='4 3')
            g.text((a + 0.5, 1.29), lab(it('x'), ' = ', it('a'), ' + ½'),
                   size=12, color=BLUE, anchor='middle')
            g.dot(ct, r=3, fill=GREEN)
            g.text((-1.45, 1.3), lab('|', sub('c', 'T', '| &lt; 31/25', 12)),
                   size=12)
            g.line((-1.0, 1.21), shift((0, 0), u(0.78 * PI), 31 / 25),
                   stroke=INK, width=0.8)
            left = min(T, key=lambda p: p[0])
            g.dot(left, r=3.4, fill=GREEN)
            bracket(f, g.q((left[0], -0.82)), g.q((a + 0.5, -0.82)), (0, -1),
                    sub('σ', '0', size=14), off=0.16, size=14)
            g.line(left, (left[0], -0.82), stroke=GREEN, width=0.9,
                   dash='2 3')
        elif k == 1:
            m = u(lt)
            assert sig[3] >= m[1] - (s * v - 0.5) - 1e-12
            g.text(shift(ct, (-0.3, 0.3)), 'T', size=15, color=GREEN,
                   anchor='middle', italic=True)
            g.line((0, 0), m, stroke=GREEN, width=1, dash='3 3')
            g.dot(m, r=3.6, fill=GREEN)
            g.text(shift(m, (0.07, 0.12)), 'marker', size=12, color=GREEN)
            y0 = s * v - 0.5
            g.line((-0.9, y0), (1.7, y0), stroke=BLUE, width=1.2, dash='4 3')
            g.text((-0.9, y0 - 0.13), lab(it('y'), ' = ', it('u'), ' − ½'),
                   size=12, color=BLUE)
            g.line((m[0] + 0.02, m[1]), (m[0] + 0.02, y0), stroke=ORANGE,
                   width=2.2)
            g.text((m[0] + 0.1, (m[1] + y0) / 2 - 0.2),
                   lab('≤ ', sub('σ', '3')), size=13, color=ORANGE)
        elif k == 2:
            half = 1 / 2
            y = lt - half
            p = u(y)
            assert sig[2] >= p[0] - (a - 0.5) - 1e-12
            g.text(shift(ct, (0.3, 0.3)), 'T', size=15, color=GREEN,
                   anchor='middle', italic=True)
            g.arc((0, 0), 1.0, lt - half, lt + half, GREEN, width=4.5)
            g.dot(p, r=3.6, fill=GREEN)
            g.line((0, 0), p, stroke=GREEN, width=1, dash='3 3')
            g.line((a - 0.5, -1.2), (a - 0.5, 1.5), stroke=BLUE, width=1.2,
                   dash='4 3')
            g.text((a - 0.5 - 0.04, 1.42), lab(it('x'), ' = ', it('a'),
                                                 ' − ½'),
                   size=12, color=BLUE, anchor='end')
            g.line((a - 0.5, p[1] + 0.03), (p[0], p[1] + 0.03),
                   stroke=ORANGE, width=2.2)
            g.text(((a - 0.5 + p[0]) / 2, p[1] + 0.17),
                   lab('≤ ', sub('σ', '2')), size=13, color=ORANGE,
                   anchor='middle')
            g.text(shift(u(lt + half), (-0.2, 0.0)),
                   lab('marker arc of ', it('T')), size=12, color=GREEN,
                   anchor='end')
        else:
            g.text(shift(ct, (-0.3, 0.3)), 'T', size=15, color=GREEN,
                   anchor='middle', italic=True)
            ps = [q[1] for q in S]
            pt = [q[1] for q in T]
            base = -0.8
            g.line((base, -0.4), (base, 1.8), stroke=FAINT, width=1)
            g.line((base + 0.06, min(ps)), (base + 0.06, max(ps)),
                   stroke=BLUE, width=4.5)
            g.line((base - 0.06, min(pt)), (base - 0.06, max(pt)),
                   stroke=GREEN, width=4.5)
            bracket(f, g.q((base - 0.22, min(pt))),
                    g.q((base - 0.22, max(ps))), (-1, 0),
                    sub('σ', '1', size=14), off=0.18, size=14)
            for r, color in ((max(S, key=lambda q: q[1]), BLUE),
                             (min(T, key=lambda q: q[1]), GREEN)):
                g.line(r, (base - 0.22, r[1]), stroke=color, width=0.9,
                       dash='2 3')
        g.line((0, 0), u(ls), stroke=BLUE, width=1, dash='3 3')
        g.dot(u(ls), r=2.6, fill=BLUE)
    f.save('appendix-g/easy', 'The four easy sectors: (a) T has a point left of '
           'x = 37/50 while S reaches x = a + 1/2; (b) the marker point of T '
           'lies above the lower edge of S; (c) the marker arc of T reaches '
           'past the near edge of S; (d) the shadows of S and T on the '
           'forward axis overlap')


# Figure: the forward axis with positive signs (Proposition G.29).

def forward_k(x):
    return -0.8 * x + math.sin(x) + math.cos(x)


def forward_bound():
    m = 4 / 3 - 2 * PI / 15
    assert forward_k(0.2) > 1.018 > 0.915 > m and forward_k(PI / 6) > m
    assert all(forward_k(x) > m for x in grid(0.2, PI / 6))
    f = Figure(0, 10.0, 0, 4.75, 70)
    # (a) The cases of the proof in the square of the two labels.
    q = PI / 4
    g = Plot(f, (0.9, 0.7, 3.2, 3.2), (0, 0.84), (0, 0.84))
    case1 = [(5 / 16, 0), (q, 0), (q, q), (5 / 16, q)]
    case3 = [(0, PI / 12), (5 / 16, 5 / 16 + PI / 12), (5 / 16, q), (0, q)]
    case4 = [(0, 0), (5 / 16, 0), (5 / 16, 5 / 16 + PI / 12), (0, PI / 12)]
    for poly, fill in ((case1, FILLS[0]), (case3, FILLS[2]),
                       (case4, FILLS[1])):
        f.polygon([g.P(*p) for p in poly], fill=fill, stroke='none')
    g.axes([(0, '0'), (5 / 16, '5/16'), (q, 'π/4')],
           [(PI / 12, 'π/12'), (q, 'π/4')], 'ℓ', 'ℓ′')
    f.line(g.P(5 / 16, 0), g.P(5 / 16, q), stroke=INK, width=1.2)
    f.line(g.P(0, PI / 12), g.P(5 / 16, 5 / 16 + PI / 12), stroke=INK,
           width=1.2)
    f.line(g.P(5 / 16, 5 / 16 + PI / 12), g.P(q, q), stroke=INK, width=0.8,
           dash='3 3')
    f.line(g.P(0, q), g.P(q, q), stroke=FAINT, width=0.8)
    f.line(g.P(q, 0), g.P(q, q), stroke=FAINT, width=0.8)
    mtext(f, g.P(0.55, 0.42), 'step 1', size=13, color=BLUE, anchor='middle')
    mtext(f, g.P(0.55, 0.42), sub('σ', '1', ' &gt; 1/100', 12), size=12,
          color=BLUE, anchor='middle', dy=17)
    mtext(f, g.P(0.14, 0.64), 'step 3', size=13, color=GREEN,
          anchor='middle')
    mtext(f, g.P(0.14, 0.64), sub('σ', '1', ' &gt; 7/80', 12), size=12,
          color=GREEN, anchor='middle', dy=17)
    mtext(f, g.P(0.155, 0.14), 'step 4', size=13, color=ORANGE,
          anchor='middle')
    mtext(f, g.P(0.12, 0.12 + PI / 12), lab(it('z'), ' = π/4'), size=12,
          dx=4, dy=14)
    g.title(lab('(a) the steps, in the labels (', it('ℓ'), ', ',
                it('ℓ′'), ')'))
    # (b) Step 4: the concave function k above the level m.
    h = Plot(f, (5.9, 0.7, 3.6, 3.2), (0, 0.85), (0.86, 1.06))
    h.axes([(0, '0'), (0.2, '1/5'), (PI / 6, 'π/6'), (PI / 4, 'π/4')],
           [(m, it('m')), (1.0, '1')], 'x')
    h.hline(m, 0, 0.82, stroke=ORANGE, width=1.4, dash='6 3')
    h.graph(forward_k, 0, 0.69, stroke=FAINT, width=1.6)
    h.graph(forward_k, 0.2, PI / 6, stroke=BLUE, width=2.6)
    for x in (0.2, PI / 6):
        h.vline(x, 0.86, forward_k(x))
        f.dot(h.P(x, forward_k(x)), r=3.2, fill=BLUE)
    mtext(f, h.P(0.36, forward_k(0.36)), it('k'), size=16, color=BLUE,
          anchor='middle', dy=-14)
    mtext(f, h.P(0.25, m), lab(it('m'), ' = 4/3 − 2π/15'), size=12,
          color=ORANGE, dy=14)
    h.title(lab('(b) step 4: ', it('k'), ' &gt; ', it('m'), ' on [1/5, π/6]'))
    f.save('appendix-g/forward-bound', 'Left: the square of the source label l and '
           'the target label l′ split into the cases of the proof: l at least '
           '5/16 (blue), and for smaller l the turn z at least pi/4 (green, '
           'above a line of slope 1) or below pi/4 (orange). Right: the '
           'concave function k(x) = -4x/5 + sin x + cos x, in blue on '
           '[1/5, pi/6] and grey beyond, above the dashed level m = 4/3 - '
           '2 pi/15 at both ends')


# Figure: the capped triangle.

def capped():
    cap = CAP
    lo, hi = 0.575, 0.815
    f = Figure(lo, hi + 0.1, lo, hi, 1800)
    f.polygon([(lo, lo), (hi, hi), (lo, hi)], fill=GREY, stroke='none',
              opacity=0.6)
    f.polygon(cap, fill=FILLS[1], stroke=ORANGE, width=2)
    f.line((lo, PI / 5), (hi, PI / 5), stroke=ORANGE, width=1, dash='5 3')
    f.line(((7 - PI + 4 * lo) / 9, lo), ((7 - PI + 4 * hi) / 9, hi),
           stroke=ORANGE, width=1, dash='5 3')
    f.line((lo, lo), (hi, hi), width=1.3)
    f.line((axial_line(lo), lo), cap[1], stroke=PURPLE, width=1.3)
    p = (0.72, 0.672)
    assert label(*p) == PI / 4 and admissible(*p)
    for q in cap:
        assert abs(label(*q) - PI / 4) < 1e-12 and admissible(*q)
        f.line(p, q, stroke=INK, width=0.9, dash='3 3')
    f.dot(p, r=3.8)
    mtext(f, (p[0] - 0.005, p[1] + 0.002), lab('(', it('a'), ', ', it('u'),
                                               ')'), size=14, anchor='end')
    labels = [(sub('V', '0', size=14), (-0.008, 0.008), 'end'),
              (sub('V', '1', size=14), (-0.012, -0.012), 'end'),
              (sub('V', '2', size=14), (-0.009, 0.004), 'end')]
    for q, (s, off, anc) in zip(cap, labels):
        f.dot(q, r=4, fill=ORANGE)
        mtext(f, shift(q, off), s, size=14, anchor=anc, color=ORANGE)
    mtext(f, (0.8, PI / 5 + 0.008), lab(it('u'), ' = π/5'), size=12,
          color=ORANGE, anchor='end')
    mtext(f, (0.81, 0.785),
          lab('9', it('a'), ' − 4', it('u'), ' = 7 − π'), size=12,
          color=ORANGE)
    mtext(f, (0.66, 0.672), lab(it('u'), ' = ', it('a')), size=12,
          anchor='end')
    mtext(f, (0.59, 0.795), lab(it('u'), ' &gt; ', it('a'), ': no states'),
          size=12)
    mtext(f, (0.772, 0.588), 'tie line', size=12, color=PURPLE)
    mtext(f, (0.655, 0.6), 'axial', size=13, color=BLUE, anchor='middle')
    mtext(f, (0.8, 0.68), 'side', size=13, color=GREEN, anchor='middle')
    f.save('appendix-g/capped', 'The capped triangle with vertices V0, V1, V2, cut '
           'out by the line u = pi/5 where the axial label is pi/4, the line '
           '9a - 4u = 7 - pi where the side label is pi/4, and the diagonal '
           'u = a; a capped state (a, u) is a convex combination of the '
           'three vertices')


def main():
    pair_axes()
    support_bounds()
    regions()
    transition()
    axial_top_figure()
    parametrization()
    circle_functions()
    segments()
    slope()
    transition_pair()
    transition_profile()
    diagonal_profile()
    ratio()
    quintic_figure()
    targets()
    easy()
    forward_bound()
    capped()


if __name__ == '__main__':
    main()

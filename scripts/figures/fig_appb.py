#!/usr/bin/env python3
"""Draw the figures of Appendix B (docs/proof/appendix-b.md).

    python3 scripts/figures/fig_appb.py

The label regions, their boundary pieces, the profiles and the canonical pairs
are computed from the same formulas as the text: the labels of a state, the
circle phi = 13/4, the transition state and the diagonal corner, and the
support sums of a canonical pair at the gap pi/3.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, u, shift, sb)

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]


# The labels and the boundary of the label regions.

def axial(v):
    return 5 * v / 4


def side(a, v):
    return PI / 6 + (v - 0.5) / 3 + 3 * (1 - a) / 4


def label(a, v):
    return min(axial(v), side(a, v), PI / 4)


M = 2 * PI + 17
J = math.sqrt(202 * 13 / 4 - M ** 2)
X0, Y0 = (9 * M + 11 * J) / 202, (11 * M - 9 * J) / 202
A0, U0 = X0 - 0.5, Y0 - 0.5
S0 = 5 * U0 / 4
RD = math.sqrt(13 / 8) - 0.5
TD = PI / 6 + 7 / 12 - 5 * RD / 12
NN = 97 / 144
ROOT3 = math.sqrt(3)
CAP = [(PI / 5, PI / 5), ((7 - PI / 5) / 9, PI / 5),
       ((7 - PI) / 5, (7 - PI) / 5)]


def circle(v):
    return math.sqrt(13 / 4 - (v + 0.5) ** 2) - 0.5


def axial_line(v):
    return (2 * PI + 7 - 11 * v) / 9


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
        self.f.text(self.q(c), s, **kw)


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
        for p, q in zip(pts, pts[1:]):
            self.f.line(self.P(*p), self.P(*q), stroke=stroke, width=width,
                        dash=dash)

    def axes(self, xticks, yticks, xlabel, size=12):
        f = self.f
        f.line(self.P(self.x0, self.y0), self.P(self.x1, self.y0), width=1,
               arrow=True)
        f.line(self.P(self.x0, self.y0), self.P(self.x0, self.y1), width=1,
               arrow=True)
        for x, s in xticks:
            f.line(self.P(x, self.y0), shift(self.P(x, self.y0), (0, -0.06)),
                   width=1)
            f.text(shift(self.P(x, self.y0), (0, -0.2)), s, size=size,
                   italic=False)
        for y, s in yticks:
            f.line(self.P(self.x0, y), shift(self.P(self.x0, y), (-0.06, 0)),
                   width=1)
            f.text(shift(self.P(self.x0, y), (-0.1, 0)), s, size=size,
                   italic=False, anchor='end')
        f.text(shift(self.P(self.x1, self.y0), (0, 0.18)), xlabel,
               anchor='end')


def bracket(f, p, q, normal, text, color=ORANGE, size=15, off=0.15):
    """A measured interval from p to q with end ticks and a label beside it."""
    f.line(p, q, stroke=color, width=2.6)
    for r in (p, q):
        f.line(shift(r, normal, 0.07), shift(r, normal, -0.07), stroke=color,
               width=1.6)
    mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
    f.text(shift(mid, normal, off), text, size=size, color=color)


def canonical(a, v, s, A, w, t, gap=PI / 3):
    """The canonical pair: the centre of S, the centre of T and its turn d."""
    d = gap + s * label(a, v) - t * label(A, w)
    c = (A * math.cos(d) - t * w * math.sin(d),
         A * math.sin(d) + t * w * math.cos(d))
    return (a, s * v), c, d


def draw_pair(g, cs, ct, d, markers=True):
    S, T = square_corners(cs), square_corners(ct, math.degrees(d))
    g.arc((0, 0), 1.0, -0.5, 2.1, GREY, width=1.2)
    g.polygon(S, fill=FILLS[0], stroke=BLUE, opacity=0.85)
    g.polygon(T, fill=FILLS[2], stroke=GREEN, opacity=0.85)
    g.dot((0, 0))
    g.text((-0.06, -0.09), 'o', anchor='end', size=14)
    return S, T


# Figure: the four support sums of a canonical pair.

def pair_axes():
    a, v, A, w = 0.95, 0.35, 1.0, 0.2
    cs, ct, d = canonical(a, v, 1, A, w, 1)
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
        g.text((cs[0] + 0.3, cs[1] - 0.3), 'S', size=16, color=BLUE)
        g.text((ct[0] - 0.02, ct[1] + 0.2), 'T', size=16, color=GREEN)
        proj = lambda p: p[0] * n[0] + p[1] * n[1]
        ps, pt = [proj(p) for p in S], [proj(p) for p in T]
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
        g.text(shift(at(far + 0.3), side_dir, 0.17), sb('n', str(k), size=14),
               size=14)
        lo, hi = min(pt), max(ps)
        normal = (0, -1) if horizontal else (-1, 0)
        bracket(f, g.q(at(lo, -0.22)), g.q(at(hi, -0.22)), normal,
                sb('σ', str(k), size=15), off=0.18)
        pS = max(S, key=proj)
        pT = min(T, key=proj)
        for r, color in ((pS, BLUE), (pT, GREEN)):
            g.line(r, at(proj(r), -0.22), stroke=color, width=0.9, dash='2 3')
        g.text((0.2, 1.95), f'k = {k}: {names[k]} axis', size=13,
               italic=False)
    f.save('appb-pair-axes', 'A canonical pair of squares S and T at the gap '
           'pi/3, drawn once for each axis; in each panel the shadows of S '
           'and T on the line of the normal n_k, and the support sum sigma_k, '
           'the length from the lowest point of T to the highest point of S '
           'along n_k')


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
    for p, q in zip(pts, pts[1:]):
        f.line(p, q, width=1.5)
    f.line((0.5, 0), (0.5, 0.5), width=1.5)
    f.line((0.5, 0.5), (RD, RD), width=1.5)
    f.line((A0, U0), cap[1], stroke=PURPLE, width=1.8)
    f.line(cap[0], cap[1], stroke=ORANGE, width=1.5, dash='5 3')
    f.line(cap[1], cap[2], stroke=ORANGE, width=1.5, dash='5 3')
    f.line((0.5, 0), (ROOT3 - 0.5, 0), stroke=BLUE, width=4.5)
    f.line((0.36, 0), (1.32, 0), width=1, arrow=True)
    f.text((1.32, -0.035), 'a', anchor='end')
    f.line((0.4, -0.06), (0.4, 0.86), width=1, arrow=True)
    f.text((0.385, 0.85), 'u', anchor='end')
    for x, s in ((0.5, '½'), (1.0, '1'), (ROOT3 - 0.5, '√3 − ½')):
        f.line((x, 0), (x, -0.012), width=1)
        f.text((x, -0.042), s, size=12, italic=False)
    f.line((0.4, 0.5), (0.412, 0.5), width=1)
    f.text((0.39, 0.5), '½', size=12, italic=False, anchor='end')
    f.line((0.412, 0.5), (0.5, 0.5), stroke=FAINT, width=0.8, dash='2 3')
    f.dot((A0, U0), r=4, fill=PURPLE)
    f.text((A0 + 0.018, U0 + 0.012), '(' + sb('a', '0', ', ', 13)
           + sb('u', '0', ')', 13), size=13, anchor='start', color=PURPLE)
    f.dot((RD, RD), r=4)
    f.text((RD + 0.018, RD + 0.006), '(' + sb('r', 'd', ', ', 13)
           + sb('r', 'd', ')', 13), size=13, anchor='start')
    f.dot((1.0, 0.5), r=4, fill=GREEN)
    f.text((1.016, 0.512), '(1, ½)', size=13, italic=False, anchor='start',
           color=GREEN)
    for k, (p, off, anchor) in enumerate(((cap[0], (-0.014, 0.012), 'end'),
                                          (cap[1], (0.004, -0.03), 'middle'),
                                          (cap[2], (-0.016, 0.004), 'end'))):
        f.dot(p, r=3.4, fill=ORANGE)
        f.text(shift(p, off), sb('V', str(k), size=14), size=14,
               anchor=anchor, color=ORANGE)
    f.text((0.8, 0.22), 'axial', size=16, italic=False, color=BLUE)
    f.text((0.975, 0.6), 'side', size=16, italic=False, color=GREEN)
    f.text((0.57, 0.8), 'capped', size=14, italic=False, color=ORANGE)
    f.line((0.6, 0.785), (0.68, 0.7), stroke=ORANGE, width=0.8)
    f.text((0.87, -0.042), 'axial states (a, 0)', size=12, italic=False,
           color=BLUE)
    f.text((1.17, 0.38), 'φ = 13/4', size=13, anchor='start')
    f.text((0.585, 0.56), 'u = a', size=12, italic=False, anchor='end')
    f.text((0.9, 0.39), '9a + 11u = 2π + 7', size=12, italic=False,
           color=PURPLE, anchor='end')
    f.save('appb-regions', 'The admissible states in the (a, u)-plane, split '
           'into the axial, side and capped label regions by the tie line '
           '9a + 11u = 2 pi + 7 and the cap lines u = pi/5 and '
           '9a - 4u = 7 - pi, with the transition state (a0, u0), the '
           'diagonal corner (rd, rd), the side state (1, 1/2), the axial '
           'states (a, 0) and the vertices V0, V1, V2 of the capped triangle')


# Figure: the circle parametrised by the side label.

def parametrisation():
    R = math.sqrt(13) / 2
    rn = math.sqrt(NN)
    e = (0.75 / rn, -1 / (3 * rn))
    g = (1 / (3 * rn), 0.75 / rn)
    f = Figure(-0.35, 2.05, -0.75, 2.0, 230)
    t = 0.6
    P = (X(t), Y(t))
    # the quarter circle and the arc of the parametrisation
    pts = [u(k * PI / 2 / 120) for k in range(121)]
    for p, q in zip(pts, pts[1:]):
        f.line(shift((0, 0), p, R), shift((0, 0), q, R), stroke=INK, width=1.3)
    t0, t1 = math.atan2(Y0, X0), PI / 4
    f.arc((0, 0), R, t0, t1, GREEN, width=5)
    f.line((0, 0), (1.95, 1.95), stroke=FAINT, width=1, dash='4 3')
    f.text((1.9, 1.98), 'X = Y', size=12, italic=False, anchor='end',
           color=FAINT)
    # the line of side label t: 3X/4 - Y/3 = D(t)
    foot = shift((0, 0), e, D(t) / rn)
    f.line(shift(foot, g, -0.55), shift(foot, g, 2.05), stroke=PURPLE,
           width=1.6)
    f.text(shift(foot, g, -0.5), '3X/4 − Y/3 = D(τ)', size=12, italic=False,
           color=PURPLE, anchor='start', dx=8)
    # the orthogonal frame and the coordinates of P
    f.line((0, 0), shift((0, 0), e, 0.34), width=1.6, arrow=True)
    f.line((0, 0), shift((0, 0), g, 0.34), width=1.6, arrow=True)
    f.text(shift((0, 0), e, 0.3), '(3/4, −1/3)', size=12, italic=False,
           anchor='end', dy=16)
    f.text(shift((0, 0), g, 0.36), '(1/3, 3/4)', size=12, italic=False,
           anchor='end', dx=-6)
    f.line((0, 0), foot, stroke=ORANGE, width=2.4)
    f.line(foot, P, stroke=BLUE, width=2.4)
    f.text(shift(shift((0, 0), e, D(t) / rn / 2), g, -0.09),
           'D(τ)/√N', size=13, color=ORANGE)
    f.text(shift(shift(foot, g, Z(t) / rn / 2), e, 0.1), 'Z(τ)/√N',
           size=13, color=BLUE, anchor='start')
    f.dot(P, r=4, fill=GREEN)
    f.text(shift(P, (0.05, 0.06)), '(X(τ), Y(τ))', size=13, anchor='start')
    f.dot((X0, Y0), r=3.6, fill=PURPLE)
    f.text((X0 + 0.05, Y0 - 0.06), '(' + sb('X', '0', ', ', 13)
           + sb('Y', '0', ')', 13), size=13, anchor='start', color=PURPLE)
    f.dot((RD + 0.5, RD + 0.5), r=3.6)
    f.text((RD + 0.42, RD + 0.58), '(' + sb('r', 'd', ' + ½, ', 13)
           + sb('r', 'd', ' + ½)', 13), size=13, anchor='end')
    f.dot((0, 0))
    f.text((-0.04, -0.07), '0', anchor='end', size=13, italic=False)
    f.line((-0.3, 0), (2.0, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, -0.7), (0, 1.95), stroke=FAINT, width=1, arrow=True)
    f.text((2.0, -0.07), 'X', anchor='end', color=FAINT)
    f.text((0.06, 1.93), 'Y', anchor='start', color=FAINT)
    f.text((1.35, 0.5), 'X² + Y² = 13/4', size=13, italic=False,
           anchor='start')
    f.save('appb-parametrisation', 'The circle X^2 + Y^2 = 13/4 in the '
           'coordinates X = a + 1/2, Y = u + 1/2, a line of constant side '
           'label, 3X/4 - Y/3 = D(tau), and the orthogonal frame of the '
           'vectors (3/4, -1/3) and (1/3, 3/4); the point (X(tau), Y(tau)) '
           'where the line meets the circle, with its coordinates D/root N '
           'and Z/root N in that frame; the arc it sweeps as tau runs from s0 '
           'to td, from (X0, Y0) to the diagonal')


# Figure: segments of constant side label.

def segments():
    _, side_reg, cap = region_polygons()
    f = Figure(0.62, 1.3, 0.23, 0.83, 740)
    f.polygon(side_reg, fill=FILLS[2], stroke='none')
    f.polygon(cap, fill=FILLS[1], stroke='none')
    pts = [(circle(v), v) for v in grid(0.24, RD, 160)]
    for p, q in zip(pts, pts[1:]):
        f.line(p, q, width=1.5)
    f.line((0.635, 0.635), (RD, RD), width=1.5)
    f.line((A0, U0), cap[1], stroke=PURPLE, width=1.8)
    f.line((A0, U0), (axial_line(0.25), 0.25), stroke=PURPLE, width=1,
           dash='2 3')
    f.line(cap[0], cap[1], stroke=ORANGE, width=1.5, dash='5 3')
    taus = [(0.42, '0.42'), (0.48, '0.48'), (PI / 6, 'π/6'), (0.6, '0.6'),
            (0.66, '0.66'), (0.72, '0.72'), (TD, None), (0.765, None),
            (PI / 4, 'π/4')]
    for t, s in taus:
        p, q = (tie_a(t), 0.8 * t), side_top(t)
        f.line(p, q, stroke=GREEN if t < PI / 4 else ORANGE,
               width=1.6 if t < PI / 4 else 2)
        f.dot(p, r=2.6, fill=PURPLE)
        f.dot(q, r=2.6, fill=INK)
        if s and t < PI / 4:
            f.text(shift(p, (-0.012, -0.012)), s, size=12, italic=False,
                   anchor='end', color=GREEN)
        elif s:
            mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
            f.text(shift(mid, (-0.012, 0.01)), s, size=12, italic=False,
                   anchor='end', color=ORANGE)
    f.dot((A0, U0), r=4.2, fill=PURPLE)
    f.text((A0 + 0.014, U0 + 0.004), '(' + sb('a', '0', ', ', 13)
           + sb('u', '0', ')', 13) + ', τ = ' + sb('s', '0', size=13),
           size=13, anchor='start', color=PURPLE)
    f.dot((RD, RD), r=4.2)
    f.text((RD + 0.014, RD + 0.004), '(' + sb('r', 'd', ', ', 13)
           + sb('r', 'd', ')', 13) + ', τ = ' + sb('t', 'd', size=13),
           size=13, anchor='start')
    f.dot((1.0, 0.5), r=4.2, fill=GREEN)
    f.text((1.014, 0.505), '(1, ½)', size=13, italic=False, anchor='start',
           color=GREEN)
    f.text((1.12, 0.62), 'φ = 13/4', size=13, anchor='start')
    f.text((0.69, 0.73), 'u = a', size=12, italic=False, anchor='end')
    f.text((0.9, 0.3), 'tie line 9a + 11u = 2π + 7', size=12, italic=False,
           color=PURPLE, anchor='start')
    f.text((CAP[1][0] - 0.006, CAP[1][1] - 0.02), sb('V', '1', size=13),
           size=13, color=ORANGE, anchor='end')
    f.text((CAP[2][0] - 0.01, CAP[2][1] + 0.012), sb('V', '2', size=13),
           size=13, color=ORANGE, anchor='end')
    f.line((0.63, 0.25), (1.29, 0.25), width=1, arrow=True)
    f.text((1.29, 0.232), 'a', anchor='end')
    f.line((0.64, 0.24), (0.64, 0.82), width=1, arrow=True)
    f.text((0.652, 0.815), 'u', anchor='start')
    f.save('appb-segments', 'The side region foliated by the segments of '
           'constant side label tau, of slope 9/4 in the (a, u)-plane; each '
           'runs from the tie line up to the circle phi = 13/4 or, beyond the '
           'diagonal corner, to the diagonal u = a; the segment of label '
           'pi/6 ends at the side state (1, 1/2) and the segment of label '
           'pi/4 is the edge V1 V2 of the capped triangle')


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
    f.line((axial_line(lo), lo), (axial_line(0.66), 0.66), stroke=PURPLE,
           width=1.3)
    p = (0.715, 0.69)
    for q in cap:
        f.line(p, q, stroke=INK, width=0.9, dash='3 3')
    f.dot(p, r=3.8)
    f.text((p[0] + 0.005, p[1] + 0.008), '(a, u)', size=14, anchor='start')
    labels = [(sb('V', '0', size=14), (-0.006, 0.008), 'end'),
              (sb('V', '1', size=14), (0.008, -0.01), 'start'),
              (sb('V', '2', size=14), (-0.008, 0.004), 'end')]
    for q, (s, off, anc) in zip(cap, labels):
        f.dot(q, r=4, fill=ORANGE)
        f.text(shift(q, off), s, size=14, anchor=anc, color=ORANGE)
    f.text((0.8, PI / 5 + 0.008), 'u = π/5', size=12, italic=False,
           color=ORANGE, anchor='end')
    f.text((0.845, 0.765), '9a − 4u = 7 − π', size=12, italic=False,
           color=ORANGE, anchor='middle')
    f.text((0.66, 0.672), 'u = a', size=12, italic=False, anchor='end')
    f.text((0.59, 0.795), 'u &gt; a: no states', size=12, italic=False,
           anchor='start')
    f.text((0.7, 0.595), 'tie line', size=12, italic=False, color=PURPLE,
           anchor='start')
    f.text((0.655, 0.6), 'axial', size=13, italic=False, color=BLUE)
    f.text((0.8, 0.68), 'side', size=13, italic=False, color=GREEN)
    f.save('appb-capped', 'The capped triangle with vertices V0, V1, V2, cut '
           'out by the line u = pi/5 where the axial label is pi/4, the line '
           '9a - 4u = 7 - pi where the side label is pi/4, and the diagonal '
           'u = a; a capped state (a, u) is a convex combination of the '
           'three vertices')


# Figure: profiles along the boundary.

def transition_F(t):
    ang = PI / 3 - t + S0
    top = Y(t) if t <= TD else diagonal(t) + 0.5
    return 1 - top - (A0 - 0.5) * math.sin(ang) + Y0 * math.cos(ang)


def transition_dF(t, h=1e-6):
    return (transition_F(t + h) - transition_F(t - h)) / (2 * h)


def diagonal_K(t):
    return (6 / 5 * (PI / 6 - t) + 51 / 40 * math.cos(7 * PI / 12 - t)
            - 11 / 40 * math.sin(7 * PI / 12 - t))


def profiles():
    f = Figure(0, 10.0, 0, 4.0, 70)
    g = Plot(f, (0.9, 0.7, 4.3, 2.9), (0.38, 0.81), (-0.004, 0.056))
    g.axes([(0.4, '2/5'), (0.72, '18/25'), (PI / 4, 'π/4')],
           [(0, '0'), (0.05, '0.05')], 'τ')
    f.line(g.P(TD, -0.004), g.P(TD, 0.05), stroke=FAINT, width=0.8,
           dash='2 3')
    f.text(shift(g.P(TD, 0.05), (0, 0.14)), sb('t', 'd', size=12), size=12)
    tp = 0.72
    F0, F1 = transition_F(tp), transition_dF(tp)
    par = [(x, F0 + F1 * (x - tp) + 3 / 16 * (x - tp) ** 2)
           for x in grid(0.4, TD, 100)]
    g.curve(par, stroke=ORANGE, width=1.4, dash='5 3')
    g.curve([(x, transition_F(x)) for x in grid(0.4, TD, 200)], stroke=BLUE,
            width=2.2)
    g.curve([(x, transition_F(x)) for x in grid(TD, PI / 4, 40)],
            stroke=GREEN, width=2.6)
    f.dot(g.P(tp, F0), r=3.4)
    f.text(shift(g.P(0.47, 0.034), (0.05, 0)), 'F', size=15, color=BLUE,
           anchor='start')
    f.text(shift(g.P(0.43, 0.006), (0, 0)), 'parabola', size=12,
           italic=False, color=ORANGE, anchor='start')
    f.text(shift(g.P(PI / 4, transition_F(PI / 4)), (0.08, 0.18)),
           sb('F', 'δ', size=14), size=14, color=GREEN, anchor='start')
    f.text(shift(g.P(0.38, 0.056), (0.1, 0.25)),
           '(a) the transition profile', size=13, italic=False,
           anchor='start')
    h = Plot(f, (6.1, 0.7, 3.4, 2.9), (0.38, 0.81), (0.0, 0.1))
    h.axes([(0.4, '2/5'), (PI / 4, 'π/4')],
           [(0, '0'), (0.05, '0.05'), (0.1, '0.1')], 'ℓ')
    h.curve([(x, diagonal_K(x)) for x in grid(0.4, PI / 4, 100)],
            stroke=BLUE, width=2.2)
    f.line(h.P(0.4, 361 / 8000), h.P(0.52, 361 / 8000), stroke=ORANGE,
           width=1.4, dash='4 3')
    f.text(shift(h.P(0.52, 361 / 8000), (0.06, 0)), '361/8000', size=12,
           italic=False, color=ORANGE, anchor='start')
    f.text(shift(h.P(0.6, 0.075), (0, 0.12)), 'K', size=15, color=BLUE)
    f.text(shift(h.P(0.38, 0.1), (0.1, 0.25)), '(b) the diagonal profile',
           size=13, italic=False, anchor='start')
    f.save('appb-profiles', 'Left: the transition profile F on [2/5, td] '
           '(blue) and its continuation along the diagonal on [td, pi/4] '
           '(green), above the parabola of curvature 3/8 through the point '
           'of abscissa 18/25. Right: the profile K, increasing on '
           '[2/5, pi/4] from a value above 361/8000')


# Figure: the target support on the axial boundary.

def xi(s):
    return math.sqrt(13 / 4 - (0.5 + 0.8 * s) ** 2)


def eta(s):
    return 0.5 + 0.8 * s


def circle_target(t, s):
    ang = PI / 3 - t + s
    return -(xi(s) - 1) * math.sin(ang) + eta(s) * math.cos(ang)


def line_target(t, s):
    ang = PI / 3 - t + s
    return -(tie_a(s) - 0.5) * math.sin(ang) + (0.8 * s + 0.5) * math.cos(ang)


OMEGA = math.atan(9 / 4)


def targets():
    f = Figure(0, 7.8, 0, 4.7, 80)
    g = Plot(f, (0.8, 0.75, 5.6, 3.5), (0, 0.82), (-0.14, 0.34))
    g.axes([(0, '0'), (S0, sb('s', '0', size=12)), (PI / 4, 'π/4')],
           [(0, '0'), (0.2, '0.2')], 'ℓ′')
    f.line(g.P(S0, -0.14), g.P(S0, 0.34), stroke=FAINT, width=0.8,
           dash='2 3')
    f.line(g.P(0, 0), g.P(0.82, 0), stroke=FAINT, width=0.8)
    for k, (t, name) in enumerate(((0.4, '2/5'), (0.55, '0.55'),
                                   (0.7, '0.7'), (PI / 4, 'π/4'))):
        color = COLORS[k]
        g.curve([(s, circle_target(t, s)) for s in grid(0, S0, 80)],
                stroke=color, width=2.2)
        top = min(PI / 4, OMEGA - PI / 3 + t)
        g.curve([(s, line_target(t, s)) for s in grid(S0, top, 80)],
                stroke=color, width=2.2, dash='6 3')
        f.dot(g.P(S0, circle_target(t, S0)), r=3.2, fill=color)
        f.dot(g.P(top, line_target(t, top)), r=2.6, fill=color)
        f.text(shift(g.P(top, line_target(t, top)), (0.1, 0)),
               'ℓ = ' + name, size=12, italic=False, anchor='start',
               color=color)
    f.text(g.P(0.16, -0.115), 'C(ℓ, ℓ′)', size=13)
    f.text(g.P(0.56, -0.115), 'L(ℓ, ℓ′)', size=13)
    f.save('appb-targets', 'The target support along the axial boundary as '
           'a function of the target label, for four source labels: '
           'decreasing along the circular piece up to s0 (solid) and '
           'increasing along the tie line from s0 up to the switch label or '
           'pi/4 (dashed)')


# Figure: the quintic and the derivative ratio (Lemma B.22).

def quintic(x):
    return (-500 * x ** 5 + 800 * x ** 4 + 1705 * x ** 3 - 3900 * x ** 2
            + 3120 * x - 1872)


def ratio_rho(s):
    return xi(s) * (9 / 5 - xi(s)) / (eta(s) * (xi(s) - 4 / 5))


def ratio():
    f = Figure(0, 10.0, 0, 4.0, 70)
    # (a) The quintic is concave on [8/5, 7/4], so above its chord.
    lo, hi = 8 / 5, 7 / 4

    def chord(x):
        return ((hi - x) * quintic(lo) + (x - lo) * quintic(hi)) / (hi - lo)
    assert quintic(lo) > 0 and quintic(hi) > 0
    assert all(quintic(x) > chord(x) - 1e-9 for x in grid(lo, hi, 300))
    g = Plot(f, (0.9, 0.7, 4.0, 2.9), (1.56, 1.8), (0, 150))
    g.axes([(lo, '8/5'), (hi, '7/4')],
           [(0, '0'), (50, '50'), (100, '100'), (150, '150')], 'X')
    for x in (lo, hi):
        f.line(g.P(x, 0), g.P(x, quintic(x)), stroke=FAINT, width=0.8,
               dash='2 3')
    g.curve([(x, quintic(x)) for x in grid(1.57, lo, 20)], stroke=FAINT,
            width=1.6)
    g.curve([(x, quintic(x)) for x in grid(hi, 1.78, 20)], stroke=FAINT,
            width=1.6)
    g.curve([(lo, quintic(lo)), (hi, quintic(hi))], stroke=ORANGE, width=2)
    g.curve([(x, quintic(x)) for x in grid(lo, hi, 120)], stroke=BLUE,
            width=2.4)
    for x, s, dx, anchor in ((lo, '2992/25', 0.12, 'start'),
                             (hi, '20113/256', -0.12, 'end')):
        f.dot(g.P(x, quintic(x)), r=3.4, fill=ORANGE)
        f.text(shift(g.P(x, quintic(x)), (dx, -0.38)), s, size=12,
               italic=False, color=ORANGE, anchor=anchor)
    f.text(shift(g.P(1.675, quintic(1.675)), (0, 0.2)), 'P', size=15,
           color=BLUE)
    f.text(shift(g.P(1.675, (quintic(lo) + quintic(hi)) / 2), (0, -0.2)),
           'chord', size=12, italic=False, color=ORANGE)
    f.text(shift(g.P(1.56, 150), (0.1, 0.25)), '(a) the quintic P',
           size=13, italic=False, anchor='start')
    # (b) For the source label pi/4 the ratio stays below tan d.
    assert ratio_rho(0) < 2 - ROOT3
    assert all(ratio_rho(s) < math.tan(PI / 12 + s) for s in grid(0, S0))
    h = Plot(f, (6.1, 0.7, 3.4, 2.9), (0, 0.42), (0.2, 0.8))
    h.axes([(0, '0'), (S0, sb('s', '0', size=12))],
           [(0.4, '0.4'), (0.6, '0.6'), (0.8, '0.8')], 'ℓ′')
    f.line(h.P(S0, 0.2), h.P(S0, math.tan(PI / 12 + S0)), stroke=FAINT,
           width=0.8, dash='2 3')
    h.curve([(s, math.tan(PI / 12 + s)) for s in grid(0, S0, 80)],
            stroke=ORANGE, width=2.2)
    h.curve([(s, ratio_rho(s)) for s in grid(0, S0, 80)], stroke=BLUE,
            width=2.2)
    f.dot(h.P(0, 2 - ROOT3), r=3.2, fill=ORANGE)
    f.dot(h.P(0, ratio_rho(0)), r=3.2, fill=BLUE)
    f.text(shift(h.P(0, 2 - ROOT3), (-0.12, 0.13)), '2 − √3', size=12,
           italic=False, color=ORANGE, anchor='end')
    f.text(shift(h.P(0, ratio_rho(0)), (-0.12, -0.13)), 'ρ(0)', size=12,
           color=BLUE, anchor='end')
    f.text(shift(h.P(S0, math.tan(PI / 12 + S0)), (0.1, 0)), 'tan d',
           size=13, color=ORANGE, anchor='start')
    f.text(shift(h.P(S0, ratio_rho(S0)), (0.1, 0)), 'ρ', size=15,
           color=BLUE, anchor='start')
    f.text(shift(h.P(0, 0.8), (0.1, 0.25)), '(b) ρ and tan d, for ℓ = π/4',
           size=13, italic=False, anchor='start')
    f.save('appb-ratio', 'Left: the quintic P on [8/5, 7/4], concave and '
           'above its chord through the positive end values 2992/25 and '
           '20113/256. Right: for the source label pi/4, the ratio rho on '
           '[0, s0] below tan d with d = pi/12 + l′; at 0 it starts at '
           'rho(0), just below 2 - root 3 = tan(pi/12)')


# Figure: the easy sectors.

def easy():
    W, H = 3.25, 3.35
    f = Figure(0, 2 * W, 0, 2 * H, 104)
    titles = ['(a) outward axis', '(b) backward axis, s = 1',
              '(c) inward axis, s = −1', '(d) forward axis, s = t = 1']
    configs = [((1.0, 0.5, 1), (1.0, 0.0, 1)), ((1.0, 0.5, 1), (1.0, 0.0, 1)),
               ((1.0, 0.5, -1), (1.0, 0.5, 1)),
               ((0.95, 0.35, 1), (1.0, 0.2, 1))]
    for k, ((a, v, s), (A, w, t)) in enumerate(configs):
        col, row = k % 2, 1 - k // 2
        g = Shifted(f, col * W + 1.5, row * H + 1.4)
        cs, ct, d = canonical(a, v, s, A, w, t)
        S, T = draw_pair(g, cs, ct, d)
        ls, lt = s * label(a, v), d + t * label(A, w)
        g.text(shift(cs, (0.32, -0.3)), 'S', size=15, color=BLUE)
        g.text(shift(ct, (-0.3, 0.3)), 'T', size=15, color=GREEN)
        g.text((0.2, 1.78), titles[k], size=13, italic=False)
        if k == 0:
            g.circle((0, 0), 31 / 25, stroke=INK, width=1, dash='5 4')
            g.line((37 / 50, -1.2), (37 / 50, 1.55), stroke=ORANGE, width=1.2,
                   dash='4 3')
            g.text((37 / 50 + 0.04, -1.15), 'x = 37/50', size=11,
                   italic=False, color=ORANGE, anchor='start')
            g.line((a + 0.5, -1.2), (a + 0.5, 1.2), stroke=BLUE, width=1.2,
                   dash='4 3')
            g.text((a + 0.5, 1.28), 'x = a + ½', size=11, italic=False,
                   color=BLUE)
            g.dot(ct, r=3, fill=GREEN)
            g.text((-1.3, 0.95), '|c| &lt; 31/25', size=11, italic=False,
                   anchor='start')
            left = min(T, key=lambda p: p[0])
            g.dot(left, r=3.4, fill=GREEN)
            bracket(f, g.q((left[0], -0.82)), g.q((a + 0.5, -0.82)), (0, -1),
                    sb('σ', '0', size=14), off=0.16)
            g.line(left, (left[0], -0.82), stroke=GREEN, width=0.9,
                   dash='2 3')
        elif k == 1:
            m = u(lt)
            g.line((0, 0), m, stroke=GREEN, width=1, dash='3 3')
            g.dot(m, r=3.6, fill=GREEN)
            g.text(shift(m, (-0.1, 0.08)), 'marker of T', size=11,
                   italic=False, color=GREEN, anchor='end')
            y0 = s * v - 0.5
            g.line((-0.9, y0), (1.7, y0), stroke=BLUE, width=1.2, dash='4 3')
            g.text((-0.9, y0 - 0.12), 'y = u − ½', size=11, italic=False,
                   color=BLUE, anchor='start')
            g.line((m[0] + 0.02, m[1]), (m[0] + 0.02, y0), stroke=ORANGE,
                   width=2.2)
            g.text((m[0] + 0.1, (m[1] + y0) / 2 - 0.2), '≤ ' +
                   sb('σ', '3', size=13), size=13, color=ORANGE,
                   anchor='start')
        elif k == 2:
            half = 801 / 1600
            g.arc((0, 0), 1.0, lt - half, lt + half, GREEN, width=4.5)
            y = lt - half
            p = u(y)
            g.dot(p, r=3.6, fill=GREEN)
            g.line((0, 0), p, stroke=GREEN, width=1, dash='3 3')
            g.line((a - 0.5, -1.2), (a - 0.5, 1.5), stroke=BLUE, width=1.2,
                   dash='4 3')
            g.text((a - 0.5 - 0.04, 1.4), 'x = a − ½', size=11, italic=False,
                   color=BLUE, anchor='end')
            g.line((a - 0.5, p[1] + 0.03), (p[0], p[1] + 0.03),
                   stroke=ORANGE, width=2.2)
            g.text(((a - 0.5 + p[0]) / 2, p[1] + 0.17),
                   '≤ ' + sb('σ', '2', size=13), size=13, color=ORANGE)
            g.text(shift(u(lt + half), (-0.1, 0.12)), 'marker arc of T',
                   size=11, italic=False, color=GREEN, anchor='end')
        else:
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
                    sb('σ', '1', size=14), off=0.18)
            for r, color in ((max(S, key=lambda q: q[1]), BLUE),
                             (min(T, key=lambda q: q[1]), GREEN)):
                g.line(r, (base - 0.22, r[1]), stroke=color, width=0.9,
                       dash='2 3')
        g.line((0, 0), u(ls), stroke=BLUE, width=1, dash='3 3')
        g.dot(u(ls), r=2.6, fill=BLUE)
    f.save('appb-easy', 'The four easy sectors: (a) T has a point left of '
           'x = 37/50 while S reaches x = a + 1/2; (b) the marker point of T '
           'lies above the lower edge of S; (c) the marker arc of T reaches '
           'past the near edge of S; (d) the shadows of S and T on the '
           'forward axis overlap')


def main():
    pair_axes()
    regions()
    parametrisation()
    segments()
    capped()
    profiles()
    targets()
    ratio()
    easy()


if __name__ == '__main__':
    main()

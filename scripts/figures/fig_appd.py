#!/usr/bin/env python3
"""Draw the figures of Appendix D (docs/proof/appendix-d.md), six squares: the
wings, in docs/proof/figures/appendix-d/.

    python3 scripts/figures/fig_appd.py

Every figure is computed from the definitions of the appendix: the separating
inequalities (D.1) to (D.9) of wing data, the weights and forces of the
stresses, the chord term, the bound of the phase gap, the one-variable bounds
of the lemmas, and the profiles of the cases with the values of their Taylor
bounds at the corners. The configurations of the cases are the ones whose
squares W, D and S lie in the smallest disk about the origin, for given angles
and the separations of the case: for fixed angles the separations are linear
in the coordinates, so this is a convex problem, solved here by a logarithmic
barrier and Newton steps.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY, clip,
                           square_corners, u, shift, sb, subsup)
from fig_front import it

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN, YELLOW = COLORS
MINUS = '−'
Q0 = 2.85118
R0 = math.sqrt(Q0)
RHO0 = math.sqrt(Q0 - 0.25) - 0.5
C0 = RHO0 - 1
RB, RHOB, CB = 1.6886, 1.11282, 0.11282
MUM, MUP = 0.5 - CB, 0.5 + CB

# The squares: colours and the model of Theorem 9.1.
SQUARE = {'C': (INK, GREY), 'W': (BLUE, FILLS[0]), 'D': (PURPLE, FILLS[3]),
          'S': (GREEN, FILLS[2])}
H = math.sqrt(2) / 2
_A = (1466 + 1940 * H) / 267
_B = (327 + 432 * H) / 712
S_STAR = 2 * _B / (_A + math.sqrt(_A * _A - 4 * _B))
T_STAR = (30 * H - 20) * S_STAR + 3.5 - 4.5 * H
D_STAR = 0.5 + H - T_STAR
R6 = math.sqrt(2 * S_STAR ** 2 + 4 * S_STAR + 2.5)

# Taylor polynomials of the appendix.


def C4(x):
    return 1 - x ** 2 / 2 + x ** 4 / 24


def C6(x):
    return C4(x) - x ** 6 / 720


def S5(x):
    return x - x ** 3 / 6 + x ** 5 / 120


def S7(x):
    return S5(x) - x ** 7 / 5040


def save(f, name, title):
    assert name.startswith('appendix-d/'), name
    title = (title.replace('&', '&amp;').replace('<', '&lt;')
             .replace('>', '&gt;'))
    f.save(name, title)


def num(x, digits):
    """A number with a true minus sign."""
    return f'{x:.{digits}f}'.replace('-', MINUS)


def tag(n):
    return f'(D.{n})'


def omega(x):
    return 0.5 * (abs(math.cos(x)) + abs(math.sin(x)))


def tau(x):
    return 0.5 + omega(x)


# Wing data: x = (cx, cy, aW, bW, aD, bD, aS, bS) at the angles (v, s, d).

def separations(v, s, d):
    """The separating inequalities (D.1) to (D.9) as coef . x >= threshold."""
    q, r = d + v, d - s
    c, sn = math.cos, math.sin
    return {
        1: ([c(d), sn(d), 0, 0, 1, 0, 0, 0], tau(d)),
        2: ([c(v), -sn(v), 1, 0, 0, 0, 0, 0], tau(v)),
        3: ([1, 0, c(v), sn(v), 0, 0, 0, 0], tau(v)),
        4: ([-sn(s), c(s), 0, 0, 0, 0, 1, 0], tau(s)),
        5: ([0, 1, 0, 0, 0, 0, c(s), -sn(s)], tau(s)),
        6: ([0, 0, 0, -1, sn(q), c(q), 0, 0], tau(q)),
        7: ([0, 0, sn(q), -c(q), 0, 1, 0, 0], tau(q)),
        8: ([0, 0, 0, 0, c(r), -sn(r), 0, 1], tau(r)),
        9: ([0, 0, 0, 0, 0, -1, c(r), sn(r)], tau(r)),
    }


def gauss(A, b):
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(M[i][k]))
        M[k], M[p] = M[p], M[k]
        for i in range(k + 1, n):
            f = M[i][k] / M[k][k]
            for j in range(k, n + 1):
                M[i][j] -= f * M[k][j]
    x = [0.0] * n
    for i in reversed(range(n)):
        x[i] = (M[i][n] - sum(M[i][j] * x[j] for j in range(i + 1, n))) / M[i][i]
    return x


def smallest(names, v, s, d):
    """Wing data with the separations `names` (and (D.1)) at the angles
    (v, s, d) whose squares W, D, S lie in the smallest disk about the origin.
    Minimizes t = R^2 under the linear separations, the box of C, the chart
    conditions and the far corners (a + 1/2)^2 + (|b| + 1/2)^2 <= t."""
    sep = separations(v, s, d)
    lin = [(sep[k][0] + [0], sep[k][1]) for k in sorted(set(names) | {1})]

    def e(i, k=1.0):
        return [k if j == i else 0 for j in range(9)]
    lin += [(e(0), 0), (e(1), 0), (e(0, -1), -C0), (e(1, -1), -C0)]
    for i in (2, 4, 6):
        lin += [(e(i), 0.5),
                ([1 if j == i else (-1 if j == i + 1 else 0)
                  for j in range(9)], 0),
                ([1 if j in (i, i + 1) else 0 for j in range(9)], 0)]
    quad = [(i, sg) for i in (2, 4, 6) for sg in (1, -1)]

    def values(y):
        g = [sum(a * b for a, b in zip(coef, y)) - rhs for coef, rhs in lin]
        g += [y[8] - (y[i] + 0.5) ** 2 - (sg * y[i + 1] + 0.5) ** 2
              for i, sg in quad]
        return g

    def barrier(z, mu):
        return mu * z[8] - sum(math.log(x) for x in values(z))
    y = [C0 / 2, C0 / 2, 3, 0, 3, 0, 3, 0, 40]
    for mu in [10.0 ** k for k in range(10)]:
        for _ in range(60):
            g = values(y)
            grad = [0.0] * 9
            grad[8] = mu
            Hm = [[0.0] * 9 for _ in range(9)]
            terms = [(coef, gv) for (coef, _), gv in zip(lin, g)]
            for (i, sg), gv in zip(quad, g[len(lin):]):
                dg = [0.0] * 9
                dg[8], dg[i] = 1, -2 * (y[i] + 0.5)
                dg[i + 1] = -2 * sg * (sg * y[i + 1] + 0.5)
                terms.append((dg, gv))
                Hm[i][i] += 2 / gv
                Hm[i + 1][i + 1] += 2 / gv
            for dg, gv in terms:
                for a in range(9):
                    grad[a] -= dg[a] / gv
                    for b in range(9):
                        Hm[a][b] += dg[a] * dg[b] / gv ** 2
            dy = gauss(Hm, [-x for x in grad])
            dec = -sum(a * b for a, b in zip(grad, dy))
            if dec < 1e-12:
                break
            f0, al = barrier(y, mu), 1.0
            while True:
                z = [a + al * b for a, b in zip(y, dy)]
                if min(values(z)) > 0 and barrier(z, mu) <= f0 - 0.25 * al * dec:
                    break
                al /= 2
            y = z
    return y[:8], math.sqrt(y[8])


class Wings:
    """The squares and the frames of wing data."""

    def __init__(self, v, s, d, x):
        self.v, self.s, self.d = v, s, d
        self.cx, self.cy, aW, bW, aD, bD, aS, bS = x
        self.t = {'W': PI - v, 'D': PI + d, 'S': 1.5 * PI + s, 'C': 0.0}
        self.c = {'C': (self.cx, self.cy)}
        for k, (a, b) in (('W', (aW, bW)), ('D', (aD, bD)), ('S', (aS, bS))):
            t = self.t[k]
            self.c[k] = (a * math.cos(t) - b * math.sin(t),
                         a * math.sin(t) + b * math.cos(t))

    def corners(self, k):
        return square_corners(self.c[k], math.degrees(self.t[k]))

    def e1(self, k):
        return u(self.t[k])

    def e2(self, k):
        return u(self.t[k] + PI / 2)

    def inside(self, p, k, tol=0.0):
        """Whether p lies in the open square k, deeper than tol."""
        dx, dy = p[0] - self.c[k][0], p[1] - self.c[k][1]
        e1, e2 = self.e1(k), self.e2(k)
        return (abs(dx * e1[0] + dy * e1[1]) < 0.5 - tol and
                abs(dx * e2[0] + dy * e2[1]) < 0.5 - tol)

    def edge(self, n):
        """The edge of the separating inequality (D.n): source, target and
        unit normal in the standard frame."""
        return {1: ('C', 'D', self.e1('D')), 2: ('C', 'W', self.e1('W')),
                3: ('C', 'W', (-1.0, 0.0)), 4: ('C', 'S', self.e1('S')),
                5: ('C', 'S', (0.0, -1.0)), 6: ('W', 'D', self.e2('W')),
                7: ('W', 'D', self.e2('D')), 8: ('D', 'S', self.e2('S')),
                9: ('D', 'S', self.e2('D'))}[n]

    def forces(self, weights):
        F = {k: [0.0, 0.0] for k in 'CWDS'}
        for n, lam in weights.items():
            a, b, nv = self.edge(n)
            for i in range(2):
                F[b][i] += lam * nv[i]
                F[a][i] -= lam * nv[i]
        return F


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


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

    def dot(self, c, **kw):
        self.f.dot(self.q(c), **kw)

    def text(self, c, s, **kw):
        self.f.text(self.q(c), s, **kw)

    def arc(self, r, t0, t1, stroke=INK, width=1.2, dash=None, c=(0.0, 0.0)):
        """The arc of the circle of radius r about c, as one path."""
        n = max(8, int(60 * abs(t1 - t0)))
        pts = [self.f.p(*self.q((c[0] + r * math.cos(t0 + (t1 - t0) * k / n),
                                 c[1] + r * math.sin(t0 + (t1 - t0) * k / n))))
               for k in range(n + 1)]
        d = 'M ' + ' L '.join(f'{x:.1f} {y:.1f}' for x, y in pts)
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.f.add(f'<path d="{d}" fill="none" stroke="{stroke}" '
                   f'stroke-width="{width}"{extra}/>')


class Scaled(Shifted):
    """Shifted, with every point first scaled by k about the origin."""

    def __init__(self, f, dx, dy, k):
        super().__init__(f, dx, dy)
        self.k = k

    def q(self, p):
        return (self.k * p[0] + self.dx, self.k * p[1] + self.dy)


def window_arc(g, r, box, **kw):
    """Draw the part of the circle of radius r inside the box (x0, x1, y0, y1)
    of the panel, between the angles 0.55 pi and 1.95 pi, sampled finely."""
    x0, x1, y0, y1 = box
    n = 720
    run = []
    for k in range(n + 1):
        t = 0.55 * PI + 1.4 * PI * k / n
        p = (r * math.cos(t), r * math.sin(t))
        inside = x0 <= p[0] <= x1 and y0 <= p[1] <= y1
        if inside:
            run.append(t)
        if (not inside or k == n) and len(run) > 1:
            g.arc(r, run[0], run[-1], **kw)
        if not inside:
            run = []


def centre(g, off=(-0.05, -0.1), anchor='end'):
    """The disk centre: a dot labelled o."""
    g.dot((0, 0), r=2.6)
    g.text(off, 'o', size=14, anchor=anchor)


def draw_squares(g, W, keys='CWDS', labels=True, size=16, away=None,
                 at=None):
    for k in keys:
        stroke, fill = SQUARE[k]
        g.polygon(W.corners(k), fill=fill, stroke=stroke, width=1.5)
    if labels:
        for k in keys:
            stroke, _ = SQUARE[k]
            pos = W.c[k] if k != 'C' else shift(W.c[k], (0.2, 0.2))
            if away and math.hypot(*away[k]) > 1e-9:
                fx, fy = away[k]
                n = math.hypot(fx, fy)
                if k == 'C':
                    pos = shift(W.c[k], (-fy / n, fx / n), 0.24)
                else:
                    pos = shift(W.c[k], (-fx / n, -fy / n), 0.2)
            if at and k in at:
                pos = shift(W.c[k], at[k])
            g.text(pos, k, size=size, color=stroke)


def reach(Wd, foot, tv, half, rclip, tol=0.015, step=0.005):
    """How far the line through foot in the direction tv runs, up to half,
    before it enters a square or leaves the disk of radius rclip."""
    t = 0.0
    while t < half:
        p = shift(foot, tv, t + step)
        if (math.hypot(*p) > rclip or
                any(Wd.inside(p, k, tol) for k in 'CWDS')):
            break
        t += step
    return t


def separating_line(g, W, n, color, half=0.55, width=1.6, dash='5 3',
                    rclip=None):
    """The line midway between the two squares of the edge (D.n),
    perpendicular to its normal, drawn near the squares and clipped where it
    would enter a third square or leave the disk. Returns its two ends."""
    a, b, nv = W.edge(n)
    hi = max(dot(nv, p) for p in W.corners(a))
    lo = min(dot(nv, p) for p in W.corners(b))
    m = (hi + lo) / 2
    # the point of the line nearest to the midpoint of the closest corners
    pa = max(W.corners(a), key=lambda p: dot(nv, p))
    pb = min(W.corners(b), key=lambda p: dot(nv, p))
    mid = ((pa[0] + pb[0]) / 2, (pa[1] + pb[1]) / 2)
    foot = shift(mid, nv, m - dot(nv, mid))
    tv = (-nv[1], nv[0])
    if rclip is None:
        rclip = 10.0
    tp = reach(W, foot, tv, half, rclip)
    tm = reach(W, foot, (-tv[0], -tv[1]), half, rclip)
    ends = (shift(foot, tv, tp), shift(foot, tv, -tm))
    g.line(ends[0], ends[1], stroke=color, width=width, dash=dash)
    return ends


def arrow(g, a, b, color, width=2.2, head=10.0):
    """An arrow from a to b with a filled triangular head, in pixels."""
    (x1, y1), (x2, y2) = g.f.p(*g.q(a)), g.f.p(*g.q(b))
    L = math.hypot(x2 - x1, y2 - y1)
    if L < 1e-9:
        return
    ux, uy = (x2 - x1) / L, (y2 - y1) / L
    hl = min(head, 0.6 * L)
    bx, by = x2 - hl * ux, y2 - hl * uy
    g.f.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{bx:.1f}" y2="{by:.1f}" '
            f'stroke="{color}" stroke-width="{width}"/>')
    w = 0.45 * hl
    pts = [(x2, y2), (bx - w * uy, by + w * ux), (bx + w * uy, by - w * ux)]
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in pts)
    g.f.add(f'<polygon points="{d}" fill="{color}" stroke="none"/>')


def forces(g, W, weights, scale, color=ORANGE):
    F = W.forces(weights)
    for k in 'CWDS':
        fx, fy = F[k]
        if math.hypot(fx, fy) < 1e-9:
            continue
        c = W.c[k]
        arrow(g, c, (c[0] + scale * fx, c[1] + scale * fy), color)
    return F


def model_wings():
    """The model of Theorem 9.1 as wing data: v = s = 0, d = pi/4."""
    x = (S_STAR, S_STAR, 1 - S_STAR, -T_STAR, D_STAR * math.sqrt(2), 0.0,
         1 - S_STAR, T_STAR)
    return Wings(0.0, 0.0, PI / 4, x)


# Figure: the angles and the frames of wing data.

def angles():
    v, s, d = 0.3, 0.25, 0.65
    x, rad = smallest([2, 4, 6, 8], v, s, d)
    Wd = Wings(v, s, d, x)
    f = Figure(0, 6.25, -0.32, 3.42, 100)
    g = Shifted(f, 1.98, 1.98)
    box = (-1.95, 1.32, -1.95, 1.32)
    window_arc(g, R0, box, stroke=INK, width=1.2, dash='6 4')
    window_arc(g, rad, box, stroke=PINK, width=1.2)
    at = {k: shift((0, 0), (Wd.e1(k)[0] + Wd.e2(k)[0],
                            Wd.e1(k)[1] + Wd.e2(k)[1]), -0.17)
          for k in 'WDS'}
    draw_squares(g, Wd, at=at)
    for k in 'WDS':
        c = Wd.c[k]
        for i, e in ((1, Wd.e1(k)), (2, Wd.e2(k))):
            tip = shift(c, e, 0.25)
            arrow(g, c, tip, INK, width=1.5, head=8)
            g.text(shift(tip, e, 0.13), subsup('e', str(i), k, 14),
                   size=14, italic=True)
    centre(g)
    g.text((-0.15, -2.15), '(a) the squares and their frames', size=13,
           italic=False)
    # (b) the phases
    o = (4.85, 2.55)
    h = Scaled(f, o[0], o[1], 1.3)
    for t in (PI, 1.5 * PI):
        h.line((0, 0), u(t), stroke=FAINT, width=1.2, dash='4 3')
    rays = (('W', PI - v), ('D', PI + d), ('S', 1.5 * PI + s))
    for name, t in rays:
        col = SQUARE[name][0]
        arrow(h, (0, 0), shift((0, 0), u(t), 1.0), col, width=1.8, head=9)
        h.text(shift((0, 0), u(t), 1.18), subsup('e', '1', name, 14),
               size=14, color=col, italic=True)
    h.dot((0, 0), r=2.6)
    h.text((0.06, 0.08), 'o', size=14, anchor='start')
    marks = ((PI - v, PI, 0.36, 'v'), (PI, PI + d, 0.36, 'd'),
             (1.5 * PI, 1.5 * PI + s, 0.36, 's'),
             (PI - v, PI + d, 0.62, 'q'))
    for t0, t1, r, name in marks:
        h.arc(r, t0, t1, stroke=INK, width=1.2)
        h.text(shift((0, 0), u((t0 + t1) / 2), r + 0.1), name, size=15)
    t0, t1 = PI + d, 1.5 * PI + s
    h.arc(0.8, t0, t1, stroke=INK, width=1.2)
    h.text(shift((0, 0), u((t0 + t1) / 2), 0.9), f'π/2 {MINUS} ' + it('r'),
           size=14, anchor='end', italic=False)
    f.text((o[0] - 0.45, -0.17), '(b) the phases', size=13, italic=False)
    save(f, 'appendix-d/angles', 'Two panels. Left: the central square C at '
         'the disk centre o and the squares W, D and S in the lower left part '
         'of the disk, each with the two axes of its frame drawn as arrows '
         'from its centre. Right: from a point o, the primary axes of W, D and '
         'S as arrows in their colours, with the dashed directions of phase '
         'pi and 3 pi / 2; arcs mark the angle v of W above the first dashed '
         'direction, the angle d of D below it, the angle s of S beyond the '
         'second dashed direction, the gap q from W to D and the angle pi/2 '
         '- r from D to S')
    return rad


# Figure: the wings of the model and the missing wings.

def local(Wd, k, alpha, beta):
    """The point with the coordinates (alpha, beta) in the frame of the
    square k, from its centre."""
    return shift(shift(Wd.c[k], Wd.e1(k), alpha), Wd.e2(k), beta)


def wings():
    box = (-1.82, 1.08, -1.95, 1.12)
    W_ = 3.02
    f = Figure(0, 3 * W_, -0.42, 3.1, 92)
    # (a) the model, (b) a missing south wing, (c) its reflection, a missing
    # west wing
    M = model_wings()
    v, s, d = 0.0, 0.32, PI / 4
    x, rad = smallest([3, 5, 6, 9], v, s, d)
    B = Wings(v, s, d, x)
    cx, cy, aW, bW, aD, bD, aS, bS = x
    Cr = Wings(s, v, PI / 2 - d, (cy, cx, aS, -bS, aD, -bD, aW, -bW))
    # the panels: wing data, separations, circles, and the places of the
    # labels of the separations, in the frame of a square
    panels = [(M, (6, 8), (R6,), {6: ('W', 0.22, 0.37), 8: ('S', 0.3, -0.27)}),
              (B, (6, 9), (R0, rad), {6: ('W', 0.22, 0.37),
                                      9: ('D', 0.1, 0.28)}),
              (Cr, (7, 8), (R0, rad), {7: ('D', 0.1, -0.28),
                                       8: ('S', 0.3, -0.27)})]
    titles = ['(a) the model', '(b) a missing south wing',
              '(c) a missing west wing']
    for k, (Wd, seps, radii, places) in enumerate(panels):
        g = Shifted(f, 1.9 + k * W_, 1.98)
        for R in radii:
            col = PINK if R == rad else INK
            window_arc(g, R, box, stroke=col, width=1.2,
                       dash=None if R == rad else '6 4')
        e2 = Wd.e2('D')
        at = {'D': (0.0, 0.0) if k == 0 else
              (0.2 * (2 * k - 3) * e2[0], 0.2 * (2 * k - 3) * e2[1])}
        draw_squares(g, Wd, at=at)
        for n in seps:
            col = {6: BLUE, 8: GREEN}.get(n, PURPLE)
            separating_line(g, Wd, n, col, half=0.62 if k == 0 else 0.55,
                            width=2.4, dash=None, rclip=max(radii))
            g.text(local(Wd, *places[n]), tag(n), size=14, italic=False,
                   color=col)
        if k == 0:
            g.dot((-D_STAR, -D_STAR + H), r=3.6, fill=PURPLE)
            g.dot((-D_STAR + H, -D_STAR), r=3.6, fill=PURPLE)
        g.text((-0.36, -2.18), titles[k], size=14, italic=False)
        centre(g, off=(0.05, -0.08), anchor='start')
    save(f, 'appendix-d/wings', 'Three panels, each with the central square C '
         'and the squares W, D, S in the lower left part of the disk. (a) The '
         'model: the top vertex of D lies on the lower side of W, along which '
         '(D.6) separates W and D, and its right vertex on the left side of S, '
         'along which (D.8) separates D and S. (b) A missing south wing: S is '
         'turned by 0.32 and lies beyond the line of the lower right side of '
         'D, (D.9); placed in the smallest disk that allows these separations, '
         'the squares cross the dashed circle of radius R0. (c) The mirror '
         'image of (b) in the diagonal, a missing west wing')
    return rad


# Figure: the unit forces of Table D.1.

def forces_table():
    v, s, d = 0.3, 0.25, 0.65
    q, r = d + v, d - s
    k = 0.72
    panels = [
        ('C', [(1, d, PURPLE), (2, -v, BLUE), (3, 0.0, BLUE),
               (4, PI / 2 + s, GREEN), (5, PI / 2, GREEN)]),
        ('W', [(2, 0.0, INK), (3, v, INK), (6, -PI / 2, PURPLE),
               (7, q - PI / 2, PURPLE)]),
        ('D', [(1, 0.0, INK), (6, PI / 2 - q, BLUE), (7, PI / 2, BLUE),
               (8, -r, GREEN), (9, -PI / 2, GREEN)]),
        ('S', [(4, 0.0, INK), (5, -s, INK), (8, PI / 2, PURPLE),
               (9, r, PURPLE)]),
    ]
    # label nudges (in units of the panel) where two arrows are close
    nudge = {('C', 4): (-0.2, 0.0), ('C', 5): (0.2, 0.0),
             ('C', 2): (0.0, -0.07), ('C', 3): (0.0, 0.07),
             ('W', 2): (0.0, -0.08), ('W', 3): (0.0, 0.08),
             ('S', 4): (0.0, 0.08), ('S', 5): (0.0, -0.08)}
    f = Figure(0, 8.3, -0.15, 2.55, 100)
    for i, (name, arrows) in enumerate(panels):
        o = (0.9 + 2.05 * i, 1.2)
        g = Scaled(f, o[0], o[1], k)
        g.line((-1.08, 0), (1.08, 0), stroke=FAINT, width=1, dash='4 3')
        g.line((0, -1.08), (0, 1.08), stroke=FAINT, width=1, dash='4 3')
        g.arc(1.0, 0, 2 * PI, stroke=FAINT, width=0.8, dash='2 3')
        for n, t, col in arrows:
            arrow(g, (0, 0), u(t), col, width=2.0, head=9)
            p = shift((0, 0), u(t), 1.32)
            p = shift(p, nudge.get((name, n), (0, 0)))
            g.text(p, tag(n), size=13, italic=False, color=col)
        g.dot((0, 0), r=2.4)
        f.text((o[0], -0.08), 'on ' + it(name), size=14, italic=False)
    save(f, 'appendix-d/forces', 'Four panels, for the squares C, W, D and S. '
         'Each shows the axes of the frame of its square dashed, the first '
         'pointing right and the second up, the unit circle, '
         'and an arrow for the unit force that each separating inequality '
         'puts on the square, labelled (D.1) to (D.9) and coloured by the '
         'other square of the separation: blue for W, purple for D, green for '
         'S and black for C')


# Plots.

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
        q = [self.P(*p) for p in pts]
        d = 'M ' + ' L '.join(f'{x:.1f} {y:.1f}'
                              for x, y in (self.f.p(*r) for r in q))
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.f.add(f'<path d="{d}" fill="none" stroke="{stroke}" '
                   f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')

    def line(self, a, b, **kw):
        self.f.line(self.P(*a), self.P(*b), **kw)

    def polygon(self, pts, **kw):
        self.f.polygon([self.P(*p) for p in pts], **kw)

    def dot(self, p, **kw):
        self.f.dot(self.P(*p), **kw)

    def text(self, p, s, **kw):
        self.f.text(self.P(*p), s, **kw)

    def axes(self, xticks, yticks, xlabel, ylabel, size=12, ylabel_size=15):
        """Axes with arrows, ticks and labels; the label of the first axis
        sits right of its arrow, that of the second above its arrow."""
        f = self.f
        f.line(self.P(self.x0, self.y0), shift(self.P(self.x1, self.y0),
               (0.12, 0)), width=1, arrow=True)
        f.line(self.P(self.x0, self.y0), shift(self.P(self.x0, self.y1),
               (0, 0.12)), width=1, arrow=True)
        for x, s in xticks:
            f.line(self.P(x, self.y0), shift(self.P(x, self.y0), (0, -0.05)),
                   width=1)
            f.text(shift(self.P(x, self.y0), (0, -0.18)), s, size=size,
                   italic=False)
        for y, s in yticks:
            f.line(self.P(self.x0, y), shift(self.P(self.x0, y), (-0.05, 0)),
                   width=1)
            f.text(shift(self.P(self.x0, y), (-0.09, 0)), s, size=size,
                   italic=False, anchor='end')
        if xlabel:
            f.text(shift(self.P(self.x1, self.y0), (0.2, 0.0)), xlabel,
                   size=15, anchor='start')
        if ylabel:
            f.text(shift(self.P(self.x0, self.y1), (0, 0.26)), ylabel,
                   size=ylabel_size, italic='<' not in ylabel)


def grid(lo, hi, n=200):
    return [lo + (hi - lo) * k / n for k in range(n + 1)]


# Figure: the chord term.

LS = RB * (2 + (9 / 20) ** 2 / 4)
MS = RB * 9 / 20


def chord_second(q, L=LS, M=MS):
    return -math.sin(q) + L / 4 * math.sin(q / 2) + M / 4 * math.cos(q / 2)


def taylor_second(q):
    return -S7(q) + LS / 4 * S5(q / 2) + MS / 4 * C4(q / 2)


def chord():
    f = Figure(0, 4.25, 0.38, 3.3, 100)
    g = Scaled(f, 1.05, 1.42, 1.42)
    q, z = 1.0, 9 / 20
    g.line((-0.25, 0), (1.85, 0), stroke=FAINT, width=1, dash='4 3')
    g.line((0, -0.65), (0, 1.18), stroke=FAINT, width=1, dash='4 3')
    g.text((1.9, 0), subsup('e', '1', 'D', 14), size=14, color=FAINT,
           anchor='start')
    g.text((0.05, 1.22), subsup('e', '2', 'D', 14), size=14, color=FAINT,
           anchor='start')
    g.arc(1.0, -0.1, PI / 2 + 0.25, stroke=FAINT, width=1, dash='2 3')
    a = (math.sin(q), math.cos(q))
    b = (a[0], a[1] - 1)
    c = (b[0] + z, b[1])
    g.line((0, 1), a, stroke=INK, width=1.2, dash='5 3')
    arrow(g, (0, 0), a, BLUE)
    arrow(g, a, b, PURPLE)
    arrow(g, b, c, INK)
    arrow(g, (0, 0), c, ORANGE, width=2.6)
    g.dot((0, 0), r=3)
    g.dot((0, 1), r=2.6)
    g.text((0.56, 0.5), tag(6), size=13, italic=False, color=BLUE,
           anchor='end')
    g.text((a[0] - 0.05, 0.2), tag(9), size=13, italic=False,
           color=PURPLE, anchor='end')
    g.text(((b[0] + c[0]) / 2 + 0.05, b[1] - 0.12), tag(1), size=13,
           italic=False)
    g.text((0.5, -0.37), 'F', size=16, color=ORANGE)
    g.text((0.47, 0.93), 'chord 2 sin(' + it('q') + '/2)', size=13,
           italic=False, anchor='start')
    g.arc(0.3, PI / 2 - q, PI / 2, stroke=INK, width=1)
    g.text((0.12, 0.42), 'q', size=15)
    save(f, 'appendix-d/chord', 'The force on D in its frame, for q = 1 and '
         'z = 9/20: a blue unit arrow (sin q, cos q) of (D.6) from the centre, '
         'then the purple arrow (0, -1) of (D.9) straight down from its tip; '
         'their sum is the dashed chord of the unit circle from (0, 1) to '
         '(sin q, cos q); then the black arrow (z, 0) of (D.1); the total '
         'force F in orange from the centre')


def curvature():
    f = Figure(0, 4.95, 0.15, 3.42, 100)
    B = Plot(f, (0.75, 0.55, 3.55, 2.5), (0.4, 1.85), (-0.32, 0.0))
    B.axes([(0.5, '1/2'), (1, '1'), (1.5, '3/2'), (5 / 3, '5/3')],
           [(-0.3, MINUS + '0.3'), (-0.2, MINUS + '0.2'),
            (-0.1, MINUS + '0.1'), (0, '0')], 'q', '')
    B.curve([(q, chord_second(q)) for q in grid(0.5, 5 / 3)], stroke=PURPLE,
            width=2.2)
    L38, M38 = RB * (2 + (3 / 8) ** 2 / 4), RB * 3 / 8
    B.curve([(q, chord_second(q, L38, M38)) for q in grid(0.5, 5 / 3)],
            stroke=BLUE, width=1.5)
    B.curve([(0.5, 3 / 40 - 0.15), (1, 3 / 40 - 0.3), (1.5, 3 / 40 - 0.3)],
            stroke=ORANGE, width=1.6, dash='6 3')
    B.curve([(157 / 200, -0.19), (5 / 3, -0.19)], stroke=GREEN, width=1.6,
            dash='6 3')
    for q in (0.5, 1, 1.5, 157 / 200, 5 / 3):
        B.dot((q, taylor_second(q)), r=3.2, fill=INK)
    B.text((0.56, -0.035), '3/40 ' + MINUS + ' (3/10) min(' + it('q') +
           ', 1)', size=13, italic=False, color=ORANGE, anchor='start')
    B.text((1.66, -0.172), MINUS + '19/100', size=13, italic=False,
           color=GREEN, anchor='end')
    B.text((1.69, -0.215), it('z') + ' = 9/20', size=13, italic=False,
           color=PURPLE, anchor='start')
    B.text((1.69, -0.262), it('z') + ' = 3/8', size=13, italic=False,
           color=BLUE, anchor='start')
    f.text(shift(B.P(0.4, 0), (0.05, 0.3)),
           sb(it('H') + '″', it('L') + ',' + it('M'), '(' + it('q') + ')',
              size=15), size=15, italic=False)
    save(f, 'appendix-d/curvature', 'The second derivative of the chord term '
         'on q from 1/2 to 5/3: a purple curve for the largest weights L* and '
         'M*, that is z = 9/20, and a blue one below it for z = 3/8, both '
         'below the dashed orange broken line 3/40 - (3/10) min(q, 1) and, '
         'from 157/200 on, below the dashed green level -19/100; five black '
         'dots on or just above the purple curve are the Taylor bounds of '
         'Table D.2')


# Figure: the gap of W and D (Lemma D.5).

def gap_bound(U, v, q):
    A = RHO0 - 0.5 - 0.31 * (U + U * U)
    return (A * math.sin(q) + (U - 0.5) * math.cos(q) - 0.19 - 0.17 * q
            + 0.17 * v)


def gap():
    f = Figure(0, 8.4, 0.1, 3.55, 100)
    profiles = [(it('W') + ' on its own axis', lambda v: 233 / 500 - 0.73 * v,
                 0.5, [0, 0.25, 0.5], ['0', '1/4', '1/2']),
                (it('W') + ' on the west side of ' + it('C'),
                 lambda v: 0.47 - 2 * v / 3, 0.4, [0, 0.2, 0.4],
                 ['0', '1/5', '2/5'])]
    shades = ['#6b7280', CYAN, BLUE]
    for k, (title, U, V, vs, labels) in enumerate(profiles):
        P = Plot(f, (0.8 + 4.1 * k, 0.55, 3.0, 2.5), (0, 1), (-0.56, 0.04))
        P.axes([(0, '0'), (0.5, '1/2'), (1, '1')],
               [(-0.4, MINUS + '0.4'), (-0.2, MINUS + '0.2'), (0, '0')],
               'q', 'F')
        P.line((0, 0), (1, 0), stroke=INK, width=0.8, dash='3 3')
        for v, lab, col in zip(vs, labels, shades):
            pts = [(q, gap_bound(U(v), v, q)) for q in grid(0, 1, 100)]
            P.curve(pts, stroke=col, width=2)
            P.text((0.03, pts[0][1]), it('v') + ' = ' + lab, size=13,
                   italic=False, color=col, anchor='start', dy=12)
        top = gap_bound(U(V), V, 1)
        P.dot((1, top), r=3.4, fill=ORANGE)
        P.text((0.96, 0.025), num(top, 4) + ' at ' + it('q') + ' = 1',
               size=13, color=ORANGE, anchor='end', dy=-4, italic=False)
        f.text(shift(P.P(0, 0.04), (0.12, 0.44)), title, size=13,
               italic=False, anchor='start')
    save(f, 'appendix-d/gap', 'Two graphs over q from 0 to 1 of the upper '
         'bound F(U(v), v, q) of the margin of the separation of W and D along '
         'the secondary axis of D. Left: W on its own axis, U(v) = 233/500 - '
         '73v/100, for v = 0, 1/4, 1/2. Right: W on the west side of C, U(v) = '
         '47/100 - 2v/3, for v = 0, 1/5, 2/5. All curves increase in q and '
         'stay below zero; the largest value, at q = 1 and the largest v, is '
         'marked')


# The configurations of the cases.

BOX = (-1.95, 1.32, -1.95, 1.32)
DX0 = 4.45
STRESS_COLOUR = {1: PURPLE, 2: BLUE, 3: BLUE, 4: GREEN, 5: GREEN, 6: BLUE,
                 7: PURPLE, 8: GREEN, 9: PURPLE}


def configuration(f, dx, dy, names, weights, v, s, d, scale, k=1.0):
    """A configuration of the case in the smallest disk, with the separating
    lines (those of the stress in colour) and the forces of the stress."""
    x, rad = smallest(names, v, s, d)
    Wd = Wings(v, s, d, x)
    g = Scaled(f, dx, dy, k)
    pts = [p for key in 'CWDS' for p in Wd.corners(key)]
    assert all(BOX[0] < p[0] < BOX[1] and BOX[2] < p[1] < BOX[3] for p in pts)
    window_arc(g, R0, BOX, stroke=INK, width=1.2, dash='6 4')
    window_arc(g, rad, BOX, stroke=PINK, width=1.2)
    F = Wd.forces(weights)
    draw_squares(g, Wd, away=F, at={'C': (-0.27, 0.27)})
    rclip = max(rad, R0)
    for n in sorted(set(names) | {1}):
        if n in weights:
            separating_line(g, Wd, n, STRESS_COLOUR[n], half=0.45, width=2.2,
                            dash=None, rclip=rclip)
        else:
            separating_line(g, Wd, n, FAINT, half=0.4, width=1.2, dash='4 3',
                            rclip=rclip)
    forces(g, Wd, weights, scale)
    centre(g)
    return Wd, rad, F, g


def title_lines(g, lines, x=-0.32, y=-2.12, size=13):
    for i, line in enumerate(lines):
        g.text((x, y - 0.19 * i), line, size=size, italic=False)


def case_figure(name, names, weights, angles, scale, domain, title, caption,
                width=7.4):
    f = Figure(0, width, -0.62, 3.32, 100)
    v, s, d = angles
    Wd, rad, F, g = configuration(f, 1.98, 1.98, names, weights, v, s, d,
                                  scale)
    title_lines(g, title)
    domain(f)
    save(f, name, caption.format(R=rad))
    return rad


# The profiles of the cases, with exact constants (for the shading).

def far_term(x):
    """The function T of Lemma D.8."""
    return (4 * math.cos(x) + 4 * max(-math.sin(x), 0)
            - R0 * math.sqrt(25 - 24 * math.sin(x)))


def profile_side_west(v, s, d):
    q, r = d + v, d - s
    return (9 - 6 * C0 + 2 * math.cos(v) + far_term(s) + 3 * math.cos(r)
            - R0 * math.sqrt(18 - 18 * math.sin(r))
            + 3 * (math.cos(q) + math.sin(q))
            - R0 * math.sqrt(13 + 12 * math.sin(d)))


def profile_side_small(v, d):
    q, k = d + v, d - 12 / 25
    return (8 - 4 * C0 - 3 * R0 + far_term(v) + 3 * math.sin(q)
            - 6 * R0 * math.sin(q / 2) + 3 * (math.cos(k) + math.sin(k)))


def profile_side_large(v, s, d):
    q, r = d + v, d - s
    kap = 2.4 * RB - (4 if v < 0 else 0)
    return (13 - 5 * RB - 10 * RHOB + (5 - 10 * CB) * math.cos(s)
            + 5 * math.sin(s) + 4 * math.cos(v) + kap * math.sin(v)
            + 3 * math.sin(q) - 6 * RB * math.sin(q / 2)
            - (3 * RHOB - 1.5) * math.cos(r) + 1.5 * math.sin(r))


def chord_term(L, M, q):
    return math.sin(q) - L * math.sin(q / 2) - M * math.cos(q / 2)


def wing_zeta(x):
    """The wing harmonic of Section D.7."""
    return MUM * math.cos(x) + MUP * math.sin(x)


def profile_own_side(v, d, y):
    L, M = RB * (2 + (3 / 8) ** 2 / 4), RB * 3 / 8
    xi = math.sin(d / 2) - 2 * MUP * math.cos(d / 2)
    return (4.925 - 2.281 * RB - y
            + 2.05 * (MUM * math.cos(v) + (0.5 + y) * math.sin(v))
            + 0.375 * (MUM * math.cos(d) + (0.5 - y) * math.sin(d))
            + chord_term(L, M, d + v) + xi)


def profile_south_turned(v, s, d):
    L = RB * 2.076 / 1.09
    r = d - s
    return (4.705 - 2.133 * RB - 1.59 * RHOB + 1.82 * wing_zeta(v)
            + 1.59 * wing_zeta(s) + 1.09 * chord_term(L, 0, d + v)
            - MUP * math.cos(r) + 0.5 * math.sin(r))


def profile_west_turned(v, s, d, y):
    r = d - s
    K = (5.45 / 2 + 3.25 / 2 + 1.45 / 2 - 2.4623 * RB - 0.75 * RHOB)
    return (K + 0.45 * (MUM * math.cos(d) + (0.5 - y) * math.sin(d))
            + 2.25 * (MUM * math.cos(v) + (0.5 + y) * math.sin(v))
            + chord_term(LS, MS, d + v)
            + 0.75 * ((0.5 - y) * math.cos(s) + MUP * math.sin(s))
            - MUP * math.cos(r) + 0.5 * math.sin(r) - math.sin(r) ** 2 / 12)


SIGMA = 1.415 * RB


def base_delta(x):
    return math.cos(x) - SIGMA * math.cos(x / 2) + SIGMA * math.sin(x / 2)


def base_profile(v, s, d):
    return (2.05 * wing_zeta(v) + 0.5 * math.cos(v + d)
            - MUP * math.sin(v + d) + base_delta(d - s))


def profile_diagonal_side(v, s, d):
    x = abs(s)
    sig = 5 / 6 * RB if s >= 0 else 1.5 - 5 / 6 * RB
    return (1.5 * MUM - 2.05 * MUP + 2 - 649 / 360 * RB + base_profile(v, s, d)
            + 1.5 * math.cos(x) + sig * math.sin(x))


def profile_diagonal_own(v, s, d):
    g, ell = ((1.6, 1.887) if s <= 0.15 else
              (2.0, 2.237) if s <= 0.3 else (2.6, 2.786))
    return (2 - 2.05 * MUP + base_profile(v, s, d) + g * (1 + wing_zeta(s))
            - RB * ell)


def range_constants():
    """The weights b, z, the coefficients alpha, beta and the constant K of
    the four stresses of Proposition D.7."""
    out = {}
    D0 = RB * 13 / 5 - 0.5 * (12 / 5 + 1)
    b, z = 13 / 6, 12 / 5
    out[1] = (b, z, 0.5, -MUP, 0.5 * (b + z + 1) - RHOB * b - D0)
    b = 2 / 7
    w0 = 0.4 * (53 / 49 + 25 / 16) * RB - 1 / 7
    out[2] = (b, z, 1.0, 1 - 8 / 35 * RB, 0.5 * (b + z + 1) - w0 - D0)
    b, z = 17 / 3, 14 / 3
    out[3] = (b, z, 0.5, -MUP, 0.5 * (b + z + 1) - RHOB * (b + z))
    b, z = 25 / 12, 9 / 4
    out[4] = (b, z, 0.5, -MUP, 0.5 * (b + z + 1) - RHOB * b
              - (RB * 2.4623 - 0.5 * (z + 1)))
    return out


RANGE = range_constants()


def range_profile(part, v, d):
    b, z, al, be, K = RANGE[part]
    q = v + d
    return min(K + b * (MUM * math.cos(v) + (0.5 + y) * math.sin(v))
               + z * (MUM * math.cos(d) + (0.5 - y) * math.sin(d))
               + al * math.cos(q) + be * math.sin(q) for y in (0, CB))


# Shading of the domains.

def mix(color, t):
    """The colour at the fraction t from white to `color`."""
    c = [int(color[k:k + 2], 16) for k in (1, 3, 5)]
    m = [round(255 + (x - 255) * t) for x in c]
    return '#' + ''.join(f'{x:02x}' for x in m)


def inside(p, poly):
    sgn = 0
    for k in range(len(poly)):
        (x1, y1), (x2, y2) = poly[k], poly[(k + 1) % len(poly)]
        cr = (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1)
        if abs(cr) < 1e-12:
            continue
        if sgn == 0:
            sgn = 1 if cr > 0 else -1
        elif (cr > 0) != (sgn > 0):
            return False
    return True


def clip_convex(cell, poly):
    """The part of the polygon `cell` inside the convex polygon `poly`."""
    area = sum(poly[k][0] * poly[(k + 1) % len(poly)][1]
               - poly[(k + 1) % len(poly)][0] * poly[k][1]
               for k in range(len(poly)))
    sgn = 1 if area > 0 else -1
    for k in range(len(poly)):
        (x1, y1), (x2, y2) = poly[k], poly[(k + 1) % len(poly)]
        a, b = sgn * (y2 - y1), -sgn * (x2 - x1)
        cell = clip(cell, a, b, a * x1 + b * y1)
        if len(cell) < 3:
            return []
    return cell


def shade(P, poly, fn, vmax, n=40, color=BLUE, levels=10, outline=True):
    """Fill the convex polygon `poly` of the plot P by the values of fn, in
    `levels` bands from white at 0 to `color` at vmax (nonpositive values would
    be red). Cells inside the polygon of equal colour are merged into
    rectangles, along rows and then down columns; cells on the boundary are
    clipped to the polygon. Neighbouring pieces overlap slightly."""
    xs = [p[0] for p in poly]
    ys = [p[1] for p in poly]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    dx, dy = (x1 - x0) / n, (y1 - y0) / n
    ex, ey = dx * 0.15, dy * 0.15

    def colour(cx, cy):
        val = fn(cx, cy)
        if val <= 0:
            return '#dc2626'
        k = min(levels - 1, int(levels * val / vmax))
        return mix(color, 0.75 * (k + 0.5) / levels)

    def box(a, b, j0, j1, grow=True):
        gx, gy = (ex, ey) if grow else (0, 0)
        return [(x0 + a * dx - gx, y0 + j0 * dy - gy),
                (x0 + b * dx + gx, y0 + j0 * dy - gy),
                (x0 + b * dx + gx, y0 + j1 * dy + gy),
                (x0 + a * dx - gx, y0 + j1 * dy + gy)]

    def row_runs(j):
        """The runs (i0, i1, colour) of whole cells of the row j; the cells
        on the boundary are drawn at once."""
        runs, run = [], None
        for i in range(n + 1):
            whole = i < n and all(inside(q, poly)
                                  for q in box(i, i + 1, j, j + 1, False))
            col = colour(x0 + (i + 0.5) * dx, y0 + (j + 0.5) * dy) if whole else None
            if run and (not whole or col != run[1]):
                runs.append((run[0], i, run[1]))
                run = None
            if whole and run is None:
                run = (i, col)
            if i < n and not whole:
                part = clip_convex(box(i, i + 1, j, j + 1), poly)
                if part:
                    cx = sum(q[0] for q in part) / len(part)
                    cy = sum(q[1] for q in part) / len(part)
                    P.polygon(part, fill=colour(cx, cy), stroke='none')
        return runs

    open_runs = {}
    for j in range(n + 1):
        keys = row_runs(j) if j < n else []
        for key in list(open_runs):
            if key not in keys:
                P.polygon(box(key[0], key[1], open_runs.pop(key), j),
                          fill=key[2], stroke='none')
        for key in keys:
            open_runs.setdefault(key, j)
    if outline:
        P.polygon(poly, stroke=INK, width=1.2)


def colour_bar(f, pos, vmax, color=BLUE, w=1.2, h=0.12, levels=10):
    x, y = pos
    n = levels
    for k in range(n):
        f.polygon([(x + w * k / n, y), (x + w * (k + 1) / n + 0.005, y),
                   (x + w * (k + 1) / n + 0.005, y + h), (x + w * k / n, y + h)],
                  fill=mix(color, 0.75 * (k + 0.5) / n), stroke='none')
    f.polygon([(x, y), (x + w, y), (x + w, y + h), (x, y + h)], stroke=FAINT,
              width=0.6)
    f.text((x - 0.06, y + h / 2), '0', size=12, italic=False, anchor='end')
    f.text((x + w + 0.06, y + h / 2), f'{vmax:g}', size=12, italic=False,
           anchor='start')


def legend(f, x, lines, y=0.02, size=12):
    for i, line in enumerate(lines):
        f.text((x, y - 0.17 * i), line, size=size, italic=False,
               anchor='start')


def value_label(P, p, text, off=None, anchor=None, color=INK, size=12):
    """A dot at the corner p of the domain with its value, placed inside."""
    P.dot(p, r=3.3, fill=INK)
    f = P.f
    if off is None:
        cx = (P.x0 + P.x1) / 2
        cy = (P.y0 + P.y1) / 2
        right = p[0] > cx + 1e-9
        left = p[0] < cx - 1e-9
        off = (-0.07 if right else (0.07 if left else 0),
               -0.15 if p[1] > cy else 0.15)
        anchor = 'end' if right else ('start' if left else 'middle')
    f.text(shift(P.P(*p), off), text, size=size, italic=False, anchor=anchor,
           color=color)


def fmt(x):
    """A positive lower bound, rounded down to three decimals, or to five
    below 0.01."""
    n = 5 if x < 0.01 else 3
    return f'{math.floor(x * 10 ** n + 1e-6) / 10 ** n:.{n}f}'


# Figure: the stress of Lemma D.6.

def range_stress():
    f = Figure(0, 3.55, -0.5, 3.32, 100)
    v, s, d = 0.55, 0.1, 0.55
    weights = {2: 13 / 6, 1: 12 / 5, 7: 1}
    Wd, rad, F, g = configuration(f, 1.98, 1.98, [2, 4, 7, 8], weights, v, s,
                                  d, 0.12)
    title_lines(g, ['a missing west wing, ' + it('W') + ' on its own axis'])
    save(f, 'appendix-d/range', 'The squares C, W, D and S of a missing west '
         f'wing with W on its own axis, at v = {v}, s = {s}, d = {d}, in the '
         'smallest disk that allows these separations (radius '
         f'{rad:.3f}, pink; the circle of radius R0 is dashed). In colour, '
         'the separating lines of the stress of Lemma D.6: of W and of D from '
         'C along their own axes, and of W and D along the secondary axis of '
         'D; in grey, the other separations. Orange arrows show the forces on '
         'C, W and D for the weights 13/6, 12/5 and 1; there is no force on S')
    return rad


# Figure: the walls and the range of a missing west wing.

def walls():
    f = Figure(0, 8.35, -0.3, 4.1, 100)
    lo, hi = 0.5, PI / 4
    # left: a missing south wing in the (s, d)-plane
    A = Plot(f, (0.7, 0.55, 3.1, 3.0), (-0.45, 0.72), (lo, hi))
    A.axes([(-0.4, MINUS + '2/5'), (0, '0'), (0.4, '2/5'), (0.48, ''),
            (2 / 3, '2/3')], [(0.5, '1/2'), (0.6, '3/5'), (0.7, '7/10'),
                              (hi, 'π/4')], 's', 'd')
    A.polygon([(-0.45, lo), (lo - hi, lo), (0, hi), (-0.45, hi)],
              fill=GREY, stroke='none')
    A.polygon([(lo - hi, lo), (2 / 3, lo), (2 / 3, hi), (0, hi)],
              fill=FILLS[2], stroke='none')
    A.line((lo - hi, lo), (0, hi), stroke=PURPLE, width=2)
    for x, col in ((0, INK), (0.4, INK), (0.48, ORANGE)):
        A.line((x, lo), (x, hi), stroke=col, width=1, dash='4 3')
    A.text((-0.42, 0.725), 'wall', size=14, italic=False, color=PURPLE,
           anchor='start')
    A.text((-0.42, 0.695), it('s') + ' ≤ ' + it('d') + ' ' + MINUS +
           ' π/4', size=13, italic=False, color=PURPLE, anchor='start')
    A.text((0.49, 0.535), '12/25', size=13, italic=False, color=ORANGE,
           anchor='start')
    f.text(shift(A.P(-0.45, hi), (0.1, 0.44)), 'a missing south wing',
           size=13, italic=False, anchor='start')
    # right: a missing west wing with W on its own axis, in the (v, d)-plane
    B = Plot(f, (4.85, 0.55, 3.1, 3.0), (0, 0.7), (lo, hi))
    B.axes([(0, '0'), (0.4, '2/5'), (0.62, '31/50'), (2 / 3, '')],
           [(0.5, '1/2'), (0.6, '3/5'), (0.64, '16/25'), (hi, 'π/4')],
           'v', 'd')
    B.polygon([(0, lo), (hi - lo, lo), (0, hi)], fill=GREY, stroke=INK,
              width=0.6)
    B.polygon([(hi - lo, lo), (0.5, lo), (1 - hi, hi), (0, hi)],
              fill='#fde68a', stroke=INK, width=0.6)
    parts = {1: [(0.5, lo), (2 / 3, lo), (2 / 3, 0.6), (0.4, 0.6)],
             2: [(0.4, 0.6), (0.46, 0.6), (53 / 50 - hi, hi), (1 - hi, hi)],
             3: [(0.62, 0.6), (2 / 3, 0.6), (2 / 3, hi), (0.62, hi)],
             4: [(0.46, 0.6), (0.62, 0.6), (0.62, 0.64), (0.42, 0.64)]}
    for k, poly in parts.items():
        shade(B, poly, lambda v, d, k=k: range_profile(k, v, d), 0.1,
              color=BLUE, n=30)
    rest = [(0.42, 0.64), (0.62, 0.64), (0.62, hi), (53 / 50 - hi, hi)]
    B.polygon(rest, fill=FILLS[2], stroke=INK, width=1.2)
    labels = {1: (0.575, 0.55), 2: (0.333, 0.7), 3: (0.645, 0.7),
              4: (0.53, 0.62)}
    for k, pos in labels.items():
        B.text(pos, f'({k})', size=13, italic=False)
    B.text((0.07, 0.56), 'wall', size=14, italic=False)
    B.text((0.25, 0.6), it('q') + ' ≤ 1', size=14, italic=False)
    B.line((hi - lo, lo), (0, hi), stroke=PURPLE, width=2)
    for pt in ((21 / 50, 16 / 25), (48 / 175, 11 / 14), (31 / 50, 16 / 25)):
        B.dot(pt, r=3.4, fill=GREEN)
    B.text((0.52, 0.727), '§D.9', size=13, italic=False, color=GREEN)
    f.text(shift(B.P(0, hi), (0.1, 0.44)), 'a missing west wing, ' + it('W') +
           ' on its own axis', size=13, italic=False, anchor='start')
    f.text((4.85, 0.06), 'shading: the profile of the stress of each part',
           size=12, italic=False, anchor='start')
    colour_bar(f, (5.85, -0.2), 0.1)
    save(f, 'appendix-d/walls', 'Left: the angles (s, d) of a missing south '
         'wing; the wall of Lemma 9.42 excludes s <= d - pi/4 (grey); the '
         'dashed lines s = 0, 2/5 and 12/25 bound the angles of S on its own '
         'axis and on the south side of C and split Propositions D.11 and '
         'D.12. Right: the angles (v, d) of a missing west wing with W on its '
         'own axis: the wall v <= pi/4 - d (grey), the gap q = d + v <= 1 of '
         'Lemma D.5 (yellow), and the four parts of Proposition D.7, each '
         'shaded in blue by the profile of its stress, which is positive '
         'throughout; they leave the small green domain of section D.9, with '
         'the three points of Lemma D.18 marked')


# Figure: the far-vertex term of Lemma D.8.

def far_term_fig():
    f = Figure(0, 4.7, 0.1, 3.05, 100)
    P = Plot(f, (0.85, 0.5, 3.3, 2.2), (-0.45, 0.45), (-4.8, -2.8))
    P.axes([(-0.4, MINUS + '2/5'), (0, '0'), (0.4, '2/5')],
           [(-4.5, MINUS + '4.5'), (-4, MINUS + '4'), (-3.5, MINUS + '3.5'),
            (-3, MINUS + '3')], 'x', '')
    for a, b in ((-0.4, 0), (0, 0.4)):
        P.curve([(a, far_term(a)), (b, far_term(b))], stroke=ORANGE,
                width=1.4, dash='5 3')
    P.curve([(x, far_term(x)) for x in grid(-0.4, 0, 100)], stroke=BLUE,
            width=2.2)
    P.curve([(x, far_term(x)) for x in grid(0, 0.4, 100)], stroke=BLUE,
            width=2.2)
    for x in (-0.4, 0, 0.4):
        P.dot((x, far_term(x)), r=3.2, fill=INK)
    P.text((0.4, far_term(0.4)), it('T') + '(' + it('x') + ')', size=15,
           italic=False, color=BLUE, anchor='end', dx=-8, dy=-12)
    save(f, 'appendix-d/far-term', 'The graph of T(x) on x from -2/5 to 2/5, '
         'in blue, rising from about -4.65 to -4.44 on the left half, nearly '
         'flat, and steeply to about -3.00 on the right half, with a corner at '
         '0; on each half it lies above its dashed orange chord, and dots mark '
         'the values at -2/5, 0 and 2/5')


# The cases of Sections D.5 to D.9.

def side_west():
    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (-0.4, 0.4), (0.5, PI / 4))
        P.axes([(-0.4, MINUS + '2/5'), (0, '0'), (0.4, '2/5')],
               [(0.5, '1/2'), (PI / 4, 'π/4')], 's', 'd')
        shade(P, [(-0.4, 0.5), (0.4, 0.5), (0.4, PI / 4), (-0.4, PI / 4)],
              lambda s, d: min(profile_side_west(0, s, d),
                               profile_side_west(0.4, s, d)), 1.2)
        vals = {(-0.4, 0.5): (0.94381, 0.92981),
                (-0.4, PI / 4): (1.25113, 0.75713),
                (0, 0.5): (0.09526, 0.08126), (0, PI / 4): (0.53432, 0.04032),
                (0.4, 0.5): (0.26159, 0.24759),
                (0.4, PI / 4): (0.84831, 0.35431)}
        for (s, d), (a, b) in vals.items():
            value_label(P, (s, d), fmt(a) + ' | ' + fmt(b))
        legend(f, DX0, ['shading: the minimum over ' + it('v') +
                        ' of the profile;',
                        'at the corners: the bounds for ' + it('v') +
                        ' = 0 | 2/5'])
        colour_bar(f, (DX0 + 0.7, -0.45), 1.2)
    return case_figure(
        'appendix-d/side-west', [3, 5, 7, 8], {3: 2, 5: 4, 7: 3, 8: 3},
        (0.3, 0.0, 0.75), 0.09, domain,
        ['a missing west wing,', it('W') + ' and ' + it('S') +
         ' on the sides of ' + it('C')],
        'Left: the squares C, W, D, S of a missing west wing with W on the '
        'west side and S on the south side of C, at v = 0.3, s = 0, d = 0.75, '
        'in the smallest disk that allows these separations (radius {R:.3f}, '
        'pink; the circle of radius R0 is dashed); the separating lines of the '
        'stress with the weights 2, 4, 3, 3 and the forces on the four squares '
        '(orange arrows). Right: the domain of (s, d), shaded by the minimum '
        'over v of the profile, with the lower bounds of Table D.6 at its '
        'corners')


def side_small():
    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (-0.4, 0.4), (0.5, PI / 4))
        P.axes([(-0.4, MINUS + '2/5'), (0, '0'), (0.4, '2/5')],
               [(0.5, '1/2'), (PI / 4, 'π/4')], 'v', 'd')
        shade(P, [(-0.4, 0.5), (0.4, 0.5), (0.4, PI / 4), (-0.4, PI / 4)],
              profile_side_small, 0.8)
        vals = {(-0.4, 0.5): 0.67176, (-0.4, PI / 4): 0.74901,
                (0, 0.5): 0.02128, (0, PI / 4): 0.03220,
                (0.4, 0.5): 0.47881, (0.4, PI / 4): 0.34618}
        for (v, d), a in vals.items():
            value_label(P, (v, d), fmt(a))
        legend(f, DX0, ['shading: the profile; at the corners: its',
                        'lower bounds by Taylor polynomials'])
        colour_bar(f, (DX0 + 0.7, -0.45), 0.8)
    return case_figure(
        'appendix-d/side-small', [3, 5, 6, 9], {3: 4, 6: 3, 9: 3},
        (0.0, 0.2, 0.75), 0.09, domain,
        ['a missing south wing,', it('W') + ' on the west side, ' + it('s') +
         ' ≤ 12/25'],
        'Left: the squares of a missing south wing with W and S on the sides '
        'of C, at v = 0, s = 0.2, d = 0.75, in the smallest disk that allows '
        'these separations (radius {R:.3f}); the separating lines of the stress '
        'with the weights 4, 3, 3 in colour (the separations of S and D from '
        'C, not used, in grey) and the forces of the stress. Right: the domain '
        'of (v, d), shaded by the profile, with the lower bounds of Table D.7')


def side_large():
    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (-0.4, 0.4), (0.48, 2 / 3))
        P.axes([(-0.4, MINUS + '2/5'), (0, '0'), (0.4, '2/5')],
               [(0.48, '12/25'), (2 / 3, '2/3')], 'v', 's')
        shade(P, [(-0.4, 0.48), (0.4, 0.48), (0.4, 2 / 3), (-0.4, 2 / 3)],
              lambda v, s: profile_side_large(v, s, 11 / 14), 0.8)
        vals = {(-0.4, 0.48): 0.72075, (-0.4, 2 / 3): 0.76669,
                (0, 0.48): 0.11351, (0, 2 / 3): 0.15945,
                (0.4, 0.48): 0.25197, (0.4, 2 / 3): 0.29791}
        for (v, s), a in vals.items():
            value_label(P, (v, s), fmt(a))
        legend(f, DX0, ['shading: the profile at ' + it('d') +
                        ' = 11/14, its minimum',
                        'in ' + it('d') + '; at the corners: its lower bounds'])
        colour_bar(f, (DX0 + 0.7, -0.45), 0.8)
    return case_figure(
        'appendix-d/side-large', [3, 4, 6, 9], {3: 4, 4: 10, 6: 3, 9: 3},
        (0.0, 0.55, 0.75), 0.05, domain,
        ['a missing south wing,', it('S') + ' on its own axis, ' + it('s') +
         ' ≥ 12/25'],
        'Left: the squares of a missing south wing with W on the west side of '
        'C and S on its own axis, at v = 0, s = 0.55, d = 0.75, in the smallest '
        'disk that allows these separations (radius {R:.3f}); the separating '
        'lines of the stress with the weights 4, 10, 3, 3 and its forces; the '
        'force on S, of length about 13, lies close to the own axis of S. '
        'Right: the domain of (v, s) at d = 11/14, shaded by the profile, with '
        'the lower bounds of Table D.8')


# Figure: the force on S (Lemma D.13).

def south_region(d0, d1, s_lo, s_hi, n=60):
    """The boundary of the forces (U, V) = 2 cos(d/2) (cos x, sin x), x =
    d/2 - s, for d0 <= d <= d1 and s_lo(d) <= s <= s_hi(d)."""
    def force(d, s):
        c, x = 2 * math.cos(d / 2), d / 2 - s
        return (c * math.cos(x), c * math.sin(x))
    pts = [force(d, s_lo(d)) for d in grid(d0, d1, n)]
    pts += [force(d1, s) for s in grid(s_lo(d1), s_hi(d1), n)]
    pts += [force(d, s_hi(d)) for d in grid(d1, d0, n)]
    pts += [force(d0, s) for s in grid(s_hi(d0), s_lo(d0), n)]
    return pts


def south_force():
    f = Figure(0, 8.3, -0.02, 3.4, 100)
    # left: the two unit forces on S and their sum, in the frame of S
    s, d = 0.2, 0.75
    r = d - s
    k = 1.25
    g = Scaled(f, 0.5, 1.45, k)
    g.line((-0.2, 0), (2.25, 0), stroke=FAINT, width=1, dash='4 3')
    g.line((0, -0.65), (0, 1.0), stroke=FAINT, width=1, dash='4 3')
    g.text((2.3, 0), subsup('e', '1', 'S', 14), size=14, color=FAINT,
           anchor='start')
    g.text((0.05, 1.05), subsup('e', '2', 'S', 14), size=14, color=FAINT,
           anchor='start')
    a = u(-s)
    b = u(r)
    tot = (a[0] + b[0], a[1] + b[1])
    g.line(a, tot, stroke=PURPLE, width=1, dash='4 3')
    g.line(b, tot, stroke=INK, width=1, dash='4 3')
    arrow(g, (0, 0), a, INK, width=2.0, head=9)
    arrow(g, (0, 0), b, PURPLE, width=2.0, head=9)
    arrow(g, (0, 0), tot, ORANGE, width=2.6, head=11)
    g.dot((0, 0), r=2.6)
    g.text(shift(a, (0.05, -0.13)), tag(5), size=13, italic=False,
           anchor='start')
    g.text(shift(b, (-0.06, 0.1)), tag(9), size=13, italic=False,
           color=PURPLE, anchor='end')
    g.text(shift(tot, (0.08, 0.07)), '(' + it('U') + ', ' + it('V') + ')',
           size=14, italic=False, color=ORANGE, anchor='start')
    g.arc(0.45, -s, 0, stroke=INK, width=1)
    g.text(shift((0, 0), u(-s / 2), 0.58), it('s'), size=14, italic=False)
    g.arc(0.3, 0, r, stroke=INK, width=1)
    g.text(shift((0, 0), u(r / 2), 0.42), it('r'), size=14, italic=False)
    g.text((1.0, 0.33), '2 cos(' + it('d') + '/2)', size=13, italic=False,
           color=ORANGE)
    # right: the forces of Lemma D.13 in the (U, V)-plane
    P = Plot(f, (5.45, 0.5, 2.3, 2.55), (1.5, 2.05), (-0.4, 1.1))
    P.axes([(1.5, '3/2'), (1.65, '33/20'), (1.75, '7/4'), (2, '2')],
           [(0, '0'), (0.5, '0.5'), (1, '1')], it('U'), it('V'))
    P.polygon([(1.65, -0.4), (1.65, 0.99), (1.1 / 0.6, 1.1), (2.05, 1.1),
               (2.05, -0.4)], fill=FILLS[2], stroke='none')
    P.line((1.65, -0.4), (1.65, 0.99), stroke=GREEN, width=1.2)
    P.line((1.65, 0.99), (1.1 / 0.6, 1.1), stroke=GREEN, width=1.2)
    P.line((1.5, 0.31 * 1.5), (2.05, 0.31 * 2.05), stroke=ORANGE, width=1.2,
           dash='5 3')
    one = south_region(0.5, 11 / 14, lambda d: d - 11 / 14, lambda d: 0.4)
    two = south_region(11 / 14, 34 / 35, lambda d: d - 4 / 7, lambda d: 0.4)
    P.polygon(one, fill=FILLS[0], stroke=BLUE, width=1.4)
    P.polygon(two, fill=FILLS[1], stroke=ORANGE, width=1.4)
    P.text((1.775, 0.68), '(1)', size=13, italic=False, color=BLUE)
    P.text((1.81, 0.16), '(2)', size=13, italic=False, color=ORANGE)
    save(f, 'appendix-d/south-force', 'Two panels. Left: in the frame of S, '
         'for s = 0.2 and d = 0.75, the unit force of (D.5), at the angle s '
         'below the first axis, and the unit force of (D.9), at the angle r '
         'above it, and their sum (U, V), of length 2 cos(d/2), in orange '
         'along the bisector, with the dashed parallelogram. '
         'Right: the plane of (U, V) with the part U >= 33/20, V <= 3U/5 of '
         'the third cone shaded green and the dashed line V = 0.31 U of the '
         'first cone; the forces of Lemma D.13 (1) fill a blue region inside '
         'the green part, and those of (2) a small orange region below the '
         'dashed line')


def own_side():
    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (0, 2 / 3), (0.5, 34 / 35))
        P.axes([(0, '0'), (2 / 3, '2/3')],
               [(0.5, '1/2'), (11 / 14, '11/14'), (34 / 35, '34/35')], 'v',
               'd')
        shade(P, [(0, 0.5), (2 / 3, 0.5), (2 / 3, 34 / 35), (0, 34 / 35)],
              lambda v, d: min(profile_own_side(v, d, 0),
                               profile_own_side(v, d, CB)), 0.16, color=GREEN)
        P.line((0, 11 / 14), (2 / 3, 11 / 14), stroke=INK, width=1, dash='4 3')
        vals = {(0, 0.5): (0.15986, 0.02676), (2 / 3, 0.5): (0.10606, 0.11597),
                (0, 11 / 14): (0.15955, 0.01681),
                (2 / 3, 11 / 14): (0.05399, 0.05427),
                (0, 34 / 35): (0.14803, 0.00028),
                (2 / 3, 34 / 35): (0.00480, 0.00006)}
        for (v, d), (a, b) in vals.items():
            if abs(d - 11 / 14) < 1e-9:
                off = (0.07 if v == 0 else -0.07, 0.13)
                value_label(P, (v, d), fmt(a) + ' | ' + fmt(b), off,
                            'start' if v == 0 else 'end')
            else:
                value_label(P, (v, d), fmt(a) + ' | ' + fmt(b))
        legend(f, DX0, ['shading: the minimum over the faces ' + it('y') +
                        ';', 'at the corners: the bounds for both faces'])
        colour_bar(f, (DX0 + 0.7, -0.45), 0.16, color=GREEN)
    return case_figure(
        'appendix-d/own-side', [2, 5, 6, 9],
        {2: 41 / 20, 5: 1, 1: 3 / 8, 6: 1, 9: 1},
        (0.2, 0.1, 0.75), 0.12, domain,
        ['a missing south wing, ' + it('W') + ' on its', 'own axis, ' +
         it('S') + ' on the south side'],
        'Left: the squares of a missing south wing with W on its own axis and '
        'S on the south side of C, at v = 0.2, s = 0.1, d = 0.75, in the '
        'smallest disk that allows these separations (radius {R:.3f}); the '
        'separating lines of the stress with the weights 41/20, 1, 3/8, 1, 1 '
        'and its forces; the force on S points along the bisector of its two '
        'unit forces. Right: the domain of (v, d), shaded by the profile '
        'without the angle of S, with the lower bounds of Table D.9 for both '
        'faces at the corners; the dashed line d = 11/14 separates the third '
        'and the first cone for S')


# Figure: the monotonicity in d of Proposition D.15.

KAPPA15 = 1.038 * RB
C2_15 = (-0.795 + KAPPA15 / 8 + 1.59 / 24 * 121 / 196
         - MUP / 12 * (1 - 121 / 3920))


def monotone():
    f = Figure(0, 4.75, 0.08, 3.12, 100)
    lo, hi = 0.5, 11 / 14
    P = Plot(f, (1.0, 0.5, 3.2, 2.25), (lo, hi), (-0.07, 0.01))
    P.axes([(0.5, '1/2'), (0.6, '0.6'), (0.7, '0.7'), (hi, '11/14')],
           [(-0.06, MINUS + '0.06'), (-0.04, MINUS + '0.04'),
            (-0.02, MINUS + '0.02'), (0, '0')], 'd', '')
    P.line((lo, 0), (hi, 0), stroke=INK, width=0.8, dash='3 3')

    def fd(d):
        return (1.59 * math.cos(d) + MUP * math.sin(d)
                - KAPPA15 * math.cos(d / 2))

    def quad(d):
        return 1.59 - KAPPA15 + MUP * d + C2_15 * d * d
    P.curve([(d, fd(d)) for d in grid(lo, hi)], stroke=BLUE, width=2.2)
    P.curve([(d, quad(d)) for d in grid(lo, hi)], stroke=ORANGE, width=1.6,
            dash='6 3')
    dm = MUP / (2 * abs(C2_15))
    P.dot((dm, quad(dm)), r=3.4, fill=ORANGE)
    P.text((dm + 0.008, 0.0), num(quad(dm), 4), size=13, italic=False,
           color=ORANGE, anchor='start', dy=-11)
    P.text((0.735, fd(0.735)), it('f') + '(' + it('d') + ')', size=14,
           italic=False, color=BLUE, anchor='end', dx=-6, dy=10)
    P.text((0.72, quad(0.72)), 'quadratic bound', size=13, italic=False,
           color=ORANGE, anchor='start', dx=4, dy=-12)
    save(f, 'appendix-d/monotone', 'Graph over d from 1/2 to 11/14: the bound '
         'f(d) of the derivative of the profile in d, in blue, falls from '
         'about -0.009 to about -0.062; above it the dashed orange parabola '
         'that bounds it from above, whose highest point, about -0.0021, is '
         'marked; both stay below the dashed zero line')


def south_turned():
    quad = [(0, 0), (0, 2 / 3), (22 / 75, 2 / 3), (12 / 25, 12 / 25)]

    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (0, 2 / 3), (0, 2 / 3))
        P.axes([(0, '0'), (22 / 75, '22/75'), (12 / 25, '12/25'),
                (2 / 3, '2/3')], [(0, '0'), (12 / 25, '12/25'),
                                  (2 / 3, '2/3')], 'v', 's')
        shade(P, quad, lambda v, s: profile_south_turned(v, s, 11 / 14), 0.05,
              color=GREEN)
        vals = [0.00335, 0.00470, 0.02806, 0.00224]
        offs = [((0.17, 0.08), 'start'), ((0.07, -0.13), 'start'),
                ((0.0, 0.14), 'middle'), ((0.08, 0.0), 'start')]
        for pt, a, (off, anc) in zip(quad, vals, offs):
            value_label(P, pt, fmt(a), off, anc)
        legend(f, DX0, ['shading: the profile at ' + it('d') +
                        ' = 11/14, its minimum',
                        'in ' + it('d') + '; at the vertices: its lower bounds'])
        colour_bar(f, (DX0 + 0.7, -0.45), 0.05, color=GREEN)
    return case_figure(
        'appendix-d/south-turned', [2, 4, 6, 9],
        {2: 1.82, 4: 1.59, 6: 1.09, 9: 1},
        (0.15, 0.35, 0.75), 0.15, domain,
        ['a missing south wing, both on', 'their own axes, ' + it('v') +
         ' ≤ ' + it('s')],
        'Left: the squares of a missing south wing with W and S on their own '
        'axes, at v = 0.15, s = 0.35, d = 0.75, in the smallest disk that '
        'allows these separations (radius {R:.3f}); the separating lines of the '
        'stress with the weights 1.82, 1.59, 1.09, 1 and its forces. Right: the '
        'quadrilateral 0 <= v <= s <= 2/3, v + s <= 24/25 at d = 11/14, shaded '
        'by the profile, with the lower bounds of Table D.10 at its vertices')


# Figure: the three bounds of Lemma D.16.

def transverse_second(r):
    return MUP * math.cos(r) - 0.5 * math.sin(r) - math.cos(2 * r) / 6


def bounds():
    f = Figure(0, 8.4, 0.1, 3.15, 100)
    # (1) the wing harmonic and its secant
    P = Plot(f, (0.62, 0.5, 1.95, 2.2), (0, 12 / 25), (0.37, 0.65))
    P.axes([(0, '0'), (0.24, '6/25'), (12 / 25, '12/25')],
           [(0.4, '0.4'), (0.5, '0.5'), (0.6, '0.6')], 'x', '')
    P.curve([(x, wing_zeta(x)) for x in grid(0, 12 / 25)], stroke=BLUE,
            width=2.2)
    P.curve([(0, MUM), (12 / 25, MUM + 4 / 9 * 12 / 25)], stroke=ORANGE,
            width=1.6, dash='6 3')
    P.text((0.3, wing_zeta(0.3)), it('ζ') + '(' + it('x') + ')',
           size=14, italic=False, color=BLUE, anchor='end', dx=-6, dy=-10)
    P.text((0.3, MUM + 4 / 9 * 0.3),
           sb(it('μ'), MINUS, ' + 4' + it('x') + '/9', size=13), size=13,
           italic=False, color=ORANGE, anchor='start', dx=6, dy=12)
    f.text((0.65, 3.0), '(1)', size=13, italic=False, anchor='start')
    # (2) the second derivative of J and its line
    P = Plot(f, (3.52, 0.5, 1.95, 2.2), (0, 1), (-0.1, 0.5))
    P.axes([(0, '0'), (0.5, '1/2'), (1, '1')],
           [(0, '0'), (0.2, '0.2'), (0.4, '0.4')], 'r', '')
    P.line((0, 0), (1, 0), stroke=FAINT, width=0.8, dash='3 3')
    P.curve([(r, transverse_second(r)) for r in grid(0, 1)], stroke=BLUE,
            width=2.2)
    P.curve([(0, MUP - 1 / 6), (1, MUP - 1 / 6 - 1 / 3)], stroke=ORANGE,
            width=1.6, dash='6 3')
    P.text((0.62, transverse_second(0.62)), it('J') + '″(' + it('r') +
           ')', size=14, italic=False, color=BLUE, anchor='end', dx=-8,
           dy=8)
    P.text((0.5, MUP - 1 / 6 - 0.5 / 3),
           sb(it('μ'), '+', f' {MINUS} 1/6 {MINUS} ' + it('r') + '/3',
              size=13), size=13, italic=False, color=ORANGE, anchor='start',
           dx=8, dy=-12)
    f.text((3.55, 3.0), '(2)', size=13, italic=False, anchor='start')
    # (3) cos d + sin d and the level 4/3
    lo, hi = 0.5, 163 / 175
    P = Plot(f, (6.42, 0.5, 1.6, 2.2), (lo, hi), (1.3, 1.44))
    P.axes([(0.5, '1/2'), (PI / 4, 'π/4'), (hi, '163/175')],
           [(1.3, '1.3'), (4 / 3, '4/3'), (1.4, '1.4')], 'd', '')
    P.line((lo, 4 / 3), (hi, 4 / 3), stroke=ORANGE, width=1.6, dash='6 3')
    P.curve([(x, math.cos(x) + math.sin(x)) for x in grid(lo, hi)],
            stroke=BLUE, width=2.2)
    P.text((0.62, math.cos(0.62) + math.sin(0.62)), 'cos ' + it('d') +
           ' + sin ' + it('d'), size=13, italic=False, color=BLUE,
           anchor='start', dx=4, dy=14)
    f.text((6.45, 3.0), '(3)', size=13, italic=False, anchor='start')
    save(f, 'appendix-d/bounds', 'Three graphs. (1) Over x from 0 to 12/25, '
         'the wing harmonic, in blue, concave and above the dashed orange '
         'line mu- + 4x/9, which it meets at 0. (2) Over r from 0 to 1, the '
         'second derivative of J, in blue, falling from about 0.45 to about '
         '-0.02, below the dashed orange line mu+ - 1/6 - r/3, which it meets '
         'at 0. (3) Over d from 1/2 to 163/175, cos d + sin d, in blue, a '
         'concave arch with its top at pi/4, above the dashed orange level '
         '4/3')


def west_turned():
    quad = [(0, 0), (2 / 3, 0), (2 / 3, 22 / 75), (12 / 25, 12 / 25)]

    def domain(f):
        P = Plot(f, (DX0, 0.45, 2.6, 2.3), (0, 2 / 3), (0, 2 / 3))
        P.axes([(0, '0'), (12 / 25, '12/25'), (2 / 3, '2/3')],
               [(0, '0'), (22 / 75, '22/75'), (12 / 25, '12/25'),
                (2 / 3, '2/3')], 'v', 's')

        def low(v, s):
            return min(profile_west_turned(v, s, d, y)
                       for d in (0.5, 163 / 175) for y in (0, CB))
        shade(P, quad, low, 0.2, color=GREEN)
        vals = [(0.04975, 0.03763), (0.15924, 0.09099), (0.09268, 0.00262),
                (0.10805, 0.01784)]
        offs = [((0.3, 0.1), 'start'), ((-0.07, 0.13), 'end'),
                ((-0.07, -0.14), 'end'), ((0.0, 0.15), 'middle')]
        for pt, (a, b), (off, anc) in zip(quad, vals, offs):
            value_label(P, pt, fmt(a) + ' | ' + fmt(b), off, anc)
        legend(f, DX0, ['shading: the minimum over ' + it('y') +
                        ' and the two ends',
                        'of ' + it('d') + '; at the vertices: ' + it('d') +
                        ' = 1/2 | 163/175'])
        colour_bar(f, (DX0 + 0.7, -0.45), 0.2, color=GREEN)
    return case_figure(
        'appendix-d/west-turned', [2, 4, 6, 9],
        {2: 9 / 4, 4: 3 / 4, 1: 9 / 20, 6: 1, 9: 1},
        (0.35, 0.15, 0.75), 0.15, domain,
        ['a missing south wing, both on', 'their own axes, ' + it('s') +
         ' ≤ ' + it('v')],
        'Left: the squares of a missing south wing with W and S on their own '
        'axes, at v = 0.35, s = 0.15, d = 0.75, in the smallest disk that '
        'allows these separations (radius {R:.3f}); the separating lines of the '
        'stress with the weights 9/4, 3/4, 9/20, 1, 1 and its forces. Right: the '
        'quadrilateral 0 <= s <= v <= 2/3, v + s <= 24/25, shaded by the minimum '
        'of the profile over the faces y and the ends 1/2, 163/175 of d, with '
        'the lower bounds of Table D.11 (the smaller of the two faces)')


# Figure: the base profile (Lemma D.18).

def base():
    f = Figure(0, 8.0, 0.1, 3.3, 100)
    # left: delta' and the level 7/10
    P = Plot(f, (0.75, 0.5, 2.9, 2.3), (0, 1.2), (0.6, 1.25))
    P.axes([(0, '0'), (0.6, '3/5'), (1.2, '6/5')],
           [(0.7, '7/10'), (0.9, '0.9'), (1.1, '1.1')], 'x', '')

    def dprime(x):
        return (-math.sin(x) + SIGMA / 2 * (math.sin(x / 2) + math.cos(x / 2)))
    P.line((0, 0.7), (1.2, 0.7), stroke=ORANGE, width=1.6, dash='6 3')
    P.curve([(x, dprime(x)) for x in grid(0, 1.2)], stroke=BLUE, width=2.2)
    end = -S5(1.2) + SIGMA / 2 * (S7(0.6) + C6(0.6))
    P.dot((1.2, end), r=3.2, fill=INK)
    P.text((1.2, end), num(end, 4), size=13, italic=False, anchor='start',
           dx=9)
    P.text((0.3, dprime(0.3)), it('δ') + '′(' + it('x') + ')',
           size=14, italic=False, color=BLUE, anchor='start', dx=6, dy=-12)
    # right: the domain and the order of the argument
    lo, hi = 16 / 25, 11 / 14
    B = Plot(f, (4.85, 0.5, 2.6, 2.3), (0.25, 0.65), (0.62, 0.8))
    B.axes([(48 / 175, '48/175'), (21 / 50, '21/50'), (31 / 50, '31/50')],
           [(lo, '16/25'), (hi, '11/14')], 'v', 'd')
    quad = [(21 / 50, lo), (31 / 50, lo), (31 / 50, hi), (48 / 175, hi)]
    B.polygon(quad, fill=FILLS[2], stroke='none')
    for dd in (0.665, 0.69, 0.715, 0.74, 0.765):
        B.line((53 / 50 - dd, dd), (31 / 50, dd), stroke=GREEN, width=1.1)
    B.line((21 / 50, lo), (31 / 50, lo), stroke=GREEN, width=1.1)
    B.line((48 / 175, hi), (31 / 50, hi), stroke=GREEN, width=1.1)
    B.line((21 / 50, lo), (48 / 175, hi), stroke=PURPLE, width=2.6)
    B.line((31 / 50, lo), (31 / 50, hi), stroke=ORANGE, width=2.6)
    arrow(Shifted(f, 0, 0), B.P(31 / 50 + 0.012, 0.68),
          B.P(31 / 50 + 0.012, 0.75), ORANGE, width=1.4, head=8)
    B.text((0.31, 0.7), 'wall', size=13, italic=False, color=PURPLE,
           anchor='end')
    B.text((31 / 50 + 0.024, 0.715), 'top', size=13, italic=False,
           color=ORANGE, anchor='start')
    for pt in ((21 / 50, lo), (48 / 175, hi), (31 / 50, lo)):
        B.dot(pt, r=3.8, fill=INK)
    x, y = f.p(*B.P(31 / 50, hi))
    f.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.6" fill="#ffffff" '
          f'stroke="{INK}" stroke-width="1.4"/>')
    save(f, 'appendix-d/base', 'Two panels. Left: over x from 0 to 6/5, the '
         'derivative of delta, in blue, falling from about 1.19 to about 0.73 '
         'and staying above the dashed orange level 7/10; the Taylor bound '
         '0.7278 at 6/5 is marked. Right: the domain of (v, d) of section D.9, '
         'a green quadrilateral: its left edge, the wall, drawn purple, its '
         'right edge, the top, drawn orange with an arrow pointing up, and '
         'green horizontal segments across it; black dots mark the three '
         'points of the lemma, and an open circle the fourth corner')


def diagonal():
    k = 0.8
    f = Figure(0, 8.25, -0.6, 3.0, 100)
    rads = []
    for i, (names, weights, s, title) in enumerate((
            ([2, 5, 7, 8], {2: 41 / 20, 5: 1.5, 7: 1, 8: 1}, 0.0,
             '(a) ' + it('S') + ' on the south side of ' + it('C')),
            ([2, 4, 7, 8], {2: 41 / 20, 4: 2, 7: 1, 8: 1}, 0.2,
             '(b) ' + it('S') + ' on its own axis'))):
        Wd, rad, F, g = configuration(f, 1.6 + 2.72 * i, 1.6, names, weights,
                                      0.45, s, 0.72, 0.15, k)
        g.text((-0.32, -2.15), title, size=13, italic=False)
        rads.append(rad)
    X0 = 6.12
    P = Plot(f, (X0, 0.45, 1.75, 2.15), (0.25, 0.65), (0.62, 0.8))
    P.axes([(48 / 175, '48/175'), (31 / 50, '31/50')],
           [(16 / 25, '16/25'), (11 / 14, '11/14')], 'v', 'd')
    quad = [(21 / 50, 16 / 25), (31 / 50, 16 / 25), (31 / 50, 11 / 14),
            (48 / 175, 11 / 14)]

    def low(v, d):
        side = min(profile_diagonal_side(v, s, d) for s in (-0.4, 0, 0.4))
        own = min(profile_diagonal_own(v, s, d)
                  for s in (0, 0.15, 0.15 + 1e-9, 0.3, 0.3 + 1e-9, 0.48))
        return min(side, own)
    shade(P, quad, low, 0.03, color=GREEN)
    pts = [((21 / 50, 16 / 25), (0.01258, 0.00565), (-0.04, -0.17), 'middle'),
           ((48 / 175, 11 / 14), (0.00852, 0.00502), (0.15, -0.17), 'start'),
           ((31 / 50, 16 / 25), (0.01065, 0.00372), (-0.06, 0.16), 'end')]
    for pt, (a, b), off, anc in pts:
        value_label(P, pt, fmt(a) + ' | ' + fmt(b), off, anc)
    f.text((X0 + 0.55, -0.12), '(c) the domain of (' + it('v') + ', ' +
           it('d') + ')', size=13, italic=False)
    f.text((X0 + 0.55, -0.32), 'at the points: (a) | (b)', size=12,
           italic=False)
    save(f, 'appendix-d/diagonal', 'Three panels. (a) and (b): missing west '
         'wings with W on its own axis, at v = 0.45, d = 0.72: in (a) S on the '
         'south side of C, s = 0, in the smallest disk that allows these '
         f'separations (radius {rads[0]:.3f}), with the weights 41/20, 3/2, 1, '
         f'1; in (b) S on its own axis, s = 0.2 (radius {rads[1]:.3f}), with '
         'the weights 41/20, 2, 1, 1. D is separated from W by the line of its '
         'own upper left side and from S by a side of S; orange arrows show '
         'the forces. (c) The small quadrilateral domain of (v, d) left by '
         'Proposition D.7, shaded green by the minimum over s of the profiles '
         'of both cases, with the three points of Lemma D.18 and at each the '
         'smallest lower bounds of Tables D.12 and D.13')
    return rads


# Figure: the ranges of the angle of D covered by the cases.

def ranges():
    rows = [('D.10', 0.5, PI / 4, [(0.5, PI / 4)]),
            ('D.11', 0.5, PI / 4, [(0.5, PI / 4)]),
            ('D.12', 0.5, 11 / 14, [(0.5, PI / 4)]),
            ('D.14', 0.5, 34 / 35, [(0.5, PI / 4), (PI / 4, PI / 2 - 0.6)]),
            ('D.15', 0.5, PI / 4, [(0.5, PI / 4)]),
            ('D.17', 0.5, 163 / 175, [(0.5, PI / 4), (PI / 4, PI / 2 - 0.64)]),
            ('D.19 and D.20', 16 / 25, 11 / 14, [(16 / 25, PI / 4)])]
    f = Figure(0, 8.3, -0.25, 3.3, 100)
    P = Plot(f, (2.0, 0.35, 5.8, 2.9), (0.45, 1.0), (0, len(rows)))
    f.line(P.P(0.45, 0), shift(P.P(1.0, 0), (0.12, 0)), width=1, arrow=True)
    ticks = [(0.5, '1/2', 0), (16 / 25, '16/25', 0), (PI / 4, 'π/4', 0),
             (PI / 2 - 0.64, 'π/2 ' + MINUS + ' 16/25', 0),
             (PI / 2 - 0.6, 'π/2 ' + MINUS + ' 3/5', 1)]
    for x, s, row in ticks:
        f.line(P.P(x, 0), shift(P.P(x, 0), (0, -0.05 - 0.18 * row)), width=1)
        f.text(shift(P.P(x, 0), (0, -0.19 - 0.18 * row)), s, size=12,
               italic=False)
        P.line((x, 0), (x, len(rows)), stroke=FAINT, width=0.8, dash='3 3')
    f.text(shift(P.P(1.0, 0), (0.2, 0)), 'd', size=15, anchor='start')
    for k, (name, lo, hi, used) in enumerate(rows):
        y = len(rows) - k - 0.5
        P.polygon([(lo, y - 0.22), (hi, y - 0.22), (hi, y + 0.22),
                   (lo, y + 0.22)], fill=GREY, stroke=FAINT, width=0.8)
        for j, (a, b) in enumerate(used):
            col = BLUE if j == 0 else ORANGE
            P.polygon([(a, y - 0.12), (b, y - 0.12), (b, y + 0.12),
                       (a, y + 0.12)], fill=col, stroke='none')
        label = ('Propositions ' if ' and ' in name else 'Proposition ') + name
        f.text(shift(P.P(0.45, y), (-0.1, 0)), label, size=13, italic=False,
               anchor='end')
        end = {11 / 14: '11/14', 34 / 35: '34/35', 163 / 175: '163/175'}
        if hi in end:
            x0, y0 = shift(P.P(hi, y), (0.05, 0))
            wd = 0.065 * len(end[hi]) + 0.04
            f.polygon([(x0, y0 - 0.09), (x0 + wd, y0 - 0.09),
                       (x0 + wd, y0 + 0.09), (x0, y0 + 0.09)],
                      fill='#ffffff', stroke='none')
            f.text((x0 + 0.02, y0), end[hi], size=12, italic=False,
                   anchor='start')
    save(f, 'appendix-d/ranges', 'Seven horizontal bars over the axis of d, '
         'one for each of Propositions D.10, D.11, D.12, D.14, D.15, D.17, and '
         'D.19 with D.20: each grey bar is the range of d on which the '
         'proposition is proved, a blue part inside it the range used for '
         'normalized packings, d in (1/2, pi/4] or (16/25, pi/4], and for '
         'Propositions D.14 and D.17 an orange part, d in [pi/4, pi/2 - 3/5) '
         'or [pi/4, pi/2 - 16/25), the range used for the reflections of '
         'missing west wings; the upper ends 34/35 and 163/175 lie just beyond '
         'pi/2 - 3/5 and pi/2 - 16/25')


def main():
    angles()
    wings()
    forces_table()
    chord()
    curvature()
    gap()
    range_stress()
    walls()
    far_term_fig()
    side_west()
    side_small()
    side_large()
    south_force()
    own_side()
    monotone()
    south_turned()
    bounds()
    west_turned()
    base()
    diagonal()
    ranges()


if __name__ == '__main__':
    main()

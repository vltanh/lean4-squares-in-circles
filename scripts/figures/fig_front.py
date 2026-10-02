#!/usr/bin/env python3
"""Draw the figures of Chapters 1 to 3 of docs/proof/ (the introduction,
02-preliminaries.md and 03-tools.md) as SVG files in docs/proof/figures/,
in the directories 01-introduction/, 02-preliminaries/ and 03-tools/.

    python3 scripts/figures/fig_front.py

Every figure is computed from the geometry it illustrates: arcs by sampling
the circle and testing membership in the open squares, regions by clipping,
graphs by evaluating the functions, and each drawing asserts the facts its
caption states.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, subsup, clip, clip_square, quadrant_disk)

ORANGE, BLUE, GREEN, PURPLE = COLORS[1], COLORS[0], COLORS[2], COLORS[3]
RED = '#dc2626'
RED_FILL = '#fecaca'
SQRT3 = math.sqrt(3)


# ---------------------------------------------------------------- helpers

NB = '\u00a0'


def sbn(base, sub, after='', size=15):
    """sb() with non-breaking spaces, which every renderer keeps next to a
    tspan boundary."""
    return sb(base.replace(' ', NB), sub, after.replace(' ', NB), size)


def it(s):
    """Italic markup, for mathematics inside upright text."""
    return f'<tspan font-style="italic">{s}</tspan>'


def vtext(f, pos, s, size=13, color=INK, italic=True):
    """Text turned a quarter turn counterclockwise, centred at pos."""
    x, y = f.p(*pos)
    style = ' font-style="italic"' if italic else ''
    f.add(f'<text x="0" y="0" transform="translate({x:.1f} {y:.1f}) '
          f'rotate(-90)" font-size="{size}" font-family="Georgia, \'Times '
          f'New Roman\', serif" fill="{color}" text-anchor="middle" '
          f'dominant-baseline="middle"{style}>{s}</text>')


def polyline(f, pts, stroke=INK, width=1.4, dash=None, fill='none',
             opacity=1.0):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="{fill}" fill-opacity="{opacity}" '
          f'stroke="{stroke}" stroke-width="{width}" stroke-linejoin="round" '
          f'stroke-linecap="round"{extra}/>')


def arrowhead(f, tip, back, color=INK, size=9.0):
    """A filled arrowhead at `tip`, pointing away from the point `back`."""
    (x1, y1), (x0, y0) = f.p(*tip), f.p(*back)
    n = math.hypot(x1 - x0, y1 - y0)
    ux, uy = (x1 - x0) / n, (y1 - y0) / n
    bx, by = x1 - size * ux, y1 - size * uy
    px, py = -uy * 0.42 * size, ux * 0.42 * size
    f.add(f'<path d="M {x1:.1f} {y1:.1f} L {bx + px:.1f} {by + py:.1f} '
          f'L {bx - px:.1f} {by - py:.1f} z" fill="{color}"/>')


def arrow(f, a, b, color=INK, width=1.4, dash=None, size=9.0):
    """A segment from a to b with an arrowhead at b."""
    back = size * 0.7 / f.s
    d = math.hypot(b[0] - a[0], b[1] - a[1])
    end = shift(b, ((a[0] - b[0]) / d, (a[1] - b[1]) / d), back)
    f.line(a, end, stroke=color, width=width, dash=dash)
    arrowhead(f, b, a, color, size)


def arc_points(c, r, t0, t1, n=60):
    return [shift(c, u(t0 + (t1 - t0) * k / n), r) for k in range(n + 1)]


def arc_arrow(f, c, r, t0, t1, color=INK, width=1.3, size=8.0):
    """An arc from angle t0 to t1 (either way round) with a head at t1."""
    pts = arc_points(c, r, t0, t1)
    step = math.copysign(0.8 * size / (r * f.s), t1 - t0)
    polyline(f, arc_points(c, r, t0, t1 - 0.6 * step), stroke=color,
             width=width)
    arrowhead(f, pts[-1], shift(c, u(t1 - step), r), color, size)


def thin_arc(f, c, r, t0, t1, color=INK, width=1.2, dash=None):
    polyline(f, arc_points(c, r, t0, t1, 90), stroke=color, width=width,
             dash=dash)


def open_dot(f, c, r=3.6, stroke=INK, width=1.4):
    x, y = f.p(*c)
    f.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="#ffffff" '
          f'stroke="{stroke}" stroke-width="{width}"/>')


def word(f, pos, s, size=13, color=INK, anchor='middle'):
    f.text(pos, s, size=size, italic=False, color=color, anchor=anchor)


def rotate(p, t, about=(0.0, 0.0)):
    x, y = p[0] - about[0], p[1] - about[1]
    return (about[0] + x * math.cos(t) - y * math.sin(t),
            about[1] + x * math.sin(t) + y * math.cos(t))


def norm(p):
    return math.hypot(p[0], p[1])


def dot2(p, q):
    return p[0] * q[0] + p[1] * q[1]


def interiors_meet(P, Q, tol=1e-9):
    """Whether two convex polygons have overlapping interiors, up to a
    rounding tolerance: touching polygons do not meet."""
    for poly in (P, Q):
        for i in range(len(poly)):
            a, b = poly[i], poly[(i + 1) % len(poly)]
            n = (b[1] - a[1], a[0] - b[0])
            pa = [dot2(n, x) for x in P]
            pb = [dot2(n, x) for x in Q]
            if max(pa) <= min(pb) + tol or max(pb) <= min(pa) + tol:
                return False
    return True


def longest(runs):
    return max(runs, key=lambda run: run[1] - run[0])


def outside_disk_pieces(poly, R, per_edge=400):
    """The parts of a convex polygon outside the open disk |p| < R, as
    polygons: boundary runs outside the disk, closed along the circle."""
    pts = []
    for k in range(len(poly)):
        p, q = poly[k], poly[(k + 1) % len(poly)]
        pts += [(p[0] + (q[0] - p[0]) * j / per_edge,
                 p[1] + (q[1] - p[1]) * j / per_edge)
                for j in range(per_edge)]
    out = [norm(p) >= R for p in pts]
    if all(out) or not any(out):
        return [pts] if all(out) else []
    start = out.index(False)
    n, pieces, run = len(pts), [], []
    for j in range(start, start + n + 1):
        if out[j % n]:
            run.append(pts[j % n])
        elif run:
            t0 = math.atan2(run[-1][1], run[-1][0])
            t1 = math.atan2(run[0][1], run[0][0])
            while t1 < t0:
                t1 += 2 * math.pi
            if t1 - t0 > math.pi:
                t1 -= 2 * math.pi
            pieces.append(run + arc_points((0, 0), R, t0, t1, 30))
            run = []
    return pieces


def clip_segment(a, b, top, bottom=0.0):
    """The part of the segment ab inside the box [bottom, top]^2 (convex, so
    the kept samples are contiguous)."""
    pts = [(a[0] + (b[0] - a[0]) * j / 1000, a[1] + (b[1] - a[1]) * j / 1000)
           for j in range(1001)]
    pts = [x for x in pts if bottom - 1e-12 <= x[0] <= top
           and bottom - 1e-12 <= x[1] <= top]
    return pts[0], pts[-1]


def ab_axes_at(f, at, top):
    f.line(shift(at, (-0.08, 0)), shift(at, (top, 0)), width=1)
    f.line(shift(at, (0, -0.08)), shift(at, (0, top)), width=1)
    arrowhead(f, shift(at, (top + 0.04, 0)), shift(at, (0, 0)), size=8)
    arrowhead(f, shift(at, (0, top + 0.04)), shift(at, (0, 0)), size=8)
    f.text(shift(at, (top, -0.1)), 'a', anchor='end', size=14)
    f.text(shift(at, (-0.07, top - 0.02)), 'b', anchor='end', size=14)


def check_chart(c, deg, theta, eps, X, Y):
    """Condition (3.2) at m = 0 on a grid of points: o + r u(theta + eps t)
    lies in the open square exactly when (r cos t, r sin t) lies in
    Q(X, Y)."""
    for j in range(1, 40):
        r = 0.05 * j
        for k in range(90):
            t = 2 * math.pi * k / 90 + 0.011
            p = shift((0, 0), u(theta + eps * t), r)
            chart = (abs(r * math.cos(t) - X) < 0.5
                     and abs(r * math.sin(t) - Y) < 0.5)
            assert in_open_square(p, c, deg) == chart


def chart_axes(f, at, theta, eps, length=(1.15, 1.0), color=INK):
    """The axes t = 0 and t = pi/2 of a chart, drawn at o, with an arrow for
    the sense in which the chart angle increases."""
    a1, a2 = u(theta), u(theta + eps * math.pi / 2)
    arrow(f, at, shift(at, a1, length[0]), color=color, width=1.3, size=8)
    arrow(f, at, shift(at, a2, length[1]), color=color, width=1.3, size=8)
    arc_arrow(f, at, 0.3, theta + eps * 0.2, theta + eps * (math.pi / 2 - 0.2),
              color=color, width=1.2, size=7)
    return a1, a2


class Plot:
    """A graph panel inside a figure, with its own scales on the two axes."""

    def __init__(self, f, x0, y0, width, height, xlim, ylim):
        self.f, self.x0, self.y0 = f, x0, y0
        self.w, self.h, self.xlim, self.ylim = width, height, xlim, ylim

    def P(self, x, y):
        (a, b), (c, d) = self.xlim, self.ylim
        return (self.x0 + (x - a) / (b - a) * self.w,
                self.y0 + (y - c) / (d - c) * self.h)

    def curve(self, fn, a, b, n=240, **kw):
        polyline(self.f, [self.P(a + (b - a) * k / n, fn(a + (b - a) * k / n))
                          for k in range(n + 1)], **kw)

    def axes(self, xlabel, ylabel, xticks=(), yticks=(), x_at=0.0, y_at=0.0):
        f = self.f
        (a, b), (c, d) = self.xlim, self.ylim
        arrow(f, self.P(a, y_at), self.P(b, y_at), width=1, size=8)
        arrow(f, self.P(x_at, c), self.P(x_at, d), width=1, size=8)
        f.text(shift(self.P(b, y_at), (0, -0.16)), xlabel, size=14,
               anchor='end')
        f.text(shift(self.P(x_at, d), (-0.1, -0.02)), ylabel, size=14,
               anchor='end')
        for x, s in xticks:
            q = self.P(x, y_at)
            f.line(shift(q, (0, -0.04)), shift(q, (0, 0.04)), width=1)
            word(f, shift(q, (0, -0.17)), s, size=12)
        for y, s in yticks:
            q = self.P(x_at, y)
            f.line(shift(q, (-0.04, 0)), shift(q, (0.04, 0)), width=1)
            word(f, shift(q, (-0.08, 0)), s, size=12, anchor='end')


# ------------------------------------------------------------------ models

MODELS = {
    1: ([(0, 0)], math.sqrt(2) / 2, '√2/2'),
    2: ([(-0.5, 0), (0.5, 0)], math.sqrt(5) / 2, '√5/2'),
    3: ([(-0.5, -5 / 16), (0.5, -5 / 16), (0, 11 / 16)],
        5 * math.sqrt(17) / 16, '5√17/16'),
    4: ([(0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)], math.sqrt(2),
        '√2'),
    5: ([(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)], math.sqrt(2.5), '√(5/2)'),
    7: ([(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5), (0, -1), (0, 0), (0, 1)],
        math.sqrt(13) / 2, '√13/2'),
}

# Six squares: five axis-parallel squares and one turned by 45 degrees; a
# square is either its centre or a pair (centre, angle in degrees).
_H = math.sqrt(2) / 2
_A, _B = (1466 + 1940 * _H) / 267, (327 + 432 * _H) / 712
S6 = 2 * _B / (_A + math.sqrt(_A * _A - 4 * _B))
T6 = (-20 + 30 * _H) * S6 + 3.5 - 4.5 * _H
D6 = 0.5 + _H - T6
R6 = math.sqrt(2 * S6 * S6 + 4 * S6 + 2.5)
MODELS[6] = ([(S6, S6), (S6, S6 + 1), (S6 + 1, S6), (S6 - 1, T6),
              (T6, S6 - 1), ((-D6, -D6), 45)], R6, '√q* ≈ 1.6885')


def placed(c):
    """Centre and angle of a model square given as a centre or a pair."""
    return (c, 0.0) if isinstance(c[0], (int, float)) else c


def column(heights):
    return [(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5)] + [
        (0, y) for y in heights]


def check_model(centers, R):
    """Lemma 2.8: a packing in the closed disk of radius R about the origin,
    with a corner on the circle. Returns the corners on the circle. A turned
    square is checked by its vertices and by sampling for overlaps."""
    squares = [placed(c) for c in centers]
    for i, (p, deg) in enumerate(squares):
        assert all(norm(q) <= R + 1e-9 for q in square_corners(p, deg))
        for q, deg2 in squares[i + 1:]:
            if deg == 0 and deg2 == 0:
                assert max(abs(p[0] - q[0]), abs(p[1] - q[1])) >= 1 - 1e-12
            else:
                grid = [(p[0] + (i - 10) / 14, p[1] + (j - 10) / 14)
                        for i in range(21) for j in range(21)]
                assert not any(in_open_square(x, p, deg) and
                               in_open_square(x, q, deg2) for x in grid)
    touch = [q for c, deg in squares for q in square_corners(c, deg)
             if abs(norm(q) - R) < 1e-9]
    assert touch
    return touch


def draw_model(f, centers, R, at=(0.0, 0.0), phi=0.0, fills=None,
               strokes=None, touch=True, circle=True):
    corners = check_model(centers, R)
    if circle:
        f.circle(at, R, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(centers):
        fill = fills[k] if fills else FILLS[k % len(FILLS)]
        stroke = strokes[k] if strokes else COLORS[k % len(COLORS)]
        c, deg = placed(c)
        f.polygon([shift(at, rotate(q, phi)) for q in square_corners(c, deg)],
                  fill=fill, stroke=stroke)
    if touch:
        for q in corners:
            f.dot(shift(at, rotate(q, phi)), r=2.6)
    f.dot(at, r=2.6)


def chart_of(c, deg):
    """A chart (theta, eps) of the square with centre c and frame turned by
    deg, and its offsets (a, b), a >= b >= 0, by the moves of Lemma 3.21."""
    t = rad(deg)
    X, Y = dot2(c, u(t)), dot2(c, u(t + math.pi / 2))
    theta, eps = t, 1
    if X < 0:
        theta, X, Y = theta + math.pi, -X, -Y
    if Y < 0:
        eps, Y = -eps, -Y
    if Y > X:
        theta, eps, X, Y = theta + eps * math.pi / 2, -eps, Y, X
    for r in (0.2, 0.5, 0.9, 1.3, 1.7):
        for k in range(72):
            s = 2 * math.pi * k / 72 + 0.013
            p = shift((0, 0), u(theta + eps * s), r)
            chart = (abs(r * math.cos(s) - X) < 0.5
                     and abs(r * math.sin(s) - Y) < 0.5)
            assert in_open_square(p, c, deg) == chart
    return theta, eps, X, Y


def label(a, v):
    """The label of the state (a, v) of seven squares."""
    return min(1.25 * v, math.pi / 6 + (v - 0.5) / 3 + 0.75 * (1 - a),
               math.pi / 4)


def marker(c, deg):
    theta, eps, a, b = chart_of(c, deg)
    return theta + eps * label(a, b)


def phi_ab(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


# -------------------------------------------------------------- chapter 1

def optimal_packings():
    gap, s = 0.34, 58
    rows = [(1, 2, 3, 4), (5, 6, 7)]
    widths = [sum(2 * MODELS[n][1] for n in row) + gap * (len(row) - 1)
              for row in rows]
    W = max(widths)
    top = [max(MODELS[n][1] for n in row) for row in rows]
    label_h = 0.62
    H = 2 * top[0] + label_h + 0.28 + 2 * top[1] + label_h
    f = Figure(0, W, -H, 0, s)
    ys = [-top[0], -(2 * top[0] + label_h + 0.28 + top[1])]
    eq = NB + '=' + NB
    # The radii, with R and q italic and the numbers upright.
    radii = {1: '√2/2', 2: '√5/2', 3: '5√17/16', 4: '√2', 5: '√(5/2)',
             6: '√' + sb(it('q'), '*', NB + '≈' + NB + '1.6885', 14),
             7: '√13/2'}
    for row, width, R_top, y in zip(rows, widths, top, ys):
        x = (W - width) / 2
        for n in row:
            centers, R, name = MODELS[n]
            x += R
            draw_model(f, centers, R, at=(x, y))
            word(f, (x, y - R_top - 0.2), it('n') + f' = {n}', size=14)
            word(f, (x, y - R_top - 0.45),
                 sb(it('R'), str(n), eq + radii[n], 14), size=14)
            x += R + gap
    f.save('01-introduction/optimal', 'The seven optimal packings, n = 1 to 7, each '
           'in its dashed circle of radius R_n, drawn at a common scale; dots '
           'mark the corners on the circle')


def column_packings():
    R = math.sqrt(13) / 2
    top = SQRT3 - 0.5
    cases = [((-1, 0, 1), '(−1, 0, 1)'),
             ((-top, -top + 1, 1), '(½ − √3, 3/2 − √3, 1)'),
             ((-1.2, 0, 1), '(−1.2, 0, 1)'),
             ((-1, 0.2, 1.23), '(−1, 0.2, 1.23)')]
    gap, lab = 0.3, 0.45
    cell_w, cell_h = 2 * R + gap, 2 * R + lab + gap
    f = Figure(0, 2 * cell_w - gap, -2 * cell_h + gap, 0, 74)
    for k, (hs, name) in enumerate(cases):
        y1, y2, y3 = hs
        assert y1 + 1 <= y2 + 1e-12 and y2 + 1 <= y3 + 1e-12
        assert -top - 1e-12 <= y1 and y3 <= top + 1e-12
        at = (R + (k % 2) * cell_w, -R - (k // 2) * cell_h)
        centers = column(hs)
        fills = [FILLS[0]] * 4 + [FILLS[1]] * 3
        strokes = [COLORS[0]] * 4 + [COLORS[1]] * 3
        # The room of the middle column: [-1/2, 1/2] x [-sqrt 3, sqrt 3].
        f.polygon([shift(at, q) for q in ((-0.5, -SQRT3), (0.5, -SQRT3),
                                          (0.5, SQRT3), (-0.5, SQRT3))],
                  stroke=FAINT, width=1, dash='3 3')
        draw_model(f, centers, R, at=at, fills=fills, strokes=strokes)
        f.text(shift(at, (0.07, -0.11)), 'o', anchor='start', size=14)
        word(f, shift(at, (0, -R - 0.24)),
             '(' + sb(it('y'), '1', ',' + NB, 13) +
             sb(it('y'), '2', ',' + NB, 13) +
             sb(it('y'), '3', ')' + NB + '=' + NB, 13) + name, size=13)
    f.save('01-introduction/columns', 'Four column packings of seven squares in '
           'the circle of radius root 13 over 2 about o: the side squares are '
           'fixed, and the three middle squares move along the dotted middle '
           'column, each on its own')


def reduction():
    centers, R5, _ = MODELS[5]
    R = 0.9 * R5
    phi = rad(17)
    f = Figure(-1.75, 1.75, -1.75, 1.75, 150)
    f.circle((0, 0), R5, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(centers):
        poly = [rotate(q, phi) for q in square_corners(c)]
        f.polygon(poly, fill=FILLS[k], stroke=COLORS[k])
    for k, c in enumerate(centers):
        poly = [rotate(q, phi) for q in square_corners(c)]
        for piece in outside_disk_pieces(poly, R):
            f.polygon(piece, fill=RED_FILL, stroke=RED, width=1.2)
    f.circle((0, 0), R, stroke=RED, width=1.8)
    for q in check_model(centers, R5):
        f.dot(rotate(q, phi), r=3.2)
    t = rad(-62)
    f.line((0, 0), shift((0, 0), u(t), R), stroke=RED, width=1.2)
    f.text(shift(shift((0, 0), u(t), 0.55 * R), u(t + math.pi / 2), 0.12),
           'R', color=RED)
    t5 = rad(208)
    f.line((0, 0), shift((0, 0), u(t5), R5), width=1.2)
    f.text(shift(shift((0, 0), u(t5), 0.62 * R5), u(t5 + math.pi / 2), -0.12),
           sbn('R', '5'))
    f.dot((0, 0))
    f.text((0.06, 0.1), 'o', anchor='start')
    f.save('01-introduction/reduction', 'The plus turned about o in its dashed circle of '
           'radius R_5, and a smaller circle of radius R: the corners on the '
           'dashed circle, and the shaded parts of the squares around them, '
           'lie outside the smaller disk')


def arc_method():
    """Four squares on the circle of radius 1/2: an exterior square in the
    disk of radius root 2 holds more than a quarter unless o is a vertex, and
    a square whose closed square contains o holds the quarter facing its
    centre."""
    r, R, s = 0.5, math.sqrt(2), 108
    step = 2 * R + 0.3
    f = Figure(-R, step + R, -R - 0.05, R + 0.36, s)
    titles = [it('o') + ' outside ' + it('S'), it('o') + ' in ' + it('S')]
    for k, title in enumerate(titles):
        at = (k * step, 0)
        f.circle(at, R, stroke=INK, width=1.1, dash='6 4')
        word(f, shift(at, (0, R + 0.2)), title, size=14)
        # The circle of radius 1/2, labelled on the side away from S.
        f.text(shift(at, u(rad(40 if k == 0 else -40)), r + 0.17),
               sb('Γ', '1/2', size=14), size=14)
    # An exterior square with phi <= 2 and o not a vertex.
    a, b, theta = 0.62, 0.3, rad(205)
    assert phi_ab(a, b) <= 2 and a >= 0.5 and a + b < 1
    c, deg = rotate((a, b), theta), math.degrees(theta)
    assert max(norm(q) for q in square_corners(c, deg)) <= R
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    f.circle((0, 0), r)
    runs = arcs_in(lambda p: in_open_square(p, c, deg), r)
    t0, t1 = longest(runs)
    A, V = math.acos(2 * a - 1), math.asin(1 - 2 * b)
    assert abs((t1 - t0) - (A + min(A, V))) < 0.01 and t1 - t0 > math.pi / 2
    f.arc((0, 0), r, t0, t1, ORANGE, width=5)
    for t in (t0, t1):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    thin_arc(f, (0, 0), 0.16, t0, t1)
    f.text(shift((0, 0), u((t0 + t1) / 2), 0.72), '&gt;' + NB + '90°',
           size=13, italic=False, color=ORANGE)
    f.text(shift(c, rotate((0.25, -0.28), theta)), 'S', size=17, color=BLUE)
    f.dot((0, 0))
    f.text((0.06, 0.1), 'o', anchor='start')
    # A square whose closed square contains o.
    at = (step, 0)
    a, b, theta = 0.3, 0.15, rad(55)
    assert phi_ab(a, b) <= 2 and a <= 0.5
    c, deg = shift(at, rotate((a, b), theta)), math.degrees(theta)
    f.square(c, deg, fill=FILLS[2], stroke=GREEN)
    f.circle(at, r)
    member = lambda p: in_open_square(shift(p, at), c, deg)
    for q0, q1 in arcs_in(member, r):
        f.arc(at, r, q0, q1, GREEN, width=2.2)
    for k in range(1, 80):
        assert member(shift((0, 0), u(theta + k * math.pi / 160), r))
    f.arc(at, r, theta, theta + math.pi / 2, ORANGE, width=5)
    for t in (theta, theta + math.pi / 2):
        f.line(at, shift(at, u(t), r), width=1)
    thin_arc(f, at, 0.16, theta, theta + math.pi / 2)
    f.text(shift(at, u(theta + math.pi / 4), 0.32), '90°', size=13,
           italic=False, color=ORANGE)
    f.text(shift(c, rotate((0.3, 0.3), theta)), 'S', size=17, color=GREEN)
    f.dot(at)
    f.text(shift(at, (0.02, -0.13)), 'o', anchor='start')
    f.save('01-introduction/arc-method', 'Four squares and the circle of radius 1/2 '
           'about o, inside the disk of radius root 2. Left: a square that '
           'avoids o, without a vertex at o, holds more than a quarter of the '
           'circle. Right: a square containing o holds the quarter facing its '
           'centre')


def marker_arc(f, at, c, deg, m, color):
    """The arc of the unit circle of half-width 1/2 about the marker m,
    which lies in the closed square (Lemma 10.9)."""
    for k in range(41):
        p = u(m - 0.5 + k / 40)
        x, y = p[0] - c[0], p[1] - c[1]
        t = rad(deg)
        assert abs(math.cos(t) * x + math.sin(t) * y) <= 0.5 + 1e-9
        assert abs(-math.sin(t) * x + math.cos(t) * y) <= 0.5 + 1e-9
    f.arc(at, 1, m - 0.5, m + 0.5, color, width=4)


def markers():
    """Seven squares: markers of a contact are pi/3 apart; turned closer,
    the squares overlap; in a column packing the six markers form a
    regular hexagon. Each closed square contains the arc of the unit circle
    of half-width 1/2 about its marker."""
    R, s = math.sqrt(13) / 2, 60
    step = 2 * R + 0.3
    f = Figure(-R, 2 * step + R, -R - 0.1, R + 0.4, s)
    side, top = ((1, 0.5), 0), ((0, 1), 0)
    for k, (turn, title) in enumerate(((0, 'markers π/3 apart'),
                                       (-15, 'markers closer'))):
        at = (k * step, 0)
        f.circle(at, R, stroke=INK, width=1.1, dash='6 4')
        f.circle(at, 1)
        word(f, shift(at, (0, R + 0.25)), title, size=14)
        tc, tdeg = rotate(top[0], rad(turn)), top[1] + turn
        pieces = [(side[0], side[1], 0), (tc, tdeg, 2)]
        for c, deg, col in pieces:
            f.square(shift(at, c), deg, fill=FILLS[col], stroke=COLORS[col])
        ms = []
        for c, deg, col in pieces:
            theta, eps, a, b = chart_of(c, deg)
            assert phi_ab(a, b) <= 13 / 4 + 1e-12
            m = theta + eps * label(a, b)
            ms.append(m)
            marker_arc(f, at, c, deg, m, COLORS[col])
            f.line(at, shift(at, u(m), 1.0), stroke=COLORS[col], width=1.4)
            f.dot(shift(at, u(m), 1.0), r=3.4, fill=COLORS[col])
        gap = (ms[1] - ms[0]) % (2 * math.pi)
        thin_arc(f, at, 0.3, ms[0], ms[1])
        meet = interiors_meet(square_corners(*side), square_corners(tc, tdeg))
        if turn == 0:
            assert abs(gap - math.pi / 3) < 1e-12 and not meet
        else:
            assert gap < math.pi / 3 and meet
            poly = clip_square(square_corners(*side), tc, tdeg)
            f.polygon([shift(at, q) for q in poly], fill=RED_FILL, stroke=RED,
                      width=1.4)
        f.dot(at, r=2.6)
        f.text(shift(at, (-0.05, -0.1)), 'o', anchor='end', size=14)
    # A column packing with its six markers.
    at = (2 * step, 0)
    hs = (-1.2, 0, 1)
    centers = column(hs)
    fills = [FILLS[0]] * 4 + [FILLS[2], GREY, FILLS[2]]
    strokes = [BLUE] * 4 + [GREEN, FAINT, GREEN]
    draw_model(f, centers, R, at=at, fills=fills, strokes=strokes,
               touch=False)
    word(f, shift(at, (0, R + 0.25)), 'six markers', size=14)
    f.circle(at, 1)
    exterior = [c for c in centers if not in_open_square((0, 0), c)]
    ms = sorted(marker(c, 0) % (2 * math.pi) for c in exterior)
    assert len(ms) == 6
    for k in range(6):
        assert abs(ms[k] - (math.pi / 6 + k * math.pi / 3)) < 1e-12
    polyline(f, [shift(at, u(m)) for m in ms + ms[:1]], stroke=ORANGE,
             width=1.4, dash='5 4')
    for m in ms:
        f.line(at, shift(at, u(m)), stroke=ORANGE, width=1.2)
        f.dot(shift(at, u(m)), r=3.4, fill=ORANGE)
    # The label of o in the gap between the spokes at -30 and 30 degrees.
    f.text(shift(at, (0.3, 0.0)), 'o', anchor='start', size=14)
    f.save('01-introduction/markers', 'Seven squares and their markers on the '
           'unit circle. Left: a side square and the top square touch, their '
           'markers are exactly pi/3 apart, and each square contains the arc '
           'of half-width 1/2 about its marker. Middle: turned so that the '
           'markers are closer, the squares overlap. Right: in a column '
           'packing the six markers form a regular hexagon')


# -------------------------------------------------------------- chapter 2

def angle_between():
    """The angle d between two directions: on the circle, and as the least
    distance between real representatives."""
    x, xp = rad(30), rad(250)
    two = 2 * math.pi
    d = min(abs(x - xp - k * two) for k in (-1, 0, 1))
    assert 0 <= d <= math.pi and abs(d - rad(140)) < 1e-12
    f = Figure(-1.3, 7.0, -1.2, 1.3, 78)
    f.circle((0, 0), 1)
    thin_arc(f, (0, 0), 1, x, x + (two - d), color=FAINT, width=1.6,
             dash='5 4')
    f.arc((0, 0), 1, xp, xp + d, ORANGE, width=4)
    # The unit vector u(theta) is the radius to theta of the unit circle.
    arrow(f, (0, 0), u(x), color=BLUE, width=1.8, size=9)
    f.text(shift(shift((0, 0), u(x), 0.5), u(x + math.pi / 2), 0.15),
           'u(θ)', size=14, color=BLUE)
    f.line((0, 0), u(xp), width=1)
    for t, s in ((x, 'θ'), (xp, 'θ′')):
        f.dot(u(t))
        f.text(shift((0, 0), u(t), 1.16), s)
    f.text(shift((0, 0), u(xp + d / 2), 0.62), '∠(θ, θ′)', size=14,
           color=ORANGE)
    word(f, shift((0, 0), u(x + (two - d) / 2), 0.53), '2π − ∠(θ, θ′)',
         size=13, color=FAINT)
    f.dot((0, 0))
    f.text((0.06, -0.1), 'o', anchor='start', size=14)
    # The real line, from -6.6 to 7.6, at 0.36 units of the figure per unit.
    y0 = -0.1
    X = lambda t: 1.75 + (t + 6.6) * 0.36
    f.line((X(-6.6), y0), (X(7.45), y0), width=1)
    arrowhead(f, (X(7.6), y0), (X(7.0), y0), size=8)
    ticks = [(x - two, 'x − 2π', BLUE), (x, 'x', BLUE),
             (x + two, 'x + 2π', BLUE), (xp - two, 'x′ − 2π', ORANGE),
             (xp, 'x′', ORANGE)]
    for t, s, col in ticks:
        f.line((X(t), y0 - 0.09), (X(t), y0 + 0.09), stroke=col, width=2)
        f.text((X(t), y0 - 0.25), s, color=col, size=13)
    for lo, hi, s, col in ((xp - two, x, '∠(θ, θ′)', ORANGE),
                           (x, xp, '2π − ∠(θ, θ′)', FAINT)):
        h = 0.3
        f.line((X(lo), y0 + h), (X(hi), y0 + h), stroke=col, width=1.6)
        for t in (lo, hi):
            f.line((X(t), y0 + h - 0.06), (X(t), y0 + h + 0.06), stroke=col,
                   width=1.6)
        f.text(((X(lo) + X(hi)) / 2, y0 + h + 0.17), s, size=14, color=col)
    f.save('02-preliminaries/angle', 'The unit vector u(theta) and the angle '
           'between two directions theta and theta prime: the shorter way '
           'round the unit circle, and the least distance between real '
           'numbers that represent them')


def arcsin_graph():
    """The extended arcsin and arccos on the real line."""
    ext = lambda x: math.asin(max(-1.0, min(1.0, x)))
    f = Figure(-2.35, 2.45, -1.95, 3.55, 64)
    P = lambda x, y: (x, y * 0.95)
    for y in (-math.pi / 2, math.pi / 2, math.pi):
        f.line(P(-2.2, y), P(2.2, y), stroke=GREY, width=1)
    for x in (-1, 1):
        f.line(P(x, -math.pi / 2 - 0.1), P(x, math.pi + 0.1), stroke=GREY,
               width=1)
    arrow(f, P(-2.3, 0), P(2.35, 0), width=1, size=8)
    arrow(f, P(0, -1.95), P(0, 3.6), width=1, size=8)
    f.text(shift(P(2.35, 0), (0, -0.2)), 'x', anchor='end', size=14)
    polyline(f, [P(-2.2 + 4.4 * k / 400, ext(-2.2 + 4.4 * k / 400))
                 for k in range(401)], stroke=BLUE, width=2.2)
    polyline(f, [P(-2.2 + 4.4 * k / 400, math.pi / 2 - ext(-2.2 + 4.4 * k /
                                                            400))
                 for k in range(401)], stroke=ORANGE, width=2.2)
    for x in (-1, 1):
        word(f, shift(P(x, 0), (0.1, -0.17)), str(x).replace('-', '−'),
             size=12)
    # Below the grid lines: for x < 0 the arccosine runs above pi/2, so it
    # does not cross the labels.
    for y, s in ((-math.pi / 2, '−π/2'), (math.pi / 2, 'π/2'),
                 (math.pi, 'π')):
        word(f, shift(P(0, y), (-0.08, -0.13)), s, size=12, anchor='end')
    word(f, P(1.75, math.pi / 2 + 0.22), 'arcsin', size=14, color=BLUE)
    word(f, P(-1.75, math.pi + 0.22), 'arccos', size=14, color=ORANGE)
    f.save('02-preliminaries/arcsin', 'The extended arcsine, constant at minus and plus '
           'pi over 2 outside the interval from -1 to 1, and the arccosine, pi '
           'over 2 minus the arcsine')


def quarter_frame():
    """The same square and point, read in a frame and in its quarter turn."""
    deg, x, y = 20, 0.42, 0.3
    e1, e2 = u(rad(deg)), u(rad(deg + 90))
    m1 = (-e1[0], -e1[1])
    step = 2.35
    f = Figure(-0.95, step + 0.95, -0.8, 1.15, 150)
    frames = [(e1, e2, (subsup('e', '1', 'S', 14), subsup('e', '2', 'S', 14)),
               (sbn('x', 'S', '(p)', 14), sbn('y', 'S', '(p)', 14)),
               'the frame of ' + it('S')),
              (e2, m1, (subsup('e', '2', 'S', 14),
                        '−' + subsup('e', '1', 'S', 14)),
               (sbn('y', 'S', '(p)', 14), '−' + sbn('x', 'S', '(p)', 14)),
               'turned by a quarter turn')]
    for k, (a1, a2, names, coords, title) in enumerate(frames):
        c = (k * step, 0)
        p = shift(shift(c, e1, x), e2, y)
        f.square(c, deg, fill=FILLS[0], stroke=BLUE)
        v = (p[0] - c[0], p[1] - c[1])
        cx, cy = dot2(v, a1), dot2(v, a2)
        assert abs(cx - (x if k == 0 else y)) < 1e-12
        assert abs(cy - (y if k == 0 else -x)) < 1e-12
        for a, name in ((a1, names[0]), (a2, names[1])):
            arrow(f, c, shift(c, a, 0.78), width=1.4)
            f.text(shift(c, a, 0.9), name, size=14)
        q = shift(c, a1, cx)
        f.line(c, q, stroke=ORANGE, width=2.6)
        f.line(q, p, stroke=ORANGE, width=2.6)
        # Label each leg on its outer side.
        mid1 = shift(c, a1, cx / 2)
        side1 = (-a2[0], -a2[1]) if cy > 0 else a2
        f.text(shift(mid1, side1, 0.13), coords[0], size=14, color=ORANGE)
        mid2 = shift(q, a2, cy / 2)
        if k == 0:
            f.text(shift(mid2, a1, 0.1), coords[1], size=14, color=ORANGE,
                   anchor='start')
        else:
            f.text(shift(mid2, a1, -0.16), coords[1], size=14, color=ORANGE)
        f.dot(c)
        f.dot(p, fill=ORANGE)
        f.text(shift(p, (0.05, 0.07)), 'p', anchor='start', color=ORANGE)
        f.text(shift(c, (-0.06, -0.1)), sbn('c', 'S'), anchor='end')
        f.text((c[0], 1.05), title, size=13, italic=False)
    f.save('02-preliminaries/quarter-frame', 'The same square S and point p read in the '
           'frame e1, e2 and in the frame turned by a quarter turn, e2, -e1: '
           'the local coordinates (x, y) become (y, -x)')


def touching():
    """Disjoint squares may share part of an edge or a vertex; overlapping
    ones are not disjoint."""
    deg = 20
    e1, e2 = u(rad(deg)), u(rad(deg + 90))
    cases = [(shift(shift((0, 0), e1, 1.0), e2, 0.4), deg,
              'part of an edge shared', 'disjoint', GREEN),
             (shift((0, 0), e1, 0.5 + math.sqrt(2) / 2), deg + 45,
              'a vertex on an edge', 'disjoint', GREEN),
             (shift(shift((0, 0), e1, 0.72), e2, 0.3), deg, 'overlapping',
              'not disjoint', RED)]
    step = 2.75
    f = Figure(-0.8, 2 * step + 2.0, -1.0, 1.62, 84)
    for k, (tc, tdeg, title, verdict, col) in enumerate(cases):
        at = (k * step, 0)
        S, T = square_corners(at, deg), square_corners(shift(at, tc), tdeg)
        assert interiors_meet(S, T) == (k == 2)
        f.polygon(S, fill=FILLS[0], stroke=BLUE, opacity=0.9)
        f.polygon(T, fill=FILLS[1], stroke=ORANGE, opacity=0.9)
        if k == 2:
            f.polygon(clip_square(S, shift(at, tc), tdeg), fill=RED_FILL,
                      stroke=RED, width=1.4)
        if k == 0:
            # The common part of the two edges.
            a = shift(shift(at, e1, 0.5), e2, -0.1)
            b = shift(shift(at, e1, 0.5), e2, 0.5)
            f.line(a, b, stroke=INK, width=3.2)
        if k == 1:
            f.dot(shift(at, e1, 0.5), r=4)
        f.text(shift(at, (-0.25, -0.2)), 'S', size=16, color=BLUE)
        f.text(shift(shift(at, tc), (0.1, 0.12)), 'T', size=16, color=ORANGE)
        word(f, (at[0] + 0.55, 1.5), title, size=14)
        word(f, (at[0] + 0.55, -0.92), verdict, size=14, color=col)
    f.save('02-preliminaries/touching', 'Left: two squares sharing part of an edge. '
           'Middle: a vertex of one square on an edge of the other. Both '
           'pairs are disjoint, since their open squares do not meet. Right: '
           'two overlapping squares, which are not disjoint')


def frame_map():
    """The frame F_phi carries the plane of the model onto the plane at o:
    the grid, the square Q(c) and the distance of a point from 0."""
    phi, c, q = rad(28), (1.0, 0.5), (-0.55, 0.85)
    o = (4.3, -0.3)
    F = lambda p: shift(o, rotate(p, phi))
    f = Figure(-1.45, 6.55, -1.7, 1.95, 86)
    xs, ys = (-1, 0, 1), (-1, 0, 1)
    box = (-1.25, 1.75, -1.2, 1.35)
    for M in (lambda p: p, F):
        for x in xs:
            f.line(M((x, box[2])), M((x, box[3])), stroke=GREY, width=1)
        for y in ys:
            f.line(M((box[0], y)), M((box[1], y)), stroke=GREY, width=1)
        arrow(f, M((box[0], 0)), M((box[1] + 0.1, 0)), width=1.1, size=8)
        arrow(f, M((0, box[2])), M((0, box[3] + 0.1)), width=1.1, size=8)
        f.polygon([M(p) for p in square_corners(c)], fill=FILLS[0],
                  stroke=BLUE)
        f.dot(M(c), fill=BLUE)
        centre = M((0, 0))
        f.circle(centre, norm(q), stroke=ORANGE, width=1.2, dash='4 3')
        f.line(centre, M(q), stroke=ORANGE, width=1.8)
        f.dot(M(q), fill=ORANGE)
        f.dot(centre)
    # Distances are kept, and Q(c) goes onto the square sitting at c.
    assert abs(norm((F(q)[0] - o[0], F(q)[1] - o[1])) - norm(q)) < 1e-12
    for k in range(200):
        p = (-1.2 + 3 * (k % 20) / 20, -1.1 + 2.4 * (k // 20) / 10)
        assert (in_open_square(F(p), F(c), math.degrees(phi))
                == in_open_square(p, c))
    f.text((-0.08, -0.12), '0', anchor='end', size=14, italic=False)
    f.text((1.87, -0.14), 'x', size=14)
    f.text((0.14, 1.47), 'y', size=14)
    f.text(shift(q, (-0.02, 0.14)), 'q', color=ORANGE)
    f.text(shift(c, (0.0, 0.27)), 'Q(c)', color=BLUE, size=14)
    f.text(shift(o, (-0.1, -0.16)), 'o', size=14, anchor='end')
    f.text((F(q)[0] - 0.08, F(q)[1] + 0.26), sbn('F', 'φ', '(q)'),
           color=ORANGE, anchor='end')
    f.text((F(c)[0] + 0.1, 1.5), sbn('F', 'φ', '(Q(c))', 14), color=BLUE,
           size=14)
    f.text(shift(F((box[1] + 0.1, 0)), (0.05, -0.2)), 'u(φ)', size=14,
           anchor='middle')
    f.text(shift(F((0, box[3] + 0.1)), (-0.08, 0.1)), 'u(φ + π/2)', size=14,
           anchor='end')
    f.line(o, shift(o, (1.3, 0)), stroke=FAINT, width=1, dash='3 3')
    thin_arc(f, o, 0.55, 0, phi)
    f.text(shift(o, u(phi / 2), 0.68), 'φ', size=14)
    arrow(f, (1.95, 0.75), (2.75, 0.75), width=1.6)
    f.text((2.35, 0.95), sbn('F', 'φ'), size=16)
    f.save('02-preliminaries/frame-map', 'The frame F_phi carries the plane with origin '
           '0 onto the plane with origin o, turned by phi: the grid, the '
           'square Q(c) and the point q go to the turned grid, the square '
           'sitting at c, and a point at the same distance from o')


def congruence_figure():
    """A model, and a configuration congruent to it: the frame F_phi and a
    relabelling."""
    centers, R, _ = MODELS[3]
    phi = rad(35)
    names = ['2', '3', '1']
    o = (3.15, 0)
    F = lambda p: shift(o, rotate(p, phi))
    f = Figure(-1.4, o[0] + 1.4, -1.4, 1.5, 115)
    q = (-1.0, -13 / 16)
    assert abs(norm(q) - R) < 1e-12
    # The names sit off the segment from the centre to q, which crosses the
    # square of M1 below its centre.
    offsets = [(-0.08, 0.17), (0.0, 0.0), (0.0, 0.12)]
    for side, M, centre in ((0, lambda p: p, (0, 0)), (1, F, o)):
        f.circle(centre, R, stroke=INK, width=1.2, dash='6 4')
        for k, c in enumerate(centers):
            f.polygon([M(p) for p in square_corners(c)], fill=FILLS[k],
                      stroke=COLORS[k])
            text = sbn('M', str(k + 1)) if side == 0 else sbn('S', names[k])
            f.text(M(shift(c, offsets[k])), text, size=16, color=COLORS[k])
        f.line(centre, M(q), stroke=ORANGE, width=1.6)
        f.dot(M(q), fill=ORANGE)
        f.dot(centre)
    f.text((0.07, 0.1), '0', anchor='start', size=14, italic=False)
    f.text(shift(o, (0.08, 0.1)), 'o', anchor='start', size=14)
    f.text(shift(q, (0.0, -0.14)), 'q', color=ORANGE, size=14)
    f.text(shift(F(q), (0.1, -0.1)), sbn('F', 'φ', '(q)', 14), color=ORANGE,
           anchor='start', size=14)
    arrow(f, (1.35, 1.18), (1.85, 1.18), width=1.6)
    f.text((1.6, 1.37), sbn('F', 'φ'), size=15)
    f.save('02-preliminaries/congruence', 'Left: the T as a model M1, M2, M3 in the disk '
           'of radius R about 0. Right: a configuration congruent to it, '
           'turned by phi about o and relabelled; a point q of M1 and its '
           'image are at the same distance from the centre')


def axis_lemma():
    """Lemma 2.8 (2): every point of Q(c), c = (x, y), lies in the box
    |p1| <= |x| + 1/2, |p2| <= |y| + 1/2, and the corner of Q(c) farthest
    from the origin is the corner of the box on the side of c."""
    c = (-0.7, 0.62)
    B, C = abs(c[0]) + 0.5, abs(c[1]) + 0.5
    corner = (-B, C)
    R = math.hypot(B, C) + 0.1
    far = max(square_corners(c), key=norm)
    assert abs(far[0] - corner[0]) < 1e-12 and abs(far[1] - corner[1]) < 1e-12
    assert all(abs(p[0]) <= B + 1e-12 and abs(p[1]) <= C + 1e-12
               for p in square_corners(c))
    assert norm(corner) <= R
    s = 110
    f = Figure(-R - 0.08, R + 0.12, -R - 0.08, R + 0.08, s)
    f.circle((0, 0), R, stroke=INK, width=1.2, dash='6 4')
    f.line((-R + 0.05, 0), (R - 0.05, 0), stroke=FAINT, width=1)
    f.line((0, -R + 0.05), (0, R - 0.05), stroke=FAINT, width=1)
    f.polygon([(-B, -C), (B, -C), (B, C), (-B, C)], stroke=FAINT, width=1.4)
    f.square(c, fill=FILLS[0], stroke=BLUE)
    f.dot(c, fill=BLUE)
    f.text(shift(c, (-0.08, -0.1)), 'c', color=BLUE, anchor='end')
    f.text((-0.42, 0.93), 'Q(c)', color=BLUE, size=14)
    f.line((0, 0), (-B, 0), stroke=ORANGE, width=2.4)
    f.line((-B, 0), corner, stroke=ORANGE, width=2.4)
    f.line((0, 0), corner, stroke=ORANGE, width=1.4, dash='5 3')
    f.dot(corner, fill=ORANGE)
    f.text((-B / 2, -0.15), '|x| + ½', size=13, color=ORANGE)
    vtext(f, (-B - 0.13, C / 2), '|y| + ½', size=13, color=ORANGE)
    t = rad(-50)
    f.line((0, 0), shift((0, 0), u(t), R), width=1)
    f.text(shift(shift((0, 0), u(t), 0.62 * R), u(t + math.pi / 2), 0.12),
           'R', size=14)
    f.dot((0, 0))
    f.text((0.08, 0.13), '0', anchor='start', size=14, italic=False)
    f.save('02-preliminaries/axis-lemma', 'An axis-parallel square Q(c) with '
           'c = (x, y) in the second quadrant, inside the box where the first '
           'coordinate is at most |x| + 1/2 and the second at most |y| + 1/2 '
           'in absolute value; its farthest corner from the origin is the '
           'corner of the box, |x| + 1/2 across and |y| + 1/2 up, inside the '
           'dashed circle of radius R')


def lower_bound():
    """Proposition 2.9: the corner of the model on the circle of radius R_3
    stays at that distance in every congruent configuration."""
    centers, R3, _ = MODELS[3]
    R, phi = 0.88 * R3, rad(25)
    p = (-1.0, -13 / 16)
    assert abs(norm(p) - R3) < 1e-12
    o = (3.05, 0)
    F = lambda x: shift(o, rotate(x, phi))
    f = Figure(-1.4, o[0] + 1.4, -1.62, 1.52, 115)
    for M, centre in ((lambda x: x, (0, 0)), (F, o)):
        f.circle(centre, R3, stroke=INK, width=1.2, dash='6 4')
        for k, c in enumerate(centers):
            f.polygon([M(x) for x in square_corners(c)], fill=FILLS[k],
                      stroke=COLORS[k])
        f.line(centre, M(p), stroke=ORANGE, width=1.8)
        f.dot(M(p), fill=ORANGE, r=4)
        f.dot(centre)
    f.circle(o, R, stroke=RED, width=1.8)
    assert norm((F(p)[0] - o[0], F(p)[1] - o[1])) > R
    f.text((0.07, 0.1), '0', anchor='start', size=14, italic=False)
    f.text(shift(o, (0.07, 0.1)), 'o', anchor='start', size=14)
    f.text(shift(p, (-0.04, -0.14)), 'p', color=ORANGE, anchor='end')
    f.text(shift(F(p), (-0.06, -0.15)), sbn('F', 'φ', '(p)'), color=ORANGE,
           anchor='end')
    f.text(shift((0, 0), u(rad(135)), R3 + 0.12), sbn('R', '3'), size=14)
    f.text(shift(o, u(rad(62)), R - 0.17), 'R', color=RED, size=14)
    f.text(shift(o, u(rad(100)), R3 + 0.12), sbn('R', '3'), size=14)
    arrow(f, (1.3, 1.25), (1.8, 1.25), width=1.6)
    f.text((1.55, 1.42), sbn('F', 'φ'), size=15)
    f.save('02-preliminaries/lower-bound', 'Left: the T reaching the circle of radius '
           'R_3 at a corner p. Right: a congruent configuration at o, whose '
           'corner F_phi(p) is at the same distance from o, outside the '
           'smaller disk of radius R')


def scheme():
    """Corollary 2.10 (a) and (b) for the six optimal models: each lies in
    its disk, and one corner p reaches the circle, |p|^2 = R_n^2."""
    corners = {1: ((0.5, 0.5), '¼ + ¼ = ½'),
               2: ((1, 0.5), '1 + ¼ = 5/4'),
               3: ((-1, -13 / 16), '1 + 169/256 = 425/256'),
               4: ((1, 1), '1 + 1 = 2'),
               5: ((1.5, 0.5), '9/4 + ¼ = 5/2'),
               6: ((S6 + 1.5, S6 + 0.5),
                   '(' + sb(it('s'), '*', NB + '+' + NB + '3/2)²' + NB + '+'
                            + NB + '(', 12)
                   + sb(it('s'), '*', NB + '+' + NB + '½)²' + NB + '=' + NB,
                        12)
                   + sb(it('q'), '*', size=12)),
               7: ((1.5, -1), '9/4 + 1 = 13/4')}
    gap, s = 0.62, 56
    rows = [(1, 2, 3, 4), (5, 6, 7)]
    widths = [sum(2 * MODELS[n][1] for n in row) + gap * (len(row) - 1)
              for row in rows]
    W = max(widths)
    top = [max(MODELS[n][1] for n in row) for row in rows]
    label_h = 0.72
    ys = [-top[0], -(2 * top[0] + label_h + 0.3 + top[1])]
    H = -ys[1] + top[1] + label_h
    f = Figure(-0.1, W + 0.1, -H, 0.05, s)
    for row, width, R_top, y in zip(rows, widths, top, ys):
        x = (W - width) / 2
        for n in row:
            centers, R, _ = MODELS[n]
            p, text = corners[n]
            assert abs(norm(p) - R) < 1e-12
            assert any(norm((p[0] - q[0], p[1] - q[1])) < 1e-12
                       for c in centers for q in square_corners(*placed(c)))
            x += R
            at = (x, y)
            draw_model(f, centers, R, at=at, touch=False)
            f.line(at, shift(at, p), stroke=ORANGE, width=1.8)
            f.dot(shift(at, p), r=4, fill=ORANGE)
            word(f, (x, y - R_top - 0.22), it('n') + f' = {n}', size=13)
            f.text((x, y - R_top - 0.47), '|' + it('p') + '|² = ' + text,
                   size=12, italic=False, color=ORANGE)
            x += R + gap
    f.save('02-preliminaries/scheme', 'The seven optimal models, each in its dashed circle '
           'of radius R_n, with one corner p on the circle and its squared '
           'distance from the centre, which equals R_n squared')


# --------------------------------------------- chapters 1 and 2, added

def disk_constraint():
    """The disk constraint at the radius root 2 of four squares. Left: a
    square S with the offsets (a_S, b_S) = (0.62, 0.25) of o, and its vertex
    farthest from o, at distance root phi(a_S, b_S). Right: the pair
    (a_S, b_S) in the disk phi <= 2 of the (a, b)-plane, and the tangent
    a + b = 1 at (1/2, 1/2)."""
    R, s = math.sqrt(2), 96
    a, b, deg = 0.62, 0.25, 25
    e1, e2 = u(rad(deg)), u(rad(deg + 90))
    c = shift(shift((0, 0), e1, a), e2, b)
    v = shift(shift(c, e1, 0.5), e2, 0.5)
    # Definition 3.1 and Lemma 3.4: the offsets of o from c, and the
    # farthest vertex, at squared distance phi(a, b) <= 2 from o.
    X, Y = dot2((-c[0], -c[1]), e1), dot2((-c[0], -c[1]), e2)
    assert abs(max(abs(X), abs(Y)) - a) < 1e-12
    assert abs(min(abs(X), abs(Y)) - b) < 1e-12
    far = max(square_corners(c, deg), key=norm)
    assert norm((far[0] - v[0], far[1] - v[1])) < 1e-12
    assert abs(norm(v) ** 2 - phi_ab(a, b)) < 1e-12 and phi_ab(a, b) <= 2
    assert a + b < 1
    # The (a, b)-plane: the pair (x, y) is drawn at A + k (x, y).
    k, A = 2.0, (R + 0.75, -1.12)
    P = lambda x, y: (A[0] + k * x, A[1] + k * y)
    top = 1.22
    f = Figure(-R - 0.06, P(top, 0)[0] + 0.12, -R - 0.06, R + 0.06, s)
    # Left: the square in the disk. F maps frame coordinates of S, with
    # origin o, to the plane.
    F = lambda x, y: shift(shift((0, 0), e1, x), e2, y)
    f.circle((0, 0), R, stroke=INK, width=1.2, dash='6 4')
    t = rad(205)
    f.line((0, 0), shift((0, 0), u(t), R), width=1)
    f.text(shift(shift((0, 0), u(t), 0.6 * R), u(t + math.pi / 2), -0.13),
           'R', size=15)
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    f.text(F(a + 0.3, b - 0.3), 'S', size=17, color=BLUE)
    # The path from o to c_S: a_S along e1, then b_S along e2. The segment
    # to the farthest vertex runs above it.
    assert (b + 0.5) / (a + 0.5) > b / a
    f.line((0, 0), F(a, 0), stroke=ORANGE, width=2.4)
    f.line(F(a, 0), c, stroke=ORANGE, width=2.4)
    f.text(F(a / 2, -0.12), sbn('a', 'S', size=14), size=14, color=ORANGE)
    f.text(F(a - 0.06, b / 2), sbn('b', 'S', size=14), size=14,
           color=ORANGE, anchor='end')
    f.line((0, 0), v, width=1.4, dash='5 3')
    f.dot(v, r=4)
    # The length of the segment, written along it.
    x, y = f.p(*shift(shift((0, 0), v, 0.58), (-v[1], v[0]), 0.14 / norm(v)))
    turn = -math.degrees(math.atan2(v[1], v[0]))
    f.add(f'<text x="{x:.1f}" y="{y:.1f}" transform="rotate({turn:.1f} '
          f'{x:.1f} {y:.1f})" font-size="14" font-family="Georgia, '
          f'\'Times New Roman\', serif" fill="{INK}" text-anchor="middle" '
          f'dominant-baseline="middle" font-style="italic">√φ('
          + sb('a', 'S', ',' + NB, 14) + sb('b', 'S', ')', 14) + '</text>')
    f.dot(c, fill=BLUE)
    f.text(F(a + 0.07, b - 0.04), sbn('c', 'S', size=14), size=14,
           color=BLUE, anchor='start')
    f.dot((0, 0))
    f.text((-0.05, -0.1), 'o', anchor='end')
    # Right: the (a, b)-plane.
    region = quadrant_disk(2.0, 120)
    f.polygon([P(*x) for x in region], fill=FILLS[0], stroke=BLUE, width=1.4)
    f.line(P(0, 0), P(top - 0.05, top - 0.05), stroke=FAINT, width=1,
           dash='2 3')
    tangent = [(x, 1 - x) for x in (-0.06, 1.06)]
    f.line(P(*tangent[0]), P(*tangent[1]), width=1.2, dash='6 4')
    for x, y in region[1:]:
        assert x + y <= 1 + 1e-12
    f.dot(P(0.5, 0.5), r=3.4)
    f.text(shift(P(0.06, 1.0), (0.05, 0.02)), it('a') + NB + '+' + NB +
           it('b') + NB + '=' + NB + '1', size=14, italic=False,
           anchor='start')
    f.text(P(0.15, 0.5), 'φ ≤ 2', size=14, color=BLUE)
    f.dot(P(a, b), r=4, fill=ORANGE)
    # Below the diagonal and inside the arc, left of the point.
    f.text(shift(P(a, b), (-0.1, -0.1)),
           '(' + sb('a', 'S', ',' + NB, 14) + sb('b', 'S', ')', 14),
           size=14, color=ORANGE, anchor='end')
    f.line(P(-0.06, 0), P(top, 0), width=1)
    f.line(P(0, -0.06), P(0, top), width=1)
    arrowhead(f, P(top + 0.02, 0), P(0, 0), size=8)
    arrowhead(f, P(0, top + 0.02), P(0, 0), size=8)
    f.text(shift(P(top, 0), (0, -0.16)), 'a', anchor='end', size=15)
    f.text(shift(P(0, top), (-0.1, -0.02)), 'b', anchor='end', size=15)
    f.text(shift(P(0, 0), (-0.08, -0.13)), '0', size=13, italic=False,
           anchor='end')
    f.save('01-introduction/disk-constraint', 'Left: a square S in the dashed '
           'circle of radius R = root 2 about o; from the centre of S, o is '
           'a_S along one axis and b_S along the other, and the vertex '
           'farthest from o is at distance root phi(a_S, b_S). Right: the '
           'pair (a_S, b_S) in the part of the disk phi at most 2 where a and '
           'b are nonnegative, with the dashed tangent a + b = 1 at '
           '(1/2, 1/2)')


def two_squares():
    """Two squares at the radius root 5 over 2: both centres lie in the
    closed disk of radius 1/2 about o and are at least 1 apart, so they are
    the ends of a diameter, 1 apart, and the squares share a full edge."""
    R2, r, s = math.sqrt(5) / 2, 0.5, 150
    cs, ct = (0.5, 0.0), (-0.5, 0.0)
    for c in (cs, ct):
        assert phi_ab(abs(c[0]), abs(c[1])) <= R2 ** 2 + 1e-12
        assert abs(norm(c) - r) < 1e-12
    assert abs(norm((cs[0] - ct[0], cs[1] - ct[1])) - 2 * r) < 1e-12
    S, T = square_corners(cs), square_corners(ct)
    assert not interiors_meet(S, T)
    edge = [(0.0, -0.5), (0.0, 0.5)]
    assert all(q in S and q in T for q in edge)
    f = Figure(-R2 - 0.06, R2 + 0.06, -R2 - 0.06, R2 + 0.06, s)
    f.circle((0, 0), R2, stroke=INK, width=1.2, dash='6 4')
    f.text(shift((0, 0), u(rad(118)), R2 + 0.1), sbn('R', '2', size=15),
           size=15)
    f.square(cs, fill=FILLS[0], stroke=BLUE)
    f.square(ct, fill=FILLS[2], stroke=GREEN)
    f.circle((0, 0), r, stroke=INK, width=1.1, dash='5 4')
    f.line(*edge, width=3.4)
    f.line(ct, cs, width=1.3)
    f.text((0.25, 0.08), '1', size=14, italic=False)
    for c, col, name, side in ((cs, BLUE, 'S', 1), (ct, GREEN, 'T', -1)):
        f.dot(c, r=4.2)
        f.text(shift(c, (0.12 * side, -0.13)), sbn('c', name, size=14),
               size=14, color=col)
        f.text(shift(c, (0.25 * side, 0.27)), name, size=17, color=col)
    f.text(shift((0, 0), u(rad(116)), r + 0.25), sb('Γ', '1/2', size=14),
           size=14)
    f.dot((0, 0))
    f.text((-0.05, -0.1), 'o', anchor='end')
    f.save('01-introduction/two', 'Two squares S and T forming a 2 by 1 '
           'rectangle in the dashed circle of radius root 5 over 2 about o; '
           'their centres lie on the dashed circle of radius 1/2 about o, at '
           'the ends of a diameter of length 1, and the edge the squares '
           'share, through o, is drawn thick')


def six_pins():
    """Six squares, steps 1 and 2: on the circle of radius 9/10 the five
    squares that avoid o hold arcs of more than a sixth of the circle, so
    the sixth square contains o; the five pins name the other squares."""
    centers, R, _ = MODELS[6]
    names = ['C', 'N', 'E', 'W', 'S', 'D']
    fills = [GREY] + FILLS[1:6]
    strokes = [FAINT] + COLORS[1:6]
    pins = {'E': 0.0, 'N': math.pi / 2, 'W': 11 * math.pi / 12,
            'D': 5 * math.pi / 4, 'S': 19 * math.pi / 12}
    r, s = 0.9, 128
    f = Figure(-R - 0.06, R + 0.06, -R - 0.06, R + 0.06, s)
    draw_model(f, centers, R, fills=fills, strokes=strokes, touch=False)
    f.circle((0, 0), r, stroke=INK, width=1.1, dash='1.5 3')
    total = 0.0
    for name, c, col in zip(names, centers, strokes):
        c, deg = placed(c)
        member = lambda p: in_open_square(p, c, deg)
        if name == 'C':
            assert member((0, 0)) and not arcs_in(member, r)
            continue
        assert not member((0, 0))
        run = longest(arcs_in(member, r))
        assert run[1] - run[0] > math.pi / 3
        total += run[1] - run[0]
        f.arc((0, 0), r, run[0], run[1], col, width=5)
        assert member(shift((0, 0), u(pins[name]), r))
    assert total > 5 * math.pi / 3 and 2 * math.pi - total < math.pi / 3
    for name, c, col in zip(names, centers, strokes):
        c, deg = placed(c)
        if name != 'C':
            f.dot(shift((0, 0), u(pins[name]), r), r=4)
        # The names sit beyond the pins, away from o.
        pos = {'C': (0.33, 0.33), 'D': (-0.27, -0.27)}.get(name, (0, 0))
        f.text(shift(c, pos), name, size=17, color=col)
    f.text((0.06, -0.11), 'o', anchor='start')
    # In the white corner between N and E, where the circle is dotted.
    f.text(shift((0, 0), u(rad(45)), 1.08), sb('Γ', '9/10', size=14),
           size=14)
    f.save('01-introduction/pins', 'The optimal packing of six squares with '
           'the dotted circle of radius 9/10 about o: each of the five '
           'squares that avoid o holds a thick arc of more than a sixth of '
           'it, the grey square C contains o, and five dots, the pins, lie '
           'one in each of the squares E, N, W, D and S')


def reflection():
    """The remark after Definition 2.6 for the T: the mirror image of a
    packing congruent to the T is again congruent to the T, with the two
    lower squares exchanged."""
    centers, R, _ = MODELS[3]
    phi, lam = rad(35), rad(100)
    psi = 2 * lam - phi + math.pi
    names = ['2', '3', '1']
    tau = [1, 0, 2]
    mirror = lambda p: rotate((p[0], -p[1]), 2 * lam)
    step = 2 * R + 0.75
    o2 = (step, 0.0)
    f = Figure(-R - 0.08, step + R + 0.08, -R - 0.2, R + 0.1, 112)
    for k, c in enumerate(centers):
        # The mirror image of the square in the slot c_k is the square of
        # the model at c_tau(k), turned by psi about o.
        image = sorted(mirror(rotate(x, phi)) for x in square_corners(c))
        model = sorted(rotate(x, psi) for x in square_corners(centers[tau[k]]))
        assert all(norm((p[0] - q[0], p[1] - q[1])) < 1e-9
                   for p, q in zip(image, model))
    for at, turn, slot_names in ((0, phi, names),
                                 (1, psi, [names[t] for t in tau])):
        o = (at * step, 0.0)
        f.circle(o, R, stroke=INK, width=1.2, dash='6 4')
        for t in (turn, turn + math.pi / 2):
            f.line(shift(o, u(t), -1.25), shift(o, u(t), 1.25), stroke=FAINT,
                   width=1)
        for j, c in enumerate(centers):
            name = slot_names[j]
            col = names.index(name)
            f.polygon([shift(o, rotate(x, turn)) for x in square_corners(c)],
                      fill=FILLS[col], stroke=COLORS[col])
        for j, c in enumerate(centers):
            name = slot_names[j]
            col = names.index(name)
            f.text(shift(o, rotate(shift(c, (0, 0.17)), turn)),
                   sbn('S', name, size=16), size=16, color=COLORS[col])
            f.dot(shift(o, rotate(c, turn)))
            f.text(shift(o, rotate(shift(c, (0, -0.15)), turn)),
                   sbn('c', str(j + 1), size=14), size=14)
        f.line(shift(o, u(lam), -R - 0.05), shift(o, u(lam), R + 0.05),
               stroke=PURPLE, width=1.6, dash='7 4')
        f.text(shift(o, u(lam + math.pi), R + 0.1), 'L', size=16,
               color=PURPLE, anchor='start', dx=6)
        f.dot(o)
        f.text(shift(o, (0.06, -0.1)), 'o', anchor='start', size=14)
    arrow(f, (R + 0.12, R - 0.05), (step - R - 0.12, R - 0.05), width=1.6)
    word(f, (step / 2, R + 0.08), 'mirror in ' + it('L'), size=14)
    f.save('02-preliminaries/reflection', 'Left: the packing congruent to the '
           'T of the previous figure and a dashed line L through o. Right: '
           'its mirror image in L, which is again the T, turned about o by '
           'another angle, with the squares S3, S2, S1 at the points c1, c2, '
           'c3')


# -------------------------------------------------------------- chapter 3

def tangent_line(u0, v0):
    """The tangent half-plane of Definition 3.5 at (u0, v0), as (p, q, c):
    the points with p a + q b <= c."""
    p, q = u0 + 0.5, v0 + 0.5
    return p, q, p * u0 + q * v0


def contact_polygons():
    """The contact polygons of three, four and five squares, where a, b >= 0,
    each around its disk phi <= R_n^2, with the points of tangency."""
    g = (math.sqrt(5) - 1) / 2
    cases = [('three squares', 425 / 256,
              [(0.5, 5 / 16), (5 / 16, 0.5), (11 / 16, 0), (0, 11 / 16)],
              sbn('P', '3', size=16), 'φ ≤ 425/256', (0.47, 0.5)),
             ('four squares', 2.0, [(0.5, 0.5)], 'a + b ≤ 1', 'φ ≤ 2',
              (0.72, 0.72)),
             ('five squares', 2.5, [(1, 0), (0, 1), (g, g)],
              sbn('P', '5', size=16), 'φ ≤ 5/2', (0.72, 0.72))]
    top, step = 1.2, 1.55
    f = Figure(-0.12, 2 * step + top, -0.3, top + 0.2, 175)
    for k, (title, K, points, name, disk, where) in enumerate(cases):
        at = (k * step, 0)
        poly = [(0, 0), (2, 0), (2, 2), (0, 2)]
        for u0, v0 in points:
            assert abs(phi_ab(u0, v0) - K) < 1e-12
            p, q, c = tangent_line(u0, v0)
            poly = clip(poly, p, q, c)
        # The quadrant disk lies in the polygon, touching it at the points.
        for x, y in quadrant_disk(K, 200):
            for u0, v0 in points:
                p, q, c = tangent_line(u0, v0)
                assert p * x + q * y <= c + 1e-9
        f.polygon([shift(at, x) for x in poly], fill=FILLS[1], stroke=ORANGE,
                  width=2)
        f.polygon([shift(at, x) for x in quadrant_disk(K)], fill=FILLS[0],
                  stroke=BLUE, width=1.4)
        for u0, v0 in points:
            p, q, c = tangent_line(u0, v0)
            d = (-q / math.hypot(p, q), p / math.hypot(p, q))
            seg = [shift((u0, v0), d, -0.35 + 0.7 * j / 400)
                   for j in range(401)]
            seg = [x for x in seg if -0.06 <= x[0] <= top - 0.1
                   and -0.06 <= x[1] <= top - 0.1]
            f.line(shift(at, seg[0]), shift(at, seg[-1]), width=1, dash='4 3')
            f.dot(shift(at, (u0, v0)), r=3.4)
        f.line(shift(at, (-0.05, 0)), shift(at, (top, 0)), width=1)
        f.line(shift(at, (0, -0.05)), shift(at, (0, top)), width=1)
        arrowhead(f, shift(at, (top, 0)), shift(at, (0, 0)), size=8)
        arrowhead(f, shift(at, (0, top)), shift(at, (0, 0)), size=8)
        f.text(shift(at, (top, -0.1)), 'a', anchor='end', size=14)
        f.text(shift(at, (-0.07, top - 0.02)), 'b', anchor='end', size=14)
        f.text(shift(at, (0.26, 0.24)), disk, size=13, color=BLUE)
        f.text(shift(at, where), name, size=15, color=ORANGE,
               anchor='start')
        word(f, shift(at, (0.55, -0.2)), title, size=14)
    f.save('03-tools/contact-polygons', 'The contact polygons of three, four and '
           'five squares where a, b are at least 0: each is cut out by '
           'tangent lines of the disk phi at most R_n squared at the dotted '
           'points, and contains that disk')


def support_proof():
    """Lemma 3.12: points a fraction t of the way from each centre to its
    extreme vertex, and the two supporting lines."""
    s, t = ((-0.8, 0.0), 22), ((0.95, 0.12), -31)
    n = (1.0, 0.0)
    ws = (abs(math.cos(rad(22))) + abs(math.sin(rad(22)))) / 2
    wt = (abs(math.cos(rad(31))) + abs(math.sin(rad(31)))) / 2
    S, T = square_corners(*s), square_corners(*t)
    vs = max(S, key=lambda q: dot2(q, n))
    vt = min(T, key=lambda q: dot2(q, n))
    assert abs(dot2(vs, n) - (dot2(s[0], n) + ws)) < 1e-12
    assert abs(dot2(vt, n) - (dot2(t[0], n) - wt)) < 1e-12
    assert dot2(vs, n) < dot2(vt, n)
    tt = 0.72
    f = Figure(-1.6, 1.85, -1.08, 0.95, 170)
    f.polygon(S, fill=FILLS[0], stroke=BLUE)
    f.polygon(T, fill=FILLS[2], stroke=GREEN)
    for v, col in ((vs, BLUE), (vt, GREEN)):
        f.line((v[0], -0.8), (v[0], 0.85), stroke=col, width=1.2, dash='5 4')
    kappa = (vs[0] + vt[0]) / 2
    f.line((kappa, -0.8), (kappa, 0.85), width=1.4)
    for (c, _), v, col in ((s, vs, BLUE), (t, vt, GREEN)):
        f.line(c, v, stroke=col, width=1.6)
        f.dot(c, fill=col)
        q = shift(c, (v[0] - c[0], v[1] - c[1]), tt)
        open_dot(f, q, stroke=col)
        f.dot(v, r=3.4, fill=col)
    arrow(f, (-1.5, 0.78), (-1.1, 0.78), width=1.6)
    f.text((-1.07, 0.78), 'n', anchor='start')
    y0 = -0.93
    f.line((-1.55, y0), (1.8, y0), width=1)
    arrowhead(f, (1.85, y0), (0, y0), size=8)
    for x, s_, col in ((s[0][0], sbn('c', 'S', size=13), BLUE),
                       (t[0][0], sbn('c', 'T', size=13), GREEN)):
        f.line((x, y0 - 0.04), (x, y0 + 0.04), stroke=col, width=1.4)
        f.text((x, y0 - 0.13), s_, size=13, color=col)
        f.line((x, y0 + 0.04), (x, 0.0), stroke=col, width=0.8, dash='2 3')
    for lo, hi, s_, col in ((s[0][0], vs[0], sbn('w', 'S', '(n)', 13), BLUE),
                            (vt[0], t[0][0], sbn('w', 'T', '(n)', 13),
                             GREEN)):
        h = y0 + 0.13
        f.line((lo, h), (hi, h), stroke=col, width=1.6)
        for x in (lo, hi):
            f.line((x, h - 0.04), (x, h + 0.04), stroke=col, width=1.6)
        f.text(((lo + hi) / 2, h + 0.12), s_, size=13, color=col)
    f.text((kappa, 0.92), 'κ', size=15)
    for c, deg, at, name, col in ((s[0], s[1], (-1.0, -0.33), 'S', BLUE),
                                  (t[0], t[1], (1.2, -0.2), 'T', GREEN)):
        assert in_open_square(at, c, deg)
        f.text(at, name, size=17, color=col)
    f.save('03-tools/support-proof', 'Two disjoint squares, a separating line, '
           'and the segments from each centre to its extreme vertex in the '
           'direction n; test points a fraction t of the way lie in the open '
           'squares, and the two supporting lines are at the full widths')


def lengths():
    """Lemma 3.8 (2): the coordinates p, q of a vector n in the frame of a
    square U have |p| + |q| > |n|, with equality only along a side."""
    deg = 20.0
    e1, e2 = u(rad(deg)), u(rad(deg + 90))
    f = Figure(-0.9, 3.75, -1.0, 1.25, 120)
    for k, (c, t) in enumerate((((0.0, 0.0), rad(deg + 50)),
                                ((2.6, 0.0), rad(deg)))):
        n = u(t)
        p, q = dot2(n, e1), dot2(n, e2)
        assert abs(p * p + q * q - 1) < 1e-12
        f.square(c, deg, fill=FILLS[0], stroke=BLUE)
        for e in (e1, e2):
            f.line(shift(c, e, -0.72), shift(c, e, 0.72), stroke=FAINT,
                   width=1, dash='4 3')
        corner = shift(c, e1, p)
        tip = shift(c, n)
        if k == 0:
            assert abs(p) + abs(q) > 1 + 0.3
            f.line(c, corner, stroke=ORANGE, width=2.6)
            f.line(corner, tip, stroke=GREEN, width=2.6)
            m = 0.07
            polyline(f, [shift(corner, e1, -m), shift(shift(corner, e1, -m),
                                                     e2, m),
                         shift(corner, e2, m)], width=1)
            f.text(shift(shift(c, e1, p / 2), e2, -0.1), 'p', color=ORANGE)
            f.text(shift(shift(corner, e2, q / 2), e1, 0.1), 'q',
                   color=GREEN)
            word(f, (0.0, -0.92), '|' + it('p') + '| + |' + it('q') +
                 '| > |' + it('n') + '|', size=13)
        else:
            assert abs(q) < 1e-12 and abs(abs(p) - 1) < 1e-12
            f.line(c, corner, stroke=ORANGE, width=4.2)
            f.text(shift(shift(c, e1, 0.3), e2, -0.13), 'p', color=ORANGE)
            word(f, (2.6, -0.92), it('q') + ' = 0, |' + it('p') + '| = |' +
                 it('n') + '|', size=13)
        arrow(f, c, tip, color=INK, width=1.6)
        f.text(shift(tip, n, 0.1), 'n')
        f.dot(c, fill=BLUE)
        f.text(shift(shift(c, e1, -0.33), e2, -0.33), 'U', size=16,
               color=BLUE)
    f.save('03-tools/lengths', 'Left: a vector n from the centre of a square U is '
           'the hypotenuse of a right triangle whose legs p and q lie along '
           'the axes of U, and the legs together are longer than n. Right: n '
           'along an axis of U, where the second leg vanishes and the first '
           'is n itself')


def width_graph():
    """The width of a unit square in a unit direction, from 1/2 along a side
    to root 2 over 2 along a diagonal."""
    f = Figure(-0.95, 4.35, -1.02, 1.05, 118)
    f.square((0, 0), fill=FILLS[0], stroke=BLUE)
    f.dot((0, 0), fill=BLUE)
    for t, col in ((0.0, ORANGE), (math.pi / 4, GREEN)):
        w = (abs(math.cos(t)) + abs(math.sin(t))) / 2
        foot = shift((0, 0), u(t), w)
        f.line((0, 0), foot, stroke=col, width=2.6)
        perp = u(t + math.pi / 2)
        f.line(shift(foot, perp, -0.45), shift(foot, perp, 0.45), stroke=col,
               width=1.2, dash='4 3')
        arrow(f, shift(foot, u(t), 0.08), shift(foot, u(t), 0.36), color=col,
              width=1.4, size=8)
    f.text((0.28, -0.1), '½', size=14, italic=False, color=ORANGE)
    f.text(shift((0, 0), u(math.pi / 4), 0.45), '√2/2', size=13,
           italic=False, color=GREEN, anchor='end', dx=-4)
    f.text((-0.3, -0.3), 'U', size=16, color=BLUE)
    # The graph of w over [0, pi].
    P = Plot(f, 1.4, -0.6, 2.8, 1.5, (0, math.pi), (0.4, 0.75))
    for y in (0.5, math.sqrt(2) / 2):
        f.line(P.P(0, y), P.P(math.pi, y), stroke=GREY, width=1)
    P.curve(lambda a: (abs(math.cos(a)) + abs(math.sin(a))) / 2, 0, math.pi,
            stroke=BLUE, width=2.2)
    f.line(P.P(0, 0.4), P.P(math.pi + 0.1, 0.4), width=1)
    arrowhead(f, P.P(math.pi + 0.18, 0.4), P.P(0, 0.4), size=8)
    f.line(P.P(0, 0.4), P.P(0, 0.76), width=1)
    arrowhead(f, P.P(0, 0.77), P.P(0, 0.4), size=8)
    for a, s_ in ((0, '0'), (math.pi / 4, 'π/4'), (math.pi / 2, 'π/2'),
                  (3 * math.pi / 4, '3π/4'), (math.pi, 'π')):
        q = P.P(a, 0.4)
        f.line(shift(q, (0, -0.03)), shift(q, (0, 0.03)), width=1)
        word(f, shift(q, (0, -0.13)), s_, size=12)
    for y, s_ in ((0.5, '½'), (math.sqrt(2) / 2, '√2/2')):
        word(f, shift(P.P(0, y), (-0.06, 0)), s_, size=12, anchor='end')
    for a in (0, math.pi / 2, math.pi):
        f.dot(P.P(a, 0.5), r=3.4, fill=ORANGE)
    for a in (math.pi / 4, 3 * math.pi / 4):
        f.dot(P.P(a, math.sqrt(2) / 2), r=3.4, fill=GREEN)
    word(f, shift(P.P(math.pi / 2, 0.4), (0, -0.3)), 'the angle between ' +
         it('n') + ' and a side of ' + it('U'), size=12)
    f.text(shift(P.P(0, 0.75), (0.08, 0.06)), sbn('w', 'U', '(n)', 14),
           size=14, anchor='start')
    f.save('03-tools/width-graph', 'The width of a square in a unit direction n: '
           'one half when n is parallel to a side, root 2 over 2 along a '
           'diagonal, and in between otherwise, as a function of the angle '
           'between n and a side')


def centre_slab():
    """Lemma 3.26: a centre c_S within distance 1 of o, for a unit vector n;
    the slab about c_S of half-width w_S(n) + w_T(n) >= 1 contains the unit
    disk about c_S, and so o."""
    deg_s, deg_t = 25.0, 10.0
    cs, o = (0.0, 0.0), (0.62, -0.58)
    n, perp = (1.0, 0.0), (0.0, 1.0)

    def width(deg):
        return (abs(math.cos(rad(deg))) + abs(math.sin(rad(deg)))) / 2

    W = width(deg_s) + width(deg_t)
    co = (cs[0] - o[0], cs[1] - o[1])
    assert norm(co) <= 1 <= W and abs(dot2(n, co)) <= norm(co)
    f = Figure(-1.45, 1.45, -1.3, 1.35, 150)
    L = 1.22
    f.polygon([(-W, -L), (W, -L), (W, L), (-W, L)], fill=GREY, stroke='none',
              opacity=0.6)
    for x in (-W, W):
        f.line((x, -L), (x, L), width=1.2, dash='5 4')
    f.circle(cs, 1.0, stroke=INK, width=1, dash='3 3')
    f.square(cs, deg_s, fill=FILLS[0], stroke=BLUE)
    f.dot(cs, fill=BLUE)
    f.text(shift(cs, (-0.05, 0.12)), sb('c', 'S'), anchor='end', color=BLUE)
    f.text(shift(cs, (-0.3, -0.3)), 'S', size=16, color=BLUE)
    f.dot(o)
    f.text(shift(o, (-0.06, 0.06)), 'o', anchor='end')
    arrow(f, (0.0, 1.08), (W, 1.08), color=ORANGE, width=1.4)
    f.text((W / 2, 1.2), sbn('w', 'S', '(n) + ') + sbn('w', 'T', '(n) ≥ 1'),
           size=13, color=ORANGE)
    arrow(f, (-0.25, -1.08), (0.25, -1.08), color=INK, width=1.6)
    f.text((0.0, -1.2), 'n')
    f.save('03-tools/centre-slab', 'A square S whose centre is within distance 1 '
           'of the disk centre o, for a unit vector n: the slab about the '
           'centre of S of half-width w_S(n) + w_T(n), which is at least 1, '
           'contains the unit disk about the centre of S, and so o')


def shrink():
    """Lemma 3.16: the open arcs of the T on the circle of radius 3/8, and
    the closed arcs of the shrunken half-widths."""
    centers = MODELS[3][0]
    r, t = 3 / 8, 0.8
    W = 0.78
    f = Figure(-W, W, -W, W, 300)
    for k, c in enumerate(centers):
        poly = square_corners(c)
        for p, q, cc in ((1, 0, W), (-1, 0, W), (0, 1, W), (0, -1, W)):
            poly = clip(poly, p, q, cc)
        f.polygon(poly, fill=FILLS[k], stroke=COLORS[k], width=1.2,
                  opacity=0.55)
    f.circle((0, 0), r)
    arcs = []
    for k, c in enumerate(centers):
        runs = arcs_in(lambda p: in_open_square(p, c), r)
        assert len(runs) == 1
        t0, t1 = runs[0]
        assert abs((t1 - t0) - 2 * math.pi / 3) < 2e-3
        arcs.append(((t0 + t1) / 2, (t1 - t0) / 2, COLORS[k]))
    for mid, w, col in arcs:
        f.arc((0, 0), r, mid - w, mid + w, col, width=1.6)
        f.arc((0, 0), r, mid - t * w, mid + t * w, col, width=6)
        for e in (-1, 1):
            f.dot(shift((0, 0), u(mid + e * t * w), r), r=4, fill=col)
    for mid, w, col in arcs:
        open_dot(f, shift((0, 0), u(mid + w), r), r=4.2, stroke=INK)
    mid, w, col = arcs[2]
    f.line((0, 0), shift((0, 0), u(mid), r + 0.12), width=1, dash='3 3')
    for e, s_, rad_ in ((1, 'w', 0.2), (-1, 't·w', 0.27)):
        end = mid + e * (w if e > 0 else t * w)
        f.line((0, 0), shift((0, 0), u(end), r), width=1)
        thin_arc(f, (0, 0), rad_ - 0.07, mid, end)
        f.text(shift((0, 0), u((mid + end) / 2), rad_ + 0.02), s_, size=13)
    f.dot((0, 0), r=2.6)
    f.text((0.03, -0.07), 'o', anchor='start', size=14)
    f.save('03-tools/shrink', 'The three open arcs of the T on the circle of '
           'radius 3/8 meet at their endpoints, which lie in none of them; the '
           'closed arcs of half-width t times w, thick, are disjoint')


def arc_overlap():
    """Lemma 3.17: arcs whose centres are closer than the sum of their
    half-widths share the direction x."""
    tu, wu, tv, wv = rad(15), rad(52), rad(105), rad(46)
    delta = tv - tu
    assert delta < wu + wv
    x = tu + wu / (wu + wv) * delta
    assert abs(x - tu) < wu and abs(tv - x) < wv
    f = Figure(-1.3, 1.4, -1.0, 1.42, 170)
    f.circle((0, 0), 1)
    f.arc((0, 0), 0.965, tu - wu, tu + wu, BLUE, width=5)
    f.arc((0, 0), 1.035, tv - wv, tv + wv, GREEN, width=5)
    for c, name, col in ((tu, 'U', BLUE), (tv, 'V', GREEN)):
        f.line((0, 0), shift((0, 0), u(c), 1), stroke=col, width=1.2,
               dash='4 3')
        f.text(shift((0, 0), u(c), 1.2), name, size=17, color=col)
    f.line((0, 0), shift((0, 0), u(x), 1.0), width=1.4)
    f.dot(shift((0, 0), u(x), 1.0), r=4.5, fill=ORANGE)
    f.text(shift((0, 0), u(x), 1.16), 'x', color=ORANGE, size=16)
    thin_arc(f, (0, 0), 0.32, tu, tv)
    f.text(shift((0, 0), u(rad(38)), 0.55), 'δ', size=15)
    f.dot((0, 0))
    f.text((0.04, -0.09), 'o', anchor='start')
    f.save('03-tools/arc-overlap', 'Two arcs U and V whose centres are less than '
           'the sum of their half-widths apart: the direction x that divides '
           'the angle between the centres in the ratio of the half-widths '
           'lies in both')


def perimeter():
    """Lemma 3.18: three directions cut the circle into three gaps adding up
    to 2 pi, and each angle is at most its gap."""
    xs = (rad(10), rad(70), rad(150))
    gaps = [(xs[0], xs[1]), (xs[1], xs[2]), (xs[2], xs[0] + 2 * math.pi)]
    assert abs(sum(b - a for a, b in gaps) - 2 * math.pi) < 1e-12
    f = Figure(-1.55, 1.6, -1.3, 1.35, 150)
    cols = (BLUE, GREEN, PURPLE)
    for (a, b), col in zip(gaps, cols):
        f.arc((0, 0), 1, a + 0.03, b - 0.03, col, width=5)
    names = ('U', 'V', 'W')
    for x, name in zip(xs, names):
        f.line((0, 0), shift((0, 0), u(x), 1), width=1)
        f.dot(shift((0, 0), u(x), 1), r=3.6)
        f.text(shift((0, 0), u(x), 1.17), sbn('x', name), size=15)
    labels = (sbn('x', 'V', ' − ', 13) + sbn('x', 'U', '', 13),
              sbn('x', 'W', ' − ', 13) + sbn('x', 'V', '', 13),
              sbn('x', 'U', ' + 2π − ', 13) + sbn('x', 'W', '', 13))
    for (a, b), col, s_, d in zip(gaps, cols, labels, (1.3, 1.34, 1.2)):
        f.text(shift((0, 0), u((a + b) / 2), d), s_, size=13, color=col)
    # The angle between U and W, the short way round.
    d_uw = min(abs(xs[2] - xs[0]), 2 * math.pi - abs(xs[2] - xs[0]))
    assert d_uw < gaps[2][1] - gaps[2][0]
    thin_arc(f, (0, 0), 0.42, xs[0], xs[2], color=ORANGE, width=1.6)
    # The label between the radii to x_V and x_W, clear of both.
    f.text(shift((0, 0), u((xs[1] + xs[2]) / 2), 0.62),
           '∠(' + sbn('θ', 'U', ', ', 13) + sbn('θ', 'W', ')', 13), size=13,
           color=ORANGE)
    f.dot((0, 0))
    f.text((0.05, -0.1), 'o', anchor='start')
    f.save('03-tools/perimeter', 'Three directions cut the circle into three gaps '
           'that add up to 2 pi; the angle between two of the directions is at '
           'most the gap between them, here the angle between U and W is '
           'shorter than its gap')


def gaps_figure():
    """Lemma 3.19 for six directions pairwise at least pi/3 apart: the six
    gaps, on the circle and unrolled on the line."""
    m = 6
    g = 2 * math.pi / m
    p0 = rad(-160)
    ps = [p0 + k * g for k in range(m)]
    f = Figure(-1.35, 6.7, -1.25, 1.3, 84)
    f.circle((0, 0), 1)
    for k, p in enumerate(ps):
        f.line((0, 0), shift((0, 0), u(p), 1), width=1)
        f.dot(shift((0, 0), u(p), 1), r=3.6)
        f.text(shift((0, 0), u(p), 1.18), sbn('p', str(k)), size=14)
        f.text(shift((0, 0), u(p + g / 2), 0.78), 'g', size=13,
               color=ORANGE)
    for k, p in enumerate(ps):
        col = ORANGE if k < m - 1 else PURPLE
        f.arc((0, 0), 1, p + 0.05, p + g - 0.05, col, width=3)
    f.dot((0, 0))
    # The label o between the radii to p1 and p2.
    f.text(shift((0, 0), u(ps[1] + g / 2), 0.22), 'o', size=14)
    # Unrolled: from p0 to p0 + 2 pi.
    X = lambda t: 1.9 + (t - p0) / (2 * math.pi) * 4.6
    y0 = 0.0
    f.line((X(p0) - 0.1, y0), (X(p0 + 2 * math.pi) + 0.2, y0), width=1)
    for k, p in enumerate(ps + [p0 + 2 * math.pi]):
        f.line((X(p), y0 - 0.08), (X(p), y0 + 0.08), width=1.6)
        s_ = sbn('p', str(k), size=13) if k < m else sbn('p', '0', ' + 2π',
                                                           13)
        f.text((X(p), y0 - 0.25), s_, size=13)
    for k, p in enumerate(ps):
        col = ORANGE if k < m - 1 else PURPLE
        a, b = X(p) + 0.04, X(p + g) - 0.04
        f.line((a, y0 + 0.2), (b, y0 + 0.2), stroke=col, width=3)
        f.text(((a + b) / 2, y0 + 0.4), '≥ ' + it('g'), size=13,
               color=col, italic=False)
    f.save('03-tools/gaps', 'Six directions pairwise at least g = pi/3 apart, '
           'on the circle and unrolled onto the line from p0 to p0 + 2 pi: '
           'six gaps of at least g add up to 2 pi, so each is exactly g')


def chart_moves():
    """Lemma 3.21: one square, four charts, and the coordinates of its centre
    in each."""
    alpha, X, Y = rad(20), 0.9, 0.4
    e1, e2 = u(alpha), u(alpha + math.pi / 2)
    c = shift(shift((0, 0), e1, X), e2, Y)
    deg = math.degrees(alpha)
    moves = [('a chart', alpha, 1, (X, Y), ('X', 'Y')),
             ('reversal', alpha, -1, (X, -Y), ('X', '−Y')),
             ('half turn', alpha + math.pi, 1, (-X, -Y), ('−X', '−Y')),
             ('exchange', alpha + math.pi / 2, -1, (Y, X), ('Y', 'X'))]
    heads = ['(θ, ε)', '(θ, −ε)', '(θ + π, ε)', '(θ + επ/2, −ε)']
    w, h = 3.2, 3.05

    def clearance(p, x, y):
        """Distance in chart coordinates from p to the boundary of the
        square centred at (x, y)."""
        dx = max(x - 0.5 - p[0], p[0] - x - 0.5)
        dy = max(y - 0.5 - p[1], p[1] - y - 0.5)
        return (-max(dx, dy) if dx < 0 and dy < 0
                else math.hypot(max(dx, 0), max(dy, 0)))

    def leg_label(points, x, y):
        return next(p for p in points if clearance(p, x, y) >= 0.17)

    f = Figure(0, 2 * w, -2 * h, 0, 96)
    for k, ((title, theta, eps, (x, y), names), head) in enumerate(
            zip(moves, heads)):
        at = (1.45 + (k % 2) * w, -1.75 - (k // 2) * h)
        check_chart(c, deg, theta, eps, x, y)
        cc = shift(at, c)
        f.square(cc, deg, fill=FILLS[0], stroke=BLUE)
        a1, a2 = chart_axes(f, at, theta, eps)
        chart = lambda p: shift(shift(at, a1, p[0]), a2, p[1])
        # Each axis label goes beyond the square if the axis runs into it.
        f.text(shift(at, a1, 1.6 if abs(y) < 0.5 and x > 0 else 1.37),
               it('t') + ' = 0', size=12, italic=False)
        f.text(shift(at, a2, 1.6 if abs(x) < 0.5 and y > 0 else 1.2),
               it('t') + ' = π/2', size=12, italic=False)
        q = shift(at, a1, x)
        f.line(at, q, stroke=ORANGE, width=2.6)
        f.line(q, cc, stroke=ORANGE, width=2.6)
        # Leg labels on the side away from the square, clear of its edges.
        s1, s2 = (-0.3 if y > 0 else 0.3), (0.17 if x > 0 else -0.17)
        p1 = leg_label([(x * t, s1) for t in (0.5, 0.65, 0.35)], x, y)
        p2 = leg_label([(x + s2, y * t) for t in (0.5, 0.3, 0.2)], x, y)
        f.text(chart(p1), names[0], size=14, color=ORANGE)
        f.text(chart(p2), names[1], size=14, color=ORANGE)
        f.dot(at)
        f.text(shift(at, (-0.1, -0.12)), 'o', size=14)
        f.dot(cc, fill=BLUE)
        word(f, (at[0] + 0.4, at[1] + 1.55), title + ' ' + it(head), size=14)
    f.save('03-tools/chart-moves', 'One square and four charts: a chart with '
           'phase theta and orientation epsilon, its reversal, its half turn '
           'and its exchange; in each the centre of the square has the chart '
           'coordinates (X, Y), (X, -Y), (-X, -Y) and (Y, X)')


def cartesian():
    """Lemma 3.22: with a chart (theta, eps), the square sits at
    (a, eps b) in the frame theta."""
    theta, a, b = rad(25), 0.85, 0.3
    step = 3.0
    f = Figure(-0.95, step + 1.75, -1.05, 1.75, 120)
    for k, eps in enumerate((1, -1)):
        at = (k * step, 0)
        c = shift(shift((0, 0), u(theta), a), u(theta + math.pi / 2), eps * b)
        deg = math.degrees(theta)
        check_chart(c, deg, theta, eps, a, b)
        cc = shift(at, c)
        f.square(cc, deg, fill=FILLS[0], stroke=BLUE)
        # The frame theta (always counterclockwise), and the chart.
        arrow(f, at, shift(at, u(theta), 1.55), width=1.3, size=8)
        arrow(f, at, shift(at, u(theta + math.pi / 2), 1.2), width=1.3,
              size=8)
        f.text(shift(at, u(theta + math.pi / 2), 1.33),
               'u(' + sbn('θ', 'S', ' + π/2)', 14), size=14)
        f.text(shift(at, u(theta), 1.75), 'u(' + sbn('θ', 'S', ')', 14),
               size=14)
        if eps < 0:
            arrow(f, at, shift(at, u(theta - math.pi / 2), 0.95),
                  color=ORANGE, width=1.3, size=8, dash='4 3')
            f.text(shift(at, u(theta - math.pi / 2), 1.1),
                   it('t') + ' = π/2', size=12, italic=False, color=ORANGE)
        arc_arrow(f, at, 0.3, theta + eps * 0.2,
                  theta + eps * (math.pi / 2 - 0.2), color=ORANGE, width=1.2,
                  size=7)
        q = shift(at, u(theta), a)
        f.line(at, q, stroke=ORANGE, width=2.6)
        f.line(q, cc, stroke=ORANGE, width=2.6)
        # The label a_S on the side of the first leg away from the square,
        # below the corner of the square that pokes across it.
        side = u(theta - math.pi / 2) if eps > 0 else u(theta + math.pi / 2)
        f.text(shift(shift(at, u(theta), a / 2), side, 0.36), sbn('a', 'S'),
               size=14, color=ORANGE)
        f.text(shift(shift(q, u(theta + math.pi / 2), eps * b / 2),
                     u(theta), 0.1),
               sbn('b', 'S') if eps > 0 else '−' + sbn('b', 'S'), size=14,
               color=ORANGE, anchor='start')
        f.dot(at)
        f.text(shift(at, (-0.08, -0.13)), 'o', size=14)
        f.dot(cc, fill=BLUE)
        title = ('orientation ' + it(sbn('ε', 'S', size=14)) +
                 f'<tspan dy="{-0.3 * 14:.1f}">{NB}={NB}' +
                 ('+1' if eps > 0 else '−1') + '</tspan>')
        f.text((at[0] + 0.45, 1.62), title, size=14, italic=False)
    f.save('03-tools/cartesian', 'A square with a chart of phase theta and '
           'orientation +1 or -1, and the frame theta at o: the centre is at '
           '(a, b) or (a, -b) in the frame')


def caps():
    """Lemma 3.24 (2) and (3): the full cap, the clipped cap, and the half
    circle, in the chart."""
    cases = [(it(sbn('A', 'S', ' ≤ ', 13)) + it(sbn('V', 'S', ':', 13)) + NB +
              'the full cap', 0.45, 0.75, 0.1),
             (it(sbn('V', 'S', ' &lt; ', 13)) + it(sbn('A', 'S', ':', 13)) + NB +
              'the lower edge clips it', 0.45, 0.7, 0.35),
             (it(sbn('a', 'S', size=13)) + f'<tspan dy="{-0.3 * 13:.1f}">'
              f'{NB}={NB}½:{NB}a half circle</tspan>', 0.3, 0.5, 0.15)]
    step = 2.0
    f = Figure(-0.62, 2 * step + 1.35, -0.72, 1.1, 140)
    # The chart angles of the two ends of each cap.
    ends = [('', 'A', '−', 'A'), ('', 'A', '−', 'V'), ('π/2', '', '−π/2', '')]
    for k, (title, r, a, b) in enumerate(cases):
        at = (k * step, 0)
        A = math.acos((a - 0.5) / r)
        x = (0.5 - b) / r
        V = math.pi / 2 if x >= 1 else math.asin(x)
        lo, hi = -min(A, V), A
        runs = arcs_in(lambda p: in_open_square(p, (a, b)), r, steps=14400)
        t0, t1 = longest(runs)
        t0 = t0 - 2 * math.pi if t0 > math.pi else t0
        t1 = t1 - 2 * math.pi if t1 > 2 * math.pi - 1e-9 else t1
        assert abs(t0 - lo) < 2e-3 and abs(t1 - hi) < 2e-3, (k, t0, t1, lo,
                                                               hi)
        if k == 0:
            assert A <= V
        if k == 1:
            assert V < A
        if k == 2:
            assert abs(A - math.pi / 2) < 1e-12 and V == math.pi / 2
        f.line(shift(at, (-0.55, 0)), shift(at, (1.3, 0)), stroke=FAINT,
               width=1)
        f.square(shift(at, (a, b)), fill=FILLS[0], stroke=BLUE)
        f.line(shift(at, (a - 0.5, -0.66)), shift(at, (a - 0.5, 0.75)),
               width=1, dash='4 4')
        f.line(shift(at, (-0.55, b - 0.5)), shift(at, (1.3, b - 0.5)),
               width=1, dash='4 4')
        f.circle(at, r)
        f.arc(at, r, lo, hi, ORANGE, width=5)
        for t in (lo, hi):
            f.line(at, shift(at, u(t), r), width=1)
            f.dot(shift(at, u(t), r), r=3.2)
        # Each end of the cap labelled with its chart angle: left of the
        # near edge, or below the lower edge for the clipped cap.
        pre_hi, name_hi, pre_lo, name_lo = ends[k]
        mark = (lambda pre, name: pre + sbn(name, 'S', size=13) if name
                else pre)
        f.text(shift(shift(at, u(hi), r), (-0.08, 0.14)),
               mark(pre_hi, name_hi), size=13, anchor='end',
               italic=bool(name_hi))
        if name_lo == 'V':
            f.text(shift(shift(at, u(lo), r), (0.05, -0.12)),
                   mark(pre_lo, name_lo), size=13, anchor='start')
        else:
            f.text(shift(shift(at, u(lo), r), (-0.08, -0.14)),
                   mark(pre_lo, name_lo), size=13, anchor='end',
                   italic=bool(name_lo))
        f.dot(at)
        f.text(shift(at, (-0.05, 0.08)), 'o', anchor='end', size=14)
        f.dot(shift(at, (a, b)), fill=BLUE)
        f.text((at[0] + 0.35, 1.02), title, size=13, italic=False)
    f.save('03-tools/caps', 'Three exterior squares in their charts with a '
           'circle of radius at most 1/2 about o. Left: the full cap from -A '
           'to A. Middle: the lower edge clips the cap, from -V to A. Right: '
           'with the near edge through o, the square holds a half circle')


def estimates():
    """Lemma 3.29 (2), (3) and (5): 0 <= arcsin x - x <= x^3/4 on [0, 3/5],
    and the cosine at least cos(pi/5) = (1 + sqrt 5)/4 on [-pi/5, pi/5]."""
    f = Figure(-0.42, 6.45, -0.55, 3.05, 100)
    # (2) and (3) on [0, 3/5], as differences from x:
    # 0 <= arcsin x - x <= x^3/4, with the margin at x = 3/5.
    top = 0.085
    P = Plot(f, 0, 0, 2.86, 2.72, (0, 0.8), (0, top))
    g = lambda x: math.asin(x) - x
    for k in range(101):
        x = k / 100
        assert 0 <= g(x) + 1e-15
        if x <= 0.6:
            assert g(x) <= x ** 3 / 4 + 1e-15

    def reach(fn, y, lo=0.0, hi=1.0):
        """The x in [lo, hi] where the increasing fn reaches y."""
        for _ in range(60):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if fn(mid) < y else (lo, mid)
        return lo

    P.curve(lambda x: x ** 3 / 4, 0, 0.6, stroke=ORANGE, width=2)
    P.curve(lambda x: x ** 3 / 4, 0.6, reach(lambda x: x ** 3 / 4, top),
            stroke=ORANGE, width=1.4, dash='4 4')
    P.curve(g, 0, reach(g, top), n=400, stroke=BLUE, width=2.2)
    f.line(P.P(0.6, 0), P.P(0.6, 0.6 ** 3 / 4), stroke=INK, width=1,
           dash='2 3')
    f.dot(P.P(0.6, g(0.6)), r=3.2, fill=BLUE)
    f.dot(P.P(0.6, 0.6 ** 3 / 4), r=3.2, fill=ORANGE)
    P.axes('x', '', [(0.6, '3/5')], [(0.04, '0.04'), (0.08, '0.08')])
    f.text(P.P(0.64, 0.045), 'arcsin ' + it('x') + ' − ' + it('x'), size=13,
           color=BLUE, italic=False, anchor='start')
    f.text(P.P(0.43, 0.029), 'x³/4', size=13, color=ORANGE, anchor='end')
    # (5): the cosine meets (1 + sqrt 5)/4 at -pi/5 and pi/5.
    t5 = math.pi / 5
    c5 = (1 + math.sqrt(5)) / 4
    assert abs(math.cos(t5) - c5) < 1e-15 and math.sin(t5) < 3 / 5
    Q = Plot(f, 3.6, 0, 2.6, 2.6, (-0.8, 0.8), (0.7, 1.02))
    for k in range(201):
        t = -t5 + 2 * t5 * k / 200
        assert math.cos(t) >= c5 - 1e-15
    f.polygon([Q.P(-t5, 0.7), Q.P(t5, 0.7), Q.P(t5, 1.02), Q.P(-t5, 1.02)],
              fill=GREY, stroke='none', opacity=0.5)
    assert math.cos(0.75) > 0.7
    Q.curve(lambda t: c5, -0.75, 0.75, stroke=INK, width=1, dash='4 3')
    Q.curve(math.cos, -0.75, 0.75, stroke=BLUE, width=2.2)
    for t in (-t5, t5):
        f.dot(Q.P(t, c5), r=3.2)
    Q.axes('t', '', [(-t5, '−π/5'), (t5, 'π/5')],
           [(c5, '(1 + √5)/4'), (1, '1')], x_at=-0.8, y_at=0.7)
    word(f, Q.P(0.36, 0.975), 'cos ' + it('t'), size=13, color=BLUE)
    f.save('03-tools/estimates', 'Left: the arcsine between x and x + x cubed '
           'over 4 on the interval from 0 to 3/5. Right: the cosine meets '
           'the level (1 + root 5)/4 at -pi/5 and pi/5 and lies above it in '
           'between')


def sine_concave():
    """Lemma 3.29 (4): the chord of the sine between arcsin u and arcsin v
    lies below the curve, so the midpoint mu exceeds theta."""
    uu, vv, th = 0.3, 0.95, 0.52
    x1, x2 = math.asin(uu), math.asin(vv)
    mu, m = (x1 + x2) / 2, (uu + vv) / 2
    assert math.sin(th) < m <= math.sin(mu) and th < mu
    f = Figure(-0.45, 4.35, -0.55, 2.55, 120)
    P = Plot(f, 0, 0, 3.9, 2.3, (0, math.pi / 2 + 0.1), (0, 1.1))
    for x, y in ((x1, uu), (x2, vv)):
        f.line(P.P(x, 0), P.P(x, y), stroke=FAINT, width=1, dash='2 3')
        f.line(P.P(0, y), P.P(x, y), stroke=FAINT, width=1, dash='2 3')
    f.line(P.P(0, m), P.P(math.pi / 2 + 0.05, m), stroke=ORANGE, width=1.2,
           dash='5 4')
    f.line(P.P(mu, 0), P.P(mu, math.sin(mu)), stroke=INK, width=1,
           dash='2 3')
    f.line(P.P(th, 0), P.P(th, math.sin(th)), stroke=GREEN, width=1.4)
    P.curve(math.sin, 0, math.pi / 2 + 0.1, stroke=BLUE, width=2.2)
    f.line(P.P(x1, uu), P.P(x2, vv), stroke=ORANGE, width=1.8)
    for x, y in ((x1, uu), (x2, vv)):
        f.dot(P.P(x, y), r=3.8, fill=ORANGE)
    f.dot(P.P(mu, m), r=3.8, fill=ORANGE)
    f.dot(P.P(mu, math.sin(mu)), r=3.8, fill=BLUE)
    f.dot(P.P(th, math.sin(th)), r=3.8, fill=GREEN)
    P.axes('', '', [(x1, 'arcsin ' + it('u')), (th, ''), (mu, ''),
                    (x2, 'arcsin ' + it('v'))],
           [(uu, it('u')), (m, '(' + it('u') + ' + ' + it('v') + ')/2'),
            (vv, it('v'))])
    f.text(shift(P.P(th, 0), (0, -0.17)), 'θ', size=14, color=GREEN)
    f.text(shift(P.P(mu, 0), (0, -0.17)), 'μ', size=14)
    word(f, P.P(1.45, 1.06), 'sin', size=13, color=BLUE)
    f.save('03-tools/sine-concave', 'The sine on the interval from 0 to pi/2 and '
           'its chord between arcsin u and arcsin v: the midpoint of the chord '
           'lies below the curve at mu, so a theta with sine less than (u + '
           'v)/2 lies to the left of mu')


def quarter_turn():
    """Lemma 3.30 (2): a square sitting at c in the frame phi + pi/2 sits at
    rho(c) in the frame phi."""
    phi, c = rad(15), (0.95, 0.55)
    rc = (-c[1], c[0])
    F = lambda p, t: shift((0, 0), rotate(p, t))
    centre = F(c, phi + math.pi / 2)
    assert norm((centre[0] - F(rc, phi)[0], centre[1] - F(rc, phi)[1])) < 1e-12
    deg = math.degrees(phi)
    for j in range(-12, 13):
        for k in range(-12, 13):
            p = (0.12 * j, 0.12 * k)
            assert (in_open_square(F(p, phi), centre, deg)
                    == (abs(p[0] - rc[0]) < 0.5 and abs(p[1] - rc[1]) < 0.5))
    f = Figure(-1.55, 1.45, -0.5, 1.72, 150)
    f.square(centre, deg, fill=FILLS[0], stroke=BLUE)
    a1, a2 = u(phi), u(phi + math.pi / 2)
    b1, b2 = u(phi + math.pi / 2), u(phi + math.pi)
    arrow(f, (0, 0), shift((0, 0), a1, 1.3), color=GREEN, width=1.4, size=8)
    arrow(f, (0, 0), shift((0, 0), b2, 1.35), color=ORANGE, width=1.4, size=8)
    arrow(f, (0, 0), shift((0, 0), a2, 1.55), width=1.4, size=8)
    f.text(shift((0, 0), a1, 1.44), 'x', color=GREEN, size=15)
    f.text(shift((0, 0), a2, 1.68), 'y = x′', size=15)
    f.text(shift((0, 0), b2, 1.5), 'y′', color=ORANGE, size=15)
    # Coordinates in the frame phi + pi/2 (orange) and phi (green).
    q1 = shift((0, 0), b1, c[0])
    f.line((0, 0), q1, stroke=ORANGE, width=2.6)
    f.line(q1, centre, stroke=ORANGE, width=2.6)
    q2 = shift((0, 0), a1, rc[0])
    f.line((0, 0), q2, stroke=GREEN, width=2.6)
    f.line(q2, centre, stroke=GREEN, width=2.6)
    f.text(shift(shift((0, 0), b1, c[0] / 2), a1, 0.13),
           sbn('c', '1'), size=14, color=ORANGE, anchor='start')
    f.text(shift(shift(q1, b2, c[1] / 2), b1, 0.13), sbn('c', '2'), size=14,
           color=ORANGE)
    f.text(shift(shift((0, 0), a1, rc[0] / 2), a2, -0.14), '−' + sbn('c', '2'),
           size=14, color=GREEN)
    # Below the square, which the green leg enters halfway up.
    f.text(shift(shift(q2, a2, 0.25), a1, -0.12), sbn('c', '1'),
           size=14, color=GREEN, anchor='end')
    f.line((0, 0), (1.2, 0), stroke=FAINT, width=1, dash='3 3')
    thin_arc(f, (0, 0), 0.62, 0, phi)
    f.text(shift((0, 0), u(phi / 2), 0.75), 'φ', size=14)
    f.dot((0, 0))
    f.text((0.08, -0.12), 'o', size=14)
    f.dot(centre, fill=BLUE)
    f.text(shift(shift(centre, a1, -0.28), a2, 0.27), 'S', size=17,
           color=BLUE)
    f.save('03-tools/quarter-turn', 'A square sitting at c = (c1, c2) in the '
           'frame phi + pi/2, whose axes are y = x prime and y prime, sits at '
           '(-c2, c1) in the frame phi, whose axes are x and y')


def slots():
    """Lemma 3.31: every square sits, in the frame phi, at one of the points
    of the model; distinct squares at distinct points."""
    centers = MODELS[5][0]
    phi = rad(20)
    f_map = [2, 0, 4, 1, 3]  # S_{i+1} sits at c_{f_map[i]+1}
    F = lambda p: rotate(p, phi)
    f = Figure(-1.75, 1.75, -1.7, 1.75, 140)
    f.line(shift((0, 0), u(phi), -1.7), shift((0, 0), u(phi), 1.7),
           stroke=FAINT, width=1)
    f.line(shift((0, 0), u(phi + math.pi / 2), -1.7),
           shift((0, 0), u(phi + math.pi / 2), 1.7), stroke=FAINT, width=1)
    assert sorted(f_map) == list(range(5))
    for i, k in enumerate(f_map):
        c = centers[k]
        f.polygon([F(q) for q in square_corners(c)], fill=FILLS[i],
                  stroke=COLORS[i])
        f.text(F(shift(c, (0.0, 0.17))), sbn('S', str(i + 1), size=17),
               size=17, color=COLORS[i])
        f.dot(F(c), r=3)
        f.text(F(shift(c, (0.0, -0.17))), sbn('c', str(k + 1), size=13),
               size=13)
    f.text(shift((0, 0), u(phi), 1.73), 'φ', size=14, anchor='start')
    # The model point c1 = (0, 0) goes to the disk centre o.
    assert centers[0] == (0, 0)
    f.text(F((-0.12, 0.0)), 'o', size=14, anchor='end')
    f.save('03-tools/slots', 'The plus in the frame phi at o, with a square '
           'sitting at each of its five points: S1 at c3, S2 at c1, S3 at c5, '
           'S4 at c2 and S5 at c4')


def centre_bound():
    """Lemma 3.4 (2) and (3) for R^2 = 5/4, the case of two squares, where
    rho = sqrt(R^2 - 1/4) - 1/2 = 1/2: the part of the disk phi <= 5/4 with
    a, b >= 0 lies in the quarter disk a^2 + b^2 <= 1/4 and left of the line
    a = 1/2."""
    K = 1.25
    rho = math.sqrt(K - 0.25) - 0.5
    assert abs(rho - 0.5) < 1e-15
    region = quadrant_disk(K, 200)
    for a, b in region:
        assert a <= rho + 1e-12 and a * a + b * b <= rho * rho + 1e-12
    assert abs(phi_ab(rho, 0) - K) < 1e-12 and abs(phi_ab(0, rho) - K) < 1e-12
    top = 0.65
    f = Figure(-0.125, top + 0.06, -0.125, top + 0.04, 420)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    thin_arc(f, (0, 0), rho, 0, math.pi / 2, color=ORANGE, width=2)
    f.line((rho, -0.03), (rho, top - 0.025), width=1.2, dash='5 4')
    f.line((-0.04, 0), (top, 0), width=1)
    f.line((0, -0.04), (0, top), width=1)
    arrowhead(f, (top + 0.02, 0), (0, 0), size=8)
    arrowhead(f, (0, top + 0.02), (0, 0), size=8)
    f.text((top, -0.05), 'a', anchor='end', size=14)
    f.text((-0.035, top - 0.01), 'b', anchor='end', size=14)
    for p in ((rho, 0), (0, rho)):
        f.dot(p, r=3.6)
    word(f, (rho, -0.06), '½', size=14)
    word(f, (-0.04, rho), '½', size=14, anchor='end')
    f.text((0.17, 0.15), 'φ ≤ 5/4', size=14, color=BLUE)
    f.text(shift((0, 0), u(math.pi / 3), rho + 0.05), it('a') + '² + ' +
           it('b') + '² ≤ ¼', size=14, color=ORANGE, italic=False,
           anchor='start')
    f.text((rho + 0.025, 0.52), it('a') + ' ≤ ½', size=14, italic=False,
           anchor='start')
    f.dot((0, 0), r=2.6)
    f.save('03-tools/centre-bound', 'The (a, b)-plane: the part with a, b '
           'at least 0 of the disk where phi is at most 5/4 lies in the '
           'quarter disk a squared plus b squared at most 1/4, touching it at '
           '(1/2, 0) and (0, 1/2), and left of the line a = 1/2')


def chart_arc():
    """Lemma 3.21 (2) for a chart with orientation -1: the chart angles in
    (t1, t2) give the arc of directions theta - t, centred at
    theta - (t1 + t2)/2."""
    theta, eps, a, b, r = rad(35), -1, 0.8, 0.3, 0.55
    c = shift(shift((0, 0), u(theta), a), u(theta + math.pi / 2), eps * b)
    deg = math.degrees(theta)
    check_chart(c, deg, theta, eps, a, b)
    # The interval of chart angles: the run of the circle in Q(a, b).
    runs = arcs_in(lambda p: in_open_square(p, (a, b)), r, steps=14400)
    t1, t2 = longest(runs)
    t1, t2 = t1 - 2 * math.pi, t2 - 2 * math.pi
    assert len(runs) == 1 and t1 < 0 < t2
    # In the plane, the same points form the arc of directions theta + eps t.
    runs = arcs_in(lambda p: in_open_square(p, c, deg), r, steps=14400)
    p1, p2 = longest(runs)
    same = lambda x, y: abs((x - y + math.pi) % (2 * math.pi) - math.pi) < 1e-3
    assert same(p1, theta + eps * t2) and same(p2, theta + eps * t1)
    mid = (t1 + t2) / 2
    right = 3.2
    f = Figure(-0.8, right + 2.05, -0.95, 1.4, 135)
    # The plane.
    word(f, (0.35, 1.32), 'the plane', size=14, color=FAINT)
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    f.circle((0, 0), r)
    f.arc((0, 0), r, p1, p2, ORANGE, width=5)
    f.line((0, 0), shift((0, 0), u(theta), 1.45), width=1)
    f.text(shift((0, 0), u(theta), 1.55), sbn('θ', 'S', size=14), size=14)
    centre = theta + eps * mid
    f.line((0, 0), shift((0, 0), u(centre), 1.47), width=1, dash='4 3')
    f.text(shift((0, 0), u(centre), 1.52), sbn('θ', 'S', ' − (', 13) +
           sbn('t', '1', ' + ', 13) + sbn('t', '2', ')/2', 13), size=13,
           anchor='start')
    for t in (p1, p2):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
        f.dot(shift((0, 0), u(t), r), r=3.2)
    f.text(shift(shift((0, 0), u(p2), r), (-0.08, 0.17)),
           sbn('θ', 'S', ' − ', 13) + sbn('t', '1', size=13), size=13,
           anchor='end')
    f.text(shift(shift((0, 0), u(p1), r), (-0.1, -0.07)),
           sbn('θ', 'S', ' − ', 13) + sbn('t', '2', size=13), size=13,
           anchor='end')
    arc_arrow(f, (0, 0), 0.22, theta - 0.12, theta - 0.12 - 0.9,
              color=ORANGE, width=1.2, size=7)
    f.dot((0, 0))
    f.text((-0.05, -0.09), 'o', anchor='end')
    # The chart.
    o2 = (right, 0)
    word(f, (right + 0.5, 1.32), 'the chart', size=14, color=FAINT)
    f.square(shift(o2, (a, b)), fill=FILLS[0], stroke=BLUE)
    f.line(o2, shift(o2, (1.68, 0)), width=1)
    f.text(shift(o2, (1.68, 0.08)), it('t') + ' = 0', size=12, italic=False,
           anchor='end')
    f.circle(o2, r)
    f.arc(o2, r, t1, t2, ORANGE, width=5)
    f.line(o2, shift(o2, u(mid), 1.42), width=1, dash='4 3')
    f.text(shift(o2, u(mid), 1.47), '(' + sbn('t', '1', ' + ', 13) +
           sbn('t', '2', ')/2', 13), size=13, anchor='start')
    for t in (t1, t2):
        f.line(o2, shift(o2, u(t), r), width=1)
        f.dot(shift(o2, u(t), r), r=3.2)
    f.text(shift(shift(o2, u(t1), r), (0.02, -0.12)), sbn('t', '1', size=14),
           size=14, anchor='start')
    f.text(shift(shift(o2, u(t2), r), (-0.04, 0.1)), sbn('t', '2', size=14),
           size=14, anchor='end')
    f.dot(o2)
    f.text(shift(o2, (-0.05, -0.09)), 'o', anchor='end')
    arrow(f, (1.6, -0.62), (2.3, -0.62), width=1.4)
    word(f, (1.95, -0.77), 'turn by' + NB + '−' + it(sbn('θ', 'S', size=13)) +
         f'<tspan dy="{-0.3 * 13:.1f}">, reflect</tspan>', size=13)
    f.save('03-tools/chart-arc', 'A square with a chart of orientation -1, '
           'in the plane and in its chart: the chart angles from t1 to t2 '
           'give the arc of the circle from theta - t2 to theta - t1, centred '
           'at theta - (t1 + t2)/2')


def main():
    optimal_packings()
    column_packings()
    reduction()
    arc_method()
    markers()
    angle_between()
    arcsin_graph()
    quarter_frame()
    touching()
    frame_map()
    congruence_figure()
    axis_lemma()
    lower_bound()
    scheme()
    disk_constraint()
    two_squares()
    six_pins()
    reflection()
    contact_polygons()
    support_proof()
    lengths()
    width_graph()
    shrink()
    arc_overlap()
    perimeter()
    gaps_figure()
    chart_moves()
    cartesian()
    caps()
    centre_slab()
    estimates()
    sine_concave()
    quarter_turn()
    slots()
    centre_bound()
    chart_arc()


if __name__ == '__main__':
    main()

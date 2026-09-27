#!/usr/bin/env python3
"""Draw the figures of Chapters 1 to 3 of docs/proof/ (the introduction,
preliminaries.md and common.md) as SVG files docs/proof/figures/front-*.svg.

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


def column(heights):
    return [(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5)] + [
        (0, y) for y in heights]


def check_model(centers, R):
    """Lemma 2.8: a packing in the closed disk of radius R about the origin,
    with a corner on the circle. Returns the corners on the circle."""
    for i, p in enumerate(centers):
        assert (abs(p[0]) + 0.5) ** 2 + (abs(p[1]) + 0.5) ** 2 <= R * R + 1e-12
        for q in centers[i + 1:]:
            assert max(abs(p[0] - q[0]), abs(p[1] - q[1])) >= 1 - 1e-12
    touch = [q for c in centers for q in square_corners(c)
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
        f.polygon([shift(at, rotate(q, phi)) for q in square_corners(c)],
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
    rows = [(1, 2, 3, 4), (5, 7)]
    widths = [sum(2 * MODELS[n][1] for n in row) + gap * (len(row) - 1)
              for row in rows]
    W = max(widths)
    top = [max(MODELS[n][1] for n in row) for row in rows]
    label_h = 0.62
    H = 2 * top[0] + label_h + 0.28 + 2 * top[1] + label_h
    f = Figure(0, W, -H, 0, s)
    ys = [-top[0], -(2 * top[0] + label_h + 0.28 + top[1])]
    for row, width, R_top, y in zip(rows, widths, top, ys):
        x = (W - width) / 2
        for n in row:
            centers, R, name = MODELS[n]
            x += R
            draw_model(f, centers, R, at=(x, y))
            word(f, (x, y - R_top - 0.2), it('n') + f' = {n}', size=14)
            f.text((x, y - R_top - 0.45), sbn('R', str(n), ' = ' + name, 14),
                   size=14)
            x += R + gap
    f.save('front-optimal', 'The six optimal packings, n = 1, 2, 3, 4, 5 '
           'and 7, each in its dashed circle of radius R_n, drawn at a common '
           'scale; dots mark the corners on the circle')


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
        f.text(shift(at, (0, -R - 0.24)),
               '(' + sbn('y', '1', ', ', 13) + sbn('y', '2', ', ', 13) +
               sbn('y', '3', ') = ', 13) + name, size=13)
    f.save('front-columns', 'Four column packings of seven squares in the '
           'circle of radius root 13 over 2: the side squares are fixed, and '
           'the three middle squares move along the dotted middle column, '
           'each on its own')


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
    f.save('front-reduction', 'The plus turned about o in its dashed circle of '
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
    f.save('front-arc-method', 'Four squares and the circle of radius 1/2 '
           'about o, inside the disk of radius root 2. Left: a square that '
           'avoids o, without a vertex at o, holds more than a quarter of the '
           'circle. Right: a square containing o holds the quarter facing its '
           'centre')


def markers():
    """Seven squares: markers of a contact are pi/3 apart; turned closer,
    the squares overlap; in a column packing the six markers form a
    regular hexagon."""
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
    ms = sorted(marker(c, 0) % (2 * math.pi) for c in centers
                if not in_open_square((0, 0), c))
    assert len(ms) == 6
    for k in range(6):
        assert abs(ms[k] - (math.pi / 6 + k * math.pi / 3)) < 1e-12
    polyline(f, [shift(at, u(m)) for m in ms + ms[:1]], stroke=ORANGE,
             width=1.4, dash='5 4')
    for m in ms:
        f.line(at, shift(at, u(m)), stroke=ORANGE, width=1.2)
        f.dot(shift(at, u(m)), r=3.4, fill=ORANGE)
    f.text(shift(at, (0.1, 0.0)), 'o', anchor='start', size=14)
    f.save('front-markers', 'Seven squares and their markers on the unit '
           'circle. Left: a side square and the top square touch, and their '
           'markers are exactly pi/3 apart. Middle: turned so that the '
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
    for t, s in ((x, 'θ'), (xp, 'θ′')):
        f.line((0, 0), shift((0, 0), u(t), 1), width=1)
        f.dot(shift((0, 0), u(t), 1))
        f.text(shift((0, 0), u(t), 1.16), s)
    f.text(shift((0, 0), u(xp + d / 2), 0.62), 'd(θ, θ′)', size=14,
           color=ORANGE)
    word(f, shift((0, 0), u(x + (two - d) / 2), 0.7), '2π − ' + it('d'),
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
    for lo, hi, s, col in ((xp - two, x, 'd', ORANGE),
                           (x, xp, '2π − ' + it('d'), FAINT)):
        h = 0.3
        f.line((X(lo), y0 + h), (X(hi), y0 + h), stroke=col, width=1.6)
        for t in (lo, hi):
            f.line((X(t), y0 + h - 0.06), (X(t), y0 + h + 0.06), stroke=col,
                   width=1.6)
        f.text(((X(lo) + X(hi)) / 2, y0 + h + 0.17), s, size=14, color=col)
    f.save('front-angle', 'The angle between two directions theta and theta '
           'prime: the shorter way round the circle, and the least distance '
           'between real numbers that represent them')


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
    for y, s in ((-math.pi / 2, '−π/2'), (math.pi / 2, 'π/2'),
                 (math.pi, 'π')):
        word(f, shift(P(0, y), (-0.08, 0.12)), s, size=12, anchor='end')
    word(f, P(1.75, math.pi / 2 + 0.22), 'arcsin', size=14, color=BLUE)
    word(f, P(-1.75, math.pi + 0.22), 'arccos', size=14, color=ORANGE)
    f.save('front-arcsin', 'The extended arcsine, constant at minus and plus '
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
    f.save('front-quarter-frame', 'The same square S and point p read in the '
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
    f.save('front-touching', 'Left: two squares sharing part of an edge. '
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
    f.save('front-frame-map', 'The frame F_phi carries the plane with origin '
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
    for side, M, centre in ((0, lambda p: p, (0, 0)), (1, F, o)):
        f.circle(centre, R, stroke=INK, width=1.2, dash='6 4')
        for k, c in enumerate(centers):
            f.polygon([M(p) for p in square_corners(c)], fill=FILLS[k],
                      stroke=COLORS[k])
            text = sbn('M', str(k + 1)) if side == 0 else sbn('S', names[k])
            f.text(M(shift(c, (0, 0.12 if k == 2 else 0.0))), text, size=16,
                   color=COLORS[k])
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
    f.save('front-congruence', 'Left: the T as a model M1, M2, M3 in the disk '
           'of radius R about 0. Right: a configuration congruent to it, '
           'turned by phi about o and relabelled; a point q of M1 and its '
           'image are at the same distance from the centre')


def axis_lemma():
    """Lemma 2.8: centres 1 apart in one coordinate, and the farthest corner
    of an axis-parallel square."""
    p, q = (0.0, 0.0), (1.45, 0.42)
    assert not interiors_meet(square_corners(p), square_corners(q))
    o, c = (4.55, -0.45), (-0.7, 0.62)
    corner = (-(abs(c[0]) + 0.5), abs(c[1]) + 0.5)
    R = norm(corner) + 0.1
    f = Figure(-0.75, o[0] + R + 0.1, o[1] - R - 0.12, o[1] + R + 0.12, 92)
    f.square(p, fill=FILLS[0], stroke=BLUE)
    f.square(q, fill=FILLS[2], stroke=GREEN)
    y0 = -0.85
    f.line((-0.7, y0), (2.3, y0), width=1)
    x0, x1 = p[0] + 0.5, q[0] - 0.5
    for x in (x0, x1):
        f.line((x, y0 - 0.05), (x, 1.2), width=1.1, dash='6 4')
    for x, s in ((p[0], sbn('p', '1', size=13)), (q[0], sbn('q', '1', size=13))):
        f.line((x, y0 - 0.04), (x, y0 + 0.04), width=1.2)
        f.line((x, y0 + 0.04), (x, p[1] if x == p[0] else q[1]),
               stroke=FAINT, width=1, dash='2 3')
        f.text((x, y0 - 0.18), s, size=13)
    f.text((x0, y0 - 0.42), sbn('p', '1', ' + ½', 13), size=13)
    f.text((x1, y0 - 0.42), sbn('q', '1', ' − ½', 13), size=13)
    f.dot(p, fill=BLUE)
    f.dot(q, fill=GREEN)
    f.text(shift(p, (0, 0.16)), 'Q(p)', size=14, color=BLUE)
    f.text(shift(q, (0, 0.16)), 'Q(q)', size=14, color=GREEN)
    word(f, (-0.55, 1.35), '(1)', size=14)
    # (2): the farthest corner.
    cc = shift(o, c)
    far = max(square_corners(c), key=norm)
    assert abs(far[0] - corner[0]) < 1e-12 and abs(far[1] - corner[1]) < 1e-12
    f.circle(o, R, stroke=INK, width=1.2, dash='6 4')
    f.line(shift(o, (-R + 0.05, 0)), shift(o, (R - 0.05, 0)), stroke=FAINT,
           width=1)
    f.line(shift(o, (0, -R + 0.05)), shift(o, (0, R - 0.05)), stroke=FAINT,
           width=1)
    f.square(cc, fill=FILLS[0], stroke=BLUE)
    f.dot(cc, fill=BLUE)
    f.text(shift(cc, (0.1, -0.02)), 'c', color=BLUE, anchor='start')
    fc = shift(o, corner)
    f.line(o, (fc[0], o[1]), stroke=ORANGE, width=2.4)
    f.line((fc[0], o[1]), fc, stroke=ORANGE, width=2.4)
    f.line(o, fc, stroke=ORANGE, width=1.4, dash='5 3')
    f.dot(fc, fill=ORANGE)
    f.text(shift(o, (corner[0] / 2, -0.15)), '|x| + ½', size=13,
           color=ORANGE)
    vtext(f, shift(fc, (-0.12, -corner[1] / 2)), '|y| + ½', size=13,
          color=ORANGE)
    f.dot(o)
    f.text(shift(o, (0.08, -0.13)), '0', anchor='start', size=14,
           italic=False)
    f.text(shift(o, u(rad(-35)), R + 0.02), 'R', size=14, anchor='start')
    word(f, shift(o, (-R + 0.1, R - 0.05)), '(2)', size=14)
    f.save('front-axis-lemma', 'Left: two axis-parallel squares whose centres '
           'differ by more than 1 across lie on either side of a vertical '
           'line. Right: the corner of Q(c) farthest from the origin is |x| + '
           '1/2 across and |y| + 1/2 up')


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
    f.save('front-lower-bound', 'Left: the T reaching the circle of radius '
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
               7: ((1.5, -1), '9/4 + 1 = 13/4')}
    gap, s = 0.62, 56
    rows = [(1, 2, 3), (4, 5, 7)]
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
                       for c in centers for q in square_corners(c))
            x += R
            at = (x, y)
            draw_model(f, centers, R, at=at, touch=False)
            f.line(at, shift(at, p), stroke=ORANGE, width=1.8)
            f.dot(shift(at, p), r=4, fill=ORANGE)
            word(f, (x, y - R_top - 0.22), it('n') + f' = {n}', size=13)
            f.text((x, y - R_top - 0.47), '|' + it('p') + '|² = ' + text,
                   size=12, italic=False, color=ORANGE)
            x += R + gap
    f.save('front-scheme', 'The six optimal models, each in its dashed circle '
           'of radius R_n, with one corner p on the circle and its squared '
           'distance from the centre, which equals R_n squared')


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
    f = Figure(-0.12, 2 * step + top, -0.3, top + 0.2, 155)
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
    f.save('front-contact-polygons', 'The contact polygons of three, four and '
           'five squares where a, b are at least 0: each is cut out by '
           'tangent lines of the disk phi at most R_n squared at the dotted '
           'points, and contains that disk')


def octagon():
    """The octagon P8 in the plane of the local coordinates of o, with its
    eight lines, the square S itself, and the region phi <= 5/2."""
    f = Figure(-1.55, 1.55, -1.5, 1.55, 150)
    L = 1.45
    lines = [(sx * 3, sy * 1, 3) for sx in (1, -1) for sy in (1, -1)] + [
        (sx * 1, sy * 3, 3) for sx in (1, -1) for sy in (1, -1)]
    poly = [(-2, -2), (2, -2), (2, 2), (-2, 2)]
    for p, q, c in lines:
        poly = clip(poly, p, q, c)
    verts = {(round(x, 9), round(y, 9)) for x, y in poly}
    assert verts == {(1, 0), (-1, 0), (0, 1), (0, -1), (0.75, 0.75),
                     (-0.75, 0.75), (0.75, -0.75), (-0.75, -0.75)}
    # The region phi(|x|, |y|) <= 5/2: four arcs.
    region = []
    K = math.sqrt(2.5)
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        t0, t1 = math.asin(0.5 / K), math.pi / 2 - math.asin(0.5 / K)
        arc = [(-0.5 + K * math.cos(t0 + (t1 - t0) * j / 60),
                -0.5 + K * math.sin(t0 + (t1 - t0) * j / 60))
               for j in range(61)]
        arc = [(sx * x, sy * y) for x, y in arc]
        region += arc if sx * sy > 0 else arc[::-1]
    for x, y in region:
        assert all(p * x + q * y <= c + 1e-9 for p, q, c in lines)
    for p, q, c in lines:
        # Two points of the line p x + q y = c inside the window.
        if abs(q) > abs(p):
            a, b = (-L, (c + p * L) / q), (L, (c - p * L) / q)
        else:
            a, b = ((c + q * L) / p, -L), ((c - q * L) / p, L)
        f.line(a, b, stroke=FAINT, width=1, dash='4 3')
    f.polygon(poly, fill=FILLS[1], stroke=ORANGE, width=2)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.4)
    f.polygon(square_corners((0, 0)), stroke=INK, width=1.4, dash='5 3')
    f.line((-L, 0), (L, 0), stroke=INK, width=0.8)
    f.line((0, -L), (0, L), stroke=INK, width=0.8)
    f.text((L, -0.12), sbn('x', 'S', '(o)', 14), anchor='end', size=14)
    f.text((0.07, L - 0.02), sbn('y', 'S', '(o)', 14), anchor='start',
           size=14)
    for q in poly:
        f.dot(q, r=3, fill=ORANGE)
    f.text((0.82, 0.86), '(¾, ¾)', size=13, italic=False, anchor='start')
    f.text((1.04, 0.1), '(1, 0)', size=13, italic=False, anchor='start')
    f.text((0.2, -0.2), 'S', size=16)
    f.dot((0, 0), r=2.6)
    f.text((-0.07, -0.12), sbn('c', 'S'), anchor='end', size=14)
    assert abs(3 * 0.51 + 1.47 - 3) < 1e-9
    f.text((0.6, 1.47), '3x + y = 3', size=12, italic=False, anchor='start',
           color=FAINT)
    f.text((0.62, 0.52), 'φ ≤ 5/2', size=13, color=BLUE, anchor='end')
    f.text((-0.95, 0.72), sbn('P', '8', size=16), size=16, color=ORANGE)
    f.save('front-octagon', 'The octagon P8 in the plane of the local '
           'coordinates of o: the eight lines, plus or minus 3x plus or minus '
           'y = 3 and plus or minus x plus or minus 3y = 3, around the region '
           'phi at most 5/2 and the square S itself')


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
    f.text((-1.15, -0.45), 'S', size=17, color=BLUE)
    f.text((1.45, -0.45), 'T', size=17, color=GREEN)
    f.save('front-support-proof', 'Two disjoint squares, a separating line, '
           'and the segments from each centre to its extreme vertex in the '
           'direction n; test points a fraction t of the way lie in the open '
           'squares, and the two supporting lines are at the full widths')


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
    f.save('front-width-graph', 'The width of a square in a unit direction n: '
           'one half when n is parallel to a side, root 2 over 2 along a '
           'diagonal, and in between otherwise, as a function of the angle '
           'between n and a side')


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
    f.save('front-shrink', 'The three open arcs of the T on the circle of '
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
    f.save('front-arc-overlap', 'Two arcs U and V whose centres are less than '
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
    f.text(shift((0, 0), u((xs[0] + xs[2]) / 2), 0.62),
           'd(' + sbn('θ', 'U', ', ', 13) + sbn('θ', 'W', ')', 13), size=13,
           color=ORANGE)
    f.dot((0, 0))
    f.text((0.05, -0.1), 'o', anchor='start')
    f.save('front-perimeter', 'Three directions cut the circle into three gaps '
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
    f.text((0.05, -0.1), 'o', anchor='start')
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
        f.text(((a + b) / 2, y0 + 0.4), '≥ g', size=13, color=col,
               italic=False)
    f.save('front-gaps', 'Six directions pairwise at least g = pi/3 apart, '
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
    f = Figure(0, 2 * w, -2 * h, 0, 96)
    for k, ((title, theta, eps, (x, y), names), head) in enumerate(
            zip(moves, heads)):
        at = (1.45 + (k % 2) * w, -1.75 - (k // 2) * h)
        check_chart(c, deg, theta, eps, x, y)
        cc = shift(at, c)
        f.square(cc, deg, fill=FILLS[0], stroke=BLUE)
        a1, a2 = chart_axes(f, at, theta, eps)
        f.text(shift(at, a1, 1.37), 't = 0', size=12, italic=False)
        f.text(shift(at, a2, 1.2), 't = π/2', size=12, italic=False)
        q = shift(at, a1, x)
        f.line(at, q, stroke=ORANGE, width=2.6)
        f.line(q, cc, stroke=ORANGE, width=2.6)
        n1 = (a2[0] * (-1 if y > 0 else 1), a2[1] * (-1 if y > 0 else 1))
        f.text(shift(shift(at, a1, x / 2), n1, 0.2), names[0], size=14,
               color=ORANGE)
        n2 = (a1[0] * (1 if x > 0 else -1), a1[1] * (1 if x > 0 else -1))
        f.text(shift(shift(q, a2, y / 2), n2, 0.17), names[1], size=14,
               color=ORANGE)
        f.dot(at)
        f.text(shift(at, (-0.1, -0.12)), 'o', size=14)
        f.dot(cc, fill=BLUE)
        word(f, (at[0] + 0.4, at[1] + 1.55), title + ' ' + it(head), size=14)
    f.save('front-chart-moves', 'One square and four charts: a chart with '
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
            f.text(shift(at, u(theta - math.pi / 2), 1.1), 't = π/2',
                   size=12, italic=False, color=ORANGE)
        arc_arrow(f, at, 0.3, theta + eps * 0.2,
                  theta + eps * (math.pi / 2 - 0.2), color=ORANGE, width=1.2,
                  size=7)
        q = shift(at, u(theta), a)
        f.line(at, q, stroke=ORANGE, width=2.6)
        f.line(q, cc, stroke=ORANGE, width=2.6)
        side = u(theta - math.pi / 2) if eps > 0 else u(theta + math.pi / 2)
        f.text(shift(shift(at, u(theta), a / 2), side, 0.15), sbn('a', 'S'),
               size=14, color=ORANGE)
        f.text(shift(shift(q, u(theta + math.pi / 2), eps * b / 2),
                     u(theta), 0.1),
               sbn('b', 'S') if eps > 0 else '−' + sbn('b', 'S'), size=14,
               color=ORANGE, anchor='start')
        f.dot(at)
        f.text(shift(at, (-0.08, -0.13)), 'o', size=14)
        f.dot(cc, fill=BLUE)
        title = 'orientation ' + it(sbn('ε', 'S', ' = +1' if eps > 0
                                        else ' = −1', 14))
        f.text((at[0] + 0.45, 1.62), title, size=14, italic=False)
    f.save('front-cartesian', 'A square with a chart of phase theta and '
           'orientation +1 or -1, and the frame theta at o: the centre is at '
           '(a, b) or (a, -b) in the frame')


def caps():
    """Lemma 3.24 (2) and (3): the full cap, the clipped cap, and the half
    circle, in the chart."""
    cases = [(it(sbn('A', 'S', ' ≤ ', 13)) + it(sbn('V', 'S', ':', 13)) + NB +
              'the full cap', 0.45, 0.75, 0.1),
             (it(sbn('V', 'S', ' &lt; ', 13)) + it(sbn('A', 'S', ':', 13)) + NB +
              'the lower edge clips it', 0.45, 0.7, 0.35),
             (it(sbn('a', 'S', ' = ½:', 13)) + NB + 'a half circle', 0.3, 0.5,
              0.15)]
    step = 2.0
    f = Figure(-0.62, 2 * step + 1.35, -0.72, 1.1, 118)
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
        if k < 2:
            thin_arc(f, at, 0.13, 0, A)
            f.text(shift(at, u(A / 2), 0.21), sbn('A', 'S', size=13), size=13)
            thin_arc(f, at, 0.17, -min(A, V), 0)
            f.text(shift(at, u(-min(A, V) / 2), 0.27),
                   sbn('A', 'S', size=13) if k == 0 else
                   sbn('V', 'S', size=13), size=13)
        f.dot(at)
        f.text(shift(at, (-0.05, 0.08)), 'o', anchor='end', size=14)
        f.dot(shift(at, (a, b)), fill=BLUE)
        f.text((at[0] + 0.35, 1.02), title, size=13, italic=False)
    f.save('front-caps', 'Three exterior squares in their charts with a '
           'circle of radius at most 1/2 about o. Left: the full cap from -A '
           'to A. Middle: the lower edge clips the cap, from -V to A. Right: '
           'with the near edge through o, the square holds a half circle')


def support_cases():
    """Lemma 3.26: the largest value of p a + q b over the quadrilateral
    P8 with a, b >= 0, in the three cases of the proof."""
    quad = [(0, 0), (1, 0), (0.75, 0.75), (0, 1)]
    cases = [((1.0, 0.22), 'p ≥ 3q', (1, 0)),
             ((0.25, 1.0), 'q ≥ 3p', (0, 1)),
             ((1.0, 0.6), 'otherwise', (0.75, 0.75))]
    step = 1.6
    f = Figure(-0.12, 2 * step + 1.3, -0.3, 1.42, 145)
    for k, ((p, q), title, best) in enumerate(cases):
        at = (k * step, 0)
        vals = [p * x + q * y for x, y in quad]
        top = max(vals)
        assert abs(p * best[0] + q * best[1] - top) < 1e-12
        assert sum(1 for v in vals if abs(v - top) < 1e-12) == 1
        f.polygon([shift(at, x) for x in quad], fill=FILLS[1], stroke=ORANGE,
                  width=2)
        for level in (0.35 * top, 0.7 * top):
            seg = clip_segment((level / p, 0), (0, level / q), 1.25)
            f.line(shift(at, seg[0]), shift(at, seg[1]), stroke=FAINT,
                   width=1, dash='4 3')
        # The level line through the best vertex, inside the panel.
        seg = clip_segment((top / p, 0.0), (0.0, top / q), 1.25)
        f.line(shift(at, seg[0]), shift(at, seg[1]), stroke=BLUE, width=1.6)
        ab_axes_at(f, at, 1.28)
        f.dot(shift(at, best), r=4.5, fill=BLUE)
        n = (p / math.hypot(p, q), q / math.hypot(p, q))
        arrow(f, shift(at, (0.18, 0.18)), shift(at, shift((0.18, 0.18), n,
                                                          0.3)),
              width=1.6, size=8)
        f.text(shift(at, shift((0.2, 0.18), n, 0.42)), '(p, q)', size=13,
               anchor='start')
        f.text((at[0] + 0.62, 1.35), title, size=14,
               italic=title != 'otherwise')
    f.save('front-support-cases', 'The quadrilateral where P8 meets a, b at '
           'least 0, with level lines of pa + qb: the largest value is at the '
           'vertex (1, 0) when p is at least 3q, at (0, 1) when q is at least '
           '3p, and at (3/4, 3/4) otherwise')


def estimates():
    """Lemma 3.29 (2), (3) and (5): arcsin between x and x + x^3/4, and the
    cosine above 1 - t^2/2 and 401/500."""
    f = Figure(-0.35, 6.45, -0.55, 3.05, 100)
    # (2) and (3) on [0, 1].
    P = Plot(f, 0, 0, 2.86, 2.72, (0, 1.1), (0, math.pi / 2 + 0.07))
    for k in range(101):
        x = k / 100
        assert x <= math.asin(x) + 1e-15
        if x <= 0.6:
            assert math.asin(x) <= x + x ** 3 / 4 + 1e-15
    P.curve(lambda x: x, 0, 1, stroke=FAINT, width=1.6)
    P.curve(lambda x: x + x ** 3 / 4, 0, 0.6, stroke=ORANGE, width=2)
    P.curve(lambda x: x + x ** 3 / 4, 0.6, 1, stroke=ORANGE, width=1.4,
            dash='4 4')
    P.curve(math.asin, 0, 1, n=600, stroke=BLUE, width=2.2)
    f.line(P.P(0.6, 0), P.P(0.6, 0.75), stroke=INK, width=1, dash='2 3')
    P.axes('x', '', [(0.6, '3/5'), (1, '1')], [(math.pi / 2, 'π/2')])
    word(f, P.P(0.88, 1.5), 'arcsin ' + it('x'), size=13, color=BLUE)
    word(f, P.P(0.95, 0.83), it('x'), size=13, color=FAINT)
    f.text(P.P(0.47, 0.72), 'x + ' + '<tspan font-size="11">x³/4</tspan>',
           size=13, color=ORANGE, anchor='end')
    # (5) on [-pi/5, pi/5].
    t5 = math.pi / 5
    Q = Plot(f, 3.6, 0, 2.6, 2.6, (-0.8, 0.8), (0.7, 1.02))
    for k in range(201):
        t = -t5 + 2 * t5 * k / 200
        assert math.cos(t) >= 1 - t * t / 2 > 401 / 500
    f.polygon([Q.P(-t5, 0.7), Q.P(t5, 0.7), Q.P(t5, 1.02), Q.P(-t5, 1.02)],
              fill=GREY, stroke='none', opacity=0.5)
    assert 1 - 0.75 ** 2 / 2 > 0.7
    Q.curve(lambda t: 401 / 500, -0.75, 0.75, stroke=INK, width=1,
            dash='4 3')
    Q.curve(lambda t: 1 - t * t / 2, -0.75, 0.75, stroke=ORANGE, width=2)
    Q.curve(math.cos, -0.75, 0.75, stroke=BLUE, width=2.2)
    Q.axes('t', '', [(-t5, '−π/5'), (t5, 'π/5')], [(401 / 500, '401/500'),
                                                  (1, '1')],
           x_at=-0.8, y_at=0.7)
    word(f, Q.P(0.36, 0.975), 'cos ' + it('t'), size=13, color=BLUE)
    word(f, Q.P(0.0, 0.88), '1 − ' + it('t') + '²/2', size=13, color=ORANGE)
    f.save('front-estimates', 'Left: the arcsine between x and x + x cubed '
           'over 4 on the interval from 0 to 3/5. Right: on the shaded '
           'interval from -pi/5 to pi/5 the cosine lies above 1 - t squared '
           'over 2, and both lie above 401/500')


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
    f.save('front-sine-concave', 'The sine on the interval from 0 to pi/2 and '
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
    f.text(shift(shift(q2, a2, rc[1] / 2), a1, -0.12), sbn('c', '1'),
           size=14, color=GREEN, anchor='end')
    f.line((0, 0), (1.2, 0), stroke=FAINT, width=1, dash='3 3')
    thin_arc(f, (0, 0), 0.62, 0, phi)
    f.text(shift((0, 0), u(phi / 2), 0.75), 'φ', size=14)
    f.dot((0, 0))
    f.text((0.08, -0.12), 'o', size=14)
    f.dot(centre, fill=BLUE)
    f.text(shift(centre, (0.1, 0.1)), 'S', size=17, color=BLUE, anchor='start')
    f.save('front-quarter-turn', 'A square sitting at c = (c1, c2) in the '
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
    f.text(shift((0, 0), u(phi), 1.62), 'φ', size=14, anchor='start',
           dx=4)
    f.save('front-slots', 'The plus in the frame phi at o, with a square '
           'sitting at each of its five points: S1 at c3, S2 at c1, S3 at c5, '
           'S4 at c2 and S5 at c4')


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
    contact_polygons()
    octagon()
    support_proof()
    width_graph()
    shrink()
    arc_overlap()
    perimeter()
    gaps_figure()
    chart_moves()
    cartesian()
    caps()
    support_cases()
    estimates()
    sine_concave()
    quarter_turn()
    slots()


if __name__ == '__main__':
    main()

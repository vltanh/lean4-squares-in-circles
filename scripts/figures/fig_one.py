#!/usr/bin/env python3
"""Draw the figures of Chapter 4, one square, as SVG files in
docs/proof/figures/04-one/.

    python3 scripts/figures/fig_one.py

Every figure is computed from the geometry it illustrates, and the facts that
the captions state are checked by assertions. This module also holds the
label helpers shared by fig_one.py, fig_two.py and fig_four.py.
"""
import math
import re

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, square_corners,
                           in_open_square, u, shift, rad, sb)

R1 = math.sqrt(2) / 2
BLUE, ORANGE = COLORS[0], COLORS[1]


# ---------------------------------------------------------------- labels

def _char_width(ch):
    """A typical advance width of a serif character, in em."""
    if ch == ' ' or ch == ' ' or ch in ',.;:|':
        return 0.27
    if ch in '()[]':
        return 0.34
    if ch in '½¼':
        return 0.75
    if ch.isdigit():
        return 0.55
    if ch.isupper() or ch in 'ΓΔΣ':
        return 0.68
    if ch in '+−=<>≤≥√':
        return 0.58
    return 0.5


def text_width(markup, size):
    """The width in pixels of the label markup at the font size `size`,
    estimated from typical serif advance widths. A tspan counts at its own
    font size."""
    sizes, width = [size], 0.0
    for token in re.findall(r'<[^>]*>|&[a-z]+;|[^<&]', markup):
        if token.startswith('</'):
            sizes.pop()
        elif token.startswith('<'):
            m = re.search(r'font-size="([0-9.]+)"', token)
            sizes.append(float(m.group(1)) if m else sizes[-1])
        else:
            width += _char_width(token if len(token) == 1 else '<') * sizes[-1]
    return width


def isb(base, sub, after='', size=15):
    """sb() with the base and its subscript in italics, for mathematics
    inside upright text; the upright text `after` restores the baseline."""
    d = 0.3 * size
    out = (f'<tspan font-style="italic">{base}<tspan dy="{d:.1f}" '
           f'font-size="{0.68 * size:.1f}">{sub}</tspan></tspan>')
    if after:
        out += f'<tspan dy="{-d:.1f}">{after}</tspan>'
    return out


def label(f, pos, s, size=15, color=INK, italic=True, anchor='middle'):
    """A label anchored at its start, which every SVG renderer places the
    same way even when the markup has tspans; 'middle' and 'end' are
    emulated with the estimated width."""
    w = text_width(s, size) / f.s
    shiftx = {'start': 0.0, 'middle': w / 2, 'end': w}[anchor]
    f.text((pos[0] - shiftx, pos[1]), s, size=size, color=color,
           italic=italic, anchor='start')


def fit_radius(K, t):
    """In the frame of a unit square centred at the origin: the distance from
    the centre, in the direction t, to the boundary of the set of points o
    with (|x| + 1/2)^2 + (|y| + 1/2)^2 <= K, that is, of the positions of
    the disk centre for which the closed square lies in the closed disk of
    radius sqrt K about it (Lemma 3.4 (1)). The set is convex and
    star-shaped about the centre, and along the ray the condition is the
    quadratic rho^2 + (p + q) rho + 1/2 - K <= 0, p = |cos t|, q = |sin t|."""
    s = abs(math.cos(t)) + abs(math.sin(t))
    return (-s + math.sqrt(s * s + 4 * K - 2)) / 2


def fit_region(K, steps=720):
    """The boundary of that set, as a polygon."""
    return [shift((0, 0), u(2 * math.pi * k / steps),
                  fit_radius(K, 2 * math.pi * k / steps))
            for k in range(steps)]


# --------------------------------------------------------------- figures

def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def frame_point(c, t, x, y):
    """The point with coordinates (x, y) in the frame at c turned by t."""
    return shift(shift(c, u(t), x), u(t + math.pi / 2), y)


def farthest():
    """A square whose centre is not the disk centre: its vertices lie on the
    circle of radius R_1 about its centre, and the farthest one lies outside
    the circle of radius R_1 about o."""
    deg, x, y = 15, 0.3, 0.12      # the local coordinates of o are (x, y)
    t = rad(deg)
    o = (0.0, 0.0)
    c = frame_point(o, t, -x, -y)
    step = frame_point(c, t, x, 0)
    far = frame_point(c, t, -0.5, -0.5)
    corners = square_corners(c, deg)
    assert all(abs(math.dist(c, q) - R1) < 1e-12 for q in corners)
    assert abs(math.dist(o, far) ** 2 - phi(x, y)) < 1e-12
    assert max(math.dist(o, q) for q in corners) == math.dist(o, far) > R1
    f = Figure(-1.24, 0.78, -0.98, 0.78, 230)
    f.circle(c, R1, stroke=FAINT, width=1.2, dash='2 3')
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    f.circle(o, R1, stroke=INK, width=1.2, dash='6 4')
    top = u(rad(62))
    f.line(o, shift(o, top, R1), width=1)
    f.text(shift(shift(o, top, 0.5), u(rad(152)), 0.07), sb('R', '1'))
    f.line(c, step, width=2.2)
    f.line(step, o, width=2.2)
    f.text(shift(frame_point(c, t, x / 2, 0), u(t + math.pi / 2), -0.08),
           sb('a', 'S'), size=14)
    f.text(shift(frame_point(c, t, x, y / 2), u(t), 0.09), sb('b', 'S'),
           size=14)
    f.line(o, far, stroke=ORANGE, width=1.8)
    mid = ((o[0] + far[0]) / 2, (o[1] + far[1]) / 2)
    label(f, shift(mid, (0.1, -0.05)),
          '√φ(' + sb('a', 'S', ', ', 14) + sb('b', 'S', ')', 14), size=14,
          color=ORANGE, anchor='start')
    f.dot(far, r=4, fill=ORANGE)
    f.text(shift(far, (-0.06, 0.0)), 'farthest vertex', size=13,
           italic=False, color=ORANGE, anchor='end')
    f.dot(c, fill=BLUE)
    f.text(shift(c, (-0.04, 0.06)), sb('c', 'S'), color=BLUE, anchor='end')
    f.dot(o)
    f.text(shift(o, (-0.05, 0.05)), 'o', anchor='end')
    f.text(frame_point(c, t, -0.3, 0.27), 'S', size=17, color=BLUE)
    f.save('04-one/farthest', 'A unit square whose centre is not the disk centre '
           'o: its vertices lie on the dotted circle of radius R1 about its '
           'centre, and its farthest vertex from o lies outside the dashed '
           'circle of radius R1 about o')


def ab_plane():
    """The disk phi <= 1/2 of the (a, b)-plane meets the closed quadrant
    a, b >= 0 only at the origin, where it is tangent to a + b = 0."""
    lo, hi = -1.3, 0.85
    assert abs(phi(0, 0) - 0.5) < 1e-12
    f = Figure(lo, hi, lo, hi, 170)
    f.polygon([(0, 0), (hi - 0.05, 0), (hi - 0.05, hi - 0.05),
               (0, hi - 0.05)], fill=FILLS[1], stroke='none')
    f.circle((-0.5, -0.5), R1, stroke=BLUE, width=1.6, fill=FILLS[0])
    f.line((0.8, -0.8), (-0.8, 0.8), width=1.2, dash='6 4')
    f.line((lo + 0.05, 0), (hi - 0.02, 0), width=1, arrow=True)
    f.line((0, lo + 0.05), (0, hi - 0.02), width=1, arrow=True)
    f.text((hi - 0.03, -0.07), 'a', anchor='end')
    f.text((-0.07, hi - 0.05), 'b', anchor='end')
    f.dot((0, 0), r=4.2)
    f.text((0.1, 0.08), '(0, 0)', size=14, italic=False, anchor='start')
    f.dot((-0.5, -0.5), fill=BLUE)
    f.text((-0.46, -0.58), '(−½, −½)', size=13, italic=False, color=BLUE,
           anchor='start')
    f.text((-0.62, -0.28), 'φ ≤ ½', size=16, color=BLUE)
    f.text((0.44, 0.46), 'a, b ≥ 0', size=15, color=ORANGE)
    f.text((-0.66, 0.74), 'a + b = 0', size=14, anchor='start')
    f.save('04-one/ab-plane', 'The (a, b)-plane: the disk where phi is at most '
           'one half, centred at (-1/2, -1/2), lies on one side of the line a '
           'plus b equals 0 and touches it at the origin, the only point it '
           'shares with the quadrant where a and b are at least 0')


def vertex_disks():
    """In the frame of S: the closed square lies in the closed disk of radius
    R_1 about o exactly when o lies within R_1 of all four vertices, and the
    closed disks of radius R_1 about the vertices meet only at c_S."""
    verts = square_corners((0, 0))
    lower, upper = verts[0], verts[2]          # two opposite vertices
    assert abs(math.dist(lower, upper) - 2 * R1) < 1e-12
    assert all(abs(math.hypot(*v) - R1) < 1e-12 for v in verts)
    # A grid check: no point but c_S is within R_1 of all four vertices.
    for i in range(-80, 81):
        for j in range(-80, 81):
            p = (i / 80, j / 80)
            if (i, j) != (0, 0):
                assert max(math.dist(p, v) for v in verts) > R1
    f = Figure(-1.25, 1.25, -1.25, 1.25, 165)
    for v in (lower, upper):
        f.circle(v, R1, stroke=BLUE, width=1.4, fill=FILLS[0])
    for v in (verts[1], verts[3]):
        f.circle(v, R1, stroke=INK, width=1.1, dash='5 4')
    for v in (lower, upper):
        f.circle(v, R1, stroke=BLUE, width=1.4)
    f.square((0, 0), stroke=INK, width=2)
    f.line(lower, upper, width=1.1, dash='2 3')
    f.line(upper, shift(upper, (0, R1)), width=1.1)
    f.text(shift(upper, (0.05, R1 / 2)), sb('R', '1'), anchor='start')
    for v in verts:
        f.dot(v, r=3.6)
    f.dot((0, 0), r=4.4)
    # All four circles pass through c_S, tangent to the diagonals there: the
    # label goes in the gap along the first axis.
    f.text((0.1, 0.0), sb('c', 'S'), anchor='start')
    f.text((-0.34, 0.27), 'S', size=17)
    f.save('04-one/vertex-disks', 'A unit square S in its own frame with the '
           'circles of radius R1 about its four vertices; the shaded disks '
           'about two opposite vertices touch only at the centre c_S, which '
           'the two dashed circles about the other vertices also pass '
           'through')


def congruent():
    """Left, the model Q(0, 0); right, a packing at radius R_1: the model
    turned by the phase of a chart about the disk centre."""
    deg = 25
    t = rad(deg)
    right = 2.55
    o = (right, 0.0)
    f = Figure(-0.95, right + 0.95, -0.92, 1.0, 145)
    # The model.
    f.circle((0, 0), R1, stroke=INK, width=1.2, dash='6 4')
    f.square((0, 0), fill=FILLS[0], stroke=BLUE)
    f.line((-0.9, 0), (0.92, 0), width=1, arrow=True)
    f.line((0, -0.88), (0, 0.92), width=1, arrow=True)
    for q in square_corners((0, 0)):
        f.dot(q, r=2.8)
    f.dot((0, 0))
    f.text((0.05, -0.08), '0', anchor='start', italic=False)
    f.text((-0.45, 0.88), 'Q(0, 0)', size=15, color=BLUE)
    # The packing.
    f.line(shift(o, (-0.9, 0)), shift(o, (0.92, 0)), stroke=FAINT, width=1)
    f.circle(o, R1, stroke=INK, width=1.2, dash='6 4')
    f.square(o, deg, fill=FILLS[0], stroke=BLUE)
    f.line(o, shift(o, (0.92, 0)), stroke=FAINT, width=1)
    f.line(o, shift(o, u(t), 0.95), width=1, arrow=True)
    f.line(o, shift(o, u(t + math.pi / 2), 0.9), width=1, arrow=True)
    corners = square_corners(o, deg)
    assert all(abs(math.dist(o, q) - R1) < 1e-12 for q in corners)
    for q in corners:
        f.dot(q, r=2.8)
    f.arc(o, 0.3, 0, t, INK, width=1.2)
    f.text(shift(o, u(t / 2), 0.4), sb('θ', 'S', size=14), size=14)
    f.text(shift(o, u(t), 1.0), sb('θ', 'S', size=14), size=14,
           anchor='start')
    f.dot(o)
    f.text(shift(o, (-0.05, -0.08)), 'o', anchor='end')
    f.text(shift(o, u(t + rad(135)), 0.34), 'S', size=17, color=BLUE)
    f.line((0.95, -0.62), (1.6, -0.62), width=1.4, arrow=True)
    label(f, (1.27, -0.76), 'turn by ' + isb('θ', 'S', size=13), size=13,
          italic=False)
    f.save('04-one/congruent', 'Left: the model Q(0, 0), the unit square '
           'centred at the origin. Right: a unit square S centred at the disk '
           'centre o, with the axes of the frame at o turned by the phase '
           'theta S along its sides; the frame carries the model onto S')


def too_small():
    """A unit square centred at o does not fit in a disk of radius R < R_1:
    its four vertices are at distance R_1 from o."""
    deg, R = 15, 0.58
    corners = square_corners((0, 0), deg)
    assert all(abs(math.hypot(*q) - R1) < 1e-12 for q in corners)
    assert not in_open_square(u(0.0), (0, 0), deg)
    f = Figure(-0.84, 0.84, -0.84, 0.84, 230)
    f.circle((0, 0), R1, stroke=INK, width=1.2, dash='6 4')
    f.circle((0, 0), R, stroke=ORANGE, width=1.8, fill=FILLS[1])
    f.square((0, 0), deg, fill=FILLS[0], stroke=BLUE, opacity=0.8)
    f.circle((0, 0), R, stroke=ORANGE, width=1.8)
    for q in corners:
        f.dot(q, r=4, fill=ORANGE)
    t = rad(-58)
    f.line((0, 0), shift((0, 0), u(t), R), stroke=ORANGE, width=1.4)
    f.text(shift(shift((0, 0), u(t), 0.33), u(t + math.pi / 2), -0.07), 'R',
           color=ORANGE)
    v = corners[2]
    f.line((0, 0), v, width=1.2)
    tv = math.atan2(v[1], v[0])
    f.text(shift(shift((0, 0), u(tv), 0.42), u(tv + math.pi / 2), 0.08),
           sb('R', '1'))
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text(shift((0, 0), u(rad(200)), 0.3), 'S', size=17, color=BLUE)
    f.save('04-one/too-small', 'A unit square centred at o and a smaller '
           'concentric disk of radius R less than R1: the four vertices of '
           'the square lie on the dashed circle of radius R1, outside the '
           'smaller disk')


def main():
    farthest()
    ab_plane()
    vertex_disks()
    congruent()
    too_small()


if __name__ == '__main__':
    main()

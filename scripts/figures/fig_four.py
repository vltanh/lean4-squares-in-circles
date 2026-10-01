#!/usr/bin/env python3
"""Draw the figures of Chapter 7 (four squares) in
docs/proof/figures/07-four/.

    python3 scripts/figures/fig_four.py

Every arc is found by sampling the circle and testing membership in the open
squares, as in proof_figures.py, so each picture is computed from the same
geometry as the proofs.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, pair, clip_square)
from fig_one import label, isb, fit_region

HALF = math.pi / 2
R4 = math.sqrt(2)
BLUE, ORANGE = COLORS[0], COLORS[1]


def save(f, name, title):
    """Save a figure of this chapter, in its directory."""
    assert name.startswith('07-four/'), name
    f.save(name, title)


def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def cap_runs(a, b, r, o=(0.0, 0.0)):
    """The arcs of the circle of radius r about o inside the open unit
    square centred at o + (a, b), in chart coordinates."""
    c = shift(o, (a, b))
    return arcs_in(lambda p: in_open_square(shift(p, o), c), r)


def right_angle(f, o, t, size=0.07, width=1):
    """A right-angle mark at o between the directions t and t + pi/2."""
    p1 = shift(o, u(t), size)
    p2 = shift(p1, u(t + HALF), size)
    p3 = shift(o, u(t + HALF), size)
    f.line(p1, p2, width=width)
    f.line(p2, p3, width=width)


def construction():
    """Proposition 7.2: any two centres of the block differ by 1 in a
    coordinate, and the outer corners (+-1, +-1) lie on the circle of radius
    R_4 = sqrt 2, since 1 + 1 = 2."""
    centres = [(0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)]
    outer = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
    assert all(abs(math.hypot(*q) - R4) < 1e-12 for q in outer)
    for i, (x, y) in enumerate(centres):
        assert abs((abs(x) + 0.5) ** 2 + (abs(y) + 0.5) ** 2 - 2) < 1e-12
        for p in centres[i + 1:]:
            assert max(abs(x - p[0]), abs(y - p[1])) >= 1
    m = R4 + 0.16
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R4, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(centres):
        f.square(c, fill=FILLS[k], stroke=COLORS[k])
    f.line((-m + 0.03, 0), (m - 0.03, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, -m + 0.03), (0, m - 0.03), stroke=FAINT, width=1, arrow=True)
    f.text((m - 0.05, -0.1), 'x', anchor='end', color=FAINT)
    f.text((-0.07, m - 0.07), 'y', anchor='end', color=FAINT)
    f.line((0, 0), (1, 0), width=2.4)
    f.line((1, 0), (1, 1), width=2.4)
    f.line((0, 0), (1, 1), width=1.4)
    f.text((0.5, -0.11), '1', italic=False)
    f.text((1.07, 0.5), '1', italic=False, anchor='start')
    f.text((0.3, 0.46), sb('R', '4'))
    for q in outer:
        f.dot(q, r=3.8)
    for k, c in enumerate(centres):
        f.dot(c, fill=COLORS[k])
        spot = shift(c, (0.06, -0.1)) if k == 0 else shift(c, (0, -0.12))
        label(f, spot, sb('c', str(k + 1)), color=COLORS[k],
              anchor='start' if k == 0 else 'middle')
    f.dot((0, 0))
    f.text((-0.06, -0.1), 'o', anchor='end')
    save(f, '07-four/construction', 'The 2 by 2 block of the squares centred '
         'at c1 = (1/2, 1/2), c2 = (-1/2, 1/2), c3 = (-1/2, -1/2) and '
         'c4 = (1/2, -1/2), inside the dashed circle of radius root 2 about o; '
         'the right triangle with legs 1 and 1 joins o to the corner (1, 1), '
         'which lies on the circle like the other three outer corners')


def diamond_frame():
    """Lemma 7.4 in the frame of S: the positions of o for which S fits in
    the closed disk of radius R_4 about o lie in the square |x| + |y| <= 1,
    and reach its boundary only at the four vertices of S."""
    K = 2.0
    region = fit_region(K)
    steps = len(region)
    for k, (x, y) in enumerate(region):
        assert abs(phi(abs(x), abs(y)) - K) < 1e-9
        assert abs(x) + abs(y) <= 1 + 1e-12
        on_edge = abs(abs(x) + abs(y) - 1) < 1e-9
        assert on_edge == (k % (steps // 4) == steps // 8)
    verts = square_corners((0, 0))
    assert all(abs(phi(abs(x), abs(y)) - K) < 1e-12 for x, y in verts)
    f = Figure(-1.16, 1.16, -1.16, 1.16, 190)
    f.line((-1.14, 0), (1.14, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, -1.14), (0, 1.14), stroke=FAINT, width=1, arrow=True)
    f.polygon([(1, 0), (0, 1), (-1, 0), (0, -1)], fill=FILLS[1],
              stroke=ORANGE, width=2)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    f.square((0, 0), stroke=INK, width=1.8)
    for v in verts:
        f.dot(v, r=4.2)
    f.dot((0, 0))
    f.text((1.12, -0.09), 'x', anchor='end', color=FAINT)
    f.text((-0.08, 1.1), 'y', anchor='end', color=FAINT)
    f.text((-0.05, -0.08), sb('c', 'S'), anchor='end')
    f.text((-0.3, 0.3), 'S', size=17)
    f.text((0.66, 0.66), '|x| + |y| = 1', size=14, color=ORANGE,
           anchor='start')
    save(f, '07-four/diamond-frame', 'A unit square S in its own frame, the '
         'blue region of the points o for which S fits in the closed disk of '
         'radius root 2 about o, and the orange square |x| + |y| at most 1 '
         'standing on a vertex, which contains the region and touches it only '
         'at the four vertices of S')


def exterior_arc():
    """Lemma 7.5: a square with a + b < 1 holds more than a quarter of the
    circle of radius 1/2, since the quarter from A - pi/2 to A lies in its
    cap; at (1/2, 1/2) the cap is exactly the quarter from 0 to pi/2."""
    r = 0.5
    dx = 2.15
    f = Figure(-0.66, dx + 1.12, -0.64, 1.22, 170)
    # Left: a = 0.72, b = 0.1, inside the disk phi <= 2 and off the edge.
    a, b = 0.72, 0.1
    assert phi(a, b) <= 2 and a + b < 1
    A = math.acos((a - 0.5) / r)
    V = math.asin((0.5 - b) / r)
    (t0, t1), = cap_runs(a, b, r)
    assert abs(t0 - (-V + 2 * math.pi)) < 2e-3 or abs(t0 + V) < 2e-3
    assert V > HALF - A
    f.line((-0.64, 0), (1.3, 0), stroke=FAINT, width=1)
    f.line((a - 0.5, -0.62), (a - 0.5, 0.78), width=1, dash='4 4')
    f.line((-0.64, b - 0.5), (1.3, b - 0.5), width=1, dash='4 4')
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.dot((a, b), fill=BLUE)
    label(f, (a + 0.04, b + 0.07), pair(('a', 'S'), ('b', 'S'), 13), size=13,
          color=BLUE, anchor='start')
    f.circle((0, 0), r)
    f.arc((0, 0), r, t0, t1, ORANGE, width=5)
    for t in (A, A - HALF):
        f.line((0, 0), shift((0, 0), u(t), r), width=1.1)
    right_angle(f, (0, 0), A - HALF)
    f.dot(shift((0, 0), u(-V), r), fill=INK)
    f.dot(shift((0, 0), u(A), r), fill=INK)
    label(f, shift(shift((0, 0), u(A), r + 0.07), (-0.02, 0.0)),
          sb('A', 'S', size=13), size=13, anchor='end')
    label(f, shift(shift((0, 0), u(-V), r), (-0.03, -0.07)),
          '−' + sb('V', 'S', size=13), size=13, anchor='end')
    label(f, shift(shift((0, 0), u(A - HALF), 0.2), u(A - math.pi), 0.1),
          sb('A', 'S', ' − π/2', 13), size=13, anchor='end')
    f.text((a - 0.5 + 0.03, 0.74), 'near edge', size=12, italic=False,
           anchor='start')
    f.text((1.3, b - 0.5 - 0.07), 'lower edge', size=12, italic=False,
           anchor='end')
    f.dot((0, 0))
    f.text((-0.04, 0.06), 'o', anchor='end')
    label(f, (0.33, 1.08), isb('a', 'S', ' + ', 14) + isb('b', 'S', ' &lt; 1',
                                                           14),
          size=14, italic=False)
    # Right: a = b = 1/2, the tight case: o is a vertex.
    o2 = (dx, 0.0)
    f.line(shift(o2, (-0.64, 0)), shift(o2, (1.1, 0)), stroke=FAINT, width=1)
    f.square(shift(o2, (0.5, 0.5)), fill=FILLS[0], stroke=BLUE)
    f.dot(shift(o2, (0.5, 0.5)), fill=BLUE)
    f.text(shift(o2, (0.54, 0.57)), '(½, ½)', anchor='start', size=13,
           color=BLUE, italic=False)
    f.circle(o2, r)
    (s0, s1), = cap_runs(0.5, 0.5, r, o2)
    assert abs((s1 - s0) - HALF) < 2e-3
    f.arc(o2, r, s0, s1, ORANGE, width=5)
    right_angle(f, o2, 0)
    f.dot(o2)
    f.text(shift(o2, (-0.04, -0.07)), 'o', anchor='end')
    label(f, shift(o2, (0.25, 1.08)), isb('a', 'S', ' = ', 14) +
          isb('b', 'S', ' = ½', 14), size=14, italic=False)
    save(f, '07-four/exterior-arc', 'Left: an exterior square in its chart with '
         'a plus b less than 1; its cap on the circle of radius 1/2 runs from '
         'minus V to A and contains the quarter circle from A minus pi/2 to A. '
         'Right: the square with a = b = 1/2, a vertex at o, holds exactly '
         'the quarter from 0 to pi/2')


def cap_half_width(a, b):
    """The half-width of the cap of Lemma 3.24 (2) on the circle of radius
    1/2, for an exterior square with b <= 1/2 and a < 1."""
    A = math.acos(2 * a - 1)
    V = math.asin(1 - 2 * b)
    return (A + min(A, V)) / 2


def arc_region():
    """Lemma 7.5 in the (a, b)-plane, for exterior squares: the cap holds a
    quarter circle exactly when A_S >= pi/4 and A_S + V_S >= pi/2, that is,
    a <= (2 + sqrt 2)/4 and a + b <= 1; the part of the disk phi <= 2 with
    a >= 1/2 lies in this region, and (0.9, 0.05) lies in the diamond but
    not in it."""
    q = (2 + math.sqrt(2)) / 4                 # where A_S = pi/4
    edge = math.sqrt(1.75) - 0.5               # phi(edge, 0) = 2
    assert abs(math.acos(2 * q - 1) - math.pi / 4) < 1e-12
    # The region where the cap is at least a quarter circle, checked on a
    # grid against the formula, and the formula against sampled arcs.
    for i in range(1, 50):
        for j in range(0, 50):
            a, b = 0.5 + 0.5 * i / 50, 0.5 * j / 50
            inside = a <= q and a + b <= 1
            w = cap_half_width(a, b)
            if abs(a - q) > 1e-3 and abs(a + b - 1) > 1e-3:
                assert (w > math.pi / 4) == inside
            if phi(a, b) <= 2:
                assert inside
    for a, b in ((0.72, 0.1), (0.9, 0.05), (0.6, 0.3), (0.8, 0.15)):
        (t0, t1), = [run for run in cap_runs(a, b, 0.5)
                     if run[1] - run[0] < math.pi]
        assert abs((t1 - t0) / 2 - cap_half_width(a, b)) < 2e-3
    assert phi(0.9, 0.05) > 2 and 0.9 + 0.05 < 1 and 0.9 > q
    # The part of the disk phi <= 2 with a >= 1/2 and b >= 0: bounded by the
    # a-axis, the circle about (-1/2, -1/2) of radius sqrt 2 from (edge, 0)
    # to (1/2, 1/2), and the line a = 1/2.
    s0, s1 = math.atan2(0.5, edge + 0.5), math.pi / 4
    disk = [(0.5, 0.0)] + [shift((-0.5, -0.5), u(s0 + (s1 - s0) * k / 100),
                                 R4) for k in range(101)]
    assert abs(disk[1][1]) < 1e-12 and math.dist(disk[-1], (0.5, 0.5)) < 1e-12
    f = Figure(-0.08, 1.12, -0.14, 0.72, 400)
    f.polygon([(0.5, 0), (q, 0), (q, 1 - q), (0.5, 0.5)], fill=FILLS[1],
              stroke=ORANGE, width=1.6)
    f.polygon(disk, fill=FILLS[0], stroke=BLUE, width=1.4)
    f.line((0.38, 0.62), (1.0, 0.0), stroke=ORANGE, width=2)
    f.line((q, 0), (q, 0.66), width=1.2, dash='5 4')
    f.line((-0.06, 0), (1.1, 0), width=1, arrow=True)
    f.line((0, -0.06), (0, 0.7), width=1, arrow=True)
    f.text((1.1, -0.06), 'a', anchor='end')
    f.text((-0.05, 0.68), 'b', anchor='end')
    for x, s in ((0.5, '½'), (q, '(2 + √2)/4'), (1.0, '1')):
        f.line((x, -0.012), (x, 0.012), width=1)
        f.text((x, -0.05), s, size=13, italic=False)
    f.line((-0.012, 0.5), (0.012, 0.5), width=1)
    f.text((-0.03, 0.5), '½', size=13, italic=False, anchor='end')
    label(f, (q + 0.02, 0.64), sb('A', 'S', ' = π/4', 14), size=14,
          anchor='start')
    label(f, (0.42, 0.66), sb('A', 'S', ' + ', 14) + sb('V', 'S', ' = π/2',
                                                          14),
          size=14, color=ORANGE, anchor='start')
    f.text((0.6, 0.12), 'φ ≤ 2', size=15, color=BLUE)
    f.dot((0.5, 0.5), r=4)
    f.text((0.47, 0.5), '(½, ½)', size=13, italic=False, anchor='end')
    f.dot((0.9, 0.05), r=4)
    f.text((0.92, 0.11), '(0.9, 0.05)', size=13, italic=False,
           anchor='start')
    save(f, '07-four/arc-region', 'The (a, b)-plane right of a = 1/2: the '
         'orange quadrilateral where the cap of an exterior square on the '
         'circle of radius 1/2 is at least a quarter circle, bounded by the '
         'dashed line a = (2 + root 2)/4, where A = pi/4, and the line '
         'a + b = 1, where A + V = pi/2; the blue part of the disk where phi '
         'is at most 2 lies inside it and meets the line a + b = 1 only at '
         '(1/2, 1/2), while the point (0.9, 0.05) lies below the line '
         'a + b = 1 but right of the dashed line')


def less_than_quarter():
    """Without the disk constraint Lemma 7.5 fails: (0.9, 0.05) lies in the
    diamond but the cap is shorter than a quarter circle."""
    r = 0.5
    a, b = 0.9, 0.05
    assert a + b < 1 and phi(a, b) > 2
    A = math.acos((a - 0.5) / r)
    (t0, t1), = cap_runs(a, b, r)
    assert abs((t1 - t0) - 2 * A) < 2e-3 and 2 * A < HALF
    f = Figure(-0.64, 1.48, -0.64, 0.66, 230)
    f.line((-0.62, 0), (1.46, 0), stroke=FAINT, width=1)
    f.line((a - 0.5, -0.62), (a - 0.5, 0.62), width=1, dash='4 4')
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.dot((a, b), fill=BLUE)
    f.text((a + 0.04, b + 0.07), '(0.9, 0.05)', anchor='start', size=13,
           color=BLUE, italic=False)
    f.circle((0, 0), r)
    for t in (-math.pi / 4, math.pi / 4):
        f.line((0, 0), shift((0, 0), u(t), r + 0.05), stroke=FAINT,
               width=1.2, dash='4 3')
    f.text((0.36, 0.5), 'π/4', size=13, italic=False, anchor='end',
           color=FAINT)
    f.text((0.36, -0.5), '−π/4', size=13, italic=False, anchor='end',
           color=FAINT)
    f.arc((0, 0), r, t0, t1, ORANGE, width=5)
    for t in (A, -A):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    f.arc((0, 0), 0.16, 0, A, INK, width=1.2)
    f.text(shift((0, 0), u(A / 2), 0.24), sb('A', 'S', size=13), size=13)
    f.text((a - 0.5 + 0.03, 0.58), 'near edge', size=12, italic=False,
           anchor='start')
    f.dot((0, 0))
    f.text((-0.04, 0.06), 'o', anchor='end')
    save(f, '07-four/less-than-quarter', 'A square with a = 0.9 and b = 0.05, '
         'inside the diamond but outside the disk where phi is at most 2: its '
         'cap on the circle of radius 1/2 is shorter than a quarter circle')


def not_rigid():
    """The four outer squares of the plus: disjoint, all with (a, b) = (1, 0)
    on the edge of the diamond, and not the block."""
    centres = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    f = Figure(-1.62, 1.62, -1.62, 1.62, 120)
    f.circle((0, 0), R4, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(centres):
        f.square(c, fill=FILLS[k], stroke=COLORS[k])
        f.dot(c, fill=COLORS[k])
    f.circle((0, 0), 0.5)
    for k, c in enumerate(centres):
        assert not cap_runs(c[0], c[1], 0.5)
        f.dot((c[0] / 2, c[1] / 2), r=3.6, fill=COLORS[1])
    f.text((0.14, -0.28), sb('Γ', '1/2', size=14), size=14, anchor='start')
    f.text(shift((0, 0), u(rad(38)), R4 + 0.1), '√2', size=13, italic=False,
           anchor='start')
    f.dot((0, 0))
    f.text((-0.05, -0.08), 'o', anchor='end')
    save(f, '07-four/not-rigid', 'The four side-neighbours of a square centred '
         'at o, without the centre square: pairwise disjoint, each with '
         '(a, b) = (1, 0) on the edge of the diamond; the circle of radius 1/2 '
         'only touches them, and they stick out of the dashed circle of '
         'radius root 2')


def containing_quarter():
    """Lemma 7.6: if a, b <= 1/2 the square contains the open box
    (0, 1/2)^2, and with it the quarter circle between chart angles 0 and
    pi/2."""
    r = 0.5
    a, b = 0.3, 0.14
    f = Figure(-0.64, 0.98, -0.62, 0.8, 280)
    f.line((-0.62, 0), (0.96, 0), stroke=FAINT, width=1)
    f.line((0, -0.6), (0, 0.78), stroke=FAINT, width=1)
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.polygon([(0, 0), (0.5, 0), (0.5, 0.5), (0, 0.5)], fill=FILLS[1],
              stroke=ORANGE, width=1.2, dash='4 3')
    f.square((a, b), stroke=BLUE)
    f.circle((0, 0), r)
    for t0, t1 in cap_runs(a, b, r):
        f.arc((0, 0), r, t0, t1, ORANGE, width=1.8)
    assert all(in_open_square((r * math.cos(t), r * math.sin(t)), (a, b))
               for t in (HALF * k / 200 for k in range(1, 200)))
    f.arc((0, 0), r, 0, HALF, ORANGE, width=5)
    f.line((0, 0), shift((0, 0), u(math.pi / 4), 0.95), width=1, dash='3 3',
           arrow=True)
    f.arc((0, 0), 0.14, math.pi / 4, HALF, INK, width=1.1)
    f.text(shift((0, 0), u(3 * math.pi / 8), 0.23), 'π/4', size=12,
           italic=False)
    f.dot((a, b), fill=BLUE)
    label(f, (a, b - 0.075), pair(('a', 'S'), ('b', 'S'), 13), size=13,
          color=BLUE)
    f.text((0.53, 0.46), '(½, ½)', size=12, italic=False, anchor='start',
           color=ORANGE)
    f.dot((0.5, 0.5), r=2.4, fill=ORANGE)
    f.dot((0, 0))
    f.text((-0.04, -0.06), 'o', anchor='end')
    f.text((0.73, -0.3), 'S', size=17, color=BLUE)
    save(f, '07-four/containing-quarter', 'A square containing o, in its chart: '
         'it contains the box from (0, 0) to (1/2, 1/2), and with it the '
         'quarter of the circle of radius 1/2 between the chart angles 0 and '
         'pi/2, centred at the chart angle pi/4; thin, the rest of the circle '
         'inside the square')


def no_containing():
    """Step 3 of the proof of Proposition 7.3: if o is a vertex of T, a
    square that contains o in its interior overlaps T."""
    th = rad(20)
    e1, e2 = u(th), u(th + HALF)
    t_centre = shift(shift((0, 0), e1, 0.5), e2, 0.5)
    tdeg = math.degrees(th)
    s_deg = -12
    s_centre = (-0.12, -0.2)
    assert in_open_square((0, 0), s_centre, s_deg)
    lens = clip_square(square_corners(t_centre, tdeg), s_centre, s_deg)
    green = COLORS[2]
    top = max(y for x, y in square_corners(t_centre, tdeg))
    f = Figure(-0.78, 1.02, -0.86, top + 0.04, 250)
    f.square(t_centre, tdeg, fill=FILLS[0], stroke=BLUE)
    f.square(s_centre, s_deg, fill=FILLS[2], stroke=green, dash='5 4',
             opacity=0.7)
    f.polygon(lens, fill=FILLS[1], stroke=ORANGE, width=1.6)
    f.square(t_centre, tdeg, stroke=BLUE)
    f.dot((0, 0))
    f.text((-0.04, 0.06), 'o', anchor='end')
    f.text(shift(t_centre, (0.25, 0.3)), 'T', size=17, color=BLUE)
    f.text(shift(s_centre, (-0.3, -0.34)), 'S', size=17, color=green)
    save(f, '07-four/no-containing', 'A square T with a vertex at o, and a '
         'dashed square S that contains o in its interior: the two open '
         'squares overlap near o')


def quarter_grid():
    """Steps 4 and 5 of the proof of Proposition 7.3: the four quarter arcs
    are centred on a grid of quarter turns mu_0 + k pi/2, and in the frame
    mu_0 - pi/4 the squares sit at the centres of the block."""
    phi0 = rad(20)
    mu0 = phi0 + math.pi / 4
    slots = [(0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)]
    rot = lambda p: (p[0] * math.cos(phi0) - p[1] * math.sin(phi0),
                     p[0] * math.sin(phi0) + p[1] * math.cos(phi0))
    deg = math.degrees(phi0)
    r = 0.5
    f = Figure(-2.05, 2.05, -1.9, 1.95, 125)
    for k, c in enumerate(slots):
        f.square(rot(c), deg, fill=FILLS[k], stroke=COLORS[k])
    f.circle((0, 0), r)
    for k, c in enumerate(slots):
        (t0, t1), = arcs_in(lambda p: in_open_square(p, rot(c), deg), r)
        mid = (t0 + t1) / 2
        assert abs((mid - (mu0 + k * HALF) + math.pi) % (2 * math.pi)
                   - math.pi) < 2e-3
        f.arc((0, 0), r, t0, t1, COLORS[k], width=5)
    names = ['', ' + π/2', ' + π', ' + 3π/2']
    for k in range(4):
        t = mu0 + k * HALF
        f.line(shift((0, 0), u(t), r), shift((0, 0), u(t), 1.62), width=1,
               dash='3 3')
        f.dot(rot(slots[k]), fill=COLORS[k])
        anchor = 'start' if math.cos(t) > 0.3 else (
            'end' if math.cos(t) < -0.3 else 'middle')
        label(f, shift((0, 0), u(t), 1.72), sb('μ', '0', names[k], 14),
              size=14, anchor=anchor)
        subc = shift(rot(slots[k]), u(t + HALF), 0.15)
        f.text(subc, sb('c', str(k + 1), size=15), size=15, color=COLORS[k])
    f.line((0, 0), shift((0, 0), u(phi0), 1.5), width=1.6, arrow=True)
    f.line((0, 0), shift((0, 0), u(phi0 + HALF), 1.5), width=1.6,
           arrow=True)
    label(f, shift((0, 0), u(phi0), 1.6), sb('μ', '0', ' − π/4', 14),
          size=14, anchor='start')
    f.dot((0, 0))
    f.text((0.06, -0.1), 'o', anchor='start')
    save(f, '07-four/quarter-grid', 'Four squares with a common vertex at o. '
         'Their quarter arcs of the circle of radius 1/2 are centred at mu0 '
         'and its quarter turns; in the frame at o with first axis mu0 minus '
         'pi/4 the squares sit at the centres c1 to c4 of the block')


def main():
    construction()
    diamond_frame()
    exterior_arc()
    arc_region()
    less_than_quarter()
    not_rigid()
    containing_quarter()
    no_containing()
    quarter_grid()


if __name__ == '__main__':
    main()

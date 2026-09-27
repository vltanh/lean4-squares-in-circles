#!/usr/bin/env python3
"""Draw the new figures of Chapter 8 (five squares) in docs/proof/figures/.

    python3 scripts/fig_five.py

Arcs are found by sampling the circle and testing membership in the open
squares (or in the radial sweep), as in proof_figures.py, so each picture is
computed from the same geometry as the proofs.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, pair, clip, clip_square, convex_hull,
                           point_in_convex)

R_AUX = 5 / 6
HALF = math.pi / 2
SQ5 = math.sqrt(5)
G = (SQ5 - 1) / 2
# The corner of the 12-gon where 3a + b = 3 meets a + b = sqrt 5 - 1.
CX = (4 - SQ5) / 2
CY = SQ5 - 1 - CX


def save(f, name, title):
    """Save a figure of this chapter; only names with the prefix five-."""
    assert name.startswith('five-'), name
    f.save(name, title)


def asin_ext(w):
    """The arcsine extended by -pi/2 and pi/2 outside [-1, 1]."""
    return math.copysign(HALF, w) if abs(w) >= 1 else math.asin(w)


def crossing_angles(a, b, r=R_AUX):
    A = HALF - asin_ext((a - 0.5) / r)
    V = asin_ext((0.5 - b) / r)
    U = asin_ext((b + 0.5) / r)
    return A, V, U


def chart_runs(a, b, o=(0.0, 0.0), r=R_AUX):
    """The arcs of the circle of radius r about o inside the open unit square
    centred at o + (a, b), as angle intervals."""
    c = shift(o, (a, b))
    return arcs_in(lambda p: in_open_square(shift(p, o), c), r)


def twelve_gon_plane():
    """Definition 8.4: the 12-gon in the plane of the local coordinates of o,
    around the region where the square fits in the disk of radius
    sqrt(5/2), with the octagon dashed."""
    K = 2.5
    Rk = math.sqrt(K)
    orange, blue = COLORS[1], COLORS[0]
    quad = [(1, 0), (CX, CY), (CY, CX), (0, 1)]
    twelve = []
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        pts = [(sx * x, sy * y) for x, y in quad]
        if sx * sy < 0:
            pts.reverse()
        twelve += pts[:-1]
    twelve = convex_hull(twelve)
    assert len(twelve) == 12
    octagon = convex_hull([(sx * x, sy * y) for x, y in
                           ((1, 0), (0.75, 0.75), (0, 1))
                           for sx in (1, -1) for sy in (1, -1)])
    assert len(octagon) == 8
    t0 = math.asin(0.5 / Rk)
    region = []
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        arc = [(sx * (-0.5 + Rk * math.cos(t)), sy * (-0.5 + Rk * math.sin(t)))
               for t in (t0 + (HALF - 2 * t0) * k / 60 for k in range(61))]
        region += arc if sx * sy > 0 else arc[::-1]
    region = convex_hull(region)
    f = Figure(-1.3, 1.3, -1.3, 1.3, 200)
    f.line((-1.28, 0), (1.28, 0), stroke=FAINT, width=1)
    f.line((0, -1.28), (0, 1.28), stroke=FAINT, width=1)
    f.polygon(twelve, fill=FILLS[1], stroke=orange, width=2)
    f.polygon(region, fill=FILLS[0], stroke=blue, width=1.4)
    f.polygon(octagon, stroke=INK, width=1, dash='5 4')
    f.polygon(twelve, stroke=orange, width=2)
    f.square((0, 0), stroke=FAINT, width=1.2)
    f.text((-0.38, 0.38), 'S', size=16, color=FAINT)
    for q in ((1, 0), (0, 1), (-1, 0), (0, -1)):
        f.dot(q, r=3.6)
    for sx in (1, -1):
        for sy in (1, -1):
            f.dot((sx * G, sy * G), r=3.6)
    f.text((1.28, -0.07), sb('x', 'S', '(o)', 13), size=13, anchor='end',
           color=FAINT)
    f.text((0.04, 1.26), sb('y', 'S', '(o)', 13), size=13, anchor='start',
           color=FAINT)
    f.text((0.2, -0.6), 'φ ≤ 5/2', size=14, color=blue)
    f.text((0.98, 0.5), sb('P', '5', size=16), size=16, color=orange,
           anchor='start')
    f.text((0.84, 0.84), sb('P', '8', size=14), size=14, anchor='start')
    save(f, 'five-twelve-gon-plane', 'The positions of the disk centre o in '
         'the frame of a square S that keep S in the disk of radius root 5/2 '
         '(blue), inside the 12-gon P5 (orange), inside the dashed octagon; '
         'the dots are the points of tangency')


def chart_panel(f, o, a, b, color, title, arc_label, lines=True):
    """A square at (a, b) in its chart about o, the circle of radius 5/6, and
    the arc that it holds."""
    blue = COLORS[0]
    f.line(shift(o, (-0.92, 0)), shift(o, (1.5, 0)), stroke=FAINT, width=1)
    if lines:
        f.line(shift(o, (a - 0.5, -0.93)), shift(o, (a - 0.5, 1.2)), width=1,
               dash='4 4')
        f.line(shift(o, (-0.92, b - 0.5)), shift(o, (1.5, b - 0.5)), width=1,
               dash='4 4')
        f.line(shift(o, (-0.92, b + 0.5)), shift(o, (1.5, b + 0.5)), width=1,
               dash='4 4')
    f.square(shift(o, (a, b)), fill=FILLS[0], stroke=blue)
    f.dot(shift(o, (a, b)), fill=blue)
    f.circle(o, R_AUX)
    (t0, t1), = chart_runs(a, b, o)
    shift0 = math.remainder(t0, 2 * math.pi) - t0
    t0, t1 = t0 + shift0, t1 + shift0
    f.arc(o, R_AUX, t0, t1, color, width=5)
    for t in (t0, t1):
        f.line(o, shift(o, u(t), R_AUX), width=1)
    f.arc(o, 0.2, t0, t1, INK, width=1.1)
    f.text(shift(o, u((t0 + t1) / 2), 0.33), arc_label, size=13,
           italic=False)
    f.dot(o)
    f.text(shift(o, (-0.04, -0.08)), 'o', anchor='end')
    f.text(shift(o, (0.3, 1.3)), title, size=14, italic=False)
    return t0, t1


def third_side():
    """Why P5 needs its third side: at the corner (3/4, 3/4) of the octagon
    the arc on the circle of radius 5/6 is less than a fifth; at the corner
    of P5 it is just more."""
    dx = 2.55
    f = Figure(-0.95, dx + 1.52, -0.97, 1.42, 128)
    t0, t1 = chart_panel(f, (0, 0), 0.75, 0.75, COLORS[4],
                         'corner (¾, ¾) of ' + sb('P', '8', size=14),
                         '≈ 55°')
    assert 55 < math.degrees(t1 - t0) < 55.2 < 72
    s0, s1 = chart_panel(f, (dx, 0), CX, CY, COLORS[1],
                         'corner of ' + sb('P', '5', size=14),
                         '≈ 72.8°')
    assert 72 < 72.7 < math.degrees(s1 - s0) < 72.9
    save(f, 'five-third-side', 'Left: a square at the corner (3/4, 3/4) of '
         'the octagon holds only about 55 degrees of the circle of radius 5/6, '
         'less than a fifth. Right: at the corner of the 12-gon it holds about '
         '72.8 degrees, just more than a fifth')


def arcsine_region():
    """Lemma 8.7: its region in the (x, y)-plane, split into the three cases
    of the proof, below the level curve of the arcsine sum at pi/10."""
    q = 23 / 60
    s = 237 / 1000
    xc = (1 - s) / 2
    yc = s - xc
    orange, blue, green, purple = COLORS[1], COLORS[0], COLORS[2], COLORS[3]
    f = Figure(-0.1, 0.72, -0.6, 0.47, 540)
    region = [(0, -0.5), (0.5, -0.5), (xc, yc), (0, s)]
    case1 = [(0, 0), (s, 0), (0, s)]
    case2 = [(0, -0.5), (q, -0.5), (q, 1 - 3 * q), (xc, yc), (s, 0), (0, 0)]
    case3 = [(q, -0.5), (0.5, -0.5), (q, 1 - 3 * q)]
    for poly, k in ((case1, 2), (case2, 0), (case3, 3)):
        f.polygon(poly, fill=FILLS[k], stroke='none')
    f.polygon(region, stroke=INK, width=1.6)
    f.line((q, -0.5), (q, 1 - 3 * q), stroke=INK, width=1, dash='3 3')
    f.line((xc, yc), (0.5, s - 0.5), stroke=INK, width=1, dash='1 3')
    f.line((0, 0), (s, 0), stroke=INK, width=1, dash='3 3')
    # The level curve arcsin(6x/5) + arcsin(6y/5) = pi/10.
    level = []
    for k in range(101):
        x = 0.5 * k / 100
        y = R_AUX * math.sin(math.pi / 10 - math.asin(x / R_AUX))
        level.append((x, y))
    for k in range(100):
        f.line(level[k], level[k + 1], stroke=orange, width=1.8)
    worst = max(math.asin(1.2 * x) + math.asin(1.2 * y)
                for x in (0.5 * i / 400 for i in range(401))
                for y in (-0.5 + j / 400 for j in range(401))
                if x + y <= s and 3 * x + y <= 1)
    assert worst < 313 / 1000 < math.pi / 10
    # Axes, ticks and labels.
    f.line((-0.06, 0), (0.6, 0), width=1, arrow=True)
    f.line((0, -0.58), (0, 0.45), width=1, arrow=True)
    f.text((0.6, -0.03), 'x', anchor='end')
    f.text((-0.02, 0.44), 'y', anchor='end')
    for x, label in ((0.5, '½'), (q, '23/60')):
        f.line((x, -0.51), (x, -0.49), width=1)
        f.text((x, -0.535), label, size=12, italic=False)
    f.line((-0.01, -0.5), (0.01, -0.5), width=1)
    f.text((-0.02, -0.5), '−½', size=12, italic=False, anchor='end')
    f.line((-0.01, s), (0.01, s), width=1)
    f.text((-0.02, s), '237/1000', size=11, italic=False, anchor='end')
    f.text((0.06, 0.06), '(i)', size=14, italic=False, color=green)
    f.text((0.15, -0.3), '(ii)', size=14, italic=False, color=blue)
    f.text((0.425, -0.42), '(iii)', size=13, italic=False, color=purple)
    f.text((0.505, s - 0.5), 'x + y = 237/1000', size=12, italic=False,
           anchor='start')
    f.text((0.46, -0.35), '3x + y = 1', size=12, italic=False,
           anchor='start')
    f.text((0.03, 0.3), 'sum = π/10', size=12, italic=False, color=orange,
           anchor='start')
    save(f, 'five-arcsine-region', 'The region of the arcsine-sum lemma in the '
         'plane of x and y, cut by x + y at most 237/1000 and 3x + y at most '
         '1, split into the three cases of the proof; it lies below the curve '
         'where the arcsine sum equals pi/10')


def arc_cases():
    """Lemma 8.8: the arc of an exterior square on the circle of radius 5/6
    ends on the lower edge at -V, and on the near edge at A or on the upper
    edge at U, whichever comes first."""
    dx = 2.55
    f = Figure(-0.95, dx + 1.55, -0.97, 1.3, 128)
    blue, orange = COLORS[0], COLORS[1]
    for o, (a, b), name in (((0, 0), (0.8, 0.4), 'A'),
                            ((dx, 0), (1.0, 0.0), 'U')):
        A, V, U = crossing_angles(a, b)
        assert V < A
        assert (A <= U) == (name == 'A')
        f.line(shift(o, (-0.92, 0)), shift(o, (1.52, 0)), stroke=FAINT,
               width=1)
        for p0, p1 in (((a - 0.5, -0.93), (a - 0.5, 1.28)),
                       ((-0.92, b - 0.5), (1.52, b - 0.5)),
                       ((-0.92, b + 0.5), (1.52, b + 0.5))):
            f.line(shift(o, p0), shift(o, p1), width=1, dash='4 4')
        f.square(shift(o, (a, b)), fill=FILLS[0], stroke=blue)
        f.dot(shift(o, (a, b)), fill=blue)
        f.circle(o, R_AUX)
        (t0, t1), = chart_runs(a, b, o)
        shift0 = math.remainder(t0, 2 * math.pi) - t0
        t0, t1 = t0 + shift0, t1 + shift0
        assert abs(t0 + V) < 2e-3 and abs(t1 - min(A, U)) < 2e-3
        f.arc(o, R_AUX, t0, t1, orange, width=5)
        marks = [(-V, sb('−V', 'S', size=13), INK), (A, sb('A', 'S', size=13),
                 INK if name == 'A' else FAINT),
                 (-A, sb('−A', 'S', size=13), FAINT)]
        if U < HALF:
            marks.append((U, sb('U', 'S', size=13),
                          INK if name == 'U' else FAINT))
        for t, label, color in marks:
            p = shift(o, u(t), R_AUX)
            f.dot(p, r=3.4, fill=color)
            f.text(shift(o, u(t), R_AUX + 0.13), label, size=13, color=color,
                   anchor='end' if math.cos(t) < 0.75 else 'start')
        f.text(shift(o, (-0.9, b + 0.5 + 0.06)), 'upper edge', size=11,
               italic=False, anchor='start')
        f.text(shift(o, (-0.9, b - 0.5 - 0.07)), 'lower edge', size=11,
               italic=False, anchor='start')
        f.text(shift(o, (a - 0.5 + 0.03, 1.25)), 'near edge', size=11,
               italic=False, anchor='start')
        f.dot(o)
        f.text(shift(o, (-0.04, 0.07)), 'o', anchor='end')
        f.text(shift(o, (a + 0.05, b - 0.08)), f'({a:g}, {b:g})', size=12,
               italic=False, color=blue, anchor='start')
    save(f, 'five-arc-cases', 'Two exterior squares in their charts on the '
         'circle of radius 5/6. Left, the square at (0.8, 0.4): the arc runs '
         'from the lower edge at minus V to the near edge at A, length A + V. '
         'Right, the square at (1, 0): it runs from the lower edge at minus V '
         'to the upper edge at U, length U + V')


def sweep_positions():
    """Lemma 8.10 at three positions of a containing square: slid out to
    distance 1/root 2, its inscribed disk covers a fifth of the circle of
    radius 5/6, which therefore lies in the radial sweep."""
    orange, blue = COLORS[1], COLORS[0]
    offsets = [(0.06, 0.035), (0.3, 0.12), (0.44, 0.38)]
    dx = 2.45
    box = (-0.92, 1.45, -0.92, 1.42)
    f = Figure(box[0], 2 * dx + box[1], box[2], box[3], 88)
    for k, (a, b) in enumerate(offsets):
        o = (k * dx, 0.0)
        ell = math.hypot(a, b)
        assert ell ** 2 < 0.5 and max(a, b) < 0.5
        delta = math.atan2(b, a)
        m = 1 / (math.sqrt(2) * ell) - 1
        cstar = ((1 + m) * a, (1 + m) * b)
        corners = square_corners((a, b))
        hull = convex_hull(corners + [shift(p, (a, b), 40) for p in corners])
        panel = [(box[0], box[2]), (box[1], box[2]), (box[1], box[3]),
                 (box[0], box[3])]
        shown = hull
        for p, q in zip(panel, panel[1:] + panel[:1]):
            nx, ny = q[1] - p[1], p[0] - q[0]
            shown = clip(shown, nx, ny, nx * p[0] + ny * p[1])
        member = lambda p: point_in_convex(p, hull)
        (t0, t1), = [run for run in arcs_in(member, R_AUX)
                     if run[0] <= delta + 2 * math.pi <= run[1]
                     or run[0] <= delta <= run[1]]
        assert t1 - t0 > 2 * math.pi / 5
        for t in (delta - math.pi / 5 + j * (2 * math.pi / 5) / 50
                  for j in range(51)):
            p = (R_AUX * math.cos(t), R_AUX * math.sin(t))
            assert math.dist(p, cstar) < 0.5 and member(p)
        f.polygon([shift(o, p) for p in shown], fill=FILLS[1], stroke='none',
                  opacity=0.7)
        f.square(shift(o, (a, b)), fill=FILLS[0], stroke=blue)
        f.square(shift(o, cstar), stroke=orange, width=1.2, dash='4 3')
        f.circle(shift(o, cstar), 0.5, stroke=orange, width=1.4)
        f.circle(o, R_AUX)
        f.arc(o, R_AUX, delta - math.pi / 5, delta + math.pi / 5, orange,
              width=5)
        f.line(o, shift(o, u(delta), 1.35), width=1, dash='2 3', arrow=True)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.08)), 'o', anchor='end')
        f.dot(shift(o, (a, b)), r=2.6, fill=blue)
        f.dot(shift(o, cstar), r=2.6, fill=orange)
        f.text(shift(o, (-0.62, -0.72)), 'S', size=15, color=blue)
        f.text(shift(o, (0.3, 1.3)), pair(('a', 'S'), ('b', 'S'), 12) + ' = ('
               + f'{a:g}, {b:g})', size=12, italic=False, color=blue)
    save(f, 'five-sweep-positions', 'Three containing squares in their charts, '
         'with their radial sweeps shaded. Each slid copy, dashed, has its '
         'centre at distance 1 over root 2 from o, and its inscribed disk '
         'covers the arc of the circle of radius 5/6 of half-width pi/5 about '
         'the direction of the centre')


def budget():
    """Proposition 8.11. Left: four arcs of more than a fifth and one of a
    fifth overrun the circle. Right: in the plus the four outer squares leave
    gaps adding up to less than a fifth."""
    dx = 2.75
    f = Figure(-1.22, dx + 1.62, -1.62, 1.35, 118)
    # Left: the schematic overrun, with the lengths of the plus.
    w = 2 * math.asin(0.6)
    start = HALF
    for k in range(4):
        f.arc((0, 0), R_AUX, start + k * w, start + (k + 1) * w, COLORS[k],
              width=5)
    s5 = start + 4 * w
    f.arc((0, 0), R_AUX + 0.12, s5, s5 + 2 * math.pi / 5, COLORS[4], width=5)
    over = s5 + 2 * math.pi / 5 - (start + 2 * math.pi)
    assert over > 0
    f.arc((0, 0), R_AUX + 0.25, start, start + over, INK, width=2)
    f.circle((0, 0), R_AUX)
    f.text(shift((0, 0), u(start + over / 2), R_AUX + 0.38), 'overlap',
           size=12, italic=False, anchor='start')
    for k in range(4):
        f.text(shift((0, 0), u(start + (k + 0.5) * w), R_AUX - 0.22),
               '&gt; 72°', size=11, italic=False, color=COLORS[k])
    f.text(shift((0, 0), u(s5 + math.pi / 5), R_AUX + 0.33), '72°', size=11,
           italic=False, color=COLORS[4])
    f.dot((0, 0))
    f.text((0.04, -0.08), 'o', anchor='start')
    # Right: the plus on the circle of radius 5/6.
    o = (dx, 0.0)
    centres = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    f.square(o, fill=GREY, stroke=FAINT)
    for k, c in enumerate(centres):
        f.square(shift(o, c), fill=FILLS[k], stroke=COLORS[k])
    f.circle(o, R_AUX)
    runs = []
    for k, c in enumerate(centres):
        (t0, t1), = arcs_in(lambda p: in_open_square(shift(p, o),
                                                     shift(o, c)), R_AUX)
        runs.append((t0, t1))
        f.arc(o, R_AUX, t0, t1, COLORS[k], width=5)
    assert not arcs_in(lambda p: in_open_square(shift(p, o), o), R_AUX)
    gaps = 2 * math.pi - sum(t1 - t0 for t0, t1 in runs)
    assert gaps < 2 * math.pi / 5
    for k in range(4):
        mid = math.pi / 4 + k * HALF
        f.arc(o, R_AUX, mid - gaps / 8, mid + gaps / 8, INK, width=2)
    f.text(shift(o, u(math.pi / 4), R_AUX + 0.62), 'gaps: 4 × 16.3°',
           size=12, italic=False, anchor='start')
    f.dot(o)
    f.text(shift(o, (0.05, -0.08)), 'o', anchor='start')
    save(f, 'five-budget', 'Left: four arcs of more than a fifth of the circle '
         'and one of a fifth cannot be disjoint; laid end to end, the last '
         'overlaps the first. Right: in the plus the four outer squares hold '
         'about 73.7 degrees each, and the four gaps between them add up to '
         'about 65 degrees, less than a fifth')


def unit_contacts():
    """Proof of Proposition 8.6: a square with its centre at distance 1 from
    the centred square overlaps it unless it is a side-neighbour."""
    th = rad(20)
    tdeg = math.degrees(th)
    dx = 3.45
    f = Figure(-1.7, dx + 1.72, -1.6, 1.72, 96)
    # Left: a square at distance 1 in a direction off the axes overlaps.
    blue, orange, green = COLORS[0], COLORS[1], COLORS[2]
    d = th + rad(45)
    c = shift((0, 0), u(d), 1.0)
    ddeg = math.degrees(d)
    lens = clip_square(square_corners((0, 0), tdeg), c, ddeg)
    assert len(lens) >= 3
    f.circle((0, 0), 1.0, stroke=INK, width=1.1, dash='5 4')
    f.square((0, 0), tdeg, fill=GREY, stroke=FAINT)
    f.square(c, ddeg, fill=FILLS[2], stroke=green, opacity=0.8)
    f.polygon(lens, fill=FILLS[1], stroke=orange, width=1.6)
    f.line((0, 0), c, width=1.1)
    f.text(shift(shift((0, 0), u(d), 0.82), u(d + HALF), 0.1), '1', size=13,
           italic=False)
    f.dot((0, 0))
    f.text((0.04, -0.1), 'o', anchor='start')
    f.dot(c, fill=green)
    f.text(shift((0, 0), u(th + rad(225)), 0.42), sb('S', 'k', size=15),
           size=15, color=INK)
    # Right: the plus, turned by 20 degrees; its centres lie on the circle.
    o = (dx, 0.0)
    rot = lambda p: (p[0] * math.cos(th) - p[1] * math.sin(th),
                     p[0] * math.sin(th) + p[1] * math.cos(th))
    f.circle(o, 1.0, stroke=INK, width=1.1, dash='5 4')
    f.square(o, tdeg, fill=GREY, stroke=FAINT)
    for k, p in enumerate(((1, 0), (0, 1), (-1, 0), (0, -1))):
        f.square(shift(o, rot(p)), tdeg, fill=FILLS[k], stroke=COLORS[k])
        f.line(o, shift(o, rot(p)), width=1)
        f.dot(shift(o, rot(p)), fill=COLORS[k])
    f.dot(o)
    f.text(shift(o, (0.05, -0.1)), 'o', anchor='start')
    f.text(shift(o, u(th + rad(225)), 0.42), sb('S', 'k', size=15),
           size=15, color=INK)
    save(f, 'five-unit-contacts', 'Around a square centred at o, with the '
         'dashed unit circle about o. Left: a square whose centre is at '
         'distance 1 from o but not on an axis of the centred square overlaps '
         'it. Right: the only squares at distance 1 that do not overlap it are '
         'its four side-neighbours: the plus')


def main():
    twelve_gon_plane()
    third_side()
    arcsine_region()
    arc_cases()
    sweep_positions()
    budget()
    unit_contacts()


if __name__ == '__main__':
    main()

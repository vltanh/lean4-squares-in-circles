#!/usr/bin/env python3
"""Draw the figures of Chapter 8 (five squares) in docs/proof/figures/08-five/,
except the few older ones that proof_figures.py draws.

    python3 scripts/figures/fig_five.py

Arcs are found by sampling the circle and testing membership in the open
squares (or in the radial sweep), as in proof_figures.py, so each picture is
computed from the same geometry as the proofs; level curves are traced on a
grid, and graphs are sampled from their functions.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, subscript, clip, clip_square, convex_hull,
                           point_in_convex)
from fig_front import it, sbn
from fig_appa import Plot, x_axis, y_axis
from fig_three import arc, eqn, label, pair_s, up

R_AUX = 5 / 6
HALF = math.pi / 2
SQ5 = math.sqrt(5)
R5 = math.sqrt(2.5)
G = (SQ5 - 1) / 2
# The corner of the 12-gon where 3a + b = 3 meets a + b = sqrt 5 - 1.
CX = (4 - SQ5) / 2
CY = SQ5 - 1 - CX
CENTRES = [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)]
BLUE, ORANGE, GREEN, PURPLE, RED = COLORS[:5]


def save(f, name, title):
    """Save a figure of this chapter, in its directory."""
    assert name.startswith('08-five/'), name
    f.save(name, title)


def asin_ext(w):
    """The arcsine extended by -pi/2 and pi/2 outside [-1, 1]."""
    return math.copysign(HALF, w) if abs(w) >= 1 else math.asin(w)


def crossing_angles(a, b, r=R_AUX):
    A = HALF - asin_ext((a - 0.5) / r)
    V = asin_ext((0.5 - b) / r)
    U = asin_ext((b + 0.5) / r)
    return A, V, U


def arc_length(a, b):
    """The length min(A, U) + min(A, V) of the arc of Lemma 3.24 (1) on the
    circle of radius 5/6."""
    A, V, U = crossing_angles(a, b)
    return min(A, U) + min(A, V)


def chart_runs(a, b, o=(0.0, 0.0), r=R_AUX):
    """The arcs of the circle of radius r about o inside the open unit square
    centred at o + (a, b), as angle intervals."""
    c = shift(o, (a, b))
    return arcs_in(lambda p: in_open_square(shift(p, o), c), r)


def level_curves(fn, box, level, n=160):
    """The curves fn = level in the box (x0, x1, y0, y1), traced by marching
    squares on an n by n grid and joined into polylines."""
    x0, x1, y0, y1 = box
    xs = [x0 + (x1 - x0) * i / n for i in range(n + 1)]
    ys = [y0 + (y1 - y0) * j / n for j in range(n + 1)]
    val = [[fn(x, y) - level for y in ys] for x in xs]
    segs = []
    for i in range(n):
        for j in range(n):
            corners = [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)]
            cuts = []
            for k in range(4):
                (p, q), (r, s) = corners[k], corners[(k + 1) % 4]
                v, w = val[p][q], val[r][s]
                if (v < 0) != (w < 0):
                    t = v / (v - w)
                    cuts.append((round(xs[p] + t * (xs[r] - xs[p]), 12),
                                 round(ys[q] + t * (ys[s] - ys[q]), 12)))
            if len(cuts) == 2:
                segs.append(tuple(cuts))
            elif len(cuts) == 4:
                segs += [(cuts[0], cuts[1]), (cuts[2], cuts[3])]
    ends = {}
    for k, (p, q) in enumerate(segs):
        ends.setdefault(p, []).append(k)
        ends.setdefault(q, []).append(k)
    used, lines = set(), []
    for k in range(len(segs)):
        if k in used:
            continue
        used.add(k)
        line = list(segs[k])
        for forward in (True, False):
            while True:
                tip = line[-1] if forward else line[0]
                nxt = [m for m in ends[tip] if m not in used]
                if not nxt:
                    break
                used.add(nxt[0])
                p, q = segs[nxt[0]]
                other = q if p == tip else p
                if forward:
                    line.append(other)
                else:
                    line.insert(0, other)
        lines.append(line)
    return lines


def polyline(f, pts, stroke=INK, width=1.4, dash=None):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')


# 8.1 Construction.

def construction():
    """Proposition 8.2: the plus in the closed disk of radius R5, with its
    centres; the eight outer corners lie on the circle."""
    m = R5 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R5, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(CENTRES):
        fill, stroke = (GREY, FAINT) if k == 0 else (FILLS[k], COLORS[k])
        f.square(c, fill=fill, stroke=stroke)
    on_circle = [q for c in CENTRES for q in square_corners(c)
                 if abs(q[0] ** 2 + q[1] ** 2 - 2.5) < 1e-12]
    assert len(set(on_circle)) == 8
    assert all(q[0] ** 2 + q[1] ** 2 <= 2.5 + 1e-12
               for c in CENTRES for q in square_corners(c))
    for q in set(on_circle):
        f.dot(q, r=4)
    for k, c in enumerate(CENTRES[1:], start=1):
        f.dot(c, r=3, fill=COLORS[k])
        subscript(f, shift(c, (0.0, -0.12)), 'c', str(k + 1),
                  color=COLORS[k])
    f.text((1.43, 0.63), '(3/2, ½)', size=13, italic=False, anchor='end')
    f.text((0.6, 1.58), '(½, 3/2)', size=13, italic=False, anchor='start')
    f.dot((0, 0))
    label(f, (0.0, -0.13), sbn('c', '1', ' = ', 15) + 'o', 15, 'middle')
    t = rad(-35)
    f.line((0, 0), shift((0, 0), u(t), R5), width=1, dash='3 3')
    subscript(f, shift(shift((0, 0), u(t), 0.8 * R5), u(t + HALF), 0.1), 'R',
              '5', size=16)
    save(f, '08-five/construction', 'The plus in the circle of radius root 5/2 '
         'about o, with the centres c1 to c5 of its squares; the eight outer '
         'corners, among them (3/2, 1/2) and (1/2, 3/2), lie on the circle')


# 8.2 The 12-gon.

def twelve_gon_plane():
    """Definition 8.4: the 12-gon in the plane of the local coordinates of o,
    around the region where the square fits in the disk of radius
    sqrt(5/2), with the octagon of its first two sides dashed."""
    K = 2.5
    Rk = math.sqrt(K)
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
        arc_pts = [(sx * (-0.5 + Rk * math.cos(t)),
                    sy * (-0.5 + Rk * math.sin(t)))
                   for t in (t0 + (HALF - 2 * t0) * k / 60 for k in range(61))]
        region += arc_pts if sx * sy > 0 else arc_pts[::-1]
    region = convex_hull(region)
    touch = [(1, 0), (0, 1), (-1, 0), (0, -1)] + [
        (sx * G, sy * G) for sx in (1, -1) for sy in (1, -1)]
    f = Figure(-1.3, 1.3, -1.3, 1.3, 200)
    f.line((-1.28, 0), (1.28, 0), stroke=FAINT, width=1)
    f.line((0, -1.28), (0, 1.28), stroke=FAINT, width=1)
    f.polygon(twelve, fill=FILLS[1], stroke=ORANGE, width=2)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.4)
    f.polygon(octagon, stroke=INK, width=1, dash='5 4')
    f.polygon(twelve, stroke=ORANGE, width=2)
    f.square((0, 0), stroke=FAINT, width=1.2)
    f.text((-0.38, 0.38), 'S', size=16, color=FAINT)
    for q in touch:
        f.dot(q, r=3.6)
    label(f, (1.28, -0.07), sbn('x', 'S', '(o)', 13), 13, 'end', color=FAINT)
    label(f, (0.04, 1.26), sbn('y', 'S', '(o)', 13), 13, color=FAINT)
    f.text((0.2, -0.6), 'φ ≤ 5/2', size=14, color=BLUE)
    f.text((0.98, 0.5), sb('P', '5', size=16), size=16, color=ORANGE,
           anchor='start')
    save(f, '08-five/twelve-gon-plane', 'The positions of the disk centre o in '
         'the frame of a square S that keep S in the disk of radius root 5/2 '
         '(blue), inside the 12-gon P5 (orange), inside the dashed octagon of '
         'its first two sides; the dots are the eight points of tangency')


# 8.3 Exterior squares.

def chart_panel(f, o, a, b, color, title, value):
    """A square at (a, b) in its chart about o, the circle of radius 5/6, the
    lines of its near, lower and upper edges, and the arc that it holds."""
    f.line(shift(o, (-0.92, 0)), shift(o, (1.5, 0)), stroke=FAINT, width=1)
    f.line(shift(o, (a - 0.5, -0.93)), shift(o, (a - 0.5, 1.2)), width=1,
           dash='4 4')
    f.line(shift(o, (-0.92, b - 0.5)), shift(o, (1.5, b - 0.5)), width=1,
           dash='4 4')
    f.line(shift(o, (-0.92, b + 0.5)), shift(o, (1.5, b + 0.5)), width=1,
           dash='4 4')
    f.square(shift(o, (a, b)), fill=FILLS[0], stroke=BLUE)
    f.dot(shift(o, (a, b)), fill=BLUE)
    f.circle(o, R_AUX)
    (t0, t1), = chart_runs(a, b, o)
    shift0 = math.remainder(t0, 2 * math.pi) - t0
    t0, t1 = t0 + shift0, t1 + shift0
    assert abs((t1 - t0) - arc_length(a, b)) < 2e-3
    f.arc(o, R_AUX, t0, t1, color, width=5)
    for t in (t0, t1):
        f.line(o, shift(o, u(t), R_AUX), width=1)
    f.arc(o, 0.2, t0, t1, INK, width=1.1)
    f.dot(o)
    f.text(shift(o, (-0.04, -0.08)), 'o', anchor='end')
    label(f, shift(o, (0.3, 1.54)), title, 14, 'middle', italic=False)
    f.text(shift(o, (0.3, 1.39)), value, size=14, italic=False, color=color)
    return t0, t1


def third_side():
    """Why P5 needs its third side: at the point (3/4, 3/4), where its first
    two sides meet, the arc on the circle of radius 5/6 is less than a fifth;
    at the corner of P5 it is just more."""
    dx = 2.55
    f = Figure(-0.95, dx + 1.52, -0.97, 1.62, 165)
    assert 3 * 0.75 + 0.75 == 3 and 0.75 + 3 * 0.75 == 3
    t0, t1 = chart_panel(f, (0, 0), 0.75, 0.75, RED, 'the point (¾, ¾)',
                         'arc ≈ 55°')
    assert 55 < math.degrees(t1 - t0) < 55.2 < 72
    s0, s1 = chart_panel(f, (dx, 0), CX, CY, ORANGE,
                         'corner of ' + it(sb('P', '5', size=14)),
                         'arc ≈ 72.8°')
    assert 72 < 72.7 < math.degrees(s1 - s0) < 72.9
    save(f, '08-five/third-side', 'Left: a square at (3/4, 3/4), where the '
         'first two sides of the 12-gon meet, holds only about 55 degrees of '
         'the circle of radius 5/6, less than a fifth. Right: at the corner of '
         'the 12-gon it holds about 72.8 degrees, just more than a fifth')


def arcsine_region():
    """Lemma 8.8: its region in the (x, y)-plane, split at x = 2/5 into the
    two cases of the proof, below the level curve of the arcsine sum at
    pi/10."""
    q = 2 / 5
    s = SQ5 - 2
    xc = (1 - s) / 2
    yc = s - xc
    f = Figure(-0.1, 0.74, -0.6, 0.47, 540)
    region = [(0, -0.5), (0.5, -0.5), (xc, yc), (0, s)]
    case1 = [(0, -0.5), (q, -0.5), (q, 1 - 3 * q), (xc, yc), (0, s)]
    case2 = [(q, -0.5), (0.5, -0.5), (q, 1 - 3 * q)]
    assert xc < q
    for poly, k in ((case1, 0), (case2, 3)):
        f.polygon(poly, fill=FILLS[k], stroke='none')
    f.polygon(region, stroke=INK, width=1.6)
    f.line((q, -0.5), (q, 1 - 3 * q), stroke=INK, width=1, dash='3 3')
    f.line((xc, yc), (0.5, s - 0.5), stroke=INK, width=1, dash='1 3')
    # The level curve arcsin(6x/5) + arcsin(6y/5) = pi/10.
    level = []
    for k in range(101):
        x = 0.5 * k / 100
        y = R_AUX * math.sin(math.pi / 10 - math.asin(x / R_AUX))
        level.append((x, y))
    polyline(f, level, stroke=ORANGE, width=1.8)
    # Without the side 3x + y <= 1 the lemma fails at x = 1/2.
    assert level[-1][1] < s - 0.5
    worst = max(math.asin(1.2 * x) + math.asin(1.2 * y)
                for x in (0.5 * i / 400 for i in range(401))
                for y in (-0.5 + j / 400 for j in range(401))
                if x + y <= s and 3 * x + y <= 1)
    assert worst < 0.314 < math.pi / 10
    # The bounds of the proof: sqrt 5 - 2 < 0.237, and the two cases.
    assert 2.237 ** 2 > 5 and 54 / 125 * q ** 3 < 0.0277
    assert 6 / 5 * 0.237 + 0.0277 < 0.314
    assert abs(6 / 5 / 5 + 54 / 125 / 8 - 0.294) < 1e-12
    # Axes, ticks and labels.
    f.line((-0.06, 0), (0.6, 0), width=1, arrow=True)
    f.line((0, -0.58), (0, 0.45), width=1, arrow=True)
    f.text((0.6, -0.03), 'x', anchor='end')
    f.text((-0.02, 0.44), 'y', anchor='end')
    for x, name in ((0.5, '½'), (q, '2/5')):
        f.line((x, -0.51), (x, -0.49), width=1)
        f.text((x, -0.535), name, size=12, italic=False)
    f.line((-0.01, -0.5), (0.01, -0.5), width=1)
    f.text((-0.02, -0.5), '−½', size=12, italic=False, anchor='end')
    f.line((-0.01, s), (0.01, s), width=1)
    f.text((-0.02, s), '√5 − 2', size=12, italic=False, anchor='end')
    f.text((0.15, -0.3), '(i)', size=14, italic=False, color=BLUE)
    f.text((0.437, -0.42), '(ii)', size=13, italic=False, color=PURPLE)
    label(f, (0.52, s - 0.5), eqn('x + y = √5 − 2'), 12, italic=False)
    label(f, (0.46, -0.35), eqn('3x + y = 1'), 12, italic=False)
    label(f, (0.03, 0.3), 'arcsin ' + it('6x') + '/5 + arcsin ' + it('6y')
          + '/5 = π/10', 12, color=ORANGE, italic=False)
    save(f, '08-five/arcsine-region', 'The region of the arcsine-sum lemma in the '
         'plane of x and y, cut by x + y at most root 5 - 2 and 3x + y at '
         'most 1, split at x = 2/5 into the two cases of the proof; it lies '
         'below the curve where the arcsine sum equals pi/10')


def arc_cases():
    """The remark after Lemma 8.9: the arc of an exterior square on the circle
    of radius 5/6 ends on the lower edge at -V, and on the near edge at A or
    on the upper edge at U, whichever comes first."""
    dx = 2.55
    f = Figure(-0.95, dx + 1.55, -0.97, 1.36, 165)
    # Label offsets, chosen clear of the lines of the edges: for each mark
    # the position relative to its point on the circle and the anchor.
    places = {'A': {'−V': ((0.1, -0.09), 'start'), 'A': ((-0.1, 0.17), 'end'),
                    '−A': (None, 'start')},
              'U': {'−V': ((0.08, -0.08), 'start'), 'A': (None, 'start'),
                    '−A': (None, 'start'), 'U': ((0.08, 0.07), 'start')}}
    for o, (a, b), name in (((0, 0), (0.8, 0.4), 'A'),
                            ((dx, 0), (1.0, 0.0), 'U')):
        A, V, U = crossing_angles(a, b)
        assert V < A
        assert (A <= U) == (name == 'A')
        f.line(shift(o, (-0.92, 0)), shift(o, (1.52, 0)), stroke=FAINT,
               width=1)
        for p0, p1 in (((a - 0.5, -0.93), (a - 0.5, 1.3)),
                       ((-0.92, b - 0.5), (1.52, b - 0.5)),
                       ((-0.92, b + 0.5), (1.52, b + 0.5))):
            f.line(shift(o, p0), shift(o, p1), width=1, dash='4 4')
        f.square(shift(o, (a, b)), fill=FILLS[0], stroke=BLUE)
        f.dot(shift(o, (a, b)), fill=BLUE)
        f.circle(o, R_AUX)
        (t0, t1), = chart_runs(a, b, o)
        shift0 = math.remainder(t0, 2 * math.pi) - t0
        t0, t1 = t0 + shift0, t1 + shift0
        assert abs(t0 + V) < 2e-3 and abs(t1 - min(A, U)) < 2e-3
        f.arc(o, R_AUX, t0, t1, ORANGE, width=5)
        marks = [(-V, '−V', INK), (A, 'A', INK if name == 'A' else FAINT),
                 (-A, '−A', FAINT)]
        if U < HALF:
            marks.append((U, 'U', INK if name == 'U' else FAINT))
        for t, key, color in marks:
            p = shift(o, u(t), R_AUX)
            f.dot(p, r=3.4, fill=color)
            d, anchor = places[name][key]
            # The crossings beyond the arc (grey) are labelled outside the
            # circle, along their radius.
            at = shift(p, u(t), 0.12) if d is None else shift(p, d)
            label(f, at, sbn(key, 'S', size=13), 13, anchor, color=color)
        # The names of the edges sit clear of the circle.
        f.text(shift(o, (-0.55, b + 0.5 + 0.07)), 'upper edge', size=12,
               italic=False, anchor='start')
        f.text(shift(o, (-0.55, b - 0.5 - 0.08)), 'lower edge', size=12,
               italic=False, anchor='start')
        f.text(shift(o, (a - 0.5 + 0.04, 1.25)), 'near edge', size=12,
               italic=False, anchor='start')
        f.dot(o)
        f.text(shift(o, (-0.04, 0.08)), 'o', anchor='end')
        f.text(shift(o, (a + 0.05, b - 0.09)), f'({a:g}, {b:g})', size=12,
               italic=False, color=BLUE, anchor='start')
    save(f, '08-five/arc-cases', 'Two exterior squares in their charts on the '
         'circle of radius 5/6. Left, the square at (0.8, 0.4): the arc runs '
         'from the lower edge at minus V to the near edge at A, length A + V. '
         'Right, the square at (1, 0): it runs from the lower edge at minus V '
         'to the upper edge at U, length U + V')


def arc_map():
    """Lemma 8.10 over the whole region: the length of the arc of an exterior
    square on the circle of radius 5/6, as a function of (a, b). It exceeds
    72 degrees on the 12-gon, and falls below it only beyond its third
    side."""
    octagon = [(0.5, 0), (1, 0), (0.75, 0.75), (0.5, 0.5)]      # b <= a
    p5 = clip(octagon, 1, 1, SQ5 - 1)
    assert len(p5) == 5
    deg = lambda a, b: math.degrees(arc_length(a, b))
    inside = lambda p: point_in_convex(p, octagon)
    # On the 12-gon the arc is smallest at its corner, 72.8 degrees; below
    # 72 degrees only beyond the third side.
    grid = [(0.5 + 0.5 * i / 200, 0.75 * j / 200) for i in range(201)
            for j in range(201)]
    low = min(deg(*q) for q in [q for q in grid if point_in_convex(q, p5)]
              + list(p5))
    assert abs(low - deg(CX, CY)) < 1e-6 and 72.8 < low < 72.81
    assert all(q[0] + q[1] > SQ5 - 1 for q in grid
               if inside(q) and deg(*q) < 72)
    # The level 72 degrees, where A + V = 2 pi/5: by Lemma 8.8 in the
    # coordinates x = a - 1/2, y = b - 1/2.
    curve = lambda a: 0.5 + R_AUX * math.sin(math.pi / 10
                                             - math.asin(1.2 * (a - 0.5)))
    def root(g, lo, hi):
        assert (g(lo) > 0) != (g(hi) > 0)
        for _ in range(80):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if (g(mid) > 0) == (g(lo) > 0) else (lo, mid)
        return lo
    # Where the curve meets the diagonal b = a and the side 3a + b = 3.
    a0 = root(lambda a: curve(a) - a, 0.6, 0.75)
    a1 = root(lambda a: curve(a) - (3 - 3 * a), 0.75, 0.95)
    assert abs(curve(a0) - a0) < 1e-9 and abs(curve(a1) - (3 - 3 * a1)) < 1e-9
    level = [(a0 + (a1 - a0) * k / 60, curve(a0 + (a1 - a0) * k / 60))
             for k in range(61)]
    for q in level[1:-1]:
        assert inside(q) and abs(deg(*q) - 72) < 1e-6
    f = Figure(0.44, 1.04, -0.045, 0.81, 640)
    f.polygon(octagon, fill=FILLS[1], stroke='none')
    f.polygon(level + [(0.75, 0.75)], fill=RED, stroke='none', opacity=0.3)
    # Level curves every 4 degrees, labelled where the arc is U + V and
    # they are horizontal.
    for lev in (76, 80, 84):
        for ln in level_curves(deg, (0.5, 1.0, 0.0, 0.75), lev, 150):
            pts = [q for q in ln if inside(q)]
            if len(pts) > 1:
                polyline(f, pts, stroke=FAINT, width=1)
        height = [q[1] for q in grid if q[0] == 0.5 and deg(*q) <= lev
                  and q[1] < 1 / 3][-1]
        f.text((0.6, height + 0.014), f'{lev}°', size=12, italic=False)
    polyline(f, level, stroke=RED, width=2)
    # The boundary between the two cases: the upper near corner
    # (a - 1/2, b + 1/2) of the square on the circle of radius 5/6.
    split = [(0.5 + 0.4284 * k / 80,
              math.sqrt(25 / 36 - (0.4284 * k / 80) ** 2) - 0.5)
             for k in range(81)]
    assert abs(3 * split[-1][0] + split[-1][1] - 3) < 1e-3
    polyline(f, split, stroke=INK, width=1.2, dash='5 4')
    f.polygon(octagon, stroke=INK, width=1, dash='3 3')
    f.polygon(p5, stroke=ORANGE, width=2)
    # Axes and labels.
    f.line((0.47, 0), (1.03, 0), width=1, arrow=True)
    f.text((1.03, -0.025), 'a', anchor='end')
    f.line((0.47, -0.02), (0.47, 0.8), width=1, arrow=True)
    f.text((0.48, 0.795), 'b', anchor='start')
    for x, name in ((0.5, '½'), (0.75, '¾'), (1.0, '1')):
        f.line((x, -0.006), (x, 0.006), width=1)
        f.text((x, -0.025), name, size=12, italic=False)
    for y, name in ((0.5, '½'), (0.75, '¾')):
        f.line((0.464, y), (0.476, y), width=1)
        f.text((0.46, y), name, size=12, italic=False, anchor='end')
    f.dot((CX, CY), r=4)
    f.text((CX + 0.012, CY + 0.014), '72.8°', size=13, italic=False,
           anchor='start')
    f.circle((0.75, 0.75), 4 / f.s, stroke=RED, width=1.4, fill='#ffffff')
    f.text((0.765, 0.757), '(¾, ¾): 55°', size=13, italic=False,
           anchor='start')
    label(f, (0.6, 0.06), sbn('U', 'S', ' + ', 14) + sb('V', 'S', size=14),
          14, 'middle')
    label(f, (0.62, 0.41), sbn('A', 'S', ' + ', 14) + sb('V', 'S', size=14),
          14, 'middle')
    f.text((0.665, 0.66), '72°', size=13, italic=False, color=RED)
    f.text((0.82, 0.08), sb('P', '5', size=16), size=16, color=ORANGE)
    save(f, '08-five/arc-map', 'The length of the arc of an exterior square on '
         'the circle of radius 5/6 over the pairs (a, b) with b at most a in '
         'the octagon of the first two sides of P5: thin level curves at 76, '
         '80 and 84 degrees, a dashed curve between the cases U + V and A + V, and '
         'the level 72 degrees in red, which cuts off the corner (3/4, 3/4) '
         'beyond the third side of P5; on P5 the length is smallest, 72.8 '
         'degrees, at its corner')


# 8.4 A centred square.

def sweep_positions():
    """Lemma 8.11 at three positions of a containing square: slid out to
    distance root 2 over 2, its inscribed disk covers a fifth of the circle of
    radius 5/6, which therefore lies in the radial sweep."""
    offsets = [(0.06, 0.035), (0.3, 0.12), (0.44, 0.38)]
    dx = 2.45
    box = (-0.92, 1.45, -0.92, 1.45)
    f = Figure(box[0], 2 * dx + box[1], box[2], box[3], 105)
    for k, (a, b) in enumerate(offsets):
        o = (k * dx, 0.0)
        ell = math.hypot(a, b)
        assert ell ** 2 < 0.5 and max(a, b) < 0.5
        delta = math.atan2(b, a)
        m = 1 / (math.sqrt(2) * ell) - 1
        cstar = ((1 + m) * a, (1 + m) * b)
        corners = square_corners((a, b))
        hull = convex_hull(corners + [shift(p, (a, b), 40) for p in corners])
        panel = [(box[0], box[2]), (box[1], box[2]), (box[1], box[3] - 0.12),
                 (box[0], box[3] - 0.12)]
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
        f.square(shift(o, (a, b)), fill=FILLS[0], stroke=BLUE)
        f.square(shift(o, cstar), stroke=ORANGE, width=1.2, dash='4 3')
        f.circle(shift(o, cstar), 0.5, stroke=ORANGE, width=1.4)
        f.circle(o, R_AUX)
        f.arc(o, R_AUX, delta - math.pi / 5, delta + math.pi / 5, ORANGE,
              width=5)
        f.line(o, shift(o, u(delta), 1.35), width=1, dash='2 3', arrow=True)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.08)), 'o', anchor='end')
        f.dot(shift(o, (a, b)), r=2.6, fill=BLUE)
        f.dot(shift(o, cstar), r=2.6, fill=ORANGE)
        f.text(shift(o, (a, b - 0.66)), 'S', size=15, color=BLUE)
        label(f, shift(o, (0.3, 1.36)), pair_s(13) + up(f' = ({a:g}, {b:g})'),
              13, 'middle', color=BLUE)
    save(f, '08-five/sweep-positions', 'Three containing squares in their charts, '
         'with their radial sweeps shaded. Each slid copy, dashed, has its '
         'centre at distance root 2 over 2 from o, and its inscribed disk '
         'covers the arc of the circle of radius 5/6 of half-width pi/5 about '
         'the direction of the centre')


def sweep_margin():
    """Step 3 of the proof of Lemma 8.11: the squared distance from p_t to the
    centre c* of the slid square, against t - delta. It stays below 1/4 on
    |t - delta| <= pi/5, with a small margin."""
    h = 1 / math.sqrt(2)
    g = lambda s: 43 / 36 - 5 / 3 * h * math.cos(s)
    edge = math.pi / 5
    reach = math.acos((43 / 36 - 0.25) / (5 / 3 * h))
    assert abs(43 / 36 - 5 / 3 * 17 / 30 - 0.25) < 1e-12
    assert g(edge) < 0.25 and 0.0089 < 0.25 - g(edge) < 0.0091
    assert edge < reach < edge + 0.013
    p = Plot(-1.0, 1.06, -0.06, 0.37, 300, 1100)
    p.polygon([(-edge, 0), (edge, 0), (edge, 0.33), (-edge, 0.33)],
              fill=FILLS[1], stroke='none')
    p.line((-0.95, 0.25), (0.95, 0.25), stroke=INK, width=1, dash='5 4')
    p.curve(g, -0.95, 0.95, ylim=(-1, 0.34), stroke=BLUE, width=2.2)
    for s in (-edge, edge):
        p.line((s, 0), (s, 0.33), stroke=ORANGE, width=1, dash='3 3')
        p.dot((s, g(s)), r=3.6, fill=BLUE)
    x_axis(p, -0.97, 1.0, ticks=((-edge, '−π/5'), (0, '0'), (edge, 'π/5')),
           label='')
    y_axis(p, 0, 0.36, x=-0.97, ticks=((0.1, '0.1'), (0.2, '0.2'),
                                       (0.25, '¼')))
    label(p.f, p.q(1.0, -0.035), eqn('t − δ'), 15, 'end', italic=False)
    label(p.f, p.q(-0.92, 0.35), '|' + sbn('p', 't', ' − ', 15) + 'c'
          '<tspan dy="-6" font-size="11">*</tspan><tspan dy="6">|²</tspan>',
          15)
    # The margin at the ends of the interval.
    p.line((edge + 0.05, g(edge)), (edge + 0.05, 0.25), stroke=RED, width=1.4)
    label(p.f, p.q(edge + 0.08, 0.215), up('margin ≈ 0.009'), 13,
          color=RED, italic=False)
    save(p, '08-five/sweep-margin', 'The squared distance from the point of the '
         'circle of radius 5/6 at chart angle t to the centre of the slid '
         'square, against t minus delta: below 1/4 for t minus delta between '
         'minus pi/5 and pi/5, by about 0.009 at the ends')


def budget():
    """Proposition 8.12. Left: four arcs of more than a fifth and one of a
    fifth overrun the circle. Right: in the plus the four outer squares leave
    gaps adding up to less than a fifth."""
    dx = 2.9
    f = Figure(-1.25, dx + 1.6, -1.6, 1.6, 118)
    # Left: the schematic overrun, with the lengths of the plus.
    w = 2 * math.asin(0.6)
    start = HALF
    f.circle((0, 0), R_AUX)
    for k in range(4):
        f.arc((0, 0), R_AUX, start + k * w, start + (k + 1) * w, COLORS[k],
              width=5)
    s5 = start + 4 * w
    f.arc((0, 0), R_AUX + 0.12, s5, s5 + 2 * math.pi / 5, COLORS[4], width=5)
    over = s5 + 2 * math.pi / 5 - (start + 2 * math.pi)
    assert over > 0
    f.arc((0, 0), R_AUX + 0.25, start, start + over, INK, width=2)
    f.text(shift((0, 0), u(start + over / 2), R_AUX + 0.4), 'overlap',
           size=12, italic=False, anchor='middle')
    for k in range(4):
        f.text(shift((0, 0), u(start + (k + 0.5) * w), R_AUX - 0.24),
               '&gt; 72°', size=12, italic=False, color=COLORS[k])
    f.text(shift((0, 0), u(s5 + math.pi / 5), R_AUX + 0.34), '72°', size=12,
           italic=False, color=COLORS[4])
    f.dot((0, 0))
    f.text((0.04, -0.08), 'o', anchor='start')
    # Right: the plus on the circle of radius 5/6.
    o = (dx, 0.0)
    centres = CENTRES[1:]
    f.square(o, fill=GREY, stroke=FAINT)
    for k, c in enumerate(centres):
        f.square(shift(o, c), fill=FILLS[k + 1], stroke=COLORS[k + 1])
    f.circle(o, R_AUX)
    runs = []
    for k, c in enumerate(centres):
        (t0, t1), = arcs_in(lambda p: in_open_square(shift(p, o),
                                                     shift(o, c)), R_AUX)
        runs.append((t0, t1))
        f.arc(o, R_AUX, t0, t1, COLORS[k + 1], width=5)
    assert not arcs_in(lambda p: in_open_square(shift(p, o), o), R_AUX)
    gaps = 2 * math.pi - sum(t1 - t0 for t0, t1 in runs)
    assert gaps < 2 * math.pi / 5
    assert abs(math.degrees(runs[0][1] - runs[0][0]) - 73.74) < 0.05
    assert abs(math.degrees(gaps) / 4 - 16.26) < 0.05
    for k in range(4):
        mid = math.pi / 4 + k * HALF
        f.arc(o, R_AUX, mid - gaps / 8, mid + gaps / 8, INK, width=2.5)
    q = shift(o, u(-math.pi / 4), R_AUX)
    f.line(shift(q, u(-math.pi / 4), 0.05), shift(o, (0.82, -0.92)), width=0.8)
    f.text(shift(o, (0.84, -0.96)), 'gaps: 4 × 16.3°', size=12, italic=False,
           anchor='start')
    f.dot(o)
    f.text(shift(o, (0.05, -0.08)), 'o', anchor='start')
    save(f, '08-five/budget', 'Left: four arcs of more than a fifth of the circle '
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
    d = th + rad(45)
    c = shift((0, 0), u(d), 1.0)
    ddeg = math.degrees(d)
    lens = clip_square(square_corners((0, 0), tdeg), c, ddeg)
    assert len(lens) >= 3
    f.circle((0, 0), 1.0, stroke=INK, width=1.1, dash='5 4')
    f.square((0, 0), tdeg, fill=GREY, stroke=FAINT)
    f.square(c, ddeg, fill=FILLS[2], stroke=GREEN, opacity=0.8)
    f.polygon(lens, fill=FILLS[1], stroke=ORANGE, width=1.6)
    f.line((0, 0), c, width=1.1)
    f.text(shift(shift((0, 0), u(d), 0.82), u(d + HALF), 0.1), '1', size=13,
           italic=False)
    f.dot((0, 0))
    f.text((0.04, -0.1), 'o', anchor='start')
    f.dot(c, fill=GREEN)
    f.text(shift((0, 0), u(th + rad(225)), 0.42), sb('S', 'k', size=15),
           size=15, color=INK)
    # Right: the plus, turned by 20 degrees; its centres lie on the circle.
    o = (dx, 0.0)
    rot = lambda p: (p[0] * math.cos(th) - p[1] * math.sin(th),
                     p[0] * math.sin(th) + p[1] * math.cos(th))
    f.circle(o, 1.0, stroke=INK, width=1.1, dash='5 4')
    f.square(o, tdeg, fill=GREY, stroke=FAINT)
    # The colours of the outer squares as in Figure 8.1.
    for k, p in enumerate(CENTRES[1:], start=1):
        f.square(shift(o, rot(p)), tdeg, fill=FILLS[k], stroke=COLORS[k])
        f.line(o, shift(o, rot(p)), width=1)
        f.dot(shift(o, rot(p)), fill=COLORS[k])
    f.dot(o)
    f.text(shift(o, (0.05, -0.1)), 'o', anchor='start')
    f.text(shift(o, u(th + rad(225)), 0.42), sb('S', 'k', size=15),
           size=15, color=INK)
    save(f, '08-five/unit-contacts', 'Around a square centred at o, with the '
         'dashed unit circle about o. Left: a square whose centre is at '
         'distance 1 from o but not on an axis of the centred square overlaps '
         'it. Right: the only squares at distance 1 that do not overlap it are '
         'its four side-neighbours: the plus')


def main():
    construction()
    twelve_gon_plane()
    third_side()
    arcsine_region()
    arc_cases()
    arc_map()
    sweep_positions()
    sweep_margin()
    budget()
    unit_contacts()


if __name__ == '__main__':
    main()

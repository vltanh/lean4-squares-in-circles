#!/usr/bin/env python3
"""Draw the figures of Chapter 6 (three squares) as SVG files in
docs/proof/figures/06-three/.

    python3 scripts/figures/fig_three.py

Every figure is computed from the geometry of the chapter: arcs of squares on
the auxiliary circles are found by sampling the circle and testing membership
in the open squares, regions of the (a, b)-, (u, v)- and (P, Q)-planes by
clipping polygons with the lines that bound them, and graphs by sampling the
functions.
"""
import math
import re

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY, SERIF,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, subscript, clip, clip_square,
                           quadrant_disk, overlap)
from fig_front import it, sbn
from fig_appa import Plot, x_axis, y_axis

K = 425 / 256
R3 = 5 * math.sqrt(17) / 16
CENTRES = [(-0.5, -5 / 16), (0.5, -5 / 16), (0, 11 / 16)]
ORANGE, BLUE, GREEN, PURPLE = COLORS[1], COLORS[0], COLORS[2], COLORS[3]
RED = COLORS[4]


# Small local helpers.

def polyline(f, pts, stroke=INK, width=1.5, dash=None):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')


def sample(g, lo, hi, steps=240):
    return [(lo + (hi - lo) * k / steps, g(lo + (hi - lo) * k / steps))
            for k in range(steps + 1)]


def asin(x):
    """The arcsine extended to all of R, as in the text."""
    return math.pi / 2 if x >= 1 else -math.pi / 2 if x <= -1 else math.asin(x)


def acos(x):
    return math.pi / 2 - asin(x)


def rotate(p, t):
    return (p[0] * math.cos(t) - p[1] * math.sin(t),
            p[0] * math.sin(t) + p[1] * math.cos(t))


def placed(a, b, theta, eps=1):
    """The centre of the square whose chart is (theta, eps) with pair (a, b):
    it sits at (a, eps b) in the frame theta."""
    return rotate((a, eps * b), theta)


def up(s):
    """Upright markup, for words inside italic text."""
    return f'<tspan font-style="normal">{s}</tspan>'


_VAR = re.compile(r'(?<![A-Za-zα-ω])([A-Za-zα-ω])(?![A-Za-zα-ω])')


def eqn(s):
    """Markup of a formula set upright, with its one-letter variables in
    italics."""
    return _VAR.sub(lambda m: it(m.group(1)), s)


def label(f, pos, s, size=13, anchor='start', deg=0.0, color=INK,
          italic=True):
    """A label, given as SVG markup, turned by deg degrees counterclockwise
    about its anchor point."""
    x, y = f.p(*pos)
    style = ' font-style="italic"' if italic else ''
    place = (f'x="0" y="0" transform="translate({x:.1f} {y:.1f}) '
             f'rotate({-deg:.1f})"' if deg else f'x="{x:.1f}" y="{y:.1f}"')
    f.add(f'<text {place} font-size="{size}" font-family="{SERIF}" '
          f'fill="{color}" text-anchor="{anchor}" '
          f'dominant-baseline="middle"{style}>{s}</text>')


def arc(f, c, r, t0, t1, color, width=4.0):
    """An arc from angle t0 to t1, drawn in pieces of at most a quarter turn:
    an SVG arc between nearly opposite points is ill-conditioned and can
    drift off its circle."""
    n = max(1, math.ceil((t1 - t0) / (math.pi / 2) - 1e-9))
    for k in range(n):
        f.arc(c, r, t0 + (t1 - t0) * k / n, t0 + (t1 - t0) * (k + 1) / n,
              color, width)


def angle_mark(f, c, r, t0, t1, label, pos_r, color=INK, size=13):
    f.arc(c, r, t0, t1, color, width=1.2)
    f.text(shift(c, u((t0 + t1) / 2), pos_r), label, size=size, color=color)


def square_arcs(f, o, r, centre, deg, color, width=5):
    for t0, t1 in arcs_in(lambda p: in_open_square(shift(p, o), centre, deg),
                          r):
        arc(f, o, r, t0, t1, color, width=width)


def label_o(f, o=(0, 0), dx=-0.03, dy=-0.07, anchor='end'):
    f.dot(o)
    f.text(shift(o, (dx, dy)), 'o', anchor=anchor)


def pair_s(size=15, sub='S'):
    """The markup of the pair (a_S, b_S), with another subscript if asked."""
    return '(' + sbn('a', sub, ', ', size) + sbn('b', sub, ')', size)


def ticks(f, axis, values, at, length, labels=None, size=12):
    """Tick marks with labels along the horizontal (axis 'x') or the vertical
    (axis 'y') line through `at`."""
    for k, v in enumerate(values):
        text = labels[k] if labels else f'{v:g}'
        if axis == 'x':
            f.line((v, at - length), (v, at + length), width=1)
            f.text((v, at - 3 * length), text, size=size, italic=False)
        else:
            f.line((at - length, v), (at + length, v), width=1)
            f.text((at - 2 * length, v), text, size=size, italic=False,
                   anchor='end')


# 6.1 Construction.

def construction():
    m = 1.62
    f = Figure(-m, m, -1.42, 1.5, 165)
    f.circle((0, 0), R3, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(CENTRES):
        f.square(c, fill=FILLS[k], stroke=COLORS[k])
    for k, c in enumerate(CENTRES):
        f.dot(c, fill=COLORS[k])
        subscript(f, shift(c, (0.0, -0.1)), 'c', str(k + 1), color=COLORS[k])
    corners = [((-1, -13 / 16), '(−1, −13/16)', 'end', (-0.05, -0.08)),
               ((1, -13 / 16), '(1, −13/16)', 'start', (0.05, -0.08)),
               ((-0.5, 19 / 16), '(−½, 19/16)', 'end', (-0.06, 0.07)),
               ((0.5, 19 / 16), '(½, 19/16)', 'start', (0.06, 0.07))]
    for q, name, anchor, d in corners:
        assert abs(q[0] ** 2 + q[1] ** 2 - K) < 1e-12
        f.dot(q, r=4, fill=INK)
        f.text(shift(q, d), name, size=13, italic=False, anchor=anchor)
    for q in ((-1, 3 / 16), (1, 3 / 16)):
        assert q[0] ** 2 + q[1] ** 2 < K
        f.dot(q, r=3, fill=FAINT)
    label_o(f, dx=0.04, dy=-0.07, anchor='start')
    f.line((0, 0), shift((0, 0), u(rad(38)), R3), width=1, dash='3 3')
    f.text(shift((0, 0), u(rad(38)), 0.82 * R3), sb('R', '3', size=16),
           size=16, dx=-10, dy=-12)
    f.save('06-three/construction', 'The T in the circle of radius R3: the four '
           'corners (-1, -13/16), (1, -13/16), (-1/2, 19/16) and (1/2, 19/16) '
           'lie on the circle, the other corners inside it')


# 6.2 The contact polygon.

def tangents():
    lo_a, hi_a, lo_b, hi_b = -0.06, 0.86, -0.1, 0.62
    f = Figure(lo_a, hi_a, lo_b, hi_b, 560)
    box = [(lo_a, lo_b), (hi_a, lo_b), (hi_a, hi_b), (lo_a, hi_b)]
    facets = [(16, 13, 193 / 16), (19, 8, 209 / 16)]
    # The part of P3 with 0 <= b <= a.
    region = [(0, 0), (2, 0), (2, 2)]
    for a, b, c in facets:
        region = clip(region, a, b, c)
    f.polygon(region, fill=FILLS[1], stroke='none')
    # The disk phi <= K in the same sector.
    disk = [p for p in quadrant_disk(K, 200) if p[1] <= p[0] + 1e-12]
    diag = 0.5 * (math.sqrt(2 * K) - 1)
    f.polygon(disk + [(diag, diag)], fill=FILLS[0], stroke='none')
    arc_pts = [(-0.5 + math.sqrt(K) * math.cos(t), -0.5 + math.sqrt(K) *
                math.sin(t)) for t in (rad(8 + 0.2 * k) for k in range(200))]
    polyline(f, [p for p in arc_pts
                 if lo_a < p[0] < hi_a and lo_b < p[1] < hi_b],
             stroke=BLUE, width=1.6)
    # The two tangent lines, across the window.
    for a, b, c in facets:
        seg = clip(clip(clip(clip(box, a, b, c + 1e-9), -a, -b, -c + 1e-9),
                        1, 0, hi_a), -1, 0, -lo_a)
        pts = sorted(seg)
        polyline(f, [pts[0], pts[-1]], stroke=ORANGE, width=2)
    f.line((0, 0), (0.58, 0.58), stroke=FAINT, width=1, dash='5 4')
    label(f, (0.56, 0.585), eqn('b = a'), 13, 'end', color=FAINT,
          italic=False)
    f.line((-0.04, 0), (0.84, 0), width=1, arrow=True)
    f.line((0, -0.08), (0, 0.6), width=1, arrow=True)
    f.text((0.84, -0.035), 'a', anchor='end')
    f.text((-0.02, 0.59), 'b', anchor='end')
    for q, name, d, anchor in (((0.5, 5 / 16), 'B = (½, 5/16)',
                                (-0.025, -0.012), 'end'),
                               ((11 / 16, 0), 'A = (11/16, 0)',
                                (-0.02, -0.04), 'end')):
        f.dot(q, r=4.2)
        f.text(shift(q, d), name, size=14, italic=False, anchor=anchor)
    # Each label clear of its line: 16a + 13b = 193/16 passes a = 0.30 at
    # the height of the first label, which ends at a = 0.27.
    assert (193 / 16 - 13 * 0.555) / 16 > 0.27 + 0.02
    label(f, (0.27, 0.54), eqn('16a + 13b = 193/16'), 14, 'end',
          color=ORANGE, italic=False)
    label(f, (0.535, 0.47), eqn('19a + 8b = 209/16'), 14, color=ORANGE,
          italic=False)
    f.text((0.2, 0.08), 'φ ≤ 425/256', size=14, color=BLUE)
    vertex = (69 / 112, 19 / 112)
    assert abs(16 * vertex[0] + 13 * vertex[1] - 193 / 16) < 1e-12
    assert abs(19 * vertex[0] + 8 * vertex[1] - 209 / 16) < 1e-12
    f.dot(vertex, r=2.6, fill=ORANGE)
    f.save('06-three/tangents', 'The sector b at most a of the (a, b)-plane: '
           'the disk where phi is at most 425/256, and its tangent lines at '
           'B = (1/2, 5/16) and A = (11/16, 0), which cut out the part of P3 '
           'in the sector')


# 6.3 Exterior squares.

def uv_plane():
    lo_u, hi_u, lo_v, hi_v = -0.1, 0.94, 0.3, 1.5
    f = Figure(lo_u, hi_u, lo_v, hi_v, 400)
    region = [(0, 0.5), (13 / 42, 37 / 42), (0.5, 4 / 3), (0, 4 / 3)]
    # Check the corners against the two facets and the lines b = 0, u = 0.
    for uu, vv in region:
        a, b = 0.5 + 3 * uu / 8, 0.5 - 3 * vv / 8
        assert 16 * a + 13 * b <= 193 / 16 + 1e-12
        assert 19 * a + 8 * b <= 209 / 16 + 1e-12
        assert b >= -1e-12 and uu >= 0
    f.polygon(region, fill=FILLS[1], stroke=ORANGE, width=2)
    f.text((0.14, 1.23), 'image of', size=13, italic=False, color=ORANGE)
    f.text((0.14, 1.17), sb('P', '3', size=14), size=14, color=ORANGE)
    # A + V = 2 pi / 3, and A = V; the chain (6.3) of Lemma 6.7 puts the
    # dotted line v = 1/2 + u between this curve and the side of the region.
    curve = lambda x: math.sin(math.asin(x) + math.pi / 6)
    for k in range(1, 101):
        x = 0.5 * k / 100
        assert curve(x) < 0.5 + x < 0.5 + 16 * x / 13
    polyline(f, sample(curve, 0, 0.72), stroke=BLUE, width=2)
    f.text((0.56, 1.03), sbn('A', 'S', ' + ', 14) + sbn('V', 'S', ' = 2π/3',
                                                         14),
           size=14, color=BLUE, anchor='start')
    polyline(f, sample(lambda x: math.sqrt(1 - x * x), 0, 0.72),
             stroke=GREEN, width=1.6, dash='6 4')
    f.text((0.73, 0.66), sbn('A', 'S', ' = ', 14) + sb('V', 'S', size=14),
           size=14, color=GREEN, anchor='start')
    f.text((0.1, 1.08), 'full caps', size=12, italic=False, color=GREEN,
           anchor='start')
    f.text((0.015, 0.8), 'clipped caps', size=12, italic=False, color=GREEN,
           anchor='start')
    polyline(f, [(x, 0.5 + x) for x in (0, 0.3)], stroke=FAINT, width=1.2,
             dash='3 3')
    f.text((0.31, 0.79), eqn('v = ½ + u'), size=12, italic=False,
           color=FAINT, anchor='start')
    f.line((0.5, lo_v + 0.02), (0.5, hi_v - 0.04), stroke=PURPLE, width=1.4,
           dash='6 4')
    f.text((0.52, 1.45), sbn('A', 'S', ' = π/3', 14), size=14, color=PURPLE,
           anchor='start')
    f.line((lo_u, 1.0), (hi_u, 1.0), stroke=GREY, width=1)
    f.line((lo_u + 0.02, lo_v + 0.04), (hi_u - 0.02, lo_v + 0.04), width=1,
           arrow=True)
    f.line((0, lo_v + 0.02), (0, hi_v - 0.02), width=1, arrow=True)
    f.text((hi_u - 0.03, lo_v + 0.09), 'u', anchor='end')
    f.text((-0.03, hi_v - 0.04), 'v', anchor='end')
    ticks(f, 'x', [0.5], lo_v + 0.04, 0.012, ['½'])
    ticks(f, 'y', [0.5, 1.0, 4 / 3], 0, 0.012, ['½', '1', '4/3'])
    f.dot((0, 0.5), r=4.2)
    f.text((0.03, 0.47), 'B', size=15, italic=False, anchor='start')
    f.dot((0.5, 4 / 3), r=4.2)
    f.text((0.53, 1.36), 'A', size=15, italic=False, anchor='start')
    f.save('06-three/uv', 'The (u, v)-plane: the image of the part of P3 with a '
           'at least 1/2, above the curve where A + V = 2 pi / 3 except at B, '
           'and left of the line where A = pi / 3 except at A; the dashed '
           'curve where A = V separates clipped from full caps')


def cap_panel(f, o, a, b, r, title):
    uu, vv = (a - 0.5) / r, (0.5 - b) / r
    A, V = acos(uu), asin(vv)
    lo = -min(A, V)
    f.line(shift(o, (-0.46, 0)), shift(o, (1.3, 0)), stroke=FAINT, width=1)
    f.text(shift(o, (1.3, 0.05)), 't = 0', size=12, italic=False,
           color=FAINT, anchor='end')
    f.square(shift(o, (a, b)), fill=FILLS[0], stroke=BLUE)
    f.dot(shift(o, (a, b)), fill=BLUE)
    f.text(shift(o, (a + 0.04, b + 0.06)), pair_s(13), size=13,
           anchor='start', color=BLUE)
    f.line(shift(o, (a - 0.5, -0.62)), shift(o, (a - 0.5, 0.95)), width=1,
           dash='4 4')
    f.line(shift(o, (-0.46, b - 0.5)), shift(o, (1.3, b - 0.5)), width=1,
           dash='4 4')
    f.circle(o, r)
    f.arc(o, r, lo, A, ORANGE, width=5)
    # Check the arc against the squares: sampled membership.
    runs = arcs_in(lambda p: in_open_square(shift(p, o), shift(o, (a, b))), r)
    assert len(runs) == 1
    t0, t1 = runs[0]
    if t0 > math.pi:
        t0, t1 = t0 - 2 * math.pi, t1 - 2 * math.pi
    assert abs(t0 - lo) < 2e-3 and abs(t1 - A) < 2e-3
    for t in (A, lo):
        f.line(o, shift(o, u(t), r), width=1)
        f.dot(shift(o, u(t), r), r=3.4)
    # The label of A_S stays right of the line of the near edge.
    angle_mark(f, o, 0.11, 0, A, sb('A', 'S', size=13), 0.25)
    if V < A:
        angle_mark(f, o, 0.15, -V, 0, sb('V', 'S', size=13), 0.22)
    else:
        f.line(o, shift(o, u(-A), r), width=1, dash='3 3', stroke=FAINT)
        f.dot(shift(o, u(-A), r), r=3.4, fill=FAINT)
        angle_mark(f, o, 0.15, -A, 0, sb('A', 'S', size=13), 0.22)
    w = (A + min(A, V)) / 2
    label(f, shift(o, (0.4, 1.1)), title, 14, 'middle', color=ORANGE)
    f.text(shift(o, (0.4, 1.0)), 'half-width %.0f°' % math.degrees(w),
           size=13, italic=False, color=ORANGE)
    label_o(f, o)
    return A, V


def caps():
    r = 3 / 8
    off = 2.0
    f = Figure(-0.5, off + 1.32, -0.66, 1.16, 205)
    A1, V1 = cap_panel(f, (0, 0), 0.6, 0.06, r,
                       up('full cap: ') + sbn('A', 'S', ' ≤ ', 14)
                       + sb('V', 'S', size=14))
    A2, V2 = cap_panel(f, (off, 0), 0.52, 0.28, r,
                       up('clipped cap: ') + sbn('V', 'S', ' &lt; ', 14)
                       + sb('A', 'S', size=14))
    assert A1 <= V1 and V2 < A2
    for a, b in ((0.6, 0.06), (0.52, 0.28)):
        assert 16 * a + 13 * b <= 193 / 16 and 19 * a + 8 * b <= 209 / 16
    f.save('06-three/caps', 'Two exterior squares in their charts with their '
           'caps on the circle of radius 3/8: a full cap, symmetric about '
           't = 0, and a cap clipped by the lower edge; both are longer than '
           'a third of the circle')


# 6.4 The containing square.

def radial_proof():
    cs, aS, bS = (-0.3, -0.1), 0.3, 0.1
    theta, aT, bT = rad(15), 0.62, 0.2
    ct = placed(aT, bT, theta)
    deg = math.degrees(theta)
    rho = (aT - aS) / 2
    assert aT - 0.5 < rho < 0.5 - aS
    f = Figure(-0.95, 1.35, -0.72, 0.95, 300)
    f.square(cs, fill=FILLS[0], stroke=BLUE)
    f.square(ct, deg, fill=FILLS[2], stroke=GREEN)
    both = clip_square(square_corners(cs), ct, deg)
    f.polygon(both, fill=FILLS[1], stroke=ORANGE, width=1.2)
    f.square(cs, stroke=BLUE)
    f.circle((0, 0), 0.5 - aS, stroke=BLUE, width=1, dash='3 3')
    f.circle((0, 0), rho, stroke=INK, width=1.4)
    square_arcs(f, (0, 0), rho, ct, deg, ORANGE, width=6)
    # The line of the near edge of T.
    n, e = u(theta), u(theta + math.pi / 2)
    p0 = shift((0, 0), n, aT - 0.5)
    f.line(shift(p0, e, -0.66), shift(p0, e, 0.9), stroke=GREEN, width=1,
           dash='4 4')
    label_o(f, dx=-0.03, dy=0.05)
    f.text((-0.7, 0.28), 'S', size=17, color=BLUE)
    f.text(shift(ct, (0.35, 0.3)), 'T', size=17, color=GREEN)
    q = shift((0, 0), u(rad(150)), rho)
    f.line(q, (-0.4, 0.2), width=0.8)
    subscript(f, (-0.42, 0.22), 'Γ', 'ρ', size=15, anchor='end')
    q = shift((0, 0), u(rad(235)), 0.5 - aS)
    f.line(q, (-0.35, -0.4), width=0.8, stroke=BLUE)
    f.text((-0.36, -0.44), 'D(o, ½ − ' + sb('a', 'S', ')', 14), size=14,
           anchor='end', color=BLUE)
    f.save('06-three/radial-proof', 'If the near edge of T came closer to o '
           'than one half minus a_S, the circle of radius rho about o would '
           'lie in S and cross into T, so S and T would overlap')


def compensation():
    top = 13 / 32
    E = lambda t: asin(0.5 + 16 * t / 13) - asin(t) - math.pi / 6
    D = lambda t: math.pi / 6 - asin(t) - asin(0.5 - 16 * t / 13)
    for k in range(401):
        t = top * k / 400
        assert E(t) >= D(t) - 1e-12
        if k:
            assert E(t) > E(top * (k - 1) / 400)
    f = Figure(-0.06, 0.49, -0.07, 0.7, 700)
    f.line((-0.01, 0), (0.46, 0), width=1, arrow=True)
    f.line((0, -0.01), (0, 0.69), width=1, arrow=True)
    f.text((0.455, 0.025), 't', anchor='end')
    ticks(f, 'x', [0.1, 0.2, 0.3, top], 0, 0.006,
          ['0.1', '0.2', '0.3', '13/32'])
    ticks(f, 'y', [0.2, 0.4, 0.6], 0, 0.006)
    f.line((top, 0), (top, 0.66), stroke=FAINT, width=1, dash='3 3')
    polyline(f, sample(E, 0, top), stroke=ORANGE, width=2.2)
    polyline(f, sample(D, 0, top), stroke=BLUE, width=2.2)
    # P and u between the ticks, so that their names stay clear of the tick
    # labels.
    P, U = 0.15, 0.25
    for x, name in ((P, 'P'), (U, 'u')):
        f.line((x, 0), (x, E(x)), stroke=FAINT, width=1, dash='3 3')
        f.text((x, -0.02), name, size=14)
    f.dot((P, D(P)), fill=BLUE)
    f.dot((P, E(P)), fill=ORANGE)
    f.dot((U, E(U)), fill=ORANGE)
    f.line((P, E(P)), (U, E(P)), stroke=ORANGE, width=1, dash='2 3')
    f.text((0.33, 0.52), 'f(t) − π/6', size=15, color=ORANGE, anchor='end')
    f.text((0.33, 0.475), 'least excess', size=12, italic=False,
           color=ORANGE, anchor='end')
    f.text((0.412, 0.12), 'largest', size=12, italic=False, color=BLUE,
           anchor='start')
    f.text((0.412, 0.095), 'deficit', size=12, italic=False, color=BLUE,
           anchor='start')
    f.save('06-three/compensation', 'Graphs on the interval from 0 to 13/32: '
           'the increasing function f(t) - pi/6, the least excess of a '
           'clipped cap, lies above the largest deficit of the containing '
           'square')


def deficit():
    r = 3 / 8
    P = Q = 13 / 58
    a = b = 0.5 - r * P
    lo, hi = -asin(Q), math.pi / 2 + asin(P)
    L = hi - lo
    assert math.pi / 2 + 13 / 29 < L < 2 * math.pi / 3
    f = Figure(-0.7, 1.05, -0.5, 1.02, 330)
    f.line((-0.53, 0), (1.0, 0), stroke=FAINT, width=1)
    f.line((0, -0.48), (0, 0.98), stroke=FAINT, width=1)
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.dot((a, b), fill=BLUE)
    f.text((a + 0.03, b + 0.06), pair_s(14), size=14, anchor='start',
           color=BLUE)
    f.circle((0, 0), r)
    runs = arcs_in(lambda p: in_open_square(p, (a, b)), r)
    assert len(runs) == 1
    f.arc((0, 0), r, lo, hi, ORANGE, width=5)
    f.arc((0, 0), r, hi, lo + 2 * math.pi / 3, RED, width=5)
    for t in (lo, hi):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    f.text(shift((0, 0), u(rad(40)), r + 0.08), sb('L', 'S', size=15),
           size=15, color=ORANGE)
    q = shift((0, 0), u(hi + 0.04), r)
    f.line(shift(q, (-0.02, 0.01)), (-0.36, 0.5), stroke=RED, width=1)
    label(f, (-0.4, 0.55), '2π/3 − ' + sbn('L', 'S', ' &lt; π/6 − 13/29', 14),
          14, 'middle', color=RED)
    label_o(f, dx=-0.03, dy=-0.06)
    f.text((a + 0.38, b + 0.42), 'S', size=17, color=BLUE)
    f.save('06-three/deficit', 'A square containing o with P = Q = 13/58, the '
           'worst case: its arc of the circle of radius 3/8 falls short of a '
           'third of the circle by less than pi/6 - 13/29')


def pq_plane():
    """Step 1 of Proposition 6.15 in the plane of (P, Q) = (P_S, Q_S): the
    line of (6.5), the curve L_S = 2 pi/3 and the diagonal P = Q cut out a
    thin sliver, which lies above the line P + Q = 13/29."""
    s0, s1 = 13 / 58, math.sin(math.pi / 12)
    line = lambda P: 0.5 - 16 * P / 13          # 16 P + 13 Q = 13/2
    curve = lambda P: math.sin(math.pi / 6 - math.asin(P))   # L_S = 2 pi/3
    assert abs(line(s0) - s0) < 1e-12 and abs(curve(s1) - s1) < 1e-12
    assert abs(math.pi / 2 + 2 * math.asin(s1) - 2 * math.pi / 3) < 1e-12
    for k in range(1, 400):
        P = s1 * k / 400
        assert curve(P) > P
        if P < s0:
            # The sliver over P: from the line up to the curve, above
            # P + Q = 13/29.
            assert curve(P) > line(P) > P and line(P) + P > 13 / 29
    sliver = ([(P, curve(P)) for P in (s1 * k / 80 for k in range(81))]
              + [(s0, s0)]
              + [(P, line(P)) for P in (s0 * (80 - k) / 80 for k in range(81))])
    p = Plot(-0.035, 0.33, -0.05, 0.6, 850, 850)
    f = p.f
    p.polygon(sliver, fill=FILLS[4], stroke=RED, width=1)
    p.line((0, 0), (0.3, 0.3), stroke=FAINT, width=1.2, dash='5 4')
    p.line((0, 13 / 29), (0.3, 13 / 29 - 0.3), stroke=INK, width=1.2,
           dash='2 3')
    p.curve(line, 0, 0.3, stroke=ORANGE, width=2)
    p.curve(curve, 0, 0.3, stroke=BLUE, width=2)
    x_axis(p, -0.02, 0.32, ticks=((0.1, '0.1'), (0.2, '0.2'), (0.3, '0.3')),
           label='P')
    y_axis(p, -0.03, 0.585, ticks=((0.1, '0.1'), (0.2, '0.2'), (0.3, '0.3'),
                                   (0.4, '0.4'), (0.5, '½')), label='Q')
    p.dot((s0, s0), r=4)
    # The corner label sits between the diagonal and the dotted line.
    p.line((s0 - 0.004, s0 - 0.002), (0.19, 0.2), width=0.8)
    label(f, p.q(0.182, 0.2), eqn('P = Q = 13/58'), 13, 'end',
          italic=False)
    # Labels along the lines, on the side away from the sliver: the orange
    # line runs below the dotted one right of the corner.
    label(f, p.q(0.105, curve(0.105) + 0.024),
          sbn('L', 'S', ' = 2π/3', 14), 14, 'middle',
          -math.degrees(math.atan(0.93)), color=BLUE)
    label(f, p.q(0.268, line(0.268) - 0.034), eqn('16P + 13Q = 13/2'), 13,
          'middle', -math.degrees(math.atan(16 / 13)), color=ORANGE,
          italic=False)
    label(f, p.q(0.07, 13 / 29 - 0.07 - 0.024), eqn('P + Q = 13/29'), 13,
          'middle', -45, italic=False)
    label(f, p.q(0.08, 0.08 - 0.024), eqn('Q = P'), 13, 'middle', 45,
          color=FAINT, italic=False)
    f.save('06-three/pq-plane', 'The (P, Q)-plane: the line 16P + 13Q = 13/2 '
           'of the strict inequality (6.5), the curve where L_S = 2 pi/3 and '
           'the diagonal Q = P bound a thin sliver, which lies above the '
           'dotted line P + Q = 13/29 and meets it only at its corner '
           'P = Q = 13/58')


def clipped_cap():
    """Step 2 of Proposition 6.15 where its conclusion fails: a containing
    square S and a disjoint square T with a clipped cap, both in the closed
    disk of radius R3, leave less than a third of the circle of radius 3/8
    for the third square."""
    r = 3 / 8
    P = Q = 0.24
    aS = bS = 0.5 - r * P
    cs = (aS, bS)
    aT, bT = 0.59, 0.18
    ct = (-aT, bT)        # o - c_T = (aT, -bT): offsets (aT, bT)
    phi = lambda a, b: (a + 0.5) ** 2 + (b + 0.5) ** 2
    assert phi(aS, bS) <= K and phi(aT, bT) <= K
    assert not overlap(square_corners(cs), square_corners(ct))
    uT, vT = (aT - 0.5) / r, (0.5 - bT) / r
    assert 16 * aT + 13 * bT <= 193 / 16 and 19 * aT + 8 * bT <= 209 / 16
    A, V = acos(uT), asin(vT)
    assert V < A and P <= uT + 1e-12
    LS = math.pi / 2 + asin(P) + asin(Q)
    (s0, s1), = arcs_in(lambda p: in_open_square(p, cs), r)
    (t0, t1), = arcs_in(lambda p: in_open_square(p, ct), r)
    assert abs((s1 - s0) - LS) < 2e-3 and abs((t1 - t0) - (A + V)) < 2e-3
    free = arcs_in(lambda p: not (in_open_square(p, cs)
                                  or in_open_square(p, ct)), r)
    total = sum(b - a for a, b in free)
    assert abs(total - (2 * math.pi - LS - A - V)) < 4e-3
    # T touches S along the line of its near edge, so the arcs meet and the
    # free part is one arc.
    assert total < 2 * math.pi / 3 and len(free) == 1
    f = Figure(-1.2, 1.02, -0.62, 1.02, 270)
    f.square(cs, fill=FILLS[0], stroke=BLUE)
    f.square(ct, fill=FILLS[2], stroke=GREEN)
    f.circle((0, 0), r)
    arc(f, (0, 0), r, s0, s1, BLUE, width=5)
    arc(f, (0, 0), r, t0, t1, GREEN, width=5)
    for a, b in free:
        arc(f, (0, 0), r, a, b, RED, width=3)
    label_o(f, dx=0.03, dy=-0.06, anchor='start')
    f.text(shift(cs, (0.36, 0.38)), 'S', size=17, color=BLUE)
    f.text(shift(ct, (-0.36, 0.38)), 'T', size=17, color=GREEN)
    f.text(shift((0, 0), u((s0 + s1) / 2), r + 0.12),
           '≈ %.0f°' % math.degrees(s1 - s0), size=13, italic=False,
           color=BLUE)
    f.text(shift((0, 0), u((t0 + t1) / 2), r + 0.13),
           '≈ %.0f°' % math.degrees(t1 - t0), size=13, italic=False,
           color=GREEN)
    big = max(free, key=lambda run: run[1] - run[0])
    q = shift((0, 0), u((big[0] + big[1]) / 2), r)
    f.line(q, (0.42, -0.5), stroke=RED, width=1)
    f.text((0.44, -0.5), 'free: ≈ %.0f° &lt; 120°' % math.degrees(total),
           size=13, italic=False, color=RED, anchor='start')
    f.save('06-three/clipped-cap', 'A square S containing o with P = Q = 0.24 '
           'and a disjoint square T whose cap on the circle of radius 3/8 is '
           'clipped: their arcs of about 118 and 135 degrees leave about 108 '
           'degrees free, less than a third of the circle')


def axial_window():
    """Step 3 of Proposition 6.15: a full cap short enough for the budget
    leaves the pair (a_T, b_T) only a small triangle at the type A point,
    below b = 1/16."""
    bound = 5 * math.pi / 12 - 13 / 58
    a0 = 0.5 + 3 / 8 * math.cos(bound)
    b0 = (209 / 16 - 19 * a0) / 8
    assert abs(b0 - 57 / 64 * (0.5 - (a0 - 0.5) / (3 / 8))) < 1e-12
    assert 0 < b0 < 1 / 16 < 19 / 112 and 69 / 112 < a0 < 11 / 16
    # The full cap at a = a0 has half-width exactly the bound, and V = pi/2.
    assert abs(acos((a0 - 0.5) / (3 / 8)) - bound) < 1e-12
    assert asin((0.5 - b0) / (3 / 8)) == math.pi / 2
    region = [(0.5, 0), (11 / 16, 0), (69 / 112, 19 / 112), (0.5, 5 / 16)]
    window = [(a0, 0), (11 / 16, 0), (a0, b0)]
    f = Figure(0.43, 0.745, -0.055, 0.37, 1300)
    # Right of the purple line the full cap is short enough: A_T decreases
    # as a_T grows.
    f.polygon([(a0, -0.02), (0.735, -0.02), (0.735, 0.35), (a0, 0.35)],
              fill=FILLS[3], stroke='none')
    f.polygon(region, fill=FILLS[1], stroke=ORANGE, width=2)
    f.polygon(window, fill=RED, stroke=RED, width=1, opacity=0.6)
    f.line((0.445, 1 / 16), (0.735, 1 / 16), stroke=INK, width=1, dash='5 4')
    f.text((0.47, 1 / 16 + 0.012), eqn('b = 1/16'), size=13, italic=False,
           anchor='start')
    f.line((a0, -0.02), (a0, 0.35), stroke=PURPLE, width=1.3, dash='6 4')
    label(f, (a0 - 0.012, 0.335), sbn('A', 'T', ' = 5π/12 − 13/58', 14), 14,
          'end', color=PURPLE)
    # Axes: a along b = 0, and b on a vertical line left of the region.
    f.line((0.445, 0), (0.735, 0), width=1, arrow=True)
    f.text((0.733, -0.025), 'a', anchor='end')
    f.line((0.455, -0.02), (0.455, 0.355), width=1, arrow=True)
    f.text((0.465, 0.355), 'b', anchor='start')
    for x, name in ((0.5, '½'), (0.6, '0.6')):
        f.line((x, -0.004), (x, 0.004), width=1)
        f.text((x, -0.02), name, size=12, italic=False)
    for y, name in ((5 / 16, '5/16'),):
        f.line((0.451, y), (0.459, y), width=1)
        f.text((0.448, y), name, size=12, italic=False, anchor='end')
    f.dot((11 / 16, 0), r=4)
    f.text((11 / 16 + 0.006, -0.02), 'A', size=14, italic=False,
           anchor='start')
    f.dot((0.5, 5 / 16), r=4)
    f.text((0.506, 5 / 16 + 0.012), 'B', size=14, italic=False,
           anchor='start')
    label(f, (0.555, 0.14), it(sbn('P', '3', ', ', 15)) + it('a') + ' ≥ ½',
          15, 'middle', color=ORANGE, italic=False)
    f.save('06-three/axial-window', 'The part of P3 with a at least 1/2 in the '
           '(a, b)-plane; right of the line where the full cap has half-width '
           '5 pi/12 - 13/58 only a small triangle at the type A point remains, '
           'below the line b = 1/16')


def wide_arc():
    r = 7 / 16
    a, b = 11 / 16, 1 / 16
    A = acos((a - 0.5) / r)
    target = math.pi / 3 + 1 / 14
    assert A > target and asin((0.5 - b) / r) == math.pi / 2
    f = Figure(-0.62, 1.3, -0.56, 0.78, 290)
    f.line((-0.6, 0), (1.28, 0), stroke=FAINT, width=1)
    f.text((-0.6, 0.04), 't = 0', size=12, italic=False, color=FAINT,
           anchor='start')
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.dot((a, b), fill=BLUE)
    f.text((a + 0.04, b + 0.06), '(11/16, 1/16)', size=13, italic=False,
           anchor='start', color=BLUE)
    f.circle((0, 0), r)
    f.circle((0, 0), 3 / 8, stroke=FAINT, width=1, dash='3 3')
    runs = arcs_in(lambda p: in_open_square(p, (a, b)), r)
    assert len(runs) == 1
    f.arc((0, 0), r, -A, A, ORANGE, width=5)
    for t in (A, -A):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    for t in (target, -target):
        f.line((0, 0), shift((0, 0), u(t), r + 0.2), stroke=PURPLE, width=1,
               dash='4 3')
    angle_mark(f, (0, 0), 0.12, 0, A, 'A', 0.18)
    f.text(shift((0, 0), u(target), r + 0.23), '±(π/3 + 1/14)', size=13,
           color=PURPLE, anchor='end', dx=-4)
    f.dot((0, -r), r=3.6, fill=RED)
    f.line((-0.4, b - 0.5), (1.2, b - 0.5), stroke=RED, width=1, dash='4 4')
    f.text((-0.4, b - 0.5 - 0.045), up('lower edge: ') + 'y' + up(' = −7/16'),
           size=12, italic=True, color=RED, anchor='start')
    q = shift((0, 0), u(rad(148)), r)
    f.line(q, (-0.5, 0.36), width=0.8)
    subscript(f, (-0.51, 0.39), 'Γ', '7/16', size=15, anchor='end')
    q = shift((0, 0), u(rad(205)), 3 / 8)
    f.line(q, (-0.52, -0.3), width=0.8, stroke=FAINT)
    subscript(f, (-0.53, -0.32), 'Γ', '3/8', size=14, anchor='end',
              color=FAINT)
    label_o(f)
    f.save('06-three/wide-arc', 'A square with a = 11/16 and b = 1/16 in its '
           'chart: the circle of radius 7/16 just touches the line of the '
           'lower edge, and the square holds a full cap of half-width more '
           'than pi/3 + 1/14')


# 6.5 The T.

def two_type_a():
    a = 11 / 16
    t1, t2 = rad(90), rad(210)
    c1, c2 = placed(a, 0, t1), placed(a, 0, t2)
    d1, d2 = math.degrees(t1), math.degrees(t2)
    assert overlap(square_corners(c1, d1), square_corners(c2, d2))
    f = Figure(-1.35, 0.72, -1.1, 1.3, 190)
    f.square(c1, d1, fill=FILLS[2], stroke=GREEN)
    f.square(c2, d2, fill=FILLS[0], stroke=BLUE)
    both = clip_square(square_corners(c1, d1), c2, d2)
    f.polygon(both, fill=FILLS[1], stroke=ORANGE, width=1.4)
    # On the circle of radius 3/8 the caps, of half-width pi/3, only meet;
    # on the circle of radius 7/16 the arcs overlap.
    f.circle((0, 0), 3 / 8)
    (g0, g1), = arcs_in(lambda p: in_open_square(p, c1, d1), 3 / 8)
    (h0, h1), = arcs_in(lambda p: in_open_square(p, c2, d2), 3 / 8)
    assert abs(g1 - h0) < 2e-3 and abs((g1 - g0) - 2 * math.pi / 3) < 2e-3
    f.circle((0, 0), 7 / 16)
    square_arcs(f, (0, 0), 3 / 8, c1, d1, GREEN, width=2.5)
    square_arcs(f, (0, 0), 3 / 8, c2, d2, BLUE, width=2.5)
    square_arcs(f, (0, 0), 7 / 16, c1, d1, GREEN, width=6)
    square_arcs(f, (0, 0), 7 / 16, c2, d2, BLUE, width=3)
    for t, color in ((t1, GREEN), (t2, BLUE)):
        f.line((0, 0), shift((0, 0), u(t), 1.0), stroke=color, width=1,
               dash='4 3')
    angle_mark(f, (0, 0), 0.16, t1, t2, '2π/3', 0.27)
    label_o(f, dx=0.04, dy=-0.06, anchor='start')
    f.text(shift(c1, (0.3, 0.38)), 'type A', size=13, italic=False,
           color=GREEN)
    f.text(shift(c2, (-0.2, -0.35)), 'type A', size=13, italic=False,
           color=BLUE)
    q = shift((0, 0), u(rad(-20)), 7 / 16)
    f.line(q, (0.55, -0.35), width=0.8)
    subscript(f, (0.56, -0.4), 'Γ', '7/16', size=14, anchor='start')
    q = shift((0, 0), u(rad(-55)), 3 / 8)
    f.line(q, (0.4, -0.62), width=0.8)
    subscript(f, (0.41, -0.67), 'Γ', '3/8', size=14, anchor='start')
    f.save('06-three/two-type-a', 'Two squares of type A whose phases are a '
           'third of a turn apart overlap; their caps on the circle of radius '
           '3/8 only meet, and their arcs of the circle of radius 7/16 '
           'overlap')


def three_type_b():
    squares = [((-0.5, -5 / 16), 0, BLUE, FILLS[0]),
               ((0.5, -5 / 16), 0, ORANGE, FILLS[1]),
               ((-5 / 16, 0.5), 0, GREEN, FILLS[2])]
    for c, d, _, _ in squares:
        assert abs(abs(c[0]) - 0.5) < 1e-12 or abs(abs(c[1]) - 0.5) < 1e-12
    zoom = 4.0
    off = (2.25, 0.0)
    f = Figure(-1.1, 3.3, -1.02, 1.1, 150)
    for c, d, color, fill in squares:
        f.square(c, d, fill=fill, stroke=color, opacity=0.75)
    for i in range(3):
        for j in range(i + 1, 3):
            ci, di = squares[i][0], squares[i][1]
            cj, dj = squares[j][0], squares[j][1]
            if overlap(square_corners(ci, di), square_corners(cj, dj)):
                f.polygon(clip_square(square_corners(ci, di), cj, dj),
                          fill=RED, stroke=RED, width=1, opacity=0.35)
    label_o(f, dx=0.03, dy=-0.06, anchor='start')
    h = 0.25
    box = [(-h, -h), (h, -h), (h, h), (-h, h)]
    f.polygon(box, stroke=INK, width=1, dash='2 2')
    f.line((h + 0.02, 0.05), (off[0] - zoom * h - 0.06, 0.3), width=1,
           dash='2 2')
    # The zoom: the squares near o and the half circles of radius 3/16.
    r = 3 / 16
    zp = lambda p: shift(off, p, zoom)
    for c, d, color, fill in squares:
        part = clip_square(box, c, d)
        f.polygon([zp(p) for p in part], fill=fill, stroke=color, width=1.4,
                  opacity=0.75)
    f.polygon([zp(p) for p in box], stroke=INK, width=1, dash='2 2')
    f.circle(off, r * zoom)
    for (c, d, color, _), width in zip(squares, (9, 9, 4)):
        for t0, t1 in arcs_in(lambda p: in_open_square(p, c, d), r):
            assert abs((t1 - t0) - math.pi) < 2e-3
            arc(f, off, r * zoom, t0, t1, color, width=width)
    f.dot(off)
    f.text(shift(off, (0.06, -0.08)), 'o', anchor='start')
    subscript(f, shift(off, (0.62, 0.62)), 'Γ', '3/16', size=15)
    f.save('06-three/three-type-b', 'Three squares of type B: each holds a half '
           'of the circle of radius 3/16 about o, and three half circles '
           'cannot be disjoint; enlarged on the right')


def phases():
    phi = rad(20)
    r = 3 / 8
    # The T turned by phi: phases, orientations and cap centres.
    data = [(0, rad(180), 1), (1, rad(0), -1), (2, rad(90), 0)]
    f = Figure(-1.45, 1.45, -1.3, 1.45, 185)
    for k, c in enumerate(CENTRES):
        f.square(rotate(c, phi), math.degrees(phi), fill=FILLS[k],
                 stroke=COLORS[k])
    f.circle((0, 0), R3, stroke=INK, width=1.2, dash='6 4')
    # The frame theta_3 - pi/2 = phi.
    for t in (phi, phi + math.pi / 2):
        f.line(shift((0, 0), u(t), -1.35), shift((0, 0), u(t), 1.35),
               stroke=FAINT, width=1, dash='2 4')
    f.circle((0, 0), r)
    names = ['1', '2', '3']
    for k, theta, eps in data:
        c = rotate(CENTRES[k], phi)
        square_arcs(f, (0, 0), r, c, math.degrees(phi), COLORS[k], width=5)
        t = phi + theta
        f.line((0, 0), shift((0, 0), u(t), 1.3), stroke=COLORS[k], width=1.2,
               dash='5 3')
        subscript(f, shift((0, 0), u(t), 1.38 if k == 2 else 1.42), 'θ',
                  names[k], size=16, color=COLORS[k])
        centre = t + eps * math.pi / 6
        runs = arcs_in(lambda p: in_open_square(p, c, math.degrees(phi)), r)
        assert len(runs) == 1
        mid = (runs[0][0] + runs[0][1]) / 2
        assert abs(math.cos(mid - centre) - 1) < 1e-5
        f.line(shift((0, 0), u(centre), r - 0.05),
               shift((0, 0), u(centre), r + 0.05), width=2)
    small = 3 / 16
    f.circle((0, 0), small)
    for k in (0, 1):
        c = rotate(CENTRES[k], phi)
        square_arcs(f, (0, 0), small, c, math.degrees(phi), COLORS[k],
                    width=3.5)
    f.dot((0, 0), r=2.4)
    for k, d in ((0, (-0.28, -0.3)), (1, (0.3, -0.25)), (2, (0.3, 0.22))):
        subscript(f, shift(rotate(CENTRES[k], phi), d), 'S', str(k + 1),
                  size=17, color=COLORS[k])
    q = shift((0, 0), u(rad(-62)), small)
    f.line(q, (0.3, -0.62), width=0.8)
    subscript(f, (0.32, -0.66), 'Γ', '3/16', size=14, anchor='start')
    q = shift((0, 0), u(rad(-118)), 3 / 8)
    f.line(q, (-0.35, -0.72), width=0.8)
    subscript(f, (-0.37, -0.76), 'Γ', '3/8', size=14, anchor='end')
    f.save('06-three/phases', 'The T turned about o: the three caps of the circle '
           'of radius 3/8, each a third, with their centres marked, the phases '
           'of the three squares, the two opposite half circles of radius '
           '3/16 held by the lower squares, and the frame in which the '
           'squares sit at c1, c2, c3')


def main():
    construction()
    tangents()
    uv_plane()
    caps()
    radial_proof()
    compensation()
    deficit()
    pq_plane()
    clipped_cap()
    axial_window()
    wide_arc()
    two_type_a()
    three_type_b()
    phases()


if __name__ == '__main__':
    main()

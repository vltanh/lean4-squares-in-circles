#!/usr/bin/env python3
"""Draw the figures of Chapter 5, two squares, as SVG files in
docs/proof/figures/05-two/.

    python3 scripts/figures/fig_two.py

Every figure is computed from the geometry it illustrates: overlaps by
clipping one square by the other, membership by testing the open squares, and
the facts that the captions state are checked by assertions.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, square_corners,
                           in_open_square, u, shift, rad, sb, subsup,
                           clip_square, quadrant_disk, ab_axes)
from fig_front import interiors_meet
from fig_one import fit_radius, fit_region

R2 = math.sqrt(5) / 2
BLUE, ORANGE, GREEN = COLORS[0], COLORS[1], COLORS[2]


def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def frame_point(c, t, x, y):
    """The point with coordinates (x, y) in the frame at c turned by t."""
    return shift(shift(c, u(t), x), u(t + math.pi / 2), y)


def polyline(f, pts, stroke=INK, width=1.2, dash=None):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}"{extra}/>')


def corners():
    """The rectangle: its corners lie on the circle of radius R_2, since
    1 + 1/4 = 5/4."""
    c1, c2 = (-0.5, 0.0), (0.5, 0.0)
    pts = [(x, y) for x in (-1.0, 1.0) for y in (-0.5, 0.5)]
    assert all(abs(math.hypot(*q) - R2) < 1e-12 for q in pts)
    m = R2 + 0.17
    f = Figure(-m, m, -m, m, 165)
    f.circle((0, 0), R2, stroke=INK, width=1.2, dash='6 4')
    f.square(c1, fill=FILLS[0], stroke=BLUE)
    f.square(c2, fill=FILLS[1], stroke=ORANGE)
    f.line((-m + 0.03, 0), (m - 0.03, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, -m + 0.03), (0, m - 0.03), stroke=FAINT, width=1, arrow=True)
    f.text((m - 0.05, -0.09), 'x', anchor='end', color=FAINT)
    f.text((-0.06, m - 0.07), 'y', anchor='end', color=FAINT)
    f.line((0, 0), (1, 0), width=2.4)
    f.line((1, 0), (1, 0.5), width=2.4)
    f.line((0, 0), (1, 0.5), width=1.4)
    f.text((0.78, -0.09), '1', italic=False)
    f.text((0.95, 0.19), '½', italic=False, anchor='end')
    f.text((0.38, 0.3), sb('R', '2'))
    for q in pts:
        f.dot(q, r=3.8)
    for c, name, color in ((c1, '1', BLUE), (c2, '2', ORANGE)):
        f.dot(c, fill=color)
        f.text(shift(c, (-0.02, 0.1)) if c is c2 else shift(c, (0, -0.1)),
               sb('c', name), color=color)
    f.dot((0, 0))
    f.text((-0.05, -0.08), 'o', anchor='end')
    f.save('05-two/corners', 'The rectangle of two unit squares centred at '
           'minus one half and one half on the x-axis, inside the dashed '
           'circle of radius R2 about o; the right triangle with legs 1 and '
           'one half joins o to the corner (1, 1/2), which lies on the circle')


def near():
    """A unit square in the closed disk of radius R_2 about o, with its
    farthest vertex on the circle: its centre lies within 1/2 of o."""
    deg, b = 20, 0.15
    a = math.sqrt(1.25 - (b + 0.5) ** 2) - 0.5
    t = rad(deg)
    o = (0.0, 0.0)
    c = frame_point(o, t, a, b)       # the local coordinates of o: (-a, -b)
    far = frame_point(c, t, 0.5, 0.5)
    assert abs(phi(a, b) - 1.25) < 1e-12
    assert abs(math.dist(o, far) - R2) < 1e-12
    assert all(math.dist(o, q) <= R2 + 1e-12
               for q in square_corners(c, deg))
    assert abs(math.dist(o, c) ** 2 - (a * a + b * b)) < 1e-12
    assert math.dist(o, c) < 0.5
    m = R2 + 0.08
    f = Figure(-m, m, -m, m, 175)
    f.circle(o, R2, stroke=INK, width=1.2, dash='6 4')
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    f.circle(o, 0.5, stroke=ORANGE, width=1.8, dash='5 3')
    s = rad(215)
    f.line(o, shift(o, u(s), 0.5), stroke=ORANGE, width=1.2)
    f.text(shift(shift(o, u(s), 0.27), u(s + math.pi / 2), 0.07), '½',
           color=ORANGE, italic=False)
    f.line(o, far, width=1.2)
    tf = math.atan2(far[1], far[0])
    f.text(shift(shift(o, u(tf), 0.8), u(tf + math.pi / 2), 0.08),
           sb('R', '2'))
    f.dot(far, r=4, fill=INK)
    f.dot(c, fill=BLUE)
    f.text(shift(c, (0.05, -0.05)), sb('c', 'S'), color=BLUE,
           anchor='start')
    f.dot(o)
    f.text((-0.04, 0.07), 'o', anchor='end')
    f.text(frame_point(c, t, 0.26, -0.24), 'S', size=17, color=BLUE)
    f.save('05-two/near', 'A unit square inside the dashed circle of radius R2 '
           'about o, with its farthest vertex on that circle; its centre lies '
           'inside the circle of radius one half about o')


def ab_plane():
    """In the closed quadrant, the disk phi <= 5/4 lies in the quarter disk
    a^2 + b^2 <= 1/4 and meets its boundary only at (1/2, 0) and (0, 1/2)."""
    region = quadrant_disk(1.25, steps=200)
    arc = region[1:]
    assert all(a * a + b * b <= 0.25 + 1e-12 for a, b in region)
    assert abs(arc[0][0] - 0.5) < 1e-12 and abs(arc[0][1]) < 1e-12
    assert abs(arc[-1][0]) < 1e-12 and abs(arc[-1][1] - 0.5) < 1e-12
    assert all(a * a + b * b < 0.25 - 1e-6 for a, b in arc[1:-1])
    f = Figure(-0.1, 0.72, -0.1, 0.72, 480)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    polyline(f, [(0.5 * math.cos(s), 0.5 * math.sin(s))
                 for s in (math.pi / 2 * k / 90 for k in range(91))],
             stroke=ORANGE, width=1.8, dash='6 4')
    ab_axes(f, 0.7)
    f.dot((0.5, 0), r=4.4)
    f.text((0.52, -0.045), '(½, 0)', size=14, italic=False, anchor='start')
    f.dot((0, 0.5), r=4.4)
    f.text((0.025, 0.535), '(0, ½)', size=14, italic=False, anchor='start')
    f.text((0.17, 0.15), 'φ ≤ 5/4', size=16, color=BLUE)
    f.text((0.45, 0.37), 'a² + b² = ¼', size=14, color=ORANGE,
           anchor='start')
    f.save('05-two/ab-plane', 'The (a, b)-plane where a and b are at least 0: '
           'the part of the disk where phi is at most 5/4 lies inside the '
           'dashed quarter circle of radius one half and meets it only at '
           '(1/2, 0) and (0, 1/2)')


def inscribed_disk():
    """Lemma 5.4 in the frame of S: the positions of o for which S fits in
    the closed disk of radius R_2 about o lie in the inscribed disk of S, the
    closed disk of radius 1/2 about c_S, and reach its circle only at the
    midpoints of the four edges."""
    K = 1.25
    region = fit_region(K)
    for p in region:
        assert abs(phi(abs(p[0]), abs(p[1])) - K) < 1e-9
        assert math.hypot(*p) <= 0.5 + 1e-12
    mids = [(0.5, 0.0), (0.0, 0.5), (-0.5, 0.0), (0.0, -0.5)]
    for k in range(720):
        t = 2 * math.pi * k / 720
        on_axis = k % 180 == 0
        assert (abs(fit_radius(K, t) - 0.5) < 1e-12) == on_axis
    assert all(abs(phi(abs(x), abs(y)) - K) < 1e-12 for x, y in mids)
    f = Figure(-0.74, 0.74, -0.74, 0.74, 300)
    f.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    f.circle((0, 0), 0.5, stroke=ORANGE, width=1.8, dash='6 4')
    f.square((0, 0), stroke=INK, width=1.8)
    t = rad(-35)
    f.line((0, 0), shift((0, 0), u(t), 0.5), stroke=ORANGE, width=1.2)
    f.text(shift(shift((0, 0), u(t), 0.3), u(t + math.pi / 2), -0.05), '½',
           color=ORANGE, italic=False)
    for q in mids:
        f.dot(q, r=4.2)
    f.dot((0, 0))
    f.text((-0.03, 0.05), sb('c', 'S'), anchor='end')
    f.text((-0.4, 0.4), 'S', size=17)
    f.save('05-two/inscribed-disk', 'A unit square S in its own frame and the '
           'blue region of the points o for which S fits in the closed disk '
           'of radius R2 about o: a rounded diamond inside the dashed circle '
           'of radius one half about the centre of S, touching it only at the '
           'midpoints of the four edges')


def shared_edge():
    """Step 1 of the proof of Proposition 5.3. The centres are the ends of a
    diameter of the circle of radius 1/2 about o, 1 apart. Left, a square T
    turned against S overlaps it. Right, by Lemma 3.13 the squares share a
    full edge, and its midpoint is o."""
    deg, turn, gap = 20, 25, 2.6
    d, n = u(rad(deg)), u(rad(deg + 90))  # the step c_T - c_S, its normal
    f = Figure(-1.05, gap + 1.05, -0.86, 0.95, 150)
    for k, tdeg in enumerate((deg + turn, deg)):
        o = (k * gap, 0.0)
        cs, ct = shift(o, d, -0.5), shift(o, d, 0.5)
        assert abs(math.dist(cs, ct) - 1) < 1e-12
        S, T = square_corners(cs, deg), square_corners(ct, tdeg)
        f.square(cs, deg, fill=FILLS[0], stroke=BLUE)
        f.square(ct, tdeg, fill=FILLS[2], stroke=GREEN, opacity=0.8)
        if k == 0:
            assert interiors_meet(S, T)
            lens = clip_square(S, ct, tdeg)
            f.polygon(lens, fill=FILLS[1], stroke=ORANGE, width=1.6)
        else:
            assert not interiors_meet(S, T)
            lo, hi = shift(o, n, -0.5), shift(o, n, 0.5)
            assert all(min(math.dist(q, v) for v in S) < 1e-12 and
                       min(math.dist(q, v) for v in T) < 1e-12
                       for q in (lo, hi))
            f.line(lo, hi, width=3.4)
        f.circle(o, 0.5, stroke=INK, width=1.1, dash='5 4')
        f.line(cs, ct, width=1.2)
        for c, name, color, side in ((cs, 'S', BLUE, -1), (ct, 'T', GREEN, 1)):
            f.dot(c, fill=color)
            f.text(shift(shift(c, d, 0.1 * side), n, -0.13), sb('c', name),
                   color=color)
            f.text(shift(shift(c, d, 0.22 * side), n, 0.3), name, size=17,
                   color=color)
        f.dot(o)
        f.text(shift(shift(o, d, -0.13), n, -0.11), 'o')
    f.save('05-two/shared-edge', 'Two panels with the dashed circle of radius '
           'one half about o and two unit squares S and T whose centres are '
           'the ends of a diameter of that circle, 1 apart. Left: T is turned '
           'against S, and the two squares overlap in a shaded region. '
           'Right: T has the sides of S, and the squares share a full edge, '
           'drawn thick, whose midpoint is o')


def frame():
    """Step 2 of the proof of Proposition 5.3. With the frames of S and T
    turned so that e^S_1 = e^T_1 is the step from c_S to c_T, the frame at o
    along that step puts S at (-1/2, 0) = c_1 and T at (1/2, 0) = c_2."""
    deg = 20
    th = rad(deg)
    e1, e2 = u(th), u(th + math.pi / 2)
    o = (0.0, 0.0)
    cs, ct = frame_point(o, th, -0.5, 0), frame_point(o, th, 0.5, 0)
    assert abs(math.dist(cs, ct) - 1) < 1e-12
    # In the frame at o along e1, each square is the axis-parallel square at
    # its slot: a point is in the open square exactly when its coordinates
    # are within 1/2 of the slot.
    for c, slot in ((cs, (-0.5, 0.0)), (ct, (0.5, 0.0))):
        for k in range(400):
            x, y = -1.2 + 2.4 * (k % 20) / 19, -0.8 + 1.6 * (k // 20) / 19
            inside = abs(x - slot[0]) < 0.5 and abs(y - slot[1]) < 0.5
            assert in_open_square(frame_point(o, th, x, y), c, deg) == inside
    f = Figure(-1.42, 1.62, -0.98, 1.12, 165)
    f.square(cs, deg, fill=FILLS[0], stroke=BLUE)
    f.square(ct, deg, fill=FILLS[2], stroke=GREEN)
    f.line(shift(o, e1, -1.38), shift(o, e1, 1.5), stroke=FAINT, width=1,
           dash='5 4', arrow=True)
    f.line(shift(o, e2, -0.95), shift(o, e2, 1.05), stroke=FAINT, width=1,
           dash='5 4', arrow=True)
    f.text(shift(o, e1, 1.58), 'φ', anchor='start')
    for c, name, color, slot in ((cs, 'S', BLUE, '(−½, 0)'),
                                 (ct, 'T', GREEN, '(½, 0)')):
        f.line(c, shift(c, e1, 0.3), width=1.6, arrow=True)
        f.line(c, shift(c, e2, 0.3), width=1.6, arrow=True)
        f.text(shift(shift(c, e1, 0.3), e2, 0.11), subsup('e', '1', name, 14),
               size=14)
        f.text(shift(shift(c, e2, 0.36), e1, -0.1), subsup('e', '2', name, 14),
               size=14)
        f.dot(c, fill=color)
        f.text(shift(c, e2, -0.2), slot, size=14, italic=False, color=color)
        f.text(shift(shift(c, e1, -0.25), e2, -0.3), name, size=17,
               color=color)
    f.dot(o)
    f.text(shift(shift(o, e1, 0.1), e2, -0.12), 'o')
    f.save('05-two/frame', 'The squares S and T with their frames turned so '
           'that the first vector of each points from the centre of S to the '
           'centre of T, and the dashed axes of the frame at o in that '
           'direction, phi; in it S sits at (-1/2, 0) and T at (1/2, 0)')


def main():
    corners()
    near()
    ab_plane()
    inscribed_disk()
    shared_edge()
    frame()


if __name__ == '__main__':
    main()

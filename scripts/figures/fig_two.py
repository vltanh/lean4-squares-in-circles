#!/usr/bin/env python3
"""Draw the figures of Chapter 5, two squares, as SVG files in
docs/proof/figures/05-two/.

    python3 scripts/figures/fig_two.py

Every figure is computed from the geometry it illustrates: arcs held by
squares are found by sampling the circle and testing membership in the open
squares, and the facts that the captions state are checked by assertions.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, square_corners,
                           in_open_square, arcs_in, u, shift, rad, sb,
                           quadrant_disk, ab_axes)
from fig_front import it
from fig_one import label, isb, fit_radius, fit_region

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
    f.line((0, 0), (0.62, 0.62), stroke=FAINT, width=1, dash='3 3')
    f.text((0.63, 0.6), 'a = b', size=13, color=FAINT, anchor='start')
    ab_axes(f, 0.7)
    f.dot((0.5, 0), r=4.4)
    f.text((0.52, -0.045), '(½, 0)', size=14, italic=False, anchor='start')
    f.dot((0, 0.5), r=4, fill=FAINT)
    f.text((0.025, 0.535), '(0, ½)', size=14, italic=False, anchor='start',
           color=FAINT)
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


def edge_midpoint():
    """Two squares with centres at distance 1/2 from o. Left, o is the
    midpoint of an edge, (a_S, b_S) = (1/2, 0), and the far corners lie on
    the circle of radius R_2. Right, a_S = b_S, and the farthest vertex lies
    outside it."""
    deg, gap = 20, 2.75
    t = rad(deg)
    offsets = ((0.5, 0.0), (0.5 / math.sqrt(2), 0.5 / math.sqrt(2)))
    f = Figure(-1.25, gap + 1.3, -1.42, 1.3, 118)
    for k, (x, y) in enumerate(offsets):
        o = (k * gap, 0.0)
        c = frame_point(o, t, x, y)   # the local coordinates of o: (-x, -y)
        assert abs(math.dist(o, c) - 0.5) < 1e-12
        f.circle(o, R2, stroke=INK, width=1.2, dash='6 4')
        f.circle(o, 0.5, stroke=FAINT, width=1.2)
        f.square(c, deg, fill=FILLS[0], stroke=BLUE)
        if k == 0:
            lo = frame_point(c, t, -0.5, -0.5)
            hi = frame_point(c, t, -0.5, 0.5)
            assert math.dist(((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2),
                             o) < 1e-12
            f.line(lo, hi, stroke=BLUE, width=3.4)
            fars = [frame_point(c, t, 0.5, s) for s in (-0.5, 0.5)]
            assert all(abs(math.dist(o, q) - R2) < 1e-12 for q in fars)
            text = ('(' + isb('a', 'S', ', ', 14) +
                    isb('b', 'S', ') = (½, 0)', 14))
            spot = shift(o, (-0.05, -0.08))
        else:
            fars = [frame_point(c, t, 0.5, 0.5)]
            assert math.dist(o, fars[0]) ** 2 > 1.25
            assert abs(math.dist(o, fars[0]) ** 2 - phi(x, y)) < 1e-12
            text = isb('a', 'S', ' = ', 14) + isb('b', 'S', ' = √2/4', 14)
            spot = shift(o, (-0.05, 0.07))
        for q in fars:
            f.dot(q, r=4.2, fill=ORANGE)
        f.dot(c, fill=BLUE)
        f.text(shift(c, (0.05, -0.07)), sb('c', 'S'), color=BLUE,
               anchor='start')
        f.dot(o)
        f.text(spot, 'o', anchor='end')
        label(f, (o[0], -1.33), text, size=14, italic=False)
    f.save('05-two/edge-midpoint', 'Two unit squares with centres at distance '
           'one half from o. Left: o is the midpoint of an edge, and the two '
           'far corners lie on the dashed circle of radius R2. Right: the '
           'centre is off the axes seen from o, and the farthest vertex lies '
           'outside that circle')


def half_circle():
    """A square with (a_S, b_S) = (1/2, 0), in its chart, holds the half of
    the circle of radius 1/2 on its side of the edge through o."""
    r, c = 0.5, (0.5, 0.0)
    runs = arcs_in(lambda p: in_open_square(p, c), r)
    assert len(runs) == 1 and abs(runs[0][1] - runs[0][0] - math.pi) < 2e-3
    t = rad(52)
    q = shift((0, 0), u(t), r)
    assert in_open_square(q, c)
    f = Figure(-0.78, 1.22, -0.66, 0.66, 290)
    f.square(c, fill=FILLS[0], stroke=BLUE)
    f.line((-0.76, 0), (1.2, 0), stroke=FAINT, width=1)
    label(f, (1.2, 0.05), it('t') + ' = 0', size=13, color=FAINT,
          italic=False, anchor='end')
    f.circle((0, 0), r)
    for t0, t1 in runs:
        f.arc((0, 0), r, t0, t1, BLUE, width=5)
    f.line((0, -0.5), (0, 0.5), width=2.6)
    f.line((0, 0), q, width=1)
    f.arc((0, 0), 0.17, 0, t, ORANGE, width=1.6)
    f.text(shift((0, 0), u(t / 2), 0.25), 't', color=ORANGE)
    f.dot(q, r=4, fill=ORANGE)
    for s in (0.5, -0.5):
        f.dot((0, s))
    label(f, (-0.04, 0.56), it('t') + ' = π/2', size=13, italic=False,
          anchor='end')
    label(f, (-0.04, -0.57), it('t') + ' = −π/2', size=13, italic=False,
          anchor='end')
    f.dot(c, fill=BLUE)
    f.text(shift(c, (0.04, -0.06)), '(½, 0)', size=14, italic=False,
           color=BLUE, anchor='start')
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text((0.78, 0.3), 'S', size=17, color=BLUE)
    f.text(shift((0, 0), u(rad(215)), 0.64), sb('Γ', '1/2', size=16),
           size=16)
    f.save('05-two/half-circle', 'A square with (a, b) = (1/2, 0) in its chart: '
           'o is the midpoint of its near edge, and the half of the circle of '
           'radius one half about o on the side of the square, from chart '
           'angle minus pi/2 to pi/2, lies in the open square')


def opposite():
    """The half circles held by S and T on the circle of radius 1/2. Left,
    their centres are less than pi apart: they share a point p, which lies in
    both squares. Right, the centres are opposite: the rectangle."""
    r, gap = 0.5, 2.75
    ts = rad(20)
    f = Figure(-1.3, gap + 1.3, -1.42, 1.3, 118)
    for k, tt in enumerate((rad(150), ts + math.pi)):
        o = (k * gap, 0.0)
        cs, ct = shift(o, u(ts), 0.5), shift(o, u(tt), 0.5)
        ds, dt = math.degrees(ts), math.degrees(tt)
        runs = [arcs_in(lambda p: in_open_square(shift(p, o), cs, ds), r),
                arcs_in(lambda p: in_open_square(shift(p, o), ct, dt), r)]
        for run in runs:
            assert len(run) == 1
            assert abs(run[0][1] - run[0][0] - math.pi) < 2e-3
        f.square(cs, ds, fill=FILLS[0], stroke=BLUE, opacity=0.7)
        f.square(ct, dt, fill=FILLS[2], stroke=GREEN, opacity=0.7)
        f.circle(o, r)
        for (t0, t1), color, width in ((runs[0][0], BLUE, 8),
                                       (runs[1][0], GREEN, 4)):
            f.arc(o, r, t0, t1, color, width=width)
        for tc, name, color in ((ts, 'S', BLUE), (tt, 'T', GREEN)):
            f.line(o, shift(o, u(tc), r + 0.2), stroke=color, width=1.2,
                   dash='4 3')
            f.text(shift(o, u(tc), r + 0.32), sb('θ', name), color=color)
        if k == 0:
            p = shift(o, u((ts + math.pi / 2 + tt - math.pi / 2) / 2), r)
            assert in_open_square(p, cs, ds) and in_open_square(p, ct, dt)
            f.dot(p, r=4.2)
            f.text(shift(p, (0.06, 0.08)), 'p', anchor='start')
            relation = ') &lt; π'
        else:
            samples = [shift(o, u(math.pi * j / 360), r) for j in range(720)]
            assert not any(in_open_square(q, cs, ds) and
                           in_open_square(q, ct, dt) for q in samples)
            relation = ') = π'
        text = (it('d') + '(' + isb('θ', 'S', ', ', 14) +
                isb('θ', 'T', relation, 14))
        f.dot(o)
        f.text(shift(o, (-0.06, -0.08)), 'o', anchor='end')
        label(f, (o[0], -1.33), text, size=14, italic=False)
    f.save('05-two/opposite', 'The half circles held by two squares on the '
           'circle of radius one half about o. Left: their centres are less '
           'than pi apart, the half circles share a point p, and the squares '
           'overlap. Right: the centres are opposite, and the squares form '
           'the rectangle')


def frame():
    """The final frame: S sits at (1/2, 0) in the frame theta_S, and T at
    (1/2, 0) in the frame theta_S + pi, that is at (-1/2, 0) in the frame
    theta_S."""
    deg = 25
    th = rad(deg)
    o = (0.0, 0.0)
    cs, ct = frame_point(o, th, 0.5, 0), frame_point(o, th + math.pi, 0.5, 0)
    assert math.dist(ct, frame_point(o, th, -0.5, 0)) < 1e-12
    f = Figure(-1.55, 1.55, -1.12, 1.18, 165)
    f.square(cs, deg, fill=FILLS[0], stroke=BLUE)
    f.square(ct, deg, fill=FILLS[2], stroke=GREEN)
    f.line(o, shift(o, u(th), 1.4), width=1.3, arrow=True)
    f.line(o, shift(o, u(th + math.pi / 2), 1.0), width=1.3, arrow=True)
    f.line(o, shift(o, u(th + math.pi), 1.4), width=1.3, dash='5 4',
           arrow=True)
    f.line(o, shift(o, u(th - math.pi / 2), 1.0), width=1.3, dash='5 4',
           arrow=True)
    f.text(shift(o, u(th), 1.48), sb('θ', 'S'), anchor='start')
    label(f, shift(o, u(th + math.pi), 1.48), sb('θ', 'S', ' + π'),
          anchor='end')
    f.dot(cs, fill=BLUE)
    f.dot(ct, fill=GREEN)
    f.text(shift(cs, (0.02, -0.1)), '(½, 0)', size=14, italic=False,
           color=BLUE, anchor='start')
    f.text(shift(ct, (-0.02, 0.1)), '(−½, 0)', size=14, italic=False,
           color=GREEN, anchor='end')
    f.dot(o)
    f.text((0.03, 0.1), 'o', anchor='start')
    f.text(frame_point(cs, th, 0.2, 0.25), 'S', size=17, color=BLUE)
    f.text(frame_point(ct, th, -0.2, -0.25), 'T', size=17, color=GREEN)
    f.save('05-two/frame', 'The two squares in the frame at o turned by theta '
           'S (solid axes), where S sits at (1/2, 0) and T at (-1/2, 0); in '
           'the opposite frame, turned by theta S plus pi (dashed axes), T '
           'sits at (1/2, 0)')


def main():
    corners()
    near()
    ab_plane()
    inscribed_disk()
    edge_midpoint()
    half_circle()
    opposite()
    frame()


if __name__ == '__main__':
    main()

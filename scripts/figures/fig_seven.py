#!/usr/bin/env python3
"""Draw the figures of Chapter 10 (seven squares) as SVG files in
docs/proof/figures/10-seven/.

    python3 scripts/figures/fig_seven.py

Every figure is computed from the definitions of the chapter: states and
labels, the canonical pair of two states, its support sums, and the column
packings. Squares, arcs and regions are sampled or clipped from that geometry.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, subsup, clip, clip_square, convex_hull)
from fig_front import it, sbn, RED, RED_FILL, NB
from fig_appa import Plot, x_axis, y_axis

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK = COLORS[:5]


def state0(size=14):
    """The markup of the transition state (a_0, b_0)."""
    return '(' + sbn('a', '0', ', ', size) + sbn('b', '0', ')', size)


L7 = math.sqrt(3) - 0.5          # the column limit sqrt 3 - 1/2
R7 = math.sqrt(13) / 2           # the optimal radius
ARC = 1 / 2                      # half-width of the marker arc


# ---------------------------------------------------------------- the model

def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def axial(b):
    return 1.25 * b


def side(a, b):
    return PI / 6 + (b - 0.5) / 3 + 0.75 * (1 - a)


def label(a, b):
    return min(axial(b), side(a, b), PI / 4)


def admissible(a, b):
    return a >= 0.5 and 0 <= b <= a and phi(a, b) <= 13 / 4 + 1e-12


def support(a, b, z):
    return (a * math.cos(z) + b * math.sin(z)
            + (abs(math.cos(z)) + abs(math.sin(z))) / 2)


def rot(p, d):
    return (p[0] * math.cos(d) - p[1] * math.sin(d),
            p[0] * math.sin(d) + p[1] * math.cos(d))


def pair(a, b, A, B, s, t, g):
    """The canonical pair: centre of S, centre of T, relative phase d."""
    d = g + s * label(a, b) - t * label(A, B)
    return (a, s * b), rot((A, t * B), d), d


def sigma(a, b, A, B, s, t, k, g):
    d = g + s * label(a, b) - t * label(A, B)
    return (support(a, s * b, k * PI / 2)
            + support(A, t * B, k * PI / 2 + PI - d))


def in_closed(p, c, deg=0.0, eps=1e-9):
    t = math.radians(deg)
    dx, dy = p[0] - c[0], p[1] - c[1]
    x = math.cos(t) * dx + math.sin(t) * dy
    y = -math.sin(t) * dx + math.cos(t) * dy
    return abs(x) <= 0.5 + eps and abs(y) <= 0.5 + eps


def overlap(P, Q):
    """Whether two convex polygons have overlapping interiors."""
    for poly in (P, Q):
        for i in range(len(poly)):
            a, b = poly[i], poly[(i + 1) % len(poly)]
            n = (b[1] - a[1], a[0] - b[0])
            pa = [n[0] * x + n[1] * y for x, y in P]
            pb = [n[0] * x + n[1] * y for x, y in Q]
            if max(pa) <= min(pb) + 1e-12 or max(pb) <= min(pa) + 1e-12:
                return False
    return True


# ------------------------------------------------------------ small helpers

def polyline(f, pts, stroke=INK, width=1.5, dash=None, fill='none'):
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="{fill}" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')


def thin_arc(f, c, r, t0, t1, stroke=FAINT, width=1.2, dash=None, n=180):
    pts = [shift(c, u(t0 + (t1 - t0) * k / n), r) for k in range(n + 1)]
    polyline(f, pts, stroke=stroke, width=width, dash=dash)


def bracket(f, p, q, text, side=1, stroke=INK, size=14, off=0.07,
            color=None, anchor='middle'):
    """A dimension bar from p to q with end ticks, and a label beside it."""
    dx, dy = q[0] - p[0], q[1] - p[1]
    n = math.hypot(dx, dy)
    nx, ny = -dy / n * side, dx / n * side
    tick = 0.035
    f.line(p, q, stroke=stroke, width=2)
    for e in (p, q):
        f.line(shift(e, (nx, ny), tick), shift(e, (nx, ny), -tick),
               stroke=stroke, width=1.6)
    mid = ((p[0] + q[0]) / 2 + nx * off, (p[1] + q[1]) / 2 + ny * off)
    f.text(mid, text, size=size, color=color or stroke, anchor=anchor)


def region_polygon(steps=160):
    """The admissible states as a convex polygon in the (a, b)-plane."""
    diag = math.sqrt(13 / 8) - 0.5
    arc = []
    t_lo = math.atan2(0.5, L7 + 0.5)            # the point (L7, 0)
    t_hi = math.atan2(diag + 0.5, diag + 0.5)   # the diagonal point
    for k in range(steps + 1):
        t = t_lo + (t_hi - t_lo) * k / steps
        arc.append((-0.5 + R7 * math.cos(t), -0.5 + R7 * math.sin(t)))
    return [(0.5, 0.0)] + arc + [(0.5, 0.5)]


def plane_axes(f, amax, bmax, ticks_a=(), ticks_b=()):
    f.line((0.38, 0), (amax, 0), width=1, arrow=True)
    f.line((0.42, -0.06), (0.42, bmax), width=1, arrow=True)
    f.text((amax, -0.05), 'a', anchor='end')
    f.text((0.39, bmax - 0.02), 'b', anchor='end')
    for x, s in ticks_a:
        f.line((x, -0.015), (x, 0.015), width=1.2)
        f.text((x, -0.055), s, size=13, italic=False)
    for y, s in ticks_b:
        f.line((0.405, y), (0.435, y), width=1.2)
        f.text((0.39, y), s, size=13, italic=False, anchor='end')


def transition_state():
    M = 2 * PI + 17
    J = math.sqrt(202 * 13 / 4 - M * M)
    return (9 * M + 11 * J) / 202 - 0.5, (11 * M - 9 * J) / 202 - 0.5


def first_exit(p, q, inside, steps=4000):
    """The last point of the segment from p towards q before it leaves."""
    last = p
    for k in range(1, steps + 1):
        x = (p[0] + (q[0] - p[0]) * k / steps, p[1] + (q[1] - p[1]) * k / steps)
        if not inside(x):
            return last
        last = x
    return last


# ------------------------------------------------------------------ figures

def columns():
    heights = [(-L7, -L7 + 1, -L7 + 2), (-L7, 0.0, L7), (L7 - 2, L7 - 1, L7)]
    names = ['pushed down', 'spread out', 'pushed up']
    gap = 2 * R7 + 0.35
    m = R7 + 0.06
    f = Figure(-m, -m + 3 * gap - 0.35 + 0.12, -m - 0.28, m, 62)
    sides = [(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5)]
    for j, (y1, y2, y3) in enumerate(heights):
        # check the heights and the packing
        assert -L7 - 1e-12 <= y1 and y1 + 1 <= y2 + 1e-12
        assert y2 + 1 <= y3 + 1e-12 and y3 <= L7 + 1e-12
        o = (j * gap, 0.0)
        cs = sides + [(0, y1), (0, y2), (0, y3)]
        for k, c in enumerate(cs):
            for x, y in square_corners(c):
                assert x * x + y * y <= 13 / 4 + 1e-9
        f.circle(o, R7, stroke=INK, width=1.2, dash='6 4')
        for k, c in enumerate(cs):
            fill = GREY if k == 5 else FILLS[k]
            stroke = FAINT if k == 5 else COLORS[k]
            f.square(shift(o, c), fill=fill, stroke=stroke, width=1.3)
        f.dot(o, r=2.6)
        f.text(shift(o, (0.08, -0.13)), 'o', size=13, anchor='start')
        f.text(shift(o, (0, -m - 0.14)), names[j], size=13, italic=False)
    f.save('10-seven/columns', 'Three column packings: the middle column pushed '
           'down, spread out and pushed up, between the same two side columns')


def states():
    poly = region_polygon()
    a0, b0 = transition_state()
    f = Figure(0.3, 1.45, -0.14, 0.92, 420)
    f.polygon(poly, fill=FILLS[0], stroke=BLUE, width=1.6)
    # the tangent line r = 0 at the side state
    f.line((0.9, (4 - 3 * 0.9) / 2), (1.32, (4 - 3 * 1.32) / 2),
           stroke=ORANGE, width=1.6, dash='6 4')
    f.text((1.31, 0.09), 'r = 0', size=14, color=ORANGE, anchor='start')
    # the axial states
    f.line((0.5, 0), (L7, 0), stroke=GREEN, width=5)
    f.text(((0.5 + L7) / 2, 0.04), 'axial states', size=13, italic=False,
           color=GREEN)
    plane_axes(f, 1.43, 0.9, ticks_a=((0.5, '½'), (1.0, '1'), (L7, '√3 − ½')),
               ticks_b=((0.5, '½'),))
    f.dot((1.0, 0.5), r=4, fill=ORANGE)
    f.text((1.03, 0.54), 'side state (1, ½)', size=13, italic=False,
           anchor='start', color=ORANGE)
    f.dot((a0, b0), r=4)
    f.text((a0 + 0.045, b0 + 0.02), state0(14), size=14, anchor='start')
    f.text((0.84, 0.8), 'φ = 13/4', size=14, color=BLUE, anchor='start')
    f.text((0.6, 0.64), 'b = a', size=14, color=FAINT, anchor='end')
    f.text((0.68, 0.22), 'admissible', size=14, italic=False, color=BLUE)
    f.save('10-seven/states', 'The admissible states in the (a, b)-plane, the '
           'side state with the tangent line r = 0, the axial segment and the '
           'transition state')


def labels():
    poly = region_polygon()
    a0, b0 = transition_state()
    tie = 2 * PI + 7
    ax = clip(clip(poly, 0, 1, PI / 5), 9, 11, tie)
    sd = clip(clip(poly, -9, -11, -tie), -9, 4, -(7 - PI))
    cp = clip(clip(poly, 0, -1, -PI / 5), 9, -4, 7 - PI)
    f = Figure(0.3, 1.45, -0.14, 0.92, 420)
    f.polygon(ax, fill=FILLS[2], stroke='none')
    f.polygon(sd, fill=FILLS[1], stroke='none')
    f.polygon(cp, fill=GREY, stroke='none')
    inside = lambda p: admissible(p[0], p[1])
    # level lines of the label
    for j in range(1, 8):
        c = j / 10
        y = 0.8 * c
        if c >= PI / 4:
            continue
        x_tie = (tie - 11 * y) / 9
        start = (max(0.5, y), y)
        end = first_exit(start, (x_tie, y), inside)
        polyline(f, [start, end], stroke=INK, width=0.8)
        f.text((start[0] - 0.012, y), f'{c:.1f}', size=12, italic=False,
               anchor='end', color=INK)
        if inside((x_tie, y)):
            # the side part: 9a - 4b = 2pi + 7 - 12c, upwards from the tie
            top = (x_tie + 4 * 0.5 / 9, y + 0.5)
            polyline(f, [(x_tie, y), first_exit((x_tie, y), top, inside)],
                     stroke=INK, width=0.8)
    # the three dividing lines inside the region, through the triple point
    triple = ((7 - PI / 5) / 9, PI / 5)
    polyline(f, [triple, (a0, b0)], stroke=INK, width=1.6)
    polyline(f, [(PI / 5, PI / 5), triple], stroke=INK, width=1.6)
    dg = ((7 - PI) / 5, (7 - PI) / 5)
    polyline(f, [triple, dg], stroke=INK, width=1.6)
    f.polygon(poly, stroke=BLUE, width=1.6)
    plane_axes(f, 1.43, 0.9, ticks_a=((0.5, '½'), (1.0, '1'), (L7, '√3 − ½')),
               ticks_b=((0.5, '½'),))
    ell = it('ℓ') + NB + '=' + NB
    f.text((0.78, 0.14), 'axial:' + NB + ell + '5' + it('b') + '/4', size=13,
           italic=False, color=GREEN)
    f.text((1.1, 0.66), 'side:' + NB + ell + 'side(' + it('a') + ',' + NB
           + it('b') + ')', size=13, italic=False, color=ORANGE,
           anchor='start')
    f.line((1.1, 0.64), (0.95, 0.53), stroke=ORANGE, width=1)
    f.text((0.6, 0.83), 'capped:' + NB + ell + 'π/4', size=13, italic=False,
           color=INK, anchor='start')
    f.line((0.68, 0.81), (0.705, 0.69), stroke=INK, width=1)
    f.dot((1.0, 0.5), r=3.6, fill=ORANGE)
    f.dot((a0, b0), r=3.6)
    f.text((a0 + 0.045, b0 + 0.0), state0(13), size=13, anchor='start')
    f.save('10-seven/labels', 'The three label regions of the admissible states, '
           'axial, side and capped, with level lines of the label')


def marker():
    a, b = 1.0, 0.45
    lab = label(a, b)
    assert admissible(a, b) and abs(lab - side(a, b)) < 1e-12
    theta, eps = rad(24), -1
    off = 2.55
    f = Figure(-0.45, off + 1.75, -1.05, 1.12, 175)
    # left panel: the square as seen from o
    o = (0.0, 0.0)
    c = rot((a, eps * b), theta)
    deg = math.degrees(theta)
    mu = theta + eps * lab
    f.square(c, deg, fill=FILLS[0], stroke=BLUE)
    thin_arc(f, o, 1.0, rad(-75), rad(95))
    member = lambda p: in_open_square(p, c, deg)
    for t0, t1 in arcs_in(member, 1.0):
        f.arc(o, 1.0, t0, t1, BLUE, width=2.2)
    for t in (mu - ARC, mu, mu + ARC):
        assert in_closed(u(t), c, deg)
    f.arc(o, 1.0, mu - ARC, mu + ARC, ORANGE, width=5)
    f.line(o, shift(o, u(theta), 1.55), stroke=INK, width=1.1, dash='5 4')
    f.line(o, shift(o, u(mu), 1.3), stroke=ORANGE, width=1.6)
    f.text(shift(o, u(theta), 1.63), sb('θ', 'S'), anchor='start')
    f.text(shift(o, u(mu), 1.4), sb('μ', 'S'), anchor='start', color=ORANGE)
    f.arc(o, 0.3, mu, theta, INK, width=1.2)
    f.text(shift(o, u((mu + theta) / 2), 0.42), 'ℓ', size=14)
    f.dot(o)
    f.text((-0.05, -0.07), 'o', anchor='end')
    f.text(shift(c, (0.22, -0.28)), 'S', size=17, color=BLUE)
    f.text((0.35, -0.95), sb('Γ', '1'), size=15)
    # right panel: its chart
    o2 = (off, 0.0)
    c2 = shift(o2, (a, b))
    f.line(o2, shift(o2, (1.72, 0)), stroke=FAINT, width=1, dash='5 4')
    f.text(shift(o2, (1.72, -0.07)), it('t') + NB + '=' + NB + '0', size=13,
           italic=False, color=FAINT, anchor='end')
    f.square(c2, fill=FILLS[0], stroke=BLUE)
    thin_arc(f, o2, 1.0, rad(-75), rad(95))
    member2 = lambda p: in_open_square(shift(p, o2), c2)
    for t0, t1 in arcs_in(member2, 1.0):
        f.arc(o2, 1.0, t0, t1, BLUE, width=2.2)
    for t in (lab - ARC, lab, lab + ARC):
        assert in_closed(shift(o2, u(t)), c2)
    f.arc(o2, 1.0, lab - ARC, lab + ARC, ORANGE, width=5)
    for t in (lab - ARC, lab + ARC):
        f.line(o2, shift(o2, u(t), 1.0), stroke=ORANGE, width=0.9)
    f.line(o2, shift(o2, u(lab), 1.3), stroke=ORANGE, width=1.6)
    f.arc(o2, 0.3, 0, lab, INK, width=1.2)
    f.text(shift(o2, u(lab / 2), 0.41), 'ℓ', size=14)
    # the half-width 1/2 of the arc, as an angle at o
    f.arc(o2, 0.48, lab, lab + ARC, INK, width=1.2)
    half = shift(o2, u(lab + ARC / 2), 0.58)
    assert half[0] + 0.03 < c2[0] - 0.5          # left of the square
    f.text(half, '½', size=14, italic=False)
    f.dot(c2, fill=BLUE)
    f.text(shift(c2, (0.04, -0.07)), '(' + it('a') + ',' + NB + it('b') + ')',
           size=13, italic=False, anchor='start', color=BLUE)
    f.dot(o2)
    f.text(shift(o2, (-0.05, -0.07)), 'o', anchor='end')
    f.save('10-seven/marker', 'An exterior square seen from the disk centre with '
           'its phase and marker, and the same square in its chart; the arc '
           'of the unit circle of half-width 1/2 about the marker lies in '
           'the closed square')


CP = dict(a=1.1, b=0.2, A=1.0, B=0.4, s=1, t=-1, g=1.6)


def canonical():
    a, b, A, B, s, t, g = (CP[k] for k in ('a', 'b', 'A', 'B', 's', 't', 'g'))
    assert admissible(a, b) and admissible(A, B)
    cS, cT, d = pair(a, b, A, B, s, t, g)
    dg = math.degrees(d)
    PS, PT = square_corners(cS), square_corners(cT, dg)
    assert not overlap(PS, PT)
    f = Figure(-1.5, 1.95, -1.2, 1.95, 150)
    thin_arc(f, (0, 0), 1.0, rad(-30), rad(150))
    f.square(cS, fill=FILLS[0], stroke=BLUE)
    f.square(cT, dg, fill=FILLS[2], stroke=GREEN)
    m1, m2 = s * label(a, b), s * label(a, b) + g
    for m, color in ((m1, BLUE), (m2, GREEN)):
        f.line((0, 0), u(m), stroke=color, width=1.6)
    f.arc((0, 0), 0.22, m1, m2, INK, width=1.2)
    # off the bisector, away from the label of n_2
    f.text(shift((0, 0), u((m1 + m2) / 2 + 0.25), 0.33), 'g', size=15)
    # the four normals of S
    mids = [(cS[0] + 0.5, cS[1]), (cS[0], cS[1] + 0.5), (cS[0] - 0.5, cS[1]),
            (cS[0], cS[1] - 0.5)]
    for k, p in enumerate(mids):
        q = shift(p, u(k * PI / 2), 0.26)
        f.line(p, q, stroke=INK, width=1.4, arrow=True)
        pos = (q[0] + 0.03, q[1] + 0.13) if k == 2 else shift(
            q, u(k * PI / 2), 0.12)
        f.text(pos, sb('n', str(k), size=14), size=14)
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text(shift(cS, (0.28, -0.27)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.05, 0.1)), 'T', size=17, color=GREEN)
    # shadows on the first axis (below) and on the second axis (left)
    xs_S = (min(x for x, _ in PS), max(x for x, _ in PS))
    xs_T = (min(x for x, _ in PT), max(x for x, _ in PT))
    ys_S = (min(y for _, y in PS), max(y for _, y in PS))
    ys_T = (min(y for _, y in PT), max(y for _, y in PT))
    yb, yb2 = -0.85, -0.95
    f.line((-1.45, yb), (1.9, yb), stroke=FAINT, width=1)
    f.line((xs_S[0], yb), (xs_S[1], yb), stroke=BLUE, width=5)
    f.line((xs_T[0], yb2), (xs_T[1], yb2), stroke=GREEN, width=5)
    for x in (xs_S[0], xs_T[1]):
        f.line((x, yb2 - 0.05), (x, max(ys_S[0], -0.3)), stroke=FAINT,
               width=0.8, dash='3 3')
    s2 = xs_T[1] - xs_S[0]
    assert abs(s2 - sigma(a, b, A, B, s, t, 2, g)) < 1e-9 and s2 < 0
    f.text(((xs_S[0] + xs_T[1]) / 2, yb2 - 0.14),
           sbn('σ', '2', ' &lt; 0', size=14), size=14)
    xl, xl2 = -1.25, -1.35
    f.line((xl, -0.4), (xl, 1.9), stroke=FAINT, width=1)
    f.line((xl, ys_S[0]), (xl, ys_S[1]), stroke=BLUE, width=5)
    f.line((xl2, ys_T[0]), (xl2, ys_T[1]), stroke=GREEN, width=5)
    s1 = ys_S[1] - ys_T[0]
    assert abs(s1 - sigma(a, b, A, B, s, t, 1, g)) < 1e-9 and s1 > 0
    bracket(f, (xl + 0.1, ys_T[0]), (xl + 0.1, ys_S[1]), sb('σ', '1', size=14),
            side=-1, off=0.08, anchor='start')
    for y in (ys_S[1], ys_T[0]):
        f.line((xl2 - 0.04, y), (xl + 0.2, y), stroke=FAINT, width=0.8,
               dash='3 3')
    f.save('10-seven/canonical-pair', 'A canonical pair with its markers a gap g '
           'apart, the four normals of S, and the shadows of the two squares '
           'on the two axes of S')


def octagon():
    a, b, A, B, s, t, g = (CP[k] for k in ('a', 'b', 'A', 'B', 's', 't', 'g'))
    cS, cT, d = pair(a, b, A, B, s, t, g)
    dg = math.degrees(d)
    W = (1 + abs(math.cos(d)) + abs(math.sin(d))) / 2
    D = (cT[0] - cS[0], cT[1] - cS[1])
    off = 3.8
    f = Figure(-1.25, off + 1.9, -1.85, 1.85, 106)
    # left panel: the pair and Delta
    f.square(cS, fill=FILLS[0], stroke=BLUE)
    f.square(cT, dg, fill=FILLS[2], stroke=GREEN)
    f.dot(cS, fill=BLUE)
    f.dot(cT, fill=GREEN)
    f.line(cS, cT, stroke=INK, width=1.6, arrow=True)
    mid = ((cS[0] + cT[0]) / 2, (cS[1] + cT[1]) / 2)
    nrm = math.hypot(D[0], D[1])
    f.text(shift(mid, (-D[1] / nrm, D[0] / nrm), -0.15), 'Δ', size=15)
    f.text(shift(cS, (0.28, -0.27)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.05, 0.12)), 'T', size=17, color=GREEN)
    # right panel: the octagon K centred at O
    O = (off, 0.0)
    K = convex_hull([(p[0] + q[0], p[1] + q[1])
                     for p in square_corners((0, 0))
                     for q in square_corners((0, 0), dg)])
    f.polygon([shift(O, p) for p in K], fill=FILLS[1], stroke=ORANGE,
              width=1.6)
    # the axes of S are n_0, ..., n_3; those of T are +-e^T_1, +-e^T_2
    normals = [(k * PI / 2, sb('n', str(k), size=13)) for k in range(4)]
    normals += [(d, subsup('e', '1', 'T', 13)), (d + PI, '−' + subsup('e', '1', 'T', 13)),
                (d + PI / 2, subsup('e', '2', 'T', 13)),
                (d + 3 * PI / 2, '−' + subsup('e', '2', 'T', 13))]
    for ang, name in normals:
        n = u(ang)
        foot = shift(O, n, W)
        tang = (-n[1], n[0])
        f.line(shift(foot, tang, -0.95), shift(foot, tang, 0.95),
               stroke=FAINT, width=0.9, dash='4 3')
        f.line(foot, shift(foot, n, 0.3), stroke=INK, width=1.2, arrow=True)
        f.text(shift(foot, n, 0.45), name, size=13)
    PD = shift(O, D)
    f.dot(O)
    f.line(O, PD, stroke=INK, width=1.4, arrow=True)
    f.dot(PD, r=3.6)
    f.text(shift(PD, (-0.08, 0.1)), 'Δ', size=15, anchor='end')
    # the support sum on the inward axis: the distance to the line x = -W
    s2 = W + D[0]
    assert abs(s2 - sigma(a, b, A, B, s, t, 2, g)) < 1e-9 and s2 < 0
    y0 = PD[1] - 0.22
    f.line((O[0] - W, y0), (PD[0], y0), stroke=BLUE, width=2.4)
    for x in (O[0] - W, PD[0]):
        f.line((x, y0 - 0.05), (x, y0 + 0.05), stroke=BLUE, width=1.4)
    f.text((PD[0] - 0.06, y0), sbn('σ', '2', ' &lt; 0', size=13), size=13,
           color=BLUE, anchor='end')
    f.text(shift(O, (0.55, -0.55)), 'K', size=17, color=ORANGE)
    f.save('10-seven/octagon', 'The canonical pair with the vector Delta between '
           'the centres, and the octagon of differences of the two squares, '
           'whose eight edges are perpendicular to the edge directions of the '
           'two squares; Delta lies outside it beyond one edge')


def contacts():
    A_axial = 1.0                  # the axial states (A, 0) and (a, 0) of the caption
    specs = [
        # (a, b, s), (A, B, t): kinds (1), (2), (3)
        ((1.0, 0.5, -1), (1.0, 0.5, 1), 1),
        ((1.0, 0.5, 1), (A_axial, 0.0, 1), 2),
        ((A_axial, 0.0, 1), (1.0, 0.5, -1), 1),
    ]
    off = 2.55
    f = Figure(-0.75, 2 * off + 1.75, -1.15, 1.72, 108)
    for j, ((a, b, s), (A, B, t), k) in enumerate(specs):
        o = (j * off, 0.0)
        cS, cT, d = pair(a, b, A, B, s, t, PI / 3)
        dg = math.degrees(d)
        assert abs(sigma(a, b, A, B, s, t, k, PI / 3)) < 1e-12
        PS, PT = square_corners(cS), square_corners(cT, dg)
        assert not overlap(PS, PT)
        thin_arc(f, o, 1.0, rad(-68), rad(112))
        f.square(shift(o, cS), fill=FILLS[0], stroke=BLUE)
        f.square(shift(o, cT), dg, fill=FILLS[2], stroke=GREEN)
        # the shared edge: the common part of the two boundaries
        n = u(k * PI / 2)
        level = max(p[0] * n[0] + p[1] * n[1] for p in PS)
        edge_S = [p for p in PS if abs(p[0] * n[0] + p[1] * n[1] - level) < 1e-9]
        edge_T = [p for p in PT if abs(p[0] * n[0] + p[1] * n[1] - level) < 1e-9]
        tang = (-n[1], n[0])
        lo = max(min(p[0] * tang[0] + p[1] * tang[1] for p in e)
                 for e in (edge_S, edge_T))
        hi = min(max(p[0] * tang[0] + p[1] * tang[1] for p in e)
                 for e in (edge_S, edge_T))
        p0 = (n[0] * level + tang[0] * lo, n[1] * level + tang[1] * lo)
        p1 = (n[0] * level + tang[0] * hi, n[1] * level + tang[1] * hi)
        f.line(shift(o, p0), shift(o, p1), stroke=INK, width=4)
        m1 = s * label(a, b)
        for m, color in ((m1, BLUE), (m1 + PI / 3, GREEN)):
            f.line(o, shift(o, u(m), 1.0), stroke=color, width=1.5)
        f.arc(o, 0.2, m1, m1 + PI / 3, INK, width=1.2)
        f.text(shift(o, u(m1 + PI / 6), 0.36), 'π/3', size=13, italic=False)
        f.dot(o)
        f.text(shift(o, (-0.05, -0.08)), 'o', anchor='end')
        f.text(shift(o, shift(cS, (0.3, -0.3))), 'S', size=16, color=BLUE)
        f.text(shift(o, shift(cT, (-0.3, 0.3))), 'T', size=16, color=GREEN)
        f.text(shift(o, (0.5, 1.62)), f'({j + 1})', size=15, italic=False)
    f.save('10-seven/contacts', 'The three kinds of contact as canonical pairs '
           'at the gap pi/3: two side squares, a side square and an axial '
           'square, an axial square and a side square')


def small_gaps():
    a, b, A, B, s, t, g = 1.0, 0.45, 1.05, 0.25, 1, -1, 0.8
    assert admissible(a, b) and admissible(A, B)
    cS, cT, d = pair(a, b, A, B, s, t, g)
    dg = math.degrees(d)
    lam = s * label(a, b)
    f = Figure(-1.05, 1.75, -0.35, 1.75, 175)
    thin_arc(f, (0, 0), 1.0, rad(-20), rad(150))
    f.square(cS, fill=FILLS[0], stroke=BLUE, opacity=0.75)
    f.square(cT, dg, fill=FILLS[2], stroke=GREEN, opacity=0.75)
    for m, color in ((lam, BLUE), (lam + g, GREEN)):
        for tt in (m - ARC, m, m + ARC):
            p = u(tt)
            ok = in_closed(p, cS) if color == BLUE else in_closed(p, cT, dg)
            assert ok
        f.arc((0, 0), 1.0, m - ARC, m + ARC, color, width=5)
        f.line((0, 0), u(m), stroke=color, width=1.3)
    lo, hi = lam + g - ARC, lam + ARC
    f.arc((0, 0), 1.0, lo, hi, ORANGE, width=8)
    mid = lam + g / 2
    f.line((0, 0), shift((0, 0), u(mid), 1.3), stroke=ORANGE, width=1.2,
           dash='4 3')
    f.text(shift((0, 0), u(mid), 1.4), 'm', size=15, color=ORANGE)
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text(shift(cS, (0.3, -0.3)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.3, 0.35)), 'T', size=17, color=GREEN)
    f.save('10-seven/small-gaps', 'The marker arcs of a canonical pair at a gap '
           'below 1 overlap around the midpoint of the markers')


def leftmost():
    def fval(y):
        """Falls from 0.62 to -0.3 on [0, 0.4], is flat on [0.4, 0.62], and
        rises to 0.12 on [0.62, 1]; continuous, with a flat minimum."""
        if y <= 0.4:
            return -0.3 + 0.92 * (1 + math.cos(PI * y / 0.4)) / 2
        if y <= 0.62:
            return -0.3
        return -0.3 + 0.42 * (1 - math.cos(PI * (y - 0.62) / 0.38)) / 2

    f = Figure(-0.12, 1.12, -0.5, 0.78, 380)
    f.line((-0.05, 0), (1.1, 0), width=1, arrow=True)
    f.line((0, -0.45), (0, 0.76), width=1, arrow=True)
    pts = [(k / 400, fval(k / 400)) for k in range(401)]
    polyline(f, pts, stroke=BLUE, width=2.4)
    fmin = min(y for _, y in pts)
    xl = min(x for x, y in pts if y <= fmin + 1e-12)
    assert abs(xl - 0.4) < 1e-9
    for x, name in ((0.0, 'α'), (1.0, 'β')):
        f.line((x, -0.02), (x, 0.02), width=1.2)
        f.text((x, -0.07), name, size=15)
    f.line((xl, 0), (xl, fmin), stroke=FAINT, width=1, dash='3 3')
    f.dot((xl, fmin), r=4.2, fill=ORANGE)
    f.text((xl, 0.06), 'x', size=15, color=ORANGE)
    f.line((xl, fmin - 0.06), (0.62, fmin - 0.06), stroke=FAINT, width=1)
    f.text((0.51, fmin - 0.12), 'minimum', size=12, italic=False, color=FAINT)
    f.text((0.05, 0.66), 'f', size=15, color=BLUE, anchor='start')
    f.save('10-seven/leftmost', 'A continuous function positive at alpha, '
           'nonnegative at beta and somewhere negative, whose minimum is '
           'attained on a stretch; x is the left end of the stretch')


def parallel_pairs():
    # d = 0: S below the axis, T above it
    a, b, A, B, s, t = 0.9, 0.55, 1.0, 0.5, -1, 1
    g1 = label(a, b) + label(A, B)
    assert admissible(a, b) and admissible(A, B) and g1 >= PI / 3
    cS, cT, d = pair(a, b, A, B, s, t, g1)
    assert abs(d) < 1e-12 and not overlap(square_corners(cS),
                                          square_corners(cT))
    # d = pi/2: T to the upper left of S
    a2, b2, A2, B2, s2, t2 = 1.2, 0.05, 1.0, 0.15, 1, -1
    g2 = PI / 2 - s2 * label(a2, b2) + t2 * label(A2, B2)
    assert admissible(a2, b2) and admissible(A2, B2) and g2 >= PI / 3
    cS2, cT2, d2 = pair(a2, b2, A2, B2, s2, t2, g2)
    assert abs(d2 - PI / 2) < 1e-12
    assert not overlap(square_corners(cS2), square_corners(cT2))
    off = 2.6
    f = Figure(-0.55, off + 1.85, -1.15, 1.72, 118)
    for o, (S, T, m1, m2, dd) in (
            ((0.0, 0.0), (cS, cT, s * label(a, b), s * label(a, b) + g1, 0)),
            ((off, 0.0), (cS2, cT2, s2 * label(a2, b2),
                          s2 * label(a2, b2) + g2, 90))):
        thin_arc(f, o, 1.0, rad(-80), rad(130))
        f.square(shift(o, S), fill=FILLS[0], stroke=BLUE)
        f.square(shift(o, T), dd, fill=FILLS[2], stroke=GREEN)
        for m, color in ((m1, BLUE), (m2, GREEN)):
            f.line(o, shift(o, u(m), 1.0), stroke=color, width=1.5)
        f.arc(o, 0.3, m1, m2, INK, width=1.2)
        # in the left panel the bisector runs along the separating line
        tg = (m1 + m2) / 2 + (0.3 if dd == 0 else 0.0)
        f.text(shift(o, u(tg), 0.42), 'g', size=15)
        f.dot(o)
        # above the separating line in the left panel, below o in the right
        f.text(shift(o, (-0.05, 0.08 if dd == 0 else -0.08)), 'o',
               anchor='end')
        f.text(shift(o, shift(S, (0.3, -0.3))), 'S', size=16, color=BLUE)
        f.text(shift(o, shift(T, (0.3, 0.3))), 'T', size=16, color=GREEN)
    ysep = (cS[1] + 0.5 + cT[1] - 0.5) / 2
    f.line((-0.5, ysep), (1.8, ysep), stroke=INK, width=1.4, dash='6 4')
    xsep = off + (cS2[0] - 0.5 + cT2[0] + 0.5) / 2
    f.line((xsep, -1.1), (xsep, 1.45), stroke=INK, width=1.4, dash='6 4')
    f.text((0.6, 1.62), it('d') + NB + '=' + NB + '0', size=14, italic=False)
    f.text((off + 0.6, 1.62), it('d') + NB + '=' + NB + 'π/2', size=14,
           italic=False)
    f.save('10-seven/parallel', 'A parallel canonical pair separated by a '
           'horizontal line, and a quarter-turned one separated by a '
           'vertical line')


def nearest_vertex():
    A, B, t = 0.85, 0.68, 1
    assert admissible(A, B)
    c = (A, t * B)
    V = (A - 0.5, t * (B - 0.5))
    delta = math.hypot(*V)
    assert delta < 0.5
    n = (-V[0] / delta, -V[1] / delta)
    # the support of T in the direction n is -delta, attained at V
    corners = square_corners(c)
    assert abs(support(c[0], c[1], math.atan2(n[1], n[0])) + delta) < 1e-12
    assert max(p[0] * n[0] + p[1] * n[1] for p in corners) <= -delta + 1e-12
    beta = math.atan2(V[1], V[0])
    assert 0 < beta <= PI / 4
    f = Figure(-0.5, 1.42, -0.4, 1.22, 250)
    f.line((-0.45, 0), (1.4, 0), stroke=FAINT, width=1, dash='5 4')
    f.square(c, fill=FILLS[2], stroke=GREEN)
    tang = (-n[1], n[0])
    f.line(shift(V, tang, -0.6), shift(V, tang, 0.7), stroke=INK,
           width=1.2, dash='5 4')
    f.line((0, 0), V, stroke=ORANGE, width=2.2)
    f.text(shift((V[0] / 2, V[1] / 2), tang, -0.07), 'δ', size=16,
           color=ORANGE)
    # the direction u(z) = -V / delta, drawn at o
    f.line((0, 0), shift((0, 0), n, 0.3), stroke=INK, width=1.6, arrow=True)
    f.text(shift((0, 0), n, 0.38), 'u(z)', size=14, anchor='end')
    f.arc((0, 0), 0.16, 0, beta, INK, width=1.2)
    f.text(shift((0, 0), u(beta / 2), 0.25), 'β', size=15)
    f.dot(V, r=4, fill=ORANGE)
    f.text(shift(V, (0.09, -0.08)), '(' + it('A') + NB + '−' + NB + '½,'
           + NB + it('t') + '(' + it('B') + NB + '−' + NB + '½))', size=13,
           italic=False, anchor='start')
    f.dot(c, fill=GREEN)
    f.text(shift(c, (0.04, 0.07)), '(' + it('A') + ',' + NB + it('tB') + ')',
           size=13, italic=False, anchor='start', color=GREEN)
    f.dot((0, 0))
    f.text((0.02, -0.09), 'o', anchor='start')
    f.text(shift(c, (0.3, 0.32)), 'T', size=17, color=GREEN)
    f.save('10-seven/nearest-vertex', 'The square T in its own chart, its vertex '
           'nearest to the disk centre at distance delta and angle beta, the '
           'line through that vertex perpendicular to it, and the direction '
           'u(z) pointing from the vertex past the centre')


def gap_profile():
    a, b, A, B, s, t = 1.0, 0.5, 1.0, 0.5, -1, 1
    gmax = PI / 2
    vs = 0.45                      # vertical scale of the graph
    curves = [[(gmax * j / 400, sigma(a, b, A, B, s, t, k, gmax * j / 400))
               for j in range(401)] for k in range(4)]
    top = vs * max(y for c in curves for _, y in c)
    bottom = vs * min(y for c in curves for _, y in c)
    f = Figure(-0.22, gmax + 0.3, bottom - 0.12, top + 0.1, 330)
    f.line((-0.05, 0), (gmax + 0.12, 0), width=1, arrow=True)
    f.line((0, bottom - 0.08), (0, top + 0.08), width=1, arrow=True)
    f.text((gmax + 0.12, -0.06), 'g', anchor='end')
    for x, name in ((PI / 3, 'π/3'), (PI / 2, 'π/2')):
        f.line((x, -0.015), (x, 0.015), width=1.2)
        f.text((x, -0.06), name, size=13, italic=False)
    for y in (1, 2):
        f.line((-0.015, vs * y), (0.015, vs * y), width=1.2)
        f.text((-0.035, vs * y), str(y), size=12, italic=False, anchor='end')
    f.line((PI / 3, bottom - 0.08), (PI / 3, top), stroke=FAINT, width=1,
           dash='4 4')
    cols = [BLUE, ORANGE, GREEN, PURPLE]
    for k, pts in enumerate(curves):
        for gg, val in pts:
            if gg < PI / 3 - 1e-9:
                assert val > 0
        polyline(f, [(gg, vs * val) for gg, val in pts], stroke=cols[k],
                 width=2)
        gg, val = pts[-1]
        f.text((gg + 0.03, vs * val), sb('σ', str(k), size=14), size=14,
               color=cols[k], anchor='start')
    assert abs(sigma(a, b, A, B, s, t, 1, PI / 3)) < 1e-12
    f.dot((PI / 3, 0), r=4, fill=ORANGE)
    f.save('10-seven/gap-profile', 'The four support sums of the pair of a side '
           'column as functions of the gap: positive below pi/3, and the '
           'forward one zero at pi/3')


def ring():
    y1, y2, y3 = -1.15, -0.1, 1.1
    assert -L7 <= y1 and y1 + 1 <= y2 and y2 + 1 <= y3 and y3 <= L7
    cs = [(1, -0.5), (1, 0.5), (0, y3), (-1, 0.5), (-1, -0.5), (0, y1)]
    kinds = ['lower', 'upper', 'axial', 'lower', 'upper', 'axial']
    cols = [0, 1, 6, 3, 2, 4]
    m = R7 + 0.1
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R7, stroke=INK, width=1.2, dash='6 4')
    f.square((0, y2), stroke=FAINT, width=1.2, dash='4 3')
    for c, k in zip(cs, cols):
        f.square(c, fill=FILLS[k], stroke=COLORS[k])
    f.circle((0, 0), 1.0)
    marks = [rad(-30 + 60 * i) for i in range(6)]
    hexagon = [u(t) for t in marks]
    f.polygon(hexagon, stroke=INK, width=1.0, dash='3 3')
    for t, k in zip(marks, cols):
        f.line((0, 0), u(t), stroke=COLORS[k], width=1.5)
        f.dot(u(t), r=3.2, fill=COLORS[k])
    # contacts: shared edges of consecutive squares
    for i in range(6):
        P = square_corners(cs[i])
        Q = square_corners(cs[(i + 1) % 6])
        xs = sorted(set(round(x, 9) for x, _ in P) & set(round(x, 9) for x, _ in Q))
        ys = sorted(set(round(y, 9) for _, y in P) & set(round(y, 9) for _, y in Q))
        if len(ys) == 1:     # a horizontal edge
            lo = max(min(x for x, _ in P), min(x for x, _ in Q))
            hi = min(max(x for x, _ in P), max(x for x, _ in Q))
            f.line((lo, ys[0]), (hi, ys[0]), stroke=INK, width=4)
        else:                # a vertical edge
            xe = [x for x in (-0.5, 0.5)
                  if any(abs(px - x) < 1e-9 for px, _ in P)
                  and any(abs(qx - x) < 1e-9 for qx, _ in Q)][0]
            lo = max(min(y for _, y in P), min(y for _, y in Q))
            hi = min(max(y for _, y in P), max(y for _, y in Q))
            assert hi > lo
            f.line((xe, lo), (xe, hi), stroke=INK, width=4)
    # each square with its kind and the point where it sits (Proposition 10.26)
    places = ['(1,' + NB + '−½)', '(1,' + NB + '½)',
              '(0,' + NB + sb(it('y'), '3', ')', 13),
              '(−1,' + NB + '½)', '(−1,' + NB + '−½)',
              '(0,' + NB + sb(it('y'), '1', ')', 13)]
    for c, name, place, k in zip(cs, kinds, places, cols):
        top = 0.32 if c[1] > 0 else -0.26      # the outer part of the square
        f.text(shift(c, (0.0, top)), name, size=13, italic=False,
               color=COLORS[k])
        f.text(shift(c, (0.0, top - 0.14)), place, size=13,
               italic=False, color=COLORS[k])
    f.dot((0, 0))
    f.text((0.13, 0.0), 'o')                 # between the rays at -30 and 30
    f.save('10-seven/ring', 'The ring of six exterior squares: the markers form '
           'a regular hexagon, the kinds are lower, upper, axial twice, and '
           'consecutive squares touch along the thick edges')


def middle():
    sides = [(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5)]
    f = Figure(-1.65, 1.65, -1.25, 1.25, 165)
    f.polygon([(-1.6, -1), (1.6, -1), (1.6, 1), (-1.6, 1)], fill='#f3f4f6',
              stroke='none')
    f.polygon([(-0.5, -1.2), (0.5, -1.2), (0.5, 1.2), (-0.5, 1.2)],
              fill=FILLS[1], stroke='none')
    for k, c in enumerate(sides):
        f.square(c, fill=FILLS[0], stroke=BLUE)
    f.line((-1.6, 1), (1.6, 1), stroke=FAINT, width=1, dash='4 4')
    f.line((-1.6, -1), (1.6, -1), stroke=FAINT, width=1, dash='4 4')
    # the allowed square
    z = 0.2
    f.square((0, z), fill=GREY, stroke=INK, width=1.4)
    # a tilted square containing o
    ct, deg = (0.05, 0.1), 40
    assert in_open_square((0, 0), ct, deg)
    f.square(ct, deg, stroke=PINK, width=1.8, dash='6 4')
    mm = max(abs(math.cos(rad(deg))), abs(math.sin(rad(deg))))
    half = 1 / (2 * mm)
    p0, p1 = (ct[0] - half, ct[1]), (ct[0] + half, ct[1])
    assert abs(p0[0]) > 0.5 and abs(p1[0]) > 0.5
    f.line(p0, p1, stroke=PINK, width=2.2)
    f.dot(p0, r=3.4, fill=PINK)
    f.dot(p1, r=3.4, fill=PINK)
    f.dot((0, 0))
    f.text((0.05, -0.1), 'o', anchor='start')
    for k, c in enumerate(sides):
        f.text(shift(c, (0.25 * c[0], 0.27 * (1 if c[1] > 0 else -1))),
               sb('P', str(k + 1), size=15), size=15, color=BLUE)
    f.text((0, 1.13), '|' + it('x') + '|' + NB + '≤' + NB + '½', size=13,
           italic=False, color=ORANGE)
    f.text((1.45, 1.07), '|' + it('y') + '|' + NB + '&lt;' + NB + '1', size=13,
           italic=False, color=FAINT, anchor='end')
    f.save('10-seven/middle', 'The four side squares, the band between them and '
           'the strip in the middle; a tilted square containing the disk '
           'centre has a chord through its centre longer than 1 that pokes '
           'into the side squares; an axis-parallel square in the strip')


def remainder(a, b):
    return 4 - 3 * a - 2 * b


def runs_in_box(pts, box):
    """The maximal runs of a sampled curve inside the box (x0, x1, y0, y1)."""
    x0, x1, y0, y1 = box
    runs, run = [], []
    for x, y in pts:
        if x0 <= x <= x1 and y0 <= y <= y1:
            run.append((x, y))
        elif run:
            runs.append(run)
            run = []
    if run:
        runs.append(run)
    return [r for r in runs if len(r) > 1]


def quadratic():
    """Lemma 10.8 (1): in the coordinates (side(a, b), r(a, b)), which are
    affine in (a, b), the states with a side label lie right of 9/25 and above
    the parabola 9/5 (l - pi/6)^2."""
    poly = region_polygon(400)
    tie = 2 * PI + 7
    sd = clip(clip(poly, -9, -11, -tie), -9, 4, -(7 - PI))
    img = [(side(a, b), remainder(a, b)) for a, b in sd]
    par = lambda l: 1.8 * (l - PI / 6) ** 2
    # every admissible state with a side label: l > 9/25 and r >= par(l)
    for i in range(301):
        for j in range(301):
            a = 0.5 + (L7 - 0.5) * i / 300
            b = a * j / 300
            if admissible(a, b) and side(a, b) <= min(axial(b), PI / 4):
                assert side(a, b) > 9 / 25
                assert remainder(a, b) >= par(side(a, b)) - 1e-12
    a0, b0 = transition_state()
    s0, r0 = side(a0, b0), remainder(a0, b0)
    corner = math.sqrt(13 / 8) - 0.5
    top = 0.17                             # the strip shown: 0 <= r <= top
    box = (0.32, 0.83, -0.005, top)
    p = Plot(0.27, 0.9, -0.03, 0.19, 820, 2000)
    p.polygon(clip(img, 0, 1, top), fill=FILLS[1], stroke='none')
    for k in range(len(img)):              # the edges of the region in the strip
        q0, q1 = img[k], img[(k + 1) % len(img)]
        if max(q0[1], q1[1]) <= top + 1e-12:
            p.line(q0, q1, stroke=ORANGE, width=1.4)
        elif min(q0[1], q1[1]) < top:
            lo, hi = (q0, q1) if q0[1] < q1[1] else (q1, q0)
            w = (top - lo[1]) / (hi[1] - lo[1])
            p.line(lo, (lo[0] + w * (hi[0] - lo[0]), top), stroke=ORANGE,
                   width=1.4)
    circle = [(side(-0.5 + R7 * math.cos(t), -0.5 + R7 * math.sin(t)),
               remainder(-0.5 + R7 * math.cos(t), -0.5 + R7 * math.sin(t)))
              for t in (2 * PI * k / 20000 for k in range(20001))]
    for run in runs_in_box(circle, box):
        p.polyline(run, stroke=BLUE, width=1.8)
    p.curve(par, 0.32, 0.83, stroke=PURPLE, width=1.8, dash='7 4')
    x_axis(p, 0.3, 0.87, ticks=((9 / 25, '9/25'), (PI / 6, 'π/6'),
                                (PI / 4, 'π/4')), label='ℓ')
    y_axis(p, -0.005, 0.185, x=0.3, ticks=((0.05, '0.05'), (0.1, '0.10'),
                                           (0.15, '0.15')), label='r')
    p.line((9 / 25, 0), (9 / 25, top), stroke=FAINT, width=1, dash='3 3')
    p.dot((PI / 6, 0), fill=ORANGE)
    p.dot((s0, r0), fill=INK)
    p.text((s0, r0), state0(13), size=13, anchor='start', dx=8, dy=4)
    p.dot((side(corner, corner), remainder(corner, corner)), fill=INK, r=2.8)
    p.text((side(corner, corner), remainder(corner, corner)), 'b = a',
           size=13, anchor='end', dx=-8, dy=-8)
    p.text((0.66, 0.135), 'side labels', size=13, italic=False, color=ORANGE)
    p.text((0.765, 0.158), 'φ = 13/4', size=13, color=BLUE, anchor='end')
    p.text((0.745, 0.072), '9/5 (ℓ − π/6)²', size=13, color=PURPLE,
           anchor='start')
    p.save('10-seven/quadratic', 'The states with a side label in the '
           'coordinates side label and remainder: a curved triangle whose lower '
           'edge is the image of the circle phi = 13/4, resting on r = 0 at the '
           'side state; it lies right of 9/25 and above the dashed parabola '
           '9/5 (l - pi/6) squared')


def support_figure():
    """Lemma 10.11 (1) and (2): the support of Q(a, b) in the direction u(z)
    is attained at a vertex, and the points u(x) of the marker arc, which lie
    in the closed square, have smaller projections cos(z - x)."""
    a, b = 1.0, 0.45
    lab = label(a, b)
    z = rad(75)
    x = lab + 0.45
    assert admissible(a, b) and abs(x - lab) <= ARC
    h = support(a, b, z)
    V = (a + 0.5, b + 0.5)
    assert abs(V[0] * math.cos(z) + V[1] * math.sin(z) - h) < 1e-12
    for q in square_corners((a, b)):
        assert q[0] * math.cos(z) + q[1] * math.sin(z) <= h + 1e-12
    P = u(x)
    assert in_closed(P, (a, b)) and math.cos(z - x) < h
    f = Figure(-0.42, 1.72, -0.22, 1.62, 205)
    thin_arc(f, (0, 0), 1.0, rad(-12), rad(118))
    f.square((a, b), fill=FILLS[0], stroke=BLUE)
    f.arc((0, 0), 1.0, lab - ARC, lab + ARC, ORANGE, width=5)
    H = shift((0, 0), u(z), h)
    F = shift((0, 0), u(z), math.cos(z - x))
    tang = (-math.sin(z), math.cos(z))
    f.line(shift(V, tang, -0.25), shift(H, tang, 0.06), stroke=INK, width=1.2,
           dash='6 4')
    f.line((0, 0), shift((0, 0), u(z), 1.55), stroke=INK, width=1.3,
           arrow=True)
    f.text(shift((0, 0), u(z), 1.6), 'u(z)', size=14, anchor='start')
    f.line(P, F, stroke=ORANGE, width=1, dash='2 3')
    f.dot(H, r=3.4)
    f.dot(F, r=3.4, fill=ORANGE)
    f.dot(V, r=3.6, fill=BLUE)
    f.dot(P, r=3.6, fill=ORANGE)
    f.text(shift(H, (-0.06, -0.05)), 'h(a, b, z)', size=14, anchor='end')
    f.text(shift(F, (-0.05, 0.0)), 'cos(' + it('z') + NB + '−' + NB + it('x')
           + ')', size=14, italic=False, anchor='end', color=ORANGE)
    f.text(shift(P, (0.07, 0.04)), 'u(x)', size=14, anchor='start',
           color=ORANGE)
    f.dot((a, b), fill=BLUE)
    f.text((a + 0.04, b - 0.07), '(' + it('a') + ',' + NB + it('b') + ')',
           size=13, italic=False, anchor='start', color=BLUE)
    f.text((a + 0.33, b - 0.33), 'Q(a, b)', size=15, color=BLUE)
    f.dot((0, 0))
    f.text((-0.04, -0.08), 'o', anchor='end')
    f.text(shift((0, 0), u(rad(-8)), 1.13), sb('Γ', '1'), size=15)
    f.save('10-seven/support', 'The closed square Q(a, b) with its marker arc, '
           'a direction u(z), the supporting line perpendicular to it through '
           'the extreme vertex at height h(a, b, z), and a point u(x) of the '
           'marker arc whose projection cos(z - x) is smaller')


def reversed_pair():
    """Lemma 10.13 (3): the reversed pair is the canonical pair seen from T,
    its image under the rotation by -d followed by the reflection in the first
    axis."""
    a, b, A, B, s, t, g = (CP[k] for k in ('a', 'b', 'A', 'B', 's', 't', 'g'))
    cS, cT, d = pair(a, b, A, B, s, t, g)
    cS2, cT2, d2 = pair(A, B, a, b, -t, -s, g)
    assert abs(d2 - d) < 1e-12
    iso = lambda p: (rot(p, -d)[0], -rot(p, -d)[1])
    dg = math.degrees(d)
    key = lambda P: sorted((round(x, 9), round(y, 9)) for x, y in P)
    assert key(map(iso, square_corners(cT, dg))) == key(square_corners(cS2))
    assert key(map(iso, square_corners(cS))) == key(square_corners(cT2, dg))
    off = 3.15
    f = Figure(-1.25, off + 1.72, -0.6, 1.95, 118)
    panels = [((0.0, 0.0), cS, 0.0, BLUE, FILLS[0], 'S', cT, dg, GREEN,
               FILLS[2], 'T', s * label(a, b)),
              ((off, 0.0), cS2, 0.0, GREEN, FILLS[2], 'S′', cT2, dg, BLUE,
               FILLS[0], 'T′', -t * label(A, B))]
    for o, c1, d1, col1, fill1, n1, c2, dd2, col2, fill2, n2, m1 in panels:
        thin_arc(f, o, 1.0, rad(-40), rad(160))
        f.square(shift(o, c1), d1, fill=fill1, stroke=col1)
        f.square(shift(o, c2), dd2, fill=fill2, stroke=col2)
        for m, col in ((m1, col1), (m1 + g, col2)):
            f.line(o, shift(o, u(m), 1.0), stroke=col, width=1.5)
        f.arc(o, 0.25, m1, m1 + g, INK, width=1.2)
        f.text(shift(o, u(m1 + g / 2 + 0.3), 0.37), 'g', size=15)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.09)), 'o', anchor='end')
        f.text(shift(o, shift(c1, (0.28, -0.27))), n1, size=17, color=col1)
        f.text(shift(o, shift(c2, (-0.02, 0.12))), n2, size=17, color=col2)
    f.save('10-seven/reversed', 'Left: a canonical pair S, T with its markers a '
           'gap g apart. Right: its reversed pair, in which S prime is the image '
           'of T and T prime the image of S under one rotation and reflection '
           'about o, with the same gap')


def overlap_pairs():
    """Proposition 10.17 and Lemma 10.14: at the gap pi/3, two admissible
    states that do not form a contact give overlapping squares."""
    specs = [((1.0, 0.5, -1), (0.9, 0.55, 1)),     # kind (1), T moved
             ((1.0, 0.5, 1), (1.0, 0.15, 1)),      # kind (2), T off the axis
             ((1.1, 0.1, 1), (1.0, 0.5, -1))]      # kind (3), S off the axis
    off = 2.55
    f = Figure(-0.75, 2 * off + 1.72, -1.15, 1.85, 108)
    for j, ((a, b, s), (A, B, t)) in enumerate(specs):
        assert admissible(a, b) and admissible(A, B)
        o = (j * off, 0.0)
        cS, cT, d = pair(a, b, A, B, s, t, PI / 3)
        dg = math.degrees(d)
        for k in range(4):
            assert sigma(a, b, A, B, s, t, k, PI / 3) > 0
            assert sigma(A, B, a, b, -t, -s, k, PI / 3) > 0
        PS, PT = square_corners(cS), square_corners(cT, dg)
        assert overlap(PS, PT)
        thin_arc(f, o, 1.0, rad(-68), rad(112))
        f.square(shift(o, cS), fill=FILLS[0], stroke=BLUE, opacity=0.85)
        f.square(shift(o, cT), dg, fill=FILLS[2], stroke=GREEN, opacity=0.85)
        common = clip_square(PS, cT, dg)
        f.polygon([shift(o, q) for q in common], fill=RED_FILL, stroke=RED,
                  width=1.4)
        m1 = s * label(a, b)
        for m, color in ((m1, BLUE), (m1 + PI / 3, GREEN)):
            f.line(o, shift(o, u(m), 1.0), stroke=color, width=1.5)
        f.arc(o, 0.16, m1, m1 + PI / 3, INK, width=1.2)
        f.text(shift(o, u(m1 + PI / 6), 0.27), 'π/3', size=13, italic=False)
        f.dot(o)
        f.text(shift(o, (-0.05, -0.08)), 'o', anchor='end')
        f.text(shift(o, shift(cS, (0.3, -0.3))), 'S', size=16, color=BLUE)
        f.text(shift(o, shift(cT, (-0.3, 0.3))), 'T', size=16, color=GREEN)
        f.text(shift(o, (0.5, 1.72)), f'({j + 1})', size=15, italic=False)
    f.save('10-seven/overlap', 'Three canonical pairs at the gap pi/3 obtained '
           'from the three kinds of contact by moving one state slightly; in '
           'each the two squares overlap in a small shaded region')


def sinusoids():
    """Lemma 10.22: the support h(A, tB, z) of T is the largest of four
    sinusoids, one per vertex; its only smooth minimum is the trough of the
    sinusoid of the vertex nearest to o, at z = pi + t beta, of depth -delta."""
    A, B, t = 0.85, 0.68, 1
    assert admissible(A, B)
    c = (A, t * B)
    verts = square_corners(c)
    sin_of = lambda q: (lambda z: q[0] * math.cos(z) + q[1] * math.sin(z))
    hz = lambda z: support(A, t * B, z)
    for k in range(721):
        z = 2 * PI * k / 720
        assert abs(hz(z) - max(sin_of(q)(z) for q in verts)) < 1e-12
    V = (A - 0.5, t * (B - 0.5))
    delta = math.hypot(*V)
    beta = math.atan2(abs(V[1]), V[0])
    zmin = PI + t * beta
    assert abs(hz(zmin) + delta) < 1e-12
    assert all(hz(2 * PI * k / 7200) >= -delta - 1e-12 for k in range(7200))
    p = Plot(-0.45, 7.05, -0.98, 2.1, 68, 150)
    bot = -0.8
    x_axis(p, -0.1, 6.95, y=bot, ticks=((0, '0'), (PI / 2, 'π/2'), (PI, 'π'),
                                       (PI + beta, 'π + β'),
                                       (3 * PI / 2, '3π/2'), (2 * PI, '2π')),
           label='z')
    y_axis(p, bot, 2.05, ticks=((0, '0'), (1, '1')))
    p.line((0, 0), (2 * PI, 0), stroke=FAINT, width=1)
    for q in verts:
        nearest = abs(q[0] - V[0]) < 1e-12 and abs(q[1] - V[1]) < 1e-12
        p.curve(sin_of(q), 0, 2 * PI, stroke=ORANGE if nearest else FAINT,
                width=1.2, dash='5 4', ylim=(bot, 2.0))
    p.curve(hz, 0, 2 * PI, n=1440, stroke=BLUE, width=2.4)
    lo, hi = PI, 3 * PI / 2
    p.curve(hz, lo, hi, n=360, stroke=ORANGE, width=2.6)
    for k in range(5):
        p.dot((k * PI / 2, hz(k * PI / 2)), fill=BLUE, r=3)
    p.line((0, -delta), (zmin, -delta), stroke=FAINT, width=1, dash='3 3')
    p.line((zmin, -delta), (zmin, bot), stroke=FAINT, width=1, dash='3 3')
    p.dot((zmin, -delta), fill=ORANGE, r=4)
    p.text((0, -delta), '−δ', size=14, anchor='end', dx=-8, color=ORANGE)
    p.text((0.75, hz(0.75)), 'h(A, tB, z)', size=14, color=BLUE,
           anchor='start', dx=8, dy=-8)
    p.save('10-seven/sinusoids', 'The support of the square T in the direction '
           'u(z) as z runs once round: the largest of four sinusoids, one for '
           'each vertex, with corners at the multiples of pi/2. Its only '
           'smooth minimum is the trough of the sinusoid of the nearest vertex, '
           'at z = pi + beta, of depth minus delta')


def pair_markers():
    """Theorem 10.24, step 1: two disjoint exterior squares with their phases
    and markers; the markers are g apart and the phases d apart, d the
    relative phase of their canonical pair."""
    (a, b, eS, thS), (A, B, eT, thT) = ((1.15, 0.2, 1, rad(-15)),
                                       (1.1, 0.3, -1, rad(95)))
    assert admissible(a, b) and admissible(A, B)
    cS = rot((a, eS * b), thS)
    cT = rot((A, eT * B), thT)
    dS, dT = math.degrees(thS), math.degrees(thT)
    assert not overlap(square_corners(cS, dS), square_corners(cT, dT))
    muS, muT = thS + eS * label(a, b), thT + eT * label(A, B)
    g = muT - muS
    d = g + eS * label(a, b) - eT * label(A, B)
    assert PI / 3 <= g < PI and abs(d - (thT - thS)) < 1e-12
    m = R7 + 0.06
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R7, stroke=INK, width=1.2, dash='6 4')
    f.circle((0, 0), 1.0)
    f.square(cS, dS, fill=FILLS[0], stroke=BLUE)
    f.square(cT, dT, fill=FILLS[2], stroke=GREEN)
    for th, mu, col, nm in ((thS, muS, BLUE, 'S'), (thT, muT, GREEN, 'T')):
        f.line((0, 0), u(th), stroke=INK, width=1.1, dash='5 4')
        f.text(shift((0, 0), u(th), 1.12), sb('θ', nm), size=15)
        f.line((0, 0), u(mu), stroke=col, width=1.8)
        f.dot(u(mu), r=3.2, fill=col)
        f.text(shift((0, 0), u(mu), 1.13), sb('μ', nm), size=15, color=col)
    f.arc((0, 0), 0.3, muS, muT, INK, width=1.2)
    f.text(shift((0, 0), u((muS + muT) / 2 - 0.1), 0.4), 'g', size=15)
    f.arc((0, 0), 0.5, thS, thT, INK, width=1.0)
    f.text(shift((0, 0), u((thS + thT) / 2 + 0.25), 0.6), 'd', size=15)
    f.dot((0, 0))
    f.text((0.03, -0.09), 'o', anchor='start')
    f.text(shift(cS, (0.2, -0.3)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.25, 0.25)), 'T', size=17, color=GREEN)
    f.save('10-seven/pair-markers', 'Two disjoint exterior squares S and T in the '
           'disk of radius root 13 over 2, with their phases dashed and their '
           'markers on the unit circle; the markers are g apart, more than '
           'pi/3, and the phases are d apart')


def main():
    columns()
    states()
    labels()
    quadratic()
    marker()
    support_figure()
    canonical()
    reversed_pair()
    octagon()
    contacts()
    overlap_pairs()
    small_gaps()
    leftmost()
    parallel_pairs()
    sinusoids()
    nearest_vertex()
    gap_profile()
    pair_markers()
    ring()
    middle()


if __name__ == '__main__':
    main()

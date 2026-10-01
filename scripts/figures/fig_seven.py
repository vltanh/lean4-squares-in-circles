#!/usr/bin/env python3
"""Draw the figures of Chapter 9 (seven squares) as SVG files.

    python3 scripts/figures/fig_seven.py

Every figure is computed from the definitions of the chapter: states and
labels, the canonical pair of two states, its support sums, and the column
packings. Squares, arcs and regions are sampled or clipped from that geometry.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           rad, sb, clip, convex_hull)

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK = COLORS[:5]
DIGITS = str.maketrans('0123456789', '₀₁₂₃₄₅₆₇₈₉')


def low(base, digits):
    """A name with a numeric subscript, in Unicode subscript digits."""
    return base + str(digits).translate(DIGITS)
L7 = math.sqrt(3) - 0.5          # the column limit sqrt 3 - 1/2
R7 = math.sqrt(13) / 2           # the optimal radius
ARC = 1 / 2                      # half-width of the marker arc


# ---------------------------------------------------------------- the model

def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def axial(u_):
    return 1.25 * u_


def side(a, u_):
    return PI / 6 + (u_ - 0.5) / 3 + 0.75 * (1 - a)


def label(a, u_):
    return min(axial(u_), side(a, u_), PI / 4)


def admissible(a, u_):
    return a >= 0.5 and 0 <= u_ <= a and phi(a, u_) <= 13 / 4 + 1e-12


def support(a, b, z):
    return (a * math.cos(z) + b * math.sin(z)
            + (abs(math.cos(z)) + abs(math.sin(z))) / 2)


def rot(p, d):
    return (p[0] * math.cos(d) - p[1] * math.sin(d),
            p[0] * math.sin(d) + p[1] * math.cos(d))


def pair(a, u_, A, v, s, t, g):
    """The canonical pair: centre of S, centre of T, turn d (radians)."""
    d = g + s * label(a, u_) - t * label(A, v)
    return (a, s * u_), rot((A, t * v), d), d


def sigma(a, u_, A, v, s, t, k, g):
    d = g + s * label(a, u_) - t * label(A, v)
    return (support(a, s * u_, k * PI / 2)
            + support(A, t * v, k * PI / 2 + PI - d))


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
    """The admissible states as a convex polygon in the (a, u)-plane."""
    diag = math.sqrt(13 / 8) - 0.5
    arc = []
    t_lo = math.atan2(0.5, L7 + 0.5)            # the point (L7, 0)
    t_hi = math.atan2(diag + 0.5, diag + 0.5)   # the diagonal point
    for k in range(steps + 1):
        t = t_lo + (t_hi - t_lo) * k / steps
        arc.append((-0.5 + R7 * math.cos(t), -0.5 + R7 * math.sin(t)))
    return [(0.5, 0.0)] + arc + [(0.5, 0.5)]


def plane_axes(f, amax, umax, ticks_a=(), ticks_u=()):
    f.line((0.38, 0), (amax, 0), width=1, arrow=True)
    f.line((0.42, -0.06), (0.42, umax), width=1, arrow=True)
    f.text((amax, -0.05), 'a', anchor='end')
    f.text((0.39, umax - 0.02), 'u', anchor='end')
    for x, s in ticks_a:
        f.line((x, -0.015), (x, 0.015), width=1.2)
        f.text((x, -0.055), s, size=13, italic=False)
    for y, s in ticks_u:
        f.line((0.405, y), (0.435, y), width=1.2)
        f.text((0.39, y), s, size=13, italic=False, anchor='end')


def transition_state():
    M = 2 * PI + 17
    J = math.sqrt(1313 / 2 - M * M)
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
    f.save('seven-columns', 'Three column packings: the middle column pushed '
           'down, spread out and pushed up, between the same two side columns')


def states():
    poly = region_polygon()
    a0, u0 = transition_state()
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
               ticks_u=((0.5, '½'),))
    f.dot((1.0, 0.5), r=4, fill=ORANGE)
    f.text((1.03, 0.54), 'side state (1, ½)', size=13, italic=False,
           anchor='start', color=ORANGE)
    f.dot((a0, u0), r=4)
    f.text((a0 + 0.045, u0 + 0.02), '(' + low('a', 0) + ', ' + low('u', 0)
           + ')', size=14, anchor='start')
    f.text((0.84, 0.8), 'φ = 13/4', size=14, color=BLUE, anchor='start')
    f.text((0.6, 0.64), 'u = a', size=13, color=FAINT, italic=False,
           anchor='end')
    f.text((0.68, 0.22), 'admissible', size=14, italic=False, color=BLUE)
    f.save('seven-states', 'The admissible states in the (a, u)-plane, the '
           'side state with the tangent line r = 0, the axial segment and the '
           'transition state')


def labels():
    poly = region_polygon()
    a0, u0 = transition_state()
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
        f.text((start[0] - 0.012, y), f'{c:.1f}', size=11, italic=False,
               anchor='end', color=INK)
        if inside((x_tie, y)):
            # the side part: 9a - 4u = 2pi + 7 - 12c, upwards from the tie
            top = (x_tie + 4 * 0.5 / 9, y + 0.5)
            polyline(f, [(x_tie, y), first_exit((x_tie, y), top, inside)],
                     stroke=INK, width=0.8)
    # the three dividing lines inside the region, through the triple point
    triple = ((7 - PI / 5) / 9, PI / 5)
    polyline(f, [triple, (a0, u0)], stroke=INK, width=1.6)
    polyline(f, [(PI / 5, PI / 5), triple], stroke=INK, width=1.6)
    dg = ((7 - PI) / 5, (7 - PI) / 5)
    polyline(f, [triple, dg], stroke=INK, width=1.6)
    f.polygon(poly, stroke=BLUE, width=1.6)
    plane_axes(f, 1.43, 0.9, ticks_a=((0.5, '½'), (1.0, '1'), (L7, '√3 − ½')),
               ticks_u=((0.5, '½'),))
    f.text((0.78, 0.14), 'axial: ℓ = 5u/4', size=13, italic=False,
           color=GREEN)
    f.text((1.1, 0.66), 'side: ℓ = side(a, u)', size=13, italic=False,
           color=ORANGE, anchor='start')
    f.line((1.1, 0.64), (0.95, 0.53), stroke=ORANGE, width=1)
    f.text((0.6, 0.83), 'capped: ℓ = π/4', size=13, italic=False,
           color=INK, anchor='start')
    f.line((0.68, 0.81), (0.705, 0.69), stroke=INK, width=1)
    f.dot((1.0, 0.5), r=3.6, fill=ORANGE)
    f.dot((a0, u0), r=3.6)
    f.text((a0 + 0.045, u0 + 0.0), '(' + low('a', 0) + ', ' + low('u', 0)
           + ')', size=13, anchor='start')
    f.save('seven-labels', 'The three label regions of the admissible states, '
           'axial, side and capped, with level lines of the label')


def marker():
    a, u_ = 1.0, 0.45
    lab = label(a, u_)
    assert admissible(a, u_) and abs(lab - side(a, u_)) < 1e-12
    theta, eps = rad(24), -1
    off = 2.55
    f = Figure(-0.45, off + 1.75, -1.05, 1.12, 175)
    # left panel: the square as seen from o
    o = (0.0, 0.0)
    c = rot((a, eps * u_), theta)
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
    f.text((0.35, -0.95), low('Γ', 1), size=15)
    # right panel: its chart
    o2 = (off, 0.0)
    c2 = shift(o2, (a, u_))
    f.line(o2, shift(o2, (1.72, 0)), stroke=FAINT, width=1, dash='5 4')
    f.text(shift(o2, (1.72, -0.07)), 't = 0', size=12, italic=False,
           color=FAINT, anchor='end')
    f.square(c2, fill=FILLS[0], stroke=BLUE)
    thin_arc(f, o2, 1.0, rad(-75), rad(95))
    member2 = lambda p: in_open_square(shift(p, o2), c2)
    for t0, t1 in arcs_in(member2, 1.0):
        f.arc(o2, 1.0, t0, t1, BLUE, width=2.2)
    for t in (lab - ARC, lab, lab + ARC):
        assert in_closed(shift(o2, u(t)), c2)
    f.arc(o2, 1.0, lab - ARC, lab + ARC, ORANGE, width=5)
    f.line(o2, shift(o2, u(lab), 1.3), stroke=ORANGE, width=1.6)
    f.arc(o2, 0.3, 0, lab, INK, width=1.2)
    f.text(shift(o2, u(lab / 2), 0.47), 'ℓ(a, u)', size=13)
    f.dot(c2, fill=BLUE)
    f.text(shift(c2, (0.04, -0.07)), '(a, u)', size=13, anchor='start',
           color=BLUE)
    f.dot(o2)
    f.text(shift(o2, (-0.05, -0.07)), 'o', anchor='end')
    f.text(shift(o2, u(lab + ARC), 1.12), '1/2', size=12, italic=False,
           color=ORANGE, anchor='start')
    f.save('seven-marker', 'An exterior square seen from the disk centre with '
           'its phase and marker, and the same square in its chart; the arc '
           'of the unit circle of half-width 1/2 about the marker lies in '
           'the closed square')


CP = dict(a=1.1, u_=0.2, A=1.0, v=0.4, s=1, t=-1, g=1.6)


def canonical():
    a, u_, A, v, s, t, g = (CP[k] for k in ('a', 'u_', 'A', 'v', 's', 't', 'g'))
    assert admissible(a, u_) and admissible(A, v)
    cS, cT, d = pair(a, u_, A, v, s, t, g)
    dg = math.degrees(d)
    PS, PT = square_corners(cS), square_corners(cT, dg)
    assert not overlap(PS, PT)
    f = Figure(-1.5, 1.95, -1.2, 1.95, 150)
    thin_arc(f, (0, 0), 1.0, rad(-30), rad(150))
    f.square(cS, fill=FILLS[0], stroke=BLUE)
    f.square(cT, dg, fill=FILLS[2], stroke=GREEN)
    m1, m2 = s * label(a, u_), s * label(a, u_) + g
    for m, color in ((m1, BLUE), (m2, GREEN)):
        f.line((0, 0), u(m), stroke=color, width=1.6)
    f.arc((0, 0), 0.34, m1, m2, INK, width=1.2)
    f.text(shift((0, 0), u((m1 + m2) / 2), 0.46), 'g', size=15)
    # the four normals of S
    mids = [(cS[0] + 0.5, cS[1]), (cS[0], cS[1] + 0.5), (cS[0] - 0.5, cS[1]),
            (cS[0], cS[1] - 0.5)]
    for k, p in enumerate(mids):
        q = shift(p, u(k * PI / 2), 0.26)
        f.line(p, q, stroke=INK, width=1.4, arrow=True)
        pos = (q[0] + 0.03, q[1] + 0.13) if k == 2 else shift(
            q, u(k * PI / 2), 0.12)
        f.text(pos, low('n', k), size=14)
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
    assert abs(s2 - sigma(a, u_, A, v, s, t, 2, g)) < 1e-9 and s2 < 0
    f.text(((xs_S[0] + xs_T[1]) / 2, yb2 - 0.14), low('σ', 2) + ' &lt; 0',
           size=14)
    xl, xl2 = -1.25, -1.35
    f.line((xl, -0.4), (xl, 1.9), stroke=FAINT, width=1)
    f.line((xl, ys_S[0]), (xl, ys_S[1]), stroke=BLUE, width=5)
    f.line((xl2, ys_T[0]), (xl2, ys_T[1]), stroke=GREEN, width=5)
    s1 = ys_S[1] - ys_T[0]
    assert abs(s1 - sigma(a, u_, A, v, s, t, 1, g)) < 1e-9 and s1 > 0
    bracket(f, (xl + 0.1, ys_T[0]), (xl + 0.1, ys_S[1]), low('σ', 1),
            side=-1, off=0.08, anchor='start')
    for y in (ys_S[1], ys_T[0]):
        f.line((xl2 - 0.04, y), (xl + 0.2, y), stroke=FAINT, width=0.8,
               dash='3 3')
    f.save('seven-canonical-pair', 'A canonical pair with its markers a gap g '
           'apart, the four normals of S, and the shadows of the two squares '
           'on the two axes of S')


def octagon():
    a, u_, A, v, s, t, g = (CP[k] for k in ('a', 'u_', 'A', 'v', 's', 't', 'g'))
    cS, cT, d = pair(a, u_, A, v, s, t, g)
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
    f.text(shift(cS, (-0.18, 0.43)), 'Δ', size=15)
    f.text(shift(cS, (0.28, -0.27)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.05, 0.12)), 'T', size=17, color=GREEN)
    # right panel: the octagon K centred at O
    O = (off, 0.0)
    K = convex_hull([(p[0] + q[0], p[1] + q[1])
                     for p in square_corners((0, 0))
                     for q in square_corners((0, 0), dg)])
    f.polygon([shift(O, p) for p in K], fill=FILLS[1], stroke=ORANGE,
              width=1.6)
    normals = [(0, 'e', '1'), (PI / 2, 'e', '2'), (d, 'f', '1'),
               (d + PI / 2, 'f', '2')]
    for ang, base, sub in normals:
        for sgn in (1, -1):
            n = u(ang + (0 if sgn == 1 else PI))
            foot = shift(O, n, W)
            tang = (-n[1], n[0])
            f.line(shift(foot, tang, -0.95), shift(foot, tang, 0.95),
                   stroke=FAINT, width=0.9, dash='4 3')
            f.line(foot, shift(foot, n, 0.3), stroke=INK, width=1.2,
                   arrow=True)
            name = ('' if sgn == 1 else '−') + low(base, sub)
            f.text(shift(foot, n, 0.44), name, size=13)
    PD = shift(O, D)
    f.dot(O)
    f.line(O, PD, stroke=INK, width=1.4, arrow=True)
    f.dot(PD, r=3.6)
    f.text(shift(PD, (-0.08, 0.1)), 'Δ', size=15, anchor='end')
    # the support sum on the inward axis: the distance to the line x = -W
    s2 = W + D[0]
    assert abs(s2 - sigma(a, u_, A, v, s, t, 2, g)) < 1e-9
    y0 = PD[1] - 0.22
    f.line((O[0] - W, y0), (PD[0], y0), stroke=BLUE, width=2.4)
    for x in (O[0] - W, PD[0]):
        f.line((x, y0 - 0.05), (x, y0 + 0.05), stroke=BLUE, width=1.4)
    f.text(((O[0] - W + PD[0]) / 2, y0 - 0.14),
           low('σ', 2) + ' &lt; 0', size=13, color=BLUE)
    f.text(shift(O, (0.55, -0.55)), 'K', size=17, color=ORANGE)
    f.save('seven-octagon', 'The canonical pair with the vector Delta between '
           'the centres, and the octagon of differences of the two squares, '
           'whose eight edges are perpendicular to the edge directions of the '
           'two squares; Delta lies outside it beyond one edge')


def contacts():
    A = 1.0
    specs = [
        # (a, u, s), (A, v, t): kinds (1), (2), (3)
        ((1.0, 0.5, -1), (1.0, 0.5, 1), 1),
        ((1.0, 0.5, 1), (A, 0.0, 1), 2),
        ((A, 0.0, 1), (1.0, 0.5, -1), 1),
    ]
    off = 2.55
    f = Figure(-0.75, 2 * off + 1.75, -1.15, 1.72, 108)
    for j, ((a, u_, s), (B, v, t), k) in enumerate(specs):
        o = (j * off, 0.0)
        cS, cT, d = pair(a, u_, B, v, s, t, PI / 3)
        dg = math.degrees(d)
        assert abs(sigma(a, u_, B, v, s, t, k, PI / 3)) < 1e-12
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
        m1 = s * label(a, u_)
        for m, color in ((m1, BLUE), (m1 + PI / 3, GREEN)):
            f.line(o, shift(o, u(m), 1.0), stroke=color, width=1.5)
        f.arc(o, 0.3, m1, m1 + PI / 3, INK, width=1.2)
        f.text(shift(o, u(m1 + PI / 6), 0.45), 'π/3', size=12, italic=False)
        f.dot(o)
        f.text(shift(o, (-0.05, -0.08)), 'o', anchor='end')
        f.text(shift(o, shift(cS, (0.3, -0.3))), 'S', size=16, color=BLUE)
        f.text(shift(o, shift(cT, (-0.3, 0.3))), 'T', size=16, color=GREEN)
        f.text(shift(o, (0.5, 1.62)), f'({j + 1})', size=15, italic=False)
    f.save('seven-contacts', 'The three kinds of contact as canonical pairs '
           'at the gap pi/3: two side squares, a side square and an axial '
           'square, an axial square and a side square')


def small_gaps():
    a, u_, A, v, s, t, g = 1.0, 0.45, 1.05, 0.25, 1, -1, 0.8
    assert admissible(a, u_) and admissible(A, v)
    cS, cT, d = pair(a, u_, A, v, s, t, g)
    dg = math.degrees(d)
    lam = s * label(a, u_)
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
    f.line((0, 0), u(mid), stroke=ORANGE, width=1.2, dash='4 3')
    f.text(shift((0, 0), u(mid), 1.12), 'm', size=15, color=ORANGE)
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text(shift(cS, (0.3, -0.3)), 'S', size=17, color=BLUE)
    f.text(shift(cT, (-0.3, 0.35)), 'T', size=17, color=GREEN)
    f.save('seven-small-gaps', 'The marker arcs of a canonical pair at a gap '
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
    f.save('seven-leftmost', 'A continuous function positive at alpha, '
           'nonnegative at beta and somewhere negative, whose minimum is '
           'attained on a stretch; x is the left end of the stretch')


def parallel_pairs():
    # d = 0: S below the axis, T above it
    a, u_, A, v, s, t = 0.9, 0.55, 1.0, 0.5, -1, 1
    g1 = label(a, u_) + label(A, v)
    assert admissible(a, u_) and admissible(A, v) and g1 >= PI / 3
    cS, cT, d = pair(a, u_, A, v, s, t, g1)
    assert abs(d) < 1e-12 and not overlap(square_corners(cS),
                                          square_corners(cT))
    # d = pi/2: T to the upper left of S
    a2, u2, A2, v2, s2, t2 = 1.2, 0.05, 1.0, 0.15, 1, -1
    g2 = PI / 2 - s2 * label(a2, u2) + t2 * label(A2, v2)
    assert admissible(a2, u2) and admissible(A2, v2) and g2 >= PI / 3
    cS2, cT2, d2 = pair(a2, u2, A2, v2, s2, t2, g2)
    assert abs(d2 - PI / 2) < 1e-12
    assert not overlap(square_corners(cS2), square_corners(cT2))
    off = 2.6
    f = Figure(-0.55, off + 1.85, -1.15, 1.72, 118)
    for o, (S, T, m1, m2, dd) in (
            ((0.0, 0.0), (cS, cT, s * label(a, u_), s * label(a, u_) + g1, 0)),
            ((off, 0.0), (cS2, cT2, s2 * label(a2, u2),
                          s2 * label(a2, u2) + g2, 90))):
        thin_arc(f, o, 1.0, rad(-80), rad(130))
        f.square(shift(o, S), fill=FILLS[0], stroke=BLUE)
        f.square(shift(o, T), dd, fill=FILLS[2], stroke=GREEN)
        for m, color in ((m1, BLUE), (m2, GREEN)):
            f.line(o, shift(o, u(m), 1.0), stroke=color, width=1.5)
        f.arc(o, 0.3, m1, m2, INK, width=1.2)
        f.text(shift(o, u((m1 + m2) / 2), 0.45), 'g', size=14)
        f.dot(o)
        f.text(shift(o, (-0.05, -0.08)), 'o', anchor='end')
        f.text(shift(o, shift(S, (0.3, -0.3))), 'S', size=16, color=BLUE)
        f.text(shift(o, shift(T, (0.3, 0.3))), 'T', size=16, color=GREEN)
    ysep = (cS[1] + 0.5 + cT[1] - 0.5) / 2
    f.line((-0.5, ysep), (1.8, ysep), stroke=INK, width=1.4, dash='6 4')
    xsep = off + (cS2[0] - 0.5 + cT2[0] + 0.5) / 2
    f.line((xsep, -1.1), (xsep, 1.45), stroke=INK, width=1.4, dash='6 4')
    f.text((0.6, 1.62), 'd = 0', size=14, italic=False)
    f.text((off + 0.6, 1.62), 'd = π/2', size=14, italic=False)
    f.save('seven-parallel', 'A parallel canonical pair separated by a '
           'horizontal line, and a quarter-turned one separated by a '
           'vertical line')


def nearest_vertex():
    A, v, t = 0.85, 0.68, 1
    assert admissible(A, v)
    c = (A, t * v)
    V = (A - 0.5, t * (v - 0.5))
    delta = math.hypot(*V)
    assert delta < 0.5
    n = (-V[0] / delta, -V[1] / delta)
    # the support of T in the direction n is -delta, attained at V
    corners = square_corners(c)
    assert abs(support(c[0], c[1], math.atan2(n[1], n[0])) + delta) < 1e-12
    assert max(p[0] * n[0] + p[1] * n[1] for p in corners) <= -delta + 1e-12
    f = Figure(-0.42, 1.45, -0.3, 1.25, 260)
    f.square(c, fill=FILLS[2], stroke=GREEN)
    tang = (-n[1], n[0])
    f.line(shift(V, tang, -0.55), shift(V, tang, 0.75), stroke=INK,
           width=1.2, dash='5 4')
    f.line((0, 0), V, stroke=ORANGE, width=2.2)
    f.text(shift((V[0] / 2, V[1] / 2), tang, 0.06), 'δ', size=16,
           color=ORANGE)
    f.line(V, shift(V, n, 0.3), stroke=INK, width=1.6, arrow=True)
    f.text(shift(V, n, 0.36), 'u(z)', size=14, anchor='end')
    f.dot(V, r=4, fill=ORANGE)
    f.text(shift(V, (0.03, -0.07)), '(A − ½, t(v − ½))', size=13,
           anchor='start')
    f.dot(c, fill=GREEN)
    f.text(shift(c, (0.04, 0.07)), '(A, tv)', size=13, anchor='start',
           color=GREEN)
    f.dot((0, 0))
    f.text((-0.04, -0.07), 'o', anchor='end')
    f.text(shift(c, (0.3, 0.32)), 'T', size=17, color=GREEN)
    f.save('seven-nearest-vertex', 'The square T in its own chart, its vertex '
           'nearest to the disk centre at distance delta, and the direction '
           'from that vertex towards the centre')


def gap_profile():
    a, u_, A, v, s, t = 1.0, 0.5, 1.0, 0.5, -1, 1
    gmax = PI / 2
    vs = 0.45                      # vertical scale of the graph
    curves = [[(gmax * j / 400, sigma(a, u_, A, v, s, t, k, gmax * j / 400))
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
        f.text((gg + 0.03, vs * val), low('σ', k), size=14, color=cols[k],
               anchor='start')
    assert abs(sigma(a, u_, A, v, s, t, 1, PI / 3)) < 1e-12
    f.dot((PI / 3, 0), r=4, fill=ORANGE)
    f.save('seven-gap-profile', 'The four support sums of the pair of a side '
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
    for c, name, k in zip(cs, kinds, cols):
        pos = shift(c, (0.0, 0.3 if c[1] > 0 else -0.3))
        if c[0] == 0:
            pos = shift(c, (0.0, 0.3 if c[1] > 0 else -0.3))
        f.text(pos, name, size=13, italic=False, color=COLORS[k])
    f.dot((0, 0))
    f.text((0.05, -0.1), 'o', anchor='start')
    f.save('seven-ring', 'The ring of six exterior squares: the markers form '
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
    f.text((0, 1.13), '|x| ≤ ½', size=13, italic=False, color=ORANGE)
    f.text((1.45, 1.07), '|y| &lt; 1', size=13, italic=False, color=FAINT,
           anchor='end')
    f.save('seven-middle', 'The four side squares, the band between them and '
           'the strip in the middle; a tilted square containing the disk '
           'centre has a chord through its centre longer than 1 that pokes '
           'into the side squares; an axis-parallel square in the strip')


def main():
    columns()
    states()
    labels()
    marker()
    canonical()
    octagon()
    contacts()
    small_gaps()
    leftmost()
    parallel_pairs()
    nearest_vertex()
    gap_profile()
    ring()
    middle()


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw the figures of Chapter 9 (six squares) as SVG files in
docs/proof/figures/09-six/.

    python3 scripts/figures/fig_six.py

Every figure is computed from the definitions of the chapter: the constants
and the model, the circle of radius 9/10 and its arcs, the ceiling Q0 and its
constants, the pins, the separating axes and margins, the supports of a square
in a disk, and the stress of the model. Configurations that are not packings
of the disk (a missing wing, a tail) are drawn in a larger circle and checked
for the separations their captions state.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           sb, clip)
from fig_front import (arrow, arrowhead, polyline, word, it, sbn, rotate,
                       norm, dot2, interiors_meet, Plot)

PI = math.pi
H = math.sqrt(2) / 2
A_STAR = (1466 + 1940 * H) / 267
B_STAR = (327 + 432 * H) / 712
S = 2 * B_STAR / (A_STAR + math.sqrt(A_STAR ** 2 - 4 * B_STAR))
T = (30 * H - 20) * S + 3.5 - 4.5 * H
D = 0.5 + H - T
Q = 2 * S * S + 4 * S + 2.5
R6 = math.sqrt(Q)
RHO = math.sqrt(Q - 0.25) - 0.5
R_STAR = (S + 0.5) / (S + 1.5)
K_STAR = (T + 0.5) / (1.5 - S)
M_STAR = (1 + R_STAR) * K_STAR
KD = 2 * H * M_STAR
BETA = M_STAR * (0.5 - T)
Q0 = 2.85118
R0 = math.sqrt(Q0)
RHO0 = math.sqrt(Q0 - 0.25) - 0.5
C0 = RHO0 - 1
CORE = 1.5 - RHO0
A0 = 2 - RHO0
U0 = math.sqrt(Q0 - (2.5 - RHO0) ** 2) - 0.5
AUX = 0.9

GREEN, ORANGE, PURPLE, PINK, CYAN = (COLORS[2], COLORS[1], COLORS[3],
                                     COLORS[4], COLORS[5])
BLUE = COLORS[0]
RED = '#dc2626'
# The squares of the model: name, centre, angle in degrees, colours.
MODEL = [('C', (S, S), 0.0, GREY, FAINT),
         ('N', (S, S + 1), 0.0, FILLS[1], ORANGE),
         ('E', (S + 1, S), 0.0, FILLS[2], GREEN),
         ('W', (S - 1, T), 0.0, FILLS[3], PURPLE),
         ('S', (T, S - 1), 0.0, FILLS[4], PINK),
         ('D', (-D, -D), 45.0, FILLS[5], CYAN)]
STYLE = {name: (fill, stroke) for name, _, _, fill, stroke in MODEL}
PIN_ANGLES = {'E': 0.0, 'N': PI / 2, 'W': 11 * PI / 12, 'D': 5 * PI / 4,
              'S': 19 * PI / 12}


def save(f, name, title):
    """Save a figure of this chapter, in its directory."""
    assert name.startswith('09-six/'), name
    f.save(name, title)


def deg(t):
    return t * 180 / PI


def oriented(t, a, b):
    """The square Q_t(a, b): its centre and its angle in degrees."""
    c = (a * math.cos(t) - b * math.sin(t), a * math.sin(t) + b * math.cos(t))
    return c, deg(t)


def corners(sq):
    c, d = sq
    return square_corners(c, d)


def omega(t):
    return (abs(math.cos(t)) + abs(math.sin(t))) / 2


def tau(t):
    return 0.5 + omega(t)


def phi(a, b):
    return (a + 0.5) ** 2 + (b + 0.5) ** 2


def pin(name, r=AUX):
    return shift((0, 0), u(PIN_ANGLES[name]), r)


def model_squares():
    return {name: (c, d) for name, c, d, _, _ in MODEL}


def check_model():
    sq = model_squares()
    names = list(sq)
    for i, p in enumerate(names):
        for q in names[i + 1:]:
            assert not interiors_meet(corners(sq[p]), corners(sq[q])), (p, q)
        assert all(norm(x) <= R6 + 1e-9 for x in corners(sq[p]))
    on = [x for p in names for x in corners(sq[p]) if abs(norm(x) - R6) < 1e-9]
    assert len(on) == 6, len(on)
    for name in 'ENWDS':
        assert in_open_square(pin(name), *sq[name])
    return on


ON_CIRCLE = check_model()


def draw_squares(f, squares, labels=True, size=17, faint=(), shift_to=(0, 0),
                 width=1.5):
    for name, (c, d) in squares.items():
        fill, stroke = STYLE.get(name[0], (FILLS[0], BLUE))
        if name in faint:
            fill, stroke = '#f3f4f6', FAINT
        f.polygon([shift(shift_to, q) for q in square_corners(c, d)],
                  fill=fill, stroke=stroke, width=width)
        if labels:
            f.text(shift(shift_to, c), name[0], size=size,
                   color=FAINT if name in faint else stroke)


def origin(f, at=(0, 0), label=True, dx=0.06, dy=-0.07):
    f.dot(at, r=2.8)
    if label:
        f.text(shift(at, (dx, dy)), 'o', size=14, anchor='start')


def segment_overlap(a0, a1, b0, b1):
    return max(a0, b0), min(a1, b1)


def contacts(f, width=3.4):
    """The six edge contacts and the two vertex contacts of the model."""
    lo, hi = S - 0.5, S + 0.5
    segs = [((lo, hi), (hi, hi)),                    # C-N
            ((hi, lo), (hi, hi)),                    # C-E
            ((lo, T - 0.5), (lo, hi)),               # C-W
            ((T - 0.5, lo), (hi, lo)),               # C-S
            ((lo, hi), (lo, T + 0.5)),               # W-N
            ((hi, lo), (T + 0.5, lo))]               # S-E
    for a, b in segs:
        f.line(a, b, stroke=INK, width=width)
    for v in ((-D, T - 0.5), (T - 0.5, -D)):
        f.dot(v, r=4.6)


# ------------------------------------------------------------ 9.1 the model

def model_figure():
    m = R6 + 0.1
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.2, dash='6 4')
    draw_squares(f, model_squares())
    contacts(f)
    for x in ON_CIRCLE:
        f.dot(x, r=2.6)
    origin(f)
    save(f, '09-six/six', 'The six-square model in its circle of radius R6, with its '
         'eight contacts and the six points on the circle')


def clip_box(poly, x0, x1, y0, y1):
    for a, b, c in ((1, 0, x1), (-1, 0, -x0), (0, 1, y1), (0, -1, -y0)):
        poly = clip(poly, a, b, c)
    return poly


def construction():
    sq = model_squares()
    m = R6 + 0.08
    f = Figure(-m, m + 2.75, -m, m, 120)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, sq, size=15)
    x0 = T - 0.5
    lo = S - 0.5
    f.line((x0, -m + 0.08), (x0, lo + 0.12), stroke=ORANGE, width=1.4,
           dash='5 4')
    f.line((-m + 0.08, x0), (lo + 0.12, x0), stroke=ORANGE, width=1.4,
           dash='5 4')
    k = 2 * S - 1
    f.line((-0.98, k + 0.98), (0.15, k - 0.15), stroke=BLUE, width=1.4,
           dash='5 4')
    f.text((x0 + 0.05, -m + 0.2), 'x = t* − ½', size=12, anchor='start',
           italic=False, color=ORANGE)
    f.text((-m + 0.14, x0 + 0.11), 'y = t* − ½', size=12, anchor='start',
           italic=False, color=ORANGE)
    f.text((0.17, k - 0.24), 'x + y = 2s* − 1', size=12, anchor='start',
           italic=False, color=BLUE)
    origin(f)
    # The corner between W and S, enlarged, at the right.
    win = (-1.0, 0.1, -1.0, 0.1)
    z = 2.35
    at = (m + 0.25, -1.3)

    def Z(p):
        return shift(at, ((p[0] - win[0]) * z, (p[1] - win[2]) * z))

    for name in ('C', 'W', 'S', 'D'):
        c, d = sq[name]
        poly = clip_box(square_corners(c, d), *win)
        if len(poly) < 3:
            continue
        fill, stroke = STYLE[name]
        f.polygon([Z(q) for q in poly], fill=fill, stroke=stroke)
    f.polygon([Z((win[0], win[2])), Z((win[1], win[2])),
               Z((win[1], win[3])), Z((win[0], win[3]))], stroke=FAINT,
              width=1.0)
    vt, vr = (-D, T - 0.5), (T - 0.5, -D)
    for v in (vt, vr):
        f.dot(Z(v), r=4.4)
    f.text(Z((-0.62, -0.62)), 'D', size=17, color=CYAN)
    f.text(Z((-0.75, 0.03)), 'W', size=16, color=PURPLE)
    f.text(Z((0.03, -0.75)), 'S', size=16, color=PINK)
    f.text(Z((-0.18, -0.18)), 'C', size=16, color=FAINT)
    f.text(shift(Z(vt), (0.05, -0.2)), '(−d*, t* − ½)', size=12,
           italic=False, anchor='start')
    f.text(shift(Z(vr), (-0.12, 0.12)), '(t* − ½, −d*)', size=12,
           italic=False, anchor='end')
    # The window in the left panel.
    f.polygon([(win[0], win[2]), (win[1], win[2]), (win[1], win[3]),
               (win[0], win[3])], stroke=FAINT, width=1.0, dash='3 3')
    save(f, '09-six/construction', 'The lines that separate the turned square '
         'D from its neighbours, and the corner between W and S enlarged')


# ---------------------------------------------------------- 9.2 the arcs

def arcs_figure():
    sq = model_squares()
    m = R6 + 0.08
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, sq)
    f.circle((0, 0), AUX, stroke=INK, width=1.0, dash='2 3')
    total = 0.0
    for name in 'ENWDS':
        c, d = sq[name]
        runs = arcs_in(lambda p: in_open_square(p, c, d), AUX, steps=36000)
        assert len(runs) == 1
        t0, t1 = runs[0]
        total += t1 - t0
        assert t1 - t0 > 2 * 14 / 25
        f.arc((0, 0), AUX, t0, t1, STYLE[name][1], width=5)
        mid = (t0 + t1) / 2
        f.text(shift((0, 0), u(mid), AUX - 0.2), f'{deg(t1 - t0):.1f}°',
               size=12, italic=False, color=STYLE[name][1])
    c, d = sq['C']
    assert not arcs_in(lambda p: in_open_square(p, c, d), AUX)
    origin(f)
    save(f, '09-six/arcs', 'The arcs of the circle of radius 9/10 held by the '
         'five outer squares of the model')
    return total


def crossing_length(a, b, r=AUX):
    """The length min(A, U) + min(A, V) of the arc of Lemma 3.24 (1)."""
    def asin_ext(x):
        return math.copysign(PI / 2, x) if abs(x) >= 1 else math.asin(x)
    A = PI / 2 - asin_ext((a - 0.5) / r)
    V = asin_ext((0.5 - b) / r)
    U = asin_ext((b + 0.5) / r)
    return min(A, U) + min(A, V)


def chains(segs, digits=6):
    """Join segments that share end points into polylines."""
    def key(p):
        return (round(p[0], digits), round(p[1], digits))
    ends = {}
    for i, (a, b) in enumerate(segs):
        ends.setdefault(key(a), []).append(i)
        ends.setdefault(key(b), []).append(i)
    used, out = set(), []
    for i in range(len(segs)):
        if i in used:
            continue
        used.add(i)
        line = list(segs[i])
        for forward in (True, False):
            while True:
                end = line[-1] if forward else line[0]
                nxt = [j for j in ends.get(key(end), []) if j not in used]
                if not nxt:
                    break
                j = nxt[0]
                used.add(j)
                a, b = segs[j]
                q = b if key(a) == key(end) else a
                if forward:
                    line.append(q)
                else:
                    line.insert(0, q)
        out.append(line)
    return out


def marching(fn, x0, x1, y0, y1, nx, ny, level, inside):
    """Segments of the level line fn = level, by marching squares, kept where
    `inside` holds at both ends."""
    xs = [x0 + (x1 - x0) * i / nx for i in range(nx + 1)]
    ys = [y0 + (y1 - y0) * j / ny for j in range(ny + 1)]
    val = [[fn(x, y) for y in ys] for x in xs]
    segs = []
    for i in range(nx):
        for j in range(ny):
            cs = [(xs[i], ys[j], val[i][j]), (xs[i + 1], ys[j], val[i + 1][j]),
                  (xs[i + 1], ys[j + 1], val[i + 1][j + 1]),
                  (xs[i], ys[j + 1], val[i][j + 1])]
            pts = []
            for k in range(4):
                (xa, ya, va), (xb, yb, vb) = cs[k], cs[(k + 1) % 4]
                if (va - level) * (vb - level) < 0:
                    s = (level - va) / (vb - va)
                    pts.append((xa + s * (xb - xa), ya + s * (yb - ya)))
            if len(pts) == 2 and inside(*pts[0]) and inside(*pts[1]):
                segs.append(tuple(pts))
            elif len(pts) == 4:
                for a, b in ((pts[0], pts[1]), (pts[2], pts[3])):
                    if inside(*a) and inside(*b):
                        segs.append((a, b))
    return segs


def arc_region():
    def inside(a, b):
        return 0.5 <= a and 0 <= b <= a and phi(a, b) <= Q0
    amax, bmax = RHO0, 0.72
    f = Figure(0.34, amax + 0.17, -0.12, bmax + 0.06, 520)
    # The region: a polygon of its boundary.
    pts = []
    n = 200
    bs = [0.5 * k / n for k in range(n + 1)]
    pts.append((0.5, 0.0))
    pts.append((RHO0, 0.0))
    # Along the circle from (rho0, 0) up to the diagonal.
    a_diag = math.sqrt(Q0 / 2) - 0.5
    for k in range(n + 1):
        b = a_diag * k / n
        pts.append((math.sqrt(Q0 - (b + 0.5) ** 2) - 0.5, b))
    pts.append((0.5, 0.5))
    f.polygon(pts, fill=FILLS[0], stroke=BLUE, width=1.4)
    # Minimum of the length on a fine grid.
    best = (10.0, None)
    for i in range(301):
        for j in range(301):
            a = 0.5 + (RHO0 - 0.5) * i / 300
            b = a_diag * j / 300
            if inside(a, b):
                L = crossing_length(a, b)
                if L < best[0]:
                    best = (L, (a, b))
    assert best[0] > 2 * 14 / 25
    levels = [66, 70, 75, 80, 90]
    for lv in levels:
        segs = marching(lambda a, b: deg(crossing_length(a, b)), 0.5, RHO0,
                        0.0, a_diag, 160, 160, lv, inside)
        for a, b in segs:
            f.line(a, b, stroke=ORANGE, width=1.1)
        if segs:
            pts = [q for sg in segs for q in sg]
            top = max(pts, key=lambda q: q[0] + 2 * q[1])
            f.text(shift(top, (0.012, 0.012)), f'{lv}°', size=11,
                   italic=False, color=ORANGE, anchor='start')
    f.dot(best[1], r=4, fill=RED)
    f.text(shift(best[1], (-0.025, 0.02)), f'{deg(best[0]):.1f}°', size=12,
           italic=False, color=RED, anchor='end')
    # Axes.
    f.line((0.38, 0), (amax + 0.12, 0), width=1)
    f.line((0.5, -0.03), (0.5, bmax), stroke=FAINT, width=0.8, dash='3 3')
    for a, s in ((0.5, '½'), (0.75, '¾'), (1.0, '1'), (RHO0, 'ρ₀')):
        f.line((a, -0.012), (a, 0.012), width=1)
        word(f, (a, -0.045), s, size=12)
    f.text((amax + 0.13, 0.0), 'a', size=14, anchor='start')
    f.line((0.38, 0), (0.38, bmax), width=1)
    for b, s in ((0.25, '¼'), (0.5, '½')):
        f.line((0.372, b), (0.388, b), width=1)
        word(f, (0.36, b), s, size=12, anchor='end')
    f.text((0.38, bmax + 0.03), 'b', size=14)
    f.text((0.56, 0.6), 'b = a', size=12, italic=False, color=BLUE,
           anchor='end')
    save(f, '09-six/arc-region', 'The length of the arc of the circle of '
         'radius 9/10 held by an exterior square, over the offsets allowed by '
         'the ceiling')
    return best


# ------------------------------------------------------ separators of C

def margins(t, a, b, c):
    xc, yc = oriented(t, a, b)[0]
    ct, st = math.cos(t), math.sin(t)
    w = tau(t)
    return {'own': a - (c[0] * ct + c[1] * st) - w,
            'sec+': (b - (-c[0] * st + c[1] * ct)) - w,
            'sec-': -(b - (-c[0] * st + c[1] * ct)) - w,
            'east': xc - c[0] - w, 'west': c[0] - xc - w,
            'north': yc - c[1] - w, 'south': c[1] - yc - w}


def support_line(f, n, value, half=1.6, centre=None, **kw):
    """The line <p, n> = value, n a unit vector, drawn over a length 2 half
    about its point nearest to `centre` (default: the origin)."""
    c = centre or (0.0, 0.0)
    k = value - dot2(c, n)
    p0 = (c[0] + k * n[0], c[1] + k * n[1])
    d = (-n[1], n[0])
    f.line(shift(p0, d, -half), shift(p0, d, half), **kw)


def separators_figure():
    c = (0.03, 0.04)
    f = Figure(-0.95, 5.05, -1.05, 1.25, 120)
    # Left: separated along the east side of C.
    t1, a1, b1 = 0.08, 1.09, 0.05
    m1 = margins(t1, a1, b1, c)
    assert m1['east'] >= 0 and phi(a1, abs(b1)) <= Q0
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT)
    f.text(shift(c, (0.0, 0.22)), 'C', size=16, color=FAINT)
    T1 = oriented(t1, a1, b1)
    f.polygon(corners(T1), fill=FILLS[1], stroke=ORANGE)
    f.text(T1[0], 'T', size=16, color=ORANGE)
    f.line((c[0] + 0.5, -0.95), (c[0] + 0.5, 1.0), stroke=INK, dash='5 4')
    word(f, (c[0] + 0.5, 1.12), 'the east side of ' + it('C'), size=12)
    origin(f)
    # Right: separated along its own axis, at the left of C.
    sh = (3.75, 0.0)
    t2, a2, b2 = PI - 0.45, 1.2, 0.1
    m2 = margins(t2, a2, b2, c)
    assert m2['own'] >= 0 and m2['west'] < 0 and m2['north'] < 0
    cs = shift(sh, c)
    f.polygon(square_corners(cs), fill=GREY, stroke=FAINT)
    f.text(shift(cs, (0.0, 0.22)), 'C', size=16, color=FAINT)
    T2c, T2d = oriented(t2, a2, b2)
    f.polygon(square_corners(shift(sh, T2c), T2d), fill=FILLS[1],
              stroke=ORANGE)
    f.text(shift(sh, T2c), 'T', size=16, color=ORANGE)
    e1 = u(t2)
    val = dot2(c, e1) + omega(t2)
    # The support line of C perpendicular to the own axis of T.
    support_line(f, e1, val + dot2(sh, e1), half=0.95, centre=cs,
                 stroke=INK, dash='5 4')
    tip = shift(shift(sh, T2c), e1, 0.42)
    arrow(f, shift(sh, T2c), tip, color=ORANGE, size=8)
    f.text(shift(tip, (0.0, 0.12)), sb('e', '1'), size=13, color=ORANGE)
    origin(f, at=sh)
    word(f, (sh[0] - 0.25, -0.98), 'the own axis of ' + it('T'), size=12)
    save(f, '09-six/separators', 'A square separated from the containing square '
         'along a side of C, and one separated along its own axis')


def extreme_shallow(c, upper):
    """The normal n of the support line of C = Q(c) through its north-east
    (upper) or south-east corner at the depth rho0 - 1/2 from the origin,
    and the steepest such: the support values of C along the normals
    (cos s, +-sin s) for s from 0 to pi/2 decrease, then increase."""
    L = RHO0 - 0.5
    best = None
    for k in range(20001):
        sth = PI / 2 * k / 20000
        n = (math.cos(sth), math.sin(sth) if upper else -math.sin(sth))
        hv = dot2(c, n) + (abs(n[0]) + abs(n[1])) / 2
        if hv <= L:
            best = n
            break
    return best


def free_arc_figure():
    panels = [((0.24, 0.05), (-0.25, 0.45)), ((0.24, 0.2), (0.0, 0.7))]
    f = Figure(-1.2, 4.05, -1.25, 1.25, 120)
    L = RHO0 - 0.5
    for k, (c, (l, h)) in enumerate(panels):
        sh = (2.65 * k, 0.0)
        for upper in (True, False):
            n = extreme_shallow(c, upper)
            if n is None:
                continue
            # Shade the side beyond the line, inside a disc of radius 1.15.
            pts = []
            for j in range(181):
                q = shift((0, 0), u(2 * PI * j / 180), 1.15)
                pts.append(q)
            region = clip(pts, -n[0], -n[1], -L)
            f.polygon([shift(sh, q) for q in region], fill='#dbeafe',
                      stroke='none', opacity=0.8)
            support_line(f, n, L + dot2(sh, n), half=0.75,
                         centre=shift(sh, c), stroke=BLUE, width=1.2,
                         dash='5 4')
            for t in (l + 1e-6, h - 1e-6):
                q = (AUX * math.cos(t), AUX * math.sin(t))
                assert dot2(q, n) < L
        f.circle(sh, AUX, stroke=INK, width=1.0, dash='2 3')
        f.polygon([shift(sh, q) for q in square_corners(c)], fill=GREY,
                  stroke=FAINT)
        f.text(shift(sh, (c[0] - 0.08, c[1] + 0.25)), 'C', size=15,
               color=FAINT)
        f.arc(sh, AUX, l, h, RED, width=5)
        f.line(shift(sh, (c[0] + 0.5, -1.05)), shift(sh, (c[0] + 0.5, 1.05)),
               stroke=INK, width=1.0, dash='6 3')
        origin(f, at=sh)
        word(f, shift(sh, (0.0, -1.17)),
             'c' + '<tspan font-size="10" dy="4">y</tspan>'
             '<tspan dy="-4"> ' + ('≤' if k == 0 else '&gt;') + ' c</tspan>'
             '<tspan font-size="10" dy="4">0</tspan>', size=13)
    save(f, '09-six/free-arc', 'The free arc east of a containing square whose '
         'centre lies beyond the box, in the two regimes of Lemma 9.14')


def core_figure():
    c = (0.02, 0.05)
    f = Figure(-1.78, 1.78, -1.78, 1.78, 125)
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT)
    f.circle((0, 0), CORE, stroke=RED, width=1.4, fill='#fee2e2')
    f.polygon([(0, 0), (C0, 0), (C0, C0), (0, C0)], fill='#9ca3af',
              stroke=INK, width=0.8)
    # Two other squares, separated from C, outside the core.
    others = [(0.1, 1.08, 0.0, 'E'), (PI - 0.2, 1.09, 0.0, 'W')]
    for t, a, b, name in others:
        sq = oriented(t, a, b)
        assert not interiors_meet(corners(sq), square_corners(c))
        assert phi(a, abs(b)) <= Q0
        fill, stroke = STYLE[name]
        f.polygon(corners(sq), fill=fill, stroke=stroke)
        f.text(sq[0], name, size=15, color=stroke)
    t, a, b = others[0][:3]
    near = (a - 0.5)
    e1 = u(t)
    arrow(f, (0, 0), shift((0, 0), e1, a), color=GREEN, width=1.2, size=8)
    f.text(shift((0, 0), e1, a * 0.55), 'a ≥ a₀', size=12, italic=False,
           color=GREEN, dy=-12)
    f.text((CORE * 0.7, -CORE * 0.95), 'r₀', size=13, italic=False,
           color=RED)
    f.text((C0 + 0.05, C0 + 0.07), '[0, c₀]²', size=11, italic=False,
           anchor='start')
    origin(f, label=False)
    assert near >= CORE - 1e-9
    save(f, '09-six/core', 'The core: the disk of radius r0 about the origin '
         'inside the containing square, which the other squares avoid')


# ------------------------------------------------------------- deep caps

def cap_switch():
    return math.asin(1 / (2 * R0))


def cap_depth(t):
    if t <= cap_switch():
        return (RHO0 - 0.5) * math.cos(t) - 0.5 * math.sin(t)
    return R0 - math.cos(t) - math.sin(t)


def caps_figure():
    f = Figure(-1.85, 5.0, -1.85, 1.85, 105)
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    hgt = 0.45
    t, a, b = 0.15, 1.08, -0.05
    sq = oriented(t, a, b)
    xs = [q[0] for q in corners(sq)]
    assert min(xs) >= hgt - 1e-9 and phi(a, abs(b)) <= Q0
    assert in_open_square((hgt + 0.5, 0), *sq)
    disk = [shift((0, 0), u(2 * PI * j / 240), R0) for j in range(240)]
    f.polygon(clip(disk, -1, 0, -hgt), fill='#fef3c7', stroke='none')
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    f.line((hgt, -1.8), (hgt, 1.8), stroke=ORANGE, width=1.4)
    f.polygon(corners(sq), fill=FILLS[2], stroke=GREEN)
    f.dot((hgt + 0.5, 0), r=4, fill=RED)
    f.text((hgt + 0.52, -0.17), '(η + ½, 0)', size=12, italic=False,
           anchor='start', color=RED)
    f.text((hgt - 0.05, 1.6), 'x = η', size=13, anchor='end', color=ORANGE)
    origin(f)
    # The cap depth as a function of the angle.
    P = Plot(f, 2.35, -1.25, 2.4, 2.75, (0, PI / 4), (0, 0.7))
    P.axes('t', 'depth', xticks=[(0.203, '0.203'), (0.4, '⅖'),
                                 (PI / 4, 'π/4')],
           yticks=[(0.5, '½'), (CORE, 'r₀'), (RHO0 - 0.5, 'ρ₀ − ½')])
    P.curve(cap_depth, 0, PI / 4, stroke=GREEN, width=1.8)
    for lv, col in ((0.5, ORANGE), (CORE, RED)):
        polyline(f, [P.P(0, lv), P.P(PI / 4, lv)], stroke=col, width=1.0,
                 dash='4 3')
    sw = cap_switch()
    f.dot(P.P(sw, cap_depth(sw)), r=3)
    word(f, shift(P.P(sw, cap_depth(sw)), (0.08, 0.1)), 'switch', size=11,
         anchor='start')
    assert cap_depth(0.203) < 0.5 and cap_depth(0.4) < CORE
    save(f, '09-six/caps', 'A square in a deep cap, and the depth of the '
         'deepest cap that holds a square at a given angle')


# ----------------------------------------------------------- the pins

def pins_figure(name='09-six/pins', chords=False):
    sq = model_squares()
    m = R6 + 0.06
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, sq, labels=False)
    for name_, (c, _) in sq.items():
        v = (c[0] / norm(c), c[1] / norm(c))
        if chords:
            v = rotate(v, 0.9)
        out = shift(c, v, 0.32)
        f.text(out, name_, size=15, color=STYLE[name_][1])
    f.circle((0, 0), AUX, stroke=INK, width=1.0, dash='2 3')
    order = 'ENWDS'
    if not chords:
        for i, a in enumerate(order):
            b = order[(i + 1) % 5]
            f.line(pin(a), pin(b), stroke=FAINT, width=1.0)
    for name_ in order:
        f.dot(pin(name_), r=4.4, fill=STYLE[name_][1])
        lab = shift((0, 0), u(PIN_ANGLES[name_]), AUX - 0.2)
        f.text(lab, sb('p', name_, size=14), size=14,
               color=STYLE[name_][1])
    if chords:
        for a, b in (('W', 'N'), ('S', 'E')):
            arrow(f, pin(a), pin(b), color=INK, width=1.6, size=10)
        tw = model_squares()
        # The four axes selected by each chord, drawn at the centres.
        sel = {'W': [(1, 0), (0, 1)], 'N': [(0, 1), (1, 0)],
               'S': [(0, 1), (1, 0)], 'E': [(1, 0), (0, 1)]}
        for name_, vecs in sel.items():
            c = tw[name_][0]
            for v in vecs:
                arrow(f, c, shift(c, v, 0.32), color=STYLE[name_][1],
                      width=1.4, size=7)
    origin(f)
    save(f, name, 'The five pins on the circle of radius 9/10 in the model'
         + (', and the chords from W to N and from S to E with the axes they '
            'select' if chords else ''))


def sixty_figure():
    f = Figure(-0.3, 6.3, -0.75, 1.62, 125)
    cases = [(0.12, 0.95, -0.28), (0.95, 1.03, 0.1), (PI / 6, 0.88, 0.0)]
    for k, (t, a, b) in enumerate(cases):
        sh = (2.15 * k, 0.0)
        assert phi(a, abs(b)) <= Q0 and abs(b) < 0.5 and 0 <= t <= PI / 3
        sq = oriented(t, a, b)
        p1, p2 = (AUX, 0.0), shift((0, 0), u(PI / 3), AUX)
        ins = (in_open_square(p1, *sq), in_open_square(p2, *sq))
        assert any(ins)
        f.arc(sh, AUX, -0.25, PI / 3 + 0.25, FAINT, width=1.2)
        f.polygon([shift(sh, q) for q in corners(sq)], fill=FILLS[0],
                  stroke=BLUE)
        f.line(sh, shift(sh, p1), stroke=FAINT, width=0.9, dash='3 3')
        f.line(sh, shift(sh, p2), stroke=FAINT, width=0.9, dash='3 3')
        for p, inside in zip((p1, p2), ins):
            f.dot(shift(sh, p), r=4.2, fill=RED if inside else INK)
        origin(f, at=sh, label=False)
        word(f, shift(sh, (0.75, -0.62)),
             it('t') + f' = {t:.2f}' if k < 2 else it('t') + ' = π/6',
             size=12)
    save(f, '09-six/sixty', 'Three squares turned by an angle between 0 and 60 '
         'degrees, each holding one of the points of the circle of radius '
         '9/10 at 0 and 60 degrees')


WINDOWS = {'E': (0.0, -5 / 12, 3 / 10), 'N': (PI / 2, -3 / 10, 5 / 12),
           'W': (PI, -2 / 3, 5 / 8), 'D': (5 * PI / 4, -15 / 14, 15 / 14),
           'S': (3 * PI / 2, -5 / 8, 2 / 3)}


def windows_figure():
    f = Figure(-1.55, 1.55, -1.55, 1.55, 135)
    radii = {'E': 1.05, 'N': 1.05, 'W': 1.2, 'D': 0.85, 'S': 1.35}
    for name in sorted(WINDOWS, key=lambda k: -radii[k]):
        th, lo, hi = WINDOWS[name]
        r = radii[name]
        col = STYLE[name][1]
        pts = [(0, 0)] + [shift((0, 0), u(th + lo + (hi - lo) * k / 60), r)
                          for k in range(61)]
        f.polygon(pts, fill=STYLE[name][0], stroke=col, width=1.0,
                  opacity=0.55)
        arrow(f, (0, 0), shift((0, 0), u(th), r + 0.08), color=col,
              width=1.6, size=8)
        f.dot(pin(name), r=4, fill=col)
        f.text(shift((0, 0), u(th), r + 0.2), name, size=15, color=col)
    f.circle((0, 0), AUX, stroke=INK, width=0.8, dash='2 3')
    origin(f)
    save(f, '09-six/windows', 'The windows of the phases of the five labelled '
         'squares, as sectors of directions')


# ------------------------------------------------------------- supports

def supports_figure():
    f = Figure(-1.8, 9.0, -1.9, 1.85, 88)
    configs = []
    th = math.atan(0.6)
    a, b = R0 * math.cos(th) - 0.5, R0 * math.sin(th) - 0.5
    configs.append(((a, b), th, (a + 0.5, b + 0.5)))
    configs.append(((RHO0, 0.0), 0.0, (RHO0 + 0.5, 0.5)))
    th3 = math.atan(0.2)
    assert math.tan(th3) <= 1 / (2 * RHO0 + 1)
    configs.append(((RHO0, 0.0), th3, (RHO0 + 0.5, 0.5)))
    for k, (c, th_, far) in enumerate(configs):
        sh = (3.6 * k, 0.0)
        assert phi(abs(c[0]), abs(c[1])) <= Q0 + 1e-9
        f.circle(sh, R0, stroke=INK, width=1.0, dash='6 4')
        f.polygon([shift(sh, q) for q in square_corners(c)], fill=FILLS[2],
                  stroke=GREEN)
        f.dot(shift(sh, c), r=2.6, fill=GREEN)
        n = u(th_)
        arrow(f, sh, shift(sh, n, 0.7), color=RED, width=1.8, size=9)
        val = dot2(far, n)
        best = max(dot2(q, n) for q in square_corners(c))
        assert abs(best - val) < 1e-9
        support_line(f, n, val + dot2(sh, n), half=0.75,
                     centre=shift(sh, far), stroke=INK, dash='5 4')
        f.dot(shift(sh, far), r=4, fill=INK)
        origin(f, at=sh)
    word(f, (0, -1.85), 'far vertex', size=13)
    word(f, (3.6, -1.85), 'along an axis', size=13)
    word(f, (7.2, -1.85), 'the cap', size=13)
    save(f, '09-six/supports', 'The far vertex, centre and cap supports of a '
         'square in the disk of radius R0')


# --------------------------------------------------- the stress of the model

def stress_figure(name='09-six/stress', contacts_mode=False):
    sq = model_squares()
    m = R6 + 0.08
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, sq, labels=False)
    cen = {k: v[0] for k, v in sq.items()}
    forces = {'E': (1, R_STAR), 'N': (R_STAR, 1),
              'W': (-(1 + R_STAR), M_STAR), 'S': (M_STAR, -(1 + R_STAR)),
              'D': (-M_STAR, -M_STAR)}
    # Edges: (source, target, normal, weight).
    edges = [('C', 'E', (1, 0), 1.0), ('C', 'N', (0, 1), 1.0),
             ('C', 'W', (-1, 0), 1.0), ('C', 'S', (0, -1), 1.0),
             ('W', 'N', (1, 0), R_STAR), ('S', 'E', (0, 1), R_STAR),
             ('W', 'D', (0, -1), M_STAR), ('D', 'S', (1, 0), M_STAR)]
    tot = {k: [0.0, 0.0] for k in cen}
    for s_, t_, nrm, w in edges:
        tot[t_][0] += w * nrm[0]
        tot[t_][1] += w * nrm[1]
        tot[s_][0] -= w * nrm[0]
        tot[s_][1] -= w * nrm[1]
    for k, v in forces.items():
        assert abs(tot[k][0] - v[0]) < 1e-12 and abs(tot[k][1] - v[1]) < 1e-12
    assert abs(tot['C'][0]) < 1e-12 and abs(tot['C'][1]) < 1e-12
    if contacts_mode:
        contacts(f)
    else:
        labels = {1.0: '1', R_STAR: 'r*', M_STAR: 'm*'}
        for s_, t_, nrm, w in edges:
            a, b = cen[s_], cen[t_]
            arrow(f, shift(a, (b[0] - a[0], b[1] - a[1]), 0.18),
                  shift(a, (b[0] - a[0], b[1] - a[1]), 0.78), color=FAINT,
                  width=1.0, size=7)
            mid = shift(a, (b[0] - a[0], b[1] - a[1]), 0.5)
            f.text(shift(mid, (0.07, 0.07)), labels[w], size=12,
                   italic=False, color=INK)
    for k, F in forces.items():
        c = cen[k]
        Ln = norm(F)
        target = shift(c, F, 0.42 / Ln)
        arrow(f, c, target, color=STYLE[k][1], width=2.6, size=10)
        if k != 'D':
            corner = max(square_corners(c), key=lambda q: norm(q))
            assert abs(norm(corner) - R6) < 1e-9
            # The force is parallel to the far corner, seen from the origin.
            assert abs(corner[0] * F[1] - corner[1] * F[0]) < 1e-9
            assert corner[0] * F[0] + corner[1] * F[1] > 0
            f.line((0, 0), corner, stroke=STYLE[k][1], width=1.0,
                   dash='2 3')
            f.dot(corner, r=3.4, fill=STYLE[k][1])
        else:
            for v in ((-D - H, -D), (-D, -D - H)):
                f.dot(v, r=3.4, fill=CYAN)
    for k in ('C', 'N', 'E', 'W', 'S', 'D'):
        off = (-0.2, 0.2) if k != 'C' else (-0.22, 0.24)
        f.text(shift(cen[k], off), k, size=15, color=STYLE[k][1])
    origin(f)
    save(f, name, 'The stress of the model: its edges with their weights and '
         'the forces on the squares' if not contacts_mode else
         'The eight contacts of the model and the forces of its stress, which '
         'point at the corners on the circle')


# ------------------------------------------------------- the west stress

def west_stress_figure():
    c = (0.06, 0.05)
    f = Figure(-2.0, 4.6, -1.75, 1.35, 105)
    tW, aW, bW = PI - 0.3, 1.1, 0.18
    tD, aD, bD = PI + 0.15, 1.05, -0.05
    W_, D_ = oriented(tW, aW, bW), oriented(tD, aD, bD)
    mW, mD = margins(tW, aW, bW, c), margins(tD, aD, bD, c)
    assert mW['own'] >= 0 and mD['west'] >= 0
    assert interiors_meet(corners(W_), corners(D_))
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT)
    f.text(c, 'C', size=15, color=FAINT)
    for sq, name, off in ((W_, 'W', (-0.05, 0.42)), (D_, 'D', (-0.1, -0.25))):
        fill, stroke = STYLE[name]
        f.polygon(corners(sq), fill=fill, stroke=stroke, opacity=0.75)
        f.text(shift(sq[0], off), name, size=15, color=stroke)
    # The separating lines: own axis of W (support line of C along e1 of W)
    e1 = u(tW)
    v = dot2(c, e1) + omega(tW)
    support_line(f, e1, v, half=1.2, stroke=PURPLE, dash='5 4', width=1.1)
    f.line((c[0] - 0.5, -1.7), (c[0] - 0.5, 1.2), stroke=CYAN, dash='5 4',
           width=1.1)
    # Forces of the west stress (weights 9/20, 3/10, 1/4, with W-D along the
    # secondary axis of W): on C, W, D.
    z = tW - PI
    FW = (-(9 / 20) * math.cos(z) - (1 / 4) * math.sin(z),
          -(9 / 20) * math.sin(z) + (1 / 4) * math.cos(z))
    FC = (3 / 10 + (9 / 20) * math.cos(z), (9 / 20) * math.sin(z))
    FD = (-3 / 10 + (1 / 4) * math.sin(z), -(1 / 4) * math.cos(z))
    assert abs(FW[0] + FC[0] + FD[0]) < 1e-12
    assert abs(FW[1] + FC[1] + FD[1]) < 1e-12
    for p, F, col in ((c, FC, INK), (W_[0], FW, PURPLE), (D_[0], FD, CYAN)):
        arrow(f, p, shift(p, F, 0.9), color=col, width=2.2, size=9)
    origin(f, label=False)
    # The triangle of the angles (t, u).
    P = Plot(f, 2.1, -1.4, 2.2, 2.5, (-0.75, 0.5), (-0.5, 0.5))
    P.axes('t', 'u', xticks=[(-2 / 3, '−⅔'), (0.4, '⅖')],
           yticks=[(-0.4, '−⅖'), (0.4, '⅖')])
    tri = [(-2 / 3, -2 / 5), (-2 / 5, -2 / 5), (2 / 5, 2 / 5), (-2 / 3, 2 / 5)]
    f.polygon([P.P(*q) for q in tri], fill=FILLS[3], stroke=PURPLE,
              opacity=0.6)
    polyline(f, [P.P(-2 / 3, 0), P.P(0, 0)], stroke=PURPLE, width=1.0,
             dash='3 3')
    polyline(f, [P.P(0, 0), P.P(0, 2 / 5)], stroke=PURPLE, width=1.0,
             dash='3 3')
    verts = [(-2 / 3, -2 / 5), (-2 / 5, -2 / 5), (-2 / 3, 0), (0, 0),
             (-2 / 3, 2 / 5), (0, 2 / 5), (2 / 5, 2 / 5)]
    for q in verts:
        f.dot(P.P(*q), r=3.6, fill=PURPLE)
    save(f, '09-six/west-stress', 'W on its own axis and D on the west side of '
         'C, with the separating lines and the forces of the west stress, and '
         'the triangle of their angles with its seven vertices')


# ------------------------------------------------- a normalized packing

def normalized_figure():
    c = (0.07, 0.04)
    conf = {'E': (0.18, 1.23, 0.1), 'N': (PI / 2 - 0.12, 1.19, 0.1),
            'W': (PI - 0.22, 1.25, -0.13), 'D': (PI + 0.66, 1.155, 0.31),
            'S': (3 * PI / 2 + 0.2, 1.12, 0.28)}
    sqs = {'C': (c, 0.0)}
    for name, (t, a, b) in conf.items():
        sqs[name] = oriented(t, a, b)
    names = list(sqs)
    for i, p in enumerate(names):
        for q in names[i + 1:]:
            assert not interiors_meet(corners(sqs[p]), corners(sqs[q])), (p, q)
    for name in 'ENWDS':
        assert in_open_square(pin(name), *sqs[name]), name
    # E, N and W are on their matching sides, D and S on their own axes.
    side = {'E': 'east', 'N': 'north', 'W': 'west', 'D': 'west',
            'S': 'south'}
    for name, (t, a, b) in conf.items():
        mg = margins(t, a, b, c)
        assert (mg[side[name]] >= 0) == (name in 'ENW'), name
        assert name in 'ENW' or mg['own'] >= 0, name
    Rn = max(norm(q) for p in names for q in corners(sqs[p]))
    m = Rn + 0.1
    f = Figure(-m, m, -m, m, 140)
    f.circle((0, 0), Rn, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, sqs, size=15)
    f.circle((0, 0), AUX, stroke=INK, width=1.0, dash='2 3')
    for name in 'ENWDS':
        f.dot(pin(name), r=3.6, fill=STYLE[name][1])
    base = {'E': 0.0, 'N': PI / 2, 'W': PI, 'D': PI, 'S': 3 * PI / 2}
    lab = {'E': 'e', 'N': 'n', 'W': 'w', 'D': 'd', 'S': 's'}
    for name, (t, a, b) in conf.items():
        r = 0.7 if name != 'D' else 0.78
        th0 = base[name]
        col = STYLE[name][1]
        f.line((0, 0), shift((0, 0), u(th0), r + 0.12), stroke=FAINT,
               width=0.8, dash='2 3')
        f.line((0, 0), shift((0, 0), u(t), r + 0.12), stroke=col, width=1.0)
        lo, hi = sorted((th0, t))
        pts = [shift((0, 0), u(lo + (hi - lo) * k / 30), r)
               for k in range(31)]
        polyline(f, pts, stroke=col, width=1.6)
        f.text(shift((0, 0), u((lo + hi) / 2), r + 0.11), lab[name],
               size=13, color=col)
    origin(f)
    save(f, '09-six/normalized', 'The angles e, n, w, d, s of a labelled '
         'configuration of six squares about a containing square')
    return Rn


# --------------------------------------------------------------- the wings

def sep_value(Ua, Va, n):
    """<n, c_V - c_U> for squares given as (centre, deg)."""
    return dot2(n, (Va[0][0] - Ua[0][0], Va[0][1] - Ua[0][1]))


def wings_figure():
    f = Figure(-1.85, 6.4, -2.05, 1.08, 108)
    w, d, s = -0.47, 0.57, 0.19
    panels = [
        # The model corner: (phase, a, b) of W, D and S.
        {'W': (PI, 1 - S, -T), 'D': (1.25 * PI, RHO, 0.0),
         'S': (1.5 * PI, 1 - S, T)},
        # A missing west wing.
        {'W': (PI + w, 1.1, -0.08), 'D': (PI + d, 1.06, 0.26),
         'S': (1.5 * PI + s, 0.96, 0.42)},
        # A missing south wing: the reflection of the second panel, which
        # maps Q_t(a, b) to Q_{pi/2 - t}(a, -b) and exchanges W and S.
        {'W': (PI - s, 0.96, -0.42), 'D': (PI + PI / 2 - d, 1.06, -0.26),
         'S': (1.5 * PI - w, 1.1, 0.08)}]
    expect = [('W', 'S'), ('D', 'S'), ('W', 'D')]
    for k, pan in enumerate(panels):
        sh = (2.65 * k, 0.0)
        sq = {name: oriented(*v) for name, v in pan.items()}
        names = list(sq)
        for i_, p_ in enumerate(names):
            for q_ in names[i_ + 1:]:
                assert not interiors_meet(corners(sq[p_]), corners(sq[q_]))
        for name, sqr in sq.items():
            fill, stroke = STYLE[name]
            f.polygon([shift(sh, q) for q in corners(sqr)], fill=fill,
                      stroke=stroke)
            f.text(shift(sh, sqr[0]), name, size=14, color=stroke)
        e2 = {name: u(pan[name][0] + PI / 2) for name in pan}
        def margin(U, V, n):
            turn = pan[V][0] - pan[U][0]
            return sep_value(sq[U], sq[V], n) - tau(turn)
        wd = [x for x in ('W', 'D') if margin('W', 'D', e2[x]) >= -1e-12]
        ds = [x for x in ('D', 'S') if margin('D', 'S', e2[x]) >= -1e-12]
        assert wd == [expect[k][0]] if k else wd[0] == 'W', (k, wd)
        assert ds == [expect[k][1]] if k else ds[0] == 'S', (k, ds)
        for (U, V), x in ((('W', 'D'), wd[0]), (('D', 'S'), ds[0])):
            n = e2[x]
            far = max(dot2(n, q) for q in corners(sq[U]))
            mid = shift(sh, ((sq[U][0][0] + sq[V][0][0]) / 2,
                             (sq[U][0][1] + sq[V][0][1]) / 2))
            support_line(f, n, far + dot2(sh, n), half=0.6, centre=mid,
                         stroke=INK, dash='4 3', width=1.3)
        word(f, shift(sh, (-0.55, -1.95)), ('the model', 'missing west wing',
                                            'missing south wing')[k], size=13)
    save(f, '09-six/wings', 'The wings of the model, a missing west wing and a '
         'missing south wing')


# ---------------------------------------------------------------- the tails

def tails_figure():
    c = (0.08, 0.06)
    w, d, s = -11 / 25, 0.78, 0.19
    aW, bW = 1.15, -0.12
    W_ = oriented(PI + w, aW, bW)
    D_ = oriented(PI + d, 1.13, -0.07)
    S_ = oriented(1.5 * PI + s, 1.075, 0.24)
    sqs = {'C': (c, 0.0), 'W': W_, 'D': D_, 'S': S_}
    names = list(sqs)
    for i, p in enumerate(names):
        for q in names[i + 1:]:
            assert not interiors_meet(corners(sqs[p]), corners(sqs[q])), (p, q)
    assert margins(PI + w, aW, bW, c)['own'] >= 0
    e2W, e2S = u(PI + w + PI / 2), u(1.5 * PI + s + PI / 2)
    assert sep_value(W_, D_, e2W) >= tau(d - w)
    assert sep_value(D_, S_, e2S) >= tau(PI / 2 + s - d)
    Rn = max(norm(q) for p in names for q in corners(sqs[p]))
    m = Rn + 0.08
    f = Figure(-m, m, -m - 0.25, m, 135)
    f.circle((0, 0), Rn, stroke=INK, width=1.0, dash='6 4')
    f.circle((0, 0), R0, stroke=RED, width=1.0, dash='2 3')
    draw_squares(f, sqs, size=15)
    e1 = u(PI + w)
    support_line(f, e1, dot2(c, e1) + omega(w), half=1.0, stroke=PURPLE,
                 dash='5 4', width=1.1)
    # Forces of the west tail stress: weights 8/15 (C-W along the own axis
    # of W), 1/5 (C-S), 1/6 (W-D along e2 of W), 1/10 (D-S along e2 of S).
    FW = (8 / 15 * e1[0] - 1 / 6 * e2W[0], 8 / 15 * e1[1] - 1 / 6 * e2W[1])
    FD = (1 / 6 * e2W[0] - 1 / 10 * e2S[0], 1 / 6 * e2W[1] - 1 / 10 * e2S[1])
    for p, F, col in ((W_[0], FW, PURPLE), (D_[0], FD, CYAN)):
        arrow(f, p, shift(p, F, 0.9), color=col, width=2.2, size=9)
    origin(f, label=False)
    word(f, (0.0, -m - 0.12), f'dashed: radius {Rn:.3f}; dotted: radius '
         f'{R0:.4f}', size=12)
    save(f, '09-six/tails', 'W on its own axis at the angle -11/25, with the '
         'separations and forces of the tail stress')
    return Rn


# --------------------------------------------------------- the stress bound

def pair_value(n, w, facet='W1', no=False, wo=False):
    """The value Pi(n, w) of Definition 9.48."""
    q = n - w
    def kappa(own, t):
        return (1.0, 0.0) if own else (math.cos(t), -math.sin(t))
    phi_ = {'W1': (-math.sin(q), -math.cos(q)), 'W2': (math.cos(q), -math.sin(q)),
            'N1': (1.0, 0.0), 'N2': (0.0, -1.0)}[facet]
    psi_ = {'W1': (1.0, 0.0), 'W2': (0.0, 1.0),
            'N1': (-math.sin(q), math.cos(q)), 'N2': (math.cos(q), math.sin(q))}[facet]
    kN, kW = kappa(no, n), kappa(wo, w)
    FN = (kN[0] + R_STAR * phi_[0], kN[1] + R_STAR * phi_[1])
    FW = (kW[0] + R_STAR * psi_[0], kW[1] + R_STAR * psi_[1] - M_STAR)
    def V(F):
        return R6 * norm(F) - (F[0] - F[1]) / 2
    BN = V(FN) if facet in ('W1', 'N2') else RHO * norm(FN)
    P = 0.0
    if no:
        P += C0 * (max(math.sin(n), 0) + 1 - math.cos(n))
    if wo:
        P += C0 * max(math.sin(w), 0)
    return (tau(n) + tau(w) + R_STAR * tau(n - w) + M_STAR / 2 - BN - V(FW)
            - P)


def line_l(w):
    return 0.72 * max(-w, 0) - 0.26 * max(w, 0)


def remainder(w, s, d):
    beta = (w - s) / 2
    delta = d - PI / 4 - (w + s) / 2
    L = KD * (math.cos(beta) - math.sin(beta))
    if 2 * R6 * abs(math.sin(delta)) <= 1:
        sig = RHO * L * math.cos(delta)
    else:
        sig = L * (R6 - (math.cos(delta) + abs(math.sin(delta))) / 2)
    Dv = M_STAR * (omega(d - w) + omega(d - s)) - sig
    return line_l(w) + line_l(-s) + Dv + 2 * BETA


def stress_bound_figure():
    f = Figure(-0.75, 6.1, -0.75, 2.8, 105)
    assert abs(pair_value(0, 0) - BETA) < 1e-12
    assert abs(remainder(0, 0, PI / 4)) < 1e-12
    # Left: the gap of the pair for the facet -e1^W, both on their sides.
    P = Plot(f, 0.0, 0.0, 2.6, 2.5, (-0.25, 0.25), (-0.4, 0.4))
    def gap(n, w):
        return pair_value(n, w) - (BETA + line_l(w) + abs(n) / 1000)
    mn = min(gap(-0.25 + 0.5 * i / 60, -0.4 + 0.8 * j / 60)
             for i in range(61) for j in range(61))
    assert mn > -1e-9
    for lv, col in ((0.002, BLUE), (0.01, BLUE), (0.03, BLUE), (0.06, BLUE),
                    (0.1, BLUE)):
        segs = marching(gap, -0.25, 0.25, -0.4, 0.4, 90, 90, lv,
                        lambda a, b: True)
        for line in chains(segs):
            polyline(f, [P.P(*q) for q in line], stroke=col, width=1.0)
    for x in (0.0,):
        polyline(f, [P.P(x, -0.4), P.P(x, 0.4)], stroke=FAINT, width=0.8,
                 dash='3 3')
    polyline(f, [P.P(-0.25, 0), P.P(0.25, 0)], stroke=FAINT, width=0.8,
             dash='3 3')
    polyline(f, [P.P(-0.25, -0.25), P.P(0.25, 0.25)], stroke=FAINT,
             width=0.8, dash='3 3')
    polyline(f, [P.P(-0.25, -0.4), P.P(0.25, -0.4), P.P(0.25, 0.4),
                 P.P(-0.25, 0.4), P.P(-0.25, -0.4)], stroke=INK, width=1.0)
    f.dot(P.P(0, 0), r=3.6, fill=RED)
    for x, lab in ((-0.25, '−¼'), (0.0, '0'), (0.25, '¼')):
        word(f, shift(P.P(x, -0.4), (0, -0.13)), lab, size=12)
    for y, lab in ((-0.4, '−⅖'), (0.0, '0'), (0.4, '⅖')):
        word(f, shift(P.P(-0.25, y), (-0.1, 0)), lab, size=12, anchor='end')
    f.text(shift(P.P(0.0, -0.4), (0, -0.33)), 'n', size=14)
    f.text(shift(P.P(-0.25, 0.4), (0.0, 0.18)), 'w', size=14)
    # Right: the remainder at d = pi/4.
    P2 = Plot(f, 3.3, 0.0, 2.6, 2.5, (-11 / 25, 2 / 5), (-2 / 5, 11 / 25))
    mn2 = min(remainder(-11 / 25 + (0.84) * i / 60, -0.4 + 0.84 * j / 60,
                        PI / 4) for i in range(61) for j in range(61))
    assert mn2 > -1e-9
    for lv in (0.005, 0.02, 0.05, 0.1, 0.15, 0.2):
        segs = marching(lambda w, s: remainder(w, s, PI / 4), -11 / 25, 2 / 5,
                        -2 / 5, 11 / 25, 90, 90, lv, lambda a, b: True)
        for line in chains(segs):
            polyline(f, [P2.P(*q) for q in line], stroke=GREEN, width=1.0)
    polyline(f, [P2.P(-11 / 25, -2 / 5), P2.P(2 / 5, -2 / 5),
                 P2.P(2 / 5, 11 / 25), P2.P(-11 / 25, 11 / 25),
                 P2.P(-11 / 25, -2 / 5)], stroke=INK, width=1.0)
    f.dot(P2.P(0, 0), r=3.6, fill=RED)
    for x, lab in ((-11 / 25, '−11/25'), (0.0, '0'), (2 / 5, '⅖')):
        word(f, shift(P2.P(x, -2 / 5), (0, -0.13)), lab, size=12)
    for y, lab in ((-2 / 5, '−⅖'), (0.0, '0'), (11 / 25, '11/25')):
        word(f, shift(P2.P(-11 / 25, y), (-0.1, 0)), lab, size=12,
             anchor='end')
    f.text(shift(P2.P(0.0, -2 / 5), (0, -0.33)), 'w', size=14)
    f.text(shift(P2.P(-11 / 25, 11 / 25), (0.0, 0.18)), 's', size=14)
    word(f, shift(P2.P(0.2, 11 / 25), (0, 0.15)), 'd = π/4', size=12)
    save(f, '09-six/stress-bound', 'Level lines of the gap of the pair estimate '
         'and of the remainder of the diagonal, which vanish only at the '
         'model')
    return mn, mn2


def main():
    model_figure()
    construction()
    total = arcs_figure()
    best = arc_region()
    separators_figure()
    free_arc_figure()
    core_figure()
    caps_figure()
    pins_figure()
    pins_figure('09-six/chords', chords=True)
    sixty_figure()
    windows_figure()
    supports_figure()
    stress_figure()
    stress_figure('09-six/contacts', contacts_mode=True)
    west_stress_figure()
    normalized_figure()
    wings_figure()
    tails_figure()
    stress_bound_figure()
    return total, best


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Draw the figures of Chapter 9 (six squares) as SVG files in
docs/proof/figures/09-six/.

    python3 scripts/figures/fig_six.py

Every figure is computed from the definitions of the chapter: the constants
and the model, the circle of radius 9/10 and its arcs, the ceiling Q0 and its
constants, the charts, the pins, the separating axes and margins, the supports
of a square in a disk, the stresses, and the pair and diagonal values.
Configurations that are not packings of the disk (a missing wing, a tail)
are drawn in a larger circle and checked for the separations their captions
state.
"""
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, arcs_in, u, shift,
                           sb, subsup, clip)
from fig_front import (arrow, polyline, word, it, rotate, NB, norm, dot2,
                       interiors_meet, Plot, thin_arc)

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


def nb(s):
    """Spaces outside the markup made non-breaking, as in sbn."""
    import re
    return ''.join(t if t.startswith('<') else t.replace(' ', NB)
                   for t in re.split(r'(<[^>]*>)', s))


def star(base, after='', size=15, italic=False):
    """A letter with a subscript asterisk, such as r_*, as SVG markup; the
    letter is italic inside upright text when `italic` is set."""
    d = 0.4 * size
    out = (it(base) if italic else base) + \
        f'<tspan dy="{d:.1f}" font-size="{0.75 * size:.1f}">*</tspan>'
    if after:
        out += f'<tspan dy="{-d:.1f}">{nb(after)}</tspan>'
    return out


def sub(base, low, after='', size=15):
    """An italic letter with an upright subscript inside upright text, as
    SVG markup (sb with the letter in italics and non-breaking spaces in
    the text after it)."""
    return sb(it(base), low, nb(after), size)


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


def corners_figure():
    """Lemma 9.2 (2): the far corners of E and S and a far vertex of D, at
    squared distance q* from the origin, with the legs of the three right
    triangles (the corner of S gives the same expression as that of W)."""
    sq = model_squares()
    m = R6 + 0.1
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    for name, (c, d) in sq.items():
        f.polygon(square_corners(c, d), fill='none', stroke=FAINT,
                  width=1.0)
    # The corner, and the vertex of the right angle of the triangle.
    tri = {'E': ((S + 1.5, S + 0.5), (S + 1.5, 0.0)),
           'S': ((T + 0.5, S - 1.5), (0.0, S - 1.5)),
           'D': ((-D - H, -D), (-D - H, 0.0))}
    for k, (q, r) in tri.items():
        assert abs(norm(q) ** 2 - Q) < 1e-12
        assert any(abs(q[0] - x[0]) + abs(q[1] - x[1]) < 1e-12
                   for x in corners(sq[k]))
        col = STYLE[k][1]
        polyline(f, [(0, 0), r, q], stroke=col, width=1.8)
        polyline(f, [(0, 0), q], stroke=col, width=1.0, dash='4 3')
        f.dot(q, r=4, fill=col)
        # the right angle at r
        u1 = (math.copysign(0.08, -r[0]) if r[0] else 0.0,
              math.copysign(0.08, -r[1]) if r[1] else 0.0)
        u2 = (math.copysign(0.08, q[0] - r[0]) if q[0] != r[0] else 0.0,
              math.copysign(0.08, q[1] - r[1]) if q[1] != r[1] else 0.0)
        f.polygon([r, shift(r, u1), shift(shift(r, u1), u2), shift(r, u2)],
                  stroke=col, width=1.0)
    lt = dict(size=14, italic=False)
    f.text(((S + 1.5) / 2, 0.13), star('s', ' + 3/2', size=14, italic=True),
           color=GREEN, **lt)
    f.text((S + 1.4, (S + 0.5) / 2), star('s', ' + ½', size=14,
           italic=True), color=GREEN, anchor='end', **lt)
    f.text((0.07, (S - 1.5) / 2 - 0.25), '3/2 − ' + star('s', size=14,
           italic=True), color=PINK, anchor='start', **lt)
    f.text(((T + 0.5) / 2, S - 1.62), star('t', ' + ½', size=14,
           italic=True), color=PINK, **lt)
    f.text((-(D + H) / 2 - 0.25, -0.14), star('d', ' + ' + it('h'), size=14,
           italic=True), color=CYAN, **lt)
    f.text((-D - H + 0.07, -D / 2), star('d', size=14, italic=True),
           color=CYAN, anchor='start', **lt)
    f.dot((0, 0), r=2.8)
    f.text((0.06, 0.12), 'o', size=14, anchor='start')
    for k, at in (('E', (1.25, -0.2)), ('S', (0.38, -1.17)),
                  ('D', (-0.78, -0.95))):
        f.text(at, k, size=16, color=STYLE[k][1])
    save(f, '09-six/corners', 'The far corners of E and S and a far vertex of '
         'D, each at squared distance q* from the origin, with the legs of '
         'the right triangles to them')


def clip_box(poly, x0, x1, y0, y1):
    for a, b, c in ((1, 0, x1), (-1, 0, -x0), (0, 1, y1), (0, -1, -y0)):
        poly = clip(poly, a, b, c)
    return poly


def construction():
    sq = model_squares()
    m = R6 + 0.08
    f = Figure(-m, m + 2.75, -m, m, 120)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    draw_squares(f, {k: v for k, v in sq.items() if k != 'C'}, size=15)
    f.polygon(square_corners(sq['C'][0]), fill=GREY, stroke=FAINT)
    f.text((0.33, 0.33), 'C', size=15, color=FAINT)
    x0 = T - 0.5
    lo = S - 0.5
    # D lies left of x = t* - 1/2 and below y = t* - 1/2; the other open
    # squares lie beyond these lines and beyond x + y = 2s* - 1.
    vt, vr = (-D, T - 0.5), (T - 0.5, -D)
    assert all(abs(abs(q[0] + D) + abs(q[1] + D) - H) < 1e-12
               for q in (vt, vr))
    f.line((x0, -m + 0.08), (x0, lo + 0.12), stroke=ORANGE, width=1.4,
           dash='5 4')
    f.line((-m + 0.08, x0), (lo + 0.12, x0), stroke=ORANGE, width=1.4,
           dash='5 4')
    k = 2 * S - 1
    f.line((-0.78, k + 0.78), (0.1, k - 0.1), stroke=BLUE, width=1.4,
           dash='5 4')
    tm = star('t', ' − ½', size=13, italic=True)
    f.text((x0 + 0.07, -1.32), it('x') + ' = ' + tm, size=13,
           anchor='start', italic=False, color=ORANGE)
    f.text((S - 1.43, x0 + 0.11), it('y') + ' = ' + tm, size=13,
           anchor='start', italic=False, color=ORANGE)
    f.text((0.17, k - 0.24), it('x') + ' + ' + it('y') + ' = 2'
           + star('s', ' − 1', size=13, italic=True), size=13,
           anchor='start', italic=False, color=BLUE)
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
    # The half-diagonal h of D, from its centre up to the vertex on W.
    cd = (-D, -D)
    f.line(Z(cd), Z(vt), stroke=CYAN, width=1.2, dash='4 3')
    f.dot(Z(cd), r=3.2, fill=CYAN)
    f.text(shift(Z(shift(cd, (0, H / 2))), (-0.1, 0)), it('h'), size=15,
           italic=False, color=CYAN, anchor='end')
    for v in (vt, vr):
        f.dot(Z(v), r=4.4)
    f.text(Z((-0.6, -0.86)), 'D', size=17, color=CYAN)
    f.text(Z((-0.5, 0.01)), 'W', size=16, color=PURPLE)
    f.text(Z((0.01, -0.93)), 'S', size=16, color=PINK)
    f.text(Z((-0.16, -0.12)), 'C', size=16, color=FAINT)
    f.text(shift(Z(vt), (0.0, 0.12)), '(−' + star('d', ', ', size=13,
           italic=True) + star('t', ' − ½)', size=13, italic=True), size=13)
    f.text(shift(Z(vr), (-0.14, 0.0)), '(' + star('t', ' − ½, −', size=13,
           italic=True) + star('d', ')', size=13, italic=True), size=13,
           anchor='end')
    # The window in the left panel.
    f.polygon([(win[0], win[2]), (win[1], win[2]), (win[1], win[3]),
               (win[0], win[3])], stroke=FAINT, width=1.0, dash='3 3')
    save(f, '09-six/construction', 'The lines that separate the turned square '
         'D from its neighbours, and the corner between W and S enlarged')


def shifted_model(s_):
    """The configuration of the remark on the constants for the shift s:
    C = Q(s, s), E and N beside it, the far corner of W on the circle
    through the far corner of E, S the mirror image of W, and D touching
    W and S. Returns the squares, t, d and the radii of the far corners
    of E and of D."""
    t = math.sqrt(s_ * s_ + 7 * s_ + 0.25) - 0.5
    d = 0.5 + H - t
    sq = {'C': ((s_, s_), 0.0), 'N': ((s_, s_ + 1), 0.0),
          'E': ((s_ + 1, s_), 0.0), 'W': ((s_ - 1, t), 0.0),
          'S': ((t, s_ - 1), 0.0), 'D': ((-d, -d), 45.0)}
    rE = math.sqrt(2 * s_ * s_ + 4 * s_ + 2.5)
    rD = math.sqrt(2 * d * d + 2 * H * d + 0.5)
    return sq, t, d, rE, rD


def constants_figure():
    s1 = 0.04
    sq, t1, d1, rE1, rD1 = shifted_model(s1)
    names = list(sq)
    for i, p_ in enumerate(names):
        for q_ in names[i + 1:]:
            assert not interiors_meet(corners(sq[p_]), corners(sq[q_]))
    assert abs(norm((s1 - 1.5, t1 + 0.5)) - rE1) < 1e-12
    assert abs(max(norm(q) for q in corners(sq['D'])) - rD1) < 1e-12
    m = rD1 + 0.06
    f = Figure(-m, m + 3.55, -m, m, 92)
    f.circle((0, 0), rE1, stroke=INK, width=1.0, dash='6 4')
    f.circle((0, 0), rD1, stroke=CYAN, width=1.0, dash='2 3')
    draw_squares(f, {k: v for k, v in sq.items() if k != 'C'}, size=15)
    f.polygon(square_corners(sq['C'][0]), fill=GREY, stroke=FAINT)
    f.text((0.26, 0.27), 'C', size=15, color=FAINT)
    for q in corners(sq['D']):
        if abs(norm(q) - rD1) < 1e-9:
            f.dot(q, r=3.4, fill=CYAN)
    f.dot((s1 + 1.5, s1 + 0.5), r=3.4, fill=GREEN)
    f.dot((s1 - 1.5, t1 + 0.5), r=3.4, fill=PURPLE)
    origin(f)
    f.text((-m + 0.05, m - 0.12), it('s') + ' = 0.04', size=13,
           italic=False, anchor='start')
    # The radii of the two circles against the shift s.
    P = Plot(f, m + 0.55, -1.6, 2.75, 3.2, (0, 0.1), (1.5, 2.3))
    P.axes(it('s'), '', xticks=[(0.04, '0.04')],
           yticks=[(1.6, '1.6'), (1.8, '1.8'), (2.0, '2.0'), (2.2, '2.2')],
           y_at=1.5)
    # D stays clear of C while s + d >= (1 + h)/2, that is s <= 0.0904.
    lo_, hi_ = 0.0, 0.1
    for _ in range(60):
        mid = (lo_ + hi_) / 2
        _, _, dm, _, _ = shifted_model(mid)
        lo_, hi_ = (mid, hi_) if mid + dm >= (1 + H) / 2 else (lo_, mid)
    smax = lo_
    P.curve(lambda x: shifted_model(x)[3], 0, smax, stroke=GREEN, width=1.8)
    P.curve(lambda x: shifted_model(x)[4], 0, smax, stroke=CYAN, width=1.8)
    assert abs(shifted_model(S)[3] - R6) < 1e-12
    assert abs(shifted_model(S)[4] - R6) < 1e-9
    q = P.P(S, R6)
    polyline(f, [P.P(S, 1.5), q, P.P(0, R6)], stroke=FAINT, width=1.0,
             dash='3 3')
    f.dot(q, r=3.8, fill=RED)
    f.text(shift(P.P(S, 1.5), (0, -0.17)), star('s', size=13, italic=True),
           size=13, italic=False)
    f.text(shift(P.P(0, R6), (-0.08, 0)), sb('R', '6', size=13), size=13,
           anchor='end')
    f.dot(P.P(s1, rE1), r=3.0, fill=GREEN)
    f.dot(P.P(s1, rD1), r=3.0, fill=CYAN)
    f.text(shift(P.P(0.002, shifted_model(0.002)[3]), (0.05, -0.16)),
           'far corners of ' + it('E') + ', ' + it('W'), size=13,
           italic=False, color=GREEN, anchor='start')
    f.text(shift(P.P(0.022, shifted_model(0.022)[4]), (0.12, 0.05)),
           'far vertex of ' + it('D'), size=13, italic=False, color=CYAN,
           anchor='start')
    save(f, '09-six/constants', 'The radius needed by the far corners of E '
         'and W and by the far vertex of D as the shift s of the central '
         'square varies; they balance at s*')
    return smax


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
    # Level lines; each is labelled at its left end on the side a = 1/2,
    # where it is horizontal (the length is U + V there, a function of b),
    # or, for 66 degrees, where it meets the circle.
    for lv in (66, 70, 75, 80, 90):
        segs = marching(lambda a, b: deg(crossing_length(a, b)), 0.5, RHO0,
                        0.0, a_diag, 360, 360, lv, inside)
        for line in chains(segs):
            polyline(f, line, stroke=ORANGE, width=1.1)
        q = [x for sg in segs for x in sg]
        left = min(q, key=lambda x: x[0])
        if left[0] < 0.51:
            f.text((0.51, left[1] + 0.017), f'{lv}°', size=12, italic=False,
                   color=ORANGE, anchor='start')
        # A piece that runs down from the side b = a to the circle.
        flat = left[1] + 0.05 if left[0] < 0.51 else 0.0
        top = [x for x in q if x[1] > flat and phi(*x) > Q0 - 0.03]
        if top:
            end = max(top, key=lambda x: x[0])
            f.text(shift(end, (0.012, 0.01)), f'{lv}°', size=12,
                   italic=False, color=ORANGE, anchor='start')
    f.dot(best[1], r=4, fill=RED)
    f.text(shift(best[1], (-0.025, 0.02)), f'{deg(best[0]):.1f}°', size=12,
           italic=False, color=RED, anchor='end')
    # Axes.
    f.line((0.38, 0), (amax + 0.12, 0), width=1)
    f.line((0.5, -0.03), (0.5, bmax), stroke=FAINT, width=0.8, dash='3 3')
    for a, s_ in ((0.5, '½'), (0.75, '¾'), (1.0, '1')):
        f.line((a, -0.012), (a, 0.012), width=1)
        word(f, (a, -0.045), s_, size=12)
    f.line((RHO0, -0.012), (RHO0, 0.012), width=1)
    f.text((RHO0, -0.045), sub('ρ', '0', size=13), size=13, italic=False)
    f.text((amax + 0.13, 0.0), 'a', size=14, anchor='start')
    f.line((0.38, 0), (0.38, bmax), width=1)
    for b, s_ in ((0.25, '¼'), (0.5, '½')):
        f.line((0.372, b), (0.388, b), width=1)
        word(f, (0.36, b), s_, size=12, anchor='end')
    f.text((0.38, bmax + 0.03), 'b', size=14)
    f.text((0.555, 0.615), it('b') + ' = ' + it('a'), size=13, color=BLUE,
           anchor='end', italic=False)
    save(f, '09-six/arc-region', 'The length of the arc of the circle of '
         'radius 9/10 held by an exterior square, over the offsets allowed by '
         'the ceiling')
    return best


def frame_figure():
    """Definition 9.9: the square Q_t(a, b) at t = 0.5, a = 1.05, b = 0.3,
    its centre reached by a along u(t) and b along u(t + pi/2), and its own
    and secondary axes."""
    t, a, b = 0.5, 1.05, 0.3
    sq = oriented(t, a, b)
    c = sq[0]
    assert abs(c[0] - (a * math.cos(t) - b * math.sin(t))) < 1e-12
    ys = [q[1] for q in corners(sq)]
    f = Figure(-0.85, 1.75, -0.25, max(ys) + 0.1, 160)
    polyline(f, [(0, 0), (1.6, 0)], stroke=FAINT, width=1.0, dash='3 3')
    polyline(f, [(0, 0), shift((0, 0), u(t), 1.62)], stroke=INK, width=1.0,
             dash='5 4')
    polyline(f, [(0, 0), shift((0, 0), u(t + PI / 2), 0.55)], stroke=INK,
             width=1.0, dash='5 4')
    f.polygon(corners(sq), fill=FILLS[1], stroke=ORANGE)
    thin_arc(f, (0, 0), 0.32, 0.0, t, color=INK, width=1.2)
    f.text(shift((0, 0), u(t / 2), 0.42), it('t'), size=15, italic=False)
    foot = shift((0, 0), u(t), a)
    polyline(f, [(0, 0), foot, c], stroke=BLUE, width=2.0)
    f.text(shift(shift((0, 0), u(t), 0.36), u(t + PI / 2), 0.12), it('a'),
           size=15, italic=False, color=BLUE)
    f.text(shift(shift(foot, u(t + PI / 2), b / 2), u(t), 0.1), it('b'),
           size=15, italic=False, color=BLUE)
    for v, w_, lab in ((u(t), u(t - PI / 2), '1'),
                       (u(t + PI / 2), u(t + PI), '2')):
        arrow(f, c, shift(c, v, 0.36), color=ORANGE, width=1.6, size=8)
        f.text(shift(shift(c, v, 0.3), w_, 0.13), sub('e', lab, size=15),
               size=15, italic=False, color=ORANGE)
    f.dot(c, r=3.2, fill=ORANGE)
    f.text(shift(shift((0, 0), u(t), 1.66), u(t + PI / 2), 0.0),
           it('u') + '(' + it('t') + ')', size=14, italic=False,
           anchor='start')
    f.text(shift((0, 0), u(t + PI / 2), 0.62), it('u') + '(' + it('t')
           + ' + π/2)', size=14, italic=False, anchor='end')
    f.dot((0, 0), r=2.8)
    f.text((0.04, -0.1), 'o', size=14, anchor='start')
    save(f, '09-six/frame', 'The square Q_t(a, b): its centre is a along '
         'u(t) and b along u(t + pi/2) from the origin, and its frame is '
         'its own axis e1 = u(t) and its secondary axis e2 = u(t + pi/2)')


def annulus_figure():
    """Lemma 9.31: two squares that avoid the core have their centres in
    the annulus a0 <= |c| <= rho0, so they are separated along a secondary
    axis; here U, V turned by 0.75 against each other, tight along e2 of U."""
    t, a, b = PI - 0.2, 0.98, -0.25
    dl = 0.75
    t2, a2 = t + dl, 1.02
    U_ = oriented(t, a, b)
    e2U = u(t + PI / 2)
    # b2 such that V is tight along e2 of U
    def gap(b2):
        V_ = oriented(t2, a2, b2)
        return sep_value(U_, V_, e2U) - tau(dl)
    lo, hi = -0.49, 0.49
    for _ in range(80):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if gap(mid) < 0 else (lo, mid)
    b2 = hi
    V_ = oriented(t2, a2, b2)
    assert abs(gap(b2)) < 1e-9 and abs(b2) < 0.5
    assert not interiors_meet(corners(U_), corners(V_))
    for sqr in (U_, V_):
        assert A0 <= norm(sqr[0]) <= RHO0
    f = Figure(-1.8, 1.3, -1.75, 1.25, 130)
    pts = ([shift((0, 0), u(2 * PI * k / 120), RHO0) for k in range(121)]
           + [shift((0, 0), u(-2 * PI * k / 120), A0) for k in range(121)])
    f.polygon(pts, fill=FILLS[0], stroke='none')
    f.circle((0, 0), RHO0, stroke=BLUE, width=1.0)
    f.circle((0, 0), A0, stroke=BLUE, width=1.0)
    f.circle((0, 0), CORE, stroke=RED, width=1.2, fill='#fee2e2')
    for sqr, k, col, fill in ((U_, 'U', ORANGE, FILLS[1]),
                              (V_, 'V', GREEN, FILLS[2])):
        f.polygon(corners(sqr), fill=fill, stroke=col, opacity=0.85)
        f.dot(sqr[0], r=3.2, fill=col)
    # The separating line along e2 of U.
    far = max(dot2(e2U, q) for q in corners(U_))
    support_line(f, e2U, far, half=0.75, centre=shift(U_[0], e2U, 0.5),
                 stroke=INK, width=1.3, dash='5 4')
    arrow(f, U_[0], shift(U_[0], e2U, 0.36), color=ORANGE, width=1.6,
          size=8)
    f.text(shift(shift(U_[0], e2U, 0.3), u(t), 0.17), subsup('e', '2', 'U',
           size=15), size=15, color=ORANGE)
    f.text(shift(U_[0], u(t), 0.28), 'U', size=16, color=ORANGE)
    f.text(shift(V_[0], u(t2), 0.28), 'V', size=16, color=GREEN)
    for r_, lab, ang in ((CORE, sub('r', '0', size=14), 0.35),
                         (A0, sub('a', '0', size=14), 0.62),
                         (RHO0, sub('ρ', '0', size=14), 0.9)):
        polyline(f, [(0, 0), shift((0, 0), u(ang), r_)], stroke=FAINT,
                 width=0.9)
        f.text(shift(shift((0, 0), u(ang), r_), u(ang), 0.1), lab, size=14,
               italic=False, anchor='start')
    f.dot((0, 0), r=2.8)
    f.text((0.05, -0.1), 'o', size=14, anchor='start')
    save(f, '09-six/annulus', 'Two squares that avoid the core, with their '
         'centres in the thin annulus between a0 and rho0, separated along '
         'the secondary axis of one of them')


def octagon_figure():
    """Lemma 9.11 for U axis-parallel at the origin and V turned by delta:
    V meets U exactly when c_V lies inside the octagon of the support
    function w_U + w_V, whose sides are perpendicular to the eight vectors
    and touch the circle of radius tau(delta)."""
    dl = 0.45
    tv = tau(dl)
    normals = sorted([(k * PI / 2) % (2 * PI) for k in range(4)]
                     + [(dl + k * PI / 2) % (2 * PI) for k in range(4)])
    octagon = []
    for i, a in enumerate(normals):
        b = normals[(i + 1) % 8] + (2 * PI if i == 7 else 0)
        octagon.append(shift((0, 0), u((a + b) / 2),
                             tv / math.cos((b - a) / 2)))
    # The octagon is the set of centres of V for which V meets U.
    for k in range(400):
        q = shift((0, 0), u(2 * PI * k / 400), 1.0)
        r_in = min(tv / dot2(q, u(a)) for a in normals if dot2(q, u(a)) > 0)
        for r_, inside in ((0.999 * r_in, True), (1.001 * r_in, False)):
            c_ = shift((0, 0), q, r_)
            assert interiors_meet(square_corners((0, 0)),
                                  square_corners(c_, deg(dl))) == inside
    f = Figure(-1.95, 1.95, -1.75, 2.05, 118)
    f.polygon(octagon, fill=FILLS[0], stroke=BLUE, width=1.2, dash='5 3')
    f.circle((0, 0), tv, stroke=INK, width=0.9, dash='2 3')
    f.polygon(square_corners((0, 0)), fill=GREY, stroke=FAINT)
    # V touches the corner of U, with its centre on the side of normal e1
    # of V, slid along that side away from the point of contact with the
    # circle.
    cV = shift(shift((0, 0), u(dl), tv), u(dl + PI / 2), 0.68)
    lam = [dot2(q, u(dl + PI / 2)) for q in octagon
           if abs(dot2(q, u(dl)) - tv) < 1e-9]
    assert min(lam) < 0.68 < max(lam)
    f.polygon(square_corners(cV, deg(dl)), fill=FILLS[1], stroke=ORANGE,
              opacity=0.85)
    # The separating line, perpendicular to e1 of V through the corner of U.
    corner = max(square_corners((0, 0)), key=lambda q: dot2(q, u(dl)))
    assert abs(dot2(corner, u(dl)) - omega(dl)) < 1e-12
    along = u(dl + PI / 2)
    f.line(shift(corner, along, -0.95), shift(corner, along, 0.8),
           stroke=INK, width=1.1, dash='5 4')
    # The eight vectors, at the points where the sides touch the circle.
    names = {0.0: ('1', 'U'), PI / 2: ('2', 'U'), dl: ('1', 'V'),
             dl + PI / 2: ('2', 'V')}
    for a in normals:
        foot = shift((0, 0), u(a), tv)
        arrow(f, foot, shift(foot, u(a), 0.3), color=INK, width=1.2, size=7)
        key = min(names, key=lambda x: abs(x - a))
        if abs(key - a) < 1e-9:
            low, up = names[key]
            side = -0.16 if key == dl else 0.0
            f.text(shift(shift(foot, u(a), 0.45), u(a + PI / 2), side),
                   subsup('e', low, up, size=15), size=15)
    polyline(f, [(0, 0), shift((0, 0), u(dl), tv)], stroke=INK, width=1.2)
    f.dot((0, 0), r=2.8)
    f.dot(cV, r=3.2, fill=ORANGE)
    f.text(shift(shift((0, 0), u(dl), 0.32), u(dl + PI / 2), 0.15),
           it('τ') + '(' + it('δ') + ')', size=14, italic=False)
    f.text((-0.3, -0.3), 'U', size=16, color=FAINT)
    f.text(shift(cV, u(dl + PI / 2), 0.23), 'V', size=16, color=ORANGE)
    save(f, '09-six/octagon', 'The centres of a square V turned by delta '
         'that meet a square U fill an octagon whose sides are perpendicular '
         'to the eight vectors and touch the circle of radius tau(delta)')


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
    f = Figure(-0.95, 5.05, -1.12, 1.18, 120)
    # Left: separated along the east side of C.
    t1, a1, b1 = 0.08, 1.09, 0.05
    m1 = margins(t1, a1, b1, c)
    assert m1['east'] >= 0 and phi(a1, abs(b1)) <= Q0
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT)
    f.text(shift(c, (0.0, 0.22)), 'C', size=16, color=FAINT)
    T1 = oriented(t1, a1, b1)
    f.polygon(corners(T1), fill=FILLS[1], stroke=ORANGE)
    f.text(T1[0], 'T', size=16, color=ORANGE)
    f.line((c[0] + 0.5, -0.9), (c[0] + 0.5, 0.95), stroke=INK, dash='5 4')
    origin(f)
    f.text((0.55, -1.03), 'along the east side of ' + it('C'), size=13,
           italic=False)
    # Right: separated along its own axis, at the left of C.
    sh = (3.75, 0.0)
    t2, a2, b2 = PI - 0.45, 1.2, 0.1
    m2 = margins(t2, a2, b2, c)
    assert m2['own'] >= 0 and m2['west'] < 0 and m2['north'] < 0
    cs = shift(sh, c)
    f.polygon(square_corners(cs), fill=GREY, stroke=FAINT)
    f.text(shift(cs, (0.0, 0.22)), 'C', size=16, color=FAINT)
    T2c, T2d = oriented(t2, a2, b2)
    ct = shift(sh, T2c)
    f.polygon(square_corners(ct, T2d), fill=FILLS[1], stroke=ORANGE)
    e1, e2 = u(t2), u(t2 + PI / 2)
    f.text(shift(shift(ct, e1, -0.17), e2, 0.2), 'T', size=16,
           color=ORANGE)
    val = dot2(c, e1) + omega(t2)
    # The support line of C perpendicular to the own axis of T.
    support_line(f, e1, val + dot2(sh, e1), half=0.95, centre=cs,
                 stroke=INK, dash='5 4')
    arrow(f, ct, shift(ct, e1, 0.42), color=ORANGE, size=8)
    f.text(shift(shift(ct, e1, 0.24), e2, -0.16), sub('e', '1', size=14),
           size=14, color=ORANGE, italic=False)
    origin(f, at=sh)
    f.text((sh[0] - 0.55, -1.03), 'along the own axis of ' + it('T'),
           size=13, italic=False)
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
        rel = ' ≤ ' if k == 0 else ' &gt; '
        f.text(shift(sh, (0.0, -1.17)), sub('c', it('y'), rel, size=14)
               + sub('c', '0', size=14), size=14, italic=False)
    save(f, '09-six/free-arc', 'The free arc east of a containing square whose '
         'centre lies beyond the box, in the two regimes of Lemma 9.14')


def core_figure():
    # C at the corner c = (c0, c0) of the box: the disk of radius
    # r0 = 1/2 - c0 about the origin touches its left and bottom sides.
    c = (C0, C0)
    f = Figure(-1.78, 1.78, -1.78, 1.78, 125)
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT)
    f.circle((0, 0), CORE, stroke=RED, width=1.4, fill='#fee2e2')
    f.polygon([(0, 0), (C0, 0), (C0, C0), (0, C0)], fill='#9ca3af',
              stroke=INK, width=0.8)
    assert abs((c[0] - 0.5) + CORE) < 1e-12
    # The squares W and S beyond the two sides that the disk touches.
    others = [(1.5 * PI + 0.15, 1.08, 0.0, 'S'), (PI - 0.2, 1.09, 0.0, 'W')]
    for t, a, b, name in others:
        sq = oriented(t, a, b)
        assert not interiors_meet(corners(sq), square_corners(c))
        assert phi(a, abs(b)) <= Q0 and a - 0.5 >= CORE
        fill, stroke = STYLE[name]
        f.polygon(corners(sq), fill=fill, stroke=stroke)
        f.text(shift(sq[0], u(t - PI / 2), 0.27), name, size=16, color=stroke)
    # Along the own axis of S: the near edge at a - 1/2 >= r0 from the
    # origin, the centre at a >= a0.
    t, a = others[0][:2]
    e1 = u(t)
    polyline(f, [(0, 0), shift((0, 0), e1, a)], stroke=PINK, width=1.2,
             dash='4 3')
    f.dot(shift((0, 0), e1, a), r=3.2, fill=PINK)
    f.dot(shift((0, 0), e1, a - 0.5), r=3.2, fill=PINK)
    f.text(shift(shift((0, 0), e1, a - 0.25), u(t + PI / 2), 0.11), '½',
           size=13, italic=False, color=PINK)
    f.text(shift(shift((0, 0), e1, a), u(t + PI / 2), 0.13), 'a', size=15,
           color=PINK)
    # The radius r0 to the point where the disk touches the left side.
    polyline(f, [(0, 0), (-CORE, 0)], stroke=RED, width=1.2)
    f.text((-CORE / 2, 0.08), sub('r', '0', size=14), size=14, color=RED,
           italic=False)
    f.dot(c, r=2.6)
    f.text(shift(c, (0.05, 0.06)), 'c', size=14, anchor='start')
    f.dot((0, 0), r=2.8)
    f.text((-0.05, -0.08), 'o', size=14, anchor='end')
    f.text((0.38, 0.42), 'C', size=16, color=FAINT)
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
    f = Figure(-1.85, 5.2, -1.85, 1.85, 105)
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    hgt = 0.45
    t, a, b = 0.15, 1.08, -0.05
    sq = oriented(t, a, b)
    xs = [q[0] for q in corners(sq)]
    assert min(xs) >= hgt - 1e-9 and phi(a, abs(b)) <= Q0 and hgt >= CORE
    assert in_open_square((hgt + 0.5, 0), *sq)
    disk = [shift((0, 0), u(2 * PI * j / 240), R0) for j in range(240)]
    f.polygon(clip(disk, -1, 0, -hgt), fill='#fef3c7', stroke='none')
    f.circle((0, 0), R0, stroke=INK, width=1.0, dash='6 4')
    f.line((hgt, -1.8), (hgt, 1.8), stroke=ORANGE, width=1.4)
    f.polygon(corners(sq), fill=FILLS[2], stroke=GREEN)
    f.dot((hgt + 0.5, 0), r=4, fill=RED)
    f.text((hgt + 0.52, -0.17), '(' + it('η') + ' + ½, 0)', size=13,
           color=RED, anchor='start', italic=False)
    f.text((hgt - 0.07, 1.3), it('x') + ' = ' + it('η'), size=14,
           color=ORANGE, anchor='end', italic=False)
    origin(f)
    # The depth of the deepest cap that holds a square turned by t.
    P = Plot(f, 2.35, -1.25, 2.6, 2.75, (0, 0.92), (0, 0.7))
    P.axes(it('t'), it('η'), xticks=[(0.203, '0.203'), (0.4, '⅖'),
                                     (PI / 4, 'π/4')])
    for y, lab in ((0.5, '½'), (CORE, sub('r', '0', size=13)),
                   (RHO0 - 0.5, sub('ρ', '0', ' − ½', size=13))):
        q = P.P(0, y)
        f.line(shift(q, (-0.04, 0)), shift(q, (0.04, 0)), width=1)
        f.text(shift(q, (-0.1, 0)), lab, size=13, anchor='end', italic=False)
    P.curve(cap_depth, 0, PI / 4, stroke=GREEN, width=1.8)
    for lv, col in ((0.5, ORANGE), (CORE, RED)):
        polyline(f, [P.P(0, lv), P.P(PI / 4, lv)], stroke=col, width=1.0,
                 dash='4 3')
        lo_, hi_ = 0.0, PI / 4
        for _ in range(60):
            mid = (lo_ + hi_) / 2
            lo_, hi_ = (mid, hi_) if cap_depth(mid) > lv else (lo_, mid)
        f.dot(P.P(lo_, lv), r=3.4, fill=col)
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
    # The names: outwards from the origin, or, with the chords, in the
    # directions left free by the short arrows and the pins.
    free = {'C': 45, 'N': 135, 'E': -45, 'W': 225, 'S': 225, 'D': 225}
    for name_, (c, _) in sq.items():
        v = (c[0] / norm(c), c[1] / norm(c))
        out = shift(c, v, 0.32)
        if chords:
            out = shift(c, u(math.radians(free[name_])), 0.27)
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
        # Drawn at the centres, or, for W and S, clear of the chords.
        at = {'W': (-1.2, 0.55), 'S': (0.5, -1.25)}
        for name_, vecs in sel.items():
            c = at.get(name_, tw[name_][0])
            assert in_open_square(c, *tw[name_])
            for v in vecs:
                arrow(f, c, shift(c, v, 0.32), color=STYLE[name_][1],
                      width=1.4, size=7)
    origin(f)
    save(f, name, 'The five pins on the circle of radius 9/10 in the model'
         + (', and the chords from W to N and from S to E with the axes they '
            'select' if chords else ''))


def sixty_figure():
    f = Figure(-0.3, 6.3, -0.95, 1.62, 125)
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
        lo = min(q[1] for q in corners(sq))
        assert lo > -0.75
        f.text(shift(sh, (0.75, -0.84)), it('t') + (f' = {t:.2f}' if k < 2
               else ' = π/6'), size=13, italic=False)
    save(f, '09-six/sixty', 'Three squares turned by an angle between 0 and 60 '
         'degrees, each holding one of the points of the circle of radius '
         '9/10 at 0 and 60 degrees')


WINDOWS = {'E': (0.0, -5 / 12, 3 / 10), 'N': (PI / 2, -3 / 10, 5 / 12),
           'W': (PI, -2 / 3, 5 / 8), 'D': (5 * PI / 4, -15 / 14, 15 / 14),
           'S': (3 * PI / 2, -5 / 8, 2 / 3)}


def windows_figure():
    f = Figure(-1.55, 1.55, -1.55, 1.55, 135)
    radii = {'E': 1.05, 'N': 1.05, 'W': 1.2, 'D': 0.85, 'S': 1.35}
    pins_ = []
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
        pins_.append((pin(name), col))
        f.text(shift((0, 0), u(th), r + 0.2), name, size=15, color=col)
    f.circle((0, 0), AUX, stroke=INK, width=0.8, dash='2 3')
    for q, col in pins_:
        f.dot(q, r=4, fill=col)
    origin(f)
    save(f, '09-six/windows', 'The windows of the phases of the five labelled '
         'squares, as sectors of directions')


def one_edge_figure():
    """The stress of one edge: U and V axis-parallel, the edge from U to V
    along n = (1, 0) with weight 1 and threshold tau(0) = 1, in the disk of
    radius sqrt(5)/2, where the centre bound rho = 1/2 is attained."""
    R = math.sqrt(5) / 2
    rho = math.sqrt(R * R - 0.25) - 0.5
    assert abs(rho - 0.5) < 1e-12
    cU, cV = (-rho, 0.0), (rho, 0.0)
    assert abs((cV[0] - cU[0]) - tau(0)) < 1e-12
    m = R + 0.08
    f = Figure(-m, m, -m, m, 140)
    f.circle((0, 0), R, stroke=INK, width=1.0, dash='6 4')
    f.polygon(square_corners(cU), fill=FILLS[0], stroke=BLUE)
    f.polygon(square_corners(cV), fill=FILLS[1], stroke=ORANGE)
    for q in square_corners(cU) + square_corners(cV):
        if abs(norm(q) - R) < 1e-12:
            f.dot(q, r=3.2)
    # The edge, from the centre of U to that of V.
    arrow(f, shift(cU, (0.12, 0)), shift(cV, (-0.12, 0)), color=FAINT,
          width=1.1, size=7)
    f.text((-0.15, 0.1), '1', size=14, italic=False)
    # The forces: n on V, -n on U.
    for c, sgn, col, lab in ((cV, 1, ORANGE, 'n'), (cU, -1, BLUE, '−n')):
        arrow(f, c, shift(c, (sgn * 0.42, 0)), color=col, width=2.4, size=10)
        f.text(shift(c, (sgn * 0.28, 0.12)), it('n') if sgn > 0 else
               '−' + it('n'), size=15, italic=False, color=col)
    for c in (cU, cV):
        f.dot(c, r=2.8)
    f.dot((0, 0), r=2.8)
    f.text((0.0, -0.13), 'o', size=14)
    f.text((-0.75, -0.3), 'U', size=16, color=BLUE)
    f.text((0.75, -0.3), 'V', size=16, color=ORANGE)
    save(f, '09-six/one-edge', 'The stress of one edge between two squares '
         'U and V, with the forces n on V and -n on U')


# ------------------------------------------------------------- supports

def supports_figure():
    # Only the right part of each disk is drawn: x >= -0.4.
    left, gap = -0.4, 0.25
    wide = R0 + 0.25 - left
    f = Figure(left, left + 3 * wide + 2 * gap, -1.98, R0 + 0.08, 112)
    th0 = PI - math.acos(-left / R0)
    configs = []
    th = math.atan(0.6)
    a, b = R0 * math.cos(th) - 0.5, R0 * math.sin(th) - 0.5
    configs.append(((a, b), th, (a + 0.5, b + 0.5)))
    configs.append(((RHO0, 0.0), 0.0, (RHO0 + 0.5, 0.5)))
    th3 = math.atan(0.2)
    assert math.tan(th3) <= 1 / (2 * RHO0 + 1)
    configs.append(((RHO0, 0.0), th3, (RHO0 + 0.5, 0.5)))
    names = ('the far vertex (1)', 'the centre (2)', 'the cap (3)')
    for k, (c, th_, far) in enumerate(configs):
        sh = ((wide + gap) * k, 0.0)
        assert phi(abs(c[0]), abs(c[1])) <= Q0 + 1e-9
        polyline(f, [shift(sh, u(-th0 + 2 * th0 * j / 120), R0)
                     for j in range(121)], stroke=INK, width=1.0,
                 dash='6 4')
        f.polygon([shift(sh, q) for q in square_corners(c)], fill=FILLS[2],
                  stroke=GREEN)
        f.dot(shift(sh, c), r=3.0, fill=GREEN)
        n = u(th_)
        tip = shift(sh, n, 0.5)
        arrow(f, sh, tip, color=RED, width=1.8, size=9)
        f.text(shift(shift(sh, n, 0.3), rotate(n, PI / 2), 0.13), 'F',
               size=15, color=RED)
        val = dot2(far, n)
        best = max(dot2(q, n) for q in square_corners(c))
        assert abs(best - val) < 1e-9
        support_line(f, n, val + dot2(sh, n), half=0.72,
                     centre=shift(sh, far), stroke=INK, dash='5 4')
        f.dot(shift(sh, far), r=4, fill=INK)
        f.dot(sh, r=2.8)
        f.text(shift(sh, (-0.05, -0.1)), 'o', size=14, anchor='end')
        word(f, shift(sh, (0.75, -1.88)), names[k], size=13)
    # The centre at distance rho0 in the middle panel.
    sh = (wide + gap, 0.0)
    y = -0.66
    for x in (0.0, RHO0):
        f.line(shift(sh, (x, y - 0.05)), shift(sh, (x, y + 0.05)), width=1)
    arrow(f, shift(sh, (RHO0 / 2, y)), shift(sh, (0, y)), size=7)
    arrow(f, shift(sh, (RHO0 / 2, y)), shift(sh, (RHO0, y)), size=7)
    f.text(shift(sh, (RHO0 / 2, y - 0.14)), sub('ρ', '0', size=14),
           size=14, italic=False)
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
        labels = {1.0: '1', R_STAR: star('r', size=14),
                  M_STAR: star('m', size=14)}
        # Where each weight is written: the fraction of the way along the
        # edge and the side of it (+1 to the left of the edge, -1 to the
        # right), clear of the other lines.
        place = {('C', 'E'): (0.40, -1), ('C', 'N'): (0.40, 1),
                 ('C', 'W'): (0.36, -1), ('C', 'S'): (0.40, 1),
                 ('W', 'N'): (0.62, -1), ('S', 'E'): (0.62, 1),
                 ('W', 'D'): (0.60, 1), ('D', 'S'): (0.40, 1)}
        for s_, t_, nrm, w in edges:
            a, b = cen[s_], cen[t_]
            v = (b[0] - a[0], b[1] - a[1])
            arrow(f, shift(a, v, 0.2), shift(a, v, 0.8), color=FAINT,
                  width=1.1, size=7)
            k, side = place[(s_, t_)]
            n_ = rotate((v[0] / norm(v), v[1] / norm(v)), side * PI / 2)
            f.text(shift(shift(a, v, k), n_, 0.11), labels[w], size=14,
                   italic=w != 1.0)
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
    # The names, on the side of each centre away from its force and edges.
    where = {'C': (0.2, 50), 'N': (0.24, 160), 'E': (0.26, -62),
             'W': (0.25, 215), 'S': (0.25, 250), 'D': (0.24, 150)}
    for k, (r_, a_) in where.items():
        f.text(shift(cen[k], u(math.radians(a_)), r_), k, size=16,
               color=STYLE[k][1])
    f.dot((0, 0), r=2.8)
    f.text((-0.05, -0.08), 'o', size=14, anchor='end')
    save(f, name, 'The stress of the model: its edges with their weights and '
         'the forces on the squares' if not contacts_mode else
         'The eight contacts of the model and the forces of its stress, which '
         'point at the corners on the circle')


def pin_order_figure():
    """Lemma 9.32: the chord from p_D to p_W has a negative projection on
    u(t + pi/2) for every phase t from pi - 2/3 to 5 pi/4."""
    sq = model_squares()
    f = Figure(-1.65, 0.66, -1.58, 0.97, 165)
    for name in ('C', 'W', 'D'):
        c, d = sq[name]
        fill, stroke = STYLE[name]
        f.polygon(square_corners(c, d), fill=fill, stroke=stroke, width=1.0,
                  opacity=0.45)
    thin_arc(f, (0, 0), AUX, 0.75 * PI, 1.55 * PI, color=INK, width=1.0,
             dash='2 3')
    pW, pD = pin('W'), pin('D')
    chord = (pW[0] - pD[0], pW[1] - pD[1])
    lo, hi = 1.5 * PI - 2 / 3, 1.75 * PI
    for k in range(101):
        t_ = lo + (hi - lo) * k / 100
        assert dot2(u(t_), chord) < 0
    mid = shift(pD, chord, 0.5)
    # The fan of the secondary axes, at the midpoint of the chord.
    fan = [mid] + [shift(mid, u(lo + (hi - lo) * k / 40), 0.42)
                   for k in range(41)]
    f.polygon(fan, fill=FILLS[2], stroke=GREEN, width=1.0, opacity=0.8)
    for t_, lab in ((1.5 * PI, 'W'), (1.75 * PI, 'D')):
        arrow(f, mid, shift(mid, u(t_), 0.42), color=GREEN, width=1.6,
              size=8)
        side = -PI / 2 if lab == 'W' else PI / 2
        f.text(shift(shift(mid, u(t_), 0.48), u(t_ + side), 0.15),
               subsup('e', '2', lab, size=15), size=15, color=GREEN)
    # The line through the midpoint perpendicular to the chord.
    nrm = (chord[0] / norm(chord), chord[1] / norm(chord))
    along = (-nrm[1], nrm[0])
    f.line(shift(mid, along, -0.55), shift(mid, along, 0.55), stroke=INK,
           width=1.0, dash='5 4')
    arrow(f, pD, pW, color=INK, width=1.6, size=10)
    for name, p_, off in (('W', pW, (-0.2, 0.05)), ('D', pD, (-0.02, -0.16))):
        f.dot(p_, r=4.2, fill=STYLE[name][1])
        f.text(shift(p_, off), sb('p', name, size=15), size=15,
               color=STYLE[name][1])
    f.dot((0, 0), r=2.8)
    f.text((0.06, -0.08), 'o', size=14, anchor='start')
    save(f, '09-six/pin-order', 'The chord from the pin of D to the pin of W '
         'and the fan of the secondary axes of squares at the phases of the '
         'windows of W and D, all pointing away from the chord')


def stress_radius_figure():
    """The weak form after Proposition 9.27: the threshold sum of the
    stress of the model against the sum of the supports at the radius R,
    which increases with R and meets it at R6."""
    FE, FW = math.hypot(1, R_STAR), (1 + R_STAR) * math.hypot(1, K_STAR)
    lhs = 4 + 2 * R_STAR + M_STAR * (1 + 2 * H)

    def rhs(R):
        rho = math.sqrt(R * R - 0.25) - 0.5
        return (2 * (R * FE - (1 + R_STAR) / 2)
                + 2 * (R * FW - (1 + R_STAR + M_STAR) / 2) + KD * rho)
    assert abs(rhs(R6) - lhs) < 1e-9
    f = Figure(-0.45, 3.05, -0.4, 2.75, 115)
    xl, yl = (1.55, 1.85), (6.0, 7.8)
    P = Plot(f, 0.15, 0.1, 2.6, 2.45, xl, yl)
    P.axes(it('R'), '', yticks=[(6.5, '6.5'), (7.5, '7.5')], x_at=xl[0],
           y_at=yl[0])
    for x, lab in ((1.6, '1.6'), (1.8, '1.8')):
        q = P.P(x, yl[0])
        f.line(shift(q, (0, -0.04)), shift(q, (0, 0.04)), width=1)
        word(f, shift(q, (0, -0.17)), lab, size=12)
    polyline(f, [P.P(xl[0], lhs), P.P(xl[1], lhs)], stroke=ORANGE,
             width=1.8)
    ends = []
    for target in yl:
        lo_, hi_ = 1.4, 2.0
        for _ in range(60):
            mid = (lo_ + hi_) / 2
            lo_, hi_ = (mid, hi_) if rhs(mid) < target else (lo_, mid)
        ends.append(min(max(lo_, xl[0]), xl[1]))
    P.curve(rhs, ends[0], ends[1], stroke=BLUE, width=1.8)
    q = P.P(R6, lhs)
    polyline(f, [q, P.P(R6, yl[0])], stroke=FAINT, width=1.0, dash='3 3')
    f.dot(q, r=3.8, fill=RED)
    f.text(shift(P.P(R6, yl[0]), (0, -0.17)), sb('R', '6', size=13),
           size=13)
    f.text(P.P(1.83, lhs + 0.1), 'thresholds', size=13, italic=False,
           color=ORANGE, anchor='end')
    f.text(P.P(1.8, rhs(1.8) - 0.12), 'supports', size=13, italic=False,
           color=BLUE, anchor='start')
    save(f, '09-six/stress-radius', 'The threshold sum of the stress of the '
         'model and the sum of its supports at the radius R, which meet at '
         'R6')


# ------------------------------------------------------- the west stress

def west_stress_figure():
    """W on its own axis, D on the west side of C and W, D separated along
    the secondary axis of W, all three separations tight, at the angles
    (t, u) = (-0.3, 0.15) of the triangle; such squares need a disk larger
    than the ceiling."""
    c = (0.06, 0.05)
    t, u_ = -0.3, 0.15
    e1W, e2W = u(PI + t), u(1.5 * PI + t)
    aW = dot2(c, e1W) + tau(t)
    aD, bD = None, 0.38
    aD = (bD * math.sin(u_) - c[0] + tau(u_)) / math.cos(u_)
    D_ = oriented(PI + u_, aD, bD)
    bW = dot2(e2W, D_[0]) - tau(u_ - t)
    W_ = oriented(PI + t, aW, bW)
    mW, mD = margins(PI + t, aW, bW, c), margins(PI + u_, aD, bD, c)
    assert abs(mW['own']) < 1e-12 and abs(mD['west']) < 1e-12
    assert abs(sep_value(W_, D_, e2W) - tau(u_ - t)) < 1e-12
    sqs = {'C': (c, 0.0), 'W': W_, 'D': D_}
    for p_, q_ in (('C', 'W'), ('C', 'D'), ('W', 'D')):
        assert not interiors_meet(corners(sqs[p_]), corners(sqs[q_]))
    Rn = max(norm(q) for k in sqs for q in corners(sqs[k]))
    assert Rn > R0
    f = Figure(-Rn - 0.08, 4.75, -Rn - 0.3, Rn + 0.08, 100)
    f.circle((0, 0), Rn, stroke=INK, width=1.0, dash='6 4')
    f.circle((0, 0), R0, stroke=RED, width=1.0, dash='2 3')
    draw_squares(f, sqs, labels=False)
    # The three separating lines.
    corner = (c[0] - 0.5, c[1] + 0.5)
    assert abs(dot2(corner, e1W) - dot2(c, e1W) - omega(t)) < 1e-12
    along = (-e1W[1], e1W[0])
    ends = sorted(dot2(shift(q, corner, -1), along) for q in corners(W_)
                  if abs(dot2(q, e1W) - dot2(corner, e1W)) < 1e-9)
    f.line(shift(corner, along, ends[0] - 0.3),
           shift(corner, along, ends[-1] + 0.12), stroke=PURPLE,
           dash='5 4', width=1.2)
    f.line((c[0] - 0.5, -1.25), (c[0] - 0.5, 0.9), stroke=CYAN, dash='5 4',
           width=1.2)
    support_line(f, e2W, dot2(e2W, W_[0]) + 0.5, half=0.75,
                 centre=shift(W_[0], e2W, 0.5), stroke=INK, dash='5 4',
                 width=1.2)
    # The forces of the west stress, with the weights 9/20, 3/10 and 1/4.
    FW = shift(shift((0, 0), e1W, 9 / 20), e2W, -1 / 4)
    FC = shift(shift((0, 0), e1W, -9 / 20), (1, 0), 3 / 10)
    FD = shift((-3 / 10, 0), e2W, 1 / 4)
    assert norm(shift(shift(FW, FC), FD)) < 1e-12
    for k, F in (('C', FC), ('W', FW), ('D', FD)):
        arrow(f, sqs[k][0], shift(sqs[k][0], F, 0.9),
              color=INK if k == 'C' else STYLE[k][1], width=2.2, size=9)
    for k, ang in (('C', 115), ('W', 15), ('D', 0)):
        f.text(shift(sqs[k][0], u(math.radians(ang)), 0.27), k, size=16,
               color=STYLE[k][1])
    f.dot((0, 0), r=2.8)
    f.text((0.05, -0.1), 'o', size=14, anchor='start')
    word(f, (0.0, -Rn - 0.18), f'dashed: radius {Rn:.3f}; dotted: radius '
         f'{R0:.4f}', size=12)
    # The triangle of the angles (t, u).
    P = Plot(f, 2.45, -1.4, 2.1, 2.5, (-0.75, 0.5), (-0.5, 0.5))
    tri = [(-2 / 3, -2 / 5), (-2 / 5, -2 / 5), (2 / 5, 2 / 5), (-2 / 3, 2 / 5)]
    f.polygon([P.P(*q) for q in tri], fill=FILLS[3], stroke=PURPLE,
              opacity=0.6)
    P.axes(it('t'), it('u'), xticks=[(-2 / 3, '−⅔'), (0.4, '⅖')],
           yticks=[(-0.4, '−⅖'), (0.4, '⅖')])
    polyline(f, [P.P(-2 / 3, 0), P.P(0, 0)], stroke=PURPLE, width=1.0,
             dash='3 3')
    polyline(f, [P.P(0, 0), P.P(0, 2 / 5)], stroke=PURPLE, width=1.0,
             dash='3 3')
    verts = [(-2 / 3, -2 / 5), (-2 / 5, -2 / 5), (-2 / 3, 0), (0, 0),
             (-2 / 3, 2 / 5), (0, 2 / 5), (2 / 5, 2 / 5)]
    for q in verts:
        f.dot(P.P(*q), r=3.6, fill=PURPLE)
    f.dot(P.P(t, u_), r=4.2, fill=INK)
    save(f, '09-six/west-stress', 'W on its own axis and D on the west side of '
         'C, separated along the secondary axis of W, with the separating '
         'lines and the forces of the west stress, and the triangle of their '
         'angles with its seven vertices')
    return Rn


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
    draw_squares(f, sqs, labels=False)
    f.circle((0, 0), AUX, stroke=INK, width=1.0, dash='2 3')
    for name in 'ENWDS':
        f.dot(pin(name), r=3.6, fill=STYLE[name][1])
    # Each angle at its square: from the direction of the own axis in the
    # model (dotted) to the own axis e1 of the square (arrow).
    base = {'E': 0.0, 'N': PI / 2, 'W': PI, 'D': PI, 'S': 3 * PI / 2}
    lab = {'E': 'e', 'N': 'n', 'W': 'w', 'D': 'd', 'S': 's'}
    for name, (t, a, b) in conf.items():
        cX = sqs[name][0]
        th0 = base[name]
        col = STYLE[name][1]
        f.line(cX, shift(cX, u(th0), 0.3), stroke=INK, width=1.0,
               dash='2 2')
        arrow(f, cX, shift(cX, u(t), 0.3), color=col, width=1.4, size=7)
        lo, hi = sorted((th0, t))
        polyline(f, [shift(cX, u(lo + (hi - lo) * k / 30), 0.2)
                     for k in range(31)], stroke=col, width=1.4)
        f.text(shift(cX, u((lo + hi) / 2), 0.38), lab[name], size=14,
               color=col)
        f.text(shift(cX, u(th0 + PI / 2), 0.3), name, size=15, color=col)
    f.text(shift(c, (0.2, 0.25)), 'C', size=15, color=FAINT)
    origin(f)
    save(f, '09-six/normalized', 'The angles e, n, w, d, s of a labelled '
         'configuration of six squares about a containing square')
    return Rn


def centre_region(R, turn=0.0, n=60):
    """The centres of the unit squares turned by `turn` that lie in the
    closed disk of radius R about the origin: (|x| + 1/2)^2 + (|y| + 1/2)^2
    <= R^2 in the frame of the squares, bounded by four circular arcs."""
    rho = math.sqrt(R * R - 0.25) - 0.5
    pts = []
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        # the arc of the circle about (-sx/2, -sy/2) in this quadrant
        a0 = math.atan2(0.5, rho + 0.5)
        arc = [(-0.5 + R * math.cos(a0 + (PI / 2 - 2 * a0) * k / n),
                -0.5 + R * math.sin(a0 + (PI / 2 - 2 * a0) * k / n))
               for k in range(n + 1)]
        if sx * sy < 0:
            arc = arc[::-1]
        pts += [rotate((sx * x, sy * y), turn) for x, y in arc]
    return pts, rho


def centres_figure():
    """Proposition 9.58: the work of the force on each square is largest
    exactly at the centre of the model, the point of the region of its
    possible centres where the force is an outward normal."""
    sq = model_squares()
    Z, rho = centre_region(R6)
    Zd, _ = centre_region(R6, PI / 4)
    assert abs(rho - RHO) < 1e-12
    m = R6 + 0.06
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R6, stroke=INK, width=1.0, dash='6 4')
    for name, (c, d) in sq.items():
        f.polygon(square_corners(c, d), fill='none', stroke=FAINT,
                  width=1.0)
    f.polygon(Zd, fill=FILLS[5], stroke=CYAN, width=1.0, opacity=0.5)
    f.polygon(Z, fill=FILLS[0], stroke=BLUE, width=1.3, opacity=0.6)
    forces = {'E': (1, R_STAR), 'N': (R_STAR, 1),
              'W': (-(1 + R_STAR), M_STAR), 'S': (M_STAR, -(1 + R_STAR)),
              'D': (-M_STAR, -M_STAR)}
    for k, F_ in forces.items():
        c = sq[k][0]
        nF = (F_[0] / norm(F_), F_[1] / norm(F_))
        if k != 'D':
            # The outward normal of the region at c is the direction of the
            # far corner, that is, of the force.
            sx, sy = math.copysign(1, c[0]), math.copysign(1, c[1])
            nrm = (c[0] + sx * 0.5, c[1] + sy * 0.5)
            assert abs(norm(nrm) - R6) < 1e-12
            assert abs(nrm[0] * F_[1] - nrm[1] * F_[0]) < 1e-12
        support_line(f, nF, dot2(c, nF), half=0.42, centre=c, stroke=INK,
                     width=1.1, dash='4 3')
        arrow(f, c, shift(c, nF, 0.38), color=STYLE[k][1], width=2.2,
              size=9)
        f.dot(c, r=3.6, fill=STYLE[k][1])
    for k, (r_, a_) in {'E': (0.22, 180), 'N': (0.22, -90), 'W': (0.22, 0),
                        'S': (0.22, 90), 'D': (0.24, 45)}.items():
        f.text(shift(sq[k][0], u(math.radians(a_)), r_), k, size=16,
               color=STYLE[k][1])
    f.dot((0, 0), r=2.8)
    f.text((0.05, -0.1), 'o', size=14, anchor='start')
    save(f, '09-six/centres', 'The region of the possible centres of a unit '
         'square in the disk of radius R6, and the centres of the model on '
         'its boundary, where the forces of the stress are outward normals')


# --------------------------------------------------------------- the wings

def sep_value(Ua, Va, n):
    """<n, c_V - c_U> for squares given as (centre, deg)."""
    return dot2(n, (Va[0][0] - Ua[0][0], Va[0][1] - Ua[0][1]))


def south_wing_missing():
    """A missing south wing at d = 0.6, s = 0.4, w = -0.45: D and S tight
    along the secondary axis e2 of D, W and D tight along that of W."""
    d, s_, w = 0.6, 0.4, -0.45
    D_ = oriented(PI + d, 1.06, -0.1)
    e2D, e2W = u(1.5 * PI + d), u(1.5 * PI + w)
    cS = shift(shift(D_[0], e2D, tau(d - s_)), u(d), 0.6)
    cW = shift(shift(D_[0], e2W, -tau(d - w)), u(w), -0.4)
    return {'W': (cW, deg(PI + w)), 'D': D_, 'S': (cS, deg(1.5 * PI + s_))}


def wings_figure():
    w, d, s = -0.47, 0.57, 0.19
    panels = [
        # The model corner: (phase, a, b) of W, D and S.
        {k: oriented(*v) for k, v in
         {'W': (PI, 1 - S, -T), 'D': (1.25 * PI, RHO, 0.0),
          'S': (1.5 * PI, 1 - S, T)}.items()},
        # A missing west wing.
        {k: oriented(*v) for k, v in
         {'W': (PI + w, 1.1, -0.08), 'D': (PI + d, 1.06, 0.26),
          'S': (1.5 * PI + s, 0.96, 0.42)}.items()},
        # A missing south wing.
        south_wing_missing()]
    expect = [('W', 'S'), ('D', 'S'), ('W', 'D')]
    # Shift each panel so that its squares sit side by side.
    xs = [[q[0] for k in pan for q in corners(pan[k])] for pan in panels]
    ys = [q[1] for pan in panels for k in pan for q in corners(pan[k])]
    gap, x0, shifts = 0.25, 0.0, []
    for k, pan in enumerate(panels):
        shifts.append((x0 - min(xs[k]), 0.0))
        x0 += max(xs[k]) - min(xs[k]) + gap
    f = Figure(-0.05, x0 - gap + 0.05, min(ys) - 0.35, max(ys) + 0.05, 102)
    for k, sq in enumerate(panels):
        sh = shifts[k]
        names = list(sq)
        for i_, p_ in enumerate(names):
            for q_ in names[i_ + 1:]:
                assert not interiors_meet(corners(sq[p_]), corners(sq[q_]))
        for name, sqr in sq.items():
            fill, stroke = STYLE[name]
            f.polygon([shift(sh, q) for q in corners(sqr)], fill=fill,
                      stroke=stroke)
            f.text(shift(sh, sqr[0]), name, size=15, color=stroke)
        e2 = {name: u(math.radians(sq[name][1]) + PI / 2) for name in sq}

        def margin(U, V, n):
            turn = math.radians(sq[V][1] - sq[U][1])
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
        cx = (min(xs[k]) + max(xs[k])) / 2 + sh[0]
        word(f, (cx, min(ys) - 0.22), ('the model', 'a missing west wing',
                                        'a missing south wing')[k], size=13)
    save(f, '09-six/wings', 'The wings of the model, a missing west wing and a '
         'missing south wing')


# ---------------------------------------------------------------- the tails

def tails_figure():
    """W on its own axis at w = -11/25 and S on its own axis at s = 1/20,
    with c = (c0, 0) and d = 0.6, all four separations of the tail stress
    tight; the centre of D is fixed by the two wings."""
    c = (C0, 0.0)
    w, d, s_ = -11 / 25, 0.6, 0.05
    e1W, e2W = u(PI + w), u(1.5 * PI + w)
    e1S, e2S = u(1.5 * PI + s_), u(s_)
    cW = shift(shift((0, 0), e1W, dot2(c, e1W) + tau(w)), e2W, -0.2)
    cS = shift(shift((0, 0), e1S, dot2(c, e1S) + tau(s_)), e2S, 0.24)
    v1 = dot2(e2W, cW) + tau(d - w)
    v2 = dot2(e2S, cS) - tau(PI / 2 + s_ - d)
    det = e2W[0] * e2S[1] - e2W[1] * e2S[0]
    cD = ((v1 * e2S[1] - e2W[1] * v2) / det,
          (e2W[0] * v2 - v1 * e2S[0]) / det)
    W_, D_, S_ = (cW, deg(PI + w)), (cD, deg(PI + d)), (cS, deg(1.5 * PI + s_))
    sqs = {'C': (c, 0.0), 'W': W_, 'D': D_, 'S': S_}
    names = list(sqs)
    for i, p_ in enumerate(names):
        for q_ in names[i + 1:]:
            assert not interiors_meet(corners(sqs[p_]), corners(sqs[q_]))
    aW, bW = dot2(cW, e1W), dot2(cW, e2W)
    aS, bS = dot2(cS, e1S), dot2(cS, e2S)
    assert abs(margins(PI + w, aW, bW, c)['own']) < 1e-12
    assert abs(margins(1.5 * PI + s_, aS, bS, c)['own']) < 1e-12
    assert abs(sep_value(W_, D_, e2W) - tau(d - w)) < 1e-12
    assert abs(sep_value(D_, S_, e2S) - tau(PI / 2 + s_ - d)) < 1e-12
    Rn = max(norm(q) for p_ in names for q in corners(sqs[p_]))
    assert Rn > R0
    m = Rn + 0.08
    f = Figure(-m, m, -m - 0.25, m, 135)
    f.circle((0, 0), Rn, stroke=INK, width=1.0, dash='6 4')
    f.circle((0, 0), R0, stroke=RED, width=1.0, dash='2 3')
    draw_squares(f, sqs, labels=False)
    # The four separating lines, each drawn a little beyond the edge it
    # runs along.

    def sep_line(n, val, sq, col):
        along = (-n[1], n[0])
        on = [q for q in corners(sq) if abs(dot2(q, n) - val) < 1e-9]
        ts = sorted(dot2(q, along) for q in on)
        base = shift((0, 0), n, val)
        f.line(shift(base, along, ts[0] - 0.25), shift(base, along,
               ts[-1] + 0.25), stroke=col, dash='5 4', width=1.3)
    sep_line(e1W, aW - 0.5, W_, PURPLE)
    sep_line(e1S, aS - 0.5, S_, PINK)
    sep_line(e2W, bW + 0.5, W_, INK)
    sep_line(e2S, bS - 0.5, S_, INK)
    # The forces of the tail stress: 8/15 on C-W, 1/5 on C-S, 1/6 on W-D
    # and 1/10 on D-S.
    l1, l2, l3, l4 = 8 / 15, 1 / 5, 1 / 6, 1 / 10
    FW = shift(shift((0, 0), e1W, l1), e2W, -l3)
    FD = shift(shift((0, 0), e2W, l3), e2S, -l4)
    FS = shift(shift((0, 0), e1S, l2), e2S, l4)
    FC = shift(shift((0, 0), e1W, -l1), e1S, -l2)
    assert norm(shift(shift(FW, FD), shift(FS, FC))) < 1e-12
    for k, F in (('C', FC), ('W', FW), ('D', FD), ('S', FS)):
        arrow(f, sqs[k][0], shift(sqs[k][0], F, 0.9),
              color=INK if k == 'C' else STYLE[k][1], width=2.2, size=9)
    for k, ang in (('C', 60), ('W', 240), ('D', 120), ('S', 30)):
        f.text(shift(sqs[k][0], u(math.radians(ang)), 0.27), k, size=16,
               color=STYLE[k][1])
    f.dot((0, 0), r=2.8)
    f.text((-0.05, -0.1), 'o', size=14, anchor='end')
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


def pair_figure():
    """Definition 9.48 at n = 0.15 with N on its own axis, w = -0.2 with W
    on its matching side and the facet -e1 of W, the three separations
    tight: the edge normals with their weights and the forces F_N, F_W."""
    c = (0.06, 0.04)
    n, w = 0.15, -0.2
    e1N, e2N = u(PI / 2 + n), u(PI + n)
    e1W, e2W = u(PI + w), u(1.5 * PI + w)
    fv = u(w)
    aN = dot2(c, e1N) + tau(n)
    bW = -0.35
    aW = (bW * math.sin(w) - c[0] + tau(w)) / math.cos(w)
    cW = shift(shift((0, 0), e1W, aW), e2W, bW)
    q = n - w
    bN = (-aN * math.sin(q) - dot2(fv, cW) - tau(q)) / math.cos(q)
    cN = shift(shift((0, 0), e1N, aN), e2N, bN)
    sq = {'C': (c, 0.0), 'N': (cN, deg(PI / 2 + n)), 'W': (cW, deg(PI + w))}
    for p_, q_ in (('C', 'N'), ('C', 'W'), ('N', 'W')):
        assert not interiors_meet(corners(sq[p_]), corners(sq[q_]))
    assert abs(margins(PI / 2 + n, aN, bN, c)['own']) < 1e-12
    assert abs(margins(PI + w, aW, bW, c)['west']) < 1e-12
    assert abs(sep_value(sq['W'], sq['N'], fv) - tau(q)) < 1e-12
    # The forces, from the normals of Definition 9.48.
    FN = shift(e1N, fv, R_STAR)
    FW = shift(shift((-1.0, 0.0), fv, -R_STAR), e2W, -M_STAR)
    kN = (dot2(e1N, e1N), dot2(e1N, e2N))
    assert abs(kN[0] - 1) < 1e-12 and abs(kN[1]) < 1e-12
    for F_, frame, want in ((FN, (e1N, e2N), shift((1.0, 0.0),
                             (-math.sin(q), -math.cos(q)), R_STAR)),
                            (FW, (e1W, e2W), shift((math.cos(w),
                             -math.sin(w)), (R_STAR, -M_STAR)))):
        got = (dot2(F_, frame[0]), dot2(F_, frame[1]))
        assert abs(got[0] - want[0]) < 1e-12 and abs(got[1] - want[1]) < 1e-12
    f = Figure(-1.75, 1.2, -0.85, 1.95, 150)
    draw_squares(f, sq, labels=False)

    def contact(n_, val, A, B, col, lab, at_edge=False):
        """The line <x, n_> = val, along which A and B are separated, and
        its normal, drawn at the touching vertex or at the middle of the
        edge on the line."""
        on = {k: [x for x in corners(sq_) if abs(dot2(x, n_) - val) < 1e-9]
              for k, sq_ in (('A', A), ('B', B))}
        along = (-n_[1], n_[0])
        ts = sorted(dot2(x, along) for x in on['A'] + on['B'])
        base = shift((0, 0), n_, val)
        f.line(shift(base, along, ts[0] - 0.3), shift(base, along,
               ts[-1] + 0.3), stroke=col, width=1.2, dash='5 4')
        # The contact: the single vertex of one square on the line, or
        # the middle of the edge of the other.
        assert len(on['A']) + len(on['B']) == 3
        edge = on['A'] if len(on['A']) == 2 else on['B']
        at = on['A'][0] if len(on['A']) == 1 else on['B'][0]
        if at_edge:
            at = shift(edge[0], (edge[1][0] - edge[0][0],
                                 edge[1][1] - edge[0][1]), 0.5)
        arrow(f, at, shift(at, n_, 0.32), color=col, width=1.5, size=8)
        f.text(shift(shift(at, n_, 0.2), along, -0.13), lab, size=14,
               italic=False, color=col)
    contact(e1N, aN - 0.5, sq['C'], sq['N'], ORANGE, '1', at_edge=True)
    contact((-1.0, 0.0), 0.5 - c[0], sq['C'], sq['W'], PURPLE, '1',
            at_edge=True)
    contact(fv, dot2(cW, fv) + 0.5, sq['W'], sq['N'], INK,
            star('r', size=14, italic=True))
    for k, F_ in (('N', FN), ('W', FW)):
        col = STYLE[k][1]
        arrow(f, sq[k][0], shift(sq[k][0], F_, 0.45), color=col, width=2.4,
              size=10)
        f.text(shift(sq[k][0], F_, 0.62), sb('F', k, size=15), size=15,
               color=col)
    f.text(shift(cW, e2W, 0.3), 'W', size=16, color=PURPLE)
    f.text(shift(cN, e2N, -0.27), 'N', size=16, color=ORANGE)
    f.text(shift(c, (0.25, -0.25)), 'C', size=16, color=FAINT)
    f.dot((0, 0), r=2.8)
    f.text((0.05, 0.08), 'o', size=14, anchor='start')
    save(f, '09-six/pair', 'The edges of the stress of the model that touch '
         'N and W, at angles n and w other than those of the model, and the '
         'forces on N and W')


def diagonal_figure():
    """Lemma 9.52 at w = -0.3, s = -0.1, d = 0.75, both wings tight: the
    wings, and the wing forces on D with their sum
    F_D = L(cos delta, -sin delta) in the frame of D."""
    w, s_, d = -0.3, -0.1, 0.75
    D_ = oriented(PI + d, 1.15, 0.0)
    cD = D_[0]
    e1D, e2D = u(PI + d), u(1.5 * PI + d)
    e2W, e2S = u(1.5 * PI + w), u(s_)
    bW = dot2(cD, e2W) - tau(d - w)
    bS = dot2(cD, e2S) + tau(d - s_)
    W_, S_ = oriented(PI + w, 1.1, bW), oriented(1.5 * PI + s_, 1.0, bS)
    c = (0.06, 0.05)
    sq = {'C': (c, 0.0), 'W': W_, 'D': D_, 'S': S_}
    names = list(sq)
    for i, p_ in enumerate(names):
        for q_ in names[i + 1:]:
            assert not interiors_meet(corners(sq[p_]), corners(sq[q_]))
    assert abs(sep_value(W_, D_, e2W) - tau(d - w)) < 1e-12
    assert abs(sep_value(D_, S_, e2S) - tau(d - s_)) < 1e-12
    beta = (w - s_) / 2
    delta = d - PI / 4 - (w + s_) / 2
    L = KD * (math.cos(beta) - math.sin(beta))
    vW = shift((0, 0), e2W, M_STAR)
    vS = shift((0, 0), e2S, -M_STAR)
    FD = shift(vW, vS)
    assert abs(dot2(FD, e1D) - L * math.cos(delta)) < 1e-12
    assert abs(dot2(FD, e2D) + L * math.sin(delta)) < 1e-12
    xs = [q[0] for k in ('W', 'D', 'S') for q in corners(sq[k])]
    ys = [q[1] for k in ('W', 'D', 'S') for q in corners(sq[k])]
    x0, y0, y1 = min(xs) - 0.1, min(ys) - 0.1, max(ys) + 0.1
    f = Figure(x0, 3.25, y0, y1, 118)
    # Left: the squares and the two wings, tight.
    f.polygon(square_corners(c), fill=GREY, stroke=FAINT, opacity=0.6)
    f.text(shift(c, (0.25, 0.27)), 'C', size=15, color=FAINT)
    draw_squares(f, {k: v for k, v in sq.items() if k != 'C'},
                 labels=False)
    for n_, val, sqr in ((e2W, bW + 0.5, W_), (e2S, bS - 0.5, S_)):
        along = (-n_[1], n_[0])
        on = [q for q in corners(sqr) if abs(dot2(q, n_) - val) < 1e-9]
        ts = sorted(dot2(q, along) for q in on)
        base = shift((0, 0), n_, val)
        f.line(shift(base, along, ts[0] - 0.2), shift(base, along,
               ts[-1] + 0.2), stroke=INK, width=1.2, dash='5 4')
    polyline(f, [cD, shift(cD, e1D, 0.45)], stroke=CYAN, width=1.2,
             dash='2 3')
    f.text(shift(shift(cD, e1D, 0.45), e2D, -0.17), subsup('e', '1', 'D',
           size=15), size=15, color=CYAN)
    for k, ang in (('W', 90), ('S', 0), ('D', 90)):
        f.text(shift(sq[k][0], u(math.radians(ang)), 0.25), k, size=16,
               color=STYLE[k][1])
    f.dot((0, 0), r=2.8)
    f.text((0.05, 0.08), 'o', size=14, anchor='start')
    # Right: the forces on D in its frame, e1 to the right.
    def frame(v):
        return (dot2(v, e1D), dot2(v, e2D))
    O = (1.25, (y0 + y1) / 2 - 0.1)
    k = 0.85
    polyline(f, [O, shift(O, (1.75, 0))], stroke=CYAN, width=1.1,
             dash='2 3')
    f.text(shift(O, (1.85, 0)), subsup('e', '1', 'D', size=15), size=15,
           color=CYAN, anchor='start')
    polyline(f, [shift(O, (0, -0.5)), shift(O, (0, 0.95))], stroke=FAINT,
             width=1.0, dash='2 3')
    f.text(shift(O, (0, 1.08)), subsup('e', '2', 'D', size=15), size=15,
           color=FAINT)
    pW, pS, pF = (shift(O, frame(v), k) for v in (vW, vS, FD))
    for p_ in (pW, pS):
        polyline(f, [p_, pF], stroke=FAINT, width=0.9, dash='3 3')
    arrow(f, O, pW, color=PURPLE, width=1.6, size=9)
    arrow(f, O, pS, color=PINK, width=1.6, size=9)
    arrow(f, O, pF, color=CYAN, width=2.6, size=10)
    f.text(shift(pW, (0.0, 0.14)), star('m', ' ', size=14, italic=True)
           + subsup(it('e'), '2', it('W'), size=14), size=14, italic=False,
           color=PURPLE)
    f.text(shift(pS, (0.05, -0.16)), '−' + star('m', ' ', size=14,
           italic=True) + subsup(it('e'), '2', it('S'), size=14), size=14,
           italic=False, color=PINK)
    f.text(shift(pF, (0.1, 0.0)), sb('F', 'D', size=15), size=15,
           color=CYAN, anchor='start')
    thin_arc(f, O, 0.7, 0.0, -delta, color=INK, width=1.2)
    f.text(shift(O, u(-delta / 2), 0.85), it('δ'), size=15, italic=False)
    f.dot(O, r=2.8, fill=CYAN)
    save(f, '09-six/diagonal', 'The two wings at the turned square D, and '
         'the wing forces on D and their sum in the frame of D')


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


def level_segments(xs, ys, val, level):
    """The segments of the level line val = level on a grid of values
    val[i][j] at (xs[i], ys[j]), by marching squares."""
    segs = []
    for i in range(len(xs) - 1):
        for j in range(len(ys) - 1):
            cs = [(xs[i], ys[j], val[i][j]), (xs[i + 1], ys[j], val[i + 1][j]),
                  (xs[i + 1], ys[j + 1], val[i + 1][j + 1]),
                  (xs[i], ys[j + 1], val[i][j + 1])]
            pts = []
            for k in range(4):
                (xa, ya, va), (xb, yb, vb) = cs[k], cs[(k + 1) % 4]
                if (va - level) * (vb - level) < 0:
                    t = (level - va) / (vb - va)
                    pts.append((xa + t * (xb - xa), ya + t * (yb - ya)))
            if len(pts) == 2:
                segs.append(tuple(pts))
            elif len(pts) == 4:
                segs += [(pts[0], pts[1]), (pts[2], pts[3])]
    return segs


def pair_least(w, own):
    """The least value of Pi(n, w) - |n|/1000 - beta* over the n of the
    domain of the pair, the four facets and both choices for N, with W on
    its own axis or on its matching side."""
    best = 1e9
    for no in (True, False):
        lo, hi = (-3 / 10, 5 / 12) if no else (-1 / 4, 1 / 4)
        for k in range(49):
            n = lo + (hi - lo) * k / 48
            for facet in ('W1', 'W2', 'N1', 'N2'):
                v = pair_value(n, w, facet, no, own) - abs(n) / 1000 - BETA
                best = min(best, v)
    return best


def pair_bound_figure():
    """Proposition 9.50 along w: the least value of Pi(n, w) - |n|/1000 -
    beta* over n, the facets and both choices for N, above the line l."""
    assert abs(pair_value(0, 0) - BETA) < 1e-12
    f = Figure(-0.3, 3.0, 0.0, 2.75, 110)
    xl, yl = (-0.54, 0.43), (-0.13, 0.45)
    P = Plot(f, 0.25, 0.1, 2.5, 2.5, xl, yl)
    P.axes('', '', yticks=[(0.2, '0.2'), (0.4, '0.4')], x_at=xl[0],
           y_at=0.0)
    for x, lab in ((-11 / 25, '−11/25'), (0.0, '0'), (2 / 5, '⅖')):
        q = P.P(x, 0.0)
        f.line(shift(q, (0, -0.04)), shift(q, (0, 0.04)), width=1)
        word(f, shift(q, (0, -0.16)), lab, size=12)
    f.text(shift(P.P(xl[1], 0.0), (0.06, 0.0)), 'w', size=15,
           anchor='start')
    runs = {True: (-11 / 25, 0.0, ORANGE), False: (-2 / 5, 2 / 5, BLUE)}
    for own, (lo, hi, col) in runs.items():
        pts = []
        for k in range(41):
            w = lo + (hi - lo) * k / 40
            g = pair_least(w, own)
            assert g >= line_l(w) - 1e-9
            pts.append(P.P(w, g))
        polyline(f, pts, stroke=col, width=1.8)
    P.curve(line_l, -11 / 25, 2 / 5, stroke=INK, width=1.3, dash='5 3')
    f.dot(P.P(0, 0), r=3.6, fill=RED)
    f.text(P.P(-0.47, 0.17), 'own axis', size=13, italic=False,
           color=ORANGE, anchor='start')
    f.text(P.P(-0.36, 0.43), 'matching side', size=13, italic=False,
           color=BLUE, anchor='start')
    f.text(P.P(0.27, -0.112), 'ℓ(' + it('w') + ')', size=14, italic=False,
           anchor='end')
    save(f, '09-six/pair-bound', 'The least value of the pair estimate '
         'along w, above the line l(w), for W on its own axis and on its '
         'matching side')


def remainder_figure():
    """Proposition 9.53: level lines of the remainder of the diagonal,
    least over 1/2 <= d <= pi/4, on the domain of the diagonal."""
    assert abs(remainder(0, 0, PI / 4)) < 1e-12
    w0, w1, s0, s1 = -11 / 25, 2 / 5, -2 / 5, 11 / 25
    nx = 64
    xs = [w0 + (w1 - w0) * i / nx for i in range(nx + 1)]
    ys = [s0 + (s1 - s0) * j / nx for j in range(nx + 1)]
    dd = [0.5 + (PI / 4 - 0.5) * k / 15 for k in range(16)]
    val = [[min(remainder(w, s_, d) for d in dd) for s_ in ys] for w in xs]
    assert min(min(r) for r in val) > -1e-9
    f = Figure(-0.62, 2.62, -0.42, 2.78, 110)
    Q_ = Plot(f, 0.0, 0.1, 2.5, 2.5, (w0, w1), (s0, s1))
    for lv in (0.02, 0.05, 0.1, 0.15):
        segs = level_segments(xs, ys, val, lv)
        for line in chains(segs):
            polyline(f, [Q_.P(*q) for q in line], stroke=GREEN, width=1.1)
        left = [q for sg in segs for q in sg if q[0] < w0 + 1e-9]
        if left:
            q = min(left, key=lambda q: q[1])
            f.text(shift(Q_.P(*q), (0.05, 0.09)), f'{lv:g}', size=11,
                   italic=False, color=GREEN, anchor='start')
    polyline(f, [Q_.P(w0, s0), Q_.P(w1, s0), Q_.P(w1, s1), Q_.P(w0, s1),
                 Q_.P(w0, s0)], stroke=INK, width=1.0)
    f.dot(Q_.P(0, 0), r=3.6, fill=RED)
    for x, lab in ((w0, '−11/25'), (0.0, '0'), (w1, '⅖')):
        word(f, shift(Q_.P(x, s0), (0, -0.15)), lab, size=12)
    for y, lab in ((s0, '−⅖'), (0.0, '0'), (s1, '11/25')):
        word(f, shift(Q_.P(w0, y), (-0.08, 0)), lab, size=12, anchor='end')
    f.text(shift(Q_.P(0.0, s0), (0, -0.37)), 'w', size=15)
    f.text(shift(Q_.P(w0, s1), (0.0, 0.16)), 's', size=15)
    save(f, '09-six/remainder', 'Level lines of the remainder of the '
         'diagonal, least over d, which vanishes only at the model')


def main():
    model_figure()
    corners_figure()
    construction()
    constants_figure()
    total = arcs_figure()
    best = arc_region()
    frame_figure()
    octagon_figure()
    separators_figure()
    free_arc_figure()
    core_figure()
    caps_figure()
    pins_figure()
    pins_figure('09-six/chords', chords=True)
    sixty_figure()
    windows_figure()
    one_edge_figure()
    supports_figure()
    stress_figure()
    stress_figure('09-six/contacts', contacts_mode=True)
    stress_radius_figure()
    annulus_figure()
    pin_order_figure()
    west_stress_figure()
    normalized_figure()
    wings_figure()
    tails_figure()
    pair_figure()
    pair_bound_figure()
    diagonal_figure()
    remainder_figure()
    centres_figure()
    return total, best


if __name__ == '__main__':
    main()

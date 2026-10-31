#!/usr/bin/env python3
"""Draw the figures of Chapter 11 (eight squares) as SVG files in
docs/proof/figures/11-eight/.

    python3 scripts/figures/fig_eight.py

Every figure is computed from the definitions of the chapter: the five-corner
chain and its stationary zero (from fig_front), the model of the five-parameter
family, the canonical frames and states of the exterior squares, and, for the
figures of the tables, rows copied from the affine-arc table that excludes
tau_G at most -4/5. Each drawing asserts the facts its caption states.
"""
import itertools
import math

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, u, shift, rad, sb, clip)
from fig_front import (it, sbn, RED, RED_FILL, NB, Q8, U8, T8, R8,
                       polyline, arrow, word)

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN, YELLOW = COLORS
Q0 = 9789 / 2500
Q1 = 1957767069 / 500000000
QMINUS = 7831 / 2000
CORE = 1 / 12
SQ2 = math.sqrt(2)

# Colours of the roles: the seven exterior squares and the central square K.
ROLE_COLOR = {'A': BLUE, 'B': ORANGE, 'D': GREEN, 'E': PURPLE, 'H': PINK,
              'T': CYAN, 'G': YELLOW}
ROLE_FILL = {k: FILLS[COLORS.index(v)] for k, v in ROLE_COLOR.items()}
EXTERIOR = 'ABTDEHG'
CYCLE = 'HGABTDE'          # the cyclic order of the candidate roles
MEASURE = [None]           # the least 3 L_1 + L_5/4 in Figure 11.6


# ------------------------------------------------------------ small vectors

def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(k, p):
    return (k * p[0], k * p[1])


def norm(p):
    return math.hypot(p[0], p[1])


def rot(p, t):
    return (p[0] * math.cos(t) - p[1] * math.sin(t),
            p[0] * math.sin(t) + p[1] * math.cos(t))


def wrap(t):
    """The representative of an angle in (-pi, pi]."""
    t = math.fmod(t, 2 * PI)
    if t <= -PI:
        t += 2 * PI
    if t > PI:
        t -= 2 * PI
    return t


# ------------------------------------------------------- the chain and model

def chain(q, y, t):
    """The five-corner chain of Definition 11.2."""
    x1 = math.sqrt(q - y * y)
    x2 = math.sqrt(q - (y + 2) ** 2)
    x3 = x2 - 3
    y3 = math.sqrt(q - x3 * x3)
    y4 = y3 - 2
    x4 = -math.sqrt(q - y4 * y4)
    c, s = math.cos(t), math.sin(t)
    h1 = c * x1 + s * y - 2 - c
    h2 = -s * x4 + c * y4 - 1 - s
    P5 = (c * h1 - s * h2, s * h1 + c * h2)
    return dict(q=q, y=y, t=t, c=c, s=s, x1=x1, x2=x2, x3=x3, y3=y3, y4=y4,
                x4=x4, h1=h1, h2=h2, F=h1 * h1 + h2 * h2 - q,
                P=[(x1, y), (x2, y + 2), (x3, y3), (x4, y4), P5])


def chain_derivatives(ch):
    """F_y and F_t of Theorem 11.1 (Lemma J.1)."""
    y, c, s = ch['y'], ch['c'], ch['s']
    x1, x2, x3, y3, y4, x4 = (ch[k] for k in ('x1', 'x2', 'x3', 'y3', 'y4',
                                               'x4'))
    h1, h2 = ch['h1'], ch['h2']
    y4d = x3 * (y + 2) / (y3 * x2)
    h1y = s - c * y / x1
    h2y = (c + s * y4 / x4) * y4d
    h1t = c * y - s * (x1 - 1)
    h2t = -c * (x4 + 1) - s * y4
    return 2 * (h1 * h1y + h2 * h2y), 2 * (h1 * h1t + h2 * h2t)


ROOT = chain(Q8, -U8, T8)
assert abs(ROOT['F']) < 1e-9
assert all(abs(d) < 1e-6 for d in chain_derivatives(ROOT))
C0, S0, TSTAR = ROOT['c'], ROOT['s'], ROOT['t']
X1, X2, X3, Y3, Y4, X4 = (ROOT[k] for k in ('x1', 'x2', 'x3', 'y3', 'y4',
                                              'x4'))
H1, H2, YSTAR = ROOT['h1'], ROOT['h2'], ROOT['y']
E_T, F_T = (C0, S0), (-S0, C0)
ZETA_PLUS = math.sqrt(Q8 - (X2 - 1) ** 2) - 0.5
ETA_MINUS = -H2 - math.sqrt(Q8 - (H1 + 2) ** 2)
ETA_PLUS = -H2 - 13 / 12
BOX = (0.14, 0.0, 0.1, 1.35, -0.32)
# Proposition 11.4 (3): the brackets of the stationary solution.
assert -0.92071 < YSTAR < -0.92059 and 0.99231 <= C0 <= 0.99242
assert 0.12327 <= S0 <= 0.12338 and 1.75152 <= X1 <= 1.75159
assert 1.65843 <= X2 <= 1.65852 and 1.45455 <= Y3 <= 1.45464
assert -1.90214 <= X4 <= -1.90211 and -1.36797 <= H1 <= -1.36748
assert -1.43022 <= H2 <= -1.42976
assert QMINUS < Q8 < Q1 < Q0 < 4


def in_frame(a, b, c=C0, s=S0):
    return (c * a - s * b, s * a + c * b)


def model(x=BOX[0], y=BOX[1], w=BOX[2], zeta=BOX[3], eta=BOX[4]):
    """The squares of the model M(x, y, w, zeta, eta) of Theorem 11.1, as
    (centre, angle in degrees)."""
    tdeg = math.degrees(TSTAR)
    return {'A': ((X1 - 0.5, YSTAR + 0.5), 0.0),
            'B': ((X2 - 0.5, YSTAR + 1.5), 0.0),
            'D': ((X3 + 0.5, Y3 - 0.5), 0.0),
            'E': ((X4 + 0.5, Y4 + 0.5), 0.0),
            'T': ((X2 - 1.5, zeta), 0.0),
            'H': (in_frame(H1 + 0.5, H2 + 0.5), tdeg),
            'G': (in_frame(H1 + 1.5, H2 + 0.5 + eta), tdeg),
            'K': ((x, y), math.degrees(2 * math.atan(w)))}


def frame(sq):
    t = rad(sq[1])
    return (math.cos(t), math.sin(t)), (-math.sin(t), math.cos(t))


def corners(sq):
    return square_corners(sq[0], sq[1])


def half_width(sq, n):
    e, f = frame(sq)
    return 0.5 * (abs(dot(n, e)) + abs(dot(n, f)))


def axis_margin(p, q, n):
    """Projection of c_q - c_p on the unit vector n minus the two half
    widths: nonnegative exactly when n separates p from q (Lemma 9.11)."""
    return dot(n, sub(q[0], p[0])) - half_width(p, n) - half_width(q, n)


def sep_margin(p, q):
    """The largest margin over the eight signed axes of the pair; the open
    squares are disjoint exactly when it is nonnegative."""
    best = -1e9
    for sq in (p, q):
        for n in frame(sq):
            best = max(best, axis_margin(p, q, n), axis_margin(p, q, mul(-1, n)))
    return best


def farthest_sq(sq):
    return max(dot(v, v) for v in corners(sq))


def core_distance(sq):
    """The distance from o to the closed square."""
    e, f = frame(sq)
    a, b = abs(dot(sq[0], e)), abs(dot(sq[0], f))
    return math.hypot(max(a - 0.5, 0.0), max(b - 0.5, 0.0))


def admissible(x, y, w, zeta, eta, tol=1e-12):
    """The admissibility conditions of Theorem 11.1, with their margins."""
    M = model(x, y, w, zeta, eta)
    C, S = (1 - w * w) / (1 + w * w), 2 * w / (1 + w * w)
    ranges = (1 - SQ2 <= w < SQ2 - 1 and 7 / 12 - tol <= zeta <= ZETA_PLUS + tol
              and ETA_MINUS - tol <= eta <= ETA_PLUS + tol)
    core = 5 / 12 - max(abs(C * x + S * y), abs(-S * x + C * y))
    seps = {k: sep_margin(M['K'], M[k]) for k in EXTERIOR}
    return ranges and core > 0 and min(seps.values()) >= -tol, core, seps


def check_packing(M, q=Q8, tol=1e-9):
    """The squares lie in the closed disk of squared radius q and are
    pairwise disjoint."""
    names = list(M)
    for k in names:
        assert farthest_sq(M[k]) <= q + tol, k
    for a, b in itertools.combinations(names, 2):
        assert sep_margin(M[a], M[b]) >= -tol, (a, b)


def canonical(sq):
    """The canonical frame of an exterior square (Definition 11.14): the
    state (a, b), the sign, the angle alpha from the centre direction to the
    canonical axis, and the direction of that axis."""
    c, deg = sq
    beta = math.atan2(c[1], c[0])
    th = rad(deg)
    m = round((beta - th) / (PI / 2))
    axis = th + m * PI / 2
    e, f = u(axis), u(axis + PI / 2)
    a, fb = dot(c, e), dot(c, f)
    sigma = -1 if fb > 0 else 1
    alpha = wrap(axis - beta)
    assert abs(alpha) <= PI / 4 + 1e-12 and a > 0
    return dict(a=a, b=abs(fb), sigma=sigma, alpha=alpha, axis=axis,
                beta=beta, tau=sigma * abs(fb) / a)


# ------------------------------------------------------------- drawing aids

def draw_square(f, sq, fill='none', stroke=INK, width=1.4, dash=None,
                opacity=1.0, at=(0.0, 0.0), scale=1.0):
    pts = [shift(at, mul(scale, p)) for p in corners(sq)]
    f.polygon(pts, fill=fill, stroke=stroke, width=width, dash=dash,
              opacity=opacity)


def draw_model(f, M, at=(0.0, 0.0), scale=1.0, labels=True, size=15,
               skip=(), dashed=(), faint=()):
    for k, sq in M.items():
        if k in skip:
            continue
        if k == 'K':
            fill, stroke = GREY, FAINT
        else:
            fill, stroke = ROLE_FILL[k], ROLE_COLOR[k]
        if k in faint:
            fill = 'none'
        draw_square(f, sq, fill=fill, stroke=stroke,
                    dash='5 3' if k in dashed else None, at=at, scale=scale)
        if labels:
            f.text(shift(at, mul(scale, sq[0])), k, size=size,
                   color=INK if k == 'K' else stroke)


def halo_text(f, pos, s, size=14, color=INK, italic=False, anchor='middle'):
    """Text with a white halo, readable over lines: the halo is a separate
    white copy drawn first, so that no part of the halo covers the glyphs
    of a text with several pieces."""
    x, y = f.p(*pos)
    style = ' font-style="italic"' if italic else ''
    common = (f'x="{x:.1f}" y="{y:.1f}" font-size="{size}" '
              f'font-family="Georgia, \'Times New Roman\', serif" '
              f'text-anchor="{anchor}" dominant-baseline="middle"{style}')
    f.add(f'<text {common} fill="#ffffff" stroke="#ffffff" stroke-width="4" '
          f'stroke-linejoin="round">{s}</text>')
    f.add(f'<text {common} fill="{color}">{s}</text>')


def sans_text(f, pos, s, size=14, color=INK, anchor='middle'):
    """Upright sans-serif text, for the four types C, L, M, H."""
    x, y = f.p(*pos)
    f.add(f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" '
          f'font-family="Helvetica, Arial, sans-serif" fill="{color}" '
          f'text-anchor="{anchor}" dominant-baseline="middle">{s}</text>')


def core_disk(f, at=(0.0, 0.0), scale=1.0, r=CORE):
    f.circle(at, r * scale, stroke=RED, width=1.0, fill=RED_FILL)


def origin(f, at=(0.0, 0.0), dx=0.06, dy=-0.08, r=2.6):
    f.dot(at, r=r)
    f.text(shift(at, (dx, dy)), 'o', size=14, anchor='start')


def segment_overlap(a0, a1, b0, b1):
    return max(a0, b0), min(a1, b1)


def contact_features(M):
    """The seven contacts of the model: thick shared side segments for the
    five pairs that share a side, contact points for the two pairs where a
    corner touches a side (Lemma 11.3)."""
    A, B, D, E, T, H, G = (M[k] for k in 'ABDETHG')
    segs = []
    lo, hi = segment_overlap(A[0][0] - 0.5, A[0][0] + 0.5, B[0][0] - 0.5,
                             B[0][0] + 0.5)
    segs.append(((lo, YSTAR + 1), (hi, YSTAR + 1)))
    lo, hi = segment_overlap(B[0][1] - 0.5, B[0][1] + 0.5, T[0][1] - 0.5,
                             T[0][1] + 0.5)
    segs.append(((X2 - 1, lo), (X2 - 1, hi)))
    lo, hi = segment_overlap(D[0][1] - 0.5, D[0][1] + 0.5, T[0][1] - 0.5,
                             T[0][1] + 0.5)
    segs.append(((X2 - 2, lo), (X2 - 2, hi)))
    lo, hi = segment_overlap(D[0][0] - 0.5, D[0][0] + 0.5, E[0][0] - 0.5,
                             E[0][0] + 0.5)
    segs.append(((lo, Y3 - 1), (hi, Y3 - 1)))
    # H and G share the side at e-coordinate h1 + 1, over an f-interval
    fh, fg = dot(H[0], F_T), dot(G[0], F_T)
    lo, hi = segment_overlap(fh - 0.5, fh + 0.5, fg - 0.5, fg + 0.5)
    segs.append((add(mul(H1 + 1, E_T), mul(lo, F_T)),
                 add(mul(H1 + 1, E_T), mul(hi, F_T))))
    for p, q in segs:
        assert norm(sub(q, p)) > 0.05
    # the corner of E on the top side of H, the corner of A on the right
    # side of G
    pE = min(corners(E), key=lambda v: dot(v, F_T))
    pA = min(corners(A), key=lambda v: dot(v, E_T))
    assert abs(dot(pE, F_T) - (H2 + 1)) < 1e-9
    assert abs(dot(pA, E_T) - (H1 + 2)) < 1e-9
    assert abs(dot(pE, E_T) - (H1 + 0.5)) < 0.5
    assert abs(dot(pA, F_T) - dot(G[0], F_T)) < 0.5
    return segs, [pE, pA]


# ----------------------------------------------------------------- figures

def eight():
    M = model(*BOX)
    ok, core, seps = admissible(*BOX)
    assert ok
    check_packing(M)
    for P in ROOT['P']:
        assert abs(norm(P) - R8) < 1e-9
    # Lemma 11.3: the identities of the contacts
    tau = 0.5 * (1 + C0 + S0)
    assert abs(dot(E_T, sub(M['G'][0], M['H'][0])) - 1) < 1e-12
    assert abs(dot(E_T, sub(M['A'][0], M['G'][0])) - tau) < 1e-9
    assert abs(dot(F_T, sub(M['E'][0], M['H'][0])) - tau) < 1e-9
    # K holds the closed core disk and touches none of the others
    assert core > 0 and min(seps.values()) > 0.02
    m = R8 + 0.24
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.2, dash='6 4')
    draw_model(f, M, labels=False)
    core_disk(f)
    segs, points = contact_features(M)
    for p, q in segs:
        f.line(p, q, stroke=INK, width=4)
    for p in points:
        f.dot(p, r=4.6)
    for k, sq in M.items():
        pos = shift(sq[0], (0.2, 0.28)) if k == 'K' else sq[0]
        f.text(pos, k, size=18, color=INK if k == 'K' else ROLE_COLOR[k])
    for j, P in enumerate(ROOT['P']):
        f.dot(P, r=3.6, fill=INK)
        f.text(mul((R8 + 0.13) / R8, P), sb(it('P'), str(j + 1), size=15),
               size=15)
    origin(f, dx=0.03, dy=-0.12)
    f.save('11-eight/eight', 'The optimal packing of eight unit squares in its '
           'circle of radius about 1.9788, with the five corners on the circle, '
           'the seven contacts and the central square holding the disk of '
           'radius 1/12')


FAMILY = [((0.14, 0.0, 0.1, 1.35, -0.32), 'box centre'),
          ((0.17, -0.18, 0.07, 0.92, -0.32), it('T') + ' lowered'),
          ((0.14, 0.015, 0.08, 1.35, -0.1), it('G') + ' pushed inward'),
          ((-0.0475, -0.0325, -0.3, ZETA_PLUS, ETA_MINUS),
           it('T') + ' and ' + it('G') + ' on the circle')]


def family():
    gap = 0.35
    m = R8 + 0.06
    s = 92
    W = 2 * (2 * m) + gap
    H = 2 * (2 * m + 0.42) + 0.1
    f = Figure(0, W, -H, 0, s)
    for k, (p, name) in enumerate(FAMILY):
        ok, core, seps = admissible(*p)
        assert ok, name
        M = model(*p)
        check_packing(M)
        col, row = k % 2, k // 2
        at = (m + col * (2 * m + gap), -(m + row * (2 * m + 0.52)))
        f.circle(at, R8, stroke=INK, width=1.1, dash='6 4')
        draw_model(f, M, at=at, labels=False)
        core_disk(f, at)
        for kk, sq in M.items():
            pos = shift(sq[0], mul(0.3, u(math.atan2(sq[0][1], sq[0][0]) + 1.2))
                        if kk == 'K' else (0, 0))
            if kk == 'K':
                pos = shift(sq[0], (0.18, 0.26))
            f.text(shift(at, pos), kk, size=12,
                   color=INK if kk == 'K' else ROLE_COLOR[kk])
        for sq in M.values():
            for v in corners(sq):
                if abs(norm(v) - R8) < 1e-9:
                    f.dot(shift(at, v), r=2.6)
        f.dot(at, r=1.8)
        word(f, shift(at, (0, -m - 0.22)), name, size=13)
    # the second and fourth panels move T and G as described
    assert FAMILY[3][0][3] == ZETA_PLUS and FAMILY[3][0][4] == ETA_MINUS
    f.save('11-eight/family', 'Four optimal packings of eight unit squares: '
           'the five squares on the circle are fixed, while the top square, '
           'the turned square G and the central square move')


def contour_segments(fn, x0, x1, y0, y1, nx, ny, level):
    """Marching squares: the segments of the level set {fn = level} on a
    grid, as pairs of points."""
    xs = [x0 + (x1 - x0) * i / nx for i in range(nx + 1)]
    ys = [y0 + (y1 - y0) * j / ny for j in range(ny + 1)]
    val = [[fn(x, y) - level for y in ys] for x in xs]
    segs = []

    def edge(i, j, k):
        # the crossing on edge k of cell (i, j): 0 bottom, 1 right, 2 top,
        # 3 left
        (a, b) = {0: ((i, j), (i + 1, j)), 1: ((i + 1, j), (i + 1, j + 1)),
                  2: ((i, j + 1), (i + 1, j + 1)), 3: ((i, j), (i, j + 1))}[k]
        va, vb = val[a[0]][a[1]], val[b[0]][b[1]]
        s = va / (va - vb)
        return (xs[a[0]] + s * (xs[b[0]] - xs[a[0]]),
                ys[a[1]] + s * (ys[b[1]] - ys[a[1]]))
    for i in range(nx):
        for j in range(ny):
            v = [val[i][j], val[i + 1][j], val[i + 1][j + 1], val[i][j + 1]]
            cross = [k for k, (p, q) in enumerate(((v[0], v[1]), (v[1], v[2]),
                                                   (v[3], v[2]), (v[0], v[3])))
                     if (p < 0) != (q < 0)]
            if len(cross) == 2:
                segs.append((edge(i, j, cross[0]), edge(i, j, cross[1])))
            elif len(cross) == 4:
                segs.append((edge(i, j, 0), edge(i, j, 3)))
                segs.append((edge(i, j, 1), edge(i, j, 2)))
    return segs


def chain_figure():
    # the pose of the left panel: P5 visibly outside the circle
    yp, tp = -0.64, 0.0
    ch = chain(Q8, yp, tp)
    assert ch['F'] > 0.4
    c, s = ch['c'], ch['s']
    et, ft = (c, s), (-s, c)
    tdeg = math.degrees(tp)

    def fr(a, b):
        return (c * a - s * b, s * a + c * b)
    sq = {'A': ((ch['x1'] - 0.5, yp + 0.5), 0.0),
          'B': ((ch['x2'] - 0.5, yp + 1.5), 0.0),
          'D': ((ch['x3'] + 0.5, ch['y3'] - 0.5), 0.0),
          'E': ((ch['x4'] + 0.5, ch['y4'] + 0.5), 0.0),
          'T': ((ch['x2'] - 1.5, 1.2), 0.0),
          'H': (fr(ch['h1'] + 0.5, ch['h2'] + 0.5), tdeg),
          'G': (fr(ch['h1'] + 1.5, ch['h2'] + 0.65), tdeg)}
    for j in range(4):
        assert abs(norm(ch['P'][j]) - R8) < 1e-9
    P5 = ch['P'][4]
    assert norm(P5) - R8 > 0.02
    # left panel
    m = R8 + 0.25
    s1 = 92
    gapx = 0.55
    # right panel geometry, in panel units
    pw, ph = 3.2, 3.2
    f = Figure(-m, m + gapx + pw + 0.55, -m, m, s1)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    for k, q in sq.items():
        draw_square(f, q, fill=ROLE_FILL[k], stroke=ROLE_COLOR[k])
        f.text(q[0], k, size=14, color=ROLE_COLOR[k])
    for j, P in enumerate(ch['P']):
        f.dot(P, r=3.2, fill=RED if j == 4 else INK)
        f.text(mul((norm(P) + 0.14) / norm(P), P), sb(it('P'), str(j + 1),
                                                     size=14), size=14,
               color=RED if j == 4 else INK)
    f.line(mul(R8 / norm(P5), P5), P5, stroke=RED, width=2.4)
    origin(f, dx=0.05, dy=-0.1)
    # right panel: level curves of F(q*, y, t)
    y0, y1, t0, t1 = -1.12, -0.6, -0.2, 0.45
    ox, oy = m + gapx + 0.45, -m + 0.45
    kx, ky = (pw - 0.45) / (y1 - y0), (ph - 0.6) / (t1 - t0)

    def P(y, t):
        return (ox + (y - y0) * kx, oy + (t - t0) * ky)
    fn = lambda yy, tt: chain(Q8, yy, tt)['F']
    levels = [0.005, 0.02, 0.05, 0.1, 0.2, 0.35]
    for lev, col in zip(levels, [BLUE] * len(levels)):
        for a, b in contour_segments(fn, y0, y1, t0, t1, 120, 120, lev):
            f.line(P(*a), P(*b), stroke=col, width=1.1)
    # the defect is positive away from its minimum, which is 0
    for yy in [y0 + (y1 - y0) * i / 40 for i in range(41)]:
        for tt in [t0 + (t1 - t0) * j / 40 for j in range(41)]:
            assert fn(yy, tt) > -1e-9
    # frame and axes
    f.polygon([P(y0, t0), P(y1, t0), P(y1, t1), P(y0, t1)], stroke=INK,
              width=1)
    for yy, lab in ((-1.1, '−1.1'), (-1.0, '−1'), (-0.9, '−0.9'),
                    (-0.8, '−0.8'), (-0.7, '−0.7'), (-0.6, '−0.6')):
        q = P(yy, t0)
        f.line(q, shift(q, (0, -0.04)), width=1)
        f.text(shift(q, (0, -0.16)), lab, size=12, italic=False)
    for tt, lab in ((-0.1, '−0.1'), (0.0, '0'), (0.1, '0.1'), (0.2, '0.2'),
                    (0.3, '0.3'), (0.4, '0.4')):
        q = P(y0, tt)
        f.line(q, shift(q, (-0.04, 0)), width=1)
        f.text(shift(q, (-0.07, 0)), lab, size=12, italic=False, anchor='end')
    f.text(P(y1, t0 - 0.06), it('y'), size=15, anchor='end', dy=4)
    f.text(P(y0 - 0.03, t1), it('t'), size=15, anchor='end')
    f.dot(P(YSTAR, TSTAR), r=3.4)
    f.text(shift(P(YSTAR, TSTAR), (0.08, 0.02)),
           '(' + sb(it('y'), '*', ',' + NB, 14) + sb(it('t'), '*', ')', 14),
           size=14, anchor='start')
    f.open_dot = None
    q = P(yp, tp)
    f.add(f'<circle cx="{f.p(*q)[0]:.1f}" cy="{f.p(*q)[1]:.1f}" r="3.6" '
          f'fill="#ffffff" stroke="{RED}" stroke-width="1.6"/>')
    f.save('11-eight/chain', 'Left: the five-corner chain at the squared '
           'radius q* for a pose with its fifth corner outside the circle. '
           'Right: level curves of the defect F(q*, y, t), around its zero at '
           '(y*, t*)')


def sliders():
    M = model(*BOX)
    ext = {k: v for k, v in M.items() if k not in 'KTG'}
    lowT = model(*BOX[:3], 7 / 12, BOX[4])['T']
    highT = model(*BOX[:3], ZETA_PLUS, BOX[4])['T']
    farG = model(*BOX[:4], ETA_MINUS)['G']
    nearG = model(*BOX[:4], ETA_PLUS)['G']
    # the extreme positions touch the core or the circle
    assert abs(core_distance(lowT) - CORE) < 1e-12
    assert abs(farthest_sq(highT) - Q8) < 1e-9
    assert abs(farthest_sq(farG) - Q8) < 1e-9
    assert abs(core_distance(nearG) - CORE) < 1e-9
    for zeta in (7 / 12, ZETA_PLUS):
        for eta in (ETA_MINUS, ETA_PLUS):
            Mz = model(*BOX[:3], zeta, eta)
            check_packing({k: v for k, v in Mz.items() if k != 'K'})
    m = R8 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.2, dash='6 4')
    draw_model(f, ext, labels=False)
    core_disk(f)
    for sq, col, fill in ((lowT, CYAN, ROLE_FILL['T']),
                          (highT, CYAN, ROLE_FILL['T']),
                          (farG, YELLOW, ROLE_FILL['G']),
                          (nearG, YELLOW, ROLE_FILL['G'])):
        draw_square(f, sq, fill=fill, opacity=0.45, stroke=col, dash='6 3',
                    width=1.6)
    f.line(lowT[0], highT[0], stroke=CYAN, width=1.8, dash='2 3')
    f.line(farG[0], nearG[0], stroke=YELLOW, width=1.8, dash='2 3')
    for p in (lowT[0], highT[0], farG[0], nearG[0]):
        f.dot(p, r=2.6)
    for k, sq in ext.items():
        f.text(sq[0], k, size=17, color=ROLE_COLOR[k])
    f.text(shift(highT[0], (0.0, 0.2)), sb(it('ζ'), '+', size=15), size=15,
           color=CYAN)
    f.text(shift(lowT[0], (0.0, -0.2)), '7/12', size=14, italic=False,
           color=CYAN)
    f.text(shift(farG[0], (0.12, -0.22)), sb(it('η'), '−', size=15),
           size=15, color=YELLOW)
    f.text(shift(nearG[0], (0.1, 0.2)), sb(it('η'), '+', size=15), size=15,
           color=YELLOW)
    f.text(shift(mul(0.5, add(lowT[0], highT[0])), (0.16, 0.05)), 'T', size=17,
           color=CYAN, anchor='start')
    f.text(shift(mul(0.5, add(farG[0], nearG[0])), (0.2, 0.0)), 'G', size=17,
           color=YELLOW, anchor='start')
    origin(f, dx=-0.04, dy=-0.13)
    f.save('11-eight/sliders', 'The seven exterior squares of the model with '
           'the ranges of the top square T and the turned square G: their '
           'extreme positions, dashed, touch the disk of radius 1/12 or the '
           'circle')


def section():
    w, zeta, eta = BOX[2], BOX[3], BOX[4]
    M = model(0, 0, w, zeta, eta)
    C, S = (1 - w * w) / (1 + w * w), 2 * w / (1 + w * w)
    K0 = ((BOX[0], BOX[1]), math.degrees(2 * math.atan(w)))
    # half planes <n, c> <= h in the centre c of K: one active separating
    # axis per exterior square, chosen at the box centre, and the core square
    halfplanes = []
    for k in EXTERIOR:
        best = None
        for sq in (K0, M[k]):
            for n in frame(sq):
                for sg in (1, -1):
                    nn = mul(sg, n)
                    mg = axis_margin(K0, M[k], nn)
                    if best is None or mg > best[0]:
                        best = (mg, nn)
        n = best[1]
        thr = half_width(K0, n) + half_width(M[k], n)
        # <n, p_k - c> >= thr  <=>  <n, c> <= <n, p_k> - thr
        halfplanes.append((n, dot(n, M[k][0]) - thr, k))
    for sg in (1, -1):
        for n in ((C, S), (-S, C)):
            halfplanes.append((mul(sg, n), 5 / 12, 'core'))
    poly = [(-1, -1), (1, -1), (1, 1), (-1, 1)]
    for n, h, _ in halfplanes:
        poly = clip(poly, n[0], n[1], h)
    assert len(poly) >= 3

    def inside(c, eps=0.0):
        return all(dot(n, c) <= h + eps for n, h, _ in halfplanes)
    # the polygon is the admissible section, away from its boundary
    xs = [p[0] for p in poly]
    ys = [p[1] for p in poly]
    for i in range(61):
        for j in range(61):
            c = (min(xs) - 0.02 + (max(xs) - min(xs) + 0.04) * i / 60,
                 min(ys) - 0.02 + (max(ys) - min(ys) + 0.04) * j / 60)
            adm = admissible(c[0], c[1], w, zeta, eta)[0]
            if inside(c, -2e-4):
                assert adm, c
            if not inside(c, 2e-4):
                assert not adm, c
    assert inside((BOX[0], BOX[1]))
    for x in (0.139, 0.141):
        for y in (-0.001, 0.001):
            assert inside((x, y))
    pad = 0.035
    x0, x1, y0, y1 = min(xs) - pad - 0.05, max(xs) + pad + 0.02, min(ys) - pad - 0.012, max(ys) + pad
    f = Figure(x0, x1, y0, y1, 1500)
    f.polygon(poly, fill=FILLS[0], stroke='none')
    # label each side by its square
    for i in range(len(poly)):
        a, b = poly[i], poly[(i + 1) % len(poly)]
        mid = mul(0.5, add(a, b))
        tight = [hp for hp in halfplanes if abs(dot(hp[0], mid) - hp[1]) < 1e-9]
        assert tight
        n, h, k = tight[0]
        if k == 'core':
            f.line(a, b, stroke=RED, width=1.6, dash='5 3')
        else:
            f.line(a, b, stroke=ROLE_COLOR[k], width=2.2)
            if norm(sub(a, b)) > 0.012:
                f.text(add(mid, mul(0.012, n)), k, size=15,
                       color=ROLE_COLOR[k])
    # the box section and the box centre
    bx = [(0.139, -0.001), (0.141, -0.001), (0.141, 0.001), (0.139, 0.001)]
    f.polygon(bx, fill=INK, stroke=INK, width=1)
    f.text((0.141 + 0.004, 0.0), 'box', size=13, anchor='start', italic=False)
    # axes
    ax0, ay0 = x0 + 0.03, y0 + 0.012
    f.line((ax0, ay0), (x1 - 0.004, ay0), width=1, arrow=True)
    f.line((ax0, ay0), (ax0, y1 - 0.004), width=1, arrow=True)
    for x in (0.10, 0.12, 0.14, 0.16):
        f.line((x, ay0), (x, ay0 - 0.004), width=1)
        f.text((x, ay0 - 0.012), f'{x:.2f}', size=12, italic=False)
    for y in (-0.2, -0.15, -0.1, -0.05, 0.0):
        f.line((ax0, y), (ax0 - 0.004, y), width=1)
        f.text((ax0 - 0.006, y), f'{y:.2f}'.replace('-', '−'), size=12,
               italic=False, anchor='end')
    f.text((x1 - 0.004, ay0 + 0.01), it('x'), size=15, anchor='end')
    f.text((ax0 + 0.006, y1 - 0.006), it('y'), size=15, anchor='start')
    f.save('11-eight/section', 'The centres of the central square admissible '
           'for w = 0.1, zeta = 1.35 and eta = -0.32: a polygon bounded by '
           'contacts with exterior squares and by the core condition, with '
           'the section of the box of Proposition 11.7')


def closed_arcs(sq, r, steps=14400):
    """The arcs of the circle of radius r about o in the closed square, as
    angle intervals, and their total length."""
    c, deg = sq
    e, fv = frame(sq)

    def inside(t):
        p = (r * math.cos(t), r * math.sin(t))
        d = sub(p, c)
        return abs(dot(d, e)) <= 0.5 + 1e-12 and abs(dot(d, fv)) <= 0.5 + 1e-12
    ts = [2 * PI * k / steps for k in range(steps)]
    flags = [inside(t) for t in ts]
    if all(flags):
        return [(0.0, 2 * PI)], 2 * PI
    start = flags.index(False)
    runs, run = [], None
    for k in range(start, start + steps + 1):
        t = ts[k % steps] + 2 * PI * (k // steps)
        if flags[k % steps] and run is None:
            run = t
        elif not flags[k % steps] and run is not None:
            runs.append((run, t))
            run = None
    return runs, sum(b - a for a, b in runs)


def measure():
    M = model(*BOX)
    m = R8 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    draw_model(f, M, labels=False)
    f.circle((0, 0), 1.0, stroke=FAINT, width=1.0)
    f.circle((0, 0), 1.25, stroke=FAINT, width=1.0)
    values = {}
    total1 = total2 = 0.0
    for k in EXTERIOR:
        a1, L1 = closed_arcs(M[k], 1.0)
        a2, L2 = closed_arcs(M[k], 1.25)
        values[k] = 3 * L1 + L2
        total1 += L1
        total2 += L2
        for t0, t1 in a1:
            f.arc((0, 0), 1.0, t0, t1, ROLE_COLOR[k], width=5)
        for t0, t1 in a2:
            f.arc((0, 0), 1.25, t0, t1, ROLE_COLOR[k], width=5)
        beta = math.atan2(M[k][0][1], M[k][0][0])
        f.text(mul(1.72, u(beta)), k, size=17, color=ROLE_COLOR[k])
    a1, L1K = closed_arcs(M['K'], 1.0)
    assert L1K == 0 and all(v > PI for v in values.values())
    assert total1 <= 2 * PI + 1e-3 and total2 <= 2 * PI + 1e-3
    f.text(shift(M['K'][0], (0.2, 0.28)), 'K', size=16)
    f.text(mul(0.82, u(-2.45)), sb('Γ', '1', size=15), size=15,
           italic=False)
    f.text(mul(1.125, u(-2.45)), sb('Γ', '5/4', size=13), size=13,
           italic=False)
    origin(f, dx=0.05, dy=-0.1)
    who = min(values, key=values.get)
    MEASURE[0] = (values[who], who)
    f.save('11-eight/measure', 'The optimal packing with the unit circle and the '
           'circle of radius 5/4 about o; each exterior square holds arcs of both '
           'circles, drawn in its colour')


def clip_rect(poly, x0, x1, y0, y1):
    for a, b, c in ((1, 0, x1), (-1, 0, -x0), (0, 1, y1), (0, -1, -y0)):
        poly = clip(poly, a, b, c)
    return poly


def core_figure():
    M = model(*BOX)
    ok, core, seps = admissible(*BOX)
    assert ok and core > 0
    for k in EXTERIOR:
        assert norm(M[k][0]) >= 7 / 12 and core_distance(M[k]) > CORE
    m = R8 + 0.1
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.0, dash='6 4')
    draw_model(f, M, labels=False)
    f.circle((0, 0), 7 / 12, stroke=INK, width=1.3, dash='2 3')
    core_disk(f)
    for k in EXTERIOR:
        f.dot(M[k][0], r=3)
        f.text(shift(M[k][0], (0.0, 0.2)), k, size=15, color=ROLE_COLOR[k])
    f.text(shift(M['K'][0], (0.2, 0.28)), 'K', size=16)
    f.text(mul(7 / 12 + 0.17, u(3.5)), '7/12', size=13, italic=False)
    f.line(mul(CORE, u(-0.6)), mul(0.33, u(-0.6)), stroke=RED, width=0.9)
    f.text(mul(0.42, u(-0.6)), '1/12', size=13, italic=False, color=RED)
    origin(f, dx=-0.03, dy=0.13, r=2.2)
    f.save('11-eight/core', 'The optimal packing with the disk of radius 1/12 '
           'about o inside the central square, and the circle of radius 7/12 '
           'outside which the centres of the exterior squares lie')


# ------------------------------------------------------------ radial curves

def outer_a(q, tg):
    """The first coordinate of the state with tangent b/a = tg on O_q."""
    A, B, C = 1 + tg * tg, 1 + tg, 0.5 - q
    return (-B + math.sqrt(B * B - 4 * A * C)) / (2 * A)


def core_a(tg):
    """The first coordinate of the state with tangent tg on the core curve."""
    if tg <= 6 / 7:
        return 7 / 12
    A, B, C = 1 + tg * tg, -(1 + tg), 0.5 - 1 / 144
    return (-B + math.sqrt(B * B - 4 * A * C)) / (2 * A)


def plane_frame(f, a0, a1, b1, ticks_a, ticks_b, ab=0.0):
    f.line((a0, ab), (a1, ab), width=1, arrow=True)
    f.line((a0, ab - 0.02), (a0, b1), width=1, arrow=True)
    f.text((a1, ab - 0.06), it('a'), size=15, anchor='end')
    f.text((a0 - 0.03, b1 - 0.02), it('b'), size=15, anchor='end')
    for x, lab in ticks_a:
        f.line((x, ab - 0.012), (x, ab + 0.012), width=1)
        f.text((x, ab - 0.055), lab, size=12, italic=False)
    for y, lab in ticks_b:
        f.line((a0 - 0.012, y), (a0 + 0.012, y), width=1)
        f.text((a0 - 0.025, y), lab, size=12, italic=False, anchor='end')


def radial():
    q = Q0
    amax = outer_a(q, 0.0)
    dO, dC = outer_a(q, 1.0), core_a(1.0)
    assert abs(dO - (math.sqrt(q / 2) - 0.5)) < 1e-12
    assert abs(dC - (0.5 + SQ2 / 24)) < 1e-12
    n = 120
    outer = [(outer_a(q, tg), tg * outer_a(q, tg))
             for tg in (j / n for j in range(n + 1))]
    corner = [(core_a(tg), tg * core_a(tg))
              for tg in (6 / 7 + (1 - 6 / 7) * j / 40 for j in range(41))]
    region = [(7 / 12, 0.0)] + outer + list(reversed(corner))
    f = Figure(0.3, 1.55, -0.12, 1.0, 420)
    f.polygon(region, fill=FILLS[0], stroke='none')
    polyline(f, outer, stroke=BLUE, width=2.2)
    polyline(f, [(7 / 12, 0.0), (7 / 12, 0.5)] + corner, stroke=RED, width=2.2)
    f.line((0.45, 0.45), (0.98, 0.98), stroke=FAINT, width=1, dash='3 3')
    for slope, tgt in ((0.25, outer_a(q, 0.25)), (3 / 7, outer_a(q, 3 / 7)),
                       (6 / 7, 7 / 12)):
        a0 = 0.5 if slope > 0.5 else 7 / 12
        f.line((a0, a0 * slope), (tgt, slope * tgt), stroke=INK, width=1,
               dash='4 3')
    for tg0, tg1, lab in ((0, 0.25, 'L'), (0.25, 3 / 7, 'M'), (3 / 7, 1, 'H')):
        tg = (tg0 + tg1) / 2
        a = outer_a(q, tg)
        p = (a, tg * a)
        nrm = mul(1 / norm(add(p, (0.5, 0.5))), add(p, (0.5, 0.5)))
        sans_text(f, add(p, mul(0.075, nrm)), lab, size=16, color=BLUE)
    f.text((0.6, 0.12), 'side', size=13, italic=False, color=RED, anchor='start')
    f.text((0.6, 0.555), 'corner', size=13, italic=False, color=RED,
           anchor='start')
    f.text((1.42, 0.27), '𝒪', size=18, italic=False, color=BLUE)
    f.text((0.545, 0.36), '𝒞', size=18, italic=False, color=RED)
    f.text((0.92, 1.0), 'b = a', size=12, color=FAINT, anchor='start')
    plane_frame(f, 0.36, 1.53, 0.98,
                ((0.5, '½'), (7 / 12, '7/12'), (1.0, '1')),
                ((0.5, '½'),), ab=0.0)
    M = model(*BOX)
    for k in EXTERIOR:
        cs = canonical(M[k])
        a, b = cs['a'], cs['b']
        phi = (a + 0.5) ** 2 + (b + 0.5) ** 2
        if k in 'ABDEH':
            assert abs(phi - Q8) < 1e-9
        else:
            assert phi < Q8 - 0.01 and core_distance(M[k]) > CORE
        f.dot((a, b), r=3.6, fill=ROLE_COLOR[k])
        off = {'A': (-0.045, -0.02), 'B': (0.035, 0.0), 'D': (0.04, -0.01),
               'E': (-0.045, 0.0), 'H': (0.04, 0.03), 'T': (-0.045, 0.0),
               'G': (0.0, -0.045)}[k]
        f.text(add((a, b), off), k, size=14, color=ROLE_COLOR[k])
    f.save('11-eight/radial', 'The radial curves in the (a, b)-plane: the core '
           'curve with its side and corner, the outer curve divided into the '
           'types L, M and H, and the states of the exterior squares of the '
           'optimal packing')


# ------------------------------------------------------- boundary reduction

WITNESS = {'H': ('e', 'G'), 'G': ('e', 'A'), 'A': ('f', 'B'),
           'B': ('-e0', 'T'), 'T': ('-e0', 'D'), 'D': ('-f', 'E'),
           'E': ('-fH', 'H')}


def witness_normal(i):
    """The unit normal, from S_i towards S_{i+1}, of the contact of the
    model on the edge from role i (Lemma 11.3)."""
    kind = WITNESS[i][0]
    return {'e': E_T, 'f': (0.0, 1.0), '-e0': (-1.0, 0.0), '-f': (0.0, -1.0),
            '-fH': mul(-1, F_T)}[kind]


def witness_margin(M, i):
    j = WITNESS[i][1]
    return axis_margin(M[i], M[j], witness_normal(i))


def reduction():
    M = model(*BOX)
    ext = {k: v for k, v in M.items() if k != 'K'}
    for i in CYCLE:
        assert abs(witness_margin(ext, i)) < 1e-9
    moved = dict(ext)
    moved['T'] = model(*BOX[:3], ZETA_PLUS, BOX[4])['T']
    moved['G'] = model(*BOX[:4], ETA_MINUS)['G']
    for k in 'TG':
        assert abs(farthest_sq(moved[k]) - Q8) < 1e-9
        assert core_distance(moved[k]) > CORE
    for i in CYCLE:
        assert witness_margin(moved, i) > -1e-9
    m = R8 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    draw_model(f, ext, labels=False)
    core_disk(f)
    tags = {}
    for k in 'TG':
        draw_square(f, moved[k], stroke=ROLE_COLOR[k], dash='6 3', width=1.6)
        c = ext[k][0]
        d = sub(moved[k][0], c)
        d = mul(1 / norm(d), d)
        nrm = (-d[1], d[0])
        arrow(f, add(c, mul(-0.13, d)), add(c, mul(0.13, d)),
              color=ROLE_COLOR[k], width=1.6)
        tags[k] = add(c, mul(-0.15, nrm))
    # the witnesses of T: the vertical lines x = x2 - 2 and x = x2 - 1
    for x in (X2 - 2, X2 - 1):
        y = math.sqrt(R8 * R8 - x * x)
        f.line((x, 0.08), (x, y), stroke=CYAN, width=1.1, dash='3 3')
    # the witnesses of G: the lines <e, p> = h1 + 1 and h1 + 2
    for h in (H1 + 1, H1 + 2):
        w = math.sqrt(R8 * R8 - h * h)
        p0 = add(mul(h, E_T), mul(-w, F_T))
        p1 = add(mul(h, E_T), mul(-0.12, F_T))
        f.line(p0, p1, stroke=YELLOW, width=1.1, dash='3 3')
    for k, sq in ext.items():
        f.text(tags.get(k, sq[0]), k, size=17, color=ROLE_COLOR[k])
    origin(f, dx=0.05, dy=-0.1)
    f.save('11-eight/reduction', 'The boundary reduction for the exterior '
           'squares of the optimal packing: T moves up between its two witness '
           'lines until it touches the circle, and G moves along H until it '
           'touches the circle')


def outer_radius(q, alpha):
    B = math.cos(alpha) + abs(math.sin(alpha))
    return (-B + math.sqrt(B * B - 4 * (0.5 - q))) / 2


def expansion():
    M = model(*BOX)
    cyc = {k: v for k, v in M.items() if k != 'K'}
    cyc['T'] = model(*BOX[:3], ZETA_PLUS, BOX[4])['T']
    cyc['G'] = model(*BOX[:4], ETA_MINUS)['G']
    alpha = {k: canonical(sq)['alpha'] for k, sq in cyc.items()}
    beta = {k: canonical(sq)['beta'] for k, sq in cyc.items()}
    for k, sq in cyc.items():
        assert abs(outer_radius(Q8, alpha[k]) - norm(sq[0])) < 1e-9

    def at_level(q):
        return {k: (mul(outer_radius(q, alpha[k]), u(beta[k])), sq[1])
                for k, sq in cyc.items()}
    qs = [3.2 + 0.8 * j / 160 for j in range(161)]
    curves = {i: [witness_margin(at_level(q), i) for q in qs] for i in CYCLE}
    for i in CYCLE:
        ys = curves[i]
        for q0, q1, y0, y1 in zip(qs, qs[1:], ys, ys[1:]):
            if y0 >= 0:
                assert (y1 - y0) / (q1 - q0) > 1 / 24
        assert abs(witness_margin(at_level(Q8), i)) < 1e-9
        assert witness_margin(at_level(4.0), i) > 0.01
    # left panel: the outer radius r(q, B) for B = 1 and B = sqrt 2
    f = Figure(0.0, 7.75, -0.15, 3.15, 106)
    ox, oy, kx, ky = 0.55, 0.3, 2.6 / 1.5, 2.55 / 0.7
    PL = lambda q, r: (ox + kx * (q - 2.5), oy + ky * (r - 0.8))
    f.line(PL(2.5, 0.8), PL(4.12, 0.8), width=1, arrow=True)
    f.line(PL(2.5, 0.8), PL(2.5, 1.575), width=1, arrow=True)
    for B, col in ((1.0, BLUE), (SQ2, ORANGE)):
        pts = []
        for j in range(121):
            q = 2.5 + 1.5 * j / 120
            r = (-B + math.sqrt(B * B - 4 * (0.5 - q))) / 2
            dr = 1 / math.sqrt(B * B + 4 * q - 2)
            assert 0.8 < r < 1.5 and 0.25 <= dr <= 1 / 3
            pts.append(PL(q, r))
        polyline(f, pts, stroke=col, width=2)
    f.text(shift(PL(3.2, (-1 + math.sqrt(1 + 4 * 2.7)) / 2), (0.05, 0.15)),
           it('B') + NB + '=' + NB + '1', size=13, color=BLUE, anchor='end',
           italic=False)
    f.text(shift(PL(3.5, (-SQ2 + math.sqrt(2 + 4 * 3.0)) / 2), (0.1, -0.2)),
           it('B') + NB + '=' + NB + '√2', size=13, color=ORANGE, anchor='start',
           italic=False)
    for q, lab in ((2.5, '5/2'), (3.0, '3'), (3.5, '3.5'), (4.0, '4')):
        f.line(PL(q, 0.8), shift(PL(q, 0.8), (0, -0.05)), width=1)
        f.text(shift(PL(q, 0.8), (0, -0.2)), lab, size=12, italic=False)
    for r, lab in ((1.0, '1'), (1.25, '1.25'), (1.5, '1.5')):
        f.line(PL(2.5, r), shift(PL(2.5, r), (-0.05, 0)), width=1)
        f.text(shift(PL(2.5, r), (-0.08, 0)), lab, size=12, italic=False,
               anchor='end')
    f.line(PL(Q8, 0.8), PL(Q8, 1.47), stroke=FAINT, width=1, dash='3 3')
    f.text(shift(PL(Q8, 1.47), (0, 0.13)), sb(it('q'), '*', size=13), size=13)
    f.text(PL(4.12, 0.83), it('q'), size=15, anchor='end')
    f.text(shift(PL(2.5, 1.575), (0.08, -0.06)), it('r'), size=15,
           anchor='start')
    # right panel: the seven witness margins against q
    ylo, yhi = -0.16, 0.04
    ox2, oy2, kx2, ky2 = 4.75, 0.3, 2.5 / 0.8, 2.55 / (yhi - ylo)
    PR = lambda q, y: (ox2 + kx2 * (q - 3.2), oy2 + ky2 * (y - ylo))
    f.line(PR(3.2, ylo), PR(4.08, ylo), width=1, arrow=True)
    f.line(PR(3.2, ylo), PR(3.2, yhi + 0.012), width=1, arrow=True)
    f.line(PR(3.2, 0), PR(4.05, 0), stroke=FAINT, width=1, dash='4 3')
    for i in CYCLE:
        pts = [PR(q, y) for q, y in zip(qs, curves[i]) if ylo <= y <= yhi]
        polyline(f, pts, stroke=ROLE_COLOR[i], width=1.6)
    for q, lab in ((3.2, '3.2'), (3.6, '3.6'), (4.0, '4')):
        f.line(PR(q, ylo), shift(PR(q, ylo), (0, -0.05)), width=1)
        f.text(shift(PR(q, ylo), (0.0, -0.2)), lab, size=12, italic=False)
    for y, lab in ((-0.15, '−0.15'), (-0.1, '−0.1'), (-0.05, '−0.05'),
                   (0.0, '0')):
        f.line(PR(3.2, y), shift(PR(3.2, y), (-0.05, 0)), width=1)
        f.text(shift(PR(3.2, y), (-0.08, 0)), lab, size=12, italic=False,
               anchor='end')
    f.dot(PR(Q8, 0), r=3.2)
    f.text(shift(PR(Q8, 0), (-0.05, 0.2)), sb(it('q'), '*', size=13), size=13,
           anchor='end')
    f.text(PR(4.08, ylo + 0.008), it('q'), size=15, anchor='start')
    f.text(shift(PR(3.2, yhi + 0.012), (0.08, -0.04)), 'witness margins',
           size=12, italic=False, anchor='start')
    f.save('11-eight/expansion', 'Left: the distance r(q, B) of a centre on the '
           'outer curve against q, for B = 1 and root 2. Right: the seven witness '
           'margins of the boundary cycle of the optimal packing moved to the '
           'level q, increasing and vanishing at q*')

# ------------------------------------------------------------ common point

def state_square(a, b, sigma, beta):
    """The square with the state (a, b), sign sigma and centre direction
    beta (Definition 11.14)."""
    r = math.hypot(a, b)
    alpha = sigma * math.atan2(b, a)
    return (mul(r, u(beta)), math.degrees(beta + alpha))


def common_point():
    q, lam, h = Q0, 41 / 40, 19 / 50
    target = (lam, 0.0)
    # every core-avoiding state of the disk contains the point, sampled
    states = []
    for j in range(41):
        tg = j / 40
        states.append((outer_a(q, tg), tg * outer_a(q, tg)))
        states.append((core_a(tg), tg * core_a(tg)))
    for a, b in states:
        assert a >= 107 / 200
        for sigma in (1, -1):
            for k in range(-10, 11):
                sq = state_square(a, b, sigma, h * k / 10)
                e, fv = frame(sq)
                d = sub(target, sq[0])
                assert abs(dot(d, e)) < 0.5 and abs(dot(d, fv)) < 0.5
    show = [((outer_a(q, 0.0), 0.0), 1, h, BLUE),
            ((outer_a(q, 1.0), outer_a(q, 1.0)), -1, -h, ORANGE),
            ((7 / 12, 0.5), 1, -h, GREEN),
            ((core_a(1.0), core_a(1.0)), -1, h, PURPLE)]
    f = Figure(-0.25, 2.1, -1.3, 1.3, 180)
    wedge = [(0, 0)] + [mul(math.sqrt(q), u(-h + 2 * h * j / 30))
                        for j in range(31)]
    f.polygon(wedge, fill=GREY, stroke='none', opacity=0.9)
    arc = [mul(math.sqrt(q), u(-0.85 + 1.7 * j / 80)) for j in range(81)]
    polyline(f, arc, stroke=INK, width=1.1, dash='6 4')
    for (a, b), sigma, beta, col in show:
        sq = state_square(a, b, sigma, beta)
        assert farthest_sq(sq) <= q + 1e-9 and core_distance(sq) >= CORE - 1e-9
        draw_square(f, sq, fill=FILLS[COLORS.index(col)], opacity=0.25,
                    stroke=col, width=1.8)
        f.dot(sq[0], r=2.2, fill=col)
    core_disk(f)
    f.dot(target, r=4.2, fill=RED)
    halo_text(f, shift(target, (0.08, -0.07)), '41/40', size=13,
              anchor='start', color=RED)
    for sgn in (1, -1):
        f.line((0, 0), mul(math.sqrt(q), u(sgn * h)), stroke=INK, width=1,
               dash='3 3')
    f.arc((0, 0), 0.55, -h, 0.0, INK, width=1.2)
    f.text(mul(0.68, u(-h / 2)), '19/50', size=12, italic=False,
           anchor='start')
    origin(f, dx=-0.05, dy=-0.1)
    f.save('11-eight/common-point', 'Squares that avoid the core and lie in the '
           'disk, with centre directions within 19/50 of the horizontal, all '
           'contain the point at distance 41/40 on the horizontal axis')


# ------------------------------------------------------------ forward axes

def margins_of(S, T):
    """The four forward margins M1..M4 of a consecutive pair, from the
    canonical frames (Lemma 11.19), as axis margins."""
    cs, ct = canonical(S), canonical(T)
    es, fs = u(cs['axis']), u(cs['axis'] + PI / 2)
    et, ft = u(ct['axis']), u(ct['axis'] + PI / 2)
    return {1: axis_margin(S, T, fs), 2: axis_margin(S, T, et),
            3: axis_margin(S, T, ft), 4: axis_margin(S, T, mul(-1, es)),
            'src+e': axis_margin(S, T, es), 'tgt-e': axis_margin(S, T, mul(-1, et)),
            'src-f': axis_margin(S, T, mul(-1, fs)),
            'tgt-f': axis_margin(S, T, mul(-1, ft))}


def axes_figure():
    M = model(*BOX)
    S, T = M['B'], M['T']
    cs, ct = canonical(S), canonical(T)
    assert abs(cs['axis']) < 1e-12 and abs(wrap(ct['axis'] - PI / 2)) < 1e-12
    mg = margins_of(S, T)
    assert abs(mg[3]) < 1e-9 and abs(mg[4]) < 1e-9
    assert mg[1] < 0 and mg[2] < 0
    for k in ('src+e', 'tgt-e', 'src-f', 'tgt-f'):
        assert mg[k] < -0.5
    a = cs['a']
    # the cap beyond the far side of the source: too thin for a square
    hcap = a + 0.5
    assert (hcap + 1) ** 2 + 0.25 > Q0
    f = Figure(-0.55, 2.15, -1.2, 2.15, 160)
    R0 = math.sqrt(Q0)
    arc = [mul(R0, u(-0.62 + (PI / 2 + 0.87) * j / 140)) for j in range(141)]
    polyline(f, arc, stroke=INK, width=1.1, dash='6 4')
    w = math.sqrt(R0 * R0 - hcap * hcap)
    cap = [(hcap, -w)] + [mul(R0, u(-math.asin(w / R0) + 2 * math.asin(w / R0)
                                     * j / 40)) for j in range(41)] + [(hcap, w)]
    f.polygon(cap, fill=RED_FILL, stroke='none')
    f.line((hcap, -1.15), (hcap, 2.0), stroke=RED, width=1.2, dash='5 3')
    draw_square(f, S, fill=ROLE_FILL['B'], stroke=ORANGE)
    draw_square(f, T, fill=ROLE_FILL['T'], stroke=CYAN)
    f.line((X2 - 1, BOX[3] - 0.5), (X2 - 1, YSTAR + 2), stroke=INK, width=3.5)
    core_disk(f)
    origin(f, dx=0.05, dy=-0.1)
    es, fs = (1.0, 0.0), (0.0, 1.0)
    et, ft = (0.0, 1.0), (-1.0, 0.0)
    L = 0.42
    arrows = [(S[0], fs, '1', True), (T[0], et, '2', True), (T[0], ft, '3', True),
              (S[0], mul(-1, es), '4', True), (S[0], es, '', False),
              (T[0], mul(-1, et), '', False), (S[0], mul(-1, fs), '', False),
              (T[0], mul(-1, ft), '', False)]
    for c, n, lab, keep in arrows:
        tip = add(c, mul(L, n))
        if keep:
            arrow(f, c, tip, color=INK, width=1.6)
            f.text(add(c, mul(L + 0.11, n)), lab, size=14, italic=False)
        else:
            arrow(f, c, tip, color=FAINT, width=1.2, dash='4 3')
    f.text(shift(S[0], (0.18, -0.3)), 'B', size=17, color=ORANGE)
    f.text(shift(T[0], (0.25, 0.3)), 'T', size=17, color=CYAN)
    f.text((hcap - 0.04, -0.9), it('a') + NB + '+' + NB + '½', size=13,
           anchor='end', color=RED)
    f.save('11-eight/axes', 'A source square B and its target T in the canonical '
           'frame of B, with the four retained signed axes numbered 1 to 4 and '
           'the four impossible ones faded; beyond the far side of the source the '
           'disk leaves only a thin cap')


# ------------------------------------------------------------- the walks

GAMMA_NUM = [[9200, 9100, 9005, 8833], [9100, 9100, 9005, 8833],
             [9005, 9005, 8912, 8926], [8833, 8833, 8926, 9099]]


def walks():
    from fractions import Fraction as Fr
    best = min(sum(GAMMA_NUM[w[i]][w[(i + 1) % 7]] for i in range(7))
               for w in itertools.product(range(4), repeat=7))
    assert Fr(best, 10000) == Fr(3881, 625)
    names = ['C', 'L', 'M', 'H']
    pos = {0: (0.0, 1.6), 1: (2.4, 1.6), 2: (2.4, 0.0), 3: (0.0, 0.0)}
    walk = [0, 2, 3, 0, 3, 0, 3]
    assert sum(GAMMA_NUM[walk[i]][walk[(i + 1) % 7]] for i in range(7)) == best
    hot = {(0, 2), (2, 3), (0, 3)}
    f = Figure(-0.9, 3.3, -0.75, 2.35, 150)
    for i in range(4):
        for j in range(i + 1, 4):
            p, q = pos[i], pos[j]
            res = (GAMMA_NUM[i][j] - 8833) / 10000
            on = (i, j) in hot
            f.line(p, q, stroke=ORANGE if on else FAINT, width=3 if on else 1.4)
            mid = mul(0.5, add(p, q))
            off = {(0, 1): (0.0, 0.1), (2, 3): (0.0, -0.17),
                   (0, 3): (-0.3, -0.04), (1, 2): (0.3, -0.04)}.get((i, j), (0.0, 0.0))
            if (i, j) == (0, 2):
                mid = add(mul(0.3, p), mul(0.7, q))
                off = (0.12, 0.1)
            if (i, j) == (1, 3):
                mid = add(mul(0.3, p), mul(0.7, q))
                off = (0.12, -0.1)
            halo_text(f, add(mid, off), f'{res:.4f}', size=13,
                      color=ORANGE if on else INK)
    for i in range(4):
        p = pos[i]
        out = mul(1 / norm(sub(p, (1.2, 0.8))), sub(p, (1.2, 0.8)))
        c = add(p, mul(0.34, out))
        f.circle(c, 0.25, stroke=FAINT, width=1.4)
        res = (GAMMA_NUM[i][i] - 8833) / 10000
        f.text(add(p, mul(0.86, out)), f'{res:.4f}', size=13, italic=False)
        f.circle(p, 0.17, stroke=INK, width=1.4, fill='#ffffff')
        sans_text(f, p, names[i], size=16)
    f.save('11-eight/walks', 'The four types C, L, M and H with the residuals of '
           'Gamma minus 0.8833 on their edges and loops, and a closed walk of '
           'length seven of least weight highlighted')


# -------------------------------------------------------------- the frames

def gfun(x):
    return 0.5 * (math.cos(x) + math.sin(x) - 1)


def frames_figure():
    # g is increasing and concave on [0, pi/4], with the stated values
    xs = [PI / 4 * j / 200 for j in range(201)]
    for x0, x1, x2 in zip(xs, xs[1:], xs[2:]):
        assert gfun(x0) < gfun(x1) and gfun(x1) >= (gfun(x0) + gfun(x2)) / 2
    assert 2 * gfun(0.7) > 2945220061 / 7200000000 > 10394 / 25425
    U = 2 * gfun(TSTAR)
    assert U < 10394 / 25425 and TSTAR < 0.7
    f = Figure(-1.75, 5.05, -1.55, 1.6, 110)
    rr = 1.15
    f.circle((0, 0), rr, stroke=INK, width=1.3)
    for j in range(8):
        a = 2 * PI * j / 8
        f.line(mul(rr - 0.05, u(a)), mul(rr + 0.05, u(a)), width=1)
    for j, lab in ((0, '0'), (2, 'π/8'), (4, 'π/4'), (6, '3π/8')):
        f.text(mul(rr + 0.24, u(2 * PI * j / 8)), lab, size=12, italic=False)
    # the bound 7/10 as an arc of the frame circle (4 times its angle)
    f.arc((0, 0), rr + 0.13, 0.0, 4 * 0.7, ORANGE, width=3)
    f.text(mul(rr + 0.38, u(1.4)), '7/10', size=13, italic=False, color=ORANGE)
    f.dot(mul(rr, u(0.0)), r=4.2, fill=BLUE)
    f.dot(mul(rr, u(4 * TSTAR)), r=4.2, fill=PINK)
    f.text(mul(rr - 0.5, u(-0.25)), 'A, B, T, D, E', size=12, color=BLUE)
    f.text(mul(rr - 0.32, u(4 * TSTAR + 0.25)), 'H, G', size=12, color=PINK)
    # right panel: g on [0, pi/4] and its chord
    ox, oy, kx, ky = 2.3, -1.2, 3.1, 7.5
    P = lambda x, y: (ox + kx * x, oy + ky * y)
    f.line(P(0, 0), P(0.86, 0), width=1, arrow=True)
    f.line(P(0, 0), P(0, 0.23), width=1, arrow=True)
    polyline(f, [P(x, gfun(x)) for x in xs], stroke=BLUE, width=2)
    gq = gfun(PI / 4)
    f.line(P(0, 0), P(PI / 4, gq), stroke=INK, width=1.1, dash='4 3')
    for x, lab in ((0.7, '7/10'), (PI / 4, 'π/4')):
        f.line(P(x, 0), P(x, -0.006), width=1)
        f.text(shift(P(x, 0), (0, -0.16)), lab, size=12, italic=False)
    f.line(P(0, gq), P(-0.012, gq), width=1)
    f.text(shift(P(0, gq), (-0.06, 0)), '(√2 − 1)/2', size=12, italic=False,
           anchor='end')
    f.dot(P(TSTAR, gfun(TSTAR)), r=3, fill=PINK)
    f.text(shift(P(TSTAR, gfun(TSTAR)), (0.05, 0.13)), sb(it('t'), '*', size=13),
           size=13, color=PINK)
    f.text(P(0.86, 0.012), it('x'), size=15, anchor='end')
    f.text(shift(P(0.42, gfun(0.42)), (-0.1, 0.14)), it('g'), size=15,
           color=BLUE, anchor='end')
    f.save('11-eight/frames', 'Left: the frames of the exterior squares of the '
           'optimal packing on the circle of directions modulo a quarter turn. '
           'Right: the frame charge g on [0, pi/4] with its chord')


# -------------------------------------------------------------- the words

def admissible_words():
    out = []
    for w in itertools.product(range(3), repeat=7):
        if sum(w) != 4 or w.count(2) > 1:
            continue
        if any(w[i] == w[(i + 1) % 7] == w[(i + 2) % 7] == 0 for i in range(7)):
            continue
        out.append(w)
    return out


def word_class(w):
    rots = [tuple(w[(i + k) % 7] for i in range(7)) for k in range(7)]
    rev = tuple(reversed(w))
    rots += [tuple(rev[(i + k) % 7] for i in range(7)) for k in range(7)]
    return min(rots)


def model_word(M):
    """The quarter word of the exterior squares of a model, from their
    canonical frames and frame lifts (Definition 11.24)."""
    th = {k: (TSTAR if k in 'HG' else 0.0) for k in CYCLE}
    cs = {k: canonical(M[k]) for k in CYCLE}
    word_ = []
    for i in range(7):
        a, b = CYCLE[i], CYCLE[(i + 1) % 7]
        gap = (cs[b]['beta'] - cs[a]['beta']) % (2 * PI)
        phi = gap + cs[b]['alpha'] - cs[a]['alpha']
        k = (phi - (th[b] - th[a])) / (PI / 2)
        assert abs(k - round(k)) < 1e-9
        word_.append(round(k))
    return word_


WORDS = ['0010012', '0010102', '0010201', '0011002', '0010111', '0011011',
         '0101011']


def words():
    adm = admissible_words()
    assert len(adm) == 70
    classes = sorted({word_class(w) for w in adm})
    assert classes == sorted(word_class(tuple(int(c) for c in w)) for w in WORDS)
    M = model(*BOX)
    assert model_word(M) == [0, 1, 0, 1, 0, 1, 1]
    f = Figure(-0.1, 7.75, -4.38, 0.95, 106)
    for j, w in enumerate(WORDS):
        c = (0.5 + 1.1 * j, 0.42)
        cand = (w == '0101011')
        f.circle(c, 0.36, stroke=ORANGE if cand else FAINT,
                 width=2.4 if cand else 1)
        for i, ch in enumerate(w):
            p = add(c, mul(0.36, u(PI / 2 - 2 * PI * i / 7)))
            fill = {'0': '#ffffff', '1': FILLS[0], '2': BLUE}[ch]
            f.circle(p, 0.085, stroke=INK, width=1.1, fill=fill)
        f.text(shift(c, (0, -0.58)), w, size=12, italic=False,
               color=ORANGE if cand else INK)
    # the model with its canonical axes and digits
    at = (3.85, -2.36)
    sc = 0.97
    for k in CYCLE:
        draw_square(f, M[k], fill=ROLE_FILL[k], stroke=ROLE_COLOR[k], at=at,
                    scale=sc)
    f.circle(at, R8 * sc, stroke=INK, width=1, dash='6 4')
    wd = model_word(M)
    for k in CYCLE:
        cs = canonical(M[k])
        c = shift(at, mul(sc, M[k][0]))
        arrow(f, c, add(c, mul(0.42, u(cs['axis']))), color=INK, width=1.5)
        f.text(add(c, mul(-0.2, u(cs['axis']))), k, size=14,
               color=ROLE_COLOR[k])
    for i in range(7):
        a, b = CYCLE[i], CYCLE[(i + 1) % 7]
        ba = math.atan2(M[a][0][1], M[a][0][0])
        bb = math.atan2(M[b][0][1], M[b][0][0])
        mid = math.atan2(math.sin(ba) + math.sin(bb), math.cos(ba) + math.cos(bb))
        f.text(shift(at, mul(0.5, u(mid))), str(wd[i]), size=15, italic=False,
               color=ORANGE)
    f.dot(at, r=2.2)
    f.save('11-eight/words', 'The seven quarter words as necklaces, with the word '
           '0101011 highlighted, and the optimal packing with the canonical axes '
           'of its exterior squares and the digit of each edge')


# ------------------------------------------------------------- the tangents

TANGENT_RANGE = {'H': (0.5, 1.0), 'G': (-0.8, -0.05), 'A': (-1.0, 1.0),
                 'B': (-1.0, 1.0), 'T': (0.05, 0.8), 'D': (-1.0, -0.5),
                 'E': (-1.0, 0.0)}


def tangents():
    M = model(*BOX)
    m = R8 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    for k in CYCLE:
        cs = canonical(M[k])
        lo, hi = TANGENT_RANGE[k]
        assert lo <= cs['tau'] <= hi
        if k in 'GT':
            assert lo < cs['tau'] < hi
        b0, b1 = cs['axis'] - math.atan(hi), cs['axis'] - math.atan(lo)
        fan = [(0, 0)] + [mul(1.85, u(b0 + (b1 - b0) * j / 40))
                          for j in range(41)]
        f.polygon(fan, fill=ROLE_FILL[k], stroke=ROLE_COLOR[k], width=1,
                  opacity=0.55)
    for k in CYCLE:
        cs = canonical(M[k])
        draw_square(f, M[k], stroke=ROLE_COLOR[k], width=1.2, dash='3 3')
        arrow(f, (0, 0), mul(1.95, u(cs['axis'])), color=ROLE_COLOR[k],
              width=1.4)
        f.dot(M[k][0], r=3.4, fill=ROLE_COLOR[k])
        f.text(add(M[k][0], mul(0.22, u(cs['beta'] + 0.5))), k, size=16,
               color=ROLE_COLOR[k])
    origin(f, dx=0.05, dy=-0.1)
    f.save('11-eight/tangents', 'The exterior squares of the optimal packing with '
           'the fans of centre directions allowed by their signed tangents after '
           'the tangent exclusions, and their actual centres')


# ------------------------------------------------- a row and its angle chains

# Data copied from G_LOWER_AFFINE_HAND_DATA.json (the table that excludes
# tau_G at most -4/5, at the level Q1), research/eight at commit a21c91f: the arcs
# 10 (role H) and 66 (role G) and all the rows of the edge H -> G for this
# pair of arcs: (axis, half r, lo, hi, multiplier, support rule).
TABLE_Q = 3.915534138
TABLE_GAMMA = 0.8977
ARC_10 = dict(role='H', kind='O', sign=-1, lo=0.0, hi=1 / 8, c=0.23532111,
              p=0.0, q=-1.05377789)
ARC_66 = dict(role='G', kind='O', sign=-1, lo=7 / 8, hi=1.0, c=0.26581382,
              p=0.0, q=-0.91311208)
ROWS_10_66 = [(1, -1, 0.0, 0.02539817, 19.9999997, 'endpoints'),
              (2, -1, 0.0, 0.02539817, 19.9999997, 'endpoints'),
              (3, -1, 0.0, 0.02539817, 19.9999997, 'endpoints'),
              (4, -1, 0.0, 0.02539817, 19.9999997, 'endpoints'),
              (1, 1, 0.0, 0.7, 7.56987426, 'upper'),
              (2, 1, 0.0, 0.7, 19.9999997, 'endpoints'),
              (3, 1, 0.0, 0.0875, 19.99999943, 'lower'),
              (3, 1, 0.0875, 0.13125, 1.03778016, 'lower'),
              (3, 1, 0.13125, 0.175, 1.023, 'circle'),
              (3, 1, 0.175, 0.21875, 1.01256, 'circle'),
              (3, 1, 0.21875, 0.2625, 1.001, 'circle'),
              (3, 1, 0.2625, 0.30625, 0.98507418, 'upper'),
              (3, 1, 0.30625, 0.35, 0.91311208, 'upper'),
              (3, 1, 0.35, 0.7, 0.0, 'endpoints'),
              (4, 1, 0.0, 0.7, 1.19411839, 'endpoints')]


def arc_states(arc, n=60):
    out = []
    for j in range(n + 1):
        tg = arc['lo'] + (arc['hi'] - arc['lo']) * j / n
        a = outer_a(TABLE_Q, tg) if arc['kind'] == 'O' else core_a(tg)
        out.append((a, tg * a))
    return out


def arc_label(arc, a, b):
    return arc['c'] + arc['p'] * a + arc['q'] * b


def pair_width(phi):
    return 0.5 * (1 + abs(math.sin(phi)) + abs(math.cos(phi)))


def forward_margin(j, sg, tg, a, b, A, B, phi):
    """The margins of (11.5)."""
    s, c = math.sin(phi), math.cos(phi)
    W = pair_width(phi)
    return {1: sg * b + A * s - tg * B * c - W, 2: A - a * c + sg * b * s - W,
            3: a * s + sg * b * c - tg * B - W,
            4: a - A * c - tg * B * s - W}[j]


def row_value(row, u_, a, b, A, B):
    """The left side of (11.10) for the arcs 10 and 66 (beta = 0)."""
    axis, half, lo, hi, lam, mode = row
    phi = half * u_
    M = forward_margin(axis, ARC_10['sign'], ARC_66['sign'], a, b, A, B, phi)
    return (phi + arc_label(ARC_10, a, b) - arc_label(ARC_66, A, B)
            - TABLE_GAMMA - lam * M)


def row_figure():
    row = ROWS_10_66[4]
    axis, half, lo, hi, lam, mode = row
    S, T = arc_states(ARC_10, 40), arc_states(ARC_66, 40)
    us = [lo + (hi - lo) * j / 70 for j in range(71)]
    true_min, bound = [], []
    sg, tg = ARC_10['sign'], ARC_66['sign']
    for u_ in us:
        phi = half * u_
        true_min.append(min(row_value(row, u_, a, b, A, B) for a, b in S
                            for A, B in T))
        # Lemma L.2 for axis 1: constant plus source and target terms
        K = phi - TABLE_GAMMA + ARC_10['c'] - ARC_66['c'] + lam * pair_width(phi)
        Xs, Ys = ARC_10['p'], ARC_10['q'] - lam * sg
        Xt = -ARC_66['p'] - lam * math.sin(phi)
        Yt = -ARC_66['q'] + lam * tg * math.cos(phi)
        src = min(Xs * a + Ys * b for a, b in (S[0], S[-1]))
        # the upper-endpoint rule: Yt - Xt * rho <= 0 at both endpoints
        for A, B in (T[0], T[-1]):
            rho = (B + 0.5) / (A + 0.5)
            assert Yt - Xt * rho <= 0
        tgt = Xt * T[-1][0] + Yt * T[-1][1]
        bound.append(K + src + tgt)
    for v, w in zip(true_min, bound):
        assert w > 0 and w <= v + 1e-9
    assert min(true_min) > 0.05
    # left panel: the arcs on the radial curves; right panel: the graph
    f = Figure(0.3, 4.55, -0.22, 1.18, 190)
    q = TABLE_Q
    outer = [(outer_a(q, j / 80), j / 80 * outer_a(q, j / 80)) for j in range(81)]
    corner = [(core_a(tg_), tg_ * core_a(tg_))
              for tg_ in (6 / 7 + (1 / 7) * j / 30 for j in range(31))]
    f.polygon([(7 / 12, 0.0)] + outer + list(reversed(corner)), fill=FILLS[0],
              stroke='none')
    polyline(f, outer, stroke=FAINT, width=1.4)
    polyline(f, [(7 / 12, 0.0), (7 / 12, 0.5)] + corner, stroke=FAINT, width=1.4)
    polyline(f, S, stroke=PINK, width=5)
    polyline(f, T, stroke=YELLOW, width=5)
    f.text(add(S[len(S) // 2], (0.06, 0.07)), 'H', size=15, color=PINK)
    f.text(add(T[len(T) // 2], (0.08, 0.04)), 'G', size=15, color=YELLOW)
    plane_frame(f, 0.4, 1.55, 1.12, ((0.5, '½'), (1.0, '1')), ((0.5, '½'),))
    # the graph
    ymax = max(true_min) * 1.05
    ox, oy, kx = 2.05, 0.05, 3.3
    ky = 1.0 / ymax
    P = lambda x, y: (ox + kx * x, oy + ky * y)
    f.line(P(0, 0), P(0.74, 0), width=1, arrow=True)
    f.line(P(0, 0), P(0, ymax * 1.06), width=1, arrow=True)
    polyline(f, [P(x, y) for x, y in zip(us, true_min)], stroke=FILLS[0],
             width=7)
    polyline(f, [P(x, y) for x, y in zip(us, true_min)], stroke=BLUE, width=1.6)
    polyline(f, [P(x, y) for x, y in zip(us, bound)], stroke=INK, width=1.3,
             dash='5 4')
    for x, lab in ((0.0, '0'), (0.35, '0.35'), (0.7, '0.7')):
        f.line(P(x, 0), P(x, -0.012 / ky), width=1)
        f.text(shift(P(x, 0), (0, -0.09)), lab, size=12, italic=False)
    for y in (0.2, 0.4, 0.6, 0.8, 1.0):
        if y < ymax:
            f.line(P(0, y), shift(P(0, y), (-0.03, 0)), width=1)
            f.text(shift(P(0, y), (-0.06, 0)), f'{y:.1f}', size=12,
                   italic=False, anchor='end')
    umin = us[true_min.index(min(true_min))]
    f.dot(P(umin, min(true_min)), r=3)
    f.text(shift(P(umin, min(true_min)), (0.0, 0.12)),
           f'{min(true_min):.3f}', size=12, italic=False)
    f.text(shift(P(0.74, 0), (-0.02, 0.13)), it('u'), size=15, anchor='end')
    f.save('11-eight/row', 'One row of the table that excludes tau_G at most -4/5: '
           'the source and target arcs on the outer curve, and the least value '
           'of the row inequality over the two arcs against the angle, with the '
           'support bound below it')
    ROW_INFO[0] = (min(true_min), min(bound))


ROW_INFO = [None]


def chains():
    # the required range of phi for the pair, from the gap bounds and the
    # frame bound (Section L.6)
    al_s = (-math.atan(ARC_10['hi']), -math.atan(ARC_10['lo']))
    al_t = (-math.atan(ARC_66['hi']), -math.atan(ARC_66['lo']))
    lo_req = max(19 / 25 - al_s[1] + al_t[0], -0.7)
    hi_req = min(710 / 113 - 114 / 25 - al_s[0] + al_t[1], 0.7)
    assert abs(lo_req + 0.02539817) < 1e-7 and hi_req == 0.7
    f = Figure(-0.42, 2.42, 0.16, 1.2, 290)
    X = lambda phi: (phi - lo_req) / (hi_req - lo_req) * 2.2
    for axis in (1, 2, 3, 4):
        yv = 1.02 - 0.2 * (axis - 1)
        f.polygon([(X(lo_req), yv - 0.075), (X(hi_req), yv - 0.075),
                   (X(hi_req), yv + 0.075), (X(lo_req), yv + 0.075)],
                  fill=GREY, stroke='none')
        ivs = sorted((min(h * a, h * b), max(h * a, h * b), mode)
                     for (ax, h, a, b, lam, mode) in ROWS_10_66 if ax == axis)
        # a closed chain covering the required range, endpoints shared
        assert abs(ivs[0][0] - lo_req) < 1e-7 and abs(ivs[-1][1] - hi_req) < 1e-9
        for (a0, a1, _), (b0, b1, _) in zip(ivs, ivs[1:]):
            assert abs(a1 - b0) < 1e-12
        for j, (a0, a1, mode) in enumerate(ivs):
            col = FILLS[0] if j % 2 == 0 else FILLS[1]
            f.polygon([(X(a0), yv - 0.05), (X(a1), yv - 0.05),
                       (X(a1), yv + 0.05), (X(a0), yv + 0.05)], fill=col,
                      stroke=INK, width=1)
            if X(a1) - X(a0) > 0.14:
                f.text(((X(a0) + X(a1)) / 2, yv), mode, size=11,
                       italic=False, color=INK)
            elif X(a1) - X(a0) > 0.05:
                f.text(((X(a0) + X(a1)) / 2, yv), mode[0], size=11,
                       italic=False, color=INK)
        f.text((-0.06, yv), str(axis), size=14, italic=False, anchor='end')
    f.text((-0.06, 1.15), 'margin', size=12, italic=False, anchor='end')
    yax = 0.3
    f.line((X(lo_req), yax), (X(hi_req) + 0.08, yax), width=1, arrow=True)
    for phi, lab, anchor in ((lo_req, '−0.0254', 'end'), (0.0, '0', 'start'),
                             (0.35, '0.35', 'middle'), (0.7, '0.7', 'middle')):
        f.line((X(phi), yax), (X(phi), yax - 0.03), width=1)
        dx = -0.01 if anchor == 'end' else (0.01 if anchor == 'start' else 0)
        f.text((X(phi) + dx, yax - 0.08), lab, size=12, italic=False,
               anchor=anchor)
    f.text((X(hi_req) + 0.1, yax + 0.05), it('φ'), size=15, anchor='start')
    f.save('11-eight/chains', 'The angle chains of one pair of arcs in the table '
           'that excludes tau_G at most -4/5: for each of the four margins the closed '
           'angle intervals of the rows meet at common endpoints and cover the '
           'required range')


# ------------------------------------------------------------ the mismatch

def mismatch():
    from fractions import Fraction as Fr
    # the exact comparisons of Proposition 11.34
    pi_up = Fr(710, 113)
    assert 7 * Fr(89727, 100000) + Fr(99, 5000) * Fr(29, 100) * Fr(2, 5) - pi_up \
        == Fr(271, 282500000)

    def P7(x):
        return (x / 2 - x ** 2 / 4 - x ** 3 / 12 + x ** 4 / 48 + x ** 5 / 240
                - x ** 6 / 1440 - x ** 7 / 10080)
    assert 7 * Fr(89727, 100000) + Fr(51, 500000) + Fr(99, 5000) * P7(Fr(13, 50)) \
        - pi_up == Fr(9154605884982919, 494375000000000000000)
    cubic = lambda x: x / 2 - x ** 2 / 4 - x ** 3 / 12
    assert 7 * Fr(897582, 10 ** 6) + Fr(1, 400) * cubic(Fr(1, 10)) - pi_up \
        == Fr(18173, 2712000000)
    g_int, g_fin = Fr(238191, 32000000), Fr(5996999, 12000000000)
    two_pi = Fr(628318531, 10 ** 8)
    assert Fr(125662969, 20000000) + Fr(1, 200) * g_int - two_pi \
        == Fr(2287, 6400000000)
    assert Fr(502653, 80000) + Fr(1, 20) * g_fin - two_pi \
        == Fr(522599, 240000000000)
    assert gfun(0.015) > float(g_int) and gfun(0.001) > float(g_fin)
    assert P7(0.26) <= gfun(0.26) and gfun(0.7) > 0.29 * 0.7
    gam_int = [Fr(8975928, 10 ** 7)] * 5 + [Fr(89759275, 10 ** 8),
                                            Fr(8975917, 10 ** 7)]
    gam_fin = [Fr(897595, 10 ** 6)] * 6 + [Fr(8975925, 10 ** 7)]
    assert sum(gam_int) == Fr(125662969, 20000000)
    assert sum(gam_fin) == Fr(502653, 80000)
    # the curves: the charge term divided by the deficit of the constants
    steps = [('coarse', float(pi_up - 7 * Fr(89727, 100000)), 99 / 5000,
              lambda d: 0.29 * d, 0.4, ORANGE, '2/5'),
             ('raised', float(pi_up - 7 * Fr(89727, 100000) - Fr(51, 500000)),
              99 / 5000, gfun, 13 / 50, ORANGE, '13/50'),
             ('M1', float(pi_up - 7 * Fr(897582, 10 ** 6)), 1 / 400, gfun, 0.1,
              BLUE, '1/10'),
             ('int', float(two_pi - sum(gam_int)), 1 / 200, gfun, 0.015, GREEN,
              '3/200'),
             ('M2', float(two_pi - sum(gam_fin)), 1 / 20, gfun, 0.001, PURPLE,
              '1/1000')]
    ox, oy, kx, ky = 0.75, 0.55, 1.45, 1.6
    lx = lambda d: ox + kx * (math.log10(d) + 4)
    P = lambda d, r: (lx(d), oy + ky * r)
    f = Figure(0.0, 7.15, 0.0, 4.2, 112)
    f.line(P(1e-4, 0), P(1.4, 0), width=1, arrow=True)
    f.line(P(1e-4, 0), P(1e-4, 2.2), width=1, arrow=True)
    f.line(P(1e-4, 1), P(1.0, 1), stroke=INK, width=1, dash='5 3')
    for e in range(-4, 1):
        d = 10.0 ** e
        f.line(P(d, 0), P(d, -0.04), width=1)
        lab = '1' if e == 0 else '10' + '<tspan dy="-6" font-size="9">' + \
            f'{e}'.replace('-', '−') + '</tspan>'
        f.text(shift(P(d, 0), (0, -0.2)), lab, size=12, italic=False)
    for r in (0.5, 1.0, 1.5, 2.0):
        f.line(P(1e-4, r), shift(P(1e-4, r), (-0.05, 0)), width=1)
        f.text(shift(P(1e-4, r), (-0.09, 0)), f'{r:.1f}', size=12,
               italic=False, anchor='end')
    for name, deficit, beta, lower, thr, col, lab in steps:
        assert deficit > 0
        ds = [10 ** (-4 + 4 * j / 200) for j in range(201)]
        pts = [P(d, beta * lower(d) / deficit) for d in ds
               if d <= (0.7 if lower is gfun else 1.0)
               and beta * lower(d) / deficit <= 2.15]
        polyline(f, pts, stroke=col, width=1.8,
                 dash='4 3' if name == 'coarse' else None)
        rt = beta * lower(thr) / deficit
        assert rt > 1
        f.dot(P(thr, rt), r=3.6, fill=col)
        dx = 0.1 if name == 'coarse' else -0.1
        f.text(shift(P(thr, rt), (dx, 0.16 if name != 'coarse' else -0.18)),
               lab, size=12, italic=False, color=col,
               anchor='start' if name == 'coarse' else 'end')
    f.text(P(1.25, 0.07), 'Δ', size=15, anchor='end')
    f.text(shift(P(1e-4, 2.2), (0.08, -0.05)), 'charge ÷ deficit', size=12,
           italic=False, anchor='start')
    f.save('11-eight/mismatch', 'The four contraction steps of the mismatch chain: '
           'for each, the charge term beta times g of the mismatch divided by the '
           'deficit of its constants, against the mismatch on a logarithmic axis; '
           'each passes 1 below its threshold, marked by a dot')


# ------------------------------------------------------------ owners, tilt

OWNERS = {'H': {1, 3}, 'G': {1}, 'A': {1, 3}, 'B': {3, 4}, 'T': {1, 3},
          'D': {3, 4}, 'E': {2}}


def owners():
    M = model(*BOX)
    m = R8 + 0.12
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    ext = {k: v for k, v in M.items() if k != 'K'}
    draw_model(f, ext, labels=False)
    segs, points = contact_features(M)
    mids = [mul(0.5, add(p, q)) for p, q in segs]
    contact = {'A': mids[0], 'B': mids[1], 'T': mids[2], 'D': mids[3],
               'H': mids[4], 'E': points[0], 'G': points[1]}
    for i in CYCLE:
        j = CYCLE[(CYCLE.index(i) + 1) % 7]
        mg = margins_of(M[i], M[j])
        zero = {a for a in (1, 2, 3, 4) if abs(mg[a]) < 1e-9}
        assert zero == OWNERS[i], (i, mg)
        assert all(mg[a] < -1e-6 for a in (1, 2, 3, 4) if a not in zero)
        n = witness_normal(i)
        c = contact[i]
        t = (-n[1], n[0])
        f.line(add(c, mul(-0.62, t)), add(c, mul(0.62, t)), stroke=INK,
               width=1.3, dash='5 3')
        lab = '{' + ', '.join(str(a) for a in sorted(OWNERS[i])) + '}'
        toward = mul(-1 / norm(c), c)
        halo_text(f, add(c, mul(0.34, toward)), lab, size=14)
    for k, sq in ext.items():
        f.text(sq[0], k, size=17, color=ROLE_COLOR[k])
    origin(f, dx=0.05, dy=-0.1)
    f.save('11-eight/owners', 'The separating lines of the seven contacts of the '
           'optimal packing, each edge labelled with its owner set of retained '
           'axes')


def tilt():
    zs = math.tan(TSTAR / 2)
    a, b = 1001 / 20000, 2 / 25
    assert a < zs < b
    assert 2 * (a - a ** 3 / 3) > 1 / 10 and 2 * math.atan(b) < 4 / 25
    assert 1 / 10 < TSTAR < 4 / 25 and math.atan(3 / 8) * 2 > 0.7
    f = Figure(-0.42, 0.42, -0.155, 0.14, 1000)
    y0 = 0.08
    f.line((-0.39, y0), (0.4, y0), width=1, arrow=True)
    for lo, hi in ((-3 / 8, a), (b, 3 / 8)):
        f.polygon([(lo, y0 - 0.012), (hi, y0 - 0.012), (hi, y0 + 0.012),
                   (lo, y0 + 0.012)], fill=RED_FILL, stroke=RED, width=1)
    for z, lab in ((-3 / 8, '−3/8'), (0.0, '0'), (3 / 8, '3/8')):
        f.line((z, y0 - 0.02), (z, y0 + 0.02), width=1)
        f.text((z, y0 + 0.04), lab, size=12, italic=False)
    f.text((0.405, y0 + 0.02), it('z'), size=15, anchor='start')
    # the enlargement of the window
    k = 8.0
    cz = (a + b) / 2
    Xz = lambda z: (z - cz) * k
    y1 = -0.09
    f.line((Xz(a) - 0.06, y1), (Xz(b) + 0.06, y1), width=1)
    f.polygon([(Xz(a) - 0.06, y1 - 0.012), (Xz(a), y1 - 0.012),
               (Xz(a), y1 + 0.012), (Xz(a) - 0.06, y1 + 0.012)], fill=RED_FILL,
              stroke=RED, width=1)
    f.polygon([(Xz(b), y1 - 0.012), (Xz(b) + 0.06, y1 - 0.012),
               (Xz(b) + 0.06, y1 + 0.012), (Xz(b), y1 + 0.012)], fill=RED_FILL,
              stroke=RED, width=1)
    f.line((a, y0 - 0.012), (Xz(a), y1 + 0.012), stroke=FAINT, width=0.8,
           dash='2 2')
    f.line((b, y0 - 0.012), (Xz(b), y1 + 0.012), stroke=FAINT, width=0.8,
           dash='2 2')
    f.dot((Xz(zs), y1), r=4, fill=INK)
    f.text((Xz(zs), y1 + 0.035), sb(it('z'), '*', NB + '≈' + NB + '0.0619', 13),
           size=13, italic=False)
    for z, lab in ((a, '1001/20000'), (b, '2/25')):
        f.text((Xz(z), y1 - 0.045), lab, size=12, italic=False)
    f.save('11-eight/tilt', 'The tilt window: the half-angle tangent z on '
           '[-3/8, 3/8] with the two excluded intervals shaded, and the window '
           'between them enlarged, containing z*')


def stationary_weights(ch):
    c, s = ch['c'], ch['s']
    y, x1, x2, x3, y3, x4, h1, h2 = (ch[k] for k in ('y', 'x1', 'x2', 'x3',
                                                      'y3', 'x4', 'h1', 'h2'))
    muA = c / (2 * x1)
    al = s - c * y / x1
    muB = al / (2 * (y + 2))
    be = al * x2 / (y + 2)
    muD = -be / (2 * x3)
    de = 2 * muD * y3
    muH = -1 / (2 * h1)
    ep = h2 / h1
    muE = -s * ep / (2 * x4)
    om = 1 / (muA + muB + muD + muE + muH)
    mu = {'A': muA * om, 'B': muB * om, 'D': muD * om, 'E': muE * om,
          'H': muH * om}
    lam = {'AB': al * om, 'TB': be * om, 'DT': be * om, 'ED': de * om,
           'HE': ep * om, 'GA': om, 'HG': om}
    return mu, lam


def stress():
    mu, lam = stationary_weights(ROOT)
    assert all(v > 0 for v in mu.values()) and all(v > 0 for v in lam.values())
    assert abs(sum(mu.values()) - 1) < 1e-12
    PP = dict(zip('ABDEH', ROOT['P']))
    e0, f0 = (1.0, 0.0), (0.0, 1.0)
    # the force identities (J.2) and the barycentre
    rhs = {'A': sub(mul(lam['GA'], E_T), mul(lam['AB'], f0)),
           'B': add(mul(lam['TB'], e0), mul(lam['AB'], f0)),
           'D': add(mul(-lam['DT'], e0), mul(lam['ED'], f0)),
           'E': sub(mul(lam['HE'], F_T), mul(lam['ED'], f0)),
           'H': sub(mul(-lam['GA'], E_T), mul(lam['HE'], F_T))}
    for k in 'ABDEH':
        assert norm(sub(mul(2 * mu[k], PP[k]), rhs[k])) < 1e-8
    bary = (sum(mu[k] * PP[k][0] for k in mu), sum(mu[k] * PP[k][1] for k in mu))
    assert norm(bary) < 1e-8
    assert max(lam.values()) < 4209 / 5000
    M = model(*BOX)
    m = R8 + 0.5
    f = Figure(-m, m, -m, m, 140)
    f.circle((0, 0), R8, stroke=INK, width=1.1, dash='6 4')
    ext = {k: v for k, v in M.items() if k != 'K'}
    draw_model(f, ext, labels=False)
    pairs = [('A', 'B', 'AB'), ('T', 'B', 'TB'), ('D', 'T', 'DT'),
             ('E', 'D', 'ED'), ('H', 'E', 'HE'), ('G', 'A', 'GA'),
             ('H', 'G', 'HG')]
    for a, b, key in pairs:
        p, q = M[a][0], M[b][0]
        f.line(p, q, stroke=INK, width=1.2)
        mid = mul(0.5, add(p, q))
        nrm = mul(1 / norm(sub(q, p)), (-(q[1] - p[1]), q[0] - p[0]))
        f.text(add(mid, mul(0.13, nrm)), f'{lam[key]:.2f}', size=12,
               italic=False)
    for k in 'ABDEH':
        P = PP[k]
        tip = add(P, mul(0.75 * 2 * mu[k], P))
        arrow(f, P, tip, color=ROLE_COLOR[k], width=3)
        off = {'A': (-0.12, -0.17), 'B': (-0.1, 0.12)}.get(k, mul(0.16 / norm(P), P))
        f.text(add(tip, off),
               sb(it('μ'), it(k), f'{NB}={NB}{mu[k]:.3f}', 12),
               size=12, italic=False, color=ROLE_COLOR[k])
    for k, sq in ext.items():
        f.dot(sq[0], r=2.2)
        f.text(add(sq[0], (0.16, 0.16)), k, size=15, color=ROLE_COLOR[k])
    origin(f, dx=0.05, dy=-0.1)
    f.save('11-eight/stress', 'The stationary weights of the optimal packing: the '
           'seven contacts with their weights and the five corner forces pointing '
           'outward along the radii, with the weights mu')


def main():
    eight()
    family()
    chain_figure()
    sliders()
    section()
    measure()
    core_figure()
    radial()
    reduction()
    expansion()
    common_point()
    axes_figure()
    walks()
    frames_figure()
    words()
    tangents()
    row_figure()
    chains()
    mismatch()
    owners()
    tilt()
    stress()


if __name__ == '__main__':
    main()

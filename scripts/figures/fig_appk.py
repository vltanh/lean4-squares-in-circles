#!/usr/bin/env python3
"""Draw the figures of Appendix K (eight squares: the central core) as SVG
files in docs/proof/figures/appendix-k/.

    python3 scripts/figures/fig_appk.py

The arcs of the circles about o in a square are computed exactly, from the
crossings of each circle with the sides; the polynomials of Lemma K.4, their
completed square and their tangent parabola in exact rational arithmetic; the
blocked directions of Lemma K.5 from their definition. Each drawing asserts
the facts its caption states.
"""
import math
from fractions import Fraction as Fr

from proof_figures import Figure, Graph, INK, FAINT, COLORS, FILLS, GREY, sb, u
from fig_front import it, NB, RED, RED_FILL, polyline
from fig_appj import halo_text, core_disk, origin, add, mul, sub, dot, norm

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN, YELLOW = COLORS
Q = 98 / 25                      # the disk of Section K.1
Q0 = 9789 / 2500
Q0F = Fr(9789, 2500)
LAM, KAP = 11 / 12, 7 / 20       # the segment V
R0 = math.sqrt(LAM ** 2 + KAP ** 2)
PHI0 = math.atan(KAP / LAM)


def shift_pt(p, v):
    return (p[0] + v[0], p[1] + v[1])


# ------------------------------------------------ arcs of circles in a square

def rect_arcs(r, x0, x1, y0, y1):
    """The arcs of the circle of radius r about o in the closed rectangle
    [x0, x1] x [y0, y1], as counterclockwise angle intervals, and their total
    length, from the crossings of the circle with the four sides."""
    eps = 1e-13

    def inside(t):
        x, y = r * math.cos(t), r * math.sin(t)
        return x0 - eps <= x <= x1 + eps and y0 - eps <= y <= y1 + eps
    ts = []
    for xv in (x0, x1):
        if abs(xv) <= r:
            a = math.acos(xv / r)
            ts += [a, -a]
    for yv in (y0, y1):
        if abs(yv) <= r:
            a = math.asin(yv / r)
            ts += [a, PI - a]
    ts = sorted({t % (2 * PI) for t in ts if inside(t)})
    if not ts:
        return ([(0.0, 2 * PI)], 2 * PI) if inside(0.0) else ([], 0.0)
    arcs = []
    for i, t in enumerate(ts):
        t1 = ts[i + 1] if i + 1 < len(ts) else ts[0] + 2 * PI
        if t1 - t > 1e-12 and inside((t + t1) / 2):
            arcs.append((t, t1))
    return arcs, sum(b - a for a, b in arcs)


def weighted(x, y):
    """3 L_1 + L_{5/4} of the canonical square [x, x + 1] x [y, y + 1]."""
    L1 = rect_arcs(1.0, x, x + 1, y, y + 1)[1]
    L2 = rect_arcs(1.25, x, x + 1, y, y + 1)[1]
    return 3 * L1 + L2, L1, L2


def canonical_ok(x, y):
    return x >= 0 and -0.5 <= y <= x and (x + 1) ** 2 + (y + 1) ** 2 <= Q


def regions():
    cases = [((0.1, -0.5), it('x') + ' &lt; ¼, ' + it('y') + ' = −½'),
             ((0.4, -0.25), it('x') + ' ≥ ¼, ' + it('y') + ' &lt; 0'),
             ((0.35, 0.2), it('x') + ' ≥ ¼, ' + it('y') + ' ≥ 0')]
    W = 3.1
    f = Figure(-1.4, -1.4 + 3 * W, -1.75, 1.42, 88)
    for k, ((x, y), name) in enumerate(cases):
        assert canonical_ok(x, y)
        v, L1, L2 = weighted(x, y)
        if k == 0:
            assert abs(L1 - PI / 3) < 1e-12 and L2 == 0
            assert (x + 1) ** 2 + 0.25 <= 25 / 16
        else:
            assert x >= 0.25 and v > PI + 0.3
        at = (k * W, 0.0)
        P = lambda p: shift_pt(at, p)
        f.circle(P((0, 0)), 1.0, stroke=FAINT, width=1)
        f.circle(P((0, 0)), 1.25, stroke=FAINT, width=1, dash='4 3')
        f.polygon([P(c) for c in ((x, y), (x + 1, y), (x + 1, y + 1),
                                  (x, y + 1))],
                  fill=FILLS[0], stroke=BLUE, width=1.4)
        for r, col in ((1.0, BLUE), (1.25, ORANGE)):
            for t0, t1 in rect_arcs(r, x, x + 1, y, y + 1)[0]:
                f.arc(P((0, 0)), r, t0, t1, col, width=4)
        f.dot(P((0, 0)), r=2.4)
        f.text(P((-0.07, -0.12)), 'o', size=13, anchor='end')
        f.text(P((0.25, -1.48)), name, size=12, italic=False)
        L1s = 'π/3' if k == 0 else f'{L1:.3f}'
        L2s = '0' if L2 == 0 else f'{L2:.3f}'
        f.text(P((0.25, -1.7)),
               sb(it('L'), '1', NB + '=' + NB + L1s + ',' + NB + NB, 12)
               + sb(it('L'), '5/4', NB + '=' + NB + L2s, 12), size=12,
               italic=False)
    f.text((-1.02, 0.86), sb('Γ', '1', size=13), size=13, italic=False,
           color=FAINT)
    f.text((-1.12, 1.16), sb('Γ', '5/4', size=13), size=13, italic=False,
           color=FAINT)
    f.save('appendix-k/regions', 'Three canonical squares with the unit circle '
           'and the circle of radius 5/4 about o and their arcs in the square: '
           'an equality square straddling the axis, and squares of the two '
           'regions with x at least 1/4')


BANDS = ['#eff6ff', '#dbeafe', '#bfdbfe', '#93c5fd', '#60a5fa', '#3b82f6',
         '#2563eb', '#1d4ed8', '#1e40af', '#1e3a8a']


def weighted_figure():
    b0 = math.sqrt(Q - 0.25) - 1
    xe = (math.sqrt(21) - 4) / 4
    ytop = math.sqrt(Q / 2) - 1
    nx, ny = 150, 150
    x_lo, x_hi, y_lo, y_hi = 0.0, b0, -0.5, ytop
    dx, dy = (x_hi - x_lo) / nx, (y_hi - y_lo) / ny
    vmax = 0.0
    rows = []
    for j in range(ny):
        yc = y_lo + (j + 0.5) * dy
        runs, cur = [], None
        for i in range(nx):
            xc = x_lo + (i + 0.5) * dx
            band = None
            if canonical_ok(xc, yc):
                v = weighted(xc, yc)[0]
                assert v > PI
                vmax = max(vmax, v)
                band = min(int((v - PI) / 0.25), len(BANDS) - 1)
            if cur and cur[2] == band:
                cur[1] = i + 1
            else:
                if cur and cur[2] is not None:
                    runs.append(tuple(cur))
                cur = [i, i + 1, band]
        if cur and cur[2] is not None:
            runs.append(tuple(cur))
        rows.append(runs)
    assert vmax < PI + 0.25 * len(BANDS)
    # on the bottom edge: pi exactly up to xe, more after
    for i in range(201):
        x = b0 * i / 200
        v = weighted(x, -0.5)[0]
        if x <= xe - 1e-9:
            assert abs(v - PI) < 1e-12
        elif x >= xe + 1e-6:
            assert v > PI + 1e-9
    sc = 525
    f = Figure(-0.12, 1.42, -0.62, 0.5, sc)
    for j, runs in enumerate(rows):
        y0 = y_lo + j * dy
        for i0, i1, band in runs:
            x0, x1 = x_lo + i0 * dx, x_lo + i1 * dx
            f.polygon([(x0, y0), (x1, y0), (x1, y0 + dy), (x0, y0 + dy)],
                      fill=BANDS[band], stroke=BANDS[band], width=0.6)
    # the boundary of the region (K.1)
    arc = [(math.sqrt(Q - (1 + yy) ** 2) - 1, yy)
           for yy in (-0.5 + (ytop + 0.5) * k / 60 for k in range(61))]
    outline = [(0.0, -0.5)] + arc + [(0.0, 0.0)]
    f.polygon(outline, stroke=INK, width=1.2)
    f.line((xe * 0, -0.5), (xe, -0.5), stroke=RED, width=4)
    f.line((0.25, -0.5), (0.25, 0.25), stroke=INK, width=1.1, dash='5 3')
    # axes
    f.line((-0.03, -0.5), (1.0, -0.5), width=1, arrow=True)
    f.line((0.0, -0.53), (0.0, 0.47), width=1, arrow=True)
    for x, lab in ((0.25, '¼'), (0.5, '½'), (0.75, '¾')):
        f.line((x, -0.5), (x, -0.515), width=1)
        f.text((x, -0.545), lab, size=12, italic=False)
    f.text((xe, -0.545), '(√21 − 4)/4', size=11, italic=False, color=RED)
    for y, lab in ((-0.5, '−½'), (0.0, '0'), (0.25, '¼')):
        f.line((0.0, y), (-0.015, y), width=1)
        f.text((-0.025, y), lab, size=12, italic=False, anchor='end')
    f.text((1.0, -0.47), it('x'), size=15, anchor='end')
    f.text((0.02, 0.46), it('y'), size=15, anchor='start')
    f.text((0.27, 0.32), it('y') + NB + '=' + NB + it('x'), size=12,
           italic=False, anchor='end', color=INK)
    f.text((0.86, 0.14), '(' + it('x') + NB + '+' + NB + '1)²' + NB + '+' + NB
           + '(' + it('y') + NB + '+' + NB + '1)²' + NB + '=' + NB + '98/25',
           size=12, italic=False, anchor='start')
    # legend
    lx, ly = 1.08, -0.5
    for k in range(len(BANDS)):
        y0 = ly + k * 0.07
        f.polygon([(lx, y0), (lx + 0.06, y0), (lx + 0.06, y0 + 0.07),
                   (lx, y0 + 0.07)], fill=BANDS[k], stroke=FAINT, width=0.6)
        lab = 'π' if k == 0 else f'π + {0.25 * k:g}'
        f.text((lx + 0.08, y0), lab, size=11, italic=False, anchor='start')
    f.text((lx + 0.08, ly + len(BANDS) * 0.07), 'π + 2.5', size=11,
           italic=False, anchor='start')
    f.text((lx, ly + len(BANDS) * 0.07 + 0.06), '3' + sb(it('L'), '1', NB + '+'
           + NB, 12) + sb(it('L'), '5/4', size=12), size=12, italic=False,
           anchor='start')
    f.save('appendix-k/weighted', 'The value of 3 L1 + L5/4 over the canonical '
           'positions, in bands of width 0.25 above pi; it equals pi only on '
           'the thick segment of the bottom edge')
    WEIGHTED_INFO[0] = vmax


WEIGHTED_INFO = [None]


# --------------------------------------------- the polynomials of Lemma K.4

def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def pscale(k, a):
    return [k * x for x in a]


def peval(a, x):
    out = 0
    for c in reversed(a):
        out = out * x + c
    return out


def band_polys(A0, Cm, Cp, Dd):
    """P and V of Lemma K.4 as coefficient lists in u."""
    z = [Fr(1), Fr(0), Fr(1)]
    c = [Fr(1), Fr(0), Fr(-1)]
    s = [Fr(0), Fr(2)]
    H = padd(padd(pscale(Fr(1, 2), z), pscale(Cm, c)), pscale(-Dd, s))
    P = padd(padd(pmul(pmul(H, H), z), pmul(pmul(H, c), padd(c, s))),
             pscale(Fr(1, 2) - Q0F, pmul(pmul(c, c), z)))
    V = padd(padd(pscale(Fr(1, 2), pmul(c, z)), pscale(A0, pmul(s, z))),
             padd(pscale(-Cp, pmul(s, c)), pscale(-Dd, pmul(c, c))))
    while P and P[-1] == 0:
        P.pop()
    while V and V[-1] == 0:
        V.pop()
    return P, V


SEGMENT = (Fr(1, 2), Fr(11, 12), Fr(11, 12), Fr(7, 20))
LAMBDA_A = Fr(10007, 10000)
BAND_A = (Fr(5007, 10000), LAMBDA_A * Fr('0.9308368'),
          LAMBDA_A * Fr('0.9308369'), LAMBDA_A * Fr('0.365435'))
LAMBDA_B = Fr(41, 40)
BAND_B = (Fr(107, 200), LAMBDA_B * Fr('0.9286'), LAMBDA_B * Fr('0.9287'),
          LAMBDA_B * Fr('0.371'))


def pderiv(a):
    return [k * a[k] for k in range(1, len(a))]


def remainder_form(P, u0):
    """c0, b and the coefficients of R with P = c0 + b (u - u0) + R (u - u0)^2,
    from the expansion of P about u0."""
    Q = [Fr(0)]
    for coeff in reversed(P):            # P(u0 + v) as a polynomial in v
        Q = padd(pmul(Q, [u0, Fr(1)]), [coeff])
    R = Q[2:]                            # R(u0 + v) in v
    Ru = [Fr(0)]
    for coeff in reversed(R):            # back to the variable u
        Ru = padd(pmul(Ru, [-u0, Fr(1)]), [coeff])
    return Q[0], Q[1], Ru


# The rational forms of the sextics: the segment, and the bands with the
# rational constants (C-, D) that bound those of Table K.1.
SEXTICS = [('segment', SEGMENT[1], SEGMENT[3], Fr(2, 5), Fr(1, 200),
            Fr(1009541, 156250000), -Fr(11807, 11718750),
            [Fr(80651), Fr(5361332), Fr(5659640), Fr(24865400),
             Fr(41159875)], Fr(11250000)),
           ('band A', Fr(23287, 25000), Fr(3657, 10000), Fr(7, 15),
            Fr(8, 25), Fr(1127543919953, 3559570312500000),
            Fr(304816277161, 26367187500000),
            [Fr(2036745397849), Fr(1029147845214), Fr(8456151284640),
             Fr(16795576114200), Fr(23166664513875)], Fr(6328125000000)),
           ('band B', Fr(4759, 5000), Fr(3803, 10000), Fr(1, 2), Fr(11, 25),
            Fr(1608241, 320000000), -Fr(21358779, 400000000),
            [Fr(179518421), Fr(38557484), Fr(660186260), Fr(1133199440),
             Fr(1465310704)], Fr(400000000))]


def check_sextics():
    """The identities and the reserves of the sextics of Section K.3, and the
    monotone comparison with the constants of Table K.1."""
    one = [Fr(1)]
    for name, Cm, Dd, u0, a, c0, b, Rc, Rd in SEXTICS:
        P = band_polys(Fr(0), Cm, Fr(0), Dd)[0]
        # R(u) = (r0 + r1 u + r2 u(1 - u) + r3 u^2(1 - u) + r4 u^2(1 - u^2))/Rd
        R = padd(padd(padd([Rc[0]], [Fr(0), Rc[1]]),
                      pscale(Rc[2], [Fr(0), Fr(1), Fr(-1)])),
                 padd(pscale(Rc[3], [Fr(0), Fr(0), Fr(1), Fr(-1)]),
                      pscale(Rc[4], [Fr(0), Fr(0), Fr(1), Fr(0), Fr(-1)])))
        R = pscale(1 / Rd, R)
        c0x, bx, Rx = remainder_form(P, u0)
        assert (c0x, bx) == (c0, b)
        assert padd(Rx, pscale(-1, R)) == [0] * max(len(Rx), len(R))
        assert Rc[0] / Rd >= a > 0 and all(r >= 0 for r in Rc)
        assert b * b < 4 * a * c0
    # Table K.1 constants: larger C-, smaller D than the rational forms
    for (name, Cm, Dd, *_), band in zip(SEXTICS[1:], (BAND_A, BAND_B)):
        assert band[1] >= Cm and band[3] <= Dd < Fr(1, 2)
        P0 = band_polys(Fr(0), Cm, Fr(0), Dd)[0]
        P1 = band_polys(Fr(0), band[1], Fr(0), band[3])[0]
        for i in range(201):
            x = Fr(i, 200)
            assert peval(P1, x) >= peval(P0, x) > 0


def check_quartics():
    """V'' >= 7/5 on [0, 3/7] and V'(1/4)^2 < 2 (7/5) V(1/4), for the three
    cases."""
    out = []
    for A0, Cm, Cp, Dd in (SEGMENT, BAND_A, BAND_B):
        V = band_polys(A0, Cm, Cp, Dd)[1]
        V1, V2 = pderiv(V), pderiv(pderiv(V))
        assert V2 == [4 * Dd, 12 * (A0 + Cp), -12 * (Fr(1, 2) + Dd)]
        for i in range(301):
            x = Fr(3, 7) * i / 300
            assert peval(V2, x) >= Fr(7, 5)
        t0 = Fr(1, 4)
        assert peval(V1, t0) ** 2 < 2 * Fr(7, 5) * peval(V, t0)
        out.append((V, V1))
    return out


def polys():
    check_sextics()
    (V, V1), _, _ = check_quartics()
    name, Cm, Dd, u0, a, c0, b, *_ = SEXTICS[0]
    P = band_polys(*SEGMENT)[0]
    para = lambda x: c0 + b * (x - u0) + a * (x - u0) ** 2
    t0 = Fr(1, 4)
    tang = lambda x: (peval(V, t0) + peval(V1, t0) * (x - t0)
                      + Fr(7, 10) * (x - t0) ** 2)
    for i in range(401):
        x = Fr(i, 400)
        assert peval(P, x) >= para(x) > 0
        y = Fr(3, 7) * i / 400
        assert peval(V, y) >= tang(y) > 0
    f = Figure(-0.25, 8.1, -0.45, 3.1, 100)
    gP = Graph(f, 3.0, 2.6 / 0.032, dx=0.75, dy=0.15)
    gV = Graph(f, 2.8 / (3 / 7), 2.6 / 0.16, dx=4.85, dy=0.15)
    for g, top, poly, low, ymax, ticks, yt, name in (
            (gP, 1.0, P, para, 0.032,
             [(0, '0'), (0.25, '¼'), (0.4, '⅖'), (0.5, '½'), (0.75, '¾'),
              (1, '1')], [(0.01, '0.01'), (0.02, '0.02'), (0.03, '0.03')],
             it('P')),
            (gV, 3 / 7, V, tang, 0.16,
             [(0, '0'), (0.125, '⅛'), (0.25, '¼'), (3 / 7, '3/7')],
             [(0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')], it('V'))):
        g.x_axis(0, top * 1.08, ticks=ticks, label=it('u'))
        g.y_axis(0, ymax, ticks=yt)
        for fn, kw in ((lambda x: float(peval(poly, Fr(x))),
                        dict(stroke=BLUE, width=2.2)),
                       (lambda x: float(low(Fr(x))),
                        dict(stroke=ORANGE, width=1.8, dash='6 4'))):
            # the part of the graph below the top of the frame
            pts = [(top * k / 400, fn(top * k / 400)) for k in range(401)]
            run = []
            for q in pts + [(None, None)]:
                if q[1] is not None and q[1] <= ymax:
                    run.append(q)
                elif run:
                    g.polyline(run, **kw)
                    run = []
        g.text((top * (0.12 if poly is P else 0.5), ymax * 0.97), name, size=16,
               italic=False)
    assert peval(P, Fr(1)) > Fr(17, 100)
    gP.text((0.93, 0.0285), it('P') + '(1)' + NB + '≈' + NB + '0.18',
            size=12, italic=False, anchor='end')
    gP.dot((0.4, float(para(Fr(2, 5)))), r=2.6, fill=ORANGE)
    gV.dot((0.25, float(peval(V, t0))), r=2.6, fill=ORANGE)
    f.save('appendix-k/polys', 'The sextic P and the quartic V of the segment '
           'case of Lemma K.4, each above a positive parabola: the completed '
           'square of P about 2/5 and the tangent parabola of V at 1/4 with '
           'curvature 7/5')


# ---------------------------------------------------------- the segment V

def rho(theta, q=Q0):
    B = math.cos(theta) + math.sin(theta)
    return (-B + math.sqrt(B * B - 4 * (0.5 - q))) / 2


def state_square_at(r, alpha, sign=1):
    """The square with centre (r, 0) whose frame is turned by sign * alpha,
    so that the centre is (a, -b) or (a, b) in its frame."""
    t = sign * alpha
    e, fv = u(t), u(t + PI / 2)
    c = (r, 0.0)
    corners = [add(c, add(mul(sx, e), mul(sy, fv)))
               for sx, sy in ((0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5),
                              (0.5, -0.5))]
    return c, e, fv, corners


def contains_V(r, alpha, sign=1, n=60):
    c, e, fv, _ = state_square_at(r, alpha, sign)
    for k in range(n + 1):
        p = (LAM, -KAP + 2 * KAP * k / n)
        d = sub(p, c)
        if not (abs(dot(d, e)) < 0.5 and abs(dot(d, fv)) < 0.5):
            return False
    return True


def segment():
    eps = 1e-3
    # Lemma K.4 (1) on a grid of the allowed states, both reflections
    for i in range(41):
        alpha = PI / 4 * i / 40
        lo, hi = (0.5 + 1e-6) / math.cos(alpha), rho(alpha)
        for j in range(41):
            r = lo + (hi - lo) * j / 40
            for sign in (1, -1):
                assert contains_V(r, alpha, sign)
    show = [(0.0, (0.5 + eps), BLUE), (0.0, rho(0.0), ORANGE),
            (PI / 4, (0.5 + eps) / math.cos(PI / 4), GREEN),
            (PI / 4, rho(PI / 4), PURPLE)]
    f = Figure(-0.2, 2.15, -0.95, 0.95, 230)
    R = math.sqrt(Q0)
    arc = [mul(R, u(-0.5 + 1.0 * k / 60)) for k in range(61)]
    polyline(f, arc, stroke=INK, width=1.1, dash='6 4')
    for alpha, r, col in show:
        c, e, fv, corners = state_square_at(r, alpha)
        assert all(dot(p, p) <= Q0 + 1e-9 for p in corners)
        assert contains_V(r, alpha)
        f.polygon(corners, fill=FILLS[COLORS.index(col)], stroke=col,
                  width=1.6, opacity=0.35)
        f.dot(c, r=2.6, fill=col)
    f.line((LAM, -KAP), (LAM, KAP), stroke=RED, width=4)
    f.line((-0.05, 0), (2.08, 0), stroke=FAINT, width=1, dash='3 3')
    origin(f, dx=0.03, dy=-0.07)
    halo_text(f, (LAM + 0.05, KAP + 0.06), it('V'), size=15, color=RED,
              italic=False)
    halo_text(f, (LAM - 0.03, -KAP - 0.04), '11/12', size=12, color=RED,
              anchor='end')
    f.save('appendix-k/segment', 'Four squares in the disk at the corners of '
           'the allowed states, each turned so that its centre direction is '
           'horizontal, all containing the segment V')


# ------------------------------------------------------- blocked directions

def F_A(A1, y):
    k = math.sqrt(R0 ** 2 - A1 ** 2)
    if y <= k:
        return math.atan(y / A1) + math.acos(LAM / math.sqrt(A1 * A1 + y * y))
    if y <= LAM:
        return math.asin(y / R0) + PHI0
    if y <= R0:
        return PI / 2 + math.acos(LAM / y)
    return PI / 2 + PHI0


def segment_meets_rect(psi, A1, y, tol=1e-12):
    """Whether the rotated segment R_psi V meets [0, A1] x [0, y]: the points
    Lambda e + t f, |t| <= kappa, clipped by the four sides (Liang-Barsky)."""
    e, fv = u(psi), u(psi + PI / 2)
    lo, hi = -KAP, KAP
    # each side: base + t * slope >= 0
    for base, slope in ((LAM * e[0], fv[0]), (A1 - LAM * e[0], -fv[0]),
                        (LAM * e[1], fv[1]), (y - LAM * e[1], -fv[1])):
        if abs(slope) < 1e-15:
            if base < -tol:
                return False
        elif slope > 0:
            lo = max(lo, -base / slope)
        else:
            hi = min(hi, -base / slope)
    return lo <= hi + tol


def blocked():
    A1, yv = LAM, 0.3
    Fv = F_A(A1, yv)
    assert abs(Fv - 2 * math.atan(yv / LAM)) < 1e-12
    for k in range(201):
        assert segment_meets_rect(Fv * k / 200, A1, yv)
    assert not segment_meets_rect(Fv + 0.005, A1, yv)
    corner = (A1, yv)
    e, fv = u(Fv), u(Fv + PI / 2)
    assert abs(dot(corner, e) - LAM) < 1e-12 and abs(dot(corner, fv)) <= KAP
    f = Figure(-0.12, 1.2, -0.42, 1.0, 470)
    f.polygon([(0, 0), (A1, 0), (A1, yv), (0, yv)], fill=FILLS[0],
              stroke=BLUE, width=1.4)
    for k in range(7):
        psi = Fv * k / 6
        e, fv = u(psi), u(psi + PI / 2)
        a = add(mul(LAM, e), mul(-KAP, fv))
        b = add(mul(LAM, e), mul(KAP, fv))
        last = (k == 6)
        f.line(a, b, stroke=RED if last else INK, width=2.4 if last else 1.0)
    f.arc((0, 0), 0.18, 0.0, Fv, ORANGE, width=2)
    halo_text(f, mul(0.3, u(Fv * 0.8)), sb(it('F'), 'Λ', '(0.3)', 13),
              size=13, color=ORANGE, anchor='start')
    # the radial projection of the corner onto the middle copy
    mid = Fv / 2
    qv = mul(LAM / dot(corner, u(mid)), corner)
    assert 0 <= qv[0] <= A1 and 0 <= qv[1] <= yv
    f.line((0, 0), corner, stroke=INK, width=1, dash='3 3')
    f.dot(corner, r=3.4, fill=RED)
    f.dot(qv, r=3, fill=INK)
    origin(f, dx=-0.02, dy=-0.05)
    f.text(shift_pt(corner, (0.03, 0.02)), '(' + it('A') + '<tspan dy="4" '
           'font-size="9">1</tspan><tspan dy="-4">,' + NB + '0.3)</tspan>',
           size=12, italic=False, anchor='start')
    halo_text(f, (LAM / 2, yv / 2), sb(it('T'), 'Λ', '(0.3)', 13), size=13,
              color=BLUE)
    halo_text(f, (LAM + 0.04, -KAP + 0.04), it('V'), size=14, italic=False,
              anchor='start')
    f.text((LAM, -KAP - 0.05), 'Λ' + NB + '=' + NB + '11/12', size=12,
           italic=False)
    f.save('appendix-k/blocked', 'The rectangle T_Lambda(0.3) and the segment V '
           'turned by angles from 0 to F_Lambda(0.3), each copy meeting the '
           'rectangle, the last one at its corner')


def widths():
    ds = [0.5 * i / 2000 for i in range(2001)]
    w1 = [F_A(LAM, d) + F_A(LAM, 1 - d) for d in ds]
    w2 = [F_A(19 / 20, d) + F_A(19 / 20, 1 - d) for d in ds]
    assert min(w1) > 347 / 200 and min(w2) > 899 / 500
    dmin = ds[w1.index(min(w1))]
    assert 0.1375 < dmin < 0.1385
    f = Figure(-0.15, 5.9, -0.45, 3.05, 120)
    ox, oy, kx = 0.8, 0.2, 9.0
    ylo, yhi = 1.6, 2.4
    ky = 2.6 / (yhi - ylo)
    P = lambda d, w: (ox + kx * d, oy + ky * (w - ylo))
    f.line(P(0, ylo), P(0.53, ylo), width=1, arrow=True)
    f.line(P(0, ylo), P(0, yhi + 0.05), width=1, arrow=True)
    for bound, lab, col in ((347 / 200, '347/200', BLUE),
                            (899 / 500, '899/500', ORANGE)):
        f.line(P(0, bound), P(0.5, bound), stroke=col, width=1, dash='5 4')
        f.text(shift_pt(P(0.5, bound), (0.08, 0)), lab, size=12, italic=False,
               anchor='start', color=col)
    polyline(f, [P(d, w) for d, w in zip(ds, w1) if w <= yhi], stroke=BLUE,
             width=2)
    polyline(f, [P(d, w) for d, w in zip(ds, w2) if w <= yhi], stroke=ORANGE,
             width=2)
    for d, lab in ((0, '0'), (1 / 12, '1/12'), (0.25, '¼'), (0.5, '½')):
        f.line(P(d, ylo), shift_pt(P(d, ylo), (0, -0.05)), width=1)
        f.text(shift_pt(P(d, ylo), (0, -0.2)), lab, size=12, italic=False)
    for w in (1.6, 1.8, 2.0, 2.2, 2.4):
        f.line(P(0, w), shift_pt(P(0, w), (-0.05, 0)), width=1)
        f.text(shift_pt(P(0, w), (-0.08, 0)), f'{w:.1f}', size=12,
               italic=False, anchor='end')
    f.text(shift_pt(P(0.53, ylo), (0, 0.15)), it('d'), size=15, anchor='end')
    hs = '\u200a'
    halo_text(f, shift_pt(P(0.38, F_A(LAM, 0.38) + F_A(LAM, 0.62)), (0, -0.32)),
              sb(it('F'), 'Λ', hs + '(' + it('d') + ')' + NB + '+' + NB, 12)
              + sb(it('F'), 'Λ', hs + '(1' + NB + '−' + NB + it('d') + ')', 12),
              size=12, color=BLUE)
    halo_text(f, shift_pt(P(0.3, F_A(0.95, 0.3) + F_A(0.95, 0.7)), (0, 0.16)),
              sb(it('F'), '19/20', hs + '(' + it('d') + ')' + NB + '+' + NB, 12)
              + sb(it('F'), '19/20', hs + '(1' + NB + '−' + NB + it('d') + ')',
                   12),
              size=12, color=ORANGE)
    f.save('appendix-k/widths', 'The widths of the blocked intervals of '
           'directions as functions of d, above their bounds 347/200 and '
           '899/500')
    WIDTHS_INFO[0] = (min(w1), dmin, min(w2))


WIDTHS_INFO = [None]


def rays():
    B, g = 347 / 200, 19 / 25
    assert Fr(347, 200) + 6 * Fr(19, 25) > Fr(44, 7)
    over = B + 6 * g - 2 * PI
    assert 0.011 < over < 0.012
    f = Figure(-1.45, 1.45, -1.3, 1.3, 220)
    f.circle((0, 0), 1.0, stroke=FAINT, width=1)
    sector = [(0, 0)] + [u(-B / 2 + B * k / 60) for k in range(61)]
    f.polygon(sector, fill=GREY, stroke=FAINT, width=1)
    f.text(shift_pt(mul(0.55, u(0)), (0, 0.06)), 'blocked', size=13,
           italic=False)
    f.text(shift_pt(mul(0.55, u(0)), (0, -0.13)), '> 347/200', size=12,
           italic=False)
    for k in range(7):
        th = B / 2 + k * g
        last = (k == 6)
        f.line((0, 0), mul(1.15, u(th)), stroke=RED if last else INK,
               width=2 if last else 1.4)
        f.dot(mul(1.15, u(th)), r=2.6, fill=RED if last else INK)
        if k < 6:
            f.arc((0, 0), 0.82, th, th + g, ORANGE, width=2)
            halo_text(f, mul(0.66, u(th + g / 2)), '19/25', size=11,
                      color=ORANGE)
    halo_text(f, shift_pt(mul(1.25, u(B / 2 + 6 * g)), (0.05, -0.04)),
              'seventh ray', size=12, color=RED, anchor='start')
    origin(f, dx=0.07, dy=0.0)
    f.save('appendix-k/rays', 'The directions blocked by a shallow central square '
           'and seven centre directions with gaps of 19/25: the seventh ray '
           'falls inside the blocked arc')


def main():
    regions()
    weighted_figure()
    polys()
    segment()
    blocked()
    widths()
    rays()


if __name__ == '__main__':
    main()

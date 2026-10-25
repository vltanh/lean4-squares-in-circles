#!/usr/bin/env python3
"""Draw the figures of Appendix J (eight squares: the stationary system) as
SVG files in docs/proof/figures/appendix-j/.

    python3 scripts/figures/fig_appj.py

Both figures are computed from the five-corner chain of Section J.1: the
minimized defect m(q) by Newton's method in the pose, in floating point and,
near q*, in 60-digit decimal arithmetic; the envelope M(q, t) by bisection on
F_y in the window of positions of Proposition J.5. Each drawing asserts the
facts its caption states. The chain and the small helpers below are shared
with fig_appk.py, fig_appl.py and fig_appm.py.
"""
import math
from decimal import Decimal, getcontext

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb
from fig_front import it, NB, RED, RED_FILL, polyline, Q8, U8, T8

Q0 = 9789 / 2500
QMINUS = 7831 / 2000
CORE = 1 / 12


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


def core_disk(f, at=(0.0, 0.0), scale=1.0, r=CORE):
    f.circle(at, r * scale, stroke=RED, width=1.0, fill=RED_FILL)


def origin(f, at=(0.0, 0.0), dx=0.06, dy=-0.08, r=2.6):
    f.dot(at, r=r)
    f.text((at[0] + dx, at[1] + dy), 'o', size=14, anchor='start')


# ------------------------------------------------------------ the chain

def chain(q, y, t):
    """The five-corner chain of Section J.1 at the squared radius q, the
    position y and the tilt t."""
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
    """F_y and F_t of Lemma J.1."""
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
TSTAR, YSTAR = ROOT['t'], ROOT['y']
# Proposition J.5 (3): the bounds of the stationary solution.
assert -0.92071 < YSTAR < -0.92059 and 0.99231 <= ROOT['c'] <= 0.99242
assert 0.12327 <= ROOT['s'] <= 0.12338 and 1.75152 <= ROOT['x1'] <= 1.75159
assert 1.65843 <= ROOT['x2'] <= 1.65852 and 1.45455 <= ROOT['y3'] <= 1.45464
assert -1.90214 <= ROOT['x4'] <= -1.90211
assert -1.36797 <= ROOT['h1'] <= -1.36748 and -1.43022 <= ROOT['h2'] <= -1.42976
assert QMINUS < Q8 < 1957767069 / 500000000 < Q0 < 4

BLUE, ORANGE, GREEN = COLORS[0], COLORS[1], COLORS[2]

# The local rectangle of Section J.2 and the trial pose.
Y_LO, Y_HI = -937 / 1000, -179 / 200
Z_LO, Z_HI = 1 / 20, 81 / 1000
Y0 = -3682626712030424527 / (4 * 10 ** 18)
Z0 = 618974110076603597 / 10 ** 19
# The bracket of Proposition J.4 (3).
L_STAR = '3.91553413751747512652'
U_STAR = '3.91553413751747542652'


def gradient(q, y, t):
    return chain_derivatives(chain(q, y, t))


def minimize(q, y=Y0, t=2 * math.atan(Z0)):
    """The minimum of F(q, ., .) over the pose, by Newton's method on
    (F_y, F_t) with a central-difference Hessian."""
    h = 1e-6
    for _ in range(50):
        gy, gt = gradient(q, y, t)
        a = (gradient(q, y + h, t)[0] - gradient(q, y - h, t)[0]) / (2 * h)
        b = (gradient(q, y, t + h)[0] - gradient(q, y, t - h)[0]) / (2 * h)
        d = (gradient(q, y, t + h)[1] - gradient(q, y, t - h)[1]) / (2 * h)
        det = a * d - b * b
        dy = -(d * gy - b * gt) / det
        dt = -(-b * gy + a * gt) / det
        y, t = y + dy, t + dt
        if max(abs(dy), abs(dt)) < 1e-15:
            break
    return y, t, chain(q, y, t)['F']


# ----------------------------------------------- the defect in 60 digits

getcontext().prec = 60
D = Decimal


def defect_dec(q, y, z):
    """F, F_y and F_t of Theorem 11.1 in decimal arithmetic, with the
    rational parametrization c = (1 - z^2)/(1 + z^2), s = 2z/(1 + z^2)."""
    c = (1 - z * z) / (1 + z * z)
    s = 2 * z / (1 + z * z)
    x1 = (q - y * y).sqrt()
    x2 = (q - (y + 2) ** 2).sqrt()
    x3 = x2 - 3
    y3 = (q - x3 * x3).sqrt()
    y4 = y3 - 2
    x4 = -(q - y4 * y4).sqrt()
    h1 = c * x1 + s * y - 2 - c
    h2 = -s * x4 + c * y4 - 1 - s
    F = h1 * h1 + h2 * h2 - q
    Fy = (2 * h1 * (s - c * y / x1)
          + 2 * h2 * (c + s * y4 / x4) * x3 * (y + 2) / (y3 * x2))
    Ft = 2 * h1 * (c * y - s * (x1 - 1)) - 2 * h2 * (c * (x4 + 1) + s * y4)
    return F, Fy, Ft


def minimum_dec(q):
    """m(q): Newton's method on (F_y, F_t) in the pose (y, z), started at
    the trial pose; F_z is a positive multiple of F_t."""
    y, z = D(Y0), D(Z0)
    h = D('1e-25')
    for _ in range(40):
        _, gy, gt = defect_dec(q, y, z)
        _, ay, at_ = defect_dec(q, y + h, z)
        _, by, bt = defect_dec(q, y - h, z)
        _, cy, ct = defect_dec(q, y, z + h)
        _, dy_, dt_ = defect_dec(q, y, z - h)
        j11, j21 = (ay - by) / (2 * h), (at_ - bt) / (2 * h)
        j12, j22 = (cy - dy_) / (2 * h), (ct - dt_) / (2 * h)
        det = j11 * j22 - j12 * j21
        sy = -(j22 * gy - j12 * gt) / det
        sz = -(-j21 * gy + j11 * gt) / det
        y, z = y + sy, z + sz
        if abs(sy) + abs(sz) < D('1e-45'):
            break
    return defect_dec(q, y, z)[0], y, z


def minimum():
    qs = [QMINUS + (Q0 - QMINUS) * j / 60 for j in range(61)]
    ms = []
    for q in qs:
        y, t, m = minimize(q)
        z = math.tan(t / 2)
        # Proposition J.4 (1): the minimum point is interior, near the trial
        # pose
        assert Y_LO < y < Y_HI and Z_LO < z < Z_HI
        assert math.hypot(y - Y0, z - Z0) < 1 / 100
        ms.append(m)
    # Proposition J.4 (2) and (3): signs at the ends, slopes in [-4, -3]
    assert ms[0] > 0 > ms[-1]
    for q0, q1, m0, m1 in zip(qs, qs[1:], ms, ms[1:]):
        assert -4 <= (m1 - m0) / (q1 - q0) <= -3
    # the bracket, in 60 digits
    lo, hi = D(L_STAR), D(U_STAR)
    m_lo, m_hi = minimum_dec(lo)[0], minimum_dec(hi)[0]
    assert m_lo > 0 > m_hi and hi - lo == D('3e-16')
    # q* to 30 digits by the secant method
    a, b, fa, fb = lo, hi, m_lo, m_hi
    for _ in range(8):
        if fb == fa or fb == 0:
            break
        c = b - fb * (b - a) / (fb - fa)
        a, fa, b, fb = b, fb, c, minimum_dec(c)[0]
    qstar = b
    assert lo < qstar < hi and abs(float(qstar) - Q8) < 1e-14
    # left panel: m(q) on the radius interval
    f = Figure(-0.2, 8.15, -0.35, 3.35, 100)
    ox, oy = 0.95, 0.35
    kx = 3.6 / (Q0 - QMINUS)
    ylo, yhi = -0.0003, 0.00015
    ky = 2.6 / (yhi - ylo)
    P = lambda q, m: (ox + kx * (q - QMINUS), oy + ky * (m - ylo))
    f.line(P(QMINUS, ylo), P(Q0, ylo), width=1)
    f.line(P(QMINUS, ylo), P(QMINUS, yhi + 0.00002), width=1, arrow=True)
    f.line(P(QMINUS, 0), P(Q0, 0), stroke=FAINT, width=1, dash='4 3')
    for s, lab in ((-3, '−3'), (-4, '−4')):
        q0 = max(QMINUS, Q8 + yhi / s)
        q1 = min(Q0, Q8 + ylo / s)
        f.line(P(q0, s * (q0 - Q8)), P(q1, s * (q1 - Q8)), stroke=INK,
               width=1, dash='5 4')
        f.text(shift_pt(P(q1, s * (q1 - Q8)), (0.1, 0.0)),
               'slope' + NB + lab, size=12, italic=False, anchor='start')
    polyline(f, [P(q, m) for q, m in zip(qs, ms)], stroke=BLUE, width=2.2)
    f.dot(P(Q8, 0), r=3.4)
    f.text(shift_pt(P(Q8, 0), (0.1, 0.16)), sb(it('q'), '*', size=14),
           size=14, anchor='start', italic=False)
    for q, lab in ((QMINUS, '7831/2000'), (Q0, '9789/2500')):
        f.line(P(q, ylo), shift_pt(P(q, ylo), (0, -0.05)), width=1)
        f.text(shift_pt(P(q, ylo), (0, -0.2)), lab, size=12, italic=False)
    for m, lab in ((-0.0002, '−0.0002'), (-0.0001, '−0.0001'), (0.0, '0'),
                   (0.0001, '0.0001')):
        f.line(P(QMINUS, m), shift_pt(P(QMINUS, m), (-0.05, 0)), width=1)
        f.text(shift_pt(P(QMINUS, m), (-0.08, 0)), lab, size=12, italic=False,
               anchor='end')
    f.text(shift_pt(P(QMINUS, yhi + 0.00002), (0.1, -0.02)),
           it('m') + '(' + it('q') + ')', size=14, italic=False, anchor='start')
    f.text(shift_pt(P(Q0, ylo), (0.12, -0.02)), it('q'), size=15, anchor='start')
    # right panel: the bracket, in units of 1e-16
    ox2, oy2 = 5.75, 0.35
    sx, sy = 0.5, 2.6 / 17
    us = [-0.6 + 4.2 * j / 6 for j in range(7)]
    vals = [float(minimum_dec(lo + D(v) * D('1e-16'))[0] * D('1e16'))
            for v in us]
    for v0, v1, w0, w1 in zip(us, us[1:], vals, vals[1:]):
        assert -4 <= (w1 - w0) / (v1 - v0) <= -3
    assert -6.5 < min(vals) and max(vals) < 10.5
    R = lambda v, w: (ox2 + sx * (v + 0.6), oy2 + sy * (w + 6.5))
    f.line(R(-0.6, -6.5), R(3.6, -6.5), width=1)
    f.line(R(-0.6, -6.5), R(-0.6, 10.5), width=1, arrow=True)
    f.line(R(-0.6, 0), R(3.6, 0), stroke=FAINT, width=1, dash='4 3')
    f.polygon([R(0, -6.5), R(3, -6.5), R(3, 10), R(0, 10)],
              fill=FILLS[1], stroke='none', opacity=0.8)
    polyline(f, [R(v, w) for v, w in zip(us, vals)], stroke=BLUE, width=2.2)
    zq = float((qstar - lo) * D('1e16'))
    f.dot(R(zq, 0), r=3.4)
    f.text(shift_pt(R(zq, 0), (0.1, 0.18)), sb(it('q'), '*', size=14),
           size=14, anchor='start', italic=False)
    for v, lab in ((0, sb('ℓ', '*', size=13)), (3, sb(it('u'), '*', size=13))):
        f.line(R(v, -6.5), shift_pt(R(v, -6.5), (0, -0.05)), width=1)
        f.text(shift_pt(R(v, -6.5), (0, -0.2)), lab, size=13, italic=False)
    for w in (-4, 0, 4, 8):
        f.line(R(-0.6, w), shift_pt(R(-0.6, w), (-0.05, 0)), width=1)
        f.text(shift_pt(R(-0.6, w), (-0.08, 0)), str(w).replace('-', '−'),
               size=12, italic=False, anchor='end')
    f.text(shift_pt(R(-0.6, 10.5), (-0.05, 0.18)),
           it('m') + NB + '(units' + NB + 'of' + NB + '10<tspan dy="-6" '
           'font-size="9">−16</tspan><tspan dy="6">)</tspan>', size=12,
           italic=False, anchor='start')
    f.text(shift_pt(R(1.5, -6.5), (0, -0.2)), 'width 3·10<tspan dy="-6" '
           'font-size="9">−16</tspan>', size=12, italic=False)
    f.save('appendix-j/minimum', 'The minimized defect m(q) on the radius '
           'interval, decreasing with slope between -4 and -3 and vanishing at '
           'q*, and an enlargement of the bracket of width 3e-16 around q*')
    MINIMUM_INFO[0] = (ms[0], ms[-1], float(m_lo), float(m_hi), str(qstar)[:32])


MINIMUM_INFO = [None]


def shift_pt(p, v):
    return (p[0] + v[0], p[1] + v[1])


# ------------------------------------------------------------ the envelope

T_MAX = math.atan(1 / 5)


def envelope_point(q, t):
    """M(q, t) of Proposition J.5, Step 2: the critical position of F(q, ., t)
    in the window 87/100 <= -y <= 11/10, by bisection on F_y, and the value
    of F there."""
    lo, hi = -11 / 10, -87 / 100
    # F_y < 0 at -y = 11/10 and F_y > 0 at -y = 87/100 (Step 2)
    assert chain_derivatives(chain(q, lo, t))[0] < 0
    assert chain_derivatives(chain(q, hi, t))[0] > 0
    for _ in range(80):
        mid = (lo + hi) / 2
        if chain_derivatives(chain(q, mid, t))[0] < 0:
            lo = mid
        else:
            hi = mid
    y = (lo + hi) / 2
    return chain(q, y, t)['F'], y


def envelope():
    n = 240
    ts = [T_MAX * k / n for k in range(n + 1)]
    qs = [Q8 - 0.012, Q8 - 0.006, Q8]
    curves = [[envelope_point(q, t)[0] for t in ts] for q in qs]
    for q, vals in zip(qs, curves):
        # one critical tilt, a minimum: the values decrease, then increase
        k = min(range(n + 1), key=lambda i: vals[i])
        assert all(a > b for a, b in zip(vals[:k], vals[1:k + 1]))
        assert all(a < b for a, b in zip(vals[k:], vals[k + 1:]))
    # at q*: M >= 0, with its zero at t*
    assert min(curves[2]) > -1e-9
    assert abs(envelope_point(Q8, TSTAR)[0]) < 1e-9
    assert abs(envelope_point(Q8, TSTAR)[1] - YSTAR) < 1e-7
    # a larger radius lowers the curve by more than the difference of radii
    for i in range(len(qs) - 1):
        for a, b in zip(curves[i], curves[i + 1]):
            assert a - b > qs[i + 1] - qs[i]
    # q* + 6e-5, still below 9789/2500: the minimum is negative
    qhi = Q8 + 0.00006
    assert qhi < Q0
    zoom_ts = [0.109 + (0.139 - 0.109) * k / 120 for k in range(121)]
    zoom_hi = [envelope_point(qhi, t)[0] for t in zoom_ts]
    zoom_st = [envelope_point(Q8, t)[0] for t in zoom_ts]
    assert min(zoom_hi) < -1e-4 and min(zoom_st) > -1e-9
    f = Figure(-0.1, 8.55, -0.02, 3.3, 100)
    # left panel: the three curves on the whole tilt interval
    ox, oy = 0.85, 0.3
    kx = 3.9 / T_MAX
    ylo, yhi = -0.002, 0.056
    ky = 2.75 / (yhi - ylo)
    P = lambda t, m: (ox + kx * t, oy + ky * (m - ylo))
    f.line(P(0, ylo), P(T_MAX * 1.04, ylo), width=1, arrow=True)
    f.line(P(0, ylo), P(0, yhi + 0.002), width=1, arrow=True)
    f.line(P(0, 0), P(T_MAX, 0), stroke=FAINT, width=1, dash='4 3')
    colors = [COLORS[2], COLORS[1], COLORS[0]]
    labels = [sb(it('q'), '*', NB + '−' + NB + '0.012', 13),
              sb(it('q'), '*', NB + '−' + NB + '0.006', 13),
              sb(it('q'), '*', '', 13)]
    for vals, col, lab in zip(curves, colors, labels):
        polyline(f, [P(t, m) for t, m in zip(ts, vals)], stroke=col,
                 width=2.2)
        halo_text(f, shift_pt(P(T_MAX, vals[-1]), (0.08, 0.0)), lab,
                  size=13, color=col, anchor='start')
    f.dot(P(TSTAR, 0), r=3.4)
    f.text(shift_pt(P(TSTAR, 0), (0.0, -0.17)), sb(it('t'), '*', size=14),
           size=14, italic=False)
    for tv, lab in ((0.0, '0'), (0.05, '0.05'), (0.1, '0.1'), (0.15, '0.15')):
        f.line(P(tv, ylo), shift_pt(P(tv, ylo), (0, -0.05)), width=1)
        f.text(shift_pt(P(tv, ylo), (0, -0.2)), lab, size=12, italic=False)
    f.line(P(T_MAX, ylo), shift_pt(P(T_MAX, ylo), (0, -0.05)), width=1)
    f.text(shift_pt(P(T_MAX, ylo), (0.05, -0.2)), 'arctan' + NB + '⅕',
           size=12, italic=False)
    for mv, lab in ((0.0, '0'), (0.02, '0.02'), (0.04, '0.04')):
        f.line(P(0, mv), shift_pt(P(0, mv), (-0.05, 0)), width=1)
        f.text(shift_pt(P(0, mv), (-0.08, 0)), lab, size=12, italic=False,
               anchor='end')
    f.text(shift_pt(P(0, yhi + 0.002), (0.1, -0.02)),
           it('M') + '(' + it('q') + ',' + NB + it('t') + ')', size=14,
           italic=False, anchor='start')
    f.text(shift_pt(P(T_MAX * 1.04, ylo), (0.12, 0.0)), it('t'), size=15,
           anchor='start')
    # right panel: near t*, the curves for q* and q* + 0.00006
    ox2, oy2 = 6.05, 0.3
    kx2 = 2.3 / 0.03
    zlo, zhi = -0.0004, 0.0012
    ky2 = 2.75 / (zhi - zlo)
    R = lambda t, m: (ox2 + kx2 * (t - 0.109), oy2 + ky2 * (m - zlo))
    f.polygon([R(0.109, zlo), R(0.139, zlo), R(0.139, zhi), R(0.109, zhi)],
              stroke=FAINT, width=1)
    f.line(R(0.109, 0), R(0.139, 0), stroke=FAINT, width=1, dash='4 3')
    clip = lambda pts: [p for p in pts if zlo <= p[1] <= zhi]
    polyline(f, [R(t, m) for t, m in clip(list(zip(zoom_ts, zoom_st)))],
             stroke=COLORS[0], width=2.2)
    polyline(f, [R(t, m) for t, m in clip(list(zip(zoom_ts, zoom_hi)))],
             stroke=COLORS[3], width=2.2, dash='6 3')
    f.dot(R(TSTAR, 0), r=3.4)
    f.text(shift_pt(R(TSTAR, 0), (0.0, 0.2)), sb(it('t'), '*', size=14),
           size=14, italic=False)
    for tv, lab in ((0.11, '0.11'), (0.12, '0.12'), (0.13, '0.13')):
        f.line(R(tv, zlo), shift_pt(R(tv, zlo), (0, -0.05)), width=1)
        f.text(shift_pt(R(tv, zlo), (0, -0.2)), lab, size=12, italic=False)
    for mv, lab in ((-0.0002, '−0.0002'), (0.0, '0'), (0.0005, '0.0005'),
                    (0.001, '0.001')):
        f.line(R(0.109, mv), shift_pt(R(0.109, mv), (-0.05, 0)), width=1)
        f.text(shift_pt(R(0.109, mv), (-0.08, 0)), lab, size=12, italic=False,
               anchor='end')
    halo_text(f, shift_pt(R(0.1335, zoom_st[96]), (-0.05, 0.22)),
              sb(it('q'), '*', '', 13), size=13, color=COLORS[0],
              anchor='end')
    halo_text(f, shift_pt(R(0.1335, zoom_hi[96]), (0.0, -0.2)),
              sb(it('q'), '*', NB + '+' + NB + '0.00006', 13), size=13,
              color=COLORS[3], anchor='middle')
    f.save('appendix-j/envelope', 'The envelope M(q, t) against the tilt t on '
           '[0, arctan(1/5)] for three squared radii, each with one minimum; '
           'at q* the minimum is zero, at t*, and a larger radius gives a '
           'negative minimum')


def main():
    minimum()
    envelope()


if __name__ == '__main__':
    main()

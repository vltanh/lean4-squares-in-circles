#!/usr/bin/env python3
"""Draw the figures of Appendix J (eight squares: the stationary system) as
SVG files in docs/proof/figures/appendix-j/.

    python3 scripts/figures/fig_appj.py

Both figures are computed from the five-corner chain of Definition 11.2: the
minimized defect m(q) by Newton's method in the pose, in floating point and,
near q*, in 60-digit decimal arithmetic; the zero sets of F_y and F_t by
marching squares. Each drawing asserts the facts its caption states.
"""
import math
from decimal import Decimal, getcontext

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb
from fig_front import it, NB, RED, polyline
from fig_eight import (chain, chain_derivatives, contour_segments, halo_text,
                       Q8, Q0, QMINUS, YSTAR, TSTAR)

BLUE, ORANGE, GREEN = COLORS[0], COLORS[1], COLORS[2]

# The local rectangle of Section J.2 and the trial pose.
Y_LO, Y_HI = -937 / 1000, -179 / 200
Z_LO, Z_HI = 1 / 20, 81 / 1000
Y0, Z0 = -0.92066, 0.0619
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


def localization():
    q = Q8
    y0, y1, z0, z1 = -1.0, -0.5, 0.0, 0.1

    def grads(y, z):
        return gradient(q, y, 2 * math.atan(z))
    fy = lambda y, z: grads(y, z)[0]
    ft = lambda y, z: grads(y, z)[1]
    fF = lambda y, z: chain(q, y, 2 * math.atan(z))['F']
    n = 160
    segs_y = contour_segments(fy, y0, y1, z0, z1, n, n, 0.0)
    segs_t = contour_segments(ft, y0, y1, z0, z1, n, n, 0.0)
    assert segs_y and segs_t

    # the crossings of the two zero sets
    def cross(a, b, c, d):
        r = (b[0] - a[0], b[1] - a[1])
        s = (d[0] - c[0], d[1] - c[1])
        den = r[0] * s[1] - r[1] * s[0]
        if abs(den) < 1e-18:
            return None
        w = (c[0] - a[0], c[1] - a[1])
        lam = (w[0] * s[1] - w[1] * s[0]) / den
        mu = (w[0] * r[1] - w[1] * r[0]) / den
        if 0 <= lam <= 1 and 0 <= mu <= 1:
            return (a[0] + lam * r[0], a[1] + lam * r[1])
        return None
    pts = []
    for a, b in segs_y:
        for c, d in segs_t:
            if (max(a[0], b[0]) < min(c[0], d[0]) or
                    max(c[0], d[0]) < min(a[0], b[0])):
                continue
            p = cross(a, b, c, d)
            if p is not None:
                pts.append(p)
    zstar = math.tan(TSTAR / 2)
    assert pts and all(math.hypot(p[0] - YSTAR, (p[1] - zstar) * 5) < 0.01
                       for p in pts)
    # the crossing lies in the local rectangle, and F vanishes there
    assert Y_LO < YSTAR < Y_HI and Z_LO < zstar < Z_HI
    assert abs(fF(YSTAR, zstar)) < 1e-9
    # F is positive on the section away from the stationary pose
    for i in range(41):
        for j in range(41):
            y = y0 + (y1 - y0) * i / 40
            z = z0 + (z1 - z0) * j / 40
            if math.hypot(y - YSTAR, (z - zstar) * 5) > 0.01:
                assert fF(y, z) > 0
    # drawing: y across, z up (stretched by 5)
    k = 900
    f = Figure(-1.12, -0.42, -0.02, 0.56, k)
    P = lambda y, z: (y, 5 * z)
    f.polygon([P(Y_LO, Z_LO), P(Y_HI, Z_LO), P(Y_HI, Z_HI), P(Y_LO, Z_HI)],
              fill=FILLS[1], stroke=ORANGE, width=1)
    for lev, dash in ((0.002, '2 3'), (0.01, '2 3'), (0.04, '2 3')):
        for a, b in contour_segments(fF, y0, y1, z0, z1, 120, 120, lev):
            f.line(P(*a), P(*b), stroke=FAINT, width=1, dash=dash)
    for a, b in segs_y:
        f.line(P(*a), P(*b), stroke=BLUE, width=2)
    for a, b in segs_t:
        f.line(P(*a), P(*b), stroke=GREEN, width=2)
    f.polygon([P(y0, z0), P(y1, z0), P(y1, z1), P(y0, z1)], stroke=INK,
              width=1)
    f.dot(P(YSTAR, zstar), r=3.6)
    halo_text(f, shift_pt(P(YSTAR, zstar), (0.012, 0.035)),
              '(' + sb(it('y'), '*', ',' + NB, 13) + sb(it('z'), '*', ')', 13),
              size=13, anchor='start')
    for y, lab in ((-1.0, '−1'), (-0.9, '−0.9'), (-0.8, '−0.8'), (-0.7, '−0.7'),
                   (-0.6, '−0.6'), (-0.5, '−½')):
        f.line(P(y, z0), P(y, z0 - 0.004), width=1)
        f.text(shift_pt(P(y, z0), (0, -0.03)), lab, size=12, italic=False)
    for z, lab in ((0.0, '0'), (0.05, '0.05'), (0.1, '0.1')):
        f.line(P(y0, z), shift_pt(P(y0, z), (-0.008, 0)), width=1)
        f.text(shift_pt(P(y0, z), (-0.014, 0)), lab, size=12, italic=False,
               anchor='end')
    f.text(shift_pt(P(y1, z0), (0.025, -0.0)), it('y'), size=15,
           anchor='start')
    f.text(shift_pt(P(y0, z1), (0.0, 0.03)), it('z'), size=15)
    # labels of the curves, placed at points of the curves
    # F_y = 0 near the bottom, where it lies right of F_t = 0, and F_t = 0
    # near the top, where it lies right of F_y = 0
    ly = min((s for s in segs_y if s[0][1] > 0.03), key=lambda s: s[0][1])[0]
    lt = max((s for s in segs_t if s[0][1] < 0.092), key=lambda s: s[0][1])[0]
    assert ly[0] > min(s[0][0] for s in segs_t if abs(s[0][1] - ly[1]) < 0.002)
    assert lt[0] > max(s[0][0] for s in segs_y if abs(s[0][1] - lt[1]) < 0.002)
    halo_text(f, shift_pt(P(*ly), (0.012, 0.0)),
              sb(it('F'), it('y'), NB + '=' + NB + '0', 13), size=13,
              color=BLUE, anchor='start')
    halo_text(f, shift_pt(P(*lt), (0.012, 0.0)),
              sb(it('F'), it('t'), NB + '=' + NB + '0', 13), size=13,
              color=GREEN, anchor='start')
    f.save('appendix-j/localization', 'The (y, z)-section of the initial box '
           'at q = q*: the zero sets of F_y and F_t cross only at the stationary '
           'pose, inside the shaded local rectangle, where F vanishes; dotted '
           'level curves of F around it')


def main():
    minimum()
    localization()


if __name__ == '__main__':
    main()

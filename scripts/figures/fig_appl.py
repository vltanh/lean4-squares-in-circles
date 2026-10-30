#!/usr/bin/env python3
"""Draw the figures of Appendix L (eight squares: what a table row proves)
as SVG files in docs/proof/figures/appendix-l/.

    python3 scripts/figures/fig_appl.py

The arcs and the support rules are computed on the outer curve of the level
Q1; the majorant of the square root from its formula; the Bernstein
coefficients exactly, with the polynomial of band A of Table K.2; the state
cover from the arcs of the role G in the coarse table of the mismatch chain.
Each drawing asserts the facts its caption states.
"""
import math
from fractions import Fraction as Fr

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb, u
from fig_front import it, NB, RED, polyline
from fig_eight import halo_text, outer_a, core_a, plane_frame, Q1
from fig_appk import band_polys, bernstein, peval, BAND_A, TABLE_BAND_A_P

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
RHO = math.sqrt(Q1)
V_C = -0.5                      # the centre (v, v) of the outer circle


def shift_pt(p, v):
    return (p[0] + v[0], p[1] + v[1])


def outer_arc(lo, hi, n=80):
    return [(outer_a(Q1, t), t * outer_a(Q1, t))
            for t in (lo + (hi - lo) * k / n for k in range(n + 1))]


def supports():
    # left: X >= 0, the function is concave along the arc
    X1, Y1 = 0.8, -1.0
    arc1 = outer_arc(1 / 8, 3 / 8)
    vals = [X1 * a + Y1 * b for a, b in arc1]
    ends = [vals[0], vals[-1]]
    assert min(vals) >= min(ends) - 1e-12
    k_min = 0 if ends[0] <= ends[1] else len(arc1) - 1
    # concavity along the arc, in the parameter b
    bs = [b for a, b in arc1]
    for i in range(1, len(arc1) - 1):
        lam = (bs[i] - bs[i - 1]) / (bs[i + 1] - bs[i - 1])
        assert vals[i] >= (1 - lam) * vals[i - 1] + lam * vals[i + 1] - 1e-12
    # right: the circle rule, attained on the arc
    X2, Y2 = -1.0, -0.6
    nrm = math.hypot(X2, Y2)
    bound = V_C * (X2 + Y2) - RHO * nrm
    touch = (V_C - RHO * X2 / nrm, V_C - RHO * Y2 / nrm)
    tg = touch[1] / touch[0]
    lo2, hi2 = 1 / 4, 1 / 2
    assert lo2 < tg < hi2
    arc2 = outer_arc(lo2, hi2)
    vals2 = [X2 * a + Y2 * b for a, b in arc2]
    assert min(vals2) >= bound - 1e-12 and min(vals2) - bound < 1e-4
    W = 0.95
    f = Figure(0.68, 0.7 + 2 * W, -0.12, 0.92, 400)
    for k, (arc, X, Y, name) in enumerate(((arc1, X1, Y1, 'concave'),
                                           (arc2, X2, Y2, 'circle'))):
        at = (k * W, 0.0)
        P = lambda p: shift_pt(at, p)
        full = outer_arc(0.0, 1.0, 120)
        polyline(f, [P(p) for p in full if p[0] < 1.55], stroke=FAINT, width=1.2)
        # level lines X a + Y b = c
        vs = [X * a + Y * b for a, b in arc]
        cmin = min(vs)
        levels = ([cmin + 0.06 * j for j in range(0, 5)] if k == 0 else
                  [bound + 0.06 * j for j in range(0, 5)])
        for j, c in enumerate(levels):
            # the part of the line X a + Y b = c in the panel window
            pts = []
            for a in (0.78, 1.52):
                b = (c - X * a) / Y
                pts.append((a, b))
            (a0, b0), (a1, b1) = pts
            # clip to b in [0, 0.85]
            seg = []
            for t in [i / 200 for i in range(201)]:
                a, b = a0 + (a1 - a0) * t, b0 + (b1 - b0) * t
                if 0.0 <= b <= 0.85:
                    seg.append((a, b))
            if len(seg) > 1:
                f.line(P(seg[0]), P(seg[-1]), stroke=INK if j == 0 else FAINT,
                       width=1.1 if j == 0 else 0.9,
                       dash='5 3' if j == 0 else '2 3')
        polyline(f, [P(p) for p in arc], stroke=BLUE, width=4.5)
        for p in (arc[0], arc[-1]):
            f.dot(P(p), r=3, fill=BLUE)
        if k == 0:
            f.dot(P(arc[k_min]), r=4.6, fill=ORANGE)
            halo_text(f, P(shift_pt(arc[k_min], (0.03, -0.03))), 'least value',
                      size=12, color=ORANGE, anchor='start')
            label = (it('X') + NB + '=' + NB + '0.8,' + NB + it('Y') + NB + '='
                     + NB + '−1')
        else:
            f.dot(P(touch), r=4.6, fill=ORANGE)
            halo_text(f, P(shift_pt(touch, (0.03, 0.04))), 'touches', size=12,
                      color=ORANGE, anchor='start')
            label = (it('X') + NB + '=' + NB + '−1,' + NB + it('Y') + NB + '='
                     + NB + '−0.6')
        f.text(P((1.15, -0.095)), label, size=12, italic=False)
        f.line(P((0.78, 0.0)), P((1.52, 0.0)), width=1)
        f.line(P((0.78, 0.0)), P((0.78, 0.85)), width=1)
        for a, lab in ((1.0, '1'), (1.25, '1.25'), (1.5, '1.5')):
            f.line(P((a, 0.0)), P((a, -0.012)), width=1)
            f.text(P((a, -0.04)), lab, size=11, italic=False)
        for b, lab in ((0.25, '¼'), (0.5, '½'), (0.75, '¾')):
            f.line(P((0.78, b)), P((0.768, b)), width=1)
            f.text(P((0.762, b)), lab, size=11, italic=False, anchor='end')
        f.text(P((1.52, 0.035)), it('a'), size=14, anchor='end')
        f.text(P((0.80, 0.84)), it('b'), size=14, anchor='start')
        halo_text(f, P(shift_pt(full[int(0.8 * len(full))], (0.04, 0.03))),
                  sb('𝒪', it('Q') + '<tspan font-size="7">1</tspan>', size=14),
                  size=14, color=FAINT, anchor='start')
    f.save('appendix-l/supports', 'Two arcs of the outer curve with level lines '
           'of linear functions: with X at least 0 the least value is at an '
           'endpoint; the circle rule takes the least value on the whole '
           'circle, here attained on the arc')


def majorant():
    h = 1.0
    T = lambda V: (5 * h + 15 * V / h - 5 * V * V / h ** 3 + V ** 3 / h ** 5) / 16
    for i in range(401):
        V = 4 * i / 400
        w = math.sqrt(V)
        diff = (w - h) ** 4 * (V + 4 * h * w + 5 * h * h) / (16 * h ** 5)
        assert abs(T(V) - w - diff) < 1e-12 and T(V) >= w - 1e-15
    assert abs(T(1.0) - 1.0) < 1e-15
    f = Figure(-0.25, 7.6, -0.45, 3.15, 106)
    ox, oy, kx, ky = 0.55, 0.15, 3.0 / 4, 2.7 / 3.2
    P = lambda V, y: (ox + kx * V, oy + ky * y)
    f.line(P(0, 0), P(4.25, 0), width=1, arrow=True)
    f.line(P(0, 0), P(0, 3.3), width=1, arrow=True)
    Vs = [4 * i / 400 for i in range(401)]
    polyline(f, [P(V, math.sqrt(V)) for V in Vs], stroke=BLUE, width=2)
    polyline(f, [P(V, T(V)) for V in Vs], stroke=ORANGE, width=2, dash='6 4')
    f.dot(P(1, 1), r=3.2)
    for V, lab in ((1, '1'), (2, '2'), (3, '3'), (4, '4')):
        f.line(P(V, 0), shift_pt(P(V, 0), (0, -0.05)), width=1)
        f.text(shift_pt(P(V, 0), (0, -0.2)), lab, size=12, italic=False)
    for y in (1, 2, 3):
        f.line(P(0, y), shift_pt(P(0, y), (-0.05, 0)), width=1)
        f.text(shift_pt(P(0, y), (-0.08, 0)), str(y), size=12, italic=False,
               anchor='end')
    f.text(shift_pt(P(4.25, 0), (0, 0.15)), it('V'), size=15, anchor='end')
    halo_text(f, shift_pt(P(3.2, math.sqrt(3.2)), (0.05, -0.2)), '√' + it('V'),
              size=14, color=BLUE, anchor='start')
    halo_text(f, shift_pt(P(3.3, T(3.3)), (-0.1, 0.12)),
              sb(it('T'), '1', '(' + it('V') + ')', 14), size=14, color=ORANGE,
              anchor='end')
    # right panel: the difference, enlarged
    ox2, oy2, kx2 = 4.6, 0.15, 2.6 / 2.5
    ymax = 0.35
    ky2 = 2.7 / ymax
    R = lambda V, y: (ox2 + kx2 * V, oy2 + ky2 * y)
    f.line(R(0, 0), R(2.7, 0), width=1, arrow=True)
    f.line(R(0, 0), R(0, ymax * 1.08), width=1, arrow=True)
    Vs2 = [2.5 * i / 400 for i in range(401)]
    polyline(f, [R(V, T(V) - math.sqrt(V)) for V in Vs2], stroke=PURPLE,
             width=2)
    f.dot(R(1, 0), r=3.2)
    for V, lab in ((0.5, '½'), (1, '1'), (2, '2')):
        f.line(R(V, 0), shift_pt(R(V, 0), (0, -0.05)), width=1)
        f.text(shift_pt(R(V, 0), (0, -0.2)), lab, size=12, italic=False)
    for y in (0.1, 0.2, 0.3):
        f.line(R(0, y), shift_pt(R(0, y), (-0.05, 0)), width=1)
        f.text(shift_pt(R(0, y), (-0.08, 0)), f'{y:.1f}', size=12,
               italic=False, anchor='end')
    f.text(shift_pt(R(2.7, 0), (0, 0.15)), it('V'), size=15, anchor='end')
    halo_text(f, R(1.45, 0.16),
              sb(it('T'), '1', '(' + it('V') + ')' + NB + '−' + NB + '√' + it('V'),
                 13), size=13, color=PURPLE, anchor='start')
    f.save('appendix-l/majorant', 'The square root of V and its polynomial '
           'majorant T_1(V), which touches it at V = 1, and their difference, '
           'enlarged, vanishing to fourth order at V = 1')


def bernstein_figure():
    P = band_polys(*BAND_A)[0]
    (l, r), bounds = next(iter(TABLE_BAND_A_P.items()))
    b = bernstein(P, l, r)
    for bk, lb in zip(b, bounds):
        assert lb <= bk * 10 ** 6 < lb + 1
    least = min(b)
    assert math.floor(least * 10 ** 6) == 76
    xs = [l + (r - l) * Fr(i, 300) for i in range(301)]
    vals = [peval(P, x) for x in xs]
    assert min(vals) > least
    n = len(b) - 1
    f = Figure(-0.2, 6.1, -0.45, 3.0, 120)
    ox, oy, kx = 0.85, 0.2, 4.6
    ky = 2.6 / 3000e-6
    X = lambda x: ox + kx * float((x - l) / (r - l))
    Y = lambda v: oy + ky * float(v)
    f.line((X(l), Y(0)), (X(r) + 0.25, Y(0)), width=1, arrow=True)
    f.line((X(l), Y(0)), (X(l), Y(3100e-6)), width=1, arrow=True)
    f.line((X(l), Y(least)), (X(r), Y(least)), stroke=FAINT, width=1,
           dash='4 3')
    pts = [(X(l + (r - l) * Fr(k, n)), Y(bk)) for k, bk in enumerate(b)]
    polyline(f, pts, stroke=ORANGE, width=1.3)
    for p in pts:
        f.dot(p, r=3.4, fill=ORANGE)
    polyline(f, [(X(x), Y(v)) for x, v in zip(xs, vals)], stroke=BLUE, width=2.2)
    for k, (p, bk) in enumerate(zip(pts, b)):
        halo_text(f, shift_pt(p, (0.0, 0.16 if k not in (2, 3) else -0.17)),
                  str(bounds[k]), size=11, color=ORANGE)
    for x, lab in ((l, '7/16'), (r, '1/2')):
        f.line((X(x), Y(0)), (X(x), Y(0) - 0.05), width=1)
        f.text((X(x), Y(0) - 0.2), lab, size=12, italic=False)
    for v in (1000e-6, 2000e-6, 3000e-6):
        f.line((X(l), Y(v)), (X(l) - 0.05, Y(v)), width=1)
        f.text((X(l) - 0.08, Y(v)), f'{v * 1e6:.0f}', size=12, italic=False,
               anchor='end')
    f.text((X(r) + 0.25, Y(0) + 0.15), it('u'), size=15, anchor='end')
    f.text((X(l) + 0.08, Y(3100e-6)), it('P') + NB + '(units' + NB + 'of' + NB
           + '10<tspan dy="-6" font-size="9">−6</tspan><tspan dy="6">)</tspan>',
           size=12, italic=False, anchor='start')
    f.save('appendix-l/bernstein', 'The polynomial P of band A on the cell from '
           '7/16 to 1/2 and its seven Bernstein control points, all positive, '
           'the least 76 millionths')


# The arcs of the role G in the coarse table of Proposition 11.34, step 1
# (CANDIDATE_COARSE_MISMATCH_HAND_DATA, research/eight at commit a21c91f):
# the tangents b/a of their endpoints, sign -1, on the outer curve and on the
# core curve.
COARSE_G_OUTER = ['1/20', '1/16', '3/32', '1/8', '5/32', '3/16', '7/32', '1/4',
                  '9/32', '5/16', '11/32', '3/8', '13/32', '7/16', '15/32',
                  '1/2', '17/32', '9/16', '19/32', '5/8', '21/32', '11/16',
                  '23/32', '3/4', '25/32', '4/5']
COARSE_G_CORE = ['1/20', '3/28', '3/14', '9/28', '3/7', '15/28', '9/14', '3/4',
                 '4/5']


def cover():
    outer = [Fr(t) for t in COARSE_G_OUTER]
    core = [Fr(t) for t in COARSE_G_CORE]
    for cuts in (outer, core):
        assert cuts[0] == Fr(1, 20) and cuts[-1] == Fr(4, 5)
        assert all(a < b for a, b in zip(cuts, cuts[1:]))
    assert len(outer) - 1 == 25 and len(core) - 1 == 8
    assert core[-1] <= Fr(6, 7)        # all on the side of the core curve
    f = Figure(0.3, 1.55, -0.1, 1.05, 520)
    full_o = [(outer_a(Q1, t), t * outer_a(Q1, t))
              for t in (k / 160 for k in range(161))]
    corner = [(core_a(t), t * core_a(t))
              for t in (6 / 7 + (1 / 7) * k / 40 for k in range(41))]
    polyline(f, full_o, stroke=FAINT, width=1.2)
    polyline(f, [(7 / 12, 0.0), (7 / 12, 0.5)] + corner, stroke=FAINT,
             width=1.2)
    for t, lab in ((1 / 20, '1/20'), (4 / 5, '4/5')):
        a_end = outer_a(Q1, t)
        f.line((0.4, 0.4 * t), (a_end + 0.05, t * (a_end + 0.05)), stroke=INK,
               width=0.9, dash='3 3')
        f.text((a_end + 0.07, t * (a_end + 0.07)), it('b') + '/' + it('a')
               + NB + '=' + NB + lab, size=12, italic=False, anchor='start')
    for cuts, curve in ((outer, 'O'), (core, 'C')):
        for k, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
            n = 12
            ts = [float(lo + (hi - lo) * Fr(j, n)) for j in range(n + 1)]
            if curve == 'O':
                pts = [(outer_a(Q1, t), t * outer_a(Q1, t)) for t in ts]
            else:
                pts = [(core_a(t), t * core_a(t)) for t in ts]
            polyline(f, pts, stroke=BLUE if k % 2 == 0 else ORANGE, width=5)
        for t in cuts:
            t = float(t)
            a = outer_a(Q1, t) if curve == 'O' else core_a(t)
            f.dot((a, t * a), r=1.8)
    plane_frame(f, 0.4, 1.52, 1.0, ((0.5, '½'), (7 / 12, '7/12'), (1.0, '1')),
                ((0.5, '½'),))
    halo_text(f, (1.3, 0.62), sb('𝒪', it('Q') + '<tspan font-size="7">1</tspan>',
                                size=15) + ': 25 arcs', size=13,
              anchor='start')
    halo_text(f, (0.6, 0.62), '𝒞: 8 arcs', size=13, anchor='start')
    f.save('appendix-l/cover', 'The arcs of the role G in the coarse table on the '
           'outer curve and on the side of the core curve, alternately '
           'coloured, covering the tangents from 1/20 to 4/5')


def main():
    supports()
    majorant()
    bernstein_figure()
    cover()


if __name__ == '__main__':
    main()

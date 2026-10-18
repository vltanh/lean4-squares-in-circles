#!/usr/bin/env python3
"""Draw the figures of Appendix M (eight squares: the sharp terminal) as SVG
files in docs/proof/figures/appendix-m/.

    python3 scripts/figures/fig_appm.py

The comparison chain at a free tilt is computed from the five-corner chain of
Definition 11.2, with its position found by Newton's method on F_y = 0; the
error alternatives from the linear form of Section M.7. Each drawing asserts
the facts its caption states.
"""
import math

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb
from fig_front import it, NB, RED, polyline
from fig_eight import (chain, chain_derivatives, contour_segments, halo_text,
                       Q8, TSTAR, YSTAR)

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
Y_LO, Y_HI = -937 / 1000, -179 / 200


def shift_pt(p, v):
    return (p[0] + v[0], p[1] + v[1])


def position(t, y=YSTAR):
    """Y(t) of Lemma M.1: the zero of F_y(q*, ., t), by Newton's method."""
    h = 1e-7
    for _ in range(50):
        g = chain_derivatives(chain(Q8, y, t))[0]
        d = (chain_derivatives(chain(Q8, y + h, t))[0]
             - chain_derivatives(chain(Q8, y - h, t))[0]) / (2 * h)
        step = -g / d
        y += step
        if abs(step) < 1e-15:
            break
    return y


def envelope():
    t0, t1 = 1 / 10, 4 / 25
    ts = [t0 + (t1 - t0) * k / 240 for k in range(241)]
    ms = []
    for t in ts:
        y = position(t)
        assert Y_LO < y < Y_HI
        # F_y increases on the pose interval: negative below, positive above
        assert chain_derivatives(chain(Q8, Y_LO, t))[0] < 0
        assert chain_derivatives(chain(Q8, Y_HI, t))[0] > 0
        m = chain(Q8, y, t)['F']
        assert m >= 3 / 8 * (t - TSTAR) ** 2 - 1e-12
        ms.append(m)
    assert abs(chain(Q8, position(TSTAR), TSTAR)['F']) < 1e-12
    assert abs(ts[ms.index(min(ms))] - TSTAR) < 1e-3
    f = Figure(-0.2, 6.3, -0.45, 3.05, 120)
    ox, oy = 0.85, 0.2
    kx = 5.0 / (t1 - t0)
    ymax = max(ms) * 1.08
    ky = 2.6 / ymax
    P = lambda t, v: (ox + kx * (t - t0), oy + ky * v)
    f.line(P(t0, 0), P(t1, 0), width=1)
    f.line(P(t0, 0), P(t0, ymax * 1.05), width=1, arrow=True)
    polyline(f, [P(t, 3 / 8 * (t - TSTAR) ** 2) for t in ts], stroke=ORANGE,
             width=1.8, dash='6 4')
    polyline(f, [P(t, m) for t, m in zip(ts, ms)], stroke=BLUE, width=2.2)
    f.dot(P(TSTAR, 0), r=3.4)
    f.text(shift_pt(P(TSTAR, 0), (0, -0.2)), sb(it('t'), '*', NB + '≈' + NB
           + '0.1236', 12), size=12, italic=False)
    for t, lab in ((t0, '1/10'), (t1, '4/25')):
        f.line(P(t, 0), shift_pt(P(t, 0), (0, -0.05)), width=1)
        f.text(shift_pt(P(t, 0), (0, -0.2)), lab, size=12, italic=False)
    step = 0.0002
    v = step
    while v < ymax:
        f.line(P(t0, v), shift_pt(P(t0, v), (-0.05, 0)), width=1)
        f.text(shift_pt(P(t0, v), (-0.08, 0)), f'{v:.4f}', size=11,
               italic=False, anchor='end')
        v += step
    f.text(shift_pt(P(t1, 0), (0.12, 0.0)), it('t'), size=15, anchor='start')
    k_lab = int(0.12 * len(ts))
    halo_text(f, shift_pt(P(ts[k_lab], ms[k_lab]), (0.15, 0.05)),
              it('F') + '(' + sb(it('q'), '*', ',' + NB, 13) + it('Y') + '('
              + it('t') + '),' + NB + it('t') + ')', size=13, color=BLUE,
              anchor='start')
    k_par = int(0.8 * len(ts))
    halo_text(f, shift_pt(P(ts[k_par], 3 / 8 * (ts[k_par] - TSTAR) ** 2),
                          (0.1, -0.12)),
              '⅜(' + it('t') + NB + '−' + NB + sb(it('t'), '*', ')²', 13),
              size=13, color=ORANGE, anchor='start')
    f.save('appendix-m/envelope', 'The defect of the comparison chain at the '
           'radius q*, with its position chosen to make F_y vanish, against '
           'the tilt from 1/10 to 4/25, and the parabola 3/8 (t - t*)^2 below '
           'it')
    ENVELOPE_INFO[0] = (max(ms), min(ms))


ENVELOPE_INFO = [None]


def vertices():
    eps = 1.0
    c = (0.9, -0.3)
    half = (0.5, 0.5)                 # lambda_i / 2

    def form(d1, d2):
        return (c[0] * d1 - half[0] * abs(d1)) + (c[1] * d2 - half[1] * abs(d2))
    alts = [(0.0, 0.0), (eps, 0.0), (-eps, 0.0), (0.0, eps), (0.0, -eps)]
    vals = [form(*p) for p in alts]
    best = max(vals)
    # the maximum over the ball is at the centre or at a vertex
    for i in range(-100, 101):
        for j in range(-100, 101):
            d1, d2 = eps * i / 100, eps * j / 100
            if abs(d1) + abs(d2) <= eps + 1e-12:
                assert form(d1, d2) <= best + 1e-12
    # and equals eps max(0, max |c_i| - lambda_i / 2)
    assert abs(best - eps * max(0.0, max(abs(c[0]) - half[0],
                                         abs(c[1]) - half[1]))) < 1e-12
    arg = alts[vals.index(best)]
    assert arg == (eps, 0.0)
    f = Figure(-1.75, 1.95, -1.45, 1.45, 170)
    f.polygon([(eps, 0), (0, eps), (-eps, 0), (0, -eps)], fill=FILLS[0],
              stroke=BLUE, width=1.6)
    f.line((-1.4, 0), (1.45, 0), width=1, arrow=True)
    f.line((0, -1.3), (0, 1.35), width=1, arrow=True)
    for lev in [k * 0.2 for k in range(-5, 3)]:
        for a, b in contour_segments(form, -1.3, 1.3, -1.25, 1.25, 52, 50,
                                     lev):
            f.line(a, b, stroke=FAINT, width=1, dash='2 2')
    for p, v in zip(alts, vals):
        top = (p == arg)
        f.dot(p, r=5 if top else 3.6, fill=ORANGE if top else INK)
    halo_text(f, (eps + 0.06, 0.12), 'maximum', size=12, color=ORANGE,
              anchor='start')
    f.text((1.45, -0.1), sb(it('d'), '1', size=15), size=15, anchor='end',
           italic=False)
    f.text((0.08, 1.33), sb(it('d'), '2', size=15), size=15, anchor='start',
           italic=False)
    f.text((eps, -0.12), 'ε', size=13, italic=True)
    f.text((-eps, -0.12), '−' + it('ε'), size=13, italic=False)
    f.text((0.12, eps + 0.08), 'ε', size=13, anchor='start')
    f.text((0.12, -eps - 0.1), '−' + it('ε'), size=13, anchor='start',
           italic=False)
    halo_text(f, (-1.15, 1.05), '|' + sb(it('d'), '1', '|' + NB + '+' + NB, 13)
              + '|' + sb(it('d'), '2', '|' + NB + '≤' + NB + it('ε'), 13), size=13,
              color=BLUE, anchor='start')
    f.save('appendix-m/vertices', 'The l1 ball of two of the aligned errors with '
           'the level lines of a linear form with cusps on the axes; its '
           'maximum over the ball is at a vertex')


def main():
    envelope()
    vertices()


if __name__ == '__main__':
    main()

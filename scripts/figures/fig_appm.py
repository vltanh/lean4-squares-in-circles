#!/usr/bin/env python3
"""Draw the figures of Appendix M (eight squares: the dual at the original
centres) as SVG files in docs/proof/figures/appendix-m/.

    python3 scripts/figures/fig_appm.py

Both figures are computed from the stationary solution of the five-corner chain
(Section J.1) and the weights of Lemma J.6; the forces of the dual are checked
to balance at every square (Lemma M.3), and the extreme positions of the two
sliders to touch the core disk or the circle (Theorem M.9). Each drawing
asserts the facts its caption states.
"""
import math

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, GREY, sb
from fig_front import (it, NB, RED, polyline, arrow, eight_model, placed,
                       R8)
from fig_appj import (ROOT, halo_text, core_disk, origin, add, sub, mul, dot,
                      norm, Q8)

BLUE, ORANGE, GREEN, PURPLE, PINK, CYAN, YELLOW = COLORS
ROLE_COLOR = {'A': BLUE, 'B': ORANGE, 'D': GREEN, 'E': PURPLE, 'H': PINK,
              'T': CYAN, 'G': YELLOW}
ROLE_FILL = {k: FILLS[COLORS.index(v)] for k, v in ROLE_COLOR.items()}

C, S = ROOT['c'], ROOT['s']
E_T, F_T = (C, S), (-S, C)
E0, F0 = (1.0, 0.0), (0.0, 1.0)
X1, X2, X3, X4 = ROOT['x1'], ROOT['x2'], ROOT['x3'], ROOT['x4']
Y, Y3, Y4 = ROOT['y'], ROOT['y3'], ROOT['y4']
H1, H2 = ROOT['h1'], ROOT['h2']
W = (1 + C + S) / 2


def frame(a, b):
    return add(mul(a, E_T), mul(b, F_T))


def weights():
    """The weights of Lemma J.6 at the stationary solution."""
    muA0 = C / (2 * X1)
    al = S - C * Y / X1
    muB0 = al / (2 * (Y + 2))
    be = al * X2 / (Y + 2)
    muD0 = -be / (2 * X3)
    de = 2 * muD0 * Y3
    muH0 = -1 / (2 * H1)
    ep = H2 / H1
    muE0 = -S * ep / (2 * X4)
    om = 1 / (muA0 + muB0 + muD0 + muE0 + muH0)
    mu = {'A': om * muA0, 'B': om * muB0, 'D': om * muD0, 'E': om * muE0,
          'H': om * muH0}
    lam = {'AB': om * al, 'TB': om * be, 'DT': om * be, 'ED': om * de,
           'GA': om, 'HG': om, 'HE': om * ep}
    return mu, lam


def corners():
    return {'A': (X1, Y), 'B': (X2, Y + 2), 'D': (X3, Y3), 'E': (X4, Y4),
            'H': frame(H1, H2)}


def contacts(z, eta):
    """The seven contacts (i, j, normal n from i to j, a point of contact)."""
    lo, hi = max(X1 - 1, X2 - 1), min(X1, X2)
    tb = (max(Y + 1, z - 0.5) + min(Y + 2, z + 0.5)) / 2
    dt = (max(Y3 - 1, z - 0.5) + min(Y3, z + 0.5)) / 2
    ed = (max(X3, X4) + min(X3 + 1, X4 + 1)) / 2
    hg = (max(H2, H2 + eta) + min(H2 + 1, H2 + eta + 1)) / 2
    return {'AB': ('A', 'B', F0, ((lo + hi) / 2, Y + 1)),
            'TB': ('T', 'B', E0, (X2 - 1, tb)),
            'DT': ('D', 'T', E0, (X3 + 1, dt)),
            'ED': ('E', 'D', F0, (ed, Y3 - 1)),
            'GA': ('G', 'A', E_T, (X1 - 1, Y)),
            'HG': ('H', 'G', E_T, frame(H1 + 1, hg)),
            'HE': ('H', 'E', F_T, (X4 + 1, Y4))}


def draw_squares(f, model, roles, labels=True, size=15):
    for k, (c, deg) in zip(roles, model):
        f.square(c, deg, fill=ROLE_FILL.get(k, GREY),
                 stroke=ROLE_COLOR.get(k, FAINT), width=1.4)
        if labels:
            f.text(c, k, size=size, color=ROLE_COLOR.get(k, INK))


def forces():
    mu, lam = weights()
    assert abs(sum(mu.values()) - 1) < 1e-12
    assert all(v > 0 for v in mu.values()) and all(v > 0 for v in lam.values())
    # the values quoted after Lemma J.6
    for k, v in (('A', 0.2097), ('B', 0.2212), ('D', 0.2734), ('E', 0.0251),
                 ('H', 0.2706)):
        assert abs(mu[k] - v) < 6e-5
    for k, v in (('AB', 0.4774), ('TB', 0.7336), ('DT', 0.7336),
                 ('ED', 0.7954), ('HE', 0.7740), ('GA', 0.7403),
                 ('HG', 0.7403)):
        assert abs(lam[k] - v) < 6e-5
    z, eta = 1.35, -0.32
    model = [placed(c) for c in eight_model(0.14, 0.0, 0.1, z, eta)]
    roles = ['A', 'B', 'D', 'E', 'H', 'T', 'G', 'K']
    P = corners()
    for k in P:
        assert abs(dot(P[k], P[k]) - Q8) < 1e-9
    cts = contacts(z, eta)
    # the contact forces on each square: lam n on j, -lam n on i
    total = {k: (0.0, 0.0) for k in 'ABDEHTG'}
    for e, (i, j, n, pt) in cts.items():
        total[j] = add(total[j], mul(lam[e], n))
        total[i] = add(total[i], mul(-lam[e], n))
    # Lemma M.3 and (J.2): they balance the corner forces -2 mu_P P_P
    for k in 'ABDEH':
        assert norm(sub(total[k], mul(2 * mu[k], P[k]))) < 1e-9
    assert norm(total['T']) < 1e-12 and norm(total['G']) < 1e-12
    # each contact point lies on both closed squares
    sq = dict(zip(roles, model))

    def in_closed(p, c, deg):
        t = math.radians(deg)
        d = sub(p, c)
        a = math.cos(t) * d[0] + math.sin(t) * d[1]
        b = -math.sin(t) * d[0] + math.cos(t) * d[1]
        return abs(a) <= 0.5 + 1e-9 and abs(b) <= 0.5 + 1e-9
    for e, (i, j, n, pt) in cts.items():
        assert in_closed(pt, *sq[i]) and in_closed(pt, *sq[j]), e
    f = Figure(-2.25, 2.25, -2.12, 2.12, 165)
    f.circle((0, 0), R8, stroke=FAINT, width=1.2)
    draw_squares(f, model[:7], roles[:7])
    f.square(model[7][0], model[7][1], fill=GREY, stroke=FAINT, width=1.2)
    core_disk(f)
    origin(f, dx=0.05, dy=-0.07)
    k = 0.42
    for key, p in P.items():
        tip = add(p, mul(-2 * mu[key] * k, p))
        if key == 'E':
            arrow(f, p, add(p, mul(-0.05 / norm(p), p)), color=INK, width=1.6,
                  size=7)
        else:
            arrow(f, p, tip, color=INK, width=1.8)
        f.dot(p, r=3.2, fill=RED)
        out = mul(1 + 0.09 / norm(p), p)
        halo_text(f, out, sb(it('μ'), key, '', 13), size=13)
    for e, (i, j, n, pt) in cts.items():
        a = add(pt, mul(k * lam[e], n))
        b = add(pt, mul(-k * lam[e], n))
        arrow(f, pt, a, color=ROLE_COLOR[j], width=1.6, size=8)
        arrow(f, pt, b, color=ROLE_COLOR[i], width=1.6, size=8)
        f.dot(pt, r=2.4)
    label_at = {'AB': (0.12, 0.07), 'TB': (0.04, 0.17), 'DT': (0.02, 0.17),
                'ED': (0.04, -0.13), 'GA': (0.15, -0.07), 'HG': (0.02, -0.17),
                'HE': (-0.19, 0.0)}
    for e, (i, j, n, pt) in cts.items():
        halo_text(f, add(pt, label_at[e]), sb(it('λ'), e, '', 12), size=12)
    f.save('appendix-m/forces', 'The weights of the dual as forces on the '
           'optimal packing: at the five corners on the circle, forces towards '
           'o labelled with the weights mu, and at the seven contacts, pairs '
           'of opposite forces labelled with the weights lambda')


def sliders():
    zmin, zmax = 7 / 12, math.sqrt(Q8 - (X2 - 1) ** 2) - 0.5
    emin = -H2 - math.sqrt(Q8 - (H1 + 2) ** 2)
    emax = -H2 - 13 / 12
    assert abs(zmax - 1.366) < 5e-4 and abs(emin + 0.445) < 5e-4
    # T at its ends touches the core disk and the circle
    assert abs((zmin - 0.5) - 1 / 12) < 1e-12 and X2 - 2 < 0 < X2 - 1
    assert abs((X2 - 1) ** 2 + (zmax + 0.5) ** 2 - Q8) < 1e-12
    # G at its ends touches the core disk and the circle
    assert abs(-(H2 + 1 + emax) - 1 / 12) < 1e-12 and H1 + 1 < 0 < H1 + 2
    assert abs((H1 + 2) ** 2 + (H2 + emin) ** 2 - Q8) < 1e-12
    lo = [placed(c) for c in eight_model(0.14, 0.0, 0.1, zmin, emin)]
    hi = [placed(c) for c in eight_model(0.14, 0.0, 0.1, zmax, emax)]
    f = Figure(-2.25, 2.25, -2.12, 2.12, 165)
    f.circle((0, 0), R8, stroke=FAINT, width=1.2)
    roles = ['A', 'B', 'D', 'E', 'H']
    draw_squares(f, lo[:5], roles)
    for m, dash in ((lo, '5 3'), (hi, '2 3')):
        for k, (c, deg) in zip(['T', 'G'], m[5:7]):
            f.square(c, deg, fill=ROLE_FILL[k], stroke=ROLE_COLOR[k],
                     width=1.3, dash=dash, opacity=0.55)
    for k, a, b in (('T', lo[5][0], hi[5][0]), ('G', lo[6][0], hi[6][0])):
        f.line(a, b, stroke=ROLE_COLOR[k], width=3.2)
        f.dot(a, r=3.2, fill=ROLE_COLOR[k])
        f.dot(b, r=3.2, fill=ROLE_COLOR[k])
    halo_text(f, add(lo[5][0], (0.0, -0.17)),
              it('Z') + NB + '=' + NB + '7/12', size=12)
    mid_t = mul(0.5, add(lo[5][0], hi[5][0]))
    mid_g = mul(0.5, add(lo[6][0], hi[6][0]))
    halo_text(f, add(mid_t, (0.14, 0.0)), 'T', size=15, color=CYAN,
              italic=True, anchor='start')
    halo_text(f, add(mid_g, (0.14, 0.0)), 'G', size=15, color=YELLOW,
              italic=True, anchor='start')
    halo_text(f, add(hi[5][0], (0.0, 0.16)),
              sb(it('z'), 'max', '', 12), size=12)
    halo_text(f, add(lo[6][0], (-0.16, 0.05)), sb(it('η'), 'min', '', 12),
              size=12, anchor='end')
    halo_text(f, add(hi[6][0], (0.05, 0.14)), sb(it('η'), 'max', '', 12),
              size=12, anchor='start')
    core_disk(f)
    origin(f, dx=0.05, dy=-0.07)
    for p in corners().values():
        f.dot(p, r=3.4, fill=RED)
    f.save('appendix-m/sliders', 'The five fixed squares with their corners on '
           'the circle, and the two sliders T and G at their extreme '
           'positions, where they touch the core disk or the circle, with the '
           'segments of their centres')


def main():
    forces()
    sliders()


if __name__ == '__main__':
    main()

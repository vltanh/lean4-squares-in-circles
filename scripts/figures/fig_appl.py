#!/usr/bin/env python3
"""Draw the figures of Appendix L (eight squares: the exact polynomial checks)
as SVG files in docs/proof/figures/appendix-l/.

    python3 scripts/figures/fig_appl.py

The regions of Lemma L.5 are the images of a grid of the square under the
three substitutions; the polynomial N of Section L.5 is built from its formula
in exact rational arithmetic, centred on its interval, and expanded in the
Chebyshev basis by the formula of Lemma L.1. Each drawing asserts the facts its
caption states.
"""
import math
from fractions import Fraction as Fr

from proof_figures import Figure, Graph, INK, FAINT, COLORS, FILLS, sb
from fig_front import it, NB, polyline
from fig_appj import halo_text, origin

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
EPS = 1e-12


def shift_pt(p, v):
    return (p[0] + v[0], p[1] + v[1])


# ------------------------------------------------- the regions of Lemma L.5

def rectangle_map(a, b):
    return lambda U, V: (a * U, b * V)


def triangle_map(d):
    return lambda U, V: (d * U * (1 - V), d * U * V)


def trapezoid_map(l, d):
    return lambda U, V: (d * U, (l + d * U) * V)


def preimage_ok(fmap, inside, box, n=40):
    """Every point of a grid of the region is the image of a point of
    [0, 1]^2, found by bisection along the lines of constant U."""
    x0, x1, y0, y1 = box
    for i in range(n + 1):
        for j in range(n + 1):
            p = (x0 + (x1 - x0) * i / n, y0 + (y1 - y0) * j / n)
            if not inside(p):
                continue
            best = min(math.hypot(fmap(U / 200, V / 200)[0] - p[0],
                                  fmap(U / 200, V / 200)[1] - p[1])
                       for U in range(201) for V in range(0, 201, 4))
            if best > 0.03:
                return False
    return True


def regions():
    panels = [
        ('rectangle', rectangle_map(1.3, 0.9),
         lambda p: -EPS <= p[0] <= 1.3 + EPS and -EPS <= p[1] <= 0.9 + EPS,
         [(0, 0), (1.3, 0), (1.3, 0.9), (0, 0.9)], (0, 1.3, 0, 0.9)),
        ('triangle', triangle_map(1.3),
         lambda p: p[0] >= -EPS and p[1] >= -EPS and p[0] + p[1] <= 1.3 + EPS,
         [(0, 0), (1.3, 0), (0, 1.3)], (0, 1.3, 0, 1.3)),
        ('trapezoid', trapezoid_map(0.45, 1.0),
         lambda p: -EPS <= p[0] <= 1.0 + EPS and -EPS <= p[1] <= 0.45 + p[0] + EPS,
         [(0, 0), (1.0, 0), (1.0, 1.45), (0, 0.45)], (0, 1.0, 0, 1.45)),
    ]
    f = Figure(-0.25, 6.0, -0.45, 1.65, 150)
    offsets = [0.0, 2.05, 4.3]
    names = ['(' + it('aU') + ',' + NB + it('bV') + ')',
             '(' + it('dU') + '(1' + NB + '−' + NB + it('V') + '),' + NB
             + it('dUV') + ')',
             '(' + it('dU') + ',' + NB + '(' + it('l') + NB + '+' + NB
             + it('dU') + ')' + it('V') + ')']
    n = 10
    for (name, fmap, inside, outline, box), ox, label in zip(panels, offsets,
                                                             names):
        # the images lie in the region, and the corners of the square map to
        # its vertices
        for i in range(n + 1):
            for j in range(n + 1):
                assert inside(fmap(i / n, j / n))
        assert preimage_ok(fmap, inside, box, n=12)
        at = lambda p: (ox + p[0], p[1])
        f.polygon([at(p) for p in outline], fill=FILLS[0], stroke='none')
        for i in range(n + 1):
            pts = [at(fmap(i / n, j / 60)) for j in range(61)]
            polyline(f, pts, stroke=BLUE, width=1.0)
            pts = [at(fmap(j / 60, i / n)) for j in range(61)]
            polyline(f, pts, stroke=ORANGE, width=1.0)
        f.polygon([at(p) for p in outline], stroke=INK, width=1.4)
        origin(f, at((0, 0)), dx=-0.12, dy=-0.06)
        f.text(at((box[1] / 2, -0.3)), label, size=13, italic=False)
    # the side U = 0 of the square collapses to the vertex o of the triangle
    tri = triangle_map(1.3)
    assert all(tri(0, j / 10) == (0.0, 0.0) for j in range(11))
    f.save('appendix-l/regions', 'The images of a grid of the square under '
           'the three substitutions of Lemma L.5: a rectangle, a triangle '
           'whose side U = 0 collapses to o, and a trapezoid')


# ------------------------------------------------ the worked example of L.5

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


def ppow(a, n):
    out = [Fr(1)]
    for _ in range(n):
        out = pmul(out, a)
    return out


def peval(a, x):
    out = 0
    for c in reversed(a):
        out = out * x + c
    return out


def certificate():
    """N of Section L.5, from its formula."""
    X = [Fr(0), Fr(1)]
    one = [Fr(1)]
    C = lambda q: [Fr(q)]
    Rlo, Rhi = Fr(19787, 10000), Fr(4947, 2500)
    Zlo, Plo, Phi = Fr(981, 500), Fr(3991, 10000), Fr(3993, 10000)
    S3 = padd(X, pscale(Fr(-1, 6), ppow(X, 3)))
    S5 = padd(S3, pscale(Fr(1, 120), ppow(X, 5)))
    C2 = padd(one, pscale(Fr(-1, 2), ppow(X, 2)))
    C4 = padd(C2, pscale(Fr(1, 24), ppow(X, 4)))
    Ylo = padd(pmul(padd(C(Zlo), pscale(-1, C4)), S3), pscale(Plo, C2))
    Yhi = padd(pmul(padd(C(Rhi), pscale(-1, C2)), S5), pscale(Phi, C4))
    Xlo = padd(padd(pscale(Zlo, C2), pscale(-Phi, S5)), pmul(S3, S3))
    Xhi = padd(padd(pscale(Rhi, C4), pscale(-Plo, S3)), pmul(S5, S5))
    Alo = padd(one, pscale(-1 / Zlo, C4))
    Llo = padd(C(Fr(1103, 625)), pscale(-1, Yhi))
    inner = padd(pmul(Llo, Xhi), pscale(Rhi, pmul(Ylo, Alo)))
    N = padd(pscale(Rlo, pmul(pmul(Xlo, Alo), inner)),
             pscale(-Rhi, pmul(pmul(Xhi, Xhi), S5)))
    while N and N[-1] == 0:
        N.pop()
    return N, dict(Ylo=Ylo, Yhi=Yhi, Xlo=Xlo, Xhi=Xhi, Alo=Alo, Llo=Llo)


def monomial_coefficient(i, j):
    """gamma_ij of Lemma L.1: the coefficient of T_j in u^i."""
    if j <= i and (i - j) % 2 == 0:
        return Fr(1 if j == 0 else 2) * math.comb(i, (i - j) // 2) / 2 ** i
    return Fr(0)


def chebyshev(p, a, b):
    """The Chebyshev coefficients c_j of p on [a, b]."""
    cen = [Fr(0)]
    for c in reversed(p):
        cen = padd(pmul(cen, [(a + b) / 2, (b - a) / 2]), [c])
    D = len(p) - 1
    cen = cen[:D + 1]
    return [sum(cen[i] * monomial_coefficient(i, j) for i in range(D + 1))
            for j in range(D + 1)]


def example():
    a, b = Fr(11, 50), Fr(7, 10)
    N, factors = certificate()
    assert len(N) - 1 == 27
    cheb = chebyshev(N, a, b)
    lower = cheb[0] - sum(abs(x) for x in cheb[1:])
    # the check of Theorem L.3 at rho = 8179/10000
    assert lower > Fr(8179, 10000)
    assert abs(float(cheb[0]) - 2.23622) < 1e-5
    assert abs(float(sum(abs(x) for x in cheb[1:])) - 1.41830) < 1e-5
    assert abs(abs(float(cheb[1])) - 1.22176) < 1e-5
    assert abs(abs(float(cheb[2])) - 0.19456) < 1e-5
    assert max(abs(x) for x in cheb[3:]) < Fr(16, 10000)
    assert 0 < abs(cheb[27]) < Fr(1, 10 ** 34)
    # the six envelopes are positive at degree 10 by the same bound
    for poly in factors.values():
        assert len(poly) - 1 <= 10
        cf = chebyshev(poly, a, b)
        assert cf[0] - sum(abs(x) for x in cf[1:]) > 0
    xs = [a + (b - a) * Fr(k, 200) for k in range(201)]
    vals = [peval(N, x) for x in xs]
    assert all(v > lower for v in vals)
    vmin = min(vals)
    assert vals.index(vmin) == 200 and abs(float(vmin) - 1.2076) < 1e-4
    assert abs(float(vals[0]) - 3.6545) < 1e-4
    f = Figure(-0.3, 8.4, -0.5, 3.15, 100)
    g = Graph(f, 3.3 / float(b - a), 2.6 / 4.0, x0=float(a), y0=0.0,
              dx=0.75, dy=0.15)
    g.x_axis(float(a), float(b) + 0.03,
             ticks=[(0.22, '11/50'), (0.3, '0.3'), (0.4, '0.4'), (0.5, '0.5'),
                    (0.6, '0.6'), (0.7, '7/10')], label=it('p'))
    g.y_axis(0, 4.0, x=float(a), ticks=[(1, '1'), (2, '2'), (3, '3')])
    g.polyline([(float(x), float(v)) for x, v in zip(xs, vals)], stroke=BLUE,
               width=2.2)
    g.line((float(a), float(lower)), (float(b), float(lower)), stroke=ORANGE,
           width=1.6, dash='6 4')
    g.dot((float(b), float(vmin)), r=3)
    g.text((float(b) - 0.01, float(vmin) + 0.28), '1.21', size=12,
           italic=False, anchor='end')
    halo_text(f, g.q(0.32, float(lower) - 0.3),
              sb(it('c'), '0', NB + '−' + NB + 'Σ' + NB + '|', 13)
              + sb(it('c'), it('j'), '|' + NB + '≈' + NB + '0.818', 13),
              size=13, color=ORANGE, anchor='start')
    g.text((0.33, 3.6), it('N') + '(' + it('p') + ')', size=15, italic=False,
           anchor='start')
    # right panel: log10 |b_j|
    h = Graph(f, 2.7 / 29, 2.6 / 36, x0=-1, y0=-35, dx=5.25, dy=0.15)
    h.x_axis(-1, 29, y=-35, ticks=[(0, '0'), (5, '5'), (10, '10'),
                                   (15, '15'), (20, '20'), (25, '25')],
             label=it('j'))
    h.y_axis(-35, 1.0, x=-1, ticks=[(0, '1'), (-10, '10⁻¹⁰'),
                                    (-20, '10⁻²⁰'), (-30, '10⁻³⁰')])
    for j, c in enumerate(cheb):
        if c == 0:
            continue
        v = math.log10(abs(float(c)))
        h.line((j, -35), (j, v), stroke=FAINT, width=1)
        h.dot((j, v), r=2.6, fill=BLUE if j else INK)
    h.text((14, 0.8), '|' + sb(it('c'), it('j'), '|', 14), size=14,
           italic=False)
    f.save('appendix-l/example', 'The polynomial N of degree 27 on '
           '[11/50, 7/10] above its Chebyshev bound 0.818, and its Chebyshev '
           'coefficients on a logarithmic scale')


def main():
    regions()
    example()


if __name__ == '__main__':
    main()

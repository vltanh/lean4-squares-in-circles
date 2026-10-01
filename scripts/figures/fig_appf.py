#!/usr/bin/env python3
"""Draw the figures of Appendix F (docs/proof/appendix-f.md), the marker arc
of seven squares, in docs/proof/figures/appendix-f/.

    python3 scripts/figures/fig_appf.py

Every curve is sampled from the function it shows, and every point is
computed from the formulas of the appendix.
"""
import math

from proof_figures import Figure, INK, FAINT, COLORS, FILLS, sb, shift, u
from fig_appa import Plot, x_axis, y_axis, vtick

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
HALF_WIDTH = 1 / 2
TARGET = 13 / 4


def label(a, uu):
    side = math.pi / 6 + (uu - 0.5) / 3 + 3 * (1 - a) / 4
    return min(1.25 * uu, side, math.pi / 4)


def admissible(a, uu):
    return 0.5 <= a and 0 <= uu <= a and (a + 0.5) ** 2 + (uu + 0.5) ** 2 <= TARGET


def marker_arc():
    states = [(1.0, 0.5, '(1, ½)'), (0.9, 0.3, '(0.9, 0.3)')]
    panel = 2.15
    f = Figure(-0.3, panel + 1.72, -1.02, 1.3, 150)
    for k, (a, uu, name) in enumerate(states):
        assert admissible(a, uu)
        o = (k * panel, 0.0)
        ell = label(a, uu)
        lo, hi = ell - HALF_WIDTH, ell + HALF_WIDTH
        # The part of the circle in the closed square, and the arc inside it.
        enter = max(math.asin(uu - 0.5), -math.acos(a - 0.5))
        leave = min(math.acos(a - 0.5), math.asin(min(1.0, uu + 0.5)))
        assert enter < lo and hi < leave
        for j in range(201):
            t = lo + (hi - lo) * j / 200
            assert abs(math.cos(t) - a) <= 0.5 and abs(math.sin(t) - uu) <= 0.5
        c = shift(o, (a, uu))
        f.line(shift(o, (-0.25, 0)), shift(o, (1.7, 0)), stroke=FAINT, width=1)
        f.text(shift(o, (1.7, 0)), 't = 0', size=12, italic=False,
               anchor='end', color=FAINT, dy=11)
        f.square(c, fill=FILLS[0], stroke=BLUE)
        for x0, y0, x1, y1 in ((a - 0.5, -0.98, a - 0.5, 1.12),
                               (a + 0.5, -0.98, a + 0.5, 1.12),
                               (-0.25, uu - 0.5, 1.7, uu - 0.5),
                               (-0.25, uu + 0.5, 1.7, uu + 0.5)):
            f.line(shift(o, (x0, y0)), shift(o, (x1, y1)), width=1, dash='4 4')
        f.text(shift(o, (a - 0.5, -0.98)), 'near', size=12, italic=False,
               anchor='end', dx=-4, dy=4)
        f.text(shift(o, (a + 0.5, -0.98)), 'far', size=12, italic=False,
               anchor='start', dx=4, dy=4)
        f.text(shift(o, (-0.25, uu - 0.5)), 'lower', size=12, italic=False,
               anchor='start', dy=-9)
        f.text(shift(o, (-0.25, uu + 0.5)), 'upper', size=12, italic=False,
               anchor='start', dy=-9)
        f.arc(o, 1.0, -math.pi / 2 - 0.05, math.pi / 2 + 0.3, FAINT,
              width=1.2)
        f.arc(o, 1.0, enter, leave, BLUE, width=2)
        f.arc(o, 1.0, lo, hi, ORANGE, width=5)
        for t in (enter, leave):
            f.dot(shift(o, u(t), 1.0), r=3.4, fill=BLUE)
        f.line(o, shift(o, u(ell), 1.22), width=1, dash='3 3', arrow=True)
        f.text(shift(o, u(ell), 1.3), 'ℓ', size=16)
        for t in (lo, hi):
            f.line(o, shift(o, u(t), 1.0), stroke=ORANGE, width=1)
        f.arc(o, 0.3, ell, hi, INK, width=1.2)
        f.dot(c, fill=BLUE)
        f.text(shift(o, (a, uu + 0.5)), '(a, u) = ' + name, size=13,
               color=BLUE, dy=-10)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.07)), 'o', anchor='end')
        f.text(shift(o, (-0.16, -0.92)), sb('Γ', '1', size=16), size=16,
               color=FAINT)
    f.save('appendix-f/marker-arc', 'Two admissible squares in their charts, with '
           'the lines of their four edges and the arc of the unit circle of '
           'half-width 1/2 about the label; left the side state (1, 1/2), '
           'whose arc nearly fills the part of the circle inside the square, '
           'right the state (0.9, 0.3), with an axial label')


def admissible_region():
    root = math.sqrt(TARGET)
    corner = math.sqrt(TARGET / 2) - 0.5
    t0, t1 = math.atan2(0.5, math.sqrt(3)), math.pi / 4
    arc = [(-0.5 + root * math.cos(t0 + (t1 - t0) * k / 80),
            -0.5 + root * math.sin(t0 + (t1 - t0) * k / 80))
           for k in range(81)]
    region = [(0.5, 0.0)] + arc + [(0.5, 0.5)]
    assert abs(arc[-1][0] - corner) < 1e-12
    for a, uu in region:
        assert (a + 0.5) ** 2 + (uu + 0.5) ** 2 <= TARGET + 1e-9
    # The line of the Cauchy-Schwarz bound, 3/4 (a + 1/2) + 2/3 (u + 1/2)
    # = sqrt(1885)/24, and the point where it touches the circle.
    L = math.sqrt(1885) / 24
    assert L < 43.42 / 24 and abs(43.42 / 24 - 43 / 24 - 0.0175) < 1e-12
    norm = math.hypot(0.75, 2 / 3)
    touch = (-0.5 + root * 0.75 / norm, -0.5 + root * (2 / 3) / norm)
    assert abs(0.75 * (touch[0] + 0.5) + (2 / 3) * (touch[1] + 0.5) - L) < 1e-12
    line_u = lambda a: (L - 0.75 * (a + 0.5)) / (2 / 3) - 0.5
    x = 0.4
    top = math.sqrt(TARGET - (x + 1) ** 2) - 0.5
    p = Plot(0.3, 1.42, -0.1, 0.98, 330, 330)
    x_axis(p, 0.35, 1.4, ticks=((0.5, '½'), (1, '1'), (math.sqrt(3) - 0.5,
                                                       '√3 − ½')), label='a')
    y_axis(p, -0.02, 0.96, x=0.35, ticks=((0.5, '½'),), label='u')
    p.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    p.curve(lambda a: math.sqrt(max(0.0, TARGET - (a + 0.5) ** 2)) - 0.5,
            0.36, math.sqrt(3) - 0.5, ylim=(-0.02, 0.96), stroke=BLUE,
            width=1, dash='4 3')
    p.line((0.62, line_u(0.62)), (1.12, line_u(1.12)), stroke=ORANGE,
           width=1.6)
    p.dot(touch, fill=ORANGE)
    p.line((x + 0.5, 0), (x + 0.5, top), stroke=GREEN, width=2.4)
    p.dot((x + 0.5, top), fill=GREEN)
    p.dot((1.0, 0.5), fill=INK)
    p.text((1.0, 0.5), '(1, ½)', size=13, italic=False, anchor='start',
           dx=7, dy=4)
    p.text((1.17, 0.26), 'φ = 13/4', size=13, color=BLUE, anchor='start')
    p.text((0.7, line_u(0.7)), 'Cauchy–Schwarz', size=13, italic=False,
           color=ORANGE, anchor='start', dx=10, dy=-6)
    p.text((x + 0.5, top / 2), 'a = x + ½', size=13, color=GREEN,
           anchor='end', dx=-6)
    p.text((0.66, 0.2), 'admissible', size=13, italic=False, color=BLUE)
    p.save('appendix-f/admissible', 'The admissible states in the (a, u)-plane: '
           'a at least 1/2, u between 0 and a, and phi at most 13/4. The line '
           'of the Cauchy-Schwarz bound passes just outside the disk, and at '
           'a = x + 1/2 the circle bounds u')


# A line against the arcsine (Lemma F.1).

def asin_line():
    g = lambda y: 1.25 * y - math.asin(max(-1.0, min(1.0, y)))
    p = Plot(-1.12, 1.18, -0.42, 0.4, 220, 480)
    # The ranges used by the two transverse edges.
    y1, y2 = -0.5, 11 / 40
    p.polygon([(y1, -0.35), (y2, -0.35), (y2, 0.35), (y1, 0.35)],
              fill=FILLS[1], stroke='none', opacity=0.55)
    p.polygon([(0.5, -0.35), (1, -0.35), (1, 0.35), (0.5, 0.35)],
              fill=FILLS[2], stroke='none', opacity=0.55)
    x_axis(p, -1.08, 1.15, ticks=((-1, '−1'), (-0.6, '−3/5'), (-0.5, ''),
                                  (0.6, '3/5'), (1, '1')), label='y')
    p.line((0, -0.38), (0, 0.38), width=1, arrow=True)
    p.line((y1, g(y1)), (y2, g(y1)), stroke=ORANGE, width=1.4, dash='5 3')
    p.line((0.5, g(0.6)), (1, g(0.6)), stroke=GREEN, width=1.4, dash='5 3')
    p.curve(g, -1, 1, n=800, stroke=BLUE, width=2.4)
    p.dot((y1, g(y1)), fill=ORANGE)
    p.dot((0.6, g(0.6)), fill=GREEN)
    p.dot((-0.6, g(-0.6)), fill=BLUE)
    p.text((y1, g(y1)), 'π/6 − 5/8', size=13, italic=False, color=ORANGE,
           anchor='end', dx=-6, dy=14)
    p.text((0.6, g(0.6)), '3/4 − arcsin 3/5', size=13, italic=False,
           color=GREEN, dy=-13)
    p.text((-0.12, 0.3), 'lower edge', size=12, italic=False, color=ORANGE)
    p.text((0.75, -0.3), 'upper edge', size=12, italic=False, color=GREEN)
    p.text((-0.95, g(-0.95)), 'g', size=17, color=BLUE, anchor='start',
           dx=8, dy=-6)
    p.save('appendix-f/asin-line', 'The function g(y) = 5/4 y minus arcsin y on '
           '[-1, 1]: it increases on [-3/5, 3/5] and decreases on [3/5, 1]. '
           'On the range of the lower edge it stays above its value at -1/2; '
           'on the range of the upper edge it stays below its value at 3/5')


# The label between the transverse edges (Lemmas F.2 and F.3).

def transverse():
    umax = math.sqrt(TARGET / 2) - 0.5

    def amax(uu):
        return math.sqrt(TARGET - (uu + 0.5) ** 2) - 0.5

    n = 400
    us = [umax * k / n for k in range(n + 1)]
    low = [label(amax(uu), uu) for uu in us]
    high = [label(max(0.5, uu), uu) for uu in us]
    lower_edge = lambda uu: math.asin(uu - 0.5) + HALF_WIDTH
    upper_edge = lambda uu: math.asin(min(1.0, uu + 0.5)) - HALF_WIDTH
    # The decimal bounds of Lemmas F.2 and F.3.
    assert (11 / 40) ** 3 / 4 < 0.0052 and 3.14 / 6 - 0.0175 - 0.0052 - 0.5 > 0
    assert 11 / 40 + 0.0052 + 0.5 < 3.14 / 4
    z = 5 / 8
    assert z - z ** 3 / 6 + z ** 5 / 120 < 0.5852 < 0.6
    # Lemmas F.2 and F.3 on a grid of admissible states.
    for i in range(0, n + 1, 4):
        uu = us[i]
        for j in range(41):
            a = max(0.5, uu) + (amax(uu) - max(0.5, uu)) * j / 40
            if admissible(a, uu):
                assert lower_edge(uu) < label(a, uu)
                if uu <= 0.5:
                    assert label(a, uu) < upper_edge(uu)
    p = Plot(-0.08, 0.86, -0.16, 1.16, 440, 300)
    x_axis(p, -0.03, 0.84, ticks=((0, '0'), (0.5, '½'), (0.775, '31/40')),
           label='u')
    y_axis(p, -0.12, 1.14, ticks=((math.pi / 4, 'π/4'), (math.pi / 6, 'π/6')))
    for y in (math.pi / 4, math.pi / 6):
        p.line((0, y), (0.8, y), stroke=FAINT, width=1, dash='3 3')
    p.polygon(list(zip(us, low)) + list(zip(reversed(us), reversed(high))),
              fill=FILLS[0], stroke=BLUE, width=1.2)
    p.polyline([(x, lower_edge(x)) for x in us], stroke=ORANGE, width=2.2)
    top = [x for x in us if x <= 0.5] + [0.5]
    p.polyline([(x, upper_edge(x)) for x in top], stroke=GREEN, width=2.2)
    p.line((0.5, 0), (0.5, upper_edge(0.5)), stroke=FAINT, width=1,
           dash='3 3')
    p.text((0.6, 0.69), 'ℓ(a, u)', size=13, color=BLUE)
    p.text((0.33, 0.17), 'arcsin(u − ½) + ½', size=13,
           color=ORANGE, anchor='start')
    p.text((0.06, 1.0), 'arcsin(u + ½) − ½', size=13,
           color=GREEN, anchor='start')
    p.save('appendix-f/transverse', 'For each u, the labels of the admissible '
           'states (a, u) form the shaded interval. It lies above the curve '
           'arcsin(u - 1/2) + 1/2 of the lower edge, and for u at most '
           '1/2 below the curve arcsin(u + 1/2) - 1/2 of the upper edge')


# The envelope (Definition F.4 and Lemmas F.5 to F.7).

def envelope(x):
    return (1 / 24 + math.sqrt(TARGET - (x + 1) ** 2) / 3 + math.asin(x)
            - 0.75 * x)


def envelope_band():
    xe = math.sqrt(3) - 1
    n = 300
    xs = [xe * k / n for k in range(n + 1)]
    side_plus = lambda x, uu: (uu - 0.5) / 3 + 0.75 * (0.5 - x) + math.asin(x)

    def umax(x):
        a = x + 0.5
        return min(a, math.sqrt(TARGET - (x + 1) ** 2) - 0.5)

    low = [side_plus(x, 0) for x in xs]
    high = [side_plus(x, umax(x)) for x in xs]
    for x, h in zip(xs, high):
        assert h <= envelope(x) + 1e-12
    level = math.pi / 3 - HALF_WIDTH
    p = Plot(-0.06, 0.84, 0.1, 0.64, 470, 620)
    x_axis(p, -0.03, 0.82, y=0.13, ticks=((0, '0'), (0.25, '¼'), (0.5, '½'),
                                          (0.75, '¾')), label='x')
    p.line((xe, 0.13), (xe, high[-1]), stroke=FAINT, width=1, dash='3 3')
    y_axis(p, 0.13, 0.62, x=0, ticks=((0.2, '0.2'), (0.3, '0.3'),
                                      (0.4, '0.4'), (0.5, '0.5')))
    p.polygon(list(zip(xs, low)) + list(zip(reversed(xs), reversed(high))),
              fill=FILLS[0], stroke=BLUE, width=1)
    p.line((0, level), (0.78, level), stroke=INK, width=1.2, dash='6 4')
    p.text((0.78, level), 'π/3 − ½', size=13, italic=False,
           anchor='end', dy=-10)
    p.curve(envelope, 0, 0.75, stroke=ORANGE, width=2.4)
    p.text((0.66, envelope(0.66)), 'E(x) − π/6', size=14, color=ORANGE,
           anchor='start', dx=8, dy=-2)
    p.text((0.33, 0.36), 'side(a, u) + arcsin x − π/6', size=13,
           color=BLUE)
    p.save('appendix-f/envelope-band', 'For each x = a - 1/2, the values of side(a, '
           'u) + arcsin x - pi/6 over the admissible states (a, u) fill the '
           'shaded interval, which lies below the graph of E(x) - pi/6 and '
           'touches it where the disk bounds u')


def peak_bound():
    """Lemma F.5: h(x) = 9 (x + 1/8)^2 (9 - 7x)^3 rises on [0, 123/280],
    falls on [123/280, 3/4], and its peak is below 676."""
    h = lambda x: 9 * (x + 1 / 8) ** 2 * (9 - 7 * x) ** 3
    dh = lambda x: 9 * (x + 1 / 8) * (9 - 7 * x) ** 2 * (123 / 8 - 35 * x)
    c, w = 123 / 280, 0.75
    for k in range(301):
        x = w * k / 300
        assert (dh(x) >= 0) == (x <= c) or abs(x - c) < 1e-12
        assert h(x) <= h(c) < 9 * 6 ** 3 / 3 == 648 < 676
    assert (c + 1 / 8) ** 2 < (4 / 7) ** 2 < 1 / 3 and 9 - 7 * c < 6
    pl = Plot(-0.07, 0.86, -40, 760, 560, 0.42)
    pl.polygon([(0, 0), (c, 0), (c, 735), (0, 735)], fill=FILLS[2],
               stroke='none', opacity=0.55)
    pl.polygon([(c, 0), (w, 0), (w, 735), (c, 735)], fill=FILLS[1],
               stroke='none', opacity=0.55)
    x_axis(pl, -0.03, 0.84, ticks=((0, '0'), (w, '¾')), label='x')
    vtick(pl, c, 0, '123/280')
    y_axis(pl, 0, 745, ticks=((200, '200'), (400, '400'), (676, '676')))
    pl.line((0, 676), (0.8, 676), stroke=INK, width=1.3, dash='6 4')
    pl.line((0, h(c)), (c, h(c)), stroke=FAINT, width=1, dash='3 3')
    pl.line((c, 0), (c, h(c)), stroke=FAINT, width=1, dash='3 3')
    pl.curve(h, 0, w, stroke=BLUE, width=2.4)
    pl.dot((c, h(c)), fill=BLUE)
    pl.text((c, h(c)), f'h(123/280) ≈ {h(c):.1f}', size=13, italic=False,
            color=BLUE, dy=-14)
    pl.text((0.12, h(0.12)), 'h', size=17, color=BLUE, anchor='end', dx=-8,
            dy=-6)
    pl.text((c / 2, 40), "h′ ≥ 0", size=14, color=GREEN)
    pl.text(((c + w) / 2, 40), "h′ ≤ 0", size=14, color=ORANGE)
    pl.save('appendix-f/peak-bound', 'The function h(x) = 9 (x + 1/8) squared '
            '(9 - 7x) cubed on [0, 3/4]: it increases up to x = 123/280, '
            'where its derivative changes sign, and decreases after it; its '
            'peak, about 596.1, is below 676')


def envelope_parabola():
    """Lemma F.7: the envelope minus pi/6 below the parabola with its value
    13/24 and slope 1/36 at 0 and curvature -1/8, whose top 353/648 at 2/9 is
    below the level pi/3 - 1/2 of Lemma F.8."""
    par = lambda x: 13 / 24 + x / 36 - x * x / 16
    top = 353 / 648
    slope = 1 - 0.75 - 1 / (3 * math.sqrt(TARGET - 1))
    assert abs(envelope(0) - 13 / 24) < 1e-12 and abs(slope - 1 / 36) < 1e-12
    assert abs(par(2 / 9) - top) < 1e-12
    level = math.pi / 3 - HALF_WIDTH
    for k in range(301):
        x = 0.75 * k / 300
        assert envelope(x) <= par(x) + 1e-12 and par(x) <= top < level
    pl = Plot(-0.07, 0.86, 0.462, 0.557, 520, 4000)
    x_axis(pl, -0.02, 0.84, y=0.466, ticks=((0, '0'), (0.75, '¾')),
           label='x')
    vtick(pl, 2 / 9, 0.466, '2/9')
    y_axis(pl, 0.466, 0.555, x=0, ticks=((0.48, '0.48'), (0.5, '0.50'),
                                         (0.52, '0.52'), (top, '353/648')))
    pl.line((0, level), (0.8, level), stroke=INK, width=1.3)
    pl.text((0.8, level), 'π/3 − ½', size=13, italic=False,
            anchor='end', dy=-10)
    pl.line((0, top), (2 / 9, top), stroke=FAINT, width=1, dash='3 3')
    pl.line((2 / 9, 0.466), (2 / 9, top), stroke=FAINT, width=1, dash='3 3')
    pl.curve(par, 0, 0.75, stroke=PURPLE, width=1.8, dash='7 4')
    pl.curve(envelope, 0, 0.75, stroke=ORANGE, width=2.4)
    pl.dot((2 / 9, top), fill=PURPLE)
    pl.dot((0, envelope(0)), fill=INK)
    pl.text((0.555, 0.5225), '13/24 + x/36 − x²/16', size=13,
            color=PURPLE, anchor='start')
    pl.text((0.5, envelope(0.5)), 'E(x) − π/6', size=14, color=ORANGE,
            anchor='end', dx=-12, dy=10)
    pl.save('appendix-f/parabola', 'The envelope minus pi/6 on [0, 3/4] below the '
            'parabola 13/24 + x/36 - x squared/16, which has the same value '
            'and slope at 0 and is highest, at 353/648, at x = 2/9; the level '
            'pi/3 - 1/2 lies above both')


def main():
    admissible_region()
    marker_arc()
    asin_line()
    transverse()
    envelope_band()
    peak_bound()
    envelope_parabola()


if __name__ == '__main__':
    main()

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
from fig_front import it, NB

BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
HALF_WIDTH = 1 / 2
TARGET = 13 / 4


def label(a, b):
    side = math.pi / 6 + (b - 0.5) / 3 + 3 * (1 - a) / 4
    return min(1.25 * b, side, math.pi / 4)


def admissible(a, b):
    return 0.5 <= a and 0 <= b <= a and (a + 0.5) ** 2 + (b + 0.5) ** 2 <= TARGET


def marker_arc():
    states = [(1.0, 0.5, '(1,' + NB + '½)'), (0.9, 0.3, '(0.9,' + NB + '0.3)')]
    panel = 2.5
    left = -0.55                         # where the edge lines start
    f = Figure(left - 0.05, panel + 1.72, -1.02, 1.3, 150)
    for k, (a, b, name) in enumerate(states):
        assert admissible(a, b)
        o = (k * panel, 0.0)
        ell = label(a, b)
        lo, hi = ell - HALF_WIDTH, ell + HALF_WIDTH
        # The part of the circle in the closed square, and the arc inside it.
        enter = max(math.asin(b - 0.5), -math.acos(a - 0.5))
        leave = min(math.acos(a - 0.5), math.asin(min(1.0, b + 0.5)))
        assert enter < lo and hi < leave
        for j in range(201):
            t = lo + (hi - lo) * j / 200
            assert abs(math.cos(t) - a) <= 0.5 and abs(math.sin(t) - b) <= 0.5
        c = shift(o, (a, b))
        f.line(shift(o, (left, 0)), shift(o, (1.7, 0)), stroke=FAINT, width=1)
        f.text(shift(o, (1.7, 0)), it('t') + NB + '=' + NB + '0', size=13,
               italic=False, anchor='end', color=FAINT, dy=12)
        f.square(c, fill=FILLS[0], stroke=BLUE)
        for x0, y0, x1, y1 in ((a - 0.5, -0.98, a - 0.5, 1.12),
                               (a + 0.5, -0.98, a + 0.5, 1.12),
                               (left, b - 0.5, 1.7, b - 0.5),
                               (left, b + 0.5, 1.7, b + 0.5)):
            f.line(shift(o, (x0, y0)), shift(o, (x1, y1)), width=1, dash='4 4')
        f.text(shift(o, (a - 0.5, -0.98)), 'near', size=13, italic=False,
               anchor='start', dx=4, dy=4)
        f.text(shift(o, (a + 0.5, -0.98)), 'far', size=13, italic=False,
               anchor='start', dx=4, dy=4)
        f.text(shift(o, (left, b - 0.5)), 'lower', size=13, italic=False,
               anchor='start', dy=-9)
        f.text(shift(o, (left, b + 0.5)), 'upper', size=13, italic=False,
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
        half = shift(o, u(ell + HALF_WIDTH / 2), 0.4)
        assert half[0] + 0.03 < o[0] + a - 0.5            # left of the near edge
        f.text(half, '½', size=14, italic=False)
        f.dot(c, fill=BLUE)
        f.text(shift(o, (a + 0.45, b + 0.5)), '(' + it('a') + ',' + NB
               + it('b') + ')' + NB + '=' + NB + name, size=13, italic=False,
               color=BLUE, anchor='end', dy=-10)
        f.dot(o)
        f.text(shift(o, (0.03, -0.08)), 'o', anchor='start')
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
    for a, b in region:
        assert (a + 0.5) ** 2 + (b + 0.5) ** 2 <= TARGET + 1e-9
    # The line of the Cauchy-Schwarz bound, 3/4 (a + 1/2) + 2/3 (b + 1/2)
    # = sqrt(1885)/24, and the point where it touches the circle.
    L = math.sqrt(1885) / 24
    assert L < 43.42 / 24 and abs(43.42 / 24 - 43 / 24 - 0.0175) < 1e-12
    norm = math.hypot(0.75, 2 / 3)
    touch = (-0.5 + root * 0.75 / norm, -0.5 + root * (2 / 3) / norm)
    assert abs(0.75 * (touch[0] + 0.5) + (2 / 3) * (touch[1] + 0.5) - L) < 1e-12
    line_b = lambda a: (L - 0.75 * (a + 0.5)) / (2 / 3) - 0.5
    x = 0.4
    top = math.sqrt(TARGET - (x + 1) ** 2) - 0.5
    p = Plot(0.3, 1.42, -0.1, 0.98, 330, 330)
    x_axis(p, 0.35, 1.4, ticks=((0.5, '½'), (1, '1'), (math.sqrt(3) - 0.5,
                                                       '√3 − ½')), label='a')
    y_axis(p, -0.02, 0.96, x=0.35, ticks=((0.5, '½'),), label='b')
    p.polygon(region, fill=FILLS[0], stroke=BLUE, width=1.6)
    p.curve(lambda a: math.sqrt(max(0.0, TARGET - (a + 0.5) ** 2)) - 0.5,
            0.36, math.sqrt(3) - 0.5, ylim=(-0.02, 0.96), stroke=BLUE,
            width=1, dash='4 3')
    p.line((0.62, line_b(0.62)), (1.12, line_b(1.12)), stroke=ORANGE,
           width=1.6)
    p.dot(touch, fill=ORANGE)
    p.line((x + 0.5, 0), (x + 0.5, top), stroke=GREEN, width=2.4)
    p.dot((x + 0.5, top), fill=GREEN)
    p.dot((1.0, 0.5), fill=INK)
    p.text((1.0, 0.5), '(1, ½)', size=13, italic=False, anchor='start',
           dx=7, dy=4)
    p.text((1.17, 0.26), 'φ = 13/4', size=13, color=BLUE, anchor='start')
    p.text((0.7, line_b(0.7)), 'Cauchy–Schwarz', size=13, italic=False,
           color=ORANGE, anchor='start', dx=10, dy=-6)
    p.text((x + 0.5, top / 2), 'a = x + ½', size=13, color=GREEN,
           anchor='end', dx=-6)
    p.text((0.66, 0.2), 'admissible', size=13, italic=False, color=BLUE)
    p.save('appendix-f/admissible', 'The admissible states in the (a, b)-plane: '
           'a at least 1/2, b between 0 and a, and phi at most 13/4. The line '
           'of the Cauchy-Schwarz bound passes just outside the disk, and at '
           'a = x + 1/2 the circle bounds b')


# A line against the arcsine (Lemma F.1).

def asin_line():
    f = lambda y: 1.25 * y - math.asin(max(-1.0, min(1.0, y)))   # f of F.1
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
    p.line((y1, f(y1)), (y2, f(y1)), stroke=ORANGE, width=1.4, dash='5 3')
    p.line((0.5, f(0.6)), (1, f(0.6)), stroke=GREEN, width=1.4, dash='5 3')
    p.curve(f, -1, 1, n=800, stroke=BLUE, width=2.4)
    p.dot((y1, f(y1)), fill=ORANGE)
    p.dot((0.6, f(0.6)), fill=GREEN)
    p.dot((-0.6, f(-0.6)), fill=BLUE)
    p.text((y1, f(y1)), 'π/6 − 5/8', size=13, italic=False, color=ORANGE,
           anchor='end', dx=-6, dy=14)
    p.text((0.6, f(0.6)), '3/4 − arcsin 3/5', size=13, italic=False,
           color=GREEN, dy=-13)
    p.text((-0.26, 0.3), 'lower edge', size=13, italic=False, color=ORANGE)
    p.text((0.75, -0.3), 'upper edge', size=13, italic=False, color=GREEN)
    p.text((-0.95, f(-0.95)), 'f', size=17, color=BLUE, anchor='start',
           dx=8, dy=-6)
    p.save('appendix-f/asin-line', 'The function f(y) = 5/4 y minus arcsin y on '
           '[-1, 1]: it increases on [-3/5, 3/5] and decreases on [3/5, 1]. '
           'On the range of the lower edge it stays above its value at -1/2; '
           'on the range of the upper edge it stays below its value at 3/5')


# The label between the transverse edges (Lemmas F.2 and F.3).

def transverse():
    bmax = math.sqrt(TARGET / 2) - 0.5

    def amax(b):
        return math.sqrt(TARGET - (b + 0.5) ** 2) - 0.5

    n = 400
    bs = [bmax * k / n for k in range(n + 1)]
    low = [label(amax(b), b) for b in bs]
    high = [label(max(0.5, b), b) for b in bs]
    lower_edge = lambda b: math.asin(b - 0.5) + HALF_WIDTH
    upper_edge = lambda b: math.asin(min(1.0, b + 0.5)) - HALF_WIDTH
    # The decimal bounds of Lemmas F.2 and F.3.
    assert (11 / 40) ** 3 / 4 < 0.0052 and 3.14 / 6 - 0.0175 - 0.0052 - 0.5 > 0
    assert 11 / 40 + 0.0052 + 0.5 < 3.14 / 4
    z = 5 / 8
    assert z - z ** 3 / 6 + z ** 5 / 120 < 0.5852 < 0.6
    # Lemmas F.2 and F.3 on a grid of admissible states.
    for i in range(0, n + 1, 4):
        b = bs[i]
        for j in range(41):
            a = max(0.5, b) + (amax(b) - max(0.5, b)) * j / 40
            if admissible(a, b):
                assert lower_edge(b) < label(a, b)
                if b <= 0.5:
                    assert label(a, b) < upper_edge(b)
    p = Plot(-0.08, 0.86, -0.16, 1.16, 440, 300)
    x_axis(p, -0.03, 0.84, ticks=((0, '0'), (0.5, '½'), (0.775, '31/40')),
           label='b')
    y_axis(p, -0.12, 1.14, ticks=((math.pi / 4, 'π/4'), (math.pi / 6, 'π/6')))
    for y in (math.pi / 4, math.pi / 6):
        p.line((0, y), (0.8, y), stroke=FAINT, width=1, dash='3 3')
    p.polygon(list(zip(bs, low)) + list(zip(reversed(bs), reversed(high))),
              fill=FILLS[0], stroke=BLUE, width=1.2)
    p.polyline([(x, lower_edge(x)) for x in bs], stroke=ORANGE, width=2.2)
    top = [x for x in bs if x <= 0.5] + [0.5]
    p.polyline([(x, upper_edge(x)) for x in top], stroke=GREEN, width=2.2)
    p.line((0.5, 0), (0.5, upper_edge(0.5)), stroke=FAINT, width=1,
           dash='3 3')
    p.text((0.6, 0.69), 'ℓ(a, b)', size=13, color=BLUE)
    p.text((0.33, 0.17), 'arcsin(' + it('b') + NB + '−' + NB + '½)' + NB + '+'
           + NB + '½', size=13, italic=False, color=ORANGE, anchor='start')
    p.text((0.06, 1.0), 'arcsin(' + it('b') + NB + '+' + NB + '½)' + NB + '−'
           + NB + '½', size=13, italic=False, color=GREEN, anchor='start')
    p.save('appendix-f/transverse', 'For each b, the labels of the admissible '
           'states (a, b) form the shaded interval. It lies above the curve '
           'arcsin(b - 1/2) + 1/2 of the lower edge, and for b at most '
           '1/2 below the curve arcsin(b + 1/2) - 1/2 of the upper edge')


# The envelope (Definition F.4 and Lemmas F.5 to F.7).

def envelope(x):
    return (1 / 24 + math.sqrt(TARGET - (x + 1) ** 2) / 3 + math.asin(x)
            - 0.75 * x)


def envelope_band():
    xe = math.sqrt(3) - 1
    n = 300
    xs = [xe * k / n for k in range(n + 1)]
    side_plus = lambda x, b: (b - 0.5) / 3 + 0.75 * (0.5 - x) + math.asin(x)

    def bmax(x):
        a = x + 0.5
        return min(a, math.sqrt(TARGET - (x + 1) ** 2) - 0.5)

    low = [side_plus(x, 0) for x in xs]
    high = [side_plus(x, bmax(x)) for x in xs]
    for x, h in zip(xs, high):
        assert h <= envelope(x) + 1e-12
    level = math.pi / 3 - HALF_WIDTH
    p = Plot(-0.06, 0.99, 0.1, 0.64, 470, 620)
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
    p.text((0.75, envelope(0.75)), 'E(x) − π/6', size=14, color=ORANGE,
           anchor='start', dx=8, dy=4)
    p.text((0.33, 0.42), 'side(' + it('a') + ',' + NB + it('b') + ')' + NB
           + '+' + NB + 'arcsin' + NB + it('x') + NB + '−' + NB + 'π/6',
           size=13, italic=False, color=BLUE)
    p.save('appendix-f/envelope-band', 'For each x = a - 1/2, the values of side(a, '
           'b) + arcsin x - pi/6 over the admissible states (a, b) fill the '
           'shaded interval, which lies below the graph of E(x) - pi/6 and '
           'touches it where the disk bounds b')


def peak_bound():
    """Lemma F.5: P(x) = 9 (x + 1/8)^2 (9 - 7x)^3 rises on [0, 123/280],
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
    pl.text((c, h(c)), it('P') + f'(123/280){NB}≈{NB}{h(c):.1f}', size=13,
            italic=False, color=BLUE, dy=-14)
    pl.text((0.12, h(0.12)), 'P', size=17, color=BLUE, anchor='end', dx=-8,
            dy=-6)
    pl.text((c / 2, 40), "P′ ≥ 0", size=14, color=GREEN)
    pl.text(((c + w) / 2, 40), "P′ ≤ 0", size=14, color=ORANGE)
    pl.save('appendix-f/peak-bound', 'The function P(x) = 9 (x + 1/8) squared '
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
    pl.text((0.555, 0.5225), '13/24' + NB + '+' + NB + it('x') + '/36' + NB
            + '−' + NB + it('x') + '²/16', size=13, italic=False,
            color=PURPLE, anchor='start')
    pl.text((0.5, envelope(0.5)), 'E(x) − π/6', size=14, color=ORANGE,
            anchor='end', dx=-12, dy=10)
    pl.save('appendix-f/parabola', 'The envelope minus pi/6 on [0, 3/4] below the '
            'parabola 13/24 + x/36 - x squared/16, which has the same value '
            'and slope at 0 and is highest, at 353/648, at x = 2/9; the level '
            'pi/3 - 1/2 lies above both')


def margins():
    """Lemmas F.2 and F.3: by how much the label clears the lower and the
    upper edge, at the admissible state with the given b where it is closest.
    The label decreases in a, so it is least at the largest a, on the circle,
    and largest at a = 1/2."""
    bmax = math.sqrt(TARGET / 2) - 0.5
    amax = lambda b: math.sqrt(TARGET - (b + 0.5) ** 2) - 0.5
    lower = lambda b: label(amax(b), b) - math.asin(b - 0.5) - HALF_WIDTH
    upper = lambda b: math.asin(b + 0.5) - HALF_WIDTH - label(0.5, b)
    n = 4000
    bs = [bmax * k / n for k in range(n + 1)]
    # the closest states really are at a = amax(b) and a = 1/2
    for k in range(0, n + 1, 40):
        b = bs[k]
        for j in range(41):
            a = max(0.5, b) + (amax(b) - max(0.5, b)) * j / 40
            if admissible(a, b):
                assert label(a, b) >= label(amax(b), b) - 1e-12
                assert label(a, b) <= label(0.5, b) + 1e-12 or b > 0.5
    lo_val, lo_b = min((lower(x), x) for x in bs)
    up_val, up_b = min((upper(x), x) for x in bs if x <= 0.5)
    assert 0.0046 < lo_val < 0.0048 and abs(lo_b - 0.72) < 0.01
    assert abs(up_b - 0.1) < 1e-3 and abs(up_val - (math.asin(0.6) - 0.625)) < 1e-6
    b0 = [x for x in bs if label(amax(x), x) < 1.25 * x - 1e-12][0]
    top = 0.1
    p = Plot(-0.08, 0.9, -0.012, 0.112, 480, 3000)
    x_axis(p, -0.03, 0.86, ticks=((0, '0'), (0.1, '0.1'), (0.5, '½'),
                                 (0.775, '31/40')), label='b')
    y_axis(p, 0, 0.108, ticks=((0.02, '0.02'), (0.04, '0.04'), (0.06, '0.06'),
                               (0.08, '0.08'), (0.1, '0.10')))
    p.curve(lower, 0, bmax, n=n, ylim=(0, top), stroke=ORANGE, width=2.4)
    p.curve(upper, 0, 0.5, n=n, ylim=(0, top), stroke=GREEN, width=2.4)
    p.line((b0, 0), (b0, lower(b0)), stroke=FAINT, width=1, dash='3 3')
    p.dot((lo_b, lo_val), fill=ORANGE)
    p.dot((up_b, up_val), fill=GREEN)
    p.text((lo_b, lo_val), f'{lo_val:.4f}', size=13, italic=False,
           color=ORANGE, dy=-14)
    p.text((up_b, up_val), 'arcsin' + NB + '3/5' + NB + '−' + NB + '5/8',
           size=13, italic=False, color=GREEN, anchor='start', dx=6, dy=12)
    assert lower(0.62) < 0.03
    p.text((0.62, 0.04), 'lower edge', size=13, italic=False, color=ORANGE,
           anchor='start')
    p.text((0.34, 0.092), 'upper edge', size=13, italic=False, color=GREEN,
           anchor='end')
    p.text((b0, 0.004), 'axial', size=12, italic=False, color=FAINT,
           anchor='end', dx=-5)
    p.text((b0, 0.004), 'side', size=12, italic=False, color=FAINT,
           anchor='start', dx=5)
    p.save('appendix-f/margins', 'The margins by which the label clears the '
           'lower edge, for b from 0 to 31/40, and the upper edge, for b up to '
           '1/2, at the closest admissible state with the given b. Both stay '
           'positive; the lower one comes down to about 0.0047 near b = 0.72, '
           'the upper one to arcsin 3/5 - 5/8 at b = 1/10')


def curvature():
    """Lemma F.6 (4): on [0, 3/4], E_2 lies below the bound of the proof,
    (x + 1/8)/A^3 - 13/(12 B^3) - 1/8, which lies below -1/8."""
    A3 = lambda x: (1 - x * x) ** 1.5
    B3 = lambda x: (TARGET - (x + 1) ** 2) ** 1.5
    E2 = lambda x: x / A3(x) - 13 / (12 * B3(x))
    U = lambda x: (x + 1 / 8) / A3(x) - 13 / (12 * B3(x)) - 1 / 8
    xs = [0.75 * k / 3000 for k in range(3001)]
    for x in xs:
        assert E2(x) <= U(x) + 1e-12 and U(x) < -1 / 8
    assert abs(E2(0) + 26 / 81) < 1e-12
    e_max, x_max = max((E2(x), x) for x in xs)
    assert abs(e_max + 0.209) < 0.001 and abs(x_max - 0.33) < 0.01
    lo = -1.15
    p = Plot(-0.07, 0.86, -1.24, 0.1, 520, 300)
    x_axis(p, -0.03, 0.83, y=0, ticks=((0.25, '¼'), (0.5, '½'),
                                      (0.75, '¾')), label='x')
    y_axis(p, lo, 0.08, ticks=((-1, '−1'), (-0.5, '−½')))
    p.line((0, -1 / 8), (0.78, -1 / 8), stroke=INK, width=1.3, dash='6 4')
    p.text((0.78, -1 / 8), '−1/8', size=13, italic=False, anchor='start',
           dx=6)
    p.curve(U, 0, 0.75, ylim=(lo, 0), stroke=PURPLE, width=1.8, dash='7 4')
    p.curve(E2, 0, 0.75, ylim=(lo, 0), stroke=BLUE, width=2.4)
    p.dot((0, E2(0)), fill=BLUE)
    p.text((0, E2(0)), '−26/81', size=13, italic=False, color=BLUE,
           anchor='end', dx=-7)
    p.dot((x_max, e_max), fill=BLUE)
    p.text((x_max, e_max), f'{e_max:.3f}'.replace('-', '−'), size=13,
           italic=False, color=BLUE, dy=14)
    p.text((0.6, E2(0.6)), sb(it('E'), '2', size=14), size=14, color=BLUE,
           anchor='end', dx=-8)
    xb = next(x for x in xs if x > x_max and U(x) < -0.75)
    p.text((xb, -0.75), 'bound of step 4', size=13, italic=False,
           color=PURPLE, anchor='start', dx=10)
    p.save('appendix-f/curvature', 'The second derivative E2 of the envelope on '
           '[0, 3/4]: it starts at -26/81, rises to about -0.209 near x = 0.33 and '
           'falls steeply; it stays below the dashed bound of the proof, which '
           'stays below the level -1/8')


def main():
    admissible_region()
    marker_arc()
    asin_line()
    transverse()
    margins()
    envelope_band()
    peak_bound()
    curvature()
    envelope_parabola()


if __name__ == '__main__':
    main()

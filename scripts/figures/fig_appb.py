#!/usr/bin/env python3
"""Draw the figures of Appendix B (docs/proof/appendix-b.md), six squares: the
normalization, in docs/proof/figures/appendix-b/.

    python3 scripts/figures/fig_appb.py

Every figure is computed from the functions and constants of the appendix:
the ceiling Q0 and the numbers rho0, c0, r0 derived from it, the support
function of the containing square, the cap depth, the radial profiles of the
squares separated along their own axis, the supports of a chart in the
ceiling, and the forces and terms of the west stress. Curves are sampled from
the functions they show, and configurations of squares are solved from the
separating inequalities of the proofs.
"""
import math
import sys

from proof_figures import (Figure, INK, FAINT, COLORS, FILLS, GREY,
                           square_corners, in_open_square, u, shift, sb)
from proof_figures import Graph as Plot
from fig_front import NB, it, word, arrow, thin_arc, polyline as fpoly

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
PINK, CYAN = COLORS[4], COLORS[5]

# The ceiling of Definition 9.4.
Q0 = 2.85118
R0 = math.sqrt(Q0)
RHO0 = math.sqrt(Q0 - 0.25) - 0.5
C0 = RHO0 - 1
R_CORE = 1.5 - RHO0
A0 = 2 - RHO0
U0 = math.sqrt(Q0 - (2.5 - RHO0) ** 2) - 0.5
L_SHALLOW = RHO0 - 0.5
SWITCH = math.asin(1 / (2 * R0))
CBAR, RBAR, RHOBAR = 0.11282, 1.6886, 1.11282


def up(s):
    """Upright markup, for function names inside italic mathematics."""
    return f'<tspan font-style="normal">{s}</tspan>'


SIN, COS = up('sin'), up('cos')


def sub(base, s, size):
    """An italic letter with an upright subscript, inside upright text."""
    return sb(it(base), s, '', size)


def save(f, name, title):
    """Save a figure of this appendix, in its directory."""
    assert name.startswith('appendix-b/'), name
    f.save(name, title)


# ---------------------------------------------------------------------------
# Drawing helpers.

class Shifted:
    """The drawing calls of a Figure, with every point shifted by (dx, dy)."""

    def __init__(self, f, dx, dy):
        self.f, self.dx, self.dy = f, dx, dy

    def q(self, p):
        return (p[0] + self.dx, p[1] + self.dy)

    def polygon(self, pts, **kw):
        self.f.polygon([self.q(p) for p in pts], **kw)

    def square(self, c, deg=0.0, **kw):
        self.polygon(square_corners(c, deg), **kw)

    def line(self, a, b, **kw):
        self.f.line(self.q(a), self.q(b), **kw)

    def polyline(self, pts, stroke=INK, width=1.6, dash=None):
        for a, b in zip(pts, pts[1:]):
            self.f.line(self.q(a), self.q(b), stroke=stroke, width=width,
                        dash=dash)

    def circle(self, c, r, **kw):
        self.f.circle(self.q(c), r, **kw)

    def dot(self, c, **kw):
        self.f.dot(self.q(c), **kw)

    def arc(self, c, r, t0, t1, stroke, width=4.0):
        self.f.arc(self.q(c), r, t0, t1, stroke, width)

    def text(self, c, s, **kw):
        self.f.text(self.q(c), s, **kw)


def clip_line(n, d, box):
    """The segment of the line <n, p> = d inside the box (x0, x1, y0, y1),
    or None."""
    x0, x1, y0, y1 = box
    p0 = (n[0] * d, n[1] * d)
    v = (-n[1], n[0])
    lo, hi = -1e9, 1e9
    for k, (a, b) in enumerate(((x0, x1), (y0, y1))):
        if abs(v[k]) < 1e-12:
            if not a <= p0[k] <= b:
                return None
            continue
        s0, s1 = (a - p0[k]) / v[k], (b - p0[k]) / v[k]
        lo, hi = max(lo, min(s0, s1)), min(hi, max(s0, s1))
    if lo >= hi:
        return None
    return ((p0[0] + lo * v[0], p0[1] + lo * v[1]),
            (p0[0] + hi * v[0], p0[1] + hi * v[1]))


def oriented_corners(t, a, b):
    """The vertices of Q_t(a, b): centre a u(t) + b u(t + pi/2), frame u(t)."""
    c = (a * math.cos(t) - b * math.sin(t), a * math.sin(t) + b * math.cos(t))
    return square_corners(c, math.degrees(t)), c


def polyline(f, pts, stroke=INK, width=1.6, dash=None, opacity=1):
    """One SVG polyline through the points, so that a dash pattern runs on
    along the whole curve."""
    d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (f.p(*q) for q in pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ''
    f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
          f'stroke-width="{width}" stroke-linejoin="round" '
          f'stroke-opacity="{opacity}"{extra}/>')


# ---------------------------------------------------------------------------
# Figure B.1: the shallow support lines of C (Lemma 9.14).

def eta(c, phi):
    x, y = math.cos(phi), math.sin(phi)
    return c[0] * x + c[1] * y + 0.5 * (abs(x) + abs(y))


def shallow_runs(c, steps=7200):
    """The maximal intervals of directions phi in [0, 2 pi) whose support
    line is shallow, eta(c, phi) <= rho0 - 1/2."""
    flags = [eta(c, 2 * PI * j / steps) <= L_SHALLOW for j in range(steps)]
    runs, start = [], None
    for j in range(steps + 1):
        flag = flags[j % steps]
        if flag and start is None:
            start = j
        if not flag and start is not None:
            runs.append((2 * PI * start / steps, 2 * PI * (j - 1) / steps))
            start = None
    return runs


def shallow():
    W = 2.15
    box = (-0.92, 1.12, -0.92, 1.08)
    f = Figure(box[0], box[1] + W, box[2], box[3] + 0.16, 175)
    cases = [((0.16, 0.03), (-0.225, 0.4), (-0.25, 0.45), 'regime (i)'),
             ((0.3, 0.2), (0.0, 0.6), (0.0, 0.7), 'regime (ii)')]
    for k, (c, (q0, q1), (th0, th1), title) in enumerate(cases):
        g = Shifted(f, k * W, 0.0)
        rect = [(0, q0), (0.9, q0), (0.9, q1), (0, q1)]
        g.polygon(rect, fill=FILLS[2], stroke='none')
        g.circle((0, 0), 0.9, stroke=FAINT, width=1, dash='2 3')
        g.circle((0, 0), L_SHALLOW, stroke=INK, width=1, dash='6 4')
        g.square(c, fill=GREY, stroke=INK, width=1.4, opacity=0.75)
        g.polygon(rect, stroke=GREEN, width=1.3)
        for lo, hi in shallow_runs(c):
            m = max(2, int((hi - lo) / 0.05))
            for j in range(m + 1):
                phi = lo + (hi - lo) * j / m
                n = u(phi)
                west = n[0] <= 1e-9
                if west and j % 3:
                    continue
                color = FAINT if west else (BLUE if n[1] > 0 else ORANGE)
                # the shallow normal closest to the east in each quadrant
                edge = (j == 0 and n[1] > 0) or (j == m and n[1] < 0)
                width = 0.8 if west else (2.0 if edge and not west else 1.0)
                seg = clip_line(n, eta(c, phi), box)
                if seg:
                    g.line(*seg, stroke=color, width=width)
        g.arc((0, 0), 0.9, th0, th1, GREEN, width=5)
        g.dot((0, 0), r=2.8)
        g.text((-0.04, -0.08), 'o', size=14, anchor='end')
        g.text((c[0] - 0.4, c[1] + 0.4), 'C', size=17)
        g.text((0.1, box[3] + 0.07), title, size=14, italic=False)
    save(f, 'appendix-b/shallow', 'Two panels, regimes (i) and (ii) of Lemma 9.14. '
         'In each, the containing square C near the origin o, the dashed '
         'circle of radius rho0 - 1/2, the dotted circle of radius 9/10 with '
         'the free arc in green, and the green rectangle of the points q '
         'allowed by the lemma. Thin lines are the support lines of C at '
         'distance at most rho0 - 1/2 from o: grey ones with a normal '
         'pointing west pass west of the rectangle; in regime (i) blue ones '
         'with a normal in the first quadrant pass above it and orange ones '
         'with a normal in the fourth quadrant below it; in regime (ii) only '
         'orange lines, nearly horizontal, remain below it')


# ---------------------------------------------------------------------------
# Figures B.2 to B.4: squares in a deep cap (Lemma 9.17).

def cap_first(s):
    return (RHO0 - 0.5) * math.cos(s) - 0.5 * math.sin(s)


def cap_second(s):
    return R0 - math.cos(s) - math.sin(s)


def cap_depth(s):
    return cap_first(s) if s <= SWITCH else cap_second(s)


def bisect(fn, lo, hi, n=80):
    """A zero of fn on [lo, hi], where fn changes sign."""
    flo = fn(lo)
    for _ in range(n):
        mid = (lo + hi) / 2
        if (fn(mid) > 0) == (flo > 0):
            lo, flo = mid, fn(mid)
        else:
            hi = mid
    return (lo + hi) / 2


def cap_depth_figure():
    f = Figure(-0.17, 0.99, -0.08, 0.56, 600)
    p = Plot(f, 1.18, 1.1, x0=0.0, y0=0.18, dx=0.0, dy=0.0)
    q4 = PI / 4
    s_half = bisect(lambda s: cap_depth(s) - 0.5, 0.1, 0.29)
    s_core = bisect(lambda s: cap_depth(s) - R_CORE, 0.31, 0.5)
    for y, color in ((R_CORE, PURPLE), (0.5, GREEN)):
        p.line((0, y), (q4, y), stroke=color, width=1, dash='5 4')
    for x in (SWITCH,):
        p.line((x, 0.18), (x, 0.66), stroke=FAINT, width=1, dash='3 3')
    p.x_axis(0, q4 + 0.05, y=0.18,
             ticks=((0, '0'), (0.203, '0.203'), (SWITCH, it('ϑ')),
                    (0.4, '2/5'), (q4, 'π/4')), label='s')
    p.y_axis(0.18, 0.67, ticks=((R_CORE, sub('r', '0', 12)),
                                (0.5, '½'),
                                (RHO0 - 0.5, sb(it('ρ'), '0', NB + '−' + NB
                                                + '½', 12))))
    p.curve(cap_first, SWITCH, SWITCH + 0.2, stroke=BLUE, width=1.3,
            dash='5 4')
    p.curve(cap_second, SWITCH - 0.16, SWITCH, stroke=ORANGE, width=1.3,
            dash='5 4')
    p.curve(cap_first, 0, SWITCH, stroke=BLUE, width=2.8)
    p.curve(cap_second, SWITCH, q4, stroke=ORANGE, width=2.8)
    for x, y, color in ((s_half, 0.5, GREEN), (s_core, R_CORE, PURPLE)):
        p.dot((x, y), r=3.6, fill=color)
    p.dot((SWITCH, cap_depth(SWITCH)), r=3.6, fill=INK)
    p.text((0.03, 0.635), '(' + sb('ρ', '0', NB + '−' + NB + '½)' + NB, 14)
           + COS + NB + 's − ½' + NB + SIN + NB + 's', size=14, color=BLUE,
           anchor='start')
    p.text((0.53, 0.238), sb('R', '0', NB + '−' + NB, 14) + COS + NB + 's − '
           + SIN + NB + 's', size=14, color=ORANGE, anchor='start')
    p.text((s_half + 0.01, 0.515), f'{s_half:.4f}', size=12, italic=False,
           color=GREEN, anchor='start')
    p.text((s_core + 0.012, R_CORE + 0.016), f'{s_core:.4f}', size=12,
           italic=False, color=PURPLE, anchor='start')
    save(f, 'appendix-b/cap-depth', 'The graph of the cap depth cap(s) for s from '
         '0 to pi/4: the blue branch (rho0 - 1/2) cos s - 1/2 sin s up to '
         'the switch angle theta, about 0.3006, where the orange branch '
         'R0 - cos s - sin s takes over, the two touching there; dashed, '
         'each branch continued a little beyond the switch. The graph '
         'crosses the level 1/2 at about 0.2021, before 0.203, and the level '
         'r0 at about 0.3832, before 2/5')


def cap_squares():
    h = R_CORE
    top = math.sqrt(Q0 - h * h)
    f = Figure(h - 0.62, R0 + 0.1, -top - 0.08, top + 0.12, 165)
    z0 = math.acos(h / R0)
    arc = [(R0 * math.cos(z), R0 * math.sin(z)) for z in
           [-z0 + 2 * z0 * k / 160 for k in range(161)]]
    f.polygon([(h, -top)] + arc + [(h, top)], fill=FILLS[5], stroke='none',
              opacity=0.6)
    polyline(f, arc, stroke=INK, width=1.2, dash='6 4')
    f.line((h, -top - 0.05), (h, top + 0.08), stroke=INK, width=1.4,
           dash='7 4')
    f.text((h + 0.04, top + 0.03), 'x = η', size=14, anchor='start')
    f.line((h - 0.57, 0), (R0 + 0.08, 0), stroke=FAINT, width=1)
    squares = [(0.0, 0.8876, 0.4612, BLUE), (0.0, 0.8876, -0.4612, GREEN),
               (0.3, 0.9444, -0.3737, ORANGE), (-0.38, 1.0403, 0.1912,
                                                PURPLE)]
    for t, a, b, color in squares:
        corners, c = oriented_corners(t, a, b)
        assert a * math.cos(t) - b * math.sin(t) >= h + 0.5 * (
            abs(math.cos(t)) + abs(math.sin(t))) - 1e-3
        assert (a + 0.5) ** 2 + (abs(b) + 0.5) ** 2 <= Q0 + 1e-3
        assert in_open_square((h + 0.5, 0), c, math.degrees(t))
        f.polygon(corners, fill='none', stroke=color, width=2)
    P = (h + 0.5, 0)
    f.line((h - 0.04, 0.2), P, stroke=INK, width=0.8)
    f.dot(P, r=4.2, fill=INK)
    f.text((h - 0.05, 0.25), '(η + ½, 0)', size=14, anchor='end')
    f.text((R0 * math.cos(1.0) + 0.04, R0 * math.sin(1.0) + 0.06),
           sb('R', '0', '', 14), size=14, anchor='start')
    f.text((h - 0.3, -0.09), '←' + NB + it('o'), size=14, italic=False)
    save(f, 'appendix-b/piercing', 'The part of the disk of radius R0 beyond the '
         'line x = eta, for the deepest cap eta = r0, shaded, with four squares '
         'drawn in it as outlines: two parallel to the axes and pushed up '
         'and down as far as the disk allows, and two turned by 0.3 and by '
         'minus 0.38, also pushed sideways. All four contain the point '
         '(eta + 1/2, 0), marked by a dot')


def cap_faces():
    h = R_CORE
    t, a, b = 0.2, 1.05, 0.08
    corners, c = oriented_corners(t, a, b)
    m = R0 + 0.06
    f = Figure(-m, m, -m, m, 140)
    f.circle((0, 0), R0, stroke=INK, width=1.2, dash='6 4')
    f.text((R0 * math.cos(2.3) - 0.05, R0 * math.sin(2.3) + 0.05),
           sb('R', '0', '', 14), size=14, anchor='end')
    f.line((h, -m + 0.02), (h, m - 0.02), stroke=INK, width=1.2, dash='7 4')
    f.text((h + 0.04, -1.45), 'x = η', size=13, anchor='start')
    f.polygon(corners, fill=FILLS[0], stroke=BLUE, width=1.8)
    f.dot(c, r=3.2, fill=BLUE)
    f.text((c[0] + 0.13, c[1] + 0.33), 'T', size=17, color=BLUE)
    offs = [(0.04, -0.12, 'start'), (0.0, 0.1, 'middle'),
            (-0.04, 0.0, 'end'), (-0.1, -0.1, 'middle')]
    for k in range(4):
        e1 = u(t + k * PI / 2)
        e2 = u(t + k * PI / 2 + PI / 2)
        A = c[0] * e1[0] + c[1] * e1[1]
        B = c[0] * e2[0] + c[1] * e2[1]
        color = BLUE if k == 0 else FAINT
        f.line((0, 0), shift((0, 0), e1, 0.62), stroke=color, width=2.2,
               arrow=True)
        dx, dy, anchor = offs[k]
        tip = shift((0, 0), e1, 0.66)
        f.text((tip[0] + dx, tip[1] + dy),
               f'({A:.2f}, {B:.2f})'.replace('-', '−'), size=13,
               italic=False, color=INK if k == 0 else FAINT, anchor=anchor)
    f.dot((0, 0), r=2.8)
    f.text((-0.05, 0.08), 'o', size=14, anchor='end')
    save(f, 'appendix-b/faces', 'A square T in the cap beyond the line x = eta, '
         'turned by 0.2, inside the circle of radius R0. From the origin, '
         'the four directions u(0.2 + k pi/2), k = 0, 1, 2, 3, that can serve '
         'as its primary axis, each labelled with the coordinates (a, b) of '
         'the centre of T in that frame: (1.05, 0.08) for the frame facing '
         'the cap, drawn in blue, and (0.08, -1.05), (-1.05, -0.08) and '
         '(-0.08, 1.05) for the others, drawn grey')


# ---------------------------------------------------------------------------
# Figures B.5 to B.8: squares separated from C along their own axis
# (Lemma 9.20).

def profile_east(t):
    """The radial profile of Lemma B.8 near the east axis."""
    if t >= 0:
        return 0.5 + 0.5 * (math.cos(t) + math.sin(t))
    return 0.5 + 0.5 * math.cos(-t) + R_CORE * math.sin(-t)


def profile_west(v):
    """The radial profile of Lemma B.8 near the west axis, t = pi + v."""
    if v <= 0:
        return 0.5 + R_CORE * math.cos(-v) + 0.5 * math.sin(-v)
    return 0.5 + R_CORE * (math.cos(v) + math.sin(v))


def west_pin_cap(v):
    """The largest radial coordinate of a square at the phase pi + v that
    holds p_W: its far corner reaches 0.9 sin(pi/12 + v) across."""
    return math.sqrt(Q0 - max(0.5, 0.9 * math.sin(PI / 12 + v)) ** 2) - 0.5


def profiles():
    q4 = PI / 4
    y0, y1 = 0.86, 1.25
    f = Figure(-0.1, 4.2, -0.22, (y1 - y0) * 3.4 + 0.2, 170)
    panels = [(profile_east, (-5 / 12, 3 / 10), '−5/12', '3/10', 't',
               'near the east axis: phase' + NB + it('t'), '−π/4'),
              (profile_west, (-2 / 3, 5 / 8), '−2/3', '5/8', 'v',
               'near the west axis: phase π +' + NB + it('v'), '')]
    for k, (fn, (lo, hi), slo, shi, var, title, sq) in enumerate(panels):
        p = Plot(f, 1.18, 3.4, x0=-q4, y0=y0, dx=0.1 + 2.15 * k, dy=0.0)
        p.polygon([(lo, y0), (hi, y0), (hi, y1), (lo, y1)],
                  fill=FILLS[2], stroke='none', opacity=0.7)
        p.x_axis(-q4, q4 + 0.08, y=y0,
                 ticks=((-q4, sq), (lo, slo), (0, '0'), (hi, shi),
                        (q4, 'π/4')), label=var)
        p.line((-q4, RHO0), (q4, RHO0), stroke=INK, width=1.2, dash='6 4')
        p.text((q4 - 0.01, RHO0 - 0.024), 'a = ' + sb('ρ', '0', '', 14),
               size=14, anchor='end')
        p.curve(fn, -q4, q4, n=400, stroke=BLUE, width=2.6)
        if k == 1:
            v0 = math.asin(5 / 9) - PI / 12
            p.curve(west_pin_cap, v0, q4, n=200, stroke=ORANGE, width=2,
                    dash='7 4')
            p.text((0.33, 1.17), 'largest' + NB + it('a') + NB + 'if' + NB
                   + it('T') + NB + 'holds' + NB + sb(it('p'), it('W'), '',
                                                      13),
                   size=13, italic=False, color=ORANGE)
        p.text((0.0, y1 + 0.035), title, size=13, italic=False)
        p.text((-q4 + 0.03, y1 - 0.02), 'least' + NB + it('a'), size=13,
               italic=False, color=BLUE, anchor='start')
    save(f, 'appendix-b/profiles', 'Two graphs over the angles from minus pi/4 to '
         'pi/4. Left, near the east axis: the least radial coordinate a '
         'allowed by the separation along the own axis, a blue curve, '
         'rises above the dashed level rho0 outside the green window from '
         'minus 5/12 to 3/10. Right, near the west axis: the blue curve rises '
         'above rho0 left of minus 2/3, and on the right it meets the dashed '
         'orange curve of the largest a for a square that holds the pin p_W '
         'before 5/8')


def own_margin(t, a, b, c):
    """The margin of Q_t(a, b) against Q(c) along its own axis."""
    return (a - c[0] * math.cos(t) - c[1] * math.sin(t) - 0.5
            - 0.5 * (abs(math.cos(t)) + abs(math.sin(t))))


def draw_disk(g, R=R0):
    g.circle((0, 0), R, stroke=INK, width=1.2, dash='6 4')
    g.circle((0, 0), 0.9, stroke=FAINT, width=1, dash='2 3')


def east_pin():
    m = R0 + 0.06
    W = 2 * m + 0.15
    f = Figure(-m, m + W, -m, m + 0.12, 112)
    cases = [(0.2630, (0.0, 0.0), 0.0, 'largest phase'),
             (-0.4095, (0.0, C0), 0.0, 'smallest phase')]
    for k, (t, c, b, title) in enumerate(cases):
        g = Shifted(f, k * W, 0.0)
        a = profile_east(t) if c == (0.0, 0.0) else (
            0.5 + 0.5 * math.cos(t) + R_CORE * math.sin(-t))
        assert own_margin(t, a, b, c) >= -1e-9
        assert (a + 0.5) ** 2 + (abs(b) + 0.5) ** 2 <= Q0
        draw_disk(g)
        g.square(c, fill=GREY, stroke=INK, width=1.3)
        g.text((c[0] - 0.3, c[1] + 0.3), 'C', size=16)
        corners, cT = oriented_corners(t, a, b)
        g.polygon(corners, fill=FILLS[1], stroke=ORANGE, width=1.8,
                  opacity=0.85)
        n = u(t)
        d = c[0] * n[0] + c[1] * n[1] + 0.5 * (abs(n[0]) + abs(n[1]))
        seg = clip_line(n, d, (-m, m, -m, m))
        g.line(*seg, stroke=INK, width=1.3, dash='6 4')
        g.line((0, 0), shift((0, 0), n, 1.55), stroke=FAINT, width=1,
               dash='2 3')
        pE = (0.9, 0.0)
        assert in_open_square(pE, cT, math.degrees(t))
        g.dot(pE, r=4, fill=INK)
        g.text((pE[0], pE[1] - 0.15), sb('p', 'E', '', 14), size=14)
        g.text(shift(cT, u(t + PI / 2), 0.22 if t > 0 else -0.22), 'T',
               size=16, color=ORANGE)
        g.dot((0, 0), r=2.6)
        g.text((-0.04, -0.09), 'o', size=13, anchor='end')
        g.text((0, m + 0.05), title + ',' + NB + it('t') + NB
               + f'= {t:.4f}'.replace('-', '−'), size=13, italic=False)
    save(f, 'appendix-b/east-pin', 'Two copies of the disk of radius R0 with the '
         'containing square C, grey, and a square T, orange, separated from '
         'C along its own axis by the dashed support line of C. Left, T at '
         'the largest phase 0.2630, with C = Q(0, 0); right, T at the '
         'smallest phase -0.4095, with C = Q(0, c0). Each T is pushed out to '
         'the circle, and each holds the east pin p_E at (9/10, 0), marked '
         'by a dot')


def far_lines():
    f = Figure(0.82, 1.98, 0.32, 1.28, 430)
    # the far corners (A, B) = (a + 1/2, |b| + 1/2) of charts in the ceiling
    top = math.sqrt(Q0 / 2)
    arc = [(R0 * math.cos(z), R0 * math.sin(z)) for z in
           [math.asin(0.5 / R0) + (PI / 4 - math.asin(0.5 / R0)) * k / 120
            for k in range(121)]]
    region = [(1.0, 0.5)] + arc + [(1.0, 1.0)]
    f.polygon(region, fill=FILLS[0], stroke='none')
    full = [(R0 * math.cos(z), R0 * math.sin(z)) for z in
            [0.15 + 0.85 * k / 160 for k in range(161)]]
    for a, b in zip(full, full[1:]):
        if 0.82 <= a[0] <= 1.98 and 0.32 <= a[1] <= 1.28:
            f.line(a, b, stroke=INK, width=1.6)
    f.line((1.0, 0.5), (1.0, 1.0), stroke=BLUE, width=1)
    f.line((1.0, 0.5), (arc[0][0], 0.5), stroke=BLUE, width=1)
    f.line((1.0, 1.0), (top, top), stroke=BLUE, width=1)
    f.text((1.22, 0.62), 'far corners', size=13, italic=False, color=BLUE)
    f.text((1.68, 1.0), 'A² + B² = ' + sb('Q', '0', '', 14), size=14,
           anchor='start')
    # the line 4A + B = 7 and its moving point
    f.line(((7 - 1.28) / 4, 1.28), ((7 - 0.32) / 4, 0.32), stroke=ORANGE,
           width=1, dash='5 4')
    seg = [(1.5 + v / 4, 1 - v) for v in (0, 5 / 12)]
    f.line(seg[0], seg[1], stroke=ORANGE, width=3.2)
    word(f, shift(seg[0], (0.03, 0.03)), '(1)', size=13, color=ORANGE,
         anchor='start')
    # the line 27A + 10B = 395/8 of the western flank
    c = 395 / 8
    f.line(((c - 10 * 1.28) / 27, 1.28), ((c - 10 * 0.32) / 27, 0.32),
           stroke=GREEN, width=1, dash='5 4')
    w0, w1 = PI / 12, 2 / 3
    seg = [(11 / 8 + w / 3, 49 / 40 - 0.9 * w) for w in (w0, w1)]
    f.line(seg[0], seg[1], stroke=GREEN, width=3.2)
    word(f, shift(seg[0], (-0.03, 0.03)), '(2)', size=13, color=GREEN,
         anchor='end')
    # the point of the W pin
    f.dot((1.54, 0.696), r=4.4, fill=PURPLE)
    f.line((1.545, 0.69), (1.75, 0.62), stroke=PURPLE, width=0.8)
    word(f, (1.755, 0.62), '(3) (1.54, 0.696)', size=13, color=PURPLE,
         anchor='start')
    # axes
    f.line((0.85, 0.35), (1.95, 0.35), width=1, arrow=True)
    f.line((0.85, 0.35), (0.85, 1.25), width=1, arrow=True)
    f.text((1.95, 0.39), 'A', size=15, anchor='end')
    f.text((0.87, 1.24), 'B', size=15, anchor='start')
    for x in (1.0, 1.5):
        f.line((x, 0.35), (x, 0.34), width=1)
        f.text((x, 0.33), f'{x:g}', size=12, italic=False, dy=6)
    for y in (0.5, 1.0):
        f.line((0.85, y), (0.86, y), width=1)
        f.text((0.84, y), f'{y:g}', size=12, italic=False, anchor='end')
    save(f, 'appendix-b/far-lines', 'The plane of the far corner (A, B) = (a + 1/2, '
         '|b| + 1/2) of a chart in the ceiling, whose possible positions fill '
         'the blue region inside the circle A^2 + B^2 = Q0. Three obstacles '
         'lie outside the circle: (1) an orange segment on the line 4A + B = '
         '7, (2) a green segment on the line 27A + 10B = 395/8, and (3) the '
         'purple point (1.54, 0.696); the dashed lines miss the disk')


def flank():
    box = (-1.78, 0.72, -1.05, 1.78)
    W = box[1] - box[0] + 0.2
    f = Figure(box[0], box[1] + W, box[2], box[3] + 0.14, 132)
    pW = (0.9 * math.cos(11 * PI / 12), 0.9 * math.sin(11 * PI / 12))
    pD = (0.9 * math.cos(5 * PI / 4), 0.9 * math.sin(5 * PI / 4))
    arc = [(R0 * math.cos(z), R0 * math.sin(z)) for z in
           [0.25 + 3.6 * k / 400 for k in range(401)]]
    arc = [q for q in arc if box[0] <= q[0] <= box[1]
           and box[2] <= q[1] <= box[3]]
    # left: separated along its own axis, with C = Q(c0, 0)
    g = Shifted(f, 0.0, 0.0)
    c = (C0, 0.0)
    w = 0.5
    t = PI - w
    a = 0.5 + R_CORE * math.cos(w) + 0.5 * math.sin(w)
    b = -(math.sqrt(Q0 - (a + 0.5) ** 2) - 0.5)
    assert own_margin(t, a, b, c) >= -1e-9
    delta = w - PI / 12
    b_miss = 0.9 * math.sin(delta) - 0.505
    for k, gg in enumerate((g, Shifted(f, W, 0.0))):
        polyline(f, [gg.q(q) for q in arc], stroke=INK, width=1.2,
                 dash='6 4')
        gg.circle((0, 0), 0.9, stroke=FAINT, width=1, dash='2 3')
        gg.dot((0, 0), r=2.6)
        gg.text((0.05, -0.09), 'o', size=13, anchor='start')
    g.square(c, fill=GREY, stroke=INK, width=1.3)
    g.text((c[0] + 0.25, c[1] + 0.3), 'C', size=16)
    corners, cT = oriented_corners(t, a, b)
    g.polygon(corners, fill=FILLS[1], stroke=ORANGE, width=1.8, opacity=0.85)
    ghost, cg = oriented_corners(t, a, b_miss)
    g.polygon(ghost, stroke=PURPLE, width=1.4, dash='6 4')
    far = max(ghost, key=lambda q: q[0] ** 2 + q[1] ** 2)
    assert far[0] ** 2 + far[1] ** 2 > Q0
    assert not in_open_square(pW, cg, math.degrees(t))
    g.dot(far, r=4, fill=PURPLE)
    g.text((far[0] - 0.08, far[1] + 0.03), 'far vertex', size=12,
           italic=False, color=PURPLE, anchor='end')
    assert in_open_square(pW, cT, math.degrees(t))
    n = u(t)
    d = c[0] * n[0] + c[1] * n[1] + 0.5 * (abs(n[0]) + abs(n[1]))
    seg = clip_line(n, d, box)
    g.line(*seg, stroke=INK, width=1.2, dash='6 4')
    g.text(shift(cT, u(t), 0.12), 'T', size=16, color=ORANGE)
    g.text((box[0] + 0.05, box[3] + 0.06), 'own axis, phase π − 0.5',
           size=13, italic=False, anchor='start')
    # right: in a deep cap beyond the west side x = -h, h = r0
    g = Shifted(f, W, 0.0)
    c = (C0, C0)
    h = 0.5 - c[0]
    w = 0.3
    t = PI - w
    a, b = 1.0755, -0.05
    assert -(a * math.cos(t) - b * math.sin(t)) >= h + 0.5 * (
        math.cos(w) + math.sin(w))
    assert (a + 0.5) ** 2 + (abs(b) + 0.5) ** 2 <= Q0
    g.square(c, fill=GREY, stroke=INK, width=1.3)
    g.text((c[0] + 0.25, c[1] + 0.3), 'C', size=16)
    g.line((-h, box[2]), (-h, box[3]), stroke=INK, width=1.2, dash='6 4')
    g.text((-h + 0.04, box[2] + 0.08), 'x = −η', size=13, anchor='start')
    corners, cT = oriented_corners(t, a, b)
    g.polygon(corners, fill=FILLS[1], stroke=ORANGE, width=1.8, opacity=0.85)
    assert in_open_square(pW, cT, math.degrees(t))
    g.text(shift(cT, u(t), 0.12), 'T', size=16, color=ORANGE)
    g.text((box[0] + 0.05, box[3] + 0.06), 'west side of' + NB + it('C')
           + ', phase π − 0.3', size=13, italic=False, anchor='start')
    for gg in (Shifted(f, 0.0, 0.0), g):
        for q, name in ((pW, 'W'), (pD, 'D')):
            gg.dot(q, r=4, fill=INK)
            gg.text((q[0], q[1] - 0.13), sb('p', name, '', 14), size=14)
    save(f, 'appendix-b/flank', 'Two panels with the arc of the circle of radius '
         'R0 and the dotted circle of radius 9/10 through the pins p_W and '
         'p_D. Left: a square T at the phase pi - 0.5, separated from C = '
         'Q(c0, 0) along its own axis by the dashed line, pushed sideways as '
         'far as the disk allows; it holds p_W. Dashed purple, the same '
         'square moved across until it just misses p_W: its far vertex, '
         'marked, lies outside the circle. Right: a square T at the phase '
         'pi - 0.3 beyond the dashed line x = -eta of the west side of C; it '
         'holds p_W')


# ---------------------------------------------------------------------------
# Figures B.9 and B.10: the supports in the ceiling (Lemma 9.26).

def chart_region_boundary(n=160):
    """The boundary of the centres (a, b) of the charts in the ceiling,
    counterclockwise from (1/2, -1/2)."""
    rd = math.sqrt(Q0 / 2) - 0.5
    lower = []
    for k in range(n + 1):
        y = rd - 2 * rd * k / n            # b from rd down to -rd
        a = math.sqrt(Q0 - (abs(y) + 0.5) ** 2) - 0.5
        lower.append((a, y))
    lower.reverse()                        # b from -rd up to rd
    return [(0.5, -0.5), (rd, -rd)] + lower + [(rd, rd), (0.5, 0.5)]


def centres():
    f = Figure(0.42, 2.0, -0.8, 0.82, 330)
    reg = chart_region_boundary()
    par = [(RHO0 - 0.31 * (abs(y) + y * y), y) for y in
           [-0.78 + 1.56 * j / 300 for j in range(301)]]
    f.polygon(reg, fill=FILLS[0], stroke=BLUE, width=1.3)
    polyline(f, par, stroke=INK, width=1.6, dash='6 4')
    U, V = it('U'), it('V')
    cones = [(1.0, 0.31, 0.0, INK, f'|{V}| ≤ 0.31{U}'),
             (0.6, 0.24, None, PURPLE,
              f'3/5 ≤ {U} ≤ 7/10, |{V}| ≤ 2{U}/5'),
             (7 / 5, 7 / 10, 1 / 12, ORANGE, f'{U} ≥ 7/5, |{V}| ≤ {U}/2'),
             (33 / 20, 0.99, 3 / 25, GREEN, f'{U} ≥ 33/20, |{V}| ≤ 3{U}/5')]
    legend = (1.36, 0.62)
    for j, (U, V, kappa, color, name) in enumerate(cones):
        bound = (RHOBAR * U + kappa * V * V) if kappa is not None else (
            RHO0 * U + 1 / 160)
        top = max(reg + par, key=lambda q: U * q[0] + V * q[1])
        assert U * top[0] + V * top[1] <= bound
        nrm = math.hypot(U, V)
        seg = clip_line((U / nrm, V / nrm), bound / nrm,
                        (0.42, 1.34, -0.4, 0.8))
        f.line(seg[0], seg[1], stroke=color, width=1.6)
        ytan = max(0.0, (V / (0.31 * U) - 1) / 2)
        f.dot((RHO0 - 0.31 * (ytan + ytan ** 2), ytan), r=3.2, fill=color)
        y = legend[1] - 0.09 * j
        f.line((legend[0], y), (legend[0] + 0.08, y), stroke=color, width=1.8)
        f.text((legend[0] + 0.1, y), name, size=12, italic=False,
               anchor='start')
    y = legend[1] - 0.09 * 4
    polyline(f, [(legend[0], y), (legend[0] + 0.08, y)], stroke=INK,
             width=1.6, dash='6 4')
    f.text((legend[0] + 0.1, y), 'a + 0.31(|b| + b²) = ' +
           sb('ρ', '0', '', 12), size=12, anchor='start')
    f.dot((RHO0, 0), r=3.2, fill=INK)
    f.text((RHO0 - 0.04, -0.06), sb('ρ', '0', '', 14), size=14,
           anchor='end')
    f.line((0.45, 0), (1.34, 0), stroke=FAINT, width=1, arrow=True)
    f.text((1.34, -0.04), 'a', size=15, anchor='end')
    f.line((0.5, -0.78), (0.5, 0.78), stroke=FAINT, width=1, arrow=True)
    f.text((0.48, 0.76), 'b', size=15, anchor='end')
    f.text((0.7, -0.12), 'centres', size=14, italic=False, color=BLUE)
    save(f, 'appendix-b/centres', 'The centres (a, b) of the charts in the '
         'ceiling, a blue region bounded by the lines a = 1/2 and |b| = a '
         'and by the circle of the far corner, and around it the dashed '
         'parabola a + 0.31(|b| + b^2) = rho0, which touches it at (rho0, '
         '0). Four support lines U a + V b = bound, one for the extreme '
         'force of each cone of Lemma 9.26 (2), listed in the legend, fan '
         'out from the tip; each lies beyond the parabola and comes close '
         'to it near a dot')


def chord_length(z, q):
    return math.hypot(z + math.sin(q), math.cos(q) - 1)


def chord_majorant(z, q):
    return (2 + z * z / 4) * math.sin(q / 2) + z * math.cos(q / 2)


def chord():
    f = Figure(-0.25, 3.75, -0.32, 3.05, 150)
    p = Plot(f, 1.0, 1.0, x0=0.0, y0=0.0, dx=0.15, dy=0.0)
    p.x_axis(0, PI + 0.2, ticks=((PI / 2, 'π/2'), (PI, 'π')), label='q')
    p.y_axis(0, 2.85, ticks=((1, '1'), (2, '2')))
    for z, color in ((0.0, INK), (0.5, BLUE), (1.0, ORANGE), (1.5, GREEN)):
        p.curve(lambda q: chord_majorant(z, q), 0, PI, stroke=color,
                width=1.6, dash='6 4')
        p.curve(lambda q: chord_length(z, q), 0, PI, stroke=color, width=2.4)
        assert all(chord_length(z, q) <= chord_majorant(z, q) + 1e-12
                   for q in [PI * k / 200 for k in range(201)])
        ylab = {0.0: 1.93, 0.5: 2.11, 1.0: 2.27, 1.5: 2.6}[z]
        p.text((PI + 0.05, ylab), it('z') + NB + f'= {z:g}', size=13,
               italic=False, color=color, anchor='start')
    save(f, 'appendix-b/chord', 'For z = 0, 0.5, 1 and 1.5, the length of the '
         'force (z + sin q, cos q - 1) as a function of q from 0 to pi, '
         'solid, and its majorant (2 + z^2/4) sin(q/2) + z cos(q/2), dashed '
         'in the same colour just above it; for z = 0 the two coincide, as '
         'the chord 2 sin(q/2)')


# ---------------------------------------------------------------------------
# Figures B.11 to B.13: the west stress (Proposition 9.33).

def tau(x):
    return 0.5 + 0.5 * (abs(math.cos(x)) + abs(math.sin(x)))


def west_config(t, v, c, bW, z):
    """W at the phase pi + t, separated from C along its own axis, and D at
    pi + v, separated along the west side of C and from W along the normal
    (sin z, -cos z), all three separations tight."""
    e1, e2 = u(PI + t), u(PI + t + PI / 2)
    aW = c[0] * e1[0] + c[1] * e1[1] + tau(t)
    cW = (aW * e1[0] + bW * e2[0], aW * e1[1] + bW * e2[1])
    xD = c[0] - tau(v)
    n = (math.sin(z), -math.cos(z))
    yD = (tau(v - t) + n[0] * cW[0] + n[1] * cW[1] - n[0] * xD) / n[1]
    return cW, (xD, yD), n


def west_forces(t, z):
    FC = (0.3 + 0.45 * math.cos(t), 0.45 * math.sin(t))
    FW = (-0.45 * math.cos(t) - 0.25 * math.sin(z),
          -0.45 * math.sin(t) + 0.25 * math.cos(z))
    FD = (-0.3 + 0.25 * math.sin(z), -0.25 * math.cos(z))
    return FC, FW, FD


def west_stress_figure():
    t, v = -0.3, 0.1
    z = t
    c = (C0 / 2, C0 / 2)
    best = None
    for k in range(-600, 601):
        bW = k / 1000
        cW, cD, n = west_config(t, v, c, bW, z)
        far = max(max(math.hypot(*q) for q in
                      square_corners(cW, math.degrees(PI + t))),
                  max(math.hypot(*q) for q in
                      square_corners(cD, math.degrees(PI + v))))
        if best is None or far < best[0]:
            best = (far, bW, cW, cD, n)
    far, bW, cW, cD, n = best
    assert far > R0
    m = 1.86
    box = (-m, m, -m, m)
    f = Figure(*box, 152)
    f.circle((0, 0), R0, stroke=INK, width=1.3, dash='6 4')
    f.circle((0, 0), far, stroke=PINK, width=1, dash='1.5 3')
    Wc = square_corners(cW, math.degrees(PI + t))
    Dc = square_corners(cD, math.degrees(PI + v))
    f.square(c, fill=GREY, stroke=INK, width=1.3)
    f.polygon(Wc, fill=FILLS[1], stroke=ORANGE, width=1.8, opacity=0.9)
    f.polygon(Dc, fill=FILLS[0], stroke=BLUE, width=1.8, opacity=0.9)
    # the three separating lines, each labelled with its weight near the
    # point of the line at the given height or abscissa
    e1 = u(PI + t)
    d1 = c[0] * e1[0] + c[1] * e1[1] + 0.5 * (abs(e1[0]) + abs(e1[1]))
    dn = n[0] * cW[0] + n[1] * cW[1] + 0.5
    lines = [(e1, d1, '9/20', ((d1 - e1[1] * 1.5) / e1[0] + 0.07, 1.5),
              'start'),
             ((-1.0, 0.0), 0.5 - c[0], '3/10', (c[0] - 0.5 + 0.06, -1.5),
              'start'),
             (n, dn, '1/4', (1.25, (dn - n[0] * 1.25) / n[1] + 0.1),
              'middle')]
    for nn, d, w, pos, anchor in lines:
        seg = clip_line(nn, d, box)
        f.line(*seg, stroke=INK, width=1.3, dash='7 4')
        word(f, pos, w, size=14, anchor=anchor)
    # the forces, drawn at 0.9 times their length, labelled beside the arrow
    FC, FW, FD = west_forces(t, z)
    for p0, F, name, color, side in ((c, FC, 'C', INK, 0),
                                     (cW, FW, 'W', ORANGE, -1),
                                     (cD, FD, 'D', BLUE, 1)):
        f.dot(p0, r=3, fill=color)
        tip = shift(p0, F, 0.9)
        arrow(f, p0, tip, color=color, width=2.6, size=11)
        nF = math.hypot(*F)
        if side:
            pos = shift(shift(p0, F, 0.45), (-F[1] / nF, F[0] / nF),
                        0.17 * side)
        else:
            pos = shift(tip, F, 0.25)
        f.text(pos, sb('F', name, '', 15), size=15, color=color)
    for q in Wc + Dc:
        if math.hypot(*q) > R0:
            f.dot(q, r=3.6, fill=PINK)
    f.text((cW[0] + 0.22, cW[1] - 0.22), 'W', size=17, color=ORANGE)
    f.text((cD[0] + 0.25, cD[1] - 0.22), 'D', size=17, color=BLUE)
    f.text((c[0] + 0.3, c[1] + 0.3), 'C', size=17)
    f.text(shift((0, 0), u(PI / 4), R0 - 0.16), sb('R', '0', '', 14),
           size=14)
    save(f, 'appendix-b/west-stress', 'The containing square C, grey, the square '
         'W, orange, turned by -0.3 from the west and separated from C along '
         'its own axis, and the square D, blue, turned by 0.1 and separated '
         'from C along the west side of C and from W along the secondary '
         'axis of W; the three separating lines are dashed and labelled '
         'with their weights 9/20, 3/10 and 1/4. Thick arrows are the forces '
         'F_C, F_W and F_D of the west stress. With every separation tight '
         'and W moved to the best place, two vertices, marked, still lie '
         'outside the dashed circle of radius R0; the dotted circle through '
         'the farthest has radius about 1.80')


def west_terms(R, t, positive):
    al = 0.225 - 0.45 * C0
    B = al if positive else -0.225
    return (al * math.cos(t) + B * math.sin(t)
            - R * math.sqrt(61 / 400 - 0.15 * math.sin(t)))


def west_H(R, v):
    B = 0.0 if v >= 0 else -0.3
    return (0.3 * math.cos(v) + B * math.sin(v)
            - R * math.sqrt(61 / 400 - 0.15 * math.sin(v)))


def west_G(R, d):
    return (0.25 * (math.cos(d) + math.sin(d))
            - R * math.sqrt(53 / 200 + 0.225 * math.sin(d)))


def west_phi(t, v, which):
    """Phi_W (which = 'W') or Phi_D (which = 'D') of Definition B.18."""
    if which == 'W':
        r = math.sqrt(53 / 200)
        s = math.sqrt(61 / 400 - 0.15 * math.sin(t))
    else:
        r = math.sqrt(53 / 200 + 0.225 * math.sin(v - t))
        s = math.sqrt(61 / 400 - 0.15 * math.sin(v))
    return (17 / 20 + 0.3 * math.cos(v) + 0.3 * max(-math.sin(v), 0)
            + 9 / 40 * (math.cos(t) + abs(math.sin(t)))
            + 0.25 * (math.cos(v - t) + math.sin(v - t))
            - C0 * (0.3 + 0.45 * math.cos(t) + 0.45 * max(math.sin(t), 0))
            - R0 * r - R0 * s)


def triangle():
    f = Figure(-1.4, 0.8, -0.6, 0.58, 380)
    q = lambda t, v: (t, v)
    T, U = it('t'), it('u')
    parts = [([(-2 / 3, -0.4), (-0.4, -0.4), (0, 0), (-2 / 3, 0)], FILLS[0],
              U + NB + '≤ 0', (-0.45, -0.08)),
             ([(-2 / 3, 0), (0, 0), (0, 0.4), (-2 / 3, 0.4)], FILLS[1],
              T + NB + '≤ 0 ≤' + NB + U, (-0.33, 0.2)),
             ([(0, 0), (0.4, 0.4), (0, 0.4)], FILLS[2], '0 ≤' + NB + T,
              (0.11, 0.3))]
    for pts, fill, name, pos in parts:
        f.polygon([q(*p) for p in pts], fill=fill, stroke=INK, width=1.2)
        f.text(pos, name, size=13, italic=False)
    # horizontal segments inside the parts, along which the stresses are
    # concave in t: they stop short of the cut t = 0
    for v in (-0.3, -0.15):
        f.line((-2 / 3, v), (v, v), stroke=FAINT, width=1, dash='3 3')
    for v in (0.12, 0.28):
        f.line((-2 / 3, v), (-0.012, v), stroke=FAINT, width=1, dash='3 3')
        f.line((0.012, v), (v, v), stroke=FAINT, width=1, dash='3 3')
    verts = [((-2 / 3, -0.4), (-0.03, -0.05), 'end'),
             ((-0.4, -0.4), (0.03, -0.05), 'start'),
             ((-2 / 3, 0.0), (-0.03, 0.0), 'end'),
             ((0.0, 0.0), (0.03, -0.035), 'start'),
             ((-2 / 3, 0.4), (-0.03, 0.04), 'end'),
             ((0.0, 0.4), (0.0, 0.06), 'middle'),
             ((0.4, 0.4), (0.03, 0.0), 'start')]
    for k, ((t, v), (dx, dy), anchor) in enumerate(verts):
        pw, pd = west_phi(t, v, 'W'), west_phi(t, v, 'D')
        assert pw > 0 and pd > 0
        f.dot((t, v), r=3.6)
        f.text((t + dx, v + dy), sub('v', str(k + 1), 13) + ':' + NB
               + f'{pw:.4f} / {pd:.4f}', size=13, italic=False, anchor=anchor)
    f.line((-1.2, -0.48), (0.7, -0.48), width=1, arrow=True)
    f.text((0.7, -0.52), 't', size=15, anchor='end')
    f.line((-1.16, -0.52), (-1.16, 0.54), width=1, arrow=True)
    f.text((-1.18, 0.53), 'u', size=15, anchor='end')
    for t, name in ((-2 / 3, '−2/3'), (-0.4, '−2/5'), (0, '0'),
                    (0.4, '2/5')):
        f.line((t, -0.48), (t, -0.47), width=1)
        f.text((t, -0.48), name, size=12, italic=False, dy=14)
    for v, name in ((-0.4, '−2/5'), (0, '0'), (0.4, '2/5')):
        f.line((-1.16, v), (-1.15, v), width=1)
        f.text((-1.16, v), name, size=12, italic=False, anchor='end',
               dx=-6)
    save(f, 'appendix-b/region', 'The region of the angles (t, u) with -2/3 '
         'at most t, t at most u, and u between -2/5 and 2/5, cut by the '
         'lines u = 0 and t = 0 into three parts, shaded differently: u '
         'negative, t negative and u positive, and t positive. The '
         'seven vertices v1 to v7 of the parts are marked, each labelled with '
         'the values of the two west stresses there, Phi_W first and Phi_D '
         'second, all positive; dotted horizontal segments inside the parts '
         'indicate the directions in which the stresses are concave')


def terms():
    PW, PH, GAP = 1.45, 0.82, 0.32
    f = Figure(-0.42, 3 * PW + 2 * GAP + 0.05, -2 * PH - 0.52, 0.02, 150)
    J = lambda R: (lambda x: west_terms(R, x, x >= 0))
    H = lambda R: (lambda x: west_H(R, x))
    G = lambda R: (lambda x: west_G(R, x))
    cols = [('t', -2 / 3, 0.4, J, 'J(t; ', ('−2/3', '0', '2/5'), True),
            ('u', -0.4, 0.4, H, 'H(u; ', ('−2/5', '0', '2/5'), True),
            ('d', 0.0, 16 / 15, G, 'G(u − t; ', ('0', '', '16/15'), False)]
    rows = [(sb('Φ', it('W'), '', 15), (R0, 0.0, 0.0)),
            (sb('Φ', it('D'), '', 15), (0.0, R0, R0))]
    for i, (rname, Rs) in enumerate(rows):
        y0 = -(i + 1) * PH - i * 0.36 - 0.12
        f.text((-0.38, y0 + PH / 2), rname, size=15, italic=False,
               anchor='start')
        for j, (var, lo, hi, fam, title, ticks, kink) in enumerate(cols):
            R = Rs[j]
            fn = fam(R)
            xs = [lo + (hi - lo) * k / 300 for k in range(301)]
            ys = [fn(x) for x in xs]
            ymin, ymax = min(ys), max(ys)
            pad = 0.15 * (ymax - ymin)
            x0 = j * (PW + GAP)
            X = lambda x: x0 + (x - lo) / (hi - lo) * PW
            Y = lambda y: y0 + (y - ymin + pad) / (ymax - ymin + 2 * pad) * PH
            f.polygon([(x0, y0), (x0 + PW, y0), (x0 + PW, y0 + PH),
                       (x0, y0 + PH)], stroke=FAINT, width=1)
            if kink:
                f.line((X(0), y0), (X(0), y0 + PH), stroke=FAINT, width=1,
                       dash='3 3')
                pieces = [(lo, 0.0), (0.0, hi)]
            else:
                pieces = [(lo, hi)]
            color = ORANGE if R > 0 else BLUE
            for a, b in pieces:
                pts = [(X(x), Y(fn(x))) for x in
                       [a + (b - a) * k / 200 for k in range(201)]]
                polyline(f, pts, stroke=color, width=2.4)
                f.line((X(a), Y(fn(a))), (X(b), Y(fn(b))), stroke=INK,
                       width=1, dash='4 3')
            for x, name in zip((lo, 0.0 if kink else None, hi), ticks):
                if x is None or not name:
                    continue
                f.text((X(x), y0), name, size=12, italic=False, dy=12)
            f.text((x0, y0 + PH + 0.08),
                   title.replace(' ', NB) + ('0)' if R == 0 else
                                             sb('R', '0', ')', 13)),
                   size=13, anchor='start')
            f.text((x0 + PW, y0 + PH + 0.08),
                   f'[{ymin:.2f}, {ymax:.2f}]'.replace('-', '−'), size=12,
                   italic=False, color=FAINT, anchor='end')
    save(f, 'appendix-b/terms', 'Six graphs in two rows and three columns: the '
         'terms J(t) on -2/3 to 2/5, H(u) on -2/5 to 2/5 and G(u - t) on 0 '
         'to 16/15 of the west stress, each on its own vertical scale, with '
         'its range written above it. The top row has the terms of Phi_W, '
         'J(t; R0), H(u; 0) and G(u - t; 0); the bottom row those of Phi_D, '
         'J(t; 0), H(u; R0) and G(u - t; R0). Each curve lies above its '
         'dashed chords on either side of 0, where J and H have a convex '
         'corner')


# ---------------------------------------------------------------------------
# The support of C against the direction of its normal (Lemma B.1).

def support():
    """g(u(phi)) = c_x cos phi + c_y sin phi + (|cos phi| + |sin phi|)/2 for
    the normals pointing east, for the two centres of the next figure: the
    shallow normals, g <= L, lie within the angles of Lemma B.1 of the north
    and the south."""
    north = math.degrees(math.acos(0.21))     # x < 21/100
    south = -math.degrees(math.acos(0.43))    # x < 43/100
    cases = [((0.16, 0.03), 'regime (i),' + NB + it('c') + NB
              + '= (0.16, 0.03)',
              [(north, 90.0, FILLS[0], '12°'), (-90.0, south, FILLS[1],
                                                '25°')]),
             ((0.3, 0.2), 'regime (ii),' + NB + it('c') + NB + '= (0.3, 0.2)',
              [(-90.0, -45.0, FILLS[1], '45°')])]
    PWd, GAP, y0, y1 = 1.8, 0.7, 0.25, 1.12
    kx, ky = PWd / 180, 1.5
    f = Figure(-0.3, 2 * PWd + GAP + 0.22, -0.3, (y1 - y0) * ky + 0.36, 155)
    for k, (c, title, bands) in enumerate(cases):
        g = Plot(f, kx, ky, x0=-90.0, y0=y0, dx=k * (PWd + GAP), dy=0.0)
        for lo, hi, fill, name in bands:
            g.polygon([(lo, y0), (hi, y0), (hi, y1), (lo, y1)], fill=fill,
                      stroke='none', opacity=0.9)
            word(f, g.q((lo + hi) / 2, y1 - 0.06), name, size=12)
        g.x_axis(-90, 100, y=y0, ticks=((-90, 'south'), (-45, '−45°'),
                                        (0, 'east'), (45, '45°'),
                                        (90, 'north')))
        g.y_axis(y0, y1 + 0.05, x=-90, ticks=((0.5, '½'), (1, '1')))
        g.line((-90, L_SHALLOW), (90, L_SHALLOW), stroke=INK, width=1.1,
               dash='5 4')
        g.text((90, L_SHALLOW), 'L', size=14, anchor='start', dx=6)
        phis = [-90 + 180 * j / 900 for j in range(901)]
        val = lambda p: eta(c, math.radians(p))
        runs, run, flag = [], [], None
        for p in phis:
            fl = val(p) <= L_SHALLOW
            if run and fl != flag:
                runs.append((flag, run + [(p, val(p))]))
                run = []
            run.append((p, val(p)))
            flag = fl
        runs.append((flag, run))
        for shallow_part, pts in runs:
            if shallow_part:
                color = BLUE if pts[0][0] > 0 else ORANGE
                g.polyline(pts, stroke=color, width=3)
                assert all(any(lo <= p <= hi for lo, hi, _, _ in bands)
                           for p, _ in pts[1:-1])
            else:
                g.polyline(pts, stroke=INK, width=1.6)
        g.text((0, y1 + 0.1), title, size=13, italic=False)
    f.text((0.08, (y1 - y0) * ky + 0.1), 'g', size=15)
    save(f, 'appendix-b/support', 'Two graphs, regimes (i) and (ii) of Lemma '
         '9.14, of the support g of C along a unit normal, against the '
         'direction of the normal from south through east to north. A '
         'dashed level L = rho0 - 1/2 marks the shallow lines; the graph '
         'dips below it only near the ends, thick blue near the north and '
         'thick orange near the south, inside shaded bands of 12 and 25 '
         'degrees in regime (i) and of 45 degrees near the south in regime '
         '(ii)')


# ---------------------------------------------------------------------------
# The cap depth: the far corner and the deepest caps (Definition B.2).

def deepest():
    s1, s2 = 0.12, 0.6
    assert s1 < SWITCH < s2
    K = (RHO0 + 0.5, 0.5)
    assert abs(math.hypot(*K) - R0) < 1e-9
    f = Figure(-0.12, 4.08, -1.12, 1.1, 150)
    # Left: the plane of the far corner.
    g = Shifted(f, 0.0, -0.95)
    reg = ([(0.5, 0.5), K] +
           [shift((0, 0), u(z), R0) for z in
            [SWITCH + (PI / 2 - 2 * SWITCH) * j / 80 for j in range(81)]] +
           [(0.5, math.sqrt(Q0 - 0.25))])
    g.polygon(reg, fill=FILLS[5], stroke='none', opacity=0.8)
    g.polyline([shift((0, 0), u(z), R0) for z in
                [0.08 + 1.42 * j / 120 for j in range(121)]], stroke=INK,
               width=1.3)
    arrow(f, g.q((0, 0)), g.q((1.92, 0)), width=1, size=8)
    arrow(f, g.q((0, 0)), g.q((0, 1.92)), width=1, size=8)
    g.text((1.9, -0.1), 'A', size=15, anchor='end')
    g.text((-0.06, 1.88), 'B', size=15, anchor='end')
    g.line((0, 0), K, stroke=FAINT, width=1, dash='3 3')
    thin_arc(f, g.q((0, 0)), 1.0, 0, SWITCH, color=INK, width=1)
    g.text(shift((0, 0), u(SWITCH * 0.6), 1.1), it('ϑ'), size=14,
           italic=False)
    for s, color, top in ((s1, BLUE, K), (s2, ORANGE, shift((0, 0), u(s2),
                                                              R0))):
        n = u(s)
        d = n[0] * top[0] + n[1] * top[1]
        seg = clip_line(n, d, (0.35, 1.95, 0.0, 1.85))
        g.line(*seg, stroke=color, width=1.4, dash='6 4')
        arrow(f, g.q((0, 0)), g.q(shift((0, 0), n, 0.62)), color=color,
              width=1.8, size=9)
        g.dot(top, r=3.8, fill=color)
    g.text((0.35, -0.12), it('s') + NB + '= 0.12', size=13, italic=False,
           color=BLUE)
    g.text(shift((0, 0), u(s2), 0.66), it('s') + NB + '= 0.6', size=13,
           italic=False, color=ORANGE, anchor='start', dx=4, dy=-4)
    g.text((K[0] - 0.1, K[1] + 0.12), '(' + sb(it('ρ'), '0', NB + '+' + NB
                                                + '½, ½)', 13),
           size=13, italic=False, anchor='end')
    g.text((0.95, 0.95), 'far corners', size=13, italic=False, color=INK)
    # Right: the two squares that attain the cap depth.
    r = Shifted(f, 2.25, 0.0)
    zmax = math.asin(1.08 / R0)
    polyline(f, [r.q(shift((0, 0), u(z), R0)) for z in
                 [-zmax + 2 * zmax * j / 160 for j in range(161)]],
             stroke=INK, width=1.2, dash='6 4')
    sq1, _ = oriented_corners(s1, RHO0, 0.0)
    a2, b2 = R0 * math.cos(s2) - 0.5, R0 * math.sin(s2) - 0.5
    sq2, _ = oriented_corners(-s2, a2, b2)
    for sq, s, color in ((sq1, s1, BLUE), (sq2, s2, ORANGE)):
        x = cap_depth(s)
        assert abs(min(q[0] for q in sq) - x) < 1e-9
        assert max(math.hypot(*q) for q in sq) <= R0 + 1e-9
        r.polygon(sq, stroke=color, width=2)
        r.line((x, -1.08), (x, 1.08), stroke=color, width=1.2, dash='6 4')
        r.dot(min(sq, key=lambda q: q[0]), r=3.6, fill=color)
        for q in sq:
            if math.hypot(*q) > R0 - 1e-9:
                r.dot(q, r=3.6, fill=color)
    word(f, r.q((cap_depth(s1) + 0.02, 1.0)), up('cap') + '(0.12)',
         size=13, color=BLUE, anchor='start')
    word(f, r.q((cap_depth(s2) - 0.02, -1.0)), up('cap') + '(0.6)', size=13,
         color=ORANGE, anchor='end')
    r.dot((0, 0), r=2.6)
    r.text((-0.04, -0.09), 'o', size=14, anchor='end')
    r.line((0, 0), (R0 + 0.05, 0), stroke=FAINT, width=1)
    r.text(shift((0, 0), u(0.5), R0 + 0.12), sb('R', '0', '', 14), size=14)
    save(f, 'appendix-b/deepest', 'Left: the plane of the far corner (A, B), '
         'with the part A, B at least one half of the disk of radius R0 '
         'shaded; its corner (rho0 + 1/2, 1/2) lies on the circle in the '
         'direction theta. For the direction s = 0.12, blue, the dashed line '
         'perpendicular to it through the corner keeps the shaded part on '
         'one side; for s = 0.6, orange, the dashed tangent at the point of '
         'the circle in that direction does. Right: the two squares turned '
         'by these angles that reach deepest into a cap: the blue one with '
         'both corners of its far edge on the circle, the orange one with '
         'its far vertex on the circle on the axis; each touches its dashed '
         'line x = cap(s) with a vertex')


# ---------------------------------------------------------------------------
# The phases near the west axis (proof of Lemma 9.20 (2)).

def west_phases():
    f = Figure(-1.42, 2.05, -1.02, 1.02, 165)
    rin, rout = 0.2, 1.08
    sectors = [(-PI / 4, -2 / 3, GREY), (-2 / 3, -PI / 12, FILLS[2]),
               (-PI / 12, 5 / 8, FILLS[0]), (5 / 8, PI / 4, FILLS[3])]
    for lo, hi, fill in sectors:
        n = max(4, int((hi - lo) * 60))
        outer = [shift((0, 0), u(PI + lo + (hi - lo) * j / n), rout)
                 for j in range(n + 1)]
        inner = [shift((0, 0), u(PI + hi - (hi - lo) * j / n), rin)
                 for j in range(n + 1)]
        f.polygon(outer + inner, fill=fill, stroke='none')
    for v, name in ((-PI / 4, '−π/4'), (-2 / 3, '−2/3'), (-PI / 12, '−π/12'),
                    (5 / 8, '5/8'), (PI / 4, 'π/4')):
        f.line(shift((0, 0), u(PI + v), rin), shift((0, 0), u(PI + v), rout),
               stroke=INK, width=1)
        word(f, shift((0, 0), u(PI + v), rout + 0.12), name, size=12)
    thin_arc(f, (0, 0), 0.9, PI / 2, 3 * PI / 2, color=FAINT, width=1,
             dash='2 3')
    for ang, name, lab in ((11 * PI / 12, 'W', (11 * PI / 12 - 0.15, 0.74)),
                           (5 * PI / 4, 'D', (5 * PI / 4 + 0.17, 0.9))):
        f.dot(shift((0, 0), u(ang), 0.9), r=3.8)
        f.text(shift((0, 0), u(lab[0]), lab[1]), sb('p', name, '', 14),
               size=14)
    f.dot((0, 0), r=2.6)
    f.text((0.05, -0.09), 'o', size=14, anchor='start')
    rows = [(GREY, it('v') + NB + '≤ −2/3: none (Lemma B.11)'),
            (FILLS[2], it('v') + NB + '≤ −π/12: holds' + NB
             + sb(it('p'), it('W'), '', 13) + NB + '(Lemma B.14)'),
            (FILLS[0], it('v') + NB + '&lt; 5/8:' + NB
             + sb(it('p'), it('W'), '', 13) + ' or ' + sb(it('p'), it('D'),
                                                          '', 13)
             + NB + '(Lemma 9.19)'),
            (FILLS[3], it('v') + NB + '≥ 5/8:' + NB
             + sb(it('p'), it('D'), '', 13) + ' (Lemmas 9.19, B.15)')]
    for j, (fill, text) in enumerate(rows):
        y = 0.45 - 0.3 * j
        f.polygon([(0.25, y - 0.07), (0.39, y - 0.07), (0.39, y + 0.07),
                   (0.25, y + 0.07)], fill=fill, stroke=FAINT, width=0.8)
        f.text((0.46, y), text, size=13, italic=False, anchor='start')
    f.text((0.25, 0.8), 'phase π +' + NB + it('v') + ', own axis', size=13,
           italic=False, anchor='start')
    save(f, 'appendix-b/west-phases', 'The directions pi + v around the west '
         'side of o, for v from -pi/4 to pi/4, cut into four coloured '
         'sectors at v = -2/3, -pi/12 and 5/8, with the pins p_W and p_D on '
         'the dotted circle of radius 9/10. A legend reads: v at most -2/3, '
         'none (Lemma B.11); v at most -pi/12, the square holds p_W (Lemma '
         'B.14); v below 5/8, it holds p_W or p_D (Lemma 9.19); v at least '
         '5/8, it holds p_D (Lemmas 9.19 and B.15)')


# ---------------------------------------------------------------------------
# The work of a force at the corner of a part of the disk (Lemma B.16 (3)).

def corner():
    l = 2.5 - RHO0
    beta = math.sqrt(Q0 - l * l)
    assert abs(beta - (U0 + 0.5)) < 1e-12
    f = Figure(0.98, 2.12, 0.28, 1.36, 330)
    part = ([(l, 0.5), (math.sqrt(Q0 - 0.25), 0.5)] +
            [shift((0, 0), u(z), R0) for z in
             [math.asin(0.5 / R0) + (math.atan2(beta, l)
                                      - math.asin(0.5 / R0)) * j / 60
              for j in range(61)]])
    f.polygon(part, fill=FILLS[0], stroke='none', opacity=0.9)
    fpoly(f, [shift((0, 0), u(z), R0) for z in
              [0.22 + 0.68 * j / 120 for j in range(121)]], stroke=INK,
          width=1.4)
    f.line((l, 0.3), (l, 1.3), stroke=INK, width=1.1, dash='6 4')
    word(f, (l + 0.02, 1.3), it('A') + NB + '=' + NB + it('l'), size=14,
         anchor='start')
    # the tangent at the corner
    tdir = (-beta / R0, l / R0)
    f.line(shift((l, beta), tdir, -0.25), shift((l, beta), tdir, 0.32),
           stroke=FAINT, width=1.2)
    for s, color, name in ((0.0, GREEN, '0'),
                           (math.sqrt(0.5), ORANGE, it('h'))):
        gam = math.sqrt(1 - s * s)
        assert R0 * s <= l
        # the part lies below the line s A + gam B = s l + gam beta
        assert all(s * q[0] + gam * q[1] <= s * l + gam * beta + 1e-9
                   for q in part)
        along = (gam, -s)
        f.line(shift((l, beta), along, -0.38), shift((l, beta), along, 0.62),
               stroke=color, width=1.4, dash='6 4')
        arrow(f, (l, beta), shift((l, beta), (s, gam), 0.24), color=color,
              width=1.8, size=9)
        f.text(shift((l, beta), (s, gam), 0.24), it('s') + NB + '=' + NB
               + name, size=13, italic=False, color=color, anchor='end',
               dx=-8)
    f.dot((l, beta), r=4)
    f.text((l, beta), '(' + it('l') + ',' + NB + '√(' + sub('Q', '0', 13)
           + NB + '−' + NB + it('l') + '²))', size=13, italic=False,
           anchor='end', dx=-10, dy=24)
    f.text((1.66, 0.42), 'A² + B² = ' + sb('Q', '0', '', 14), size=14,
           anchor='end')
    save(f, 'appendix-b/corner', 'The plane of the far corner near the line A '
         '= l, l = 5/2 - rho0: the part of the disk of radius R0 right of the '
         'dashed line and above B = 1/2 is shaded, and its corner (l, '
         'square root of Q0 - l^2) on the circle is marked. From the corner, '
         'two forces, straight up (s = 0, green) and at 45 degrees (s = h, '
         'orange), each with the dashed line through the corner '
         'perpendicular to it; the shaded part lies below both. The tangent '
         'to the circle at the corner is grey')


# ---------------------------------------------------------------------------
# The forces of the west stress as turning forces (Lemma B.18).

def forces():
    f = Figure(-0.72, 1.42, -0.42, 0.42, 300)
    # Left: F_W in the frame of W, 9/20 e1 plus a quarter turned by z - t.
    o1 = (-0.68, 0.0)
    g = Shifted(f, o1[0], o1[1])
    base = (0.45, 0.0)
    g.circle(base, 0.25, stroke=FAINT, width=1, dash='3 3')
    arc = [shift(base, u(-PI / 2 + 16 / 15 * j / 80), 0.25)
           for j in range(81)]
    g.polyline(arc, stroke=ORANGE, width=3)
    lens = []
    for d, dash in ((0.0, None), (16 / 15, '6 4')):
        tip = shift(base, u(-PI / 2 + d), 0.25)
        lens.append(math.hypot(*tip))
        assert abs(math.hypot(*tip) ** 2 - (53 / 200 + 9 / 40 * math.sin(d))
                   ) < 1e-12
        arrow(f, g.q((0, 0)), g.q(tip), color=BLUE, width=2, size=9,
              dash=dash)
    arrow(f, g.q((0, 0)), g.q(base), color=INK, width=1.6, size=9)
    arrow(f, g.q(base), g.q(shift(base, u(-PI / 2 + 16 / 15), 0.25)),
          color=ORANGE, width=1.2, size=8)
    g.dot((0, 0), r=3)
    g.text((0.22, 0.05), '9/20', size=13, italic=False)
    g.text(shift(shift(base, u(-PI / 2 + 16 / 15), 0.13), u(16 / 15), 0.05),
           '¼', size=13, italic=False, color=ORANGE)
    g.text(shift(base, u(-PI / 2), 0.25), it('z') + NB + '=' + NB + it('t'),
           size=13, italic=False, anchor='start', dx=6, dy=10)
    g.text(shift(base, u(-PI / 2 + 16 / 15), 0.25), it('u') + NB + '−' + NB
           + it('t') + NB + '= 16/15', size=13, italic=False,
           anchor='start', dx=8)
    g.text((0.02, 0.3), sb(it('F'), it('W'), '', 14) + ' in the frame of'
           + NB + it('W'), size=14, italic=False, anchor='start')
    g.line((-0.02, 0), (0.85, 0), stroke=FAINT, width=0.8)
    g.text((0.86, 0), sb(it('e'), '1', '', 13), size=13, italic=False,
           anchor='start', dx=-6, dy=-9)
    # Right: F_D, -3/10 e_x plus a quarter turned by z.
    g = Shifted(f, 1.2, 0.0)
    base = (-0.3, 0.0)
    g.circle(base, 0.25, stroke=FAINT, width=1, dash='3 3')
    z0, z1 = -2 / 3, 2 / 5
    arc = [shift(base, u(-PI / 2 + z0 + (z1 - z0) * j / 80), 0.25)
           for j in range(81)]
    g.polyline(arc, stroke=ORANGE, width=3)
    for z, name, dx in ((z0, '−2/3', -6), (z1, '2/5', 6)):
        tip = shift(base, u(-PI / 2 + z), 0.25)
        assert abs(math.hypot(*tip) ** 2 - (61 / 400 - 3 / 20 * math.sin(z))
                   ) < 1e-12
        arrow(f, g.q((0, 0)), g.q(tip), color=BLUE, width=2, size=9)
        g.text(tip, it('z') + NB + '=' + NB + name, size=13, italic=False,
               anchor='end' if dx < 0 else 'start', dx=dx, dy=12)
    arrow(f, g.q((0, 0)), g.q(base), color=INK, width=1.6, size=9)
    arrow(f, g.q(base), g.q(shift(base, u(-PI / 2 + z0), 0.25)),
          color=ORANGE, width=1.2, size=8)
    g.dot((0, 0), r=3)
    g.text((-0.15, 0.05), '3/10', size=13, italic=False)
    g.text(shift(base, u(-PI / 2 + z0), 0.13), '¼', size=13, italic=False,
           color=ORANGE, dx=-9, dy=-2)
    g.text((-0.4, 0.3), sb(it('F'), it('D'), '', 14), size=14,
           italic=False, anchor='start')
    g.line((-0.42, 0), (0.12, 0), stroke=FAINT, width=0.8)
    save(f, 'appendix-b/forces', 'Left: the force on W in the frame of W, '
         'the sum of 9/20 along its primary axis and a vector of length 1/4 '
         'whose tip runs on the dashed circle; for z = t it points straight '
         'down, and as u - t grows to 16/15 it turns along the orange arc. '
         'Right: the force on D, the sum of 3/10 to the west and a vector '
         'of length 1/4 turned by z, its tip on the orange arc for z from '
         '-2/3 to 2/5')


# ---------------------------------------------------------------------------
# The hypothesis of Lemma A.12 for the terms of the west stress (Lemma
# B.19 (2)).

def margins():
    al = 0.225 - 0.45 * C0
    rad_JH = lambda x: RBAR * math.sqrt(61 / 400 - 0.15 * math.sin(x))
    rad_G = lambda x: RBAR * math.sqrt(53 / 200 + 0.225 * math.sin(x))
    harm_J = lambda x: 4 * (al * math.cos(x) + (al if x >= 0 else -0.225)
                            * math.sin(x))
    harm_H = lambda x: 4 * (0.3 * math.cos(x) + (0.0 if x >= 0 else -0.3)
                            * math.sin(x))
    harm_G = lambda x: math.cos(x) + math.sin(x)
    cols = [('J', -2 / 3, 0.4, harm_J, rad_JH, ('−2/3', '0', '2/5')),
            ('H', -0.4, 0.4, harm_H, rad_JH, ('−2/5', '0', '2/5')),
            ('G', 0.0, 16 / 15, harm_G, rad_G, ('0', None, '16/15'))]
    PW, GAP, y0, y1, ky = 1.35, 0.35, 0.4, 1.65, 1.0
    f = Figure(-0.42, 3 * PW + 2 * GAP + 0.1, -0.55, (y1 - y0) * ky + 0.3,
               150)
    for j, (name, lo, hi, harm, rad, ticks) in enumerate(cols):
        xs = [lo + (hi - lo) * k / 300 for k in range(301)]
        assert all(rad(x) < harm(x) for x in xs)
        g = Plot(f, PW / (hi - lo), ky, x0=lo, y0=y0, dx=j * (PW + GAP),
                 dy=0.0)
        g.polygon([(x, rad(x)) for x in xs] +
                  [(x, harm(x)) for x in reversed(xs)], fill=FILLS[2],
                  stroke='none', opacity=0.9)
        g.polyline([(x, harm(x)) for x in xs], stroke=BLUE, width=2.4)
        g.polyline([(x, rad(x)) for x in xs], stroke=ORANGE, width=2.4)
        g.x_axis(lo, hi + 0.06 * (hi - lo), y=y0,
                 ticks=tuple((x, s) for x, s in zip((lo, 0.0, hi), ticks)
                             if s is not None))
        if j == 0:
            g.y_axis(y0, y1, x=lo, ticks=((0.5, '0.5'), (1.0, '1'),
                                          (1.5, '1.5')))
        else:
            g.line((lo, y0), (lo, y1), stroke=FAINT, width=0.8)
        f.text(g.q(lo + 0.5 * (hi - lo), y1), it(name) + ('±' if name != 'G'
                                                          else ''),
               size=15, italic=False, dy=-4)
    for k, (color, text) in enumerate(
            ((BLUE, '4(' + it('A') + NB + COS + NB + it('x') + ' + '
              + it('B') + NB + SIN + NB + it('x') + ')'),
             (ORANGE, it('R̄') + NB + '√(' + it('p') + ' + ' + it('q') + NB
              + SIN + NB + it('x') + ')'))):
        x0 = 0.3 + 2.4 * k
        f.line((x0, -0.42), (x0 + 0.3, -0.42), stroke=color, width=2.4)
        f.text((x0 + 0.38, -0.42), text, size=14, italic=False,
               anchor='start')
    save(f, 'appendix-b/margins', 'Three graphs, for the terms J, H and G of '
         'the west stress on their intervals -2/3 to 2/5, -2/5 to 2/5 and 0 '
         'to 16/15: in blue four times the harmonic part, in orange the '
         'radical with R = 1.6886, and the gap between them shaded green; '
         'the blue curve lies above the orange one everywhere, with a corner '
         'at 0 for J and H')


# ---------------------------------------------------------------------------
# The two west stresses on the triangle (Lemmas B.20 and B.21).

def segments(fn, xs, ys, level):
    """The level set fn = level on the grid xs x ys, by marching squares,
    as a list of segments."""
    vals = [[fn(x, y) for x in xs] for y in ys]
    segs = []
    for j in range(len(ys) - 1):
        for i in range(len(xs) - 1):
            c = [(xs[i], ys[j], vals[j][i]), (xs[i + 1], ys[j], vals[j][i + 1]),
                 (xs[i + 1], ys[j + 1], vals[j + 1][i + 1]),
                 (xs[i], ys[j + 1], vals[j + 1][i])]
            pts = []
            for k in range(4):
                (xa, ya, va), (xb, yb, vb) = c[k], c[(k + 1) % 4]
                if (va - level) * (vb - level) < 0:
                    s = (level - va) / (vb - va)
                    pts.append((xa + s * (xb - xa), ya + s * (yb - ya)))
            if len(pts) == 2:
                segs.append(tuple(pts))
            elif len(pts) == 4:
                segs += [(pts[0], pts[1]), (pts[2], pts[3])]
    return segs


def clip_below_diagonal(seg):
    """The part of a segment where t <= u."""
    (t0, u0), (t1, u1) = seg
    d0, d1 = u0 - t0, u1 - t1
    if d0 >= 0 and d1 >= 0:
        return seg
    if d0 < 0 and d1 < 0:
        return None
    s = d0 / (d0 - d1)
    m = (t0 + s * (t1 - t0), u0 + s * (u1 - u0))
    return (seg[0], m) if d0 >= 0 else (m, seg[1])


def stress_map():
    verts = [(-2 / 3, -0.4), (-0.4, -0.4), (-2 / 3, 0.0), (0.0, 0.0),
             (-2 / 3, 0.4), (0.0, 0.4), (0.4, 0.4)]
    tri = [(-2 / 3, -0.4), (-0.4, -0.4), (0.4, 0.4), (-2 / 3, 0.4)]
    k, gap = 1.0, 0.42
    W = (0.4 + 2 / 3) * k
    f = Figure(-2 / 3 - 0.2, -2 / 3 + 2 * W + gap + 0.12, -0.62, 0.62, 280)
    xs = [-2 / 3 + (0.4 + 2 / 3) * i / 160 for i in range(161)]
    ys = [-0.4 + 0.8 * j / 120 for j in range(121)]
    levels = (0.025, 0.05, 0.1, 0.15)
    for p, which in enumerate(('W', 'D')):
        fn = lambda t, v, w=which: west_phi(t, v, w)
        vals = [fn(t, v) for t in xs for v in ys if t <= v]
        assert min(vals) >= min(fn(*q) for q in verts) - 1e-12
        g = Shifted(f, p * (W + gap), 0.0)
        g.polygon(tri, fill=FILLS[0], stroke='none', opacity=0.8)
        for lev in levels:
            for seg in segments(fn, xs, ys, lev):
                seg = clip_below_diagonal(seg)
                if seg:
                    g.line(*seg, stroke=FAINT, width=1)
        g.polygon(tri, stroke=INK, width=1.2)
        g.line((0, 0), (0, 0.4), stroke=INK, width=1, dash='4 3')
        g.line((-2 / 3, 0), (0, 0), stroke=INK, width=1, dash='4 3')
        lowest = min(verts, key=lambda q: fn(*q))
        for q in verts:
            g.dot(q, r=3.2)
        g.circle(lowest, 0.03, stroke=PINK, width=2)
        # each level labelled where it meets the top edge, else the left edge
        for lev in levels:
            top = [bisect(lambda t: fn(t, 0.4) - lev, a, b) for a, b in
                   zip(xs, xs[1:]) if (fn(a, 0.4) - lev) * (fn(b, 0.4) - lev)
                   < 0]
            if top:
                g.line((top[0], 0.4), (top[0], 0.415), stroke=FAINT, width=1)
                word(f, g.q((top[0], 0.445)), f'{lev:g}', size=12)
                continue
            left = [bisect(lambda v: fn(-2 / 3, v) - lev, a, b) for a, b in
                    zip(ys, ys[1:]) if (fn(-2 / 3, a) - lev)
                    * (fn(-2 / 3, b) - lev) < 0]
            assert left and p == 1
            word(f, g.q((-2 / 3 - 0.02, max(left))), f'{lev:g}', size=12,
                 anchor='end')
        g.text((-2 / 3 + W / 2 - 0.1, 0.5), sb('Φ', it(which), '', 15),
               size=15, italic=False)
        g.line((-2 / 3, -0.48), (0.45, -0.48), width=1)
        for t, name in ((-2 / 3, '−2/3'), (0.0, '0'), (0.4, '2/5')):
            g.line((t, -0.48), (t, -0.465), width=1)
            word(f, g.q((t, -0.54)), name, size=12)
        g.text((0.47, -0.48), 't', size=14, anchor='start')
        if p == 0:
            g.line((-2 / 3 - 0.08, -0.4), (-2 / 3 - 0.08, 0.45), width=1)
            for v, name in ((-0.4, '−2/5'), (0.0, '0'), (0.4, '2/5')):
                g.line((-2 / 3 - 0.08, v), (-2 / 3 - 0.065, v), width=1)
                word(f, g.q((-2 / 3 - 0.1, v)), name, size=12, anchor='end')
            g.text((-2 / 3 - 0.13, 0.47), 'u', size=14)
    save(f, 'appendix-b/stress-map', 'The region of the angles (t, u), '
         'twice: left with level curves of Phi_W, right with level curves of '
         'Phi_D, at 0.025, 0.05, 0.1 and 0.15, the cuts t = 0 and u = 0 '
         'dashed and the seven vertices marked. Both stresses are positive '
         'on the whole region; the smallest value, circled, is at a vertex: '
         '0.0027 for Phi_W at (-2/3, 2/5) and 0.0104 for Phi_D at (-2/3, 0)')


FIGURES = {
    'shallow': shallow,
    'cap_depth': cap_depth_figure,
    'cap_squares': cap_squares,
    'cap_faces': cap_faces,
    'profiles': profiles,
    'east_pin': east_pin,
    'far_lines': far_lines,
    'flank': flank,
    'centres': centres,
    'chord': chord,
    'west_stress': west_stress_figure,
    'triangle': triangle,
    'terms': terms,
    'support': support,
    'deepest': deepest,
    'west_phases': west_phases,
    'corner': corner,
    'forces': forces,
    'margins': margins,
    'stress_map': stress_map,
}


def main(names=None):
    for name in names or FIGURES:
        FIGURES[name]()


if __name__ == '__main__':
    main(sys.argv[1:])

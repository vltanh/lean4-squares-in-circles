#!/usr/bin/env python3
"""Draw the figures of docs/proof/ as SVG files in docs/proof/figures/.

    python3 scripts/figures/proof_figures.py

The figures of each chapter go to the directory of its page: 01-introduction/
for the introduction, 02-preliminaries/ to 10-seven/ for the chapters, and
appendix-a/ to appendix-i/ for the appendices. This module draws the figures
shared since the first version of the pages and holds the drawing helpers; the
modules fig_front.py (Chapters 1 to 3), fig_one.py to fig_seven.py
(Chapters 4 to 10) and fig_appa.py to fig_appi.py (Appendices A to I) draw the
figures of each chapter, and main() runs them all.

Arcs of squares on the auxiliary circles are found by sampling the circle and
testing membership in the open squares, so every figure is computed from the
same geometry as the proofs.
"""
import math
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / 'docs' / 'proof' / 'figures'

INK = '#1f2937'
FAINT = '#9ca3af'
COLORS = ['#2563eb', '#ea580c', '#16a34a', '#9333ea', '#db2777', '#0891b2',
          '#ca8a04']
FILLS = ['#dbeafe', '#ffedd5', '#dcfce7', '#f3e8ff', '#fce7f3', '#cffafe',
         '#fef9c3']
GREY = '#e5e7eb'
SERIF = "Georgia, 'Times New Roman', serif"


class Figure:
    def __init__(self, xmin, xmax, ymin, ymax, scale, pad=18):
        self.xmin, self.ymax, self.s, self.pad = xmin, ymax, scale, pad
        self.w = (xmax - xmin) * scale + 2 * pad
        self.h = (ymax - ymin) * scale + 2 * pad
        self.items = []

    def p(self, x, y):
        return (self.pad + (x - self.xmin) * self.s,
                self.pad + (self.ymax - y) * self.s)

    def add(self, item):
        self.items.append(item)

    def polygon(self, pts, fill='none', stroke=INK, width=1.5, dash=None,
                opacity=1):
        d = ' '.join(f'{x:.1f},{y:.1f}' for x, y in (self.p(*q) for q in pts))
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.add(f'<polygon points="{d}" fill="{fill}" stroke="{stroke}" '
                 f'stroke-width="{width}" fill-opacity="{opacity}"{extra}/>')

    def square(self, c, deg=0.0, **kw):
        self.polygon(square_corners(c, deg), **kw)

    def line(self, a, b, stroke=INK, width=1.2, dash=None, arrow=False):
        (x1, y1), (x2, y2) = self.p(*a), self.p(*b)
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        if arrow:
            extra += ' marker-end="url(#arrow)"'
        self.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" '
                 f'y2="{y2:.1f}" stroke="{stroke}" stroke-width="{width}"'
                 f'{extra}/>')

    def circle(self, c, r, stroke=FAINT, width=1.2, dash=None, fill='none'):
        x, y = self.p(*c)
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r * self.s:.1f}" '
                 f'fill="{fill}" stroke="{stroke}" stroke-width="{width}"'
                 f'{extra}/>')

    def dot(self, c, r=3.2, fill=INK):
        x, y = self.p(*c)
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}"/>')

    def arc(self, c, r, t0, t1, stroke, width=4.0):
        """Counterclockwise arc from angle t0 to t1 (radians), in pieces of
        at most 2.5 radians: an SVG arc between nearly opposite points is
        placed by its rounded end points and can drift off its circle."""
        n = max(1, math.ceil((t1 - t0) / 2.5))
        ts = [t0 + (t1 - t0) * k / n for k in range(n + 1)]
        pts = [self.p(c[0] + r * math.cos(t), c[1] + r * math.sin(t))
               for t in ts]
        rr = r * self.s
        d = f'M {pts[0][0]:.1f} {pts[0][1]:.1f}' + ''.join(
            f' A {rr:.1f} {rr:.1f} 0 0 0 {x:.1f} {y:.1f}' for x, y in pts[1:])
        self.add(f'<path d="{d}" fill="none" stroke="{stroke}" '
                 f'stroke-width="{width}" stroke-linecap="round"/>')

    def text(self, c, s, size=15, anchor='middle', color=INK, italic=True,
             dx=0, dy=0):
        x, y = self.p(*c)
        style = ' font-style="italic"' if italic else ''
        self.add(f'<text x="{x + dx:.1f}" y="{y + dy:.1f}" font-size="{size}" '
                 f'font-family="{SERIF}" fill="{color}" text-anchor="{anchor}" '
                 f'dominant-baseline="middle"{style}>{s}</text>')

    def save(self, name, title):
        svg = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w:.0f}" '
               f'height="{self.h:.0f}" viewBox="0 0 {self.w:.0f} {self.h:.0f}" '
               f'role="img" aria-label="{title}">',
               f'<title>{title}</title>',
               '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" '
               'markerUnits="userSpaceOnUse" markerWidth="11" '
               'markerHeight="11" orient="auto-start-reverse">'
               f'<path d="M 0 0 L 10 5 L 0 10 z" fill="{INK}"/></marker></defs>',
               f'<rect width="100%" height="100%" fill="#ffffff"/>']
        svg += self.items + ['</svg>']
        path = OUT / f'{name}.svg'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('\n'.join(svg) + '\n')


class Graph:
    """A graph: the data point (x, y) is drawn at (kx (x - x0), ky (y - y0))
    shifted by (dx, dy) in the coordinates of the figure, so that several
    graphs with their own scales can share one figure."""

    def __init__(self, f, kx, ky, x0=0.0, y0=0.0, dx=0.0, dy=0.0):
        self.f, self.kx, self.ky = f, kx, ky
        self.x0, self.y0, self.dx, self.dy = x0, y0, dx, dy

    def q(self, x, y):
        return (self.dx + (x - self.x0) * self.kx,
                self.dy + (y - self.y0) * self.ky)

    def polyline(self, pts, stroke=INK, width=1.8, dash=None):
        d = ' '.join(f'{x:.1f},{y:.1f}'
                     for x, y in (self.f.p(*self.q(*p)) for p in pts))
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.f.add(f'<polyline points="{d}" fill="none" stroke="{stroke}" '
                   f'stroke-width="{width}" stroke-linejoin="round"{extra}/>')

    def curve(self, fn, x0, x1, n=300, **kw):
        pts = [(x0 + (x1 - x0) * k / n, fn(x0 + (x1 - x0) * k / n))
               for k in range(n + 1)]
        self.polyline(pts, **kw)

    def polygon(self, pts, **kw):
        self.f.polygon([self.q(*p) for p in pts], **kw)

    def line(self, a, b, **kw):
        self.f.line(self.q(*a), self.q(*b), **kw)

    def dot(self, p, **kw):
        self.f.dot(self.q(*p), **kw)

    def text(self, p, s, **kw):
        self.f.text(self.q(*p), s, **kw)

    def x_axis(self, x0, x1, y=0.0, ticks=(), label='', size=12):
        self.line((x0, y), (x1, y), width=1, arrow=True)
        for x, name in ticks:
            a, b = self.q(x, y)
            k = 4 / self.f.s
            self.f.line((a, b - k), (a, b + k), width=1)
            self.f.text((a, b), name, size=size, italic=False, dy=15)
        if label:
            self.text((x1, y), label, size=15, anchor='end', dy=-11)

    def y_axis(self, y0, y1, x=0.0, ticks=(), label='', size=12):
        self.line((x, y0), (x, y1), width=1, arrow=True)
        for y, name in ticks:
            a, b = self.q(x, y)
            k = 4 / self.f.s
            self.f.line((a - k, b), (a + k, b), width=1)
            self.f.text((a, b), name, size=size, italic=False, anchor='end',
                        dx=-7)
        if label:
            self.text((x, y1), label, size=15, anchor='start', dx=7, dy=3)


def square_corners(c, deg=0.0):
    t = math.radians(deg)
    e1, e2 = (math.cos(t), math.sin(t)), (-math.sin(t), math.cos(t))
    return [(c[0] + sx * e1[0] / 2 + sy * e2[0] / 2,
             c[1] + sx * e1[1] / 2 + sy * e2[1] / 2)
            for sx, sy in ((-1, -1), (1, -1), (1, 1), (-1, 1))]


def in_open_square(p, c, deg=0.0):
    t = math.radians(deg)
    dx, dy = p[0] - c[0], p[1] - c[1]
    x = math.cos(t) * dx + math.sin(t) * dy
    y = -math.sin(t) * dx + math.cos(t) * dy
    return abs(x) < 0.5 and abs(y) < 0.5


def arcs_in(member, r, steps=7200):
    """Maximal angle intervals (t0, t1) of the circle of radius r about the
    origin whose points satisfy `member`."""
    ts = [2 * math.pi * k / steps for k in range(steps)]
    inside = [member((r * math.cos(t), r * math.sin(t))) for t in ts]
    if all(inside):
        return [(0.0, 2 * math.pi)]
    start = inside.index(False)
    runs, run = [], None
    for k in range(start, start + steps + 1):
        t, flag = ts[k % steps] + 2 * math.pi * (k // steps), inside[k % steps]
        if flag and run is None:
            run = t
        elif not flag and run is not None:
            runs.append((run, t))
            run = None
    return runs


def square_frame(f, label=(-0.38, 0.38)):
    """The unit square in its own frame, with its axes and centre."""
    f.line((-0.72, 0), (1.12, 0), stroke=FAINT, dash='4 4')
    f.line((0, -0.72), (0, 0.74), stroke=FAINT, dash='4 4')
    f.text((1.15, 0.0), sb('x', 'S', size=14), size=14, anchor='start',
           color=FAINT)
    f.text((0.03, 0.74), sb('y', 'S', size=14), size=14, anchor='start',
           color=FAINT)
    f.square((0, 0), fill=FILLS[0], stroke=COLORS[0])
    f.text(label, 'S', size=17, color=COLORS[0])
    f.dot((0, 0))


def position():
    a, b = 0.85, 0.3
    o, turn = (a, b), (a, 0)
    f = Figure(-0.75, 1.3, -0.62, 0.8, 200)
    square_frame(f)
    f.text((-0.04, -0.07), sb('c', 'S'), anchor='end')
    f.line((0, 0), turn, width=2.4)
    f.line(turn, o, width=2.4)
    for x in (0, a):
        f.line((x, -0.03), (x, 0.03), width=1.6)
    f.line((a - 0.03, b), (a + 0.03, b), width=1.6)
    f.text((a / 2, -0.08), sb('a', 'S'))
    f.text((a + 0.07, b / 2), sb('b', 'S'), anchor='start')
    f.dot(o)
    f.text((o[0] - 0.02, o[1] + 0.08), 'o', anchor='end')
    f.save('03-tools/position', 'A square in its own frame, turned so that the disk '
           'centre o lies in the first quadrant; o is reached from the centre '
           'by going a along the first axis and b along the second')


def farthest_vertex():
    a, b = 0.85, 0.3
    o, far, corner = (a, b), (-0.5, -0.5), (-0.5, b)
    orange = COLORS[1]
    f = Figure(-0.75, 1.3, -0.78, 0.8, 200)
    square_frame(f, label=(0.4, -0.4))
    f.text((0.04, 0.07), sb('c', 'S'), anchor='start')
    # The right triangle from o to the farthest vertex.
    f.line(o, far, stroke=orange, width=1.8, dash='6 4')
    f.line(o, corner, stroke=orange, width=2.4)
    f.line(corner, far, stroke=orange, width=2.4)
    f.line((-0.45, b), (-0.45, b - 0.05), stroke=orange, width=1.2)
    f.line((-0.45, b - 0.05), (-0.5, b - 0.05), stroke=orange, width=1.2)
    for x in (a, 0, -0.5):
        f.line((x, b - 0.03), (x, b + 0.03), stroke=orange, width=1.6)
    for y in (b, 0, -0.5):
        f.line((-0.53, y), (-0.47, y), stroke=orange, width=1.6)
    f.text((a / 2, b + 0.08), sb('a', 'S'), color=orange)
    f.text((-0.25, b + 0.08), '½', color=orange, italic=False)
    f.text((-0.58, b / 2), sb('b', 'S'), color=orange, anchor='end')
    f.text((-0.58, -0.25), '½', color=orange, anchor='end', italic=False)
    f.text((0.14, -0.3), '√φ(' + sb('a', 'S', ', ') + sb('b', 'S', ')'),
           size=15, color=orange)
    f.dot(far, fill=orange)
    f.text((-0.5, -0.63), 'farthest vertex', size=13, italic=False,
           color=orange)
    f.dot(o)
    f.text((o[0] + 0.03, o[1] + 0.02), 'o', anchor='start')
    f.save('03-tools/farthest-vertex', 'The farthest vertex of a square from the disk '
           'centre, in the frame of the square turned so that o lies in the '
           'first quadrant')


def chart():
    r, a, b = 0.45, 0.75, 0.25
    A = math.acos((a - 0.5) / r)
    V = math.asin((0.5 - b) / r)
    assert V < A and b + 0.5 > r
    orange = COLORS[1]

    def italic(base, sub, after, size):
        """An italic letter with a subscript, then upright text."""
        d = 0.3 * size
        return (f'<tspan font-style="italic">{sb(base, sub, size=size)}'
                f'</tspan><tspan dy="{-d:.1f}">{after}</tspan>')

    f = Figure(-0.5, 1.45, -0.62, 1.0, 250)
    f.square((a, b), fill=FILLS[0], stroke=COLORS[0])
    f.dot((a, b), fill=COLORS[0])
    f.text((a + 0.03, b + 0.05), '(' + sb('a', 'S', ', ', 14) + sb('b', 'S', ')', 14), anchor='start', size=14,
           color=COLORS[0])
    # The chart axis and the lines of the near and lower edges.
    f.line((-0.48, 0), (1.43, 0), stroke=FAINT, width=1)
    f.text((1.43, 0.05), '<tspan font-style="italic">t</tspan> = 0', size=12,
           anchor='end', italic=False, color=FAINT)
    f.line((a - 0.5, -0.6), (a - 0.5, 0.92), stroke=INK, width=1, dash='4 4')
    f.text((a - 0.5, 0.96), 'near edge  <tspan font-style="italic">'
           'x</tspan> = ' + italic('a', 'S', ' − ½', 13), size=13,
           italic=False)
    f.line((-0.48, b - 0.5), (1.43, b - 0.5), stroke=INK, width=1, dash='4 4')
    f.text((1.43, b - 0.5 - 0.06), 'lower edge  <tspan '
           'font-style="italic">y</tspan> = ' +
           italic('b', 'S', ' − ½', 13), size=13, anchor='end',
           italic=False)
    f.circle((0, 0), r)
    f.text((-0.36, 0.36), sb('Γ', 'r', size=16), size=16)
    # The cap, and the three crossings that bound it.
    f.arc((0, 0), r, -V, A, orange, width=5)
    f.text((0.52, 0.2), 'cap', size=14, italic=False, color=orange,
           anchor='start')
    for t, dash, color in ((A, None, INK), (-V, None, INK),
                           (-A, '3 3', FAINT)):
        p = (r * math.cos(t), r * math.sin(t))
        f.line((0, 0), p, stroke=color, width=1, dash=dash)
        f.dot(p, r=3.6, fill=color)
    f.arc((0, 0), 0.1, 0, A, INK, width=1.2)
    f.text((0.16 * math.cos(A / 2), 0.16 * math.sin(A / 2)), sb('A', 'S'))
    f.arc((0, 0), 0.13, -V, 0, INK, width=1.2)
    f.text((0.19 * math.cos(-V / 2), 0.19 * math.sin(-V / 2)), sb('V', 'S'))
    q = (r * math.cos(-A), r * math.sin(-A))
    f.text((q[0] - 0.03, q[1] - 0.06), '−' + sb('A', 'S', size=13), size=13, anchor='end',
           color=FAINT)
    f.dot((0, 0))
    f.text((-0.03, 0.05), 'o', anchor='end')
    f.save('03-tools/chart', 'A square in its chart: the circle meets the line of '
           'the near edge at the angles plus and minus A and the line of '
           'the lower edge at minus V, and the cap runs between')


def budget():
    squares = [((0.772, 0.33), -9.4), ((-0.362, 0.759), 20.8),
               ((-0.84, -0.389), -36.8), ((0.266, -0.881), 39.9)]
    r = 0.5
    xs = [x for c, d in squares for x, _ in square_corners(c, d)]
    ys = [y for c, d in squares for _, y in square_corners(c, d)]
    f = Figure(min(xs) - 0.05, max(xs) + 0.05, min(ys) - 0.05, max(ys) + 0.05,
               150)
    f.circle((0, 0), r)
    for k, (c, d) in enumerate(squares):
        f.square(c, d, fill=FILLS[k], stroke=COLORS[k])
        for t0, t1 in arcs_in(lambda p: in_open_square(p, c, d), r):
            f.arc((0, 0), r, t0, t1, COLORS[k], width=5)
    f.dot((0, 0))
    f.text((0.04, -0.07), 'o', anchor='start')
    f.text((-0.02, -0.34), sb('Γ', 'r', size=16), size=16)
    f.save('03-tools/budget', 'Disjoint squares hold disjoint arcs of a circle around '
           'the disk centre')


def sweep():
    c, d, r = (0.1, 0.05), 20, 5 / 6
    step = (c[0], c[1])
    orange, blue = COLORS[1], COLORS[0]
    far = 30.0
    corners = square_corners(c, d)
    hull = convex_hull(corners + [(x + far * step[0], y + far * step[1])
                                  for x, y in corners])
    f = Figure(-1.0, 1.9, -1.0, 1.25, 170)
    f.polygon(hull, fill=FILLS[1], stroke=orange, width=1.2, dash='5 4',
              opacity=0.8)
    for m in (4.5, 9.0):
        shifted = (c[0] + m * step[0], c[1] + m * step[1])
        f.square(shifted, d, stroke=orange, width=1, dash='2 3')
    f.square(c, d, fill=FILLS[0], stroke=blue)
    f.circle((0, 0), r)
    member = lambda p: point_in_convex(p, hull)
    for t0, t1 in arcs_in(member, r):
        f.arc((0, 0), r, t0, t1, orange, width=5)
    for t0, t1 in arcs_in(lambda p: in_open_square(p, c, d), r):
        f.arc((0, 0), r, t0, t1, blue, width=5)
    tip = (c[0] + 15 * step[0], c[1] + 15 * step[1])
    f.line((0, 0), tip, stroke=INK, width=1.2, dash='3 3', arrow=True)
    f.dot((0, 0))
    f.text((-0.03, -0.06), 'o', anchor='end')
    f.dot(c)
    f.text((c[0] + 0.02, c[1] - 0.07), sb('c', 'S'), anchor='start')
    f.text((-0.1, -0.4), 'S', size=17, color=blue)
    f.text((1.45, 1.02), 'Ŝ', size=19, color=orange)
    f.text((-0.72, 0.62), sb('Γ', 'r', size=16), size=16)
    f.save('03-tools/sweep', 'A square containing the disk centre and copies of it '
           'slid away from the centre; together they form the radial '
           'sweep, which covers a long arc of the circle')


def point_in_convex(p, poly):
    """Whether p is strictly inside the counterclockwise convex polygon."""
    for k in range(len(poly)):
        (x1, y1), (x2, y2) = poly[k], poly[(k + 1) % len(poly)]
        if (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1) <= 0:
            return False
    return True


def convex_hull(pts):
    pts = sorted(set(pts))

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def packing(name, title, centers, R, r=None, labels=(), grey=()):
    m = R + 0.08
    f = Figure(-m, m, -m, m, 150)
    f.circle((0, 0), R, stroke=INK, width=1.2, dash='6 4')
    for k, c in enumerate(centers):
        fill = GREY if k in grey else FILLS[k]
        stroke = FAINT if k in grey else COLORS[k]
        f.square(c, fill=fill, stroke=stroke)
    if r is not None:
        f.circle((0, 0), r)
    for k, c in enumerate(centers):
        if k in grey or r is None:
            continue
        for t0, t1 in arcs_in(lambda p: in_open_square(p, c), r):
            f.arc((0, 0), r, t0, t1, COLORS[k], width=5)
    for pos, s in labels:
        f.text(pos, s, size=13, italic=False)
    f.dot((0, 0))
    f.text((0.05, -0.08), 'o', anchor='start')
    f.save(name, title)


def u(t):
    return (math.cos(t), math.sin(t))


def shift(p, v, k=1.0):
    return (p[0] + k * v[0], p[1] + k * v[1])


def rad(deg):
    return math.radians(deg)


def sb(base, sub, after='', size=15):
    """Text with a subscript, as SVG markup."""
    d = 0.3 * size
    out = f'{base}<tspan dy="{d:.1f}" font-size="{0.68 * size:.1f}">{sub}</tspan>'
    if after:
        out += f'<tspan dy="{-d:.1f}">{after}</tspan>'
    return out


def subsup(base, sub, sup, size=15):
    """Text with a subscript and a superscript stacked, as SVG markup."""
    d, small = 0.3 * size, 0.68 * size
    back = 0.55 * small * len(sub)
    return (f'{base}<tspan dy="{d:.1f}" font-size="{small:.1f}">{sub}</tspan>'
            f'<tspan dx="{-back:.1f}" dy="{-2.2 * d:.1f}" '
            f'font-size="{small:.1f}">{sup}</tspan>')


def subscript(f, pos, base, sub, size=15, color=INK, anchor='middle',
              after=''):
    f.text(pos, sb(base, sub, after, size), size=size, color=color,
           anchor=anchor)


def overlap(P, Q):
    """Whether two convex polygons have overlapping interiors."""
    for poly in (P, Q):
        for i in range(len(poly)):
            a, b = poly[i], poly[(i + 1) % len(poly)]
            n = (b[1] - a[1], a[0] - b[0])
            pa = [n[0] * x + n[1] * y for x, y in P]
            pb = [n[0] * x + n[1] * y for x, y in Q]
            if max(pa) <= min(pb) or max(pb) <= min(pa):
                return False
    return True


def directions():
    r, t1, t2 = 1.0, rad(20), rad(125)
    orange = COLORS[1]
    f = Figure(-1.2, 1.25, -1.12, 1.18, 150)
    f.circle((0, 0), r, stroke=INK)
    for t in (t1, t2):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
        f.dot(shift((0, 0), u(t), r))
    # The unit vector u(theta), with an arrowhead of its own colour.
    (x1, y1), (x0, y0) = f.p(*shift((0, 0), u(t1), 0.45)), f.p(0, 0)
    k = math.hypot(x1 - x0, y1 - y0)
    ex, ey = (x1 - x0) / k, (y1 - y0) / k
    f.line((0, 0), shift((0, 0), u(t1), 0.45 - 6 / f.s), stroke=COLORS[0],
           width=2.4)
    f.add(f'<path d="M {x1:.1f} {y1:.1f} L {x1 - 11 * ex - 4.6 * ey:.1f} '
          f'{y1 - 11 * ey + 4.6 * ex:.1f} L {x1 - 11 * ex + 4.6 * ey:.1f} '
          f'{y1 - 11 * ey - 4.6 * ex:.1f} z" fill="{COLORS[0]}"/>')
    f.text(shift((0.06, -0.08), u(t1), 0.33), 'u(θ)', color=COLORS[0],
           anchor='start')
    f.arc((0, 0), 0.28, t1, t2, orange, width=1.8)
    f.text(shift((0, 0), u((t1 + t2) / 2), 0.43), 'd(θ, θ′)', color=orange)
    f.text(shift((0, 0), u(t1), 1.1), 'θ')
    f.text(shift((0, 0), u(t2), 1.1), 'θ′')
    subscript(f, (-0.85, -0.85), 'Γ', 'r', size=16)
    f.text(shift((0.07, 0.05), u(t2), 0.6), 'r')
    f.dot((0, 0))
    f.text((0.02, -0.08), 'o', anchor='start')
    f.save('03-tools/directions', 'Two directions from o, the unit vector u(theta), '
           'and the angle d between the directions on the circle of radius r')


def local_coordinates():
    d, c = 25, (0.0, 0.0)
    e1, e2 = u(rad(d)), u(rad(d + 90))
    x, y = 0.95, 0.55
    q = shift(c, e1, x)
    p = shift(q, e2, y)
    orange = COLORS[1]
    f = Figure(-0.95, 1.25, -0.8, 1.1, 190)
    f.line(shift(c, e1, -0.9), shift(c, e1, 1.35), stroke=FAINT, dash='4 4')
    f.line(shift(c, e2, -0.8), shift(c, e2, 1.1), stroke=FAINT, dash='4 4')
    f.square(c, d, fill=FILLS[0], stroke=COLORS[0])
    f.line(c, q, stroke=orange, width=2.4)
    f.line(q, p, stroke=orange, width=2.4)
    # The frame vectors on top of the path, so that e1 stays visible.
    f.line(c, shift(c, e1, 0.32), arrow=True)
    f.line(c, shift(c, e2, 0.32), arrow=True)
    f.text(shift(shift(c, e1, 0.38), e2, -0.09), subsup('e', '1', 'S', 14), size=14)
    f.text(shift(shift(c, e2, 0.38), e1, -0.12), subsup('e', '2', 'S', 14), size=14)
    subscript(f, shift(shift(c, e1, 0.72), e2, -0.13), 'x', 'S',
              color=orange, after='(p)')
    subscript(f, shift(shift(q, e2, y / 2), e1, 0.1), 'y', 'S',
              color=orange, anchor='start', after='(p)')
    f.dot(c)
    f.text(shift(c, (-0.05, -0.08)), sb('c', 'S'), anchor='end')
    f.dot(p)
    f.text(shift(p, (0.05, 0.03)), 'p', anchor='start')
    f.text(shift(shift(c, e1, -0.33), e2, 0.32), 'S', size=17,
           color=COLORS[0])
    f.save('02-preliminaries/local-coordinates', 'A unit square with centre c and frame e1, '
           'e2, and the local coordinates of a point p')


def packing_example():
    squares = [((0.05, 0.72), 12), ((-0.66, -0.35), -22), ((0.68, -0.4), 35)]
    polys = [square_corners(c, d) for c, d in squares]
    R = 1.5
    for i in range(3):
        assert max(math.hypot(*q) for q in polys[i]) <= R
        for j in range(i + 1, 3):
            assert not overlap(polys[i], polys[j])
    f = Figure(-1.58, 1.58, -1.58, 1.58, 130)
    f.circle((0, 0), R, stroke=INK, dash='6 4')
    for k, (c, d) in enumerate(squares):
        f.square(c, d, fill=FILLS[k], stroke=COLORS[k])
        subscript(f, c, 'S', str(k + 1), size=17, color=COLORS[k])
    # Draw the radius where it crosses no square.
    def clear(t):
        return not any(in_open_square(shift((0, 0), u(t), k * R / 40), c, d)
                       for c, d in squares for k in range(1, 41))
    t = next(rad(deg) for deg in range(-90, 270, 3) if clear(rad(deg)))
    f.line((0, 0), shift((0, 0), u(t), R), width=1)
    f.text(shift(shift((0, 0), u(t), 0.6 * R), u(t + math.pi / 2), 0.1),
           'R')
    f.dot((0, 0))
    f.text((0.05, 0.08), 'o', anchor='start')
    f.save('02-preliminaries/packing', 'Three pairwise disjoint unit squares '
           'S1, S2, S3 in a closed disk of radius R about o')


def width_figure():
    d, c = 20, (0.0, 0.0)
    e1, e2 = u(rad(d)), u(rad(d + 90))
    n = u(rad(60))
    w = (abs(math.cos(rad(40))) + abs(math.sin(rad(40)))) / 2
    v = shift(shift(c, e1, 0.5), e2, 0.5)
    foot = shift(c, n, w)
    perp = (-n[1], n[0])
    orange = COLORS[1]
    f = Figure(-0.85, 1.05, -0.8, 1.05, 220)
    f.line(shift(c, n, -0.75), shift(c, n, 1.0), stroke=FAINT, dash='4 4')
    f.square(c, d, fill=FILLS[0], stroke=COLORS[0])
    f.line(shift(foot, perp, -0.55), shift(foot, perp, 0.55), width=1,
           dash='5 4')
    f.line(c, foot, stroke=orange, width=2.6)
    f.dot(v, fill=INK)
    f.dot(c)
    f.text(shift(c, (0.05, -0.07)), sb('c', 'S'), anchor='start')
    subscript(f, shift(shift(c, n, w / 2), perp, 0.16), 'w', 'S',
              color=orange, after='(n)')
    f.line((-0.75, 0.75), shift((-0.75, 0.75), n, 0.3), arrow=True,
           width=1.6)
    f.text(shift((-0.72, 0.8), n, 0.3), 'n', anchor='start')
    f.text((-0.22, -0.3), 'S', size=17, color=COLORS[0])
    f.save('03-tools/width', 'The half-width of a square in a unit direction n: how '
           'far the square reaches beyond its centre in that direction')


def arc_figure():
    r, c, d = 0.8, (0.95, 0.45), 15
    runs = arcs_in(lambda p: in_open_square(p, c, d), r)
    t0, t1 = max(runs, key=lambda run: run[1] - run[0])
    theta = t0 + 0.55 * (t1 - t0)
    w = 0.3 * (t1 - t0)
    orange = COLORS[1]
    f = Figure(-0.95, 1.55, -0.95, 1.05, 190)
    f.square(c, d, fill=FILLS[0], stroke=COLORS[0])
    f.circle((0, 0), r)
    f.arc((0, 0), r, t0, t1, orange, width=1.8)
    f.arc((0, 0), r, theta - w, theta + w, orange, width=5)
    f.line((0, 0), shift((0, 0), u(theta), r + 0.2), width=1, dash='4 3')
    for t in (theta - w, theta + w):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    f.arc((0, 0), 0.3, theta, theta + w, INK, width=1.2)
    f.text(shift((0, 0), u(theta + w / 2), 0.4), 'w')
    subscript(f, shift((0, 0), u(theta), r + 0.3), 'θ', '0')
    f.text((1.3, 0.75), 'U', size=17, color=COLORS[0])
    subscript(f, (-0.75, 0.6), 'Γ', 'r', size=16)
    f.dot((0, 0))
    f.text((-0.03, -0.08), 'o', anchor='end')
    f.save('03-tools/arc', 'An arc of a set U on the circle: all points within angle '
           'w of the direction theta zero lie in U')


def chart_panels():
    theta, a, b, r, t = rad(30), 0.9, 0.3, 0.55, rad(30)
    # The point at chart angle t lies in the open square.
    assert abs(r * math.cos(t) - a) < 0.5 and abs(r * math.sin(t) - b) < 0.5
    orange, blue = COLORS[1], COLORS[0]
    right = 2.9
    f = Figure(-0.75, right + 1.7, -0.75, 1.55, 140)
    c = (a * math.cos(theta) - b * math.sin(theta),
         a * math.sin(theta) + b * math.cos(theta))
    # The plane.
    f.text((0.3, 1.47), 'the plane', size=14, italic=False, color=FAINT)
    f.square(c, math.degrees(theta), fill=FILLS[0], stroke=blue)
    f.line((0, 0), shift((0, 0), u(theta), 1.62), width=1)
    subscript(f, shift((0, 0), u(theta), 1.68), 'θ', 'S', anchor='start')
    f.circle((0, 0), r)
    q = shift((0, 0), u(theta + t), r)
    f.line((0, 0), q, width=1)
    f.dot(q, fill=orange)
    f.arc((0, 0), 0.25, theta, theta + t, orange, width=1.6)
    f.text(shift((0, 0), u(theta + t / 2), 0.35), 't', color=orange)
    f.dot((0, 0))
    f.text((-0.03, -0.08), 'o', anchor='end')
    f.dot(c, fill=blue)
    f.text(shift(c, (0.05, -0.07)), sb('c', 'S'), anchor='start', color=blue)
    # The chart.
    o2 = (right, 0)
    f.text((right + 0.35, 1.47), 'the chart', size=14, italic=False,
           color=FAINT)
    f.square(shift(o2, (a, b)), fill=FILLS[0], stroke=blue)
    f.line(o2, shift(o2, (1.68, 0)), width=1)
    f.text(shift(o2, (1.68, 0.08)), '<tspan font-style="italic">t</tspan> = 0',
           size=12, italic=False, anchor='end')
    f.circle(o2, r)
    q2 = shift(o2, u(t), r)
    f.line(o2, q2, width=1)
    f.dot(q2, fill=orange)
    f.arc(o2, 0.25, 0, t, orange, width=1.6)
    f.text(shift(o2, u(t / 2), 0.35), 't', color=orange)
    f.dot(o2)
    f.text(shift(o2, (-0.03, -0.08)), 'o', anchor='end')
    f.dot(shift(o2, (a, b)), fill=blue)
    f.text(shift(o2, (a + 0.05, b - 0.08)), '(' + sb('a', 'S', ', ', 14) + sb('b', 'S', ')', 14), anchor='start',
           color=blue, size=14)
    f.line((1.45, -0.45), (2.2, -0.45), width=1.4, arrow=True)
    f.text((1.82, -0.6), 'turn by −<tspan font-style="italic">' +
           sb('θ', 'S', size=13) + '</tspan>', size=13, italic=False)
    f.save('03-tools/chart-panels', 'A square seen from o, and the same square in its '
           'chart after turning by minus its phase')


def frame_figure():
    phi, c = rad(25), (0.9, 0.45)
    e1, e2 = u(phi), u(phi + math.pi / 2)
    q = shift((0, 0), e1, c[0])
    centre = shift(q, e2, c[1])
    orange = COLORS[1]
    f = Figure(-0.75, 1.75, -0.55, 1.55, 180)
    f.line((-0.7, 0), (1.6, 0), stroke=FAINT, width=1)
    f.line(shift((0, 0), e1, -0.6), shift((0, 0), e1, 1.75), width=1.1,
           arrow=True)
    f.line(shift((0, 0), e2, -0.5), shift((0, 0), e2, 1.4), width=1.1,
           arrow=True)
    f.square(centre, math.degrees(phi), fill=FILLS[0], stroke=COLORS[0])
    f.line((0, 0), q, stroke=orange, width=2.4)
    f.line(q, centre, stroke=orange, width=2.4)
    subscript(f, shift(shift((0, 0), e1, 0.66), e2, 0.1), 'c', '1',
              color=orange)
    subscript(f, shift(shift(q, e2, c[1] / 2), e1, 0.12), 'c', '2',
              color=orange, anchor='start')
    f.arc((0, 0), 0.35, 0, phi, INK, width=1.2)
    f.text(shift((0, 0), u(phi / 2), 0.45), 'φ')
    f.dot(centre, fill=COLORS[0])
    f.dot((0, 0))
    f.text((-0.04, -0.08), 'o', anchor='end')
    f.text(shift(shift(centre, e1, -0.24), e2, 0.27), 'S', size=17,
           color=COLORS[0])
    f.text(shift(shift((0, 0), e1, 1.68), e2, -0.16), 'u(φ)', size=14)
    f.text(shift(shift((0, 0), e2, 1.38), e1, 0.1), 'u(φ + π/2)', size=14,
           anchor='start')
    f.save('02-preliminaries/frame', 'The frame at o turned by phi, with axes '
           'u(phi) and u(phi + pi/2), and a square S sitting at c = (c1, c2) '
           'in that frame')


def congruent_figure():
    """Definition 2.6: a packing congruent to the T. In the frame phi at o
    each square sits at one of the points c1, c2, c3 of the model."""
    phi = rad(35)
    centers = [(-0.5, -5 / 16), (0.5, -5 / 16), (0, 11 / 16)]
    names = ['2', '3', '1']
    R = 5 * math.sqrt(17) / 16
    rot = lambda p: (p[0] * math.cos(phi) - p[1] * math.sin(phi),
                     p[0] * math.sin(phi) + p[1] * math.cos(phi))
    f = Figure(-1.4, 1.75, -1.4, 1.42, 150)
    f.circle((0, 0), R, stroke=INK, dash='6 4')
    f.line(shift((0, 0), u(phi), -1.3), shift((0, 0), u(phi), 1.62),
           stroke=FAINT, width=1)
    f.line(shift((0, 0), u(phi + math.pi / 2), -1.3),
           shift((0, 0), u(phi + math.pi / 2), 1.35), stroke=FAINT, width=1)
    # The angle phi of the frame, outside the circle.
    f.line((0, 0), (1.62, 0), stroke=FAINT, width=1, dash='3 3')
    f.arc((0, 0), 1.45, 0, phi, INK, width=1.2)
    f.text(shift((0, 0), u(phi / 2), 1.58), 'φ')
    for k, (c, name) in enumerate(zip(centers, names)):
        # The square in the slot c_k is the square of the model at c_k,
        # turned by phi about o.
        assert all(in_open_square(rot(x), rot(c), math.degrees(phi))
                   for x in (shift(c, (0.4, 0.3)), shift(c, (-0.3, -0.45))))
        f.square(rot(c), math.degrees(phi), fill=FILLS[k], stroke=COLORS[k])
        subscript(f, rot(shift(c, (0, 0.17))), 'S', name, size=16,
                  color=COLORS[k])
        f.dot(rot(c), fill=INK)
        subscript(f, rot(shift(c, (0, -0.15))), 'c', str(k + 1), size=14)
    f.dot((0, 0))
    f.text((0.05, 0.08), 'o', anchor='start')
    f.save('02-preliminaries/congruent', 'A packing congruent to the T: in '
           'the frame at o turned by phi, the squares S2, S3, S1 sit at the '
           'points c1, c2, c3 of the model')


def inscribed_disks():
    alpha, o = 0.25, (-0.25, 0.2)
    # Lemma 3.9 (2) with a_S = alpha: the disk about o touches a side.
    assert max(abs(o[0]), abs(o[1])) == alpha
    orange, blue = COLORS[1], COLORS[0]
    f = Figure(-0.62, 0.62, -0.62, 0.62, 280)
    f.square((0, 0), fill=FILLS[0], stroke=blue)
    f.circle((0, 0), 0.5, stroke=blue, width=1.4, dash='5 4')
    f.circle(o, 0.5 - alpha, stroke=orange, width=1.6, fill=FILLS[1])
    f.line((0, 0), shift((0, 0), u(rad(-35)), 0.5), stroke=blue, width=1.2)
    f.text(shift((0.02, 0.05), u(rad(-35)), 0.3), '½', color=blue,
           italic=False)
    f.line(o, shift(o, u(rad(150)), 0.5 - alpha), stroke=orange, width=1.2)
    f.text(shift(o, (0.02, 0.1)), '½ − α', color=orange, size=13,
           anchor='end')
    f.dot((0, 0))
    f.text((-0.03, -0.05), sb('c', 'S'), anchor='end')
    f.dot(o, fill=orange)
    f.text(shift(o, (0.04, -0.05)), 'o', anchor='start', color=orange)
    f.save('03-tools/inscribed-disks', 'The disk of radius one half about the centre, '
           'and the disk of radius one half minus alpha about o, both inside '
           'the open square')


def midpoint_figure():
    s, t = ((-0.42, -0.05), 15), ((0.38, 0.1), -20)
    m = ((s[0][0] + t[0][0]) / 2, (s[0][1] + t[0][1]) / 2)
    f = Figure(-1.05, 1.05, -0.8, 0.85, 220)
    for k, (c, d) in enumerate((s, t)):
        f.square(c, d, fill=FILLS[2 * k], stroke=COLORS[2 * k], opacity=0.6)
        f.circle(c, 0.5, stroke=COLORS[2 * k], width=1.2, dash='5 4')
        f.dot(c, fill=COLORS[2 * k])
    f.line(s[0], t[0], width=1.2)
    f.dot(m, r=4)
    f.text(shift(m, (0.0, 0.09)), 'm')
    subscript(f, shift(s[0], (-0.02, -0.1)), 'c', 'S', color=COLORS[0])
    subscript(f, shift(t[0], (0.0, -0.1)), 'c', 'T', color=COLORS[2])
    f.save('03-tools/midpoint', 'Two squares whose centres are less than 1 apart: '
           'the midpoint lies in both inscribed disks')


def shadows():
    s, t = ((-0.75, 0.05), 20), ((0.8, -0.1), -35)
    ws = (math.cos(rad(20)) + math.sin(rad(20))) / 2
    wt = (math.cos(rad(35)) + math.sin(rad(35))) / 2
    y0 = -0.95
    f = Figure(-1.55, 1.65, -1.15, 0.85, 170)
    for k, (c, d), w in ((0, s, ws), (2, t, wt)):
        f.square(c, d, fill=FILLS[k], stroke=COLORS[k])
        f.dot(c, fill=COLORS[k])
        f.line((c[0] - w, y0), (c[0] + w, y0), stroke=COLORS[k], width=5)
        f.line((c[0], y0 - 0.04), (c[0], y0 + 0.04), stroke=COLORS[k],
               width=1.6)
        f.line(c, (c[0], y0), stroke=COLORS[k], width=1, dash='3 3')
    f.line((-1.5, y0), (1.6, y0), width=1, arrow=True)
    f.text((1.6, y0 + 0.08), 'n', anchor='end')
    f.line((0, -0.85), (0, 0.8), width=1.2, dash='6 4')
    subscript(f, (s[0][0] + ws / 2, y0 - 0.11), 'w', 'S', size=14,
              color=COLORS[0], after='(n)')
    subscript(f, (t[0][0] - wt / 2, y0 - 0.11), 'w', 'T', size=14,
              color=COLORS[2], after='(n)')
    f.text((-1.2, 0.62), 'S', size=17, color=COLORS[0])
    f.text((1.3, 0.55), 'T', size=17, color=COLORS[2])
    f.save('03-tools/shadows', 'Two disjoint squares and a separating direction n: '
           'their shadows on a line in direction n do not overlap')


def edge_contact():
    d = 20
    e1 = u(rad(d))
    s, t = (0.0, 0.0), shift((0.0, 0.0), e1, 1.0)
    f = Figure(-0.75, 1.72, -0.72, 1.05, 190)
    f.square(s, d, fill=FILLS[0], stroke=COLORS[0])
    f.square(t, d, fill=FILLS[2], stroke=COLORS[2])
    f.line(s, t, width=1.4)
    f.dot(s, fill=COLORS[0])
    f.dot(t, fill=COLORS[2])
    f.text(shift(shift(s, e1, 0.72), u(rad(d + 90)), 0.1), '1',
           italic=False)
    subscript(f, shift(s, (-0.05, -0.1)), 'c', 'S', color=COLORS[0])
    subscript(f, shift(t, (0.0, -0.1)), 'c', 'T', color=COLORS[2])
    f.save('03-tools/edge-contact', 'Two squares with centres exactly 1 apart share a '
           'full edge')


def arc_centres():
    r = 1.0
    arcs = [(rad(20), rad(40), COLORS[0], 'U'), (rad(128), rad(35), COLORS[2],
                                                  'V')]
    f = Figure(-1.25, 1.3, -1.1, 1.3, 160)
    f.circle((0, 0), r)
    for c, w, color, name in arcs:
        f.arc((0, 0), r, c - w, c + w, color, width=5)
        f.line((0, 0), shift((0, 0), u(c), r), stroke=color, width=1.2,
               dash='4 3')
        f.text(shift((0, 0), u(c), r + 0.14), name, color=color, size=16)
    f.arc((0, 0), 0.32, arcs[0][0], arcs[1][0], INK, width=1.4)
    label = ('≥ ' + sb('w', 'U', ' + ', 14) + sb('w', 'V', '', 14))
    f.text(shift((0, 0), u((arcs[0][0] + arcs[1][0]) / 2), 0.55), label,
           size=14)
    f.dot((0, 0))
    f.text((0.03, -0.08), 'o', anchor='start')
    f.save('03-tools/arc-centres', 'Two disjoint arcs on a circle: their centres are '
           'at least the sum of their half-widths apart')


def rectangle_interval():
    r, a, b = 5 / 6, 0.95, 0.1
    lo = math.asin((b - 0.5) / r)
    hi = min(math.acos((a - 0.5) / r), math.asin((b + 0.5) / r))
    A = math.acos((a - 0.5) / r)
    U = math.asin((b + 0.5) / r)
    # The arc runs from -V to U: the upper edge comes before the near edge.
    assert hi == U < A
    runs = arcs_in(lambda p: in_open_square(p, (a, b)), r, steps=14400)
    t0, t1 = max(runs, key=lambda run: run[1] - run[0])
    assert abs(t0 - 2 * math.pi - lo) < 1e-3
    assert abs(t1 - 2 * math.pi - hi) < 1e-3
    orange = COLORS[1]
    f = Figure(-0.95, 1.6, -0.95, 1.05, 200)
    f.square((a, b), fill=FILLS[0], stroke=COLORS[0])
    f.dot((a, b), fill=COLORS[0])
    f.text((a + 0.04, b + 0.07), pair(('a', 'S'), ('b', 'S'), 14),
           anchor='start', size=14, color=COLORS[0])
    for x0, y0, x1, y1 in ((a - 0.5, -0.93, a - 0.5, 1.0),
                           (-0.93, b - 0.5, 1.58, b - 0.5),
                           (-0.93, b + 0.5, 1.58, b + 0.5)):
        f.line((x0, y0), (x1, y1), width=1, dash='4 4')
    f.text((a - 0.5 - 0.03, 0.97), 'near edge', size=12, italic=False,
           anchor='end')
    # Inside the circle, which crosses the line of the lower edge further left.
    f.text((-0.6, b - 0.5 - 0.06), 'lower edge', size=12, italic=False,
           anchor='start')
    f.text((-0.9, b + 0.5 + 0.06), 'upper edge', size=12, italic=False,
           anchor='start')
    f.line((-0.93, 0), (1.58, 0), stroke=FAINT, width=1)
    f.circle((0, 0), r)
    f.arc((0, 0), r, lo, hi, orange, width=5)
    for t in (lo, hi):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
        f.dot(shift((0, 0), u(t), r))
    f.dot(shift((0, 0), u(A), r), fill=FAINT)
    subscript(f, shift((0, 0), u(hi), r + 0.13), 'U', 'S', size=14)
    f.text(shift((0, 0), u(lo), r + 0.16), '−' + sb('V', 'S', size=14),
           size=14)
    subscript(f, shift((0, 0), u(A + 0.15), r + 0.1), 'A', 'S', size=14,
              color=FAINT, anchor='end')
    f.dot((0, 0))
    f.text((-0.03, -0.08), 'o', anchor='end')
    subscript(f, (-0.72, -0.72), 'Γ', 'r', size=16)
    f.save('03-tools/rectangle-interval', 'On a larger circle the arc of an exterior '
           'square runs from the lower edge to the upper edge')


def safe_sweep():
    s, t = (0.15, 0.1), (-0.9, 0.2)
    orange, blue, green = COLORS[1], COLORS[0], COLORS[2]
    corners = square_corners(s)
    hull = convex_hull(corners + [shift(q, s, 12) for q in corners])
    f = Figure(-1.55, 1.75, -0.7, 1.2, 160)
    f.polygon(hull, fill=FILLS[1], stroke=orange, width=1.2, dash='5 4',
              opacity=0.8)
    f.square(s, fill=FILLS[0], stroke=blue)
    f.square(t, fill=FILLS[2], stroke=green)
    f.line((-0.375, -0.68), (-0.375, 1.15), width=1.4, dash='6 4')
    f.line((-0.375, 0.95), (-0.72, 0.95), width=1.6, arrow=True)
    f.text((-0.74, 1.04), 'n', anchor='end')
    f.line((0, 0), shift((0, 0), s, 7.5), width=1.2, dash='3 3', arrow=True)
    f.dot((0, 0))
    f.text((-0.03, -0.08), 'o', anchor='end')
    f.dot(s, fill=blue)
    subscript(f, shift(s, (0.03, -0.1)), 'c', 'S', color=blue,
              anchor='start')
    f.text((0.25, -0.25), 'S', size=17, color=blue)
    f.text((-1.2, 0.5), 'T', size=17, color=green)
    f.text((1.5, 0.95), 'Ŝ', size=19, color=orange)
    f.save('03-tools/safe-sweep', 'The separating line between S and T; the ray from '
           'o through the centre of S points away from T, so the sweep of S '
           'stays on its side')


def clip(poly, a, b, c):
    """The part of a convex polygon where a x + b y <= c."""
    out = []
    for k in range(len(poly)):
        p, q = poly[k], poly[(k + 1) % len(poly)]
        fp, fq = a * p[0] + b * p[1] - c, a * q[0] + b * q[1] - c
        if fp <= 0:
            out.append(p)
        if fp * fq < 0:
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def clip_square(poly, c, deg=0.0):
    """The part of a convex polygon inside the closed square at c."""
    t = math.radians(deg)
    for e in ((math.cos(t), math.sin(t)), (-math.sin(t), math.cos(t))):
        for sgn in (1, -1):
            a, b = sgn * e[0], sgn * e[1]
            poly = clip(poly, a, b, a * c[0] + b * c[1] + 0.5)
    return poly


def pair(a, b, size=15):
    """The markup of the pair (a_S, b_S), with other subscripts if asked."""
    return '(' + sb(a[0], a[1], ', ', size) + sb(b[0], b[1], ')', size)


def quadrant_disk(K, steps=80):
    """The part of the disk phi <= K with a, b >= 0, as a polygon."""
    R = math.sqrt(K)
    t0 = math.asin(0.5 / R)
    t1 = math.pi / 2 - t0
    return [(0, 0)] + [(-0.5 + R * math.cos(t0 + (t1 - t0) * k / steps),
                        -0.5 + R * math.sin(t0 + (t1 - t0) * k / steps))
                       for k in range(steps + 1)]


def ab_axes(f, top):
    f.line((-0.1, 0), (top, 0), width=1, arrow=True)
    f.line((0, -0.1), (0, top), width=1, arrow=True)
    f.text((top, -0.06), 'a', anchor='end')
    f.text((-0.06, top - 0.02), 'b', anchor='end')


def containing_exterior():
    f = Figure(-0.8, 3.05, -0.78, 0.95, 170)
    a_s = '<tspan font-style="italic">' + sb('a', 'S', size=14) + '</tspan>'
    for dx, d, o, label, color in (
            (0.0, 15, (0.2, 0.12),
             a_s + '<tspan dy="-4.2"> &lt; ½</tspan>', 0),
            (2.25, -20, (-0.8, -0.3),
             a_s + '<tspan dy="-4.2"> ≥ ½</tspan>', 2)):
        c = (dx, 0.0)
        t = rad(d)
        po = (c[0] + o[0] * math.cos(t) - o[1] * math.sin(t),
              c[1] + o[0] * math.sin(t) + o[1] * math.cos(t))
        assert in_open_square(po, c, d) == (color == 0)
        f.square(c, d, fill=FILLS[color], stroke=COLORS[color])
        f.dot(c, fill=COLORS[color])
        f.text(shift(c, (0.04, -0.08)), sb('c', 'S'), anchor='start',
               color=COLORS[color])
        f.dot(po)
        f.text(shift(po, (-0.04, 0.07)), 'o', anchor='end')
        name = 'containing' if color == 0 else 'exterior'
        f.text((dx, 0.86), name + ': ' + label, size=14, italic=False,
               color=COLORS[color])
    f.save('03-tools/containing-exterior', 'Left: a containing square, with the disk '
           'centre o inside it. Right: an exterior square, with o outside it')


def tangent_half_plane():
    K = 2.0
    R = math.sqrt(K)
    orange, blue = COLORS[1], COLORS[0]
    lo, hi = -2.0, 1.45
    f = Figure(lo, hi, lo, hi, 140)
    box = [(lo, lo), (hi, lo), (hi, hi), (lo, hi)]
    f.polygon(clip(box, 1, 1, 1), fill=FILLS[1], stroke='none')
    f.circle((-0.5, -0.5), R, stroke=blue, width=1.6, fill=FILLS[0])
    f.line((hi, 1 - hi), (1 - hi, hi), stroke=orange, width=2)
    f.line((lo + 0.05, 0), (hi - 0.05, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, lo + 0.05), (0, hi - 0.05), stroke=FAINT, width=1, arrow=True)
    f.text((hi - 0.05, -0.1), 'a', anchor='end', color=FAINT)
    f.text((-0.1, hi - 0.08), 'b', anchor='end', color=FAINT)
    f.dot((0.5, 0.5), r=4)
    f.text((0.58, 0.62), '(u, v)', anchor='start', size=14)
    f.dot((-0.5, -0.5), fill=blue)
    f.text((-0.45, -0.62), '(−½, −½)', size=13, italic=False, color=blue,
           anchor='start')
    f.text((-1.0, -1.1), 'φ ≤ K', size=16, color=blue)
    f.text((0.95, -1.7), 'tangent half-plane', size=14, italic=False,
           color=orange)
    f.save('03-tools/tangent-half-plane', 'The disk where phi is at most K in the '
           '(a, b)-plane, a point (u, v) on its boundary, and the tangent '
           'half-plane there, which contains the disk')


def four_directions():
    r = 1.0
    t0 = rad(25)
    f = Figure(-1.55, 1.6, -1.3, 1.35, 150)
    f.circle((0, 0), r)
    names = ['', ' + π/2', ' + π', ' + 3π/2']
    for k in range(4):
        t = t0 + k * math.pi / 2
        q = shift((0, 0), u(t), r)
        f.line((0, 0), q, width=1.4)
        f.dot(q)
        anchor = 'start' if math.cos(t) > 0.2 else (
            'end' if math.cos(t) < -0.2 else 'middle')
        f.text(shift((0, 0), u(t), 1.12), sb('θ', '0', names[k]),
               anchor=anchor)
    a1 = shift((0, 0), u(t0), 0.13)
    a2 = shift(a1, u(t0 + math.pi / 2), 0.13)
    a3 = shift((0, 0), u(t0 + math.pi / 2), 0.13)
    f.line(a1, a2, width=1)
    f.line(a2, a3, width=1)
    f.dot((0, 0))
    f.text((-0.06, -0.14), 'o', anchor='end')
    f.save('03-tools/four-directions', 'Four directions pairwise at least a quarter '
           'turn apart: they are a first direction and its quarter turns')


def parallelogram():
    """Lemma 5.5. Left: two centres in the closed disk of radius 1/2 about
    o, the parallelogram with the sides u = c_S - o and v = c_T - o, and its
    diagonals u - v and u + v. Right: the equality case u + v = 0, where the
    centres are opposite points of the circle, exactly 1 apart."""
    from fig_front import it
    from fig_one import label, isb
    orange, blue, green = COLORS[1], COLORS[0], COLORS[2]
    o, cs, ct = (0.0, 0.0), (-0.4, -0.2), (0.15, 0.4)
    far = (cs[0] + ct[0], cs[1] + ct[1])
    assert all(math.hypot(*c) <= 0.5 for c in (cs, ct))
    # The parallelogram law, with u = c_S - o and v = c_T - o.
    lhs = math.dist(cs, ct) ** 2 + math.hypot(*far) ** 2
    rhs = 2 * math.hypot(*cs) ** 2 + 2 * math.hypot(*ct) ** 2
    assert abs(lhs - rhs) < 1e-12 and math.dist(cs, ct) < 1

    def towards(p, q, gap):
        """The point of the segment pq at distance gap before q."""
        d = math.dist(p, q)
        return shift(q, ((p[0] - q[0]) / d, (p[1] - q[1]) / d), gap)

    f = Figure(-0.64, 2.12, -0.68, 0.6, 300)
    f.circle(o, 0.5, stroke=INK, dash='5 4')
    f.polygon([o, cs, far, ct], fill=FILLS[1], stroke=FAINT, width=1)
    f.line(cs, ct, stroke=orange, width=2.2)
    f.line(o, far, stroke=INK, width=1.2, dash='3 3')
    f.line(o, towards(o, cs, 0.015), width=1.3, arrow=True)
    f.line(o, towards(o, ct, 0.015), width=1.3, arrow=True)
    f.text((-0.17, -0.18), 'u')
    f.text((0.14, 0.17), 'v')
    f.text(shift(far, (0.0, 0.08)), 'u + v', size=14)
    t = rad(-20)
    f.line(o, shift(o, u(t), 0.5), width=1)
    f.text(shift(shift(o, u(t), 0.3), u(t + math.pi / 2), -0.06), '½',
           italic=False)
    f.dot(o)
    f.text((0.0, -0.08), 'o')
    f.dot(far, r=2.5, fill=FAINT)
    f.dot(cs, fill=blue)
    subscript(f, shift(cs, (-0.16, -0.07)), 'c', 'S', color=blue,
              anchor='start')
    f.dot(ct, fill=green)
    subscript(f, shift(ct, (0.05, -0.02)), 'c', 'T', color=green,
              anchor='start')
    # Right: equality, u + v = 0.
    o2 = (1.6, 0.0)
    th = rad(20)
    cs2, ct2 = shift(o2, u(th + math.pi), 0.5), shift(o2, u(th), 0.5)
    assert abs(math.dist(cs2, ct2) - 1) < 1e-12
    f.circle(o2, 0.5, stroke=INK, dash='5 4')
    f.line(cs2, ct2, stroke=orange, width=2.2)
    f.dot(o2)
    f.text(shift(o2, (-0.02, 0.08)), 'o')
    f.dot(cs2, fill=blue)
    subscript(f, shift(cs2, (0.02, 0.07)), 'c', 'S', color=blue,
              anchor='start')
    f.dot(ct2, fill=green)
    subscript(f, shift(ct2, (-0.13, -0.08)), 'c', 'T', color=green,
              anchor='start')
    label(f, (o2[0], -0.6), it('u') + ' + ' + it('v') + ' = 0,  |' +
          isb('c', 'S', ' − ', 14) + isb('c', 'T', '| = 1', 14), size=14,
          italic=False)
    f.save('05-two/parallelogram', 'Left: two centres c_S and c_T inside the '
           'dashed circle of radius one half about o, the parallelogram with '
           'sides u from o to c_S and v from o to c_T, and its diagonals u '
           'minus v, between the centres, and u plus v, dashed from o. Right: '
           'the equality case, where the centres are opposite points of the '
           'circle, 1 apart, and o is their midpoint')


def contact_types():
    from fig_three import label, pair_s, arc
    orange = COLORS[1]
    off = 2.25
    f = Figure(-0.62, off + 1.47, -0.62, 1.12, 190)
    for dx, c, color, name, value, mid in (
            (0.0, (11 / 16, 0.0), 0, 'type A', '(11/16, 0)', 0.0),
            (off, (0.5, 5 / 16), 2, 'type B', '(½, 5/16)', math.pi / 6)):
        o = (dx, 0.0)
        centre = shift(o, c)
        f.line(shift(o, (-0.45, 0)), shift(o, (1.45, 0)), stroke=FAINT,
               width=1)
        f.text(shift(o, (1.45, 0.05)), 't = 0', size=12, italic=False,
               color=FAINT, anchor='end')
        f.square(centre, fill=FILLS[color], stroke=COLORS[color])
        f.dot(centre, fill=COLORS[color])
        f.circle(o, 3 / 8)
        (t0, t1), = arcs_in(lambda p: in_open_square(shift(p, o), centre),
                            3 / 8)
        # A third of the circle, centred at the chart angle 0 for type A and
        # pi/6 for type B (Lemma 6.9).
        assert abs((t1 - t0) - 2 * math.pi / 3) < 2e-3
        assert math.cos((t0 + t1) / 2 - mid) > 1 - 1e-5
        arc(f, o, 3 / 8, t0, t1, orange, width=5)
        f.line(shift(o, u(mid), 3 / 8 - 0.05), shift(o, u(mid), 3 / 8 + 0.05),
               width=2.2)
        f.text(shift(o, u(mid + 0.75), 0.49), '2π/3', size=13, color=orange,
               italic=False)
        f.dot(o)
        f.text(shift(o, (-0.04, -0.08)), 'o', anchor='end')
        q = shift(o, u(rad(212)), 3 / 8)
        f.line(q, shift(o, (-0.44, -0.33)), width=0.8)
        subscript(f, shift(o, (-0.45, -0.36)), 'Γ', '3/8', size=14,
                  anchor='end')
        label(f, (dx + 0.6, 1.03), name, 14, 'middle', color=COLORS[color],
              italic=False)
        label(f, (dx + 0.6, 0.9), pair_s(13) + '<tspan font-style="normal">'
              f' = {value}</tspan>', 13, 'middle', color=COLORS[color])
    o = (off, 0.0)
    label(f, shift(o, u(math.pi / 6 - 0.25), 0.49), 't = π/6', 12,
          color=INK, italic=False)
    f.circle(o, 3 / 16)
    (t0, t1), = arcs_in(lambda p: in_open_square(shift(p, o),
                                                 (off + 0.5, 5 / 16)), 3 / 16)
    assert abs((t1 - t0) - math.pi) < 2e-3
    arc(f, o, 3 / 16, t0, t1, COLORS[3], width=4)
    q = shift(o, u(rad(-70)), 3 / 16)
    f.line(q, shift(o, (0.16, -0.42)), width=0.8)
    subscript(f, shift(o, (0.17, -0.46)), 'Γ', '3/16', size=14,
              anchor='start')
    f.save('06-three/contact-types', 'Left: a type A square in its chart, holding '
           'a third of the circle of radius 3/8, centred on its axis. '
           'Right: a type B square, holding a third of that circle, centred '
           'at the chart angle pi/6, and half of the small circle of radius '
           '3/16')


def containing_arc():
    from fig_three import label, pair_s
    from fig_front import it
    a, b, r = 0.4, 0.25, 3 / 8
    P, Q = (0.5 - a) / r, (0.5 - b) / r
    lo, hi = -math.asin(Q), math.pi / 2 + math.asin(P)
    (t0, t1), = arcs_in(lambda p: in_open_square(p, (a, b)), r)
    t0, t1 = math.remainder(t0, 2 * math.pi), math.remainder(t1, 2 * math.pi)
    assert abs(t0 - lo) < 2e-3 and abs(t1 - hi) < 2e-3
    orange = COLORS[1]
    f = Figure(-0.78, 1.2, -0.62, 0.95, 260)
    f.line((-0.6, 0), (1.05, 0), stroke=FAINT, width=1)
    f.line((0, -0.55), (0, 0.9), stroke=FAINT, width=1)
    f.square((a, b), fill=FILLS[0], stroke=COLORS[0])
    f.circle((0, 0), r)
    f.arc((0, 0), r, lo, hi, orange, width=5)
    for t in (lo, hi):
        f.line((0, 0), shift((0, 0), u(t), r), width=1)
    f.arc((0, 0), 0.1, lo, hi, INK, width=1.2)
    subscript(f, shift((0, 0), u((lo + hi) / 2), 0.17), 'L', 'S',
              color=orange)
    label(f, shift((0, 0), u(hi), r + 0.07), 'π/2 + arcsin ' +
          it(sb('P', 'S', size=13)), 13, 'end', italic=False)
    label(f, shift((0, 0), u(lo), r + 0.05), '−arcsin ' +
          it(sb('Q', 'S', size=13)), 13, italic=False)
    f.dot((a, b), fill=COLORS[0])
    label(f, (a + 0.04, b + 0.05), pair_s(14), 14, color=COLORS[0])
    f.dot((0, 0))
    f.text((-0.03, -0.07), 'o', anchor='end')
    f.text((a + 0.4, b + 0.4), 'S', size=17, color=COLORS[0])
    f.save('06-three/containing-arc', 'A square containing o, in its chart, and the '
           'arc of the circle of radius 3/8 that it holds, from the chart '
           'angle minus arcsin Q_S on its lower edge to pi/2 plus arcsin P_S '
           'on its left edge')


def radial_gap():
    from fig_three import label
    aS, bS, d = 0.35, -0.1, 0
    t = rad(d)
    s = (-(aS * math.cos(t) - bS * math.sin(t)),
         -(aS * math.sin(t) + bS * math.cos(t)))
    tc = (0.68, 0.04)
    assert not overlap(square_corners(s, d), square_corners(tc))
    orange = COLORS[1]
    rho, gap = 0.5 - aS, tc[0] - 0.5
    f = Figure(-1.0, 1.25, -0.82, 0.72, 300)
    f.square(s, d, fill=FILLS[0], stroke=COLORS[0])
    f.square(tc, fill=FILLS[2], stroke=COLORS[2])
    f.circle((0, 0), rho, stroke=orange, width=1.6, fill=FILLS[1])
    f.dot((0, 0))
    f.text((-0.03, 0.06), 'o', anchor='end')
    f.line((0, 0), (0, -0.78), stroke=FAINT, width=1, dash='3 3')
    f.line((gap, -0.46), (gap, -0.78), stroke=FAINT, width=1, dash='3 3')
    f.line((0, -0.62), (rho, -0.62), stroke=orange, width=2.4)
    label(f, (-0.05, -0.62), '½ − ' + sb('a', 'S', size=14), 14, 'end',
          color=orange)
    f.line((0, -0.74), (gap, -0.74), width=2.4)
    label(f, (-0.05, -0.74), sb('a', 'T', '\u00a0−\u00a0½', 14), 14, 'end')
    f.text((-0.75, 0.5), 'S', size=17, color=COLORS[0])
    f.text((1.08, 0.46), 'T', size=17, color=COLORS[2])
    f.save('06-three/radial-gap', 'The disk about o of radius one half minus a_S lies '
           'in the containing square S, and the near edge of T is at least '
           'that far from o')


def near_axis_overlap():
    a, b = 0.6, 0.03
    delta = rad(122)
    assert 2 * math.pi / 3 < delta < 2 * math.pi / 3 + 1 / 7
    ts = (a, b)
    tu = (a * math.cos(delta) - b * math.sin(delta),
          a * math.sin(delta) + b * math.cos(delta))
    z = (0.2, 0.4)
    ddeg = math.degrees(delta)
    assert in_open_square(z, ts) and in_open_square(z, tu, ddeg)
    f = Figure(-1.25, 1.2, -0.62, 1.25, 190)
    f.square(ts, fill=FILLS[0], stroke=COLORS[0])
    f.square(tu, ddeg, fill=FILLS[2], stroke=COLORS[2])
    f.polygon(clip_square(square_corners(ts), tu, ddeg), fill=FILLS[1],
              stroke=COLORS[1], width=1.4)
    f.square(ts, stroke=COLORS[0])
    for t, color in ((0, COLORS[0]), (delta, COLORS[2])):
        f.line((0, 0), shift((0, 0), u(t), 1.15), stroke=color, width=1,
               dash='4 3')
    f.arc((0, 0), 0.22, 0, delta, INK, width=1.2)
    f.text(shift((0, 0), u(rad(100)), 0.31), '122°', size=13, italic=False)
    f.dot(z, r=4.5, fill=COLORS[1])
    f.text(shift(z, (-0.06, 0.0)), 'z', anchor='end', color=COLORS[1])
    f.dot((0, 0))
    f.text((0.03, -0.07), 'o', anchor='start')
    f.text((1.05, -0.4), 'T', size=17, color=COLORS[0])
    f.text((-1.05, 0.95), 'U', size=17, color=COLORS[2])
    f.save('06-three/near-axis-overlap', 'Two nearly axial squares whose phases are '
           '122 degrees apart, a little more than a third of a turn, overlap; '
           'the point z lies in both')


def slid_disk():
    c, d, r = (0.1, 0.05), 20, 5 / 6
    orange, blue = COLORS[1], COLORS[0]
    L = math.hypot(*c)
    k = (1 / math.sqrt(2)) / L
    cstar = (c[0] * k, c[1] * k)
    theta = math.atan2(c[1], c[0])
    f = Figure(-0.95, 1.5, -0.95, 1.05, 200)
    f.square(c, d, fill=FILLS[0], stroke=blue)
    f.square(cstar, d, stroke=orange, width=1.2, dash='4 3')
    f.circle(cstar, 0.5, stroke=orange, width=1.6, fill=FILLS[1])
    f.circle((0, 0), r)
    f.arc((0, 0), r, theta - math.pi / 5, theta + math.pi / 5, orange,
          width=5)
    f.line((0, 0), shift((0, 0), u(theta), 1.4), width=1, dash='2 3',
           arrow=True)
    f.text(shift(shift((0, 0), u(theta), 0.4), u(theta - math.pi / 2), 0.08),
           '√2/2', size=13, italic=False)
    f.dot((0, 0))
    f.text((-0.03, -0.07), 'o', anchor='end')
    f.dot(cstar, fill=orange)
    f.text(shift(cstar, (0.03, -0.08)),
           'c<tspan dy="-6" font-size="11">*</tspan>', anchor='start',
           color=orange)
    f.text((-0.45, -0.45), 'S', size=17, color=blue)
    f.save('08-five/slid-disk', 'A square containing o slid outward until its centre '
           'is at distance root 2 over 2; its inscribed disk covers a fifth '
           'of the circle of radius 5/6')


def dodecagon_disk():
    from fig_three import eqn
    corner = (4 - math.sqrt(5)) / 2
    poly = convex_hull([(0, 0), (1, 0), (corner, 3 - 3 * corner),
                        (3 - 3 * corner, corner), (0, 1)])
    assert all(x * x + y * y <= 1 + 1e-12 for x, y in poly)
    assert abs(0.75 ** 2 + 0.75 ** 2 - 9 / 8) < 1e-12
    orange, blue = COLORS[1], COLORS[0]
    f = Figure(-0.15, 1.25, -0.15, 1.25, 280)
    f.polygon(poly, fill=FILLS[1], stroke=orange, width=2)
    # The first two sides alone meet at (3/4, 3/4), outside the unit circle.
    for p in ((corner, 3 - 3 * corner), (3 - 3 * corner, corner)):
        f.line(p, (0.75, 0.75), stroke=orange, width=1.2, dash='4 3')
    f.arc((0, 0), 1.0, 0, math.pi / 2, blue, width=2)
    ab_axes(f, 1.22)
    for q in ((1, 0), (0, 1)):
        f.dot(q, r=3.6)
    f.circle((0.75, 0.75), 4 / f.s, stroke=orange, width=1.4, fill='#ffffff')
    f.text((0.79, 0.8), '(¾, ¾)', size=13, italic=False, anchor='start')
    f.text((0.35, 0.35), sb('P', '5', size=16), size=16, color=orange)
    f.text((0.86, 0.6), eqn('a² + b² = 1'), size=13, italic=False,
           color=blue, anchor='start')
    f.save('08-five/dodecagon-disk', 'The 12-gon of five squares, in the quadrant a, '
           'b at least 0, lies inside the unit disk and touches it at (1, 0) '
           'and (0, 1); its first two sides alone would meet at (3/4, 3/4), '
           'outside the disk')


def sixteen_gon():
    K = 425 / 256
    orange, blue = COLORS[1], COLORS[0]
    facets = [(16, 13, 193 / 16), (13, 16, 193 / 16), (19, 8, 209 / 16),
              (8, 19, 209 / 16)]
    poly = [(0, 0), (2, 0), (2, 2), (0, 2)]
    for a, b, c in facets:
        poly = clip(poly, a, b, c)
    f = Figure(-0.12, 0.9, -0.12, 0.9, 480)
    f.polygon(poly, fill=FILLS[1], stroke=orange, width=2)
    f.polygon(quadrant_disk(K), fill=FILLS[0], stroke=blue, width=1.4)
    f.polygon(poly, stroke=orange, width=2)
    ab_axes(f, 0.88)
    for q, name in (((11 / 16, 0), 'A'), ((0, 11 / 16), 'A'),
                    ((0.5, 5 / 16), 'B'), ((5 / 16, 0.5), 'B')):
        f.dot(q, r=4)
        f.text(shift(q, (0.035, 0.035)), name, size=15, anchor='start',
               italic=False)
    f.text((0.25, 0.25), 'φ ≤ 425/256', size=14, color=blue)
    f.text((0.6, 0.55), sb('P', '3', size=16), size=16, color=orange,
           anchor='start')
    f.save('06-three/sixteen-gon', 'The part with a, b at least 0 of the 16-gon of '
           'three squares, hugging the disk where phi is at most 425/256; the '
           'disk touches it at the type A and type B points')


def diamond():
    orange, blue = COLORS[1], COLORS[0]
    f = Figure(-0.12, 1.15, -0.12, 1.15, 330)
    f.polygon([(0, 0), (1, 0), (0, 1)], fill=FILLS[1], stroke=orange,
              width=2)
    f.polygon(quadrant_disk(2), fill=FILLS[0], stroke=blue, width=1.4)
    ab_axes(f, 1.12)
    f.dot((0.5, 0.5), r=4)
    f.text((0.54, 0.56), '(½, ½)', size=14, anchor='start', italic=False)
    f.text((0.28, 0.2), 'φ ≤ 2', size=15, color=blue)
    f.text((0.38, 0.75), 'a + b = 1', size=14, color=orange, anchor='start')
    f.save('07-four/diamond', 'The disk where phi is at most 2, inside the diamond a '
           'plus b at most 1, which touches it at (1/2, 1/2)')


def twelve_gon():
    from fig_three import eqn, label
    g = (math.sqrt(5) - 1) / 2
    corner = (4 - math.sqrt(5)) / 2
    poly = convex_hull([(0, 0), (1, 0), (corner, 3 - 3 * corner),
                        (3 - 3 * corner, corner), (0, 1)])
    orange, blue = COLORS[1], COLORS[0]
    f = Figure(-0.12, 1.2, -0.12, 1.2, 320)
    f.polygon(poly, fill=FILLS[1], stroke=orange, width=2)
    f.polygon(quadrant_disk(2.5), fill=FILLS[0], stroke=blue, width=1.4)
    f.polygon(poly, stroke=orange, width=2)
    # The third side cuts off the corner (3/4, 3/4) of the first two.
    for p in ((corner, 3 - 3 * corner), (3 - 3 * corner, corner)):
        f.line(p, (0.75, 0.75), stroke=orange, width=1.2, dash='4 3')
    f.circle((0.75, 0.75), 4 / f.s, stroke=orange, width=1.4, fill='#ffffff')
    f.text((0.79, 0.79), '(¾, ¾)', size=13, italic=False, anchor='start')
    ab_axes(f, 1.17)
    for q in ((1, 0), (0, 1), (g, g)):
        f.dot(q, r=4)
    f.text((1.0, 0.07), '(1, 0)', size=13, italic=False, anchor='start')
    f.text((0.05, 1.05), '(0, 1)', size=13, italic=False, anchor='start')
    label(f, (g - 0.04, g - 0.05), eqn('(g, g)'), 13, 'end', italic=False)
    f.text((0.3, 0.3), 'φ ≤ 5/2', size=15, color=blue)
    f.text((0.9, 0.5), sb('P', '5', size=16), size=16, color=orange,
           anchor='start')
    f.save('08-five/twelve-gon', 'The part with a, b at least 0 of the 12-gon of five '
           'squares, around the disk where phi is at most 5/2, which it '
           'touches at (1, 0), (0, 1) and (g, g) with g = (root 5 - 1)/2; '
           'its third side cuts off the corner (3/4, 3/4) where the first '
           'two meet')


def axis_square():
    c = (1.1, 0.75)
    f = Figure(-0.25, 1.95, -0.25, 1.5, 200)
    f.line((-0.2, 0), (1.9, 0), width=1, arrow=True)
    f.line((0, -0.2), (0, 1.45), width=1, arrow=True)
    f.text((1.9, -0.08), 'x', anchor='end')
    f.text((-0.08, 1.42), 'y', anchor='end')
    for x in (c[0] - 0.5, c[0] + 0.5):
        f.line((x, 0), (x, c[1] - 0.5), stroke=FAINT, width=1, dash='3 3')
    for y in (c[1] - 0.5, c[1] + 0.5):
        f.line((0, y), (c[0] - 0.5, y), stroke=FAINT, width=1, dash='3 3')
    f.square(c, fill=FILLS[0], stroke=COLORS[0])
    f.dot(c, fill=COLORS[0])
    f.text(shift(c, (0.05, -0.07)), 'c', anchor='start', color=COLORS[0])
    for x, s in ((c[0] - 0.5, ' − ½'), (c[0] + 0.5, ' + ½')):
        f.text((x, -0.1), sb('c', '1', s, 13), size=13)
    for y, s in ((c[1] - 0.5, ' − ½'), (c[1] + 0.5, ' + ½')):
        f.text((-0.04, y), sb('c', '2', s, 13), size=13, anchor='end')
    f.text((c[0] + 0.3, c[1] + 0.32), 'Q(c)', size=15, color=COLORS[0])
    f.save('02-preliminaries/axis-square', 'The axis-parallel unit square Q(c), which spans '
           'c1 minus a half to c1 plus a half across and c2 minus a half to c2 '
           'plus a half up')


def three_arcs():
    r = 1.0
    arcs = [(rad(90), rad(48), 'U', 0), (rad(212), rad(36), 'V', 2),
            (rad(328), rad(40), 'W', 3)]
    f = Figure(-1.5, 1.5, -1.35, 1.4, 150)
    f.circle((0, 0), r)
    for t, w, name, k in arcs:
        f.arc((0, 0), r, t - w, t + w, COLORS[k], width=5)
        f.line((0, 0), shift((0, 0), u(t), r), stroke=COLORS[k], width=1,
               dash='4 3')
        f.text(shift((0, 0), u(t), r + 0.18), name, size=17,
               color=COLORS[k])
    tv, tw = arcs[1][0], arcs[2][0]
    f.arc((0, 0), 0.35, tv, tw, INK, width=1.2)
    f.text(shift((0, 0), u((tv + tw) / 2), 0.5),
           'd(' + sb('θ', 'V', ', ') + sb('θ', 'W', ')'), size=14)
    f.dot((0, 0))
    f.text((0.06, 0.08), 'o', anchor='start')
    f.save('03-tools/three-arcs', 'Three disjoint arcs U, V and W of a circle about o; '
           'the angle between the centres of V and W is at least the sum of '
           'their half-widths and at most what the arc U leaves')


def axis_squares():
    """Lemma 2.8 (1): if q1 >= p1 + 1, the open square Q(p) lies left of the
    line x = p1 + 1/2 and Q(q) right of x = q1 - 1/2, whatever the second
    coordinates."""
    ps, qs = (0.0, 0.0), (1.45, 0.42)
    assert qs[0] >= ps[0] + 1
    assert not overlap(square_corners(ps), square_corners(qs))
    x0, x1 = ps[0] + 0.5, qs[0] - 0.5
    assert all(x <= x0 for x, _ in square_corners(ps))
    assert all(x >= x1 for x, _ in square_corners(qs))
    f = Figure(-0.62, 2.12, -1.08, 1.3, 140)
    y0 = -0.8
    f.line((-0.6, y0), (2.1, y0), width=1, arrow=True)
    f.text((2.08, y0 - 0.16), 'x', anchor='end', size=14)
    f.square(ps, fill=FILLS[0], stroke=COLORS[0])
    f.square(qs, fill=FILLS[2], stroke=COLORS[2])
    for x in (x0, x1):
        f.line((x, y0), (x, 1.08), width=1.1, dash='6 4')
    f.text((x0 - 0.05, 1.18), sb('p', '1', ' + ½', 13), size=13, anchor='end')
    f.text((x1 + 0.05, 1.18), sb('q', '1', ' − ½', 13), size=13,
           anchor='start')
    for c, name, col in ((ps, 'p', COLORS[0]), (qs, 'q', COLORS[2])):
        f.line((c[0], y0 - 0.04), (c[0], y0 + 0.04), width=1.2)
        f.line((c[0], y0 + 0.04), c, stroke=FAINT, width=1, dash='2 3')
        f.text((c[0], y0 - 0.18), sb(name, '1', size=13), size=13)
        f.dot(c, fill=col)
        f.text(shift(c, (0, 0.17)), f'Q({name})', size=14, color=col)
    f.save('02-preliminaries/axis-squares', 'Two axis-parallel squares Q(p) '
           'and Q(q) whose centres differ by more than 1 across: Q(p) lies '
           'left of the dashed line x = p1 + 1/2 and Q(q) right of the '
           'dashed line x = q1 - 1/2')


def parallel_squares():
    d = 25
    e1, e2 = u(rad(d)), u(rad(d + 90))
    cs = shift(shift((0, 0), e1, 0.3), e2, 0.2)
    ct = shift(cs, e1, 1.0)
    orange = COLORS[1]
    f = Figure(-0.65, 2.2, -0.5, 1.55, 180)
    for e in (e1, e2):
        f.line(shift((0, 0), e, -0.45), shift((0, 0), e, 2.08 if e is e1
                                                 else 1.1),
               stroke=FAINT, width=1, dash='5 4', arrow=True)
    f.square(cs, d, fill=FILLS[0], stroke=COLORS[0])
    f.square(ct, d, fill=FILLS[2], stroke=COLORS[2])
    foot = shift((0, 0), e1, 1.3)
    f.line((0, 0), foot, stroke=orange, width=2.4)
    f.line(foot, ct, stroke=orange, width=2.4)
    f.dot(cs, fill=COLORS[0])
    f.dot(ct, fill=COLORS[2])
    subscript(f, shift(cs, (-0.02, 0.08)), 'c', 'S', color=COLORS[0])
    subscript(f, shift(ct, (0.05, 0.05)), 'c', 'T', color=COLORS[2],
              anchor='start')
    f.dot((0, 0))
    f.text((-0.05, -0.05), 'o', anchor='end')
    f.text(shift((0, 0), e1, 2.14), 'φ', anchor='start')
    f.text(shift(shift((0, 0), e1, 0.65), e2, -0.1), sb('c', '1'),
           color=orange)
    f.text(shift(shift(foot, e2, 0.1), e1, 0.1), sb('c', '2'),
           color=orange, anchor='start')
    f.save('03-tools/parallel-squares', 'Axes at o parallel to the sides of S; a '
           'square T with the same axes sits at the coordinates (c1, c2) of '
           'its centre in this frame')


def vertex_square():
    """Lemma 7.7: a square with a vertex at o holds the quarter of the circle
    of radius 1/2 between its two edges from o, centred at mu_S, and sits at
    (1/2, 1/2) in the frame mu_S - pi/4, whose axes run along those edges."""
    from fig_one import label
    th = rad(20)
    blue, orange = COLORS[0], COLORS[1]
    e1, e2 = u(th), u(th + math.pi / 2)
    c = shift(shift((0, 0), e1, 0.5), e2, 0.5)
    mu = th + math.pi / 4
    (t0, t1), = arcs_in(lambda p: in_open_square(p, c, math.degrees(th)), 0.5)
    assert abs((t0 + t1) / 2 - mu) < 2e-3 and abs(t1 - t0 - math.pi / 2) < 2e-3
    f = Figure(-0.62, 1.34, -0.5, 1.5, 240)
    f.square(c, math.degrees(th), fill=FILLS[0], stroke=blue)
    f.circle((0, 0), 0.5)
    f.arc((0, 0), 0.5, th, th + math.pi / 2, orange, width=5)
    f.line((0, 0), shift((0, 0), e1, 1.3), width=1.5, arrow=True)
    f.line((0, 0), shift((0, 0), e2, 1.3), width=1.5, arrow=True)
    label(f, shift(shift((0, 0), e1, 1.3), (0.06, -0.13)),
          sb('μ', 'S', ' − π/4', 14), size=14, anchor='end')
    label(f, shift(shift((0, 0), e2, 1.38), (0.04, 0.0)),
          sb('μ', 'S', ' + π/4', 14), size=14, anchor='middle')
    f.line((0, 0), shift((0, 0), u(mu), 1.1), width=1, dash='3 3')
    f.text(shift((0, 0), u(mu), 1.17), sb('μ', 'S'), anchor='start')
    f.arc((0, 0), 0.2, th, mu, INK, width=1)
    f.text(shift((0, 0), u(th + math.pi / 8), 0.3), 'π/4', size=12,
           italic=False)
    f.dot(c, fill=blue)
    f.text(shift(c, (0.05, -0.05)), '(½, ½)', size=13, italic=False,
           color=blue, anchor='start')
    f.dot((0, 0))
    f.text((-0.04, -0.06), 'o', anchor='end')
    f.text(shift(c, (0.22, -0.32)), 'S', size=17, color=blue)
    f.save('07-four/vertex-square', 'A square with a vertex at o, with arrows '
           'along its two edges from o, in the directions mu_S minus pi/4 and '
           'mu_S plus pi/4; the quarter of the circle of radius 1/2 between '
           'them is highlighted, the bisecting direction mu_S is dashed, and '
           'the centre of the square is at (1/2, 1/2) in the frame of the '
           'arrows')


def main():
    containing_exterior()
    tangent_half_plane()
    four_directions()
    parallelogram()
    contact_types()
    containing_arc()
    radial_gap()
    near_axis_overlap()
    slid_disk()
    dodecagon_disk()
    sixteen_gon()
    diamond()
    twelve_gon()
    axis_square()
    three_arcs()
    axis_squares()
    parallel_squares()
    vertex_square()
    directions()
    local_coordinates()
    packing_example()
    width_figure()
    arc_figure()
    chart_panels()
    frame_figure()
    congruent_figure()
    inscribed_disks()
    midpoint_figure()
    shadows()
    edge_contact()
    arc_centres()
    rectangle_interval()
    safe_sweep()
    position()
    farthest_vertex()
    chart()
    budget()
    sweep()
    packing('04-one/one', 'One square in its circle of radius root 2 over 2',
            [(0, 0)], math.sqrt(2) / 2)
    packing('05-two/two', 'The 2 by 1 rectangle in its circle of radius root 5 '
            'over 2', [(-0.5, 0), (0.5, 0)], math.sqrt(5) / 2)
    packing('06-three/three', 'The T with the circle of radius 3/8',
            [(-0.5, -5 / 16), (0.5, -5 / 16), (0, 11 / 16)],
            5 * math.sqrt(17) / 16, 3 / 8)
    packing('07-four/four', 'The 2 by 2 block with the circle of radius 1/2',
            [(0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)],
            math.sqrt(2), 1 / 2)
    packing('08-five/five', 'The plus with the circle of radius 5/6',
            [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)],
            math.sqrt(2.5), 5 / 6, grey=(0,))
    packing('10-seven/seven', 'Two columns of two squares beside a column of three, '
            'with the unit circle',
            [(1, -0.5), (1, 0.5), (-1, -0.5), (-1, 0.5), (0, -1), (0, 0),
             (0, 1)], math.sqrt(13) / 2, 1, grey=(5,),
            labels=(((0.86, -0.8), sb('Γ', '1', size=13)),))

    # The figures of each chapter, drawn by one module per chapter.
    import importlib
    for module in ('fig_front', 'fig_one', 'fig_two', 'fig_three', 'fig_four',
                   'fig_five', 'fig_six', 'fig_seven', 'fig_appa', 'fig_appb',
                   'fig_appc', 'fig_appd', 'fig_appe', 'fig_appf', 'fig_appg',
                   'fig_apph', 'fig_appi'):
        importlib.import_module(module).main()


if __name__ == '__main__':
    main()

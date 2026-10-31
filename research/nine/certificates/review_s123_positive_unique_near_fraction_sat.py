"""Independent exact reconstruction of both positive unique-middle covers.

No author module or author interval implementation is imported. All interval
arithmetic is exact Fraction arithmetic; only square-root endpoints are
enclosed on the strictly finer grid 2**-48. The complete five-dimensional
closed cover is generated independently on the declared 2**-40 split grid.
Both original root parametrizations, every discard guard, and all four SAT
axes are re-evaluated. An unresolved box fails the proof.
"""
from collections import Counter
from fractions import Fraction as F
from math import isqrt

GRID = 1 << 40
ROOT_GRID = 1 << 48


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        assert self.lo <= self.hi

    def __add__(a, b):
        b = iv(b)
        return Interval(a.lo + b.lo, a.hi + b.hi)

    __radd__ = __add__

    def __neg__(a):
        return Interval(-a.hi, -a.lo)

    def __sub__(a, b):
        return a + -iv(b)

    def __rsub__(a, b):
        return iv(b) + -a

    def __mul__(a, b):
        b = iv(b)
        ends = (a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi)
        return Interval(min(ends), max(ends))

    __rmul__ = __mul__

    def __truediv__(a, b):
        b = iv(b)
        assert b.lo > 0
        return a * Interval(1/b.hi, 1/b.lo)

    def abs(a):
        if a.lo <= 0 <= a.hi:
            return Interval(0, max(-a.lo, a.hi))
        return -a if a.hi < 0 else a

    def sq(a):
        lo = 0 if a.lo <= 0 <= a.hi else min(a.lo*a.lo, a.hi*a.hi)
        return Interval(lo, max(a.lo*a.lo, a.hi*a.hi))

    def sqrt(a):
        assert a.hi >= 0
        lower = max(F(0), a.lo) * ROOT_GRID**2
        upper = a.hi * ROOT_GRID**2
        l = isqrt(lower.numerator // lower.denominator)
        h = isqrt(upper.numerator // upper.denominator)
        if F(h*h) < upper:
            h += 1
        return Interval(F(l, ROOT_GRID), F(h, ROOT_GRID))


def iv(x):
    return x if isinstance(x, Interval) else Interval(x)


def angle(z):
    """Exact monotone ranges of cos(theta), sin(theta), z=tan(theta/2)."""
    assert 0 <= z.lo <= z.hi <= 1
    return (
        Interval((1-z.hi*z.hi)/(1+z.hi*z.hi),
                 (1-z.lo*z.lo)/(1+z.lo*z.lo)),
        Interval(2*z.lo/(1+z.lo*z.lo), 2*z.hi/(1+z.hi*z.hi)),
    )


def check(box, kind):
    ae, be, ze, V, epsilon = [Interval(F(l, GRID), F(h, GRID)) for l, h in box]
    da = max(F(0), ae.abs().lo-F(1, 2))
    db = max(F(0), be.abs().lo-F(1, 2))
    if da*da + db*db > F(1, 64):
        return "distance", F(1)
    d = 1 + epsilon
    top = 1 - V
    if kind == "aligned":
        r = -epsilon
        xa = d
        z = epsilon / V
        J = (V.sq() + epsilon.sq()) / (2*epsilon)
        if J.lo >= F(1, 2):
            return "J", F(1)
    else:
        xa = (d.sq() - V.sq()).sqrt()
        r = 1 - xa
        if r.lo > epsilon.hi or r.hi < -epsilon.hi:
            return "r", F(1)
        discriminant = 2*(epsilon+r)
        if discriminant.hi <= 0:
            return "r", F(1)
        z = (epsilon-r)/(V+discriminant.sqrt())
    if z.lo > F(1, 3) or z.hi < 0:
        return "angle", F(1)
    z = Interval(max(F(0), z.lo), min(F(1, 3), z.hi))
    x, t = angle(z)
    T = V*x-r*t
    if kind == "tilted":
        denominator = t+T
        if denominator.lo <= 0:
            return None
        J = xa*T/denominator
    radius_sq = (d+1).sq() + F(1, 4)
    W = (radius_sq-(top+1).sq()).sqrt()
    u = 1-W
    if W.lo >= 1 or W.hi <= F(1, 2):
        return "W", F(1)
    assert W.lo > 0
    Y = J*(top+1)/W
    if Y.hi < top.lo or Y.lo >= F(97, 100):
        return "Y", F(1)
    qn, qf = u*x-Y*t, u*t+Y*x
    if qn.hi <= epsilon.lo or qf.lo >= F(97, 100):
        return "Q", F(1)

    c, s = angle(ze)
    ex, ey = ae*c-be*s, ae*s+be*c
    own_world_halfwidth = (c+s)/2

    def world_rectangle(xl, xh, yl, yh):
        xl, xh, yl, yh = map(iv, (xl, xh, yl, yh))
        min_e, max_e = xl*c+yl*s, xh*c+yh*s
        min_j, max_j = yl*c-xh*s, yh*c-xl*s
        gaps = (
            ex+own_world_halfwidth-xl, xh+own_world_halfwidth-ex,
            ey+own_world_halfwidth-yl, yh+own_world_halfwidth-ey,
            ae+F(1, 2)-min_e, max_e-ae+F(1, 2),
            be+F(1, 2)-min_j, max_j-be+F(1, 2),
        )
        return min(g.lo for g in gaps)

    rects = [
        ("A", (r-1, r, -V, top)),
        ("K1", (r, F(1, 2), F(-3, 8), F(1, 4))),
        ("K2", (r, F(3, 4), F(-3, 8), F(1, 16))),
    ]
    if kind == "aligned":
        rects.append(("K3", (r-V/4, r, F(-3, 8), -V-F(1, 8))))
    for name, rec in rects:
        margin = world_rectangle(*rec)
        if margin > 0:
            return name, margin

    def oriented_rectangle(nx, ny, fx, fy, nc, fc, hn, hf):
        nx, ny, fx, fy, nc, fc, hn, hf = map(iv, (nx, ny, fx, fy, nc, fc, hn, hf))
        en, ef, jn, jf = c*nx+s*ny, c*fx+s*fy, -s*nx+c*ny, -s*fx+c*fy
        ec_n, ec_f = ae*en+be*jn, ae*ef+be*jf
        rc_e, rc_j = nc*en+fc*ef, nc*jn+fc*jf
        gaps = (
            hn+(en.abs()+jn.abs())/2-(ec_n-nc).abs(),
            hf+(ef.abs()+jf.abs())/2-(ec_f-fc).abs(),
            F(1, 2)+hn*en.abs()+hf*ef.abs()-(ae-rc_e).abs(),
            F(1, 2)+hn*jn.abs()+hf*jf.abs()-(be-rc_j).abs(),
        )
        return min(g.lo for g in gaps)

    margin = oriented_rectangle(x, -t, t, x, epsilon+F(1, 2), F(21, 400), F(1, 2), F(179, 400))
    if margin > 0:
        return "U", margin
    if kind == "aligned":
        margin = world_rectangle(-d-1, -d, F(-1, 2), F(1, 2))
    else:
        al, bl = xa/d, V/d
        margin = oriented_rectangle(-al, -bl, bl, -al, d+F(1, 2), 0, F(1, 2), F(1, 2))
    if margin > 0:
        return "L", margin
    return None


def endpoint(value, upper=False):
    q = F(value)*GRID
    return -((-q.numerator)//q.denominator) if upper else q.numerator//q.denominator


def run(kind):
    root = (
        (-5*GRID//8, 5*GRID//8), (-5*GRID//8, 5*GRID//8), (0, GRID),
        (endpoint(F(3, 100)), endpoint(F(13, 100), True)),
        (endpoint(F(9, 40000)), endpoint(F(1, 60), True)),
    )
    stack = [(root, 0)]
    counts, margins = Counter(), {}
    visited = max_depth = 0
    while stack:
        box, depth = stack.pop()
        visited += 1
        result = check(box, kind)
        if result is not None:
            tag, margin = result
            counts[tag] += 1
            max_depth = max(max_depth, depth)
            if tag in ("A", "K1", "K2", "K3", "U", "L"):
                margins[tag] = min(margins.get(tag, F(1)), margin)
            continue
        assert depth < 85, (kind, box, depth)
        widths = [h-l for l, h in box]
        widths[2] = widths[2]*5//4
        widths[3] = widths[3]*25//2
        widths[4] *= 75
        j = max(range(5), key=lambda i: widths[i])
        lo, hi = box[j]
        mid = (lo+hi)//2
        assert lo < mid < hi
        left, right = list(box), list(box)
        left[j], right[j] = (lo, mid), (mid, hi)
        stack.append((tuple(right), depth+1))
        stack.append((tuple(left), depth+1))
        counts["split"] += 1
    expected = {
        "aligned": (Counter(split=6388, Y=945, L=1425, Q=295, J=66, distance=97, U=1616, K3=421, K1=515, A=997, K2=12), 12777, 32),
        "tilted": (Counter(split=18211, L=5176, Y=3072, distance=324, K1=2308, U=4336, Q=391, A=2589, K2=16), 36423, 34),
    }[kind]
    assert (counts, visited, max_depth) == expected, (kind, counts, visited, max_depth)
    assert margins and min(margins.values()) > 0
    floors = {tag: (q.numerator*ROOT_GRID)//q.denominator for tag, q in sorted(margins.items())}
    assert min(floors.values()) > 0
    print("PASS", kind, dict(counts), "visited", visited, "depth", max_depth, flush=True)
    print("Exact Fraction margin lower numerators over 2**48:", floors, flush=True)
    return counts, margins


if __name__ == "__main__":
    run("aligned")
    run("tilted")

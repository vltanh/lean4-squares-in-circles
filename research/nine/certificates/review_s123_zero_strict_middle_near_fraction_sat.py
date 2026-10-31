"""Independent exact-Fraction reconstruction of the strict-M near-unit cover.

No author arithmetic implementation is imported. Integer box endpoints
only specify the complete initial cover and deterministic subdivision;
all geometric calculations below are unrounded rational intervals.
"""
from fractions import Fraction as Q
from collections import Counter

LATTICE = 1 << 40
REPORT = 1 << 48


class Range:
    def __init__(self, low, high=None):
        self.low = Q(low)
        self.high = Q(low if high is None else high)
        assert self.low <= self.high

    def __add__(self, other):
        other = as_range(other)
        return Range(self.low + other.low, self.high + other.high)

    __radd__ = __add__

    def __neg__(self):
        return Range(-self.high, -self.low)

    def __sub__(self, other):
        return self + -as_range(other)

    def __rsub__(self, other):
        return as_range(other) + -self

    def __mul__(self, other):
        other = as_range(other)
        products = [a*b for a in (self.low, self.high)
                    for b in (other.low, other.high)]
        return Range(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = as_range(other)
        assert other.low > 0
        return self * Range(1/other.high, 1/other.low)

    def square(self):
        ends = [self.low*self.low, self.high*self.high]
        low = Q(0) if self.low <= 0 <= self.high else min(ends)
        return Range(low, max(ends))

    def absolute(self):
        if self.low >= 0:
            return self
        if self.high <= 0:
            return -self
        return Range(0, max(-self.low, self.high))


def as_range(value):
    return value if isinstance(value, Range) else Range(value)


def floor(value):
    value = Q(value)
    return value.numerator // value.denominator


def ceil(value):
    return -floor(-Q(value))


def enclose_box(pair):
    return Range(Q(pair[0], LATTICE), Q(pair[1], LATTICE))


def half_angle(pair):
    low, high = (Q(value, LATTICE) for value in pair)
    cos_low = (1-high*high)/(1+high*high)
    cos_high = (1-low*low)/(1+low*low)
    sin_low = 2*low/(1+low*low)
    sin_high = 2*high/(1+high*high)
    return Range(cos_low, cos_high), Range(sin_low, sin_high)


def minimum_margin(expressions):
    return min(value.low for value in expressions)


def classify(box):
    a, b, _, height = [enclose_box(pair) for pair in box]
    da = max(Q(0), a.absolute().low-Q(1, 2))
    db = max(Q(0), b.absolute().low-Q(1, 2))
    if da*da+db*db > Q(1, 64):
        return 'distance', None

    cosine, sine = half_angle(box[2])
    center_x = a*cosine-b*sine
    center_y = a*sine+b*cosine
    half_width = (cosine+sine)/2
    epsilon = height.square()/4
    radius = 1+epsilon
    rectangles = (
        ('A', (epsilon-1, epsilon, -height, 1-height)),
        ('U', (epsilon, radius, Range(Q(-79, 200)), Range(Q(1, 2))))
    )
    for label, (left, right, bottom, top) in rectangles:
        projected_u_low = left*cosine+bottom*sine
        projected_u_high = right*cosine+top*sine
        projected_v_low = bottom*cosine-right*sine
        projected_v_high = top*cosine-left*sine
        values = (
            center_x+half_width-left, right-center_x+half_width,
            center_y+half_width-bottom, top-center_y+half_width,
            a+Q(1, 2)-projected_u_low,
            projected_u_high-a+Q(1, 2),
            b+Q(1, 2)-projected_v_low,
            projected_v_high-b+Q(1, 2))
        margin = minimum_margin(values)
        if margin > 0:
            return label, margin

    alpha = (1-epsilon)/radius
    beta = height/radius
    h = alpha*cosine+beta*sine
    k = beta*cosine-alpha*sine
    width = (h+k.absolute())/2
    leaf_center_u = -(radius+Q(1, 2))*h
    leaf_center_v = -(radius+Q(1, 2))*k
    extra_center_e = -(h*a+k*b)
    extra_center_j = k*a-h*b
    values = (
        extra_center_e+width-radius,
        radius+1-extra_center_e+width,
        extra_center_j+width+Q(1, 2),
        Q(1, 2)-extra_center_j+width,
        a+Q(1, 2)-leaf_center_u+width,
        leaf_center_u-a+Q(1, 2)+width,
        b+Q(1, 2)-leaf_center_v+width,
        leaf_center_v-b+Q(1, 2)+width)
    margin = minimum_margin(values)
    return ('L', margin) if margin > 0 else None


def run():
    initial = (
        (-5*LATTICE//8, 5*LATTICE//8),
        (-5*LATTICE//8, 5*LATTICE//8),
        (0, LATTICE),
        (floor(Q(LATTICE, 50)), ceil(Q(13*LATTICE, 100))))
    stack = [(initial, 0)]
    counts = Counter()
    margins = {}
    visits = 0
    max_depth = 0
    while stack:
        box, depth = stack.pop()
        visits += 1
        outcome = classify(box)
        if outcome is not None:
            label, margin = outcome
            counts[label] += 1
            max_depth = max(max_depth, depth)
            if margin is not None:
                margins[label] = min(margins.get(label, margin), margin)
            continue
        assert depth < 76, ('unresolved', box, depth)
        widths = [high-low for low, high in box]
        weighted = [widths[0], widths[1], 5*widths[2]//4,
                    125*widths[3]//11]
        axis = max(range(4), key=lambda index: weighted[index])
        low, high = box[axis]
        midpoint = (low+high)//2
        assert low < midpoint < high
        lower, upper = list(box), list(box)
        lower[axis] = low, midpoint
        upper[axis] = midpoint, high
        stack.append((tuple(upper), depth+1))
        stack.append((tuple(lower), depth+1))
        counts['split'] += 1
    assert all(margin > 0 for margin in margins.values())
    assert counts['split']+1 == sum(value for label, value in counts.items()
                                   if label != 'split')
    print('Independent exact Fraction cover: PASS')
    print('counts', dict(counts), 'visits', visits, 'depth', max_depth)
    print('strict positive lower numerators over', REPORT,
          {label: floor(margin*REPORT) for label, margin in margins.items()})
    return counts, margins


if __name__ == '__main__':
    run()

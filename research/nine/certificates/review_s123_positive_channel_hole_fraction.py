"""Independent unrounded-Fraction audit of the positive-channel hole cover.

The Range class is from the reviewer's earlier independently written SAT
reconstruction, not from the author implementation. Only square roots
are enclosed on a separate exact2**-48 rational lattice.
"""
from fractions import Fraction as Q
from math import isqrt
from collections import Counter
from review_s123_zero_strict_middle_near_fraction_sat import Range, floor, ceil

BOX_DENOMINATOR = 1 << 40
ROOT_DENOMINATOR = 1 << 48


def exact_range(pair):
    return Range(Q(pair[0], BOX_DENOMINATOR),
                 Q(pair[1], BOX_DENOMINATOR))


def sqrt_lower(value):
    assert value >= 0
    return Q(isqrt(value.numerator*ROOT_DENOMINATOR**2//value.denominator),
             ROOT_DENOMINATOR)


def root(interval):
    assert interval.low >= 0
    low = sqrt_lower(interval.low)
    high = sqrt_lower(interval.high)
    if high*high < interval.high:
        high += Q(1, ROOT_DENOMINATOR)
    return Range(low, high)


def classify(box):
    epsilon, depth, tilt = [exact_range(pair) for pair in box]
    d, f = 1+epsilon, 1-depth
    x = root(1-tilt.square())
    r = (epsilon-depth*tilt)/x
    if r.low > epsilon.high or r.high < -epsilon.high:
        return 'r', None
    r2 = (d+1).square()+Q(1, 4)
    radicand = r2-(f+1).square()
    if radicand.high < 0:
        return 'radicand', None
    w = root(Range(max(Q(0), radicand.low), radicand.high))
    if w.low >= 1 or w.high <= Q(1, 2):
        return 'W', None
    u = 1-w
    q = u*x-f*tilt
    if q.high <= epsilon.low:
        return 'q', None
    p = u*tilt+f*x
    transverse = depth*x-r*tilt
    if transverse.high <= 0:
        return 'T', None
    twice_area = d+(d+1)*transverse-r*(1+f)+u*f-q*(1-p)
    gap = Q(3, 4)-twice_area/2
    return ('positive', gap.low) if gap.low > 0 else None


def run():
    n = BOX_DENOMINATOR
    box = ((0, ceil(Q(n, 60))),
           (floor(Q(n, 50)), ceil(Q(13*n, 50))),
           (0, ceil(Q(3*n, 5))))
    stack = [(box, 0)]
    counts, minimum, visits, max_depth = Counter(), None, 0, 0
    while stack:
        box, depth = stack.pop()
        visits += 1
        outcome = classify(box)
        if outcome is not None:
            label, margin = outcome
            counts[label] += 1
            max_depth = max(max_depth, depth)
            if margin is not None:
                minimum = margin if minimum is None else min(minimum, margin)
            continue
        assert depth < 70, ('unresolved', box, depth)
        widths = [high-low for low, high in box]
        scaled = [60*widths[0], 25*widths[1]//6, 5*widths[2]//3]
        axis = max(range(3), key=lambda index: scaled[index])
        low, high = box[axis]
        midpoint = (low+high)//2
        assert low < midpoint < high
        lower, upper = list(box), list(box)
        lower[axis] = low, midpoint
        upper[axis] = midpoint, high
        stack.extend(((tuple(upper), depth+1), (tuple(lower), depth+1)))
        counts['split'] += 1
    assert minimum is not None and minimum > 0
    assert counts['split']+1 == sum(value for label, value in counts.items()
                                   if label != 'split')
    print('Independent Fraction hole cover: PASS')
    print('counts', dict(counts), 'visits', visits, 'depth', max_depth)
    print('strict positive lower numerator over', ROOT_DENOMINATOR,
          floor(minimum*ROOT_DENOMINATOR))


if __name__ == '__main__':
    run()

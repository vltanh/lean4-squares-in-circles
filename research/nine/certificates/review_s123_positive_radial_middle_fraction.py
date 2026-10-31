"""Independent exact-Fraction verification of both positive radial-M covers.

Only an independently written Fraction interval class is reused. Neither
author certificate nor its rounded integer arithmetic is imported.
All equations and SAT inequalities are rebuilt from the manuscript.
"""
from fractions import Fraction as Q
from collections import Counter
from review_s123_zero_strict_middle_near_fraction_sat import (
    Range, LATTICE, REPORT, floor, ceil, enclose_box, half_angle)


def root_classify(box, kind):
    z, depth = [enclose_box(pair) for pair in box]
    cosine, sine = half_angle(box[0])
    if kind == 'tilted':
        epsilon = z*depth+(1+z.square())*depth.square()/4
        V = depth+z*depth.square()/2
        r = (1-z.square())*depth.square()/4-z*depth
        XA = 1-r
    else:
        V = depth
        epsilon = z*depth
        XA = 1+epsilon
    d = 1+epsilon
    denominator = 4*d.square()+1
    a = 4*d/denominator
    b = (4*d.square()-1)/denominator
    qn, qf = d-a, b+Q(1, 2)
    east = cosine*qn+sine*qf
    north = cosine*qf-sine*qn
    W, height = 1-east, 2-V
    guards = (Q(1, 60)-epsilon, V-Q(1, 50), Q(13, 50)-V,
              W-Q(1, 2), 1-W, north-(1-V), 2-V-north)
    for index, guard in enumerate(guards):
        if guard.high < 0:
            return 'guard'+str(index), None
    circle = W.square()+height.square()-(d+1).square()-Q(1, 4)
    if circle.low > 0 or circle.high < 0:
        return 'circle', None
    if kind == 'tilted':
        moment = XA*depth*height-north*W*(sine+depth)
    else:
        moment = V*height-north*W*sine
    if moment.low > 0 or moment.high < 0:
        return 'mean', None
    targets = (V-Q(1, 25), Q(3, 50)-V, sine-Q(2, 25),
               Q(13, 100)-sine, Q(7, 2000)-epsilon)
    margin = min(value.low for value in targets)
    return ('pass', margin) if margin > 0 else None


def verify_root(kind):
    initial = ((0, ceil(Q(2*LATTICE, 13))),
               (0, ceil(Q(13*LATTICE, 50))))
    stack = [(initial, 0)]
    counts, margins = Counter(), []
    visits, maximum_depth = 0, 0
    while stack:
        box, depth = stack.pop()
        visits += 1
        result = root_classify(box, kind)
        if result is not None:
            label, margin = result
            counts[label] += 1
            maximum_depth = max(maximum_depth, depth)
            if margin is not None:
                margins.append(margin)
            continue
        assert depth < 60, ('unresolved', kind, box)
        weights = ((box[0][1]-box[0][0])*169,
                   (box[1][1]-box[1][0])*100)
        index = max(range(2), key=lambda i: weights[i])
        low, high = box[index]
        middle = (low+high)//2
        assert low < middle < high
        left, right = list(box), list(box)
        left[index], right[index] = (low, middle), (middle, high)
        stack.extend(((tuple(right), depth+1), (tuple(left), depth+1)))
        counts['split'] += 1
    expected = {
        'tilted': (Counter(split=64, circle=38, mean=24, **{'pass':3}),129,16),
        'aligned': (Counter(split=39, circle=23, mean=14, **{'pass':3}),79,12)}
    assert (counts, visits, maximum_depth) == expected[kind]
    assert min(margins) > 0
    print('ROOT', kind, dict(counts), 'visits', visits, 'depth',
          maximum_depth, 'exact lower numerator over', REPORT,
          floor(min(margins)*REPORT), flush=True)


RECTANGLES = (
    (Q(-99,100),Q(-1,250),Q(-1,25),Q(3,4)),
    (Q(1,20),Q(9,10),Q(-1,4),Q(1,4)),
    (Q(-7,4),Q(-251,250),Q(-9,20),Q(-1,5)),
    (Q(-1,200),Q(9,10),Q(-3,8),Q(-1,8)))


def near_classify(box):
    a, b, _ = [enclose_box(pair) for pair in box]
    outside_a = max(Q(0), a.absolute().low-Q(1,2))
    outside_b = max(Q(0), b.absolute().low-Q(1,2))
    if outside_a**2+outside_b**2 > Q(1,64):
        return 'distance', None
    c, s = half_angle(box[2])
    center_x, center_y = a*c-b*s, a*s+b*c
    radius = (c+s)/2
    for index, (left,right,bottom,top) in enumerate(RECTANGLES):
        tests = (center_x+radius-left, right-center_x+radius,
                 center_y+radius-bottom, top-center_y+radius,
                 a+Q(1,2)-left*c-bottom*s,
                 right*c+top*s-a+Q(1,2),
                 b+Q(1,2)+right*s-bottom*c,
                 -left*s+top*c-b+Q(1,2))
        margin = min(test.low for test in tests)
        if margin > 0:
            return index, margin
    return None


def verify_near():
    initial = ((-5*LATTICE//8,5*LATTICE//8),
               (-5*LATTICE//8,5*LATTICE//8),(0,LATTICE))
    stack = [(initial,0)]
    counts, margins = Counter(), {}
    visits, maximum_depth = 0,0
    while stack:
        box, depth = stack.pop()
        visits += 1
        result = near_classify(box)
        if result is not None:
            label, margin = result
            counts[label] += 1
            maximum_depth = max(maximum_depth,depth)
            if margin is not None:
                margins[label] = min(margins.get(label,margin),margin)
            continue
        assert depth < 70, ('unresolved',box)
        widths = [high-low for low,high in box]
        weighted = [widths[0],widths[1],5*widths[2]//4]
        index = max(range(3),key=lambda i:weighted[i])
        low,high=box[index]
        middle=(low+high)//2
        assert low < middle < high
        left,right=list(box),list(box)
        left[index],right[index]=(low,middle),(middle,high)
        stack.extend(((tuple(right),depth+1),(tuple(left),depth+1)))
        counts['split'] += 1
    assert counts == Counter({'split':2944,0:147,1:24,2:1657,3:1106,'distance':11})
    assert (visits,maximum_depth)==(5889,33)
    assert min(margins.values())>0
    print('NEAR',dict(counts),'visits',visits,'depth',maximum_depth,
          'exact lower numerators over',REPORT,
          {key:floor(value*REPORT) for key,value in margins.items()},flush=True)


if __name__=='__main__':
    verify_root('tilted')
    verify_root('aligned')
    verify_near()

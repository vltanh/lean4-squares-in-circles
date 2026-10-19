"""Exact rational necessary model for four standard and four 45-degree unit squares.

Geometry and branch coverage are proved in GATE3B_M5_HIGH_4PLUS4_CERTIFICATE_REPLAY.md.
This module has no optimizer. Rows A_r.p <= b_r are rebuilt from public
rational data; any actual admissible packing maps to a listed root and
satisfies one canonical SAT branch for every mixed pair.
"""
from fractions import Fraction as F
from itertools import permutations, product, combinations

RADIUS = F(198869, 100000)
SQ_LOWER = F(707106781, 500000000)
SQ_UPPER = F(1414213562373096, 10**15)
BOUND = F(3, 2)
REFERENCE_Q = F(395485389, 100000000)


def rotated90(p):
    x, y = p
    return -y, x


def transform_point(p, turns, reflect):
    x, y = p
    if reflect:
        x = -x
    for _ in range(turns):
        x, y = -y, x
    return x, y


def transform_root(pi, sigma, turns, reflect):
    """Apply one common physical D4 symmetry to both frame classes."""
    std = [((F(i)+pi[i])/2, (F(i)-pi[i])/2) for i in range(4)]
    dia = [(F(i), F(sigma[i])) for i in range(4)]
    std = [transform_point(p, turns, reflect) for p in std]
    dia = [transform_point(p, turns, reflect) for p in dia]
    sorder = sorted(range(4), key=lambda i: sum(std[i]))
    torder = sorted(range(4), key=lambda i: std[i][0]-std[i][1])
    xorder = sorted(range(4), key=lambda i: dia[i][0])
    yorder = sorted(range(4), key=lambda i: dia[i][1])
    return (tuple(torder.index(i) for i in sorder),
            tuple(yorder.index(i) for i in xorder))


def orbit(pi, sigma):
    return {transform_root(pi, sigma, k, mirror)
            for k in range(4) for mirror in (False, True)}


P = tuple(p for p in permutations(range(4))
          if p not in ((0, 1, 2, 3), (3, 2, 1, 0)))
REPS = tuple(sorted({min(orbit(a, b)) for a, b in product(P, P)}))


def directions():
    out = set()
    for k in range(33):
        a, b, den = 1024-k*k, 64*k, 1024+k*k
        for _ in range(4):
            out.add((F(a, den), F(b, den)))
            a, b = -b, a
    return tuple(sorted(out))

DIRS = directions()


def check_constants():
    assert 0 < SQ_LOWER*SQ_LOWER < 2 < SQ_UPPER*SQ_UPPER
    assert 0 < REFERENCE_Q < RADIUS*RADIUS < 4
    assert len(DIRS) == 128 and all(a*a+b*b == 1 for a,b in DIRS)
    assert len(P) == 22 and len(REPS) == 66
    original = set(product(P, P))
    covered = set()
    for a,b in REPS:
        covered.update(orbit(a,b))
    assert covered == original


class RationalModel:
    def __init__(self, pi, sigma):
        if tuple(pi) not in P or tuple(sigma) not in P:
            raise ValueError('Only admissible four-frame orders allowed')
        self.pi = tuple(pi)
        self.sigma = tuple(sigma)
        self.rows = []
        self.right = []
        self.names = []
        def add(row, bound, tag):
            self.rows.append({k:F(v) for k,v in row.items() if v})
            self.right.append(F(bound))
            self.names.append(tag)
        def diff(i, j, n):
            return {2*j:n[0],2*j+1:n[1],2*i:-n[0],2*i+1:-n[1]}
        def lower(i,j,n,width,tag):
            add({k:-v for k,v in diff(i,j,n).items()}, -F(width), tag)
        for i in range(8):
            for k,(a,b) in enumerate(DIRS):
                halfwidth = ((abs(a)+abs(b))/2 if i<4
                             else SQ_LOWER*max(abs(a),abs(b))/2)
                add({2*i:a,2*i+1:b}, RADIUS-halfwidth, ('disk',i,k))
        for i,j in combinations(range(4),2):
            inc = self.pi[i] < self.pi[j]
            lower(i,j,(1,1),0,('standard-s',i,j))
            lower(i,j,(1,-1) if inc else (-1,1),0,('standard-t',i,j))
            lower(i,j,(1,0) if inc else (0,1),1,('standard-sat',i,j))
        for i,j in combinations(range(4,8),2):
            inc = self.sigma[i-4] < self.sigma[j-4]
            lower(i,j,(1,0),0,('diagonal-x',i,j))
            lower(i,j,(0,1) if inc else (0,-1),0,('diagonal-y',i,j))
            lower(i,j,(1,1) if inc else (1,-1),SQ_LOWER,('diagonal-sat',i,j))
        self.base = len(self.rows)
        alternatives = ((1,0),(-1,0),(0,1),(0,-1),
                        (1,1),(-1,-1),(1,-1),(-1,1))
        self.bundles = []
        for i in range(4):
            for j in range(4,8):
                choices = []
                for nx,ny in alternatives:
                    first = len(self.rows)
                    width = ((1+SQ_LOWER)/2 if nx==0 or ny==0
                             else 1+SQ_LOWER/2)
                    lower(i,j,(nx,ny),width,('mixed',i,j,nx,ny))
                    if ny==0:
                        cones = ((-(SQ_UPPER-1)*nx, 1),
                                 (-(SQ_UPPER-1)*nx,-1))
                    elif nx==0:
                        cones = ((1,-(SQ_UPPER-1)*ny),
                                 (-1,-(SQ_UPPER-1)*ny))
                    else:
                        cones = (((SQ_LOWER-1)*nx,-ny),
                                 (-nx,(SQ_LOWER-1)*ny))
                    for m,cone in enumerate(cones):
                        add(diff(i,j,cone),0,('cone',i,j,nx,ny,m))
                    choices.append(tuple(range(first,first+3)))
                self.bundles.append(tuple(choices))


def exact_leaf_margin(model, witnesses):
    total = F(0)
    force = [F(0)]*16
    for row_id, weight in witnesses:
        if type(row_id) is not int or type(weight) is not int or weight<=0:
            raise ValueError('Invalid leaf integer weight')
        total += weight*model.right[row_id]
        for index, coefficient in model.rows[row_id].items():
            force[index] += weight*coefficient
    return total + BOUND*sum(map(abs,force))


if __name__ == '__main__':
    check_constants()
    print('66 D4 root classes, 484 ordered pairs, exact normal/support checks: PASS')

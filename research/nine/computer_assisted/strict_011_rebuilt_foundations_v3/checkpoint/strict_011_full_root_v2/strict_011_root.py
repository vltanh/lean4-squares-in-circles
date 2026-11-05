#!/usr/bin/env python3
"""Fresh full strict-011/00 physical root and rational row producer.

This module imports only the Python standard library.  In particular it does
not load a registered 001 cell, legacy V/K, a numerical Context, or a solver.
The companion independent adapter is required before any proof use.  Merely
constructing this necessary affine relaxation proves no domain excluded.
"""
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt

Q = F(1105, 256)
RHO = F(91, 60)
ROOT_ID = 'full-strict-01100-root-v2'
PREFIX = 'strict011v2:'
GRID = 1 << 48
EDGES = ((0, 1, 0), (1, 2, 1), (2, 3, 1), (4, 5, 0), (5, 6, 0))
PAIRS = tuple(combinations(range(9), 2))
CORNERS = tuple((i, e, t) for i in range(9)
                for e, t in product((-1, 1), repeat=2))
DIRECTIONS = tuple((p, q) for p in range(-33, 34)
                   for q in range(-33, 34) if p*p + q*q == 1105)
SMALL_DIRECTIONS = tuple((p, q) for p in (-1, 0, 1)
                         for q in (-1, 0, 1) if p or q)
TANGENT_PARAMETERS = (F(1), F(9, 8), F(5, 4), F(11, 8), F(3, 2))


def rational_box(value):
    return tuple(tuple(map(F, interval)) for interval in value)


def box_view(value):
    return [[str(a), str(b)] for a, b in value]


def state_view(state):
    return dict(id=state['id'], path=deepcopy(state['path']),
                angles=box_view(state['angles']),
                positions=box_view(state['positions']),
                scalar=box_view(state['scalar']),
                differences=[dict(pair=list(pair), intervals=box_view(box))
                             for pair, box in sorted(state['differences'].items())],
                diagonal=[])


def sqrt_box(value):
    value = F(value)
    assert value >= 0
    n, d = value.numerator * GRID * GRID, value.denominator
    k = isqrt(n // d)
    assert k*k*d <= n < (k+1)*(k+1)*d
    return F(k, GRID), F(k if k*k*d == n else k+1, GRID)


def signed_beta(t):
    t = F(t)
    low, high = sqrt_box(t*t / (1+t*t))
    return (low, high) if t >= 0 else (-high, -low)


def absolute_slope_bounds(interval):
    lo, hi = map(F, interval)
    assert -1 <= lo <= hi <= 1
    return (F(0) if lo <= 0 <= hi else min(abs(lo), abs(hi)),
            max(abs(lo), abs(hi)))


def width_sum_bounds(interval):
    small, large = absolute_slope_bounds(interval)
    low = sqrt_box((1+small)**2 / (1+small*small))[0]
    high = sqrt_box((1+large)**2 / (1+large*large))[1]
    return low, high


def analytic(angles):
    """Outward rational intervals for alpha, beta, |beta| and g, in blocks."""
    assert len(angles) == 9
    aa, bb, zz, gg = [], [], [], []
    for interval in angles:
        lo, hi = map(F, interval)
        small, large = absolute_slope_bounds((lo, hi))
        aa.append((sqrt_box(1/(1+large*large))[0],
                   sqrt_box(1/(1+small*small))[1]))
        bb.append((signed_beta(lo)[0], signed_beta(hi)[1]))
        zz.append((sqrt_box(small*small/(1+small*small))[0],
                   sqrt_box(large*large/(1+large*large))[1]))
        gg.append((sqrt_box((1+large*large)/(4*(1+large)**2))[0],
                   sqrt_box((1+small*small)/(4*(1+small)**2))[1]))
    return tuple(aa + bb + zz + gg)


def coarse_scalar():
    return tuple([(F(7, 10), F(1))]*9 + [(F(-3, 4), F(3, 4))]*9
                 + [(F(0), F(3, 4))]*9 + [(F(1, 3), F(1, 2))]*9)


def path_data(path):
    """Only new physical SAT/proxy choices and closed angle cuts are allowed."""
    assert isinstance(path, list)
    selected, angles, seen = [], [[F(-1), F(1)] for _ in range(9)], set()
    for entry in path:
        assert isinstance(entry, list) and len(entry) == 3
        kind, pair, choice = entry
        if kind == 'full_angle':
            assert isinstance(pair, list) and len(pair) == 2
            original, cut = pair
            assert type(original) is int and 0 <= original < 9
            cut = F(cut)
            assert type(choice) is int and choice in (0, 1)
            assert angles[original][0] <= cut <= angles[original][1]
            angles[original][1 if choice == 0 else 0] = cut
            continue
        assert kind in ('proxy', 'sat'), 'No old cell escape or normalization is allowed.'
        assert isinstance(pair, list) and len(pair) == 2
        assert all(type(i) is int for i in pair) and 0 <= pair[0] < pair[1] < 9
        assert isinstance(choice, list) and all(type(i) is int for i in choice)
        if kind == 'proxy':
            assert len(choice) == 2 and choice[0] in (0, 1) and choice[1] in (-1, 1)
        else:
            assert (len(choice) == 3 and choice[0] in pair
                    and choice[1] in (0, 1) and choice[2] in (-1, 1))
        key = kind, tuple(pair)
        assert key not in seen
        seen.add(key)
        selected.append((tuple(pair), kind, tuple(choice)))
    return selected, tuple(map(tuple, angles))


def choices(path):
    return path_data(path)[0]


def fresh_state():
    return dict(id=ROOT_ID, path=[], angles=tuple([(F(-1), F(1))]*9),
                positions=tuple([(-RHO, RHO)]*18), scalar=coarse_scalar(),
                differences={}, diagonal={}, choices=[])


def root_document():
    return dict(schema='full_strict_01100_physical_root_v2',
                status='IMPLEMENTED_INDEPENDENT_REVIEW_REQUIRED_NO_CLOSURE',
                original_id=ROOT_ID, mask='011/00', radius_mode='strict',
                target_q=str(Q), physical_originals=list(range(9)),
                original_corners=[list(corner) for corner in CORNERS],
                original_pairs=[list(pair) for pair in PAIRS],
                owned_pair_cover=[dict(pair=list(pair), alternatives=[list(c)
                    for c in product(pair, (0, 1), (-1, 1))]) for pair in PAIRS],
                exact_mask_edges=[dict(pair=[i, j], bit=bit,
                    cone='xj-xi >= abs(yj-yi)',
                    bit_relation='xj-xi < hi+hj' if bit else 'xj-xi >= hi+hj')
                    for i, j, bit in EDGES],
                exact_frame_relations=[
                    'u=(alpha,beta), v=(-beta,alpha)',
                    'alpha^2+beta^2=1', 'alpha>=abs(beta)', 'z=abs(beta)',
                    'h=(alpha+z)/2', 'g=1/(2*(alpha+z))'],
                corner_relation='Every original corner norm_squared < 1105/256',
                pair_relation='Every original pair has disjoint open interiors; physical contact allowed',
                initial=state_view(fresh_state()), variable_columns=54,
                variable_blocks=dict(position=list(range(18)), alpha=list(range(18, 27)),
                    beta=list(range(27, 36)), absolute_beta=list(range(36, 45)),
                    inset_halfside=list(range(45, 54))),
                universal_center_radius=str(RHO),
                universal_center_radius_squared_margin=str(RHO*RHO+RHO+F(1, 2)-Q),
                inherited_original_cells=[], inherited_001_premises=[],
                extra_normalizations=[], installed_conditional_terminals=[],
                numerical_solver_called=False, whole_mask_credit=0)


def validate_state(state):
    assert state['id'] == ROOT_ID
    selected, path_angles = path_data(state['path'])
    assert state['choices'] == selected
    assert set(state) == {'id', 'path', 'angles', 'positions', 'scalar',
                          'differences', 'diagonal', 'choices'}
    assert len(state['angles']) == 9 and len(state['positions']) == 18 and len(state['scalar']) == 36
    for (lo, hi), (a, b) in zip(state['angles'], path_angles):
        assert a <= lo <= hi <= b
    for lo, hi in state['positions']:
        assert -RHO <= lo <= hi <= RHO
    for (lo, hi), (a, b) in zip(state['scalar'], coarse_scalar()):
        assert a <= lo <= hi <= b
    assert not state['diagonal'], 'No diagonal propagation rule is installed in v2.'
    assert set(state['differences']) <= set(PAIRS)
    for intervals in state['differences'].values():
        assert len(intervals) == 2 and all(lo <= hi for lo, hi in intervals)
    return True


def parse_state(value):
    assert set(value) == {'id', 'path', 'angles', 'positions', 'scalar', 'differences', 'diagonal'}
    assert value['diagonal'] == []
    entries = value['differences']
    assert len({tuple(e['pair']) for e in entries}) == len(entries)
    state = dict(id=value['id'], path=deepcopy(value['path']),
                 angles=rational_box(value['angles']), positions=rational_box(value['positions']),
                 scalar=rational_box(value['scalar']),
                 differences={tuple(e['pair']): rational_box(e['intervals']) for e in entries},
                 diagonal={}, choices=choices(value['path']))
    validate_state(state)
    return state


def propagate(state):
    validate_state(state)
    result = deepcopy(state)
    scalar = []
    for k, ((a, b), (c, d)) in enumerate(zip(state['scalar'], analytic(state['angles']))):
        lo, hi = max(a, c), min(b, d)
        if lo > hi:
            return None, dict(kind='strict011_empty_scalar_intersection', index=k,
                              lower=str(lo), upper=str(hi))
        scalar.append((lo, hi))
    result['scalar'] = tuple(scalar)
    differences = {}
    for i, j in PAIRS:
        intervals = []
        for axis in (0, 1):
            a, b = state['positions'][2*i+axis]
            c, d = state['positions'][2*j+axis]
            lo, hi = c-b, d-a
            if (i, j) in state['differences']:
                e, f = state['differences'][i, j][axis]
                lo, hi = max(lo, e), min(hi, f)
            if lo > hi:
                return None, dict(kind='strict011_empty_difference_intersection',
                                  pair=[i, j], axis=axis, lower=str(lo), upper=str(hi))
            intervals.append((lo, hi))
        differences[i, j] = tuple(intervals)
    result['differences'] = differences
    return result, None


def make_row(kind, parameters, terms, rhs=F(0)):
    co = {}
    for index, value in terms:
        assert type(index) is int and index >= 0
        co[index] = co.get(index, F(0)) + F(value)
    name = PREFIX + ':'.join([kind] + [str(x) for x in parameters])
    return tuple((k, v) for k, v in sorted(co.items()) if v), F(rhs), name


def scale(terms, factor):
    return [(k, F(factor)*v) for k, v in terms]


def linear_interval(terms, intervals):
    lo = hi = F(0)
    for k, c in terms:
        a, b = intervals[k]
        lo += min(c*a, c*b)
        hi += max(c*a, c*b)
    return lo, hi


def product_interval(left, right):
    values = [a*b for a in left for b in right]
    return min(values), max(values)


def sat_products(state):
    original = state['positions'] + state['scalar']
    selected = [entry for entry in state['choices'] if entry[1] == 'sat']
    answer = []
    for slot, (pair, _, choice) in enumerate(selected):
        i, j = pair
        owner, axis, sign = choice
        normal = (((18+owner, F(sign)),), ((27+owner, F(sign)),)) if axis == 0 else (
            ((27+owner, F(-sign)),), ((18+owner, F(sign)),))
        products = []
        for direction in (0, 1):
            U = normal[direction]
            V = ((2*j+direction, F(1)), (2*i+direction, F(-1)))
            products.append((54+6*slot+direction, U, V,
                             linear_interval(U, original), state['differences'][pair][direction]))
        for offset, a, b in ((2, 18+i, 18+j), (3, 27+i, 27+j),
                             (4, 18+i, 27+j), (5, 27+i, 18+j)):
            products.append((54+6*slot+offset, ((a, F(1)),), ((b, F(1)),),
                             original[a], original[b]))
        answer.append((pair, choice, tuple(products)))
    return tuple(answer)


def collect(state):
    """Return exact necessary rows, absolute bounds, propagated state, terminal."""
    propagated, terminal = propagate(state)
    if terminal is not None:
        return None, None, None, terminal
    pos, scalar, angles = propagated['positions'], propagated['scalar'], propagated['angles']
    original = pos + scalar
    intervals = list(original)
    selected = sat_products(propagated)
    for pair, choice, products in selected:
        intervals.extend(product_interval(left, right) for _, _, _, left, right in products)
    rows = []

    def add(kind, params, terms, rhs=F(0)):
        rows.append(make_row(kind, params, terms, rhs))

    for k, (lo, hi) in enumerate(intervals):
        add('bound', (k, 1), [(k, 1)], hi)
        add('bound', (k, -1), [(k, -1)], -lo)
    for i, angle in enumerate(angles):
        a, b, z, g = 18+i, 27+i, 36+i, 45+i
        add('fold', (i,), [(z, 1), (a, -1)])
        add('absolute_lower', (i, 1), [(b, 1), (z, -1)])
        add('absolute_lower', (i, -1), [(b, -1), (z, -1)])
        add('width_floor', (i,), [(a, -1), (z, -1)], -1)
        lo, hi = angle
        add('slope', (i, 0), [(a, lo), (b, -1)])
        add('slope', (i, 1), [(b, 1), (a, -hi)])
        sl, su = width_sum_bounds(angle)
        add('width_interval', (i, -1), [(a, -1), (z, -1)], -sl)
        add('width_interval', (i, 1), [(a, 1), (z, 1)], su)
        bl, bu = original[b]
        if bl >= 0:
            add('absolute_upper', (i, 1), [(z, 1), (b, -1)])
        elif bu <= 0:
            add('absolute_upper', (i, -1), [(z, 1), (b, 1)])
        else:
            assert bl < bu
            add('absolute_chord', (i,), [(z, 1), (b, -(bu+bl)/(bu-bl))], -2*bu*bl/(bu-bl))
        for other in (b, z):
            al, au = original[a]
            vl, vu = original[other]
            add('unit_secant', (i, other), [(a, -al-au), (other, -vl-vu)], -1-al*au-vl*vu)
        for p, q in SMALL_DIRECTIONS:
            add('unit_support', (i, p, q), [(a, p), (b, q)], sqrt_box(p*p+q*q)[1])
        for sigma in TANGENT_PARAMETERS:
            add('inset_tangent', (i, sigma), [(g, -1), (a, -1/(2*sigma*sigma)),
                                             (z, -1/(2*sigma*sigma))], -1/sigma)
        add('inset_secant', (i,), [(g, 1), (a, 1/(2*sl*su)), (z, 1/(2*sl*su))],
            (sl+su)/(2*sl*su))
        for p, q in SMALL_DIRECTIONS:
            add('center_support', (i, p, q), [(2*i, p), (2*i+1, q)], RHO*sqrt_box(p*p+q*q)[1])
        for p, q in DIRECTIONS:
            for e, t in product((-1, 1), repeat=2):
                add('corner', (i, e, t, p, q),
                    [(2*i, p), (2*i+1, q), (a, F(e*p+t*q, 2)),
                     (b, F(e*q-t*p, 2))], F(1105, 16))
    for i, j, bit in EDGES:
        for sign in (-1, 1):
            add('cone', (i, j, sign), [(2*i, 1), (2*j, -1),
                                     (2*j+1, sign), (2*i+1, -sign)])
        terms = [(2*i, F(1)), (2*j, F(-1)), (18+i, F(1, 2)),
                 (36+i, F(1, 2)), (18+j, F(1, 2)), (36+j, F(1, 2))]
        add('mask', (i, j, bit), scale(terms, -1 if bit else 1))
        add('cone_inset', (i, j), [(2*i, 1), (2*j, -1), (45+i, 1), (45+j, 1)])
    for i, j in PAIRS:
        ds = propagated['differences'][i, j]
        for axis, (lo, hi) in enumerate(ds):
            add('difference', (i, j, axis, 1), [(2*j+axis, 1), (2*i+axis, -1)], hi)
            add('difference', (i, j, axis, -1), [(2*j+axis, -1), (2*i+axis, 1)], -lo)
        (lx, ux), (ly, uy) = ds
        add('distance', (i, j), [(2*i, lx+ux), (2*j, -lx-ux),
                               (2*i+1, ly+uy), (2*j+1, -ly-uy)], -1-lx*ux-ly*uy)
    for (i, j), kind, choice in propagated['choices']:
        if kind == 'proxy':
            axis, sign = choice
            add('proxy', (i, j, axis, sign), [(2*i+axis, sign), (2*j+axis, -sign),
                                             (45+i, 1), (45+j, 1)])
    for slot, (pair, choice, products) in enumerate(selected):
        for target, U, V, (ul, uu), (vl, vu) in products:
            offset = target-(54+6*slot)
            add('mccormick', (slot, offset, 0), [(target, -1)]+scale(V, ul)+scale(U, vl), ul*vl)
            add('mccormick', (slot, offset, 1), [(target, -1)]+scale(V, uu)+scale(U, vu), uu*vu)
            add('mccormick', (slot, offset, 2), [(target, 1)]+scale(V, -uu)+scale(U, -vl), -uu*vl)
            add('mccormick', (slot, offset, 3), [(target, 1)]+scale(V, -ul)+scale(U, -vu), -ul*vu)
        x = 54+6*slot
        for c, s in product((-1, 1), repeat=2):
            add('separation', (slot, c, s), [(x, -2), (x+1, -2), (x+2, c),
                                            (x+3, c), (x+4, s), (x+5, -s)], -1)
        add('projection_floor', (slot,), [(x, -1), (x+1, -1)], -1)
        add('relative_cosine', (slot, -1), [(x+2, -1), (x+3, -1)])
        add('relative_cosine', (slot, 1), [(x+2, 1), (x+3, 1)], 1)
        for sign in (-1, 1):
            add('relative_sine', (slot, sign), [(x+4, sign), (x+5, -sign)], 1)
    assert len({row[2] for row in rows}) == len(rows)
    bounds = tuple(max(abs(lo), abs(hi)) for lo, hi in intervals)
    return rows, bounds, propagated, None


def physical_child(parent, kind, pair, choice):
    validate_state(parent)
    assert kind in ('sat', 'proxy')
    child = deepcopy(parent)
    child['path'].append([kind, list(pair), list(choice)])
    child['choices'] = choices(child['path'])
    validate_state(child)
    return child


def angle_child(parent, original, cut, side):
    validate_state(parent)
    assert type(original) is int and 0 <= original < 9
    assert type(side) is int and side in (0, 1)
    cut = F(cut)
    assert parent['angles'][original][0] < cut < parent['angles'][original][1]
    child = deepcopy(parent)
    child['path'].append(['full_angle', [original, str(cut)], side])
    angles = [list(interval) for interval in child['angles']]
    angles[original][1 if side == 0 else 0] = cut
    child['angles'] = tuple(map(tuple, angles))
    child['choices'] = choices(child['path'])
    validate_state(child)
    return child


def infer_angles(angles, scalar):
    """Conservative v2 interface: no scalar-to-angle contraction is asserted."""
    assert len(angles) == 9 and len(scalar) == 36
    return tuple(map(tuple, angles)), None, []


class Context:
    """Solver-free interface; no existing numerical Context is initialized."""
    collect = staticmethod(collect)
    child = staticmethod(lambda state, pair, choice: physical_child(state, 'sat', pair, choice))
    proxy_child = staticmethod(lambda state, pair, choice: physical_child(state, 'proxy', pair, choice))
    angle_child = staticmethod(angle_child)
    analytic = staticmethod(analytic)
    infer_angles = staticmethod(infer_angles)

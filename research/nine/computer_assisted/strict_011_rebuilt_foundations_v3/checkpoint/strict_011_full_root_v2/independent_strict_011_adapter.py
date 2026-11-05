#!/usr/bin/env python3
"""Independent exact attachment for the fresh full strict-011/00 root.

No producer, optimizer, old original-cell context, or legacy geometry is
imported.  Printed rows are reconstructed from their names and the same
already-certified physical state.  The enclosing complete-tree replay must
begin with verify_root() and retain every closed cover alternative.
"""
from copy import deepcopy
from fractions import Fraction as Rational
from itertools import combinations, product
from math import isqrt

R = Rational
IDENTITY = 'full-strict-01100-root-v2'
NAMESPACE = 'strict011v2:'
RADIUS_SQUARED = R(1105, 256)
CENTER_BOUND = R(91, 60)
LINKS = ((0, 1, 0), (1, 2, 1), (2, 3, 1), (4, 5, 0), (5, 6, 0))
PAIR_SET = set(combinations(range(9), 2))
UNIT_NORMALS = {(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1) if a or b}
INSET_TANGENCIES = {R(1), R(9, 8), R(5, 4), R(11, 8), R(3, 2)}
DEN = 2**48


def square_root_enclosure(argument):
    argument = R(argument)
    assert argument >= 0
    n = isqrt(argument.numerator * DEN**2 // argument.denominator)
    low = R(n, DEN)
    high = low if low*low == argument else R(n+1, DEN)
    assert 0 <= low <= high and low*low <= argument <= high*high
    assert high-low in (R(0), R(1, DEN))
    assert (low+R(1, DEN))**2 > argument
    return low, high


def beta_at_slope(value):
    value = R(value)
    lower, upper = square_root_enclosure(value**2/(1+value**2))
    if value < 0:
        return -upper, -lower
    return lower, upper


def absolute_slope(interval):
    left, right = interval
    assert -1 <= left <= right <= 1
    minimum = R(0) if left <= 0 <= right else min(abs(left), abs(right))
    return minimum, max(abs(left), abs(right))


def frame_width_interval(interval):
    nearest, farthest = absolute_slope(interval)
    return (square_root_enclosure((1+nearest)**2/(1+nearest**2))[0],
            square_root_enclosure((1+farthest)**2/(1+farthest**2))[1])


def analytic(angles):
    assert len(angles) == 9
    result = [None]*36
    for i, (left, right) in enumerate(angles):
        minimum, maximum = absolute_slope((left, right))
        result[i] = (square_root_enclosure(R(1)/(1+maximum**2))[0],
                     square_root_enclosure(R(1)/(1+minimum**2))[1])
        result[9+i] = (beta_at_slope(left)[0], beta_at_slope(right)[1])
        result[18+i] = (square_root_enclosure(minimum**2/(1+minimum**2))[0],
                        square_root_enclosure(maximum**2/(1+maximum**2))[1])
        result[27+i] = (square_root_enclosure((1+maximum**2)/(4*(1+maximum)**2))[0],
                        square_root_enclosure((1+minimum**2)/(4*(1+minimum)**2))[1])
    return tuple(result)


def root_scalar_intervals():
    return tuple([(R(7, 10), R(1)) for _ in range(9)]
                 + [(R(-3, 4), R(3, 4)) for _ in range(9)]
                 + [(R(0), R(3, 4)) for _ in range(9)]
                 + [(R(1, 3), R(1, 2)) for _ in range(9)])


def reconstruct_path(path):
    assert type(path) is list
    angle_conditions = [[R(-1), R(1)] for _ in range(9)]
    alternatives, used = [], set()
    for element in path:
        assert type(element) is list and len(element) == 3
        kind, argument, side = element
        if kind == 'full_angle':
            assert type(argument) is list and len(argument) == 2
            i, split = argument
            assert type(i) is int and 0 <= i < 9
            assert type(side) is int and side in (0, 1)
            split = R(split)
            assert angle_conditions[i][0] <= split <= angle_conditions[i][1]
            if side == 0:
                angle_conditions[i][1] = split
            else:
                angle_conditions[i][0] = split
        else:
            assert kind in ('sat', 'proxy')
            assert type(argument) is list and len(argument) == 2
            assert all(type(i) is int for i in argument)
            pair = tuple(argument)
            assert pair in PAIR_SET
            assert type(side) is list and all(type(i) is int for i in side)
            if kind == 'sat':
                assert len(side) == 3 and side[0] in pair and side[1] in (0, 1) and side[2] in (-1, 1)
            else:
                assert len(side) == 2 and side[0] in (0, 1) and side[1] in (-1, 1)
            assert (pair, kind) not in used
            used.add((pair, kind))
            alternatives.append((pair, kind, tuple(side)))
    return alternatives, tuple(map(tuple, angle_conditions))


def choices(path):
    return reconstruct_path(path)[0]


def state_view(state):
    def show(box):
        return [[str(a), str(b)] for a, b in box]
    return dict(id=state['id'], path=deepcopy(state['path']),
                angles=show(state['angles']), positions=show(state['positions']),
                scalar=show(state['scalar']),
                differences=[dict(pair=list(pair), intervals=show(box))
                             for pair, box in sorted(state['differences'].items())],
                diagonal=[])


def expected_initial_state():
    return dict(id=IDENTITY, path=[], angles=tuple([(R(-1), R(1))]*9),
                positions=tuple([(-CENTER_BOUND, CENTER_BOUND)]*18),
                scalar=root_scalar_intervals(), differences={}, diagonal={}, choices=[])


def verify_root(document):
    expected = dict(schema='full_strict_01100_physical_root_v2',
        status='IMPLEMENTED_INDEPENDENT_REVIEW_REQUIRED_NO_CLOSURE',
        original_id=IDENTITY, mask='011/00', radius_mode='strict', target_q='1105/256',
        physical_originals=list(range(9)),
        original_corners=[[i, e, t] for i in range(9) for e, t in product((-1, 1), repeat=2)],
        original_pairs=[list(p) for p in sorted(PAIR_SET)],
        owned_pair_cover=[dict(pair=list(p), alternatives=[list(c)
            for c in product(p, (0, 1), (-1, 1))]) for p in sorted(PAIR_SET)],
        exact_mask_edges=[dict(pair=[i, j], bit=bit, cone='xj-xi >= abs(yj-yi)',
            bit_relation='xj-xi < hi+hj' if bit else 'xj-xi >= hi+hj') for i, j, bit in LINKS],
        exact_frame_relations=['u=(alpha,beta), v=(-beta,alpha)',
            'alpha^2+beta^2=1', 'alpha>=abs(beta)', 'z=abs(beta)',
            'h=(alpha+z)/2', 'g=1/(2*(alpha+z))'],
        corner_relation='Every original corner norm_squared < 1105/256',
        pair_relation='Every original pair has disjoint open interiors; physical contact allowed',
        initial=state_view(expected_initial_state()), variable_columns=54,
        variable_blocks=dict(position=list(range(18)), alpha=list(range(18, 27)),
            beta=list(range(27, 36)), absolute_beta=list(range(36, 45)),
            inset_halfside=list(range(45, 54))),
        universal_center_radius='91/60', universal_center_radius_squared_margin='31/57600',
        inherited_original_cells=[], inherited_001_premises=[], extra_normalizations=[],
        installed_conditional_terminals=[], numerical_solver_called=False, whole_mask_credit=0)
    assert document == expected, 'The entire strict caller must match; no extra or omitted premise.'
    assert CENTER_BOUND**2+CENTER_BOUND+R(1, 2)-RADIUS_SQUARED == R(31, 57600) > 0
    assert R(7, 10)**2 < R(1, 2) < R(3, 4)**2
    assert R(1, 3)**2 < R(1, 8)
    return expected_initial_state()


def validate_state(state):
    assert set(state) == {'id', 'path', 'angles', 'positions', 'scalar', 'differences', 'diagonal', 'choices'}
    assert state['id'] == IDENTITY
    selected, angle_limits = reconstruct_path(state['path'])
    assert selected == state['choices']
    assert len(state['angles']) == 9 and len(state['positions']) == 18 and len(state['scalar']) == 36
    for current, permitted in zip(state['angles'], angle_limits):
        assert len(current) == 2 and permitted[0] <= current[0] <= current[1] <= permitted[1]
    for lower, upper in state['positions']:
        assert -CENTER_BOUND <= lower <= upper <= CENTER_BOUND
    for (lower, upper), (a, b) in zip(state['scalar'], root_scalar_intervals()):
        assert a <= lower <= upper <= b
    assert state['diagonal'] == {}
    assert set(state['differences']) <= PAIR_SET
    for intervals in state['differences'].values():
        assert len(intervals) == 2 and all(len(ab) == 2 and ab[0] <= ab[1] for ab in intervals)
    return True


def propagate(state):
    validate_state(state)
    answer = deepcopy(state)
    new_scalars = []
    for index, (old, trigonometric) in enumerate(zip(state['scalar'], analytic(state['angles']))):
        lower = max(old[0], trigonometric[0])
        upper = min(old[1], trigonometric[1])
        if lower > upper:
            return None, dict(kind='strict011_empty_scalar_intersection', index=index,
                              lower=str(lower), upper=str(upper))
        new_scalars.append((lower, upper))
    answer['scalar'] = tuple(new_scalars)
    answer['differences'] = {}
    for i, j in sorted(PAIR_SET):
        rectangle = []
        for direction in (0, 1):
            left = state['positions'][2*i+direction]
            right = state['positions'][2*j+direction]
            lower, upper = right[0]-left[1], right[1]-left[0]
            previous = state['differences'].get((i, j))
            if previous is not None:
                lower, upper = max(lower, previous[direction][0]), min(upper, previous[direction][1])
            if lower > upper:
                return None, dict(kind='strict011_empty_difference_intersection', pair=[i, j],
                                  axis=direction, lower=str(lower), upper=str(upper))
            rectangle.append((lower, upper))
        answer['differences'][i, j] = tuple(rectangle)
    return answer, None


def normalized(terms):
    co = {}
    for column, coefficient in terms:
        assert type(column) is int and column >= 0
        co[column] = co.get(column, R(0)) + R(coefficient)
    return tuple((k, v) for k, v in sorted(co.items()) if v)


def multiply(terms, coefficient):
    return [(k, coefficient*v) for k, v in terms]


def term_interval(terms, boxes):
    lower, upper = R(0), R(0)
    for column, coefficient in terms:
        candidates = [coefficient*bound for bound in boxes[column]]
        lower, upper = lower+min(candidates), upper+max(candidates)
    return lower, upper


def selected_products(state):
    originals = state['positions'] + state['scalar']
    descriptors, boxes = [], list(originals)
    for pair, kind, choice in state['choices']:
        if kind != 'sat':
            continue
        i, j = pair
        owner, direction, sign = choice
        if direction == 0:
            normal = [[(18+owner, R(sign))], [(27+owner, R(sign))]]
        else:
            normal = [[(27+owner, R(-sign))], [(18+owner, R(sign))]]
        six = []
        for axis in range(2):
            U, V = normal[axis], [(2*j+axis, R(1)), (2*i+axis, R(-1))]
            six.append((U, V, term_interval(U, originals), state['differences'][pair][axis]))
        for left, right in ((18+i, 18+j), (27+i, 27+j), (18+i, 27+j), (27+i, 18+j)):
            six.append(([(left, R(1))], [(right, R(1))], originals[left], originals[right]))
        descriptors.append((pair, choice, six))
        for _, _, left, right in six:
            products = [a*b for a in left for b in right]
            boxes.append((min(products), max(products)))
    return descriptors, tuple(boxes)


def row_from_name(name, state, products, intervals):
    assert type(name) is str and name.startswith(NAMESPACE)
    fields = name[len(NAMESPACE):].split(':')
    family, fields = fields[0], fields[1:]
    terms, rhs = [], R(0)

    def integers(count):
        assert len(fields) == count
        result = tuple(int(value) for value in fields)
        assert all(str(i) == v for i, v in zip(result, fields))
        return result

    def original(i):
        assert 0 <= i < 9
        return 18+i, 27+i, 36+i, 45+i

    def chosen_slot(slot):
        assert 0 <= slot < len(products)
        return 54+6*slot

    if family == 'bound':
        column, sign = integers(2)
        assert 0 <= column < len(intervals) and sign in (-1, 1)
        terms = [(column, sign)]
        rhs = intervals[column][1] if sign == 1 else -intervals[column][0]
    elif family in ('fold', 'width_floor', 'absolute_chord', 'inset_secant'):
        (i,) = integers(1)
        a, b, z, g = original(i)
        if family == 'fold':
            terms = [(z, 1), (a, -1)]
        elif family == 'width_floor':
            terms, rhs = [(a, -1), (z, -1)], R(-1)
        elif family == 'absolute_chord':
            low, high = intervals[b]
            assert low < 0 < high
            terms, rhs = [(z, 1), (b, -(high+low)/(high-low))], -2*high*low/(high-low)
        else:
            lower, upper = frame_width_interval(state['angles'][i])
            assert lower > 0
            terms = [(g, 1), (a, R(1)/(2*lower*upper)), (z, R(1)/(2*lower*upper))]
            rhs = (lower+upper)/(2*lower*upper)
    elif family in ('absolute_lower', 'absolute_upper', 'slope', 'width_interval', 'unit_secant'):
        i, flag = integers(2)
        a, b, z, g = original(i)
        left, right = state['angles'][i]
        if family == 'absolute_lower':
            assert flag in (-1, 1)
            terms = [(b, flag), (z, -1)]
        elif family == 'absolute_upper':
            assert flag in (-1, 1)
            assert intervals[b][0] >= 0 if flag == 1 else intervals[b][1] <= 0
            terms = [(z, 1), (b, -flag)]
        elif family == 'slope':
            assert flag in (0, 1)
            terms = [(a, left), (b, -1)] if flag == 0 else [(b, 1), (a, -right)]
        elif family == 'width_interval':
            assert flag in (-1, 1)
            bounds = frame_width_interval((left, right))
            terms = [(a, flag), (z, flag)]
            rhs = bounds[1] if flag == 1 else -bounds[0]
        else:
            assert flag in (b, z)
            low, high = intervals[a]
            vl, vu = intervals[flag]
            terms = [(a, -low-high), (flag, -vl-vu)]
            rhs = -1-low*high-vl*vu
    elif family in ('unit_support', 'center_support'):
        i, p, q = integers(3)
        a, b, z, g = original(i)
        assert (p, q) in UNIT_NORMALS
        if family == 'unit_support':
            terms = [(a, p), (b, q)]
            rhs = square_root_enclosure(p*p+q*q)[1]
        else:
            terms = [(2*i, p), (2*i+1, q)]
            rhs = CENTER_BOUND*square_root_enclosure(p*p+q*q)[1]
    elif family == 'inset_tangent':
        assert len(fields) == 2
        i, sigma = int(fields[0]), R(fields[1])
        assert str(i) == fields[0] and str(sigma) == fields[1]
        assert sigma in INSET_TANGENCIES
        a, b, z, g = original(i)
        terms = [(g, -1), (a, -R(1)/(2*sigma*sigma)), (z, -R(1)/(2*sigma*sigma))]
        rhs = -R(1)/sigma
    elif family == 'corner':
        i, e, t, p, q = integers(5)
        a, b, z, g = original(i)
        assert e in (-1, 1) and t in (-1, 1) and p*p+q*q == 1105
        # Directly expand p*(x+(e*alpha-t*beta)/2)
        #                + q*(y+(e*beta+t*alpha)/2).
        terms = [(2*i, p), (2*i+1, q), (a, R(e*p+t*q, 2)), (b, R(e*q-t*p, 2))]
        rhs = R(1105, 16)
        assert rhs**2 == RADIUS_SQUARED*(p*p+q*q)
    elif family in ('cone', 'mask', 'cone_inset'):
        if family == 'cone_inset':
            i, j = integers(2)
            assert any((i, j) == link[:2] for link in LINKS)
            terms = [(2*i, 1), (2*j, -1), (45+i, 1), (45+j, 1)]
        else:
            i, j, flag = integers(3)
            assert any((i, j) == link[:2] for link in LINKS)
            if family == 'cone':
                assert flag in (-1, 1)
                terms = [(2*i, 1), (2*j, -1), (2*j+1, flag), (2*i+1, -flag)]
            else:
                assert (i, j, flag) in LINKS
                terms = [(2*i, R(1)), (2*j, R(-1)), (18+i, R(1, 2)),
                         (36+i, R(1, 2)), (18+j, R(1, 2)), (36+j, R(1, 2))]
                if flag == 1:
                    terms = multiply(terms, -1)
    elif family == 'difference':
        i, j, axis, sign = integers(4)
        assert (i, j) in PAIR_SET and axis in (0, 1) and sign in (-1, 1)
        lower, upper = state['differences'][i, j][axis]
        terms, rhs = [(2*j+axis, sign), (2*i+axis, -sign)], upper if sign == 1 else -lower
    elif family == 'distance':
        i, j = integers(2)
        assert (i, j) in PAIR_SET
        (xlo, xhi), (ylo, yhi) = state['differences'][i, j]
        terms = [(2*i, xlo+xhi), (2*j, -xlo-xhi), (2*i+1, ylo+yhi), (2*j+1, -ylo-yhi)]
        rhs = -1-xlo*xhi-ylo*yhi
    elif family == 'proxy':
        i, j, axis, sign = integers(4)
        assert ((i, j), 'proxy', (axis, sign)) in state['choices']
        terms = [(2*i+axis, sign), (2*j+axis, -sign), (45+i, 1), (45+j, 1)]
    elif family == 'mccormick':
        slot, offset, plane = integers(3)
        first = chosen_slot(slot)
        assert 0 <= offset < 6 and plane in range(4)
        U, V, (ul, uu), (vl, vu) = products[slot][2][offset]
        target = first+offset
        if plane == 0:
            terms, rhs = [(target, -1)]+multiply(V, ul)+multiply(U, vl), ul*vl
        elif plane == 1:
            terms, rhs = [(target, -1)]+multiply(V, uu)+multiply(U, vu), uu*vu
        elif plane == 2:
            terms, rhs = [(target, 1)]+multiply(V, -uu)+multiply(U, -vl), -uu*vl
        else:
            terms, rhs = [(target, 1)]+multiply(V, -ul)+multiply(U, -vu), -ul*vu
    elif family == 'separation':
        slot, c, s = integers(3)
        x = chosen_slot(slot)
        assert c in (-1, 1) and s in (-1, 1)
        terms, rhs = [(x, -2), (x+1, -2), (x+2, c), (x+3, c), (x+4, s), (x+5, -s)], R(-1)
    elif family == 'projection_floor':
        (slot,) = integers(1)
        x = chosen_slot(slot)
        terms, rhs = [(x, -1), (x+1, -1)], R(-1)
    elif family in ('relative_cosine', 'relative_sine'):
        slot, sign = integers(2)
        x = chosen_slot(slot)
        assert sign in (-1, 1)
        if family == 'relative_cosine':
            terms, rhs = [(x+2, sign), (x+3, sign)], R(0 if sign == -1 else 1)
        else:
            terms, rhs = [(x+4, sign), (x+5, -sign)], R(1)
    else:
        raise AssertionError('Unknown physical row family: '+family)
    assert all(0 <= column < len(intervals) for column, _ in terms)
    return normalized(terms), R(rhs), name


class Adapter:
    choices = staticmethod(choices)
    analytic = staticmethod(analytic)

    @staticmethod
    def infer_angles(angles, scalar):
        assert len(angles) == 9 and len(scalar) == 36
        return tuple(map(tuple, angles)), None, []

    @staticmethod
    def rebuild(state, printed_rows):
        current, terminal = propagate(state)
        assert terminal is None
        products, intervals = selected_products(current)
        answer = {}
        for row in printed_rows:
            index = row['index']
            assert type(index) is int and index >= 0 and index not in answer
            expected = row_from_name(row['name'], current, products, intervals)
            literal = (normalized(row['coefficients']), R(row['rhs']), row['name'])
            assert expected == literal, row['name']
            answer[index] = expected
        return answer, tuple(max(abs(a), abs(b)) for a, b in intervals), current

    @staticmethod
    def verify_early_terminal(state, terminal):
        _, expected = propagate(state)
        assert expected is not None and terminal == expected
        return True


def angle_child(parent, original, cut, side):
    validate_state(parent)
    assert type(original) is int and 0 <= original < 9
    assert type(side) is int and side in (0, 1)
    cut = R(cut)
    assert parent['angles'][original][0] < cut < parent['angles'][original][1]
    answer = deepcopy(parent)
    answer['path'].append(['full_angle', [original, str(cut)], side])
    intervals = [list(pair) for pair in answer['angles']]
    if side == 0:
        intervals[original][1] = cut
    else:
        intervals[original][0] = cut
    answer['angles'] = tuple(map(tuple, intervals))
    answer['choices'] = choices(answer['path'])
    validate_state(answer)
    return answer


def check_complete_angle_cover(parent, original, cut, children, check_record):
    sides = [side for side, record in children]
    assert len(sides) == 2 and set(sides) == {0, 1}
    reports, survivors = [], []
    adapter = Adapter()
    for side, record in children:
        report, state = check_record(record, angle_child(parent, original, cut, side), adapter)
        reports.append(dict(side=side, audit=report))
        if state is not None:
            survivors.append((side, state))
    return dict(status='PASS_COMPLETE_PHYSICAL_ANGLE_COVER' if not survivors else 'PASS_PARTIAL_PHYSICAL_ANGLE_COVER',
                original=original, cut=str(R(cut)), closed_shared_faces_retained=True,
                children=reports, whole_original_credit=0, whole_mask_credit=0), survivors

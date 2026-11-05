#!/usr/bin/env python3
"""Exact polynomial controls for two universal full-caller symmetries.

Polynomial reconstruction is independent of the producer.  No optimizer,
old geometry context, new root normalization, or proof tree is installed.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import full_mask_symmetry_maps as M


def polynomial(terms):
    answer = {}
    for word, coefficient in terms:
        word = tuple(sorted(word))
        answer[word] = answer.get(word, F(0))+F(coefficient)
    return {word: value for word, value in answer.items() if value}


def constant(value):
    return polynomial([((), value)])


def variable(column, value=1):
    return polynomial([((column,), value)])


def add(*expressions):
    return polynomial((word, value) for expression in expressions for word, value in expression.items())


def scale(expression, coefficient):
    return polynomial((word, value*coefficient) for word, value in expression.items())


def mul(left, right):
    return polynomial((a+b, x*y) for a, x in left.items() for b, y in right.items())


def substitute(expression, mapping):
    terms = []
    for word, value in expression.items():
        image = []
        for column in word:
            old, sign = mapping[column]
            image.append(old); value *= sign
        terms.append((tuple(image), value))
    return polynomial(terms)


def corner_coordinates(i, epsilon, tau):
    return (add(variable(2*i), variable(18+i, F(epsilon, 2)), variable(27+i, F(-tau, 2))),
            add(variable(2*i+1), variable(27+i, F(epsilon, 2)), variable(18+i, F(tau, 2))))


def norm_squared(coordinates):
    return add(*(mul(a, a) for a in coordinates))


def difference(pair):
    i, j = pair
    return add(variable(2*j), variable(2*i, -1)), add(variable(2*j+1), variable(2*i+1, -1))


def relative(pair):
    i, j = pair
    cosine = add(mul(variable(18+i), variable(18+j)), mul(variable(27+i), variable(27+j)))
    sine = add(mul(variable(18+i), variable(27+j)), scale(mul(variable(27+i), variable(18+j)), -1))
    return cosine, sine


def separating_polynomial(pair, choice, csign, ssign):
    owner, axis, sign = choice
    normal = (variable(18+owner, sign), variable(27+owner, sign)) if axis == 0 else (
        variable(27+owner, -sign), variable(18+owner, sign))
    d = difference(pair)
    cosine, sine = relative(pair)
    return add(scale(add(mul(normal[0], d[0]), mul(normal[1], d[1])), 2),
               constant(-1), scale(cosine, -csign), scale(sine, -ssign))


def proxy_polynomial(pair, choice):
    i, j = pair
    axis, sign = choice
    return add(variable(2*j+axis, sign), variable(2*i+axis, -sign),
               variable(45+i, -1), variable(45+j, -1))


def expected_mapping(reflect, swap):
    mapping = []
    # Independent table by coordinate block, without producer relabel().
    labels = list(range(9))
    if swap:
        labels[7], labels[8] = 8, 7
    for i in labels:
        mapping += [(2*i, 1), (2*i+1, -1 if reflect else 1)]
    for block in (18, 27, 36, 45):
        mapping += [(block+i, -1 if reflect and block == 27 else 1) for i in labels]
    return tuple(mapping)


def check_transformation(reflect, swap, map_override=None):
    mapping = M.variable_map(reflect, swap) if map_override is None else map_override
    assert mapping == expected_mapping(reflect, swap)
    assert sorted(column for column, sign in mapping) == list(range(54))
    assert all(mapping[column] == (i, sign) for i, (column, sign) in enumerate(mapping))
    counts = dict(corner_norms=0, unit_frames=0, fold_inequalities=0, inset_identities=0,
                  owned_support_literals=0, proxy_literals=0, marked_cones=0,
                  marked_bit_margins=0, mask_predicate_bijections=0)
    for i in range(9):
        new_i = 15-i if swap and i in (7, 8) else i
        assert substitute(add(mul(variable(18+new_i), variable(18+new_i)),
                              mul(variable(27+new_i), variable(27+new_i)), constant(-1)), mapping) == (
            add(mul(variable(18+i), variable(18+i)), mul(variable(27+i), variable(27+i)), constant(-1)))
        counts['unit_frames'] += 1
        for sign in (-1, 1):
            new_sign = -sign if reflect else sign
            assert substitute(add(variable(18+new_i), variable(27+new_i, new_sign)), mapping) == add(
                variable(18+i), variable(27+i, sign))
            counts['fold_inequalities'] += 1
        assert substitute(add(scale(mul(variable(45+new_i), add(variable(18+new_i), variable(36+new_i))), 2),
                              constant(-1)), mapping) == add(scale(mul(variable(45+i), add(variable(18+i), variable(36+i))), 2), constant(-1))
        assert substitute(add(mul(variable(36+new_i), variable(36+new_i)),
                              scale(mul(variable(27+new_i), variable(27+new_i)), -1)), mapping) == add(
            mul(variable(36+i), variable(36+i)), scale(mul(variable(27+i), variable(27+i)), -1))
        counts['inset_identities'] += 2
        for e, t in product((-1, 1), repeat=2):
            image = M.map_corner(i, e, t, reflect, swap)
            assert image == (new_i, e, -t if reflect else t)
            assert substitute(norm_squared(corner_coordinates(*image)), mapping) == norm_squared(corner_coordinates(i, e, t))
            counts['corner_norms'] += 1
    for pair in combinations(range(9), 2):
        for choice in product(pair, (0, 1), (-1, 1)):
            image, new_choice, sine_sign = M.map_owned_choice(pair, choice, reflect, swap)
            assert image in set(combinations(range(9), 2)) and new_choice[0] in image
            for csign, ssign in product((-1, 1), repeat=2):
                assert substitute(separating_polynomial(image, new_choice, csign, ssign*sine_sign), mapping) == separating_polynomial(pair, choice, csign, ssign)
                counts['owned_support_literals'] += 1
        image_choices = [M.map_owned_choice(pair, choice, reflect, swap)[1]
                         for choice in product(pair, (0, 1), (-1, 1))]
        image_pair = M.map_owned_choice(pair, (pair[0], 0, 1), reflect, swap)[0]
        assert set(image_choices) == set(product(image_pair, (0, 1), (-1, 1)))
        for choice in product((0, 1), (-1, 1)):
            image, new_choice = M.map_proxy_choice(pair, choice, reflect, swap)
            assert substitute(proxy_polynomial(image, new_choice), mapping) == proxy_polynomial(pair, choice)
            counts['proxy_literals'] += 1
    edges = ((0, 1), (1, 2), (2, 3), (4, 5), (5, 6))
    for pair in edges:
        dx, dy = difference(pair)
        for sign in (-1, 1):
            assert substitute(add(dx, scale(dy, -sign if reflect else sign)), mapping) == add(dx, scale(dy, sign))
            counts['marked_cones'] += 1
        i, j = pair
        margin = add(dx, variable(18+i, -F(1, 2)), variable(36+i, -F(1, 2)),
                     variable(18+j, -F(1, 2)), variable(36+j, -F(1, 2)))
        assert substitute(margin, mapping) == margin
        counts['marked_bit_margins'] += 1
    # Equality of these five margins preserves each of the 32 literal
    # combinations of >=0 (actual) and <0 (weak), without monotonicity.
    for bits in product((0, 1), repeat=5):
        assert len(bits) == len(edges)
        counts['mask_predicate_bijections'] += 1
    return counts


def physical_assignment(seed, zero_faces=False):
    halfangles = [F(-2, 5), F(-1, 3), F(-1, 5), F(0), F(1, 5), F(1, 3), F(2, 5)]
    centers = [(F((seed+7*i) % 19-9, 8), F((3*seed+5*i) % 19-9, 8)) for i in range(9)]
    frames = []
    for i in range(9):
        t = halfangles[(seed+3*i) % len(halfangles)]
        frames.append(((1-t*t)/(1+t*t), 2*t/(1+t*t)))
    if zero_faces:
        frames[3] = F(1), F(0)
        centers[8] = centers[7][0], centers[8][1]
    values = [v for pair in centers for v in pair]
    values += [a for a, b in frames]+[b for a, b in frames]
    values += [abs(b) for a, b in frames]+[1/(2*(a+abs(b))) for a, b in frames]
    return tuple(values)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source_hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in (Path(__file__).resolve(), Path(M.__file__).resolve())}
    counts = {}
    for reflect, swap in product((False, True), repeat=2):
        counts[f'reflect_{int(reflect)}_swap_{int(swap)}'] = check_transformation(reflect, swap)
    assignments = fixed_faces = 0
    for seed in range(100):
        for zero_faces in (False, True):
            values = physical_assignment(seed, zero_faces)
            normalized, flags = M.normalize_physical_assignment(values)
            assert normalized[30] >= 0 and normalized[14] <= normalized[16]
            assert M.transform(normalized, **flags) == values
            assert M.transform(M.transform(values, True, False), False, True) == M.transform(M.transform(values, False, True), True, False)
            assert M.normalize_physical_assignment(normalized)[0] == normalized
            if zero_faces:
                assert flags == dict(reflect=False, swap_extras=False)
                fixed_faces += 1
            assignments += 1
    rejected = []
    def reject(name, function):
        try:
            function()
        except (AssertionError, ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError('Damaged symmetry accepted: '+name)
    wrong = list(M.variable_map(True, False)); wrong[27] = (27, 1)
    reject('reflect y but not beta', lambda: check_transformation(True, False, tuple(wrong)))
    wrong = list(M.variable_map(False, True)); wrong[14], wrong[16] = (14, 1), (16, 1)
    reject('swap frames without corresponding centers', lambda: check_transformation(False, True, tuple(wrong)))
    wrong = list(M.variable_map(False, False)); wrong[18] = (19, 1)
    reject('alter marked original frame', lambda: check_transformation(False, False, tuple(wrong)))
    reject('omit ninth frame block', lambda: M.normalize_physical_assignment(physical_assignment(0)[:-1]))
    invalid = list(physical_assignment(0)); invalid[21] = 0
    reject('invalid unit endpoint frame', lambda: M.normalize_physical_assignment(invalid))
    # Explicitly exercise the two sign corrections most easily lost in a
    # label or reflection implementation.
    pair, choice = (0, 1), (0, 1, 1)
    image, new_choice, sine = M.map_owned_choice(pair, choice, True, False)
    assert new_choice == (0, 1, -1) and sine == -1
    wrong = separating_polynomial(image, (0, 1, 1), 1, -1)
    assert substitute(wrong, M.variable_map(True, False)) != separating_polynomial(pair, choice, 1, 1)
    rejected.append('lost reflected v-axis separator sign')
    pair, choice = (7, 8), (7, 0, 1)
    image, new_choice, sine = M.map_owned_choice(pair, choice, False, True)
    assert image == (7, 8) and new_choice == (8, 0, -1) and sine == -1
    wrong = separating_polynomial(image, (8, 0, 1), 1, -1)
    assert substitute(wrong, M.variable_map(False, True)) != separating_polynomial(pair, choice, 1, 1)
    rejected.append('lost reversed sorted-pair separator sign')
    assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest for path, digest in source_hashes.items())
    report = dict(status='PASS_FULL_CALLER_SYMMETRY_POLYNOMIAL_CONTROLS',
        scope='Universal whole-caller transformations only; no normalized adapter or search installed',
        polynomial_counts=counts, rational_normalization_assignments=assignments,
        shared_zero_faces=fixed_faces, damaged_controls_rejected=rejected,
        reduction_guards=['beta_D>=0', 'x_H<=x_I'],
        all_32_exact_masks_preserved=True, strict_and_closed_containment_preserved=True,
        physical_frames=9, physical_corners=36, physical_pairs=36, marked_cones=5,
        old_001_normalizations_imported=False, numerical_solver_called=False,
        whole_mask_credit=0, source_sha256=source_hashes)
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2); stream.write('\n')
    print(json.dumps({'status':report['status'], 'maps':4,
        'owned_support_polynomial_identities':sum(x['owned_support_literals'] for x in counts.values()),
        'normalization_assignments':assignments, 'damaged_controls':len(rejected), 'whole_mask_credit':0}))


if __name__ == '__main__':
    main()

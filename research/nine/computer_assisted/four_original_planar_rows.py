"""Planar four-center energy restrictions for physical unit squares.

For four points with every mutual distance at least one,
sum_{i<j} |c_i-c_j|^2 >= 8. Unit-square incircles provide the premise.
The theorem is independent of frame choices and the mask.
"""
from fractions import Fraction as Q
from itertools import combinations, product

def linear_rows(differences, diagonal=None, all_combinations=True):
    """Upper secants of each squared distance give affine necessary rows."""
    diagonal = diagonal or {}
    rows = []
    for quad in combinations(range(9), 4):
        pairs = list(combinations(quad, 2))
        options = [(0, 1) if pair in diagonal else (0,) for pair in pairs]
        if not all_combinations:
            options = [(0,) for pair in pairs]
        for codes in product(*options):
            co, rhs = {}, Q(-8)
            for (i, j), code in zip(pairs, codes):
                bounds = diagonal[i, j] if code else differences[i, j]
                factor = Q(1, 2) if code else Q(1)
                for axis, (lo, hi) in enumerate(bounds):
                    expr = {2*j: Q(1), 2*i: Q(-1)} if code else {2*j+axis: Q(1), 2*i+axis: Q(-1)}
                    if code:
                        sg = 1 if axis == 0 else -1
                        expr[2*j+1], expr[2*i+1] = Q(sg), Q(-sg)
                    for k, v in expr.items():
                        co[k] = co.get(k, Q(0)) - factor*(lo+hi)*v
                    rhs -= factor*lo*hi
            name = 'four_center_energy_' + '_'.join(map(str, quad)) + '_' + ''.join(map(str, codes))
            rows.append((tuple((k, v) for k, v in sorted(co.items()) if v), rhs, name))
    return rows

def moment_rows(L):
    """Exact quadratic restrictions, before any numerical square cuts."""
    rows = []
    for quad in combinations(range(9), 4):
        co = {}
        for i, j in combinations(quad, 2):
            for axis in (0, 1):
                L.multiply(co, L.delta(i, j, axis), L.delta(i, j, axis), -1)
        rows.append(L.clean(co, -8, 'four_center_energy_moment_' + '_'.join(map(str, quad))))
    return rows

def matchings(quad):
    """The exhaustive three-alternative planar matching cover."""
    a, b, c, d = quad
    return (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c)))

def matching_linear_rows(quad, choice, differences, diagonal=None):
    """Necessary rows on one chosen matching's squared-distance sum >=4.

    These rows are CONDITIONAL. A caller must cover all three choices.
    They must never be installed unconditionally on an original parent.
    """
    diagonal = diagonal or {}
    assert len(quad) == 4 and len(set(quad)) == 4 and tuple(sorted(quad)) == tuple(quad)
    assert choice in (0, 1, 2)
    pairs = matchings(quad)[choice]
    rows = []
    options = [(0, 1) if pair in diagonal else (0,) for pair in pairs]
    for codes in product(*options):
        co, rhs = {}, Q(-4)
        for (i, j), code in zip(pairs, codes):
            bounds = diagonal[i, j] if code else differences[i, j]
            factor = Q(1, 2) if code else Q(1)
            for axis, (lo, hi) in enumerate(bounds):
                expr = {2*j: Q(1), 2*i: Q(-1)} if code else {2*j+axis: Q(1), 2*i+axis: Q(-1)}
                if code:
                    sg = 1 if axis == 0 else -1
                    expr[2*j+1], expr[2*i+1] = Q(sg), Q(-sg)
                for k, v in expr.items():
                    co[k] = co.get(k, Q(0)) - factor*(lo+hi)*v
                rhs -= factor*lo*hi
        name = 'four_center_matching_' + '_'.join(map(str, quad)) + '_' + str(choice) + '_' + ''.join(map(str, codes))
        rows.append((tuple((k, v) for k, v in sorted(co.items()) if v), rhs, name))
    return rows

def matching_moment_row(L, quad, choice):
    """A conditional exact quadratic matching row; cover all three choices."""
    co = {}
    for i, j in matchings(quad)[choice]:
        for axis in (0, 1):
            L.multiply(co, L.delta(i, j, axis), L.delta(i, j, axis), -1)
    return L.clean(co, -4, 'four_center_matching_moment_' + '_'.join(map(str, quad)) + '_' + str(choice))

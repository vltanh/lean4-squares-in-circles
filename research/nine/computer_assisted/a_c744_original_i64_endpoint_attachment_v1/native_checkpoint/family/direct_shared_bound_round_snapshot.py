"""Copy proved shared-source affine endpoints through ordinary bound certificates.

No LP is solved. The unchanged diagonal replay core sees standard positive
integer multipliers, zero residual and its usual grid-rounded endpoints.
The caller must provide the actual engine and domain-bound context. Only
explicitly selected shared-source row prefixes may supply deductions.
"""
from fractions import Fraction as F


def canonical(coefficients):
    result = {}
    for index, value in coefficients:
        result[index] = result.get(index, F(0)) + F(value)
    return tuple((index, value) for index, value in sorted(result.items()) if value)


def bound_round(engine, context, state, source_prefixes, eps=F(1, 2000)):
    assert isinstance(source_prefixes, tuple) and source_prefixes
    assert all(isinstance(prefix, str) and prefix for prefix in source_prefixes)
    assert engine.SCALE == 1 << 40 and engine.GRID == 1 << 20
    # Domain applicability and all original geometry are checked by the
    # existing context on the untouched caller before any bound is copied.
    rows, bounds, propagated, early = context.collect(state)
    if early is not None:
        return None, None, early
    candidates = {}
    for index, (coefficients, rhs, name) in enumerate(rows):
        if not name.startswith(source_prefixes):
            continue
        key = canonical(coefficients)
        item = (F(rhs), index)
        if key not in candidates or item < candidates[key]:
            candidates[key] = item
    targets = []
    for index, (lo, hi) in enumerate(propagated['positions'] + propagated['scalar']):
        for sign in (-1, 1):
            targets.append(('scalar', index, sign, [(index, sign)], hi if sign == 1 else -lo))
    for (i, j), intervals in sorted(propagated['differences'].items()):
        for axis, (lo, hi) in enumerate(intervals):
            for sign in (-1, 1):
                targets.append(('difference', (i, j, axis), sign,
                    [(2*j+axis, sign), (2*i+axis, -sign)], hi if sign == 1 else -lo))
    for (i, j), intervals in sorted(propagated['diagonal'].items()):
        for axis, (lo, hi) in enumerate(intervals):
            sy = 1 if axis == 0 else -1
            for sign in (-1, 1):
                targets.append(('diagonal', (i, j, axis), sign,
                    [(2*j, sign), (2*i, -sign), (2*j+1, sign*sy), (2*i+1, -sign*sy)],
                    hi if sign == 1 else -lo))
    positions = [list(ab) for ab in propagated['positions']]
    scalar = [list(ab) for ab in propagated['scalar']]
    differences = {pair: [list(ab) for ab in intervals]
        for pair, intervals in propagated['differences'].items()}
    diagonal = {pair: [list(ab) for ab in intervals]
        for pair, intervals in propagated['diagonal'].items()}
    proposals, used = [], set()
    for kind, key, sign, objective, old in targets:
        candidate = candidates.get(canonical(objective))
        if candidate is None:
            continue
        rhs, index = candidate
        upper = engine.ceil_grid(rhs)
        if old - upper < eps:
            continue
        assert canonical(rows[index][0]) == canonical(objective)
        proposals.append(dict(kind=kind, key=list(key) if isinstance(key, tuple) else key,
            sign=sign, objective=[list(term) for term in objective], upper=str(upper),
            proved_upper=str(rhs), weights=[[index, engine.SCALE]], summed_rhs=str(rhs),
            residual_coefficients=[], residual_correction='0'))
        used.add(index)
        if kind == 'scalar':
            target = positions[key] if key < 18 else scalar[key-18]
        else:
            target = (differences if kind == 'difference' else diagonal)[key[0], key[1]][key[2]]
        if sign == 1:
            target[1] = min(target[1], upper)
        else:
            target[0] = max(target[0], -upper)
    record = dict(before=engine.stateview(state), propagated=engine.stateview(propagated),
        proposals=proposals, printed_rows=engine.printed(rows, used),
        absolute_variable_bounds=list(map(str, bounds)), numeric_failures=0,
        direct_shared_affine_copy=True, numerical_solves=0)
    terminal = None
    for index, (lo, hi) in enumerate(positions + scalar):
        if lo > hi:
            terminal = dict(kind='proved_empty_scalar', index=index, lower=str(lo), upper=str(hi))
            break
    if terminal is None:
        for pair, intervals in differences.items():
            for axis, (lo, hi) in enumerate(intervals):
                if lo > hi:
                    terminal = dict(kind='proved_empty_difference', pair=list(pair), axis=axis,
                        lower=str(lo), upper=str(hi))
                    break
    if terminal is None:
        for pair, intervals in diagonal.items():
            for axis, (lo, hi) in enumerate(intervals):
                if lo > hi:
                    terminal = dict(kind='proved_empty_diagonal', pair=list(pair), axis=axis,
                        lower=str(lo), upper=str(hi))
                    break
    if terminal is not None:
        return None, record, terminal
    positions, scalar = tuple(map(tuple, positions)), tuple(map(tuple, scalar))
    differences = {pair: tuple(map(tuple, intervals)) for pair, intervals in differences.items()}
    diagonal = {pair: tuple(map(tuple, intervals)) for pair, intervals in diagonal.items()}
    angles, term, identities = context.R.infer_angles(state['angles'], scalar)
    record['physical_frame_inferences'] = identities
    if term:
        return None, record, dict(kind='proved_frame_contradiction', label=term)
    analytic = context.K.analytic(angles)
    scalar = tuple((max(a, c), min(b, d)) for (a, b), (c, d) in zip(scalar, analytic))
    for index, (lo, hi) in enumerate(scalar):
        if lo > hi:
            return None, record, dict(kind='proved_empty_analytic_frame', index=index,
                lower=str(lo), upper=str(hi))
    after = dict(state, positions=positions, scalar=scalar, differences=differences,
        diagonal=diagonal, angles=angles)
    record['after'] = engine.stateview(after)
    if not proposals and record['after'] == record['before']:
        return state, None, None
    return after, record, None

"""Cheap discovery-only screen for a solver-free shared-bound round.

False means no listed source endpoint improves the current explicit box by
the normal threshold. It never modifies a state or authorizes a premise.
The real round still obtains and validates rows through the unchanged
domain-bound context before applying any deduction.
"""
from fractions import Fraction as F
from direct_shared_bound_round import canonical


def may_improve(engine, state, source_rows, source_prefixes, eps=F(1, 2000)):
    assert isinstance(source_prefixes, tuple) and source_prefixes
    limits = {}
    for index, (lo, hi) in enumerate(state['positions'] + state['scalar']):
        limits[((index, F(1)),)] = F(hi)
        limits[((index, F(-1)),)] = -F(lo)
    for kind in ('differences', 'diagonal'):
        for (i, j), intervals in state.get(kind, {}).items():
            for axis, (lo, hi) in enumerate(intervals):
                for sign in (-1, 1):
                    if kind == 'differences':
                        objective = [(2*j+axis, sign), (2*i+axis, -sign)]
                    else:
                        sy = 1 if axis == 0 else -1
                        objective = [(2*j, sign), (2*i, -sign),
                            (2*j+1, sign*sy), (2*i+1, -sign*sy)]
                    limits[canonical(objective)] = F(hi) if sign == 1 else -F(lo)
    for coefficients, rhs, name in source_rows:
        if not name.startswith(source_prefixes):
            continue
        objective = canonical(coefficients)
        if objective in limits:
            if limits[objective] - engine.ceil_grid(F(rhs)) >= eps:
                return True
        elif len(objective) in (2, 4) and all(index < 18 for index, _ in objective):
            # Missing pair boxes will be reconstructed by ordinary physical
            # propagation. Conservatively permit the real direct-round check.
            return True
    return False

"""Literal I=H or I=I application of the accepted seven-original theorem."""
from pathlib import Path
import hashlib
import accepted_actual_ab_guard as SOURCE

SOURCE_SHA = '3a965bdcc8fc0f4de55fc5e3a5fef945f584710fa5ff6c339de44abcea640c19'
assert hashlib.sha256(Path(SOURCE.__file__).read_bytes()).hexdigest() == SOURCE_SHA


def evaluate(state, extra):
    assert type(extra) is int and extra in (7, 8)
    positions, angles, scalar, differences = SOURCE.unpack(state)
    permutation = tuple(range(9)) if extra == 8 else (0, 1, 2, 3, 4, 5, 6, 8, 7)
    temporary = dict(
        positions=tuple(positions[2 * permutation[i] + axis]
                        for i in range(9) for axis in (0, 1)),
        angles=tuple(angles[permutation[i]] for i in range(9)),
        scalar=tuple(scalar[offset + permutation[i]]
                     for offset in (0, 9, 18, 27) for i in range(9)),
        differences={})
    for i in range(9):
        for j in range(i + 1, 9):
            u, v = permutation[i], permutation[j]
            pair = tuple(sorted((u, v)))
            if pair in differences:
                temporary['differences'][i, j] = (
                    differences[pair] if u < v else
                    tuple((-hi, -lo) for lo, hi in differences[pair]))
    result = SOURCE.evaluate(temporary)
    result['status'] = ('PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD'
                        if result['status'] == 'PASS_ACTUAL_AB_TWO_LINK_TERMINAL_GUARD'
                        else 'GUARD_NOT_IMPLIED')
    result['B_extra_D_order_intervals'] = result.pop('BI_ID_order_intervals')
    result.update(extra_original=extra, physical_row=[0, 1, extra, 3],
                  selected_distinct_originals=[0, 1, extra, 3, 4, 5, 6],
                  literal_source_substitution={'I': 'H' if extra == 7 else 'I'})
    return result

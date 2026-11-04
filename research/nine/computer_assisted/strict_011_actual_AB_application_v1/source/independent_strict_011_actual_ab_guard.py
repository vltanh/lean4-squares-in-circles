"""Independent literal check of the strict-only fixed-mask application."""
from pathlib import Path
import hashlib
import independent_actual_ab_any_extra_guard as QUANTITATIVE

assert hashlib.sha256(Path(QUANTITATIVE.__file__).read_bytes()).hexdigest() == \
    'de0123de0071222760abdb8f942a3119ebbb0209574a1cfc22fb511d620b7fbf'


def evaluate(state, extra, *, mask, radius_mode):
    assert mask == '011/00'
    assert radius_mode == 'strict'
    literal = QUANTITATIVE.evaluate(state, extra)
    accepted = literal['status'] == 'PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD'
    assert literal.pop('all_nine_original_00100_ancestry_required') is True
    literal['status'] = ('PASS_CONDITIONAL_STRICT_01100_ACTUAL_AB_GUARD'
                         if accepted else 'GUARD_NOT_IMPLIED')
    literal['application'] = 'strict_01100_actual_AB_either_extra_v1'
    literal['mask'] = '011/00'
    literal['radius_mode'] = 'strict'
    literal['squared_radius_threshold'] = '1105/256'
    literal['strict_q_below_threshold_required'] = True
    literal['certified_all_nine_original_01100_ancestry_required'] = True
    literal['required_actual_links'] = [[0, 1], [4, 5], [5, 6]]
    literal['retained_strict_weak_links'] = [[1, 2], [2, 3]]
    literal['retained_original_center_cones'] = [[0, 1], [1, 2], [2, 3], [4, 5], [5, 6]]
    literal['all_36_original_corners_and_pairs_required'] = True
    literal['theorem_conclusion_used'] = 'q >= 1105/256'
    literal['closed_Q_excluded'] = False
    literal['current_00100_CD_equality_blocker_used'] = False
    literal['whole_mask_cover_checked'] = False
    return literal


def verify_literal(printed, state, *, mask, radius_mode):
    result = evaluate(state, printed['extra_original'], mask=mask, radius_mode=radius_mode)
    assert result['status'] == 'PASS_CONDITIONAL_STRICT_01100_ACTUAL_AB_GUARD'
    assert printed == result
    return result

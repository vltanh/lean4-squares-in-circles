"""Conditional strict-radius 011/00 application; no closed-Q conclusion."""
from pathlib import Path
import hashlib
import actual_ab_any_extra_guard as QUANTITATIVE

assert hashlib.sha256(Path(QUANTITATIVE.__file__).read_bytes()).hexdigest() == \
    '600763e67222e28451fed47e87c04283be1fa1869fbcf8cc8537e265e2727402'


def evaluate(state, extra, *, mask, radius_mode):
    assert mask == '011/00'
    assert radius_mode == 'strict'
    result = QUANTITATIVE.evaluate(state, extra)
    passed = result['status'] == 'PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD'
    # That field describes the previous caller's equality-blocker scope.
    # All numerical guard conditions precede it and are unchanged.
    assert result.pop('all_nine_original_00100_ancestry_required') is True
    result.update(
        status='PASS_CONDITIONAL_STRICT_01100_ACTUAL_AB_GUARD' if passed else 'GUARD_NOT_IMPLIED',
        application='strict_01100_actual_AB_either_extra_v1',
        mask=mask, radius_mode=radius_mode, squared_radius_threshold='1105/256',
        strict_q_below_threshold_required=True,
        certified_all_nine_original_01100_ancestry_required=True,
        required_actual_links=[[0, 1], [4, 5], [5, 6]],
        retained_strict_weak_links=[[1, 2], [2, 3]],
        retained_original_center_cones=[[0, 1], [1, 2], [2, 3], [4, 5], [5, 6]],
        all_36_original_corners_and_pairs_required=True,
        theorem_conclusion_used='q >= 1105/256',
        closed_Q_excluded=False,
        current_00100_CD_equality_blocker_used=False,
        whole_mask_cover_checked=False)
    return result

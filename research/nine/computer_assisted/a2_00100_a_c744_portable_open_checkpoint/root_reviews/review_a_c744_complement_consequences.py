#!/usr/bin/env python3
"""Root review controls for the three whole-original A consequences."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib, json, sys

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'ac_work/tree'
sys.path.insert(0, str(SOURCE))
import a_c744_complement_consequence_rows as PRODUCER
import independent_a_c744_complement_consequences as CHECKER

binding = CHECKER.verify_binding()
state = dict(id=CHECKER.TARGET, path=deepcopy(CHECKER.TARGET_PATH))
expected = [
    ((((2, F(1)), (16, F(-1)))), F(0)),
    ((((3, F(1)), (7, F(-1)))), F(3, 5)),
    ((((3, F(1)), (7, F(1)), (17, F(-2)))), F(3, 5)),
]
rows = PRODUCER.rows(state)
assert len(rows) == 3
rejected = 0
for literal, pair in zip(rows, expected):
    assert literal[:2] == pair
    CHECKER.verify_literal(literal, state)
    descendant = deepcopy(state)
    descendant['path'].append(['angle_cut', [8, '0'], 0])
    CHECKER.verify_literal(literal, descendant)
    coefficient, rhs, name = literal
    for damaged in [(coefficient, rhs + 1, name),
                    (coefficient, rhs, name + '0'),
                    (tuple((i, -v) for i, v in coefficient), rhs, name)]:
        try:
            CHECKER.verify_literal(damaged, state)
        except (AssertionError, ValueError):
            rejected += 1
        else:
            raise AssertionError('Damaged literal accepted')
    for key, value in [('id', 'wrong-original'), ('path', [])]:
        wrong = deepcopy(state)
        wrong[key] = value
        try:
            CHECKER.verify_literal(literal, wrong)
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError('Wrong original accepted')

base_path = SOURCE / 'A_C744_CONSEQUENCE_ATTACHMENT_BASE_REPLAY.json'
base = json.loads(base_path.read_text())
source = base['freshly_replayed_original_complement_consequences']
assert source['status'] == 'PASS_FRESH_COMPLEMENT_EXCLUSION_CONSEQUENCES'
assert source['binding_sha256'] == CHECKER.BINDING_SHA
assert source['excluded_components'] == [0, 2, 4]
report = dict(
    status='PASS_ROOT_PHYSICAL_AND_ATTACHMENT_REVIEW',
    binding_sha256=CHECKER.BINDING_SHA,
    original_id=CHECKER.TARGET,
    original_path=CHECKER.TARGET_PATH,
    literal_rows=3, valid_descendant_callers=3,
    damaged_literals_or_wrong_originals_rejected=rejected,
    source_report_sha256=hashlib.sha256(base_path.read_bytes()).hexdigest(),
    source_exclusions_freshly_replayed_by_attachment=True,
    root_repeated_source_arithmetic=False,
    first_weighted_consumer_replay_still_required=True,
    no_child_sat_choices_or_auxiliaries_transported=True,
    acyclic_old_checkers_bound_before_new_consequences=True,
    whole_original_or_mask_closure_claimed=False,
    lean_lake_ci_run=False,
)
out = Path(__file__).with_suffix('.json')
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))

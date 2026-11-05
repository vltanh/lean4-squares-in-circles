"""Cold checks of actual new literals and multiplier use, conditional on saved bounds.

The complete native prefix/old-row replay is recorded separately. This script
does not replace that replay or assert original-cell exclusion.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import gzip, json, sys
import independent_relative_support_chords as V

HERE = Path(__file__).resolve().parent
scope = json.loads((HERE/'WEIGHTED_SCOPE.json').read_text())
raw = gzip.decompress((HERE/'B7_CONDITIONAL_BOUND_RECORD.json.gz').read_bytes())
assert sha256(raw).hexdigest() == scope['record_sha256']
record = json.loads(raw)
assert record['status'] == 'OPEN' and len(record['rounds']) == 1
checked = uses = 0
for rr in record['rounds']:
    state = rr['propagated']
    scalar = tuple(tuple(map(F, ab)) for ab in state['scalar'])
    differences = {tuple(e['pair']): tuple(tuple(map(F, ab)) for ab in e['intervals'])
                   for e in state['differences']}
    new = set()
    for row in rr['printed_rows']:
        if not row['name'].startswith(V.PREFIX):
            continue
        literal = tuple((k, F(v)) for k, v in row['coefficients']), F(row['rhs']), row['name']
        assert V.verify_literal(literal, scalar, differences)
        assert row['index'] not in new
        new.add(row['index'])
        checked += 1
    used = set()
    for proposal in rr['proposals']:
        for index, weight in proposal['weights']:
            assert type(weight) is int and weight > 0
            if index in new:
                used.add(index)
                uses += 1
    assert used == new
assert checked == scope['new_family_rows_checked'] == 10
assert not any(x in sys.modules for x in ('numpy', 'scipy', 'highspy',
    'physical_relative_support_chords', 'owner_free_relative_support_snapshot'))
result = dict(status='PASS_ACTUAL_WEIGHTED_NEW_LITERALS_CONDITIONAL_ON_SAVED_BOUNDS',
              new_family_literals=checked, positive_multiplier_occurrences=uses,
              all_old_rows_and_original_ancestry_replayed_by_this_script=False,
              native_full_replay_evidence='NATIVE_PREFIX_REPLAY.json',
              producer_imported=False, numerical_library_imported=False,
              original_cells_closed=0, masks_closed=0)
(HERE/'WEIGHTED_NEW_ROWS_REPLAY.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))

#!/usr/bin/env python3
"""Freeze this newly prepared application packet; never overwrite a binding."""
if not __debug__:
    raise RuntimeError('Exact source freeze requires assertions.')
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import source_bindings as S

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def main():
    S.verify_dependencies()
    controls=json.loads((HERE/'FRESH_GUARD_CONTROLS.json').read_text())
    assert controls['status']=='PASS_NEW_STRICT011_UNIVERSAL021_HI_AND_C_GUARD_CONTROLS'
    assert controls['installed_in_tree_replay'] is False
    assert controls['original_cell_credit']==controls['whole_mask_credit']==0
    assert controls['fresh_scalar_replay_performed'] is False
    for name,expected in controls['source_hashes'].items():assert digest(HERE/name)==expected
    execution=json.loads((HERE/'CONTROL_EXECUTION.json').read_text())
    assert execution['observed_exit_code']==0
    assert execution['report_sha256']==digest(HERE/'FRESH_GUARD_CONTROLS.json')
    files={}
    for path in sorted(HERE.rglob('*')):
        assert not path.is_symlink()
        if not path.is_file():continue
        relative=str(path.relative_to(HERE))
        assert relative!='PREMISE_BINDINGS.json'
        assert path.suffix not in ('.pyc','.log')
        files[relative]=dict(bytes=path.stat().st_size,sha256=digest(path))
    value=dict(schema='new_strict011_universal021_HI_and_C_applications_v2',
        status='PREPARED_FRESH_CONTROLS_PASS_INDEPENDENT_REVIEW_PENDING_NO_INSTALLATION',
        mask='011/00',radius_mode='strict',middle_originals=[2,7,8],
        theorem='universal_actual_AB_two_link_v1',dependency_manifest_sha256=S.DEPENDENCY_SHA,
        foundation_manifest_sha256=controls['foundation_manifest_sha256'],
        controls_sha256=digest(HERE/'FRESH_GUARD_CONTROLS.json'),
        old_missing_control_receipts_reused=False,missing_search_records_recovered=False,
        actual_state_ancestry_and_fresh_scalar_required_at_use=True,
        installed_in_tree_replay=False,original_cell_credit=0,whole_mask_credit=0,
        files=files)
    target=HERE/'PREMISE_BINDINGS.json'
    with target.open('x') as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
    expected=digest(target)
    assert S.verify_binding(expected)==value
    print(json.dumps(dict(status=value['status'],files=len(files),bytes=sum(v['bytes'] for v in files.values()),binding_sha256=expected)))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Freeze new source-layer preparation after its fresh controls."""
if not __debug__:
    raise RuntimeError('Exact source freeze requires assertions.')
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import layer_dependencies as D
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def main():
    D.verify_family()
    controls=json.loads((HERE/'FRESH_LAYER_CONTROLS.json').read_text())
    assert controls['status']=='PASS_NEW_STRICT011_FOUR_PRODUCT_SAME_STATE_LAYER_CONTROLS'
    assert controls['actual_weighted_use_gate_passed']is False and controls['installed_in_tree_replay']is False
    assert controls['original_cell_credit']==controls['whole_mask_credit']==0
    for name,expected in controls['source_hashes'].items():assert digest(HERE/name)==expected
    execution=json.loads((HERE/'CONTROL_EXECUTION.json').read_text())
    assert execution['observed_exit_code']==0 and execution['report_sha256']==digest(HERE/'FRESH_LAYER_CONTROLS.json')
    inventory={}
    for path in sorted(HERE.rglob('*')):
        assert not path.is_symlink()
        if not path.is_file():continue
        name=str(path.relative_to(HERE));assert name!='PREMISE_BINDINGS.json'
        assert path.suffix not in('.log','.pyc')
        inventory[name]=dict(bytes=path.stat().st_size,sha256=digest(path))
    binding=dict(schema='new_strict011_four_product_same_state_layer_v2',
        status='PREPARED_FRESH_CONTROLS_PASS_INDEPENDENT_REVIEW_PENDING_NO_INSTALLATION',
        mask='011/00',radius_mode='strict',original_variables=54,new_auxiliary_variables=0,
        accepted_family_manifest_sha256=D.FAMILY,foundation_manifest_sha256=D.FOUNDATION,
        source_frame_and_caller_checks_unchanged=True,accepted_literal_decoder_unchanged=True,
        actual_weighted_use_gate_passed=False,installed_in_tree_replay=False,
        old_missing_controls_reused=False,original_cell_credit=0,whole_mask_credit=0,
        files=inventory)
    target=HERE/'PREMISE_BINDINGS.json'
    with target.open('x')as stream:json.dump(binding,stream,indent=2,sort_keys=True);stream.write('\n')
    expected=digest(target);assert D.verify_layer_binding(expected)==binding
    print(json.dumps(dict(status=binding['status'],files=len(inventory),
                         bytes=sum(v['bytes']for v in inventory.values()),binding_sha256=expected)))
if __name__=='__main__':main()

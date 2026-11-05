"""Final immutable inventory of the proof infrastructure; no solver or credit."""
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
W=HERE.parents[1]

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

origin=json.loads((HERE/'SOURCE_RECONSTRUCTION.json').read_text())
inputs=[
    (W/'b_work/independent_physical_sat_replay.py','b_work/independent_physical_sat_replay.py',
     '1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc'),
    (W/'b_work/independent_physical_proxy_cover.py','b_work/independent_physical_proxy_cover.py',
     '3b46b8a966c712e23894ae4cd7964355730f2bfe3c58a04871ade9d35ddf1277')]
for control in origin['restored_committed_controls']:
    source=Path(control['target'])
    inputs.append((source,str(source.relative_to(W)),control['sha256']))
deps={}
for source,relative,expected in inputs:
    assert digest(source)==expected
    target=HERE/'dependencies/workspace'/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as f:
        f.write(source.read_bytes())
    assert digest(target)==expected
    deps[relative]=expected
reports={}
for rel,status in (
    ('strict_011_full_root_v2/FRESH_ROOT_CONTROLS.json','PASS_FRESH_STRICT011_ROOT_LITERAL_AND_COVER_CONTROLS'),
    ('full_mask_symmetries_v1/FRESH_SYMMETRY_CONTROLS.json','PASS_FULL_CALLER_SYMMETRY_POLYNOMIAL_CONTROLS'),
    ('strict_011_complete_cover_v2/fresh_controls/COMPLETE_TREE_CONTROLS.json','PASS_FRESH_STRICT011_COMPLETE_TREE_CONTROLS'),
    ('strict_011_representative_root_v1/FRESH_REPRESENTATIVE_CONTROLS.json','PASS_REPRESENTATIVE_STRICT011_ROOT_AND_LITERAL_CONTROLS'),
    ('strict_011_representative_cover_v1/fresh_controls/COMPLETE_TREE_CONTROLS.json','PASS_FRESH_STRICT011_COMPLETE_TREE_CONTROLS')):
    r=json.loads((HERE/rel).read_text())
    assert r['status']==status and r['whole_mask_credit']==0
    reports[rel]=dict(sha256=digest(HERE/rel),status=status,observed_process_exit=0)
files={}
for p in sorted(HERE.rglob('*')):
    if p.is_file() and p.suffix!='.log':
        assert not p.is_symlink()
        files[str(p.relative_to(HERE))]=dict(bytes=p.stat().st_size,sha256=digest(p))
assert 'CHECKPOINT_MANIFEST.json' not in files
result=dict(status='FROZEN_REBUILT_STRICT011_FOUNDATIONS_AND_REPRESENTATIVE_ROOT_NO_CLOSURE',
    schema='rebuilt_strict011_foundations_checkpoint_v3',files=files,
    source_reconstruction_sha256=digest(HERE/'SOURCE_RECONSTRUCTION.json'),
    fresh_control_reports=reports,portable_exact_dependencies=deps,
    lost_JSON_binding_recovery_claimed=False,lost_numerical_suffix_reconstruction_claimed=False,
    base_mathematical_source_bytes_unchanged=True,whole_target_mask='011/00',radius_mode='strict',
    physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
    representative_guard_scope='Separate root through whole-caller existence equivalence',
    conditional_terminals_installed=False,numerical_solver_called=False,
    original_cell_credit=0,whole_mask_credit=0)
with (HERE/'CHECKPOINT_MANIFEST.json').open('x') as f:
    json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(dict(status=result['status'],files=len(files),bytes=sum(x['bytes'] for x in files.values()),
    manifest_sha256=digest(HERE/'CHECKPOINT_MANIFEST.json'))))

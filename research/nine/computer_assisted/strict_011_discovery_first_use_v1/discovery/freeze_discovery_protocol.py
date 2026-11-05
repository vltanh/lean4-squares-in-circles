"""Freeze prepared commands; does not launch an optimization process."""
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
W=HERE.parents[1]
CHECKPOINT=W/'global_work/strict_011_rebuilt_v3'

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')

driver=HERE/'fresh_strict011_discovery_singlethread_v2.py'
assert digest(driver)=='58a85d7976aff42bbda10137f0c951985c674e220568f93d9244dfdf1b92275e'
assert digest(CHECKPOINT/'CHECKPOINT_MANIFEST.json')=='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
controls=HERE/'exact_controls/DISCOVERY_CONTROLS.json'
assert digest(controls)=='787961ad66de7550e1d12ae8dec85f465242f09142725f998e53c9273b3eacc1'
unions=HERE/'store_union_controls/STORE_UNION_CONTROLS.json'
assert digest(unions)=='8f7a3f909f307d80c6823fbee14eed28be66a86bbe8a7c60b6ddf9723db6ae93'
for path in (controls,unions):
    assert json.loads(path.read_text())['actual_numerical_solver_called'] is False
options=HERE/'NUMERIC_OPTIONS_NO_SOLVE_PREFLIGHT.json'
o=json.loads(options.read_text())
assert o['status']=='PASS_INSTALLED_HIGHS_OPTION_FORWARDING_AND_READBACK_NO_SOLVE'
assert o['option_validation']['threads']['read_back']==1
assert o['actual_optimization_function_called'] is False and o['warnings_suppressed'] is False
seed=CHECKPOINT/'strict_011_representative_cover_v1/fresh_controls/fresh_root_open/manifest.json'
first=W/'repo/research/nine/.runs/strict011_representative_first_real_phase_v1'
second=W/'repo/research/nine/.runs/strict011_representative_bounded_v1'
assert not first.exists() and not second.exists()
assert not Path(str(first)+'.log').exists() and not Path(str(second)+'.log').exists()
base=['python','-B','-u',str(driver),'--checkpoint',str(CHECKPOINT),'--input',str(seed)]
protocol=dict(status='READY_FOR_ROOT_SOURCE_REVIEW_AND_NUMERICAL_SLOT_NOT_LAUNCHED',
    root_id='full-strict-01100-representative-root-v1',mask='011/00',radius_mode='strict',
    checkpoint_manifest_sha256=digest(CHECKPOINT/'CHECKPOINT_MANIFEST.json'),
    source_seed_manifest_sha256=digest(seed),driver_sha256=digest(driver),
    environment={k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS')},
    actual_backend_thread_option=1,warning_suppression=False,
    first_actual_gate=dict(command=base+['--output',str(first),'--pilot-ab-negative','--rounds','0',
        '--objectives','54','--max-nodes','5','--max-depth','1','--lp-seconds','10'],
        log=str(first)+'.log',output=str(first),
        required_exact_result=dict(nodes=5,excluded_leaves=1,open_leaves=3,whole_mask_proved=False),
        actual_numerical_backend_required=True,manual_dual_control_is_not_this_gate=True),
    subsequent_bounded_run=dict(command=base+['--output',str(second),'--rounds','1','--objectives','54',
        '--max-nodes','33','--max-depth','8','--lp-seconds','10'],log=str(second)+'.log',output=str(second),
        requires_prior_actual_gate_pass_and_root_launch=True,all_unfinished_domains_retained=True),
    exact_control_receipt_sha256=digest(controls),store_union_receipt_sha256=digest(unions),
    option_preflight_sha256=digest(options),actual_numerical_solve_called=False,
    original_cell_credit=0,whole_mask_credit=0)
write(HERE/'FIRST_NUMERICAL_PROTOCOL.json',protocol)
files={str(p.relative_to(HERE)):dict(bytes=p.stat().st_size,sha256=digest(p))
       for p in sorted(HERE.rglob('*')) if p.is_file()}
assert 'SOURCE_FREEZE.json' not in files
freeze=dict(status='FROZEN_FRESH_STRICT011_STANDALONE_DISCOVERY_AND_EXACT_CONTROLS_NO_LP_RUN',
    files=files,driver_to_run='fresh_strict011_discovery_singlethread_v2.py',
    mathematical_and_storage_kernel_controlled_in_v1=True,
    v2_only_change='Explicit threads=1, full AST equality after removal of that option',
    required_checkpoint_sha256=protocol['checkpoint_manifest_sha256'],
    root_review_and_slot_required_before_first_solve=True,
    original_cell_credit=0,whole_mask_credit=0)
write(HERE/'SOURCE_FREEZE.json',freeze)
print(json.dumps(dict(status=freeze['status'],files=len(files),bytes=sum(v['bytes'] for v in files.values()),
    freeze_sha256=digest(HERE/'SOURCE_FREEZE.json'),protocol_sha256=digest(HERE/'FIRST_NUMERICAL_PROTOCOL.json'))))

#!/usr/bin/env python3
"""Freeze the no-solver preparation and write an explicitly held pilot argv."""
if not __debug__:
    raise RuntimeError('Preparation freezing requires exact assertions.')
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORKSPACE=HERE.parents[1]
BASE='58a85d7976aff42bbda10137f0c951985c674e220568f93d9244dfdf1b92275e'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x')as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def main():
    assert not(HERE/'SOURCE_FREEZE.json').exists()
    assert not(HERE/'HELD_PILOT_LAUNCH.json').exists()
    controls=json.loads((HERE/'preparation_controls/PREPARATION_CONTROLS.json').read_text())
    assert controls['status']=='PASS_PREPARED_STRENGTHENED_DISCOVERY_CONTROLS_NO_SOLVER'
    assert controls['real_numerical_backend_constructed']is False
    assert controls['actual_positive_corner_weight_gate_passed']is False
    assert controls['successful_true_guard_gate_passed']is False
    for name,expected in controls['source_hashes'].items():assert digest(HERE/name)==expected
    assert digest(HERE/'accepted_base_discovery.py')==BASE
    options=json.loads((HERE/'PILOT_OPTIONS_NO_SOLVE.json').read_text())
    assert options['status']=='PASS_INSTALLED_HIGHS_OPTION_FORWARDING_AND_READBACK_NO_SOLVE'
    assert options['actual_optimization_function_called']is False
    assert options['option_validation']['time_limit']['read_back']==2.0
    assert options['option_validation']['threads']['read_back']==1
    seed=HERE/'fresh_zero_round_seed'
    seed_report=json.loads((seed/'ZERO_ROUND_EXACT_REPLAY.json').read_text())
    source_seed=json.loads((HERE/'preparation_controls/complete_store_cover/INPUT_EXACT_REPLAY.json').read_text())
    for report in(seed_report,source_seed):
        assert(report['nodes'],report['excluded_leaves'],report['open_leaves'])==(1,0,1)
        assert report['exact_totals']==dict(rounds=0,deductions=0,printed_rows_checked=0)
        assert report['manifest_sha256']==digest(seed/'manifest.json')
        assert report['root_id']=='full-strict-01100-representative-root-v1'
        assert report['mask']=='011/00'and report['radius_mode']=='strict'
    dependency_spec={
        'foundation':('global_work/strict_011_rebuilt_v3','CHECKPOINT_MANIFEST.json',
            'ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'),
        'complete_tree':('global_work/strict011_strengthened_tree_v1','PREMISE_BINDINGS.json',
            '697d1d0f94c6b668baf7f48c193ea7af9a8d2c8d2c51d295d29a6cb79ff55910'),
        'corner_layer':('global_work/strict011_four_product_layer_v2','PREMISE_BINDINGS.json',
            'efcf09c0494c1f36875533aeb3e4562173f84c49e8856de2d25b81eba781f778'),
        'strict_guard':('global_work/strict011_universal_021_applications_v2','PREMISE_BINDINGS.json',
            '4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023')}
    dependencies={}
    for name,(relative,filename,expected)in dependency_spec.items():
        folder=WORKSPACE/relative;manifest=folder/filename
        assert digest(manifest)==expected
        inventory=json.loads(manifest.read_text())
        for member,entry in inventory['files'].items():
            target=(folder/member).resolve()
            assert target.is_relative_to(folder.resolve())and not(folder/member).is_symlink()
            assert target.stat().st_size==entry['bytes']and digest(target)==entry['sha256']
        dependencies[name]=dict(workspace_relative_folder=relative,inventory_file=filename,
            inventory_sha256=expected,member_count=len(inventory['files']))
    write(HERE/'DEPENDENCIES.json',dict(schema='strict011_strengthened_driver_dependencies_v1',
        workspace=str(WORKSPACE),dependencies=dependencies,old_001_context_required=False))
    write(HERE/'PREPARATION_EXECUTION.json',dict(
        status='PASS_OBSERVED_NO_SOLVER_PREPARATION_CONTROLS',
        controls_session=51628,controls_observed_exit_code=0,
        controls_report_sha256=digest(HERE/'preparation_controls/PREPARATION_CONTROLS.json'),
        controls_log_sha256=digest(HERE/'PREPARATION_CONTROLS.log'),
        exact_whole_seed_freshly_replayed_by_observed_controls=True,
        original_seed_prepare_session=45533,original_seed_prepare_session_exit_observed=False,
        original_seed_session_note='Polling after compaction returned Unknown process id; retained artifacts were freshly checked by the observed controls.',
        accepted_option_inspector_session=60647,accepted_option_inspector_observed_exit_code=0,
        pilot_option_inspector_session=35774,pilot_option_inspector_observed_exit_code=0,
        pilot_option_report_sha256=digest(HERE/'PILOT_OPTIONS_NO_SOLVE.json'),
        numerical_optimization_called=False,actual_corner_weight_gate_passed=False,
        successful_true_guard_gate_passed=False,original_cell_credit=0,whole_mask_credit=0))
    files={}
    for path in sorted(HERE.rglob('*')):
        assert not path.is_symlink(),str(path)
        if path.is_file():
            assert '__pycache__'not in path.parts and path.suffix!='.pyc'
            files[str(path.relative_to(HERE))]=dict(bytes=path.stat().st_size,sha256=digest(path))
    freeze=dict(schema='prepared_strict011_strengthened_numerical_driver_v1',
        no_actual_solver_run_claimed_at_freeze=True,base_numeric_core_sha256=BASE,
        driver_sha256=digest(HERE/'strengthened_discovery.py'),
        root_id='full-strict-01100-representative-root-v1',mask='011/00',radius_mode='strict',
        original_caller_counts=dict(originals=9,corners=36,pairs=36,marked_links=5),
        input_manifest_sha256=digest(seed/'manifest.json'),
        actual_use_gates=dict(positive_new_corner_weight=False,successful_true_guard_with_fresh_scalar=False),
        inherited_numeric_or_original_cell_suffix_used=False,
        numerical_launch_held=True,original_cell_credit=0,whole_mask_credit=0,
        total_bytes=sum(entry['bytes']for entry in files.values()),files=files)
    write(HERE/'SOURCE_FREEZE.json',freeze)
    output=WORKSPACE/'repo/research/nine/.runs/strict011_strengthened_corner_first_use_v1'
    assert not output.exists()
    argv=['python','-B','-u',str(HERE/'strengthened_discovery.py'),
        '--checkpoint',str(WORKSPACE/dependency_spec['foundation'][0]),
        '--complete-folder',str(WORKSPACE/dependency_spec['complete_tree'][0]),
        '--corner-folder',str(WORKSPACE/dependency_spec['corner_layer'][0]),
        '--guard-folder',str(WORKSPACE/dependency_spec['strict_guard'][0]),
        '--input',str(seed/'manifest.json'),'--output',str(output),
        '--source-binding',digest(HERE/'SOURCE_FREEZE.json'),
        '--rounds','1','--objectives','108','--max-nodes','1','--max-depth','0',
        '--corner-passes','2','--lp-seconds','2','--enable-guards','--require-positive-corner-weight']
    launch=dict(schema='held_strict011_strengthened_first_actual_corner_use_pilot_v1',
        status='PREPARED_HELD_NOT_LAUNCHED',cwd=str(WORKSPACE),argv=argv,
        environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1'),
        source_freeze_sha256=digest(HERE/'SOURCE_FREEZE.json'),
        input_manifest_sha256=digest(seed/'manifest.json'),
        log=str(output.with_name(output.name+'.log')),
        complete_tree_binding_sha256=dependency_spec['complete_tree'][2],
        upper_solve_counts=dict(phase=6,objective=108),
        max_LP_time_seconds=2,max_nodes=1,no_new_branches=True,
        root_source_review_required_before_launch=True,fresh_capacity_check_required_before_launch=True,
        starts_numerical_job=False,
        acceptance=dict(fresh_complete_exact_replay=True,new_positive_corner_weight_required=True,
            source_and_root_hashes_unchanged=True,diagnostic_points_are_not_premises=True),
        code_3_means='Complete exact checkpoint retained, but no new positive real-LP corner weight was observed.',
        original_cell_credit=0,whole_mask_credit=0)
    write(HERE/'HELD_PILOT_LAUNCH.json',launch)
    print(json.dumps(dict(status='PASS_PREPARED_HELD_DRIVER_FROZEN',members=len(files),
        bytes=freeze['total_bytes'],source_freeze_sha256=digest(HERE/'SOURCE_FREEZE.json'),
        held_launch_sha256=digest(HERE/'HELD_PILOT_LAUNCH.json'))))
if __name__=='__main__':main()

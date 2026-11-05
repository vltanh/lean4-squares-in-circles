#!/usr/bin/env python3
"""Freeze source-only height-tree preparation and an unexecuted exact gate."""
if not __debug__:
    raise RuntimeError('Height tree freezing requires exact assertions.')
import ast
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORKSPACE=HERE.parents[1]
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def checked(folder,name,expected):
    assert digest(folder/name)==expected
    inventory=json.loads((folder/name).read_text())
    for rel,entry in inventory['files'].items():
        path=(folder/rel).resolve();assert path.is_relative_to(folder.resolve())and not(folder/rel).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
    return dict(folder=str(folder),inventory_file=name,inventory_sha256=expected,members=len(inventory['files']))
def main():
    assert not(HERE/'PREMISE_BINDINGS.json').exists()and not(HERE/'HELD_FIRST_USE.json').exists()
    dependencies={}
    spec=(
        ('foundation','global_work/strict_011_rebuilt_v3','CHECKPOINT_MANIFEST.json','ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'),
        ('corners','global_work/strict011_four_product_layer_v2','PREMISE_BINDINGS.json','efcf09c0494c1f36875533aeb3e4562173f84c49e8856de2d25b81eba781f778'),
        ('guards','global_work/strict011_universal_021_applications_v2','PREMISE_BINDINGS.json','4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'),
        ('height_design','global_work/strict011_c_height_complement_note_v1','PREMISE_BINDINGS.json','06aba6fc518e44d1b859bccb9cc81b6ab57ef5b2df91970f654ba9fe8ab3fd79'),
        ('accepted_strengthened_tree','global_work/strict011_strengthened_tree_v1','PREMISE_BINDINGS.json','697d1d0f94c6b668baf7f48c193ea7af9a8d2c8d2c51d295d29a6cb79ff55910'),
        ('unchanged_held_numerical_driver','global_work/strict011_strengthened_discovery_v1','SOURCE_FREEZE.json','9df42998d72dc39e358883fc44582e9dc69152f4f5dd20cc1de42d4e5e039ab3'))
    for key,folder,name,expected in spec:dependencies[key]=checked(WORKSPACE/folder,name,expected)
    copies=json.loads((HERE/'ACCEPTED_SOURCE_COPIES.json').read_text())
    for entry in copies['files']:
        assert digest(entry['source'])==digest(HERE/entry['copied_as'])==entry['sha256']
    transformation=json.loads((HERE/'WRAPPER_TRANSFORMATION.json').read_text())
    assert transformation['unchanged_sat_proxy_angle_dispatch_AST']is True
    assert transformation['unchanged_function_ASTs']==['digest','read_module','local_file','pin']
    assert transformation['new_source_sha256']==digest(HERE/'verify_height_complete_tree.py')
    assert transformation['height_context_adapter_sha256']==digest(HERE/'height_context_adapter.py')
    controls=json.loads((HERE/'fresh_controls/PREPARATION_CONTROLS.json').read_text())
    assert controls['status']=='PASS_PREPARED_C_HEIGHT_TREE_AND_LOCAL_CONDITIONAL_CONTROLS_NO_ACTUAL_COVER_USE'
    assert controls['preparation_damages_rejected']==32
    assert controls['fresh_scalar_or_optimizer_called']is controls['global_height_cover_replayed']is False
    assert controls['first_actual_cover_gate_still_pending']is True
    for path,expected in controls['local_source_sha256'].items():assert digest(path)==expected
    for path in HERE.glob('*.py'):ast.parse(path.read_text(),filename=str(path))
    first=HERE/'fresh_controls/first_height_cover_candidate'
    manifest=json.loads((first/'manifest.json').read_text());assert len(manifest['nodes'])==5
    assert manifest['schema']=='fresh_full_strict011_C_height_context_tree_v1'
    rounds=0
    for entry in manifest['nodes']:
        path=first/entry['file'];assert digest(path)==entry['sha256']
        record=json.loads(path.read_text());rounds+=len(record['rounds'])
        assert record['status']=='OPEN'
    assert rounds==4
    write(HERE/'DEPENDENCIES.json',dict(schema='prepared_C_height_tree_dependencies_v1',
        dependencies=dependencies,full_caller_unchanged=True,original_cell_credit=0,whole_mask_credit=0))
    write(HERE/'PREPARATION_EXECUTION.json',dict(status='PASS_OBSERVED_SOURCE_AND_CONDITIONAL_PREPARATION_ONLY',
        process_session=3778,observed_exit_code=0,
        report_sha256=digest(HERE/'fresh_controls/PREPARATION_CONTROLS.json'),
        log_sha256=digest(HERE/'PREPARATION_CONTROLS.log'),
        complete_valid_height_union_replayed=False,fresh_scalar_process_started=False,numerical_process_started=False,
        first_actual_cover_gate_held_for_source_review=True,original_cell_credit=0,whole_mask_credit=0))
    files={}
    for path in sorted(HERE.rglob('*')):
        assert not path.is_symlink()
        if path.is_file():
            assert '__pycache__'not in path.parts and path.suffix!='.pyc'
            files[str(path.relative_to(HERE))]=dict(bytes=path.stat().st_size,sha256=digest(path))
    binding=dict(schema='prepared_strict011_C_height_complete_tree_v1',
        root_id='full-strict-01100-representative-root-v1',mask='011/00',radius_mode='strict',target_q='1105/256',
        physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
        height_design_binding_sha256=dependencies['height_design']['inventory_sha256'],
        checker_sha256=digest(HERE/'verify_height_complete_tree.py'),
        context_adapter_sha256=digest(HERE/'height_context_adapter.py'),
        discovery_attachment_sha256=digest(HERE/'height_discovery_attachment.py'),
        first_use_candidate_manifest_sha256=digest(first/'manifest.json'),
        base_state_format_unchanged=True,old_complete_four_eight_two_dispatch_AST_unchanged=True,
        root_context=None,context_reconstructed_at_every_node=True,
        second_height_union_on_one_path_rejected=True,fresh_scalar_required_before_height_children=True,
        first_actual_cover_gate_executed_at_freeze=False,real_LP_required_for_height_cover_gate=False,
        frozen_corner_numerical_driver_unchanged=True,arbitrary_tree_resume_API_implemented=False,
        original_cell_credit=0,whole_mask_credit=0,
        files=files,total_bytes=sum(entry['bytes']for entry in files.values()))
    write(HERE/'PREMISE_BINDINGS.json',binding)
    output=WORKSPACE/'repo/research/nine/.runs/strict011_C_height_first_exact_use_v1'
    assert not output.exists()
    argv=['python','-B','-S','-u',str(HERE/'run_first_use_gate.py'),'--source-binding',digest(HERE/'PREMISE_BINDINGS.json'),
        '--foundation',dependencies['foundation']['folder'],'--corner-folder',dependencies['corners']['folder'],
        '--guard-folder',dependencies['guards']['folder'],'--height-folder',dependencies['height_design']['folder'],
        '--output-folder',str(output)]
    write(HERE/'HELD_FIRST_USE.json',dict(schema='held_first_exact_C_height_complete_cover_use_v1',
        status='PREPARED_NOT_EXECUTED_SOURCE_REVIEW_REQUIRED',cwd=str(WORKSPACE),argv=argv,
        source_binding_sha256=digest(HERE/'PREMISE_BINDINGS.json'),
        first_use_manifest_sha256=binding['first_use_candidate_manifest_sha256'],
        log=str(output.with_name(output.name+'.log')),
        expected_complete_unions={'strict011_C_height_four_way_v1':1},
        expected_nodes=5,expected_open_leaves=4,expected_exact_rounds=4,expected_deductions=4,expected_printed_rows=8,
        fresh_scalar_required=dict(domains=28,leaves=351,coefficients=43875),
        optimizer_called=False,hand_chosen_exact_weights=True,
        separate_real_LP_corner_gate_claimed=False,root_source_review_required_before_execution=True,
        numerical_search_launched=False,original_cell_credit=0,whole_mask_credit=0))
    print(json.dumps(dict(status='PASS_PREPARED_C_HEIGHT_TREE_FROZEN',members=len(files),bytes=binding['total_bytes'],
        binding_sha256=digest(HERE/'PREMISE_BINDINGS.json'),held_gate_sha256=digest(HERE/'HELD_FIRST_USE.json'))))
if __name__=='__main__':main()

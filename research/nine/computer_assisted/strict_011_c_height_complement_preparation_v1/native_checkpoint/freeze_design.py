#!/usr/bin/env python3
"""Freeze the prepared theorem-complement sources; no proof/search dispatch."""
if not __debug__:
    raise RuntimeError('C-height source freeze requires assertions.')
from hashlib import sha256
import argparse
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
FOUNDATION='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
GUARD='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--guard-folder',type=Path,required=True);args=parser.parse_args()
    assert not(HERE/'PREMISE_BINDINGS.json').exists()
    dependencies={}
    for name,folder,filename,expected in(
        ('full_caller_foundation',args.foundation,'CHECKPOINT_MANIFEST.json',FOUNDATION),
        ('accepted_C_application_and_universal_scalar',args.guard_folder,'PREMISE_BINDINGS.json',GUARD)):
        folder=folder.resolve();assert digest(folder/filename)==expected
        value=json.loads((folder/filename).read_text());hashes={filename:expected}
        for rel,entry in value['files'].items():
            path=(folder/rel).resolve();assert path.is_relative_to(folder)and not(folder/rel).is_symlink()
            assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
            hashes[rel]=entry['sha256']
        dependencies[name]=dict(folder=str(folder),inventory_file=filename,inventory_sha256=expected,
            member_count=len(value['files']),source_sha256=hashes)
    for model,caller in(('strict_011_full_root_v2','base'),('strict_011_representative_root_v1','representative')):
        assert(args.foundation/model/'snapshots/ROOT_DOCUMENT.json').read_bytes()==(args.guard_folder/'callers'/(caller+'.json')).read_bytes()
    controls=json.loads((HERE/'fresh_controls/LITERAL_COVER_CONTROLS.json').read_text())
    assert controls['status']=='PASS_PREPARED_C_HEIGHT_LITERAL_AND_SYMBOLIC_COMPLETE_COVER_CONTROLS'
    assert controls['damaged_literals_callers_or_source_reuse_rejected']==94
    assert controls['fresh_scalar_replayed']is controls['numerical_solver_called']is False
    for path,expected in controls['local_source_sha256'].items():assert digest(path)==expected
    for path,expected in controls['accepted_source_sha256'].items():assert digest(path)==expected
    current=json.loads((HERE/'SYMBOLIC_CONTROLS_CURRENT.json').read_text())
    for path,expected in current['source_sha256'].items():assert digest(path)==expected
    write(HERE/'DEPENDENCIES.json',dict(schema='prepared_strict011_C_height_cover_dependencies_v1',
        dependencies=dependencies,whole_caller_symmetry_binding_sha256='19ae3cdfae702f93bc426bb7dd619ce91a487a7806ebaddc59674ec7031274fe',
        fresh_scalar_gate_required_at_first_actual_cover_use=True,
        existing_scalar_receipts_accepted_as_future_gate=False,
        full_state_ancestry_not_implemented_in_this_design=True))
    write(HERE/'CONTROL_EXECUTION.json',dict(status='PASS_OBSERVED_EXACT_DESIGN_CONTROLS_ONLY',
        literal_controls_observed_exit_code=0,literal_controls_report_sha256=digest(HERE/'fresh_controls/LITERAL_COVER_CONTROLS.json'),
        symbolic_current_controls_observed_exit_code=0,symbolic_current_report_sha256=digest(HERE/'SYMBOLIC_CONTROLS_CURRENT.json'),
        source_pin_and_caller_count_checks=True,scalar_process_started=False,numerical_process_started=False,
        cover_installed=False,original_cell_credit=0,whole_mask_credit=0))
    files={}
    for path in sorted(HERE.rglob('*')):
        assert not path.is_symlink()
        if path.is_file():
            assert path.suffix!='.pyc'and'__pycache__'not in path.parts
            files[str(path.relative_to(HERE))]=dict(bytes=path.stat().st_size,sha256=digest(path))
    binding=dict(schema='prepared_strict011_C_height_closed_complement_v1',
        mask='011/00',radius_mode='strict',accepted_C_application_binding_sha256=GUARD,
        full_caller_foundation_binding_sha256=FOUNDATION,
        physical_necessity='abs(yC-yB)+abs(yD-yC)>21/100',
        closed_alternatives=4,all_originals_retained=9,all_original_corners=36,all_original_pairs=36,marked_links=5,
        strict_bit_relations_unchanged=True,shared_boundary_faces_retained=True,
        additional_frame_or_corridor_premises=False,old_001_premises=False,
        accepted_scalar_requires_fresh_replay_at_first_actual_use=True,
        new_complete_ancestry_adapter_review_required=True,
        frozen_four_eight_two_checker_or_driver_changed=False,
        cover_installed=False,numerical_search_started=False,original_cell_credit=0,whole_mask_credit=0,
        files=files,total_bytes=sum(entry['bytes']for entry in files.values()))
    write(HERE/'PREMISE_BINDINGS.json',binding)
    print(json.dumps(dict(status='PASS_PREPARED_C_HEIGHT_DESIGN_FROZEN',members=len(files),
        bytes=binding['total_bytes'],binding_sha256=digest(HERE/'PREMISE_BINDINGS.json'))))
if __name__=='__main__':main()

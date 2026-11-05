#!/usr/bin/env python3
"""Held exact-only first C-height cover use; no optimizer or discovery run."""
if not __debug__:
    raise RuntimeError('Exact first-use replay rejects optimized Python.')
from hashlib import sha256
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source-binding',required=True)
    for name in('foundation','corner-folder','guard-folder','height-folder','output-folder'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();binding_path=HERE/'PREMISE_BINDINGS.json'
    assert digest(binding_path)==args.source_binding
    binding=json.loads(binding_path.read_text())
    assert binding['schema']=='prepared_strict011_C_height_complete_tree_v1'
    assert binding['first_actual_cover_gate_executed_at_freeze']is False
    hashes={str(binding_path):args.source_binding}
    for name,entry in binding['files'].items():
        path=(HERE/name).resolve();assert path.is_relative_to(HERE)and not(HERE/name).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
        hashes[str(path)]=entry['sha256']
    out=args.output_folder.resolve();assert not out.exists()
    frozen=(HERE,args.foundation.resolve(),args.corner_folder.resolve(),args.guard_folder.resolve(),args.height_folder.resolve())
    assert all(not out.is_relative_to(folder)for folder in frozen)
    out.mkdir(parents=True)
    candidate=HERE/'fresh_controls/first_height_cover_candidate'
    manifest=candidate/'manifest.json'
    assert digest(manifest)==binding['first_use_candidate_manifest_sha256']
    report_path=out/'COMPLETE_EXACT_REPLAY.json'
    command=[sys.executable,'-B','-S',str(HERE/'verify_height_complete_tree.py'),str(manifest),str(report_path),
        '--workspace',str(args.foundation.resolve()/'dependencies/workspace'),
        '--model-folder',str(args.foundation.resolve()/'strict_011_representative_root_v1'),
        '--corner-folder',str(args.corner_folder.resolve()),'--guard-folder',str(args.guard_folder.resolve()),
        '--scalar-output-folder',str(out/'ordinary_guard_scalar'),
        '--height-folder',str(args.height_folder.resolve()),'--height-scalar-output-folder',str(out/'height_scalar')]
    with(out/'COMPLETE_EXACT_REPLAY.log').open('x')as log:
        subprocess.run(command,check=True,stdout=log,stderr=subprocess.STDOUT)
    report=json.loads(report_path.read_text())
    assert report['status']=='PASS_COMPLETE_STRICT011_C_HEIGHT_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS'
    assert report['root_id']=='full-strict-01100-representative-root-v1'
    assert report['mask']=='011/00'and report['radius_mode']=='strict'
    assert(report['physical_originals'],report['original_corners'],report['original_pairs'],report['marked_cones'])==(9,36,36,5)
    assert(report['nodes'],report['excluded_leaves'],report['open_leaves'])==(5,0,4)
    assert report['complete']is report['whole_mask_proved']is False
    assert report['complete_unions']=={'strict011_C_height_four_way_v1':1}
    assert report['exact_totals']==dict(rounds=4,deductions=4,printed_rows_checked=8)
    assert report['manifest_sha256']==digest(manifest)
    height=report['height_cover_attachment']
    assert height['complete_height_unions']==1 and height['contexts_reconstructed_from_complete_parent_unions']is True
    scalar=height['fresh_scalar_replay']['fresh_scalar']['report']
    assert(scalar['domains'],scalar['leaves'],scalar['bernstein_coefficients'])==(28,351,43875)
    assert scalar['frontier']==0 and scalar['strict_except_all_zero']is True
    manifest_value=json.loads(manifest.read_text());uses=[]
    for entry in manifest_value['nodes']:
        path=candidate/entry['file'];assert digest(path)==entry['sha256']
        record=json.loads(path.read_text())
        for number,round_ in enumerate(record['rounds']):
            rows={row['index']:row for row in round_['printed_rows']}
            for proposal in round_['proposals']:
                assert proposal['residual_coefficients']==[]and proposal['residual_correction']=='0'
                for index,weight in proposal['weights']:
                    if rows[index]['name'].startswith('strict011_C_height_complement_v1:'):
                        assert type(weight)is int and weight>0
                        uses.append(dict(node=entry['id'],round=number,row=rows[index]['name'],weight=weight,
                            context=record['height_context'],objective=proposal['objective'],upper=proposal['upper']))
    assert len(uses)==4 and {item['context']['branch']for item in uses}==set(range(4))
    for path,expected in hashes.items():assert digest(path)==expected
    result=dict(status='PASS_FIRST_ACTUAL_EXACT_C_HEIGHT_COMPLETE_COVER_USE',
        source_binding_sha256=args.source_binding,complete_report_sha256=digest(report_path),
        manifest_sha256=digest(manifest),root_id=report['root_id'],mask='011/00',radius_mode='strict',
        nodes=5,open_leaves=4,complete_height_unions=1,
        fresh_scalar_counts=dict(domains=28,leaves=351,coefficients=43875),
        exact_rounds=4,exact_deductions=4,printed_rows_checked=8,
        positive_height_row_uses=uses,weight_denominator=1<<40,
        weights_hand_chosen=True,real_optimizer_called=False,
        separate_real_LP_corner_gate_claimed=False,whole_mask_proved=False,
        original_cell_credit=0,whole_mask_credit=0)
    write(out/'FIRST_ACTUAL_USE.json',result)
    print(json.dumps(dict(status=result['status'],receipt_sha256=digest(out/'FIRST_ACTUAL_USE.json'),
        exact_report_sha256=digest(report_path),open_leaves=4)))
if __name__=='__main__':main()

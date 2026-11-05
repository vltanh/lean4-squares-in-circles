#!/usr/bin/env python3
"""Read-only inventory/caller check with optional fresh exact fixture replay."""
if not __debug__:
    raise RuntimeError('Checkpoint replay rejects optimized Python.')

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('output',type=Path)
    parser.add_argument('--replay-fixtures',action='store_true')
    args=parser.parse_args()
    manifest_path=HERE/'CHECKPOINT_MANIFEST.json'
    m=json.loads(manifest_path.read_text())
    assert m['status']=='FROZEN_REBUILT_STRICT011_FOUNDATIONS_AND_REPRESENTATIVE_ROOT_NO_CLOSURE'
    assert m['original_cell_credit']==m['whole_mask_credit']==0
    for rel,entry in m['files'].items():
        p=(HERE/rel).resolve()
        assert p.is_relative_to(HERE) and not (HERE/rel).is_symlink() and p.is_file()
        assert p.stat().st_size==entry['bytes'] and digest(p)==entry['sha256'],rel
    actual={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file()
            and p.name!='CHECKPOINT_MANIFEST.json' and p.suffix!='.log'}
    assert actual==set(m['files'])
    origin=json.loads((HERE/'SOURCE_RECONSTRUCTION.json').read_text())
    for rel,entry in origin['source_files'].items():
        assert digest(HERE/rel)==entry['sha256']
    root_audits={}
    for name in ('strict_011_full_root_v2','strict_011_representative_root_v1'):
        folder=HERE/name
        I=load('checkpoint_'+name,folder/'independent_strict_011_adapter.py')
        state=I.verify_root(json.loads((folder/'snapshots/ROOT_DOCUMENT.json').read_text()))
        root_audits[name]=dict(id=state['id'],mask='011/00',radius_mode='strict',
            physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
            representative=(name=='strict_011_representative_root_v1'))
    fixture_audits={}
    if args.replay_fixtures:
        for cover_name,model_name in (
                ('strict_011_complete_cover_v2','strict_011_full_root_v2'),
                ('strict_011_representative_cover_v1','strict_011_representative_root_v1')):
            folder=HERE/cover_name
            T=load('checkpoint_'+cover_name,folder/'verify_strict_011_complete_tree.py')
            delivered=json.loads((folder/'fresh_controls/COMPLETE_TREE_CONTROLS.json').read_text())
            checked={}
            for name,expected in delivered['fixtures'].items():
                report=T.verify(folder/'fresh_controls'/name/'manifest.json',
                                HERE/'dependencies/workspace',HERE/model_name)
                assert not report['complete'] and not report['whole_mask_proved']
                for key in ('nodes','excluded_leaves','open_leaves','exact_totals'):
                    assert report[key]==expected[key]
                assert report['complete_unions']==expected['unions']
                checked[name]={k:report[k] for k in ('status','nodes','excluded_leaves','open_leaves','exact_totals')}
            assert len(checked)==5
            fixture_audits[cover_name]=checked
    for rel,entry in m['files'].items():
        assert digest(HERE/rel)==entry['sha256']
    assert not any(n.split('.')[0] in {'numpy','scipy','z3','sympy','highspy'} for n in sys.modules)
    result=dict(status='PASS_REBUILT_STRICT011_CHECKPOINT',
        checkpoint_manifest_sha256=digest(manifest_path),files=len(m['files']),
        root_audits=root_audits,fresh_fixture_audits=fixture_audits,
        full_broad_row_controls_repeated=False,numerical_solver_called=False,
        original_cell_credit=0,whole_mask_credit=0)
    assert not args.output.resolve().is_relative_to(HERE)
    with args.output.open('x') as f:
        json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(dict(status=result['status'],files=result['files'],
        fixture_trees=sum(map(len,fixture_audits.values())),whole_mask_credit=0,
        report=str(args.output.resolve()),sha256=digest(args.output))))

if __name__=='__main__':
    main()

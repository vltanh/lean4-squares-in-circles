#!/usr/bin/env python3
"""Prepare and exactly replay a new zero-round whole representative root."""
if not __debug__:
    raise RuntimeError('Exact seed preparation rejects optimized Python.')
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser()
    for flag in('checkpoint','complete-folder','corner-folder','guard-folder','output'):
        parser.add_argument('--'+flag,type=Path,required=True)
    args=parser.parse_args();folder=args.output.resolve();assert not folder.exists()
    spec=importlib.util.spec_from_file_location('strengthened011_seed_preparation',HERE/'strengthened_discovery.py')
    D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)
    bundle=D.bootstrap(args)
    root=bundle['P'].fresh_state();view=bundle['P'].state_view(root)
    assert view==bundle['document']['initial']
    folder.mkdir(parents=True,exist_ok=False);(folder/'nodes').mkdir()
    document=bundle['checkpoint']/D.B.MODEL_NAME/'snapshots/ROOT_DOCUMENT.json'
    raw=document.read_bytes()
    with(folder/'root_document.json').open('xb')as stream:stream.write(raw)
    manifest=dict(schema=D.SCHEMA,root_document=dict(file='root_document.json',sha256=sha256(raw).hexdigest()),root=0,nodes=[])
    store=D.B.Store(bundle,folder,manifest)
    record=dict(status='OPEN',initial=view,rounds=[],final=view)
    manifest['nodes']=[store.put_immutable(0,record)];store.install(manifest)
    scalar=folder.with_name(folder.name+'_fresh_scalar_preparation')
    report=D.verify_tree(bundle,folder/'manifest.json',scalar)
    assert (report['nodes'],report['excluded_leaves'],report['open_leaves'])==(1,0,1)
    assert report['exact_totals']==dict(rounds=0,deductions=0,printed_rows_checked=0)
    assert not report['whole_mask_proved']and not scalar.exists()
    bundle['A'].write_json(folder/'ZERO_ROUND_EXACT_REPLAY.json',report)
    receipt=dict(status='PASS_FRESH_STRENGTHENED_ZERO_ROUND_WHOLE_ROOT_SEED',
        seed_manifest_sha256=digest(folder/'manifest.json'),exact_report_sha256=digest(folder/'ZERO_ROUND_EXACT_REPLAY.json'),
        caller_root_document_sha256=digest(folder/'root_document.json'),root_id=view['id'],mask='011/00',radius_mode='strict',
        physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
        source_sha256={str(p.resolve()):digest(p)for p in(HERE/'prepare_fresh_seed.py',HERE/'strengthened_discovery.py')},
        no_prior_numerical_suffix_used=True,numerical_solver_called=False,original_cell_credit=0,whole_mask_credit=0)
    bundle['A'].write_json(folder/'SEED_PREPARATION.json',receipt)
    print(json.dumps(dict(status=receipt['status'],manifest_sha256=receipt['seed_manifest_sha256'],
                         report_sha256=receipt['exact_report_sha256'],receipt_sha256=digest(folder/'SEED_PREPARATION.json'))))
if __name__=='__main__':main()

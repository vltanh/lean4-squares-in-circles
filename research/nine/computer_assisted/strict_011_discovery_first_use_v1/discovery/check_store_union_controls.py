"""Independently replay the new store's SAT8 and angle2 pending covers."""
if not __debug__:
    raise RuntimeError('Exact controls require assertions.')
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--checkpoint',type=Path,required=True)
    parser.add_argument('--output-directory',type=Path,required=True)
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    spec=importlib.util.spec_from_file_location('store_union_discovery_source',here/'fresh_strict011_discovery.py')
    D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)
    bundle=D.bootstrap(args.checkpoint)
    source=bundle['checkpoint']/D.COVER_NAME/'fresh_controls/fresh_root_open/manifest.json'
    args.output_directory.mkdir(parents=True,exist_ok=False)
    audits={}
    for name,kind,arg,cut,count in [('all_HI_owned_cases','sat',(7,8),None,8),
                                   ('both_D_angle_halves','angle',3,'1/2',2)]:
        store,before=D.initialize(bundle,source,args.output_directory/name)
        ids=store.split(store.manifest['root'],kind,arg,cut)
        assert len(ids)==count
        report=bundle['T'].verify(store.folder/'manifest.json',bundle['checkpoint']/'dependencies/workspace',
                                  bundle['checkpoint']/D.MODEL_NAME)
        assert report['nodes']==count+1 and report['open_leaves']==count and report['excluded_leaves']==0
        assert not report['whole_mask_proved'] and report['complete_unions']=={kind:1}
        audits[name]={k:report[k] for k in ('status','nodes','open_leaves','excluded_leaves','complete_unions')}
    assert not any(n.split('.')[0] in {'numpy','scipy','z3','sympy','highspy'} for n in sys.modules)
    report=dict(status='PASS_FRESH_DISCOVERY_STORE_COMPLETE_SAT8_ANGLE2',
        source_sha256={str(p):digest(p) for p in (Path(__file__).resolve(),here/'fresh_strict011_discovery.py')},
        fixtures=audits,actual_numerical_solver_called=False,whole_mask_credit=0,original_cell_credit=0)
    out=args.output_directory/'STORE_UNION_CONTROLS.json'
    with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(dict(status=report['status'],report=str(out.resolve()),sha256=digest(out))))

if __name__=='__main__':main()

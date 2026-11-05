#!/usr/bin/env python3
"""Meaningful exact-certificate and interruption controls; never calls an LP."""
if not __debug__:
    raise RuntimeError('Discovery controls reject optimized Python.')

import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--checkpoint',type=Path,required=True)
    parser.add_argument('--output-directory',type=Path,required=True)
    args=parser.parse_args()
    output=args.output_directory.resolve();output.mkdir(parents=True,exist_ok=False)
    spec=importlib.util.spec_from_file_location('controlled_fresh011_discovery',HERE/'fresh_strict011_discovery.py')
    D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)
    bundle=D.bootstrap(args.checkpoint)
    P,I,G=bundle['P'],bundle['I'],bundle['G']
    seed=bundle['checkpoint']/D.COVER_NAME/'fresh_controls/fresh_root_open/manifest.json'
    seed_hash=digest(seed)
    driver_hash=digest(HERE/'fresh_strict011_discovery.py')
    atomic_write=bundle['A'].write_json
    def audit(folder):
        return bundle['T'].verify(folder/'manifest.json',bundle['checkpoint']/'dependencies/workspace',
                                   bundle['checkpoint']/D.MODEL_NAME)
    def run_args(folder):
        return argparse.Namespace(checkpoint=args.checkpoint,input=seed,output=folder,
            pilot_ab_negative=True,rounds=0,objectives=54,max_nodes=33,max_depth=8,lp_seconds=10)

    class ExplicitDualProposal:
        """A hand-selected valid four-row dual. This is not an LP solve."""
        def __init__(self,rows,bounds,seconds):
            self.rows,self.bounds=rows,bounds
        def phase(self):
            selected={'strict011v2:proxy:0:1:0:-1':1,'strict011v2:cone_inset:0:1':1,
                      'strict011v2:bound:45:-1':2,'strict011v2:bound:46:-1':2}
            dual=[-float(selected.get(row[2],0)) for row in self.rows]
            assert sum(x!=0 for x in dual)==4
            return dict(optimal=True,status=0,point=[0.0]*len(self.bounds),phase=0.1,dual=dual)
        def maximum(self,objective):
            raise AssertionError('The phase-only control may not request a bound LP.')

    # Run the actual driver path, with only its numerical proposals replaced.
    old_bootstrap=D.bootstrap
    D.bootstrap=lambda checkpoint:bundle
    summary=D.run(run_args(output/'manual_dual_complete_proxy'),ExplicitDualProposal)
    assert summary['nodes']==5 and summary['excluded_leaves']==1 and summary['open_leaves']==3
    assert not summary['whole_mask_proved_by_exact_tree']
    exact_reserve=json.loads((output/'manual_dual_complete_proxy/EXACT_REPLAY.json').read_text())

    # Exercise the real bound-certificate construction with a hand-selected
    # three-row difference objective, including the exact residual arithmetic.
    child=P.physical_child(P.fresh_state(),'proxy',(0,1),(0,1))
    rows,bounds,propagated,terminal=P.collect(child);assert terminal is None
    class ExplicitBoundProposal:
        def maximum(self,objective):
            if objective!=[(2,-1),(0,1)]:
                return None
            names={'strict011v2:proxy:0:1:0:1','strict011v2:bound:45:-1','strict011v2:bound:46:-1'}
            dual=[-1.0 if row[2] in names else 0.0 for row in rows]
            assert sum(x!=0 for x in dual)==3
            return dual
    rr,after,terminal=D.bound_round(bundle,child,rows,bounds,propagated,ExplicitBoundProposal(),252,0)
    assert terminal is None and len(rr['proposals'])==1 and len(rr['printed_rows'])==3
    record=dict(status='OPEN',initial=P.state_view(child),rounds=[rr],final=P.state_view(after))
    exact_bound,checked=G.check_record(record,child,I.Adapter());assert checked==after
    wrong=deepcopy(record);wrong['rounds'][0]['proposals'][0]['weights'][0][1]+=1
    try:
        G.check_record(wrong,child,I.Adapter())
    except AssertionError:
        pass
    else:
        raise AssertionError('Altered exact dual accepted.')
    bundle['A'].write_json(output/'EXACT_BOUND_FIXTURE.json',record)

    failure_audits=[]
    def injected_main_failure(name,when,after_replace=False):
        folder=output/name;seen=0
        def failure(path,value):
            nonlocal seen
            if Path(path).name=='manifest.json':
                seen+=1
                if seen==when:
                    if after_replace:
                        atomic_write(path,value)
                    raise OSError(28,'injected ENOSPC at proof pointer')
            return atomic_write(path,value)
        bundle['A'].write_json=failure
        try:
            D.run(run_args(folder),ExplicitDualProposal)
        except OSError as error:
            assert error.errno==28
        else:
            raise AssertionError('Main failed to propagate I/O failure.')
        finally:
            bundle['A'].write_json=atomic_write
        report=audit(folder)
        assert not report['whole_mask_proved']
        assert report['nodes']==(1 if when==2 and not after_replace else 5)
        assert report['excluded_leaves']==(1 if when==3 and after_replace else 0)
        assert not (folder/'DISCOVERY_COMPLETION.json').exists()
        failure_audits.append(dict(name=name,manifest_sha256=digest(folder/'manifest.json'),
            nodes=report['nodes'],excluded=report['excluded_leaves'],open=report['open_leaves'],
            error_propagated=True,last_installed_complete_cover_replayed=True))
    injected_main_failure('before_complete_split_manifest',2)
    injected_main_failure('after_complete_split_manifest',2,True)
    injected_main_failure('before_exact_closed_record_manifest',3)
    injected_main_failure('after_exact_closed_record_manifest',3,True)

    # A failure midway through writing siblings leaves the previous OPEN root
    # as the entire installed cover, with the already written children retained.
    store,report=D.initialize(bundle,seed,output/'between_pending_siblings')
    old_manifest=(store.folder/'manifest.json').read_bytes()
    count=0
    def sibling_failure(path,value):
        nonlocal count
        if Path(path).parent.name=='nodes':
            count+=1
            if count==3:
                raise OSError(28,'injected ENOSPC during third sibling')
        return atomic_write(path,value)
    bundle['A'].write_json=sibling_failure
    try:
        store.split(0,'proxy',(0,1))
    except OSError as error:
        assert error.errno==28
    else:
        raise AssertionError('Sibling failure did not propagate.')
    finally:
        bundle['A'].write_json=atomic_write
    assert (store.folder/'manifest.json').read_bytes()==old_manifest
    report=audit(store.folder)
    assert report['nodes']==1 and report['open_leaves']==1
    assert len(list((store.folder/'nodes').glob('*.json')))==3
    failure_audits.append(dict(name='between_pending_siblings',nodes=1,open=1,
        error_propagated=True,last_installed_complete_cover_replayed=True,unreferenced_siblings_retained=2))
    D.bootstrap=old_bootstrap
    optimized=subprocess.run([sys.executable,'-B','-S','-O',str(HERE/'fresh_strict011_discovery.py'),'--help'],
                              capture_output=True,text=True)
    assert optimized.returncode!=0 and 'require assertions' in optimized.stderr
    assert digest(seed)==seed_hash and digest(HERE/'fresh_strict011_discovery.py')==driver_hash
    assert not any(n.split('.')[0] in {'numpy','scipy','z3','sympy','highspy'} for n in sys.modules)
    report=dict(status='PASS_FRESH_STRICT011_DISCOVERY_EXACT_AND_FAILFAST_CONTROLS',
        actual_numerical_solver_called=False,backend='explicit hand-selected rational dual proposals only',
        source_sha256={str(p):digest(p) for p in (Path(__file__).resolve(),HERE/'fresh_strict011_discovery.py',HERE/'atomic_json_checkpoint.py')},
        checkpoint_manifest_sha256=D.CHECKPOINT_SHA,source_seed_manifest_sha256=seed_hash,
        manual_dual_complete_cover=dict(nodes=5,excluded_leaves=1,open_leaves=3,
                                       report_sha256=digest(output/'manual_dual_complete_proxy/EXACT_REPLAY.json')),
        exact_difference_bound=exact_bound,altered_dual_rejected=True,
        interruption_controls=failure_audits,optimized_python_rejected_before_dispatch=True,
        old_proof_records_never_modified=True,all_preexisting_source_hashes_retained=True,
        original_cell_credit=0,whole_mask_credit=0)
    atomic_write(output/'DISCOVERY_CONTROLS.json',report)
    print(json.dumps(dict(status=report['status'],actual_numerical_solver_called=False,
                         interruption_controls=len(failure_audits),whole_mask_credit=0,
                         report=str(output/'DISCOVERY_CONTROLS.json'),sha256=digest(output/'DISCOVERY_CONTROLS.json'))))

if __name__=='__main__':
    main()

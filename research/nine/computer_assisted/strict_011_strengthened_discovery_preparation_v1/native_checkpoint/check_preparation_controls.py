#!/usr/bin/env python3
"""No-solver controls for the new orchestration, rows, covers and storage.

Fake backends supply diagnostic points or a hand-specified old AB certificate.
They never invoke the NumericalLP constructor. Actual-use gates remain pending.
"""
if not __debug__:
    raise RuntimeError('Exact preparation controls reject optimized Python.')
import argparse
from copy import deepcopy
import errno
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def main():
    parser=argparse.ArgumentParser()
    for name in('checkpoint','complete-folder','corner-folder','guard-folder','seed','output-folder'):
        parser.add_argument('--'+name,type=Path,required=True)
    config=parser.parse_args();output=config.output_folder.resolve();output.mkdir(parents=True,exist_ok=False)
    spec=importlib.util.spec_from_file_location('prepared_strengthened_discovery_controls',HERE/'strengthened_discovery.py')
    D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)
    sources={name:digest(HERE/name)for name in('strengthened_discovery.py','accepted_base_discovery.py',
        'atomic_json_checkpoint.py','prepare_fresh_seed.py','check_preparation_controls.py')}
    assert sources['accepted_base_discovery.py']==D.BASE_SHA
    assert sources['atomic_json_checkpoint.py']==D.B.ATOMIC_SHA
    assert D.NumericalLP is D.B.NumericalLP
    def args(name):
        return SimpleNamespace(checkpoint=config.checkpoint,complete_folder=config.complete_folder,
            corner_folder=config.corner_folder,guard_folder=config.guard_folder,input=config.seed/'manifest.json',
            output=output/name,rounds=0,objectives=108,max_nodes=1,max_depth=0,corner_passes=0,lp_seconds=2,
            enable_guards=True,require_positive_corner_weight=False)
    a=args('complete_store_cover');bundle=D.bootstrap(a);store,initial=D.initialize(bundle,a.input,a.output)
    assert initial['nodes']==1 and initial['open_leaves']==1
    assert bundle['I'].Adapter()is bundle['I'].Adapter()is bundle['exact']
    children=store.split(0,'proxy',(0,1));owned=store.split(children[1],'sat',(0,8));halves=store.split(owned[0],'angle',3,F(1,2))
    assert len(children)==4 and len(owned)==8 and len(halves)==2 and len(store.manifest['nodes'])==15
    class NegativeABBackend:
        calls=0
        def __init__(self,rows,bounds,seconds):self.rows=list(rows);self.bounds=bounds
        def phase(self):
            NegativeABBackend.calls+=1
            required={'strict011v2:inset_tangent:0:1','strict011v2:inset_tangent:1:1',
                      'strict011v2:mask:0:1:0','strict011v2:proxy:0:1:0:-1'}
            dual=[-0.25 if row[2]in required else 0.0 for row in self.rows]
            assert sum(value!=0 for value in dual)==4
            return dict(optimal=True,status=0,phase=0.5,point=[0.0]*len(self.bounds),dual=dual)
        def maximum(self,objective):raise AssertionError('This zero-round fake control must not ask for objective solves.')
    state,point=D.search_node(bundle,store,children[0],a,NegativeABBackend)
    assert state is None and point is None and NegativeABBackend.calls==1
    cover=D.verify_tree(bundle,store.folder/'manifest.json',output/'complete_store_fresh_scalar')
    assert (cover['nodes'],cover['excluded_leaves'],cover['open_leaves'])==(15,1,11)
    assert cover['complete_unions']=={'proxy':1,'sat':1,'angle':1}
    assert not cover['whole_mask_proved']and not cover['conditional_theorem_used']
    write(output/'COMPLETE_STORE_COVER_REPLAY.json',cover)

    # Changing diagnostic tangents forces two rounds of appended rows. The
    # returned dual must match the last solved list, never an unsolved append.
    root=bundle['P'].fresh_state();rows,bounds,current,terminal=bundle['corner'].collect(root,seed_midpoints=True)
    assert terminal is None
    starting_rows=len(rows);snapshots=[]
    class ChangingPointBackend:
        calls=0
        def __init__(self,rows,bounds,seconds):
            self.rows=list(rows);self.bounds=bounds;snapshots.append(len(rows))
        def phase(self):
            ChangingPointBackend.calls+=1
            values=[float(sum(interval)/2)for interval in current['positions']+current['scalar']]
            values[0]=2.0+ChangingPointBackend.calls/10;values[1]=2.0
            return dict(optimal=True,status=0,phase=0.0,point=values,dual=[0.0]*len(self.rows))
        def maximum(self,objective):raise AssertionError('No objective or solver is used in this cut-loop control.')
    cut_args=args('unused');cut_args.corner_passes=2;parameters=[]
    solver,phase=D.phase_with_corner_cuts(bundle,store,0,0,root,current,rows,bounds,parameters,cut_args,ChangingPointBackend)
    assert ChangingPointBackend.calls==3 and snapshots[0]==starting_rows
    assert starting_rows<snapshots[1]<snapshots[2]==len(rows)==len(solver.rows)==len(phase['dual'])
    assert parameters and all(row[2].startswith(D.PREFIX)for row in rows[starting_rows:])
    checked,bb,cc=bundle['exact'].rebuild(root,D.B.literal(rows,range(starting_rows,len(rows))))
    assert checked=={k:rows[k]for k in range(starting_rows,len(rows))}and bb==bounds and cc==current
    root_hash=digest(store.folder/'manifest.json')
    assert D.propose_guard(bundle,current)is None
    rejected=[]
    def reject(name,callback,errors=(AssertionError,ValueError,KeyError,TypeError,RuntimeError,OSError)):
        try:callback()
        except errors:rejected.append(name)
        else:raise AssertionError('Invalid proposal accepted: '+name)
    # A producer's forged PASS cannot bypass the independent guard or cause
    # a scalar replay on a state with no proved quantitative guard.
    saved_evaluate=bundle['guard'].evaluate
    def forged_evaluate(state,document,middle,mode):
        value=saved_evaluate(state,document,middle,mode)
        value['status']='PASS_STRICT011_UNIVERSAL021_GUARD'
        return value
    bundle['guard'].evaluate=forged_evaluate
    try:reject('forged_guard_proposal',lambda:D.search_node(bundle,store,children[3],a,NegativeABBackend))
    finally:bundle['guard'].evaluate=saved_evaluate
    assert digest(store.folder/'manifest.json')==root_hash
    assert not(store.folder/'DISCOVERY_FRESH_SCALAR').exists()

    # The unchanged Store writes all immutable children before replacing its
    # single manifest pointer. Inject ENOSPC at that last replacement boundary.
    fail_args=args('atomic_failure_cover');failure_store,_=D.initialize(bundle,fail_args.input,fail_args.output)
    old_manifest=(failure_store.folder/'manifest.json').read_bytes();old_records=deepcopy(failure_store.manifest)
    original_write=bundle['A'].write_json
    def failed_manifest_write(path,value):
        if Path(path)==failure_store.folder/'manifest.json':raise OSError(errno.ENOSPC,'injected manifest write failure')
        return original_write(path,value)
    bundle['A'].write_json=failed_manifest_write
    try:reject('ENOSPC_before_manifest_replace',lambda:failure_store.split(0,'proxy',(0,1)),(OSError,))
    finally:bundle['A'].write_json=original_write
    assert(failure_store.folder/'manifest.json').read_bytes()==old_manifest
    assert failure_store.manifest==old_records
    for entry in old_records['nodes']:assert digest(failure_store.folder/entry['file'])==entry['sha256']
    preserved=D.verify_tree(bundle,failure_store.folder/'manifest.json',output/'failure_cover_scalar')
    assert(preserved['nodes'],preserved['excluded_leaves'],preserved['open_leaves'])==(1,0,1)
    write(output/'ATOMIC_FAILURE_PRESERVED_COVER_REPLAY.json',preserved)

    # Run the actual new orchestration with a backend that supplies no LP
    # conclusion. Its isolated final verifier still checks the whole root.
    class NoConclusionBackend:
        calls=0
        def __init__(self,rows,bounds,seconds):pass
        def phase(self):
            NoConclusionBackend.calls+=1
            return dict(optimal=False,status=1,message='explicit no-solver preparation fixture')
        def maximum(self,objective):raise AssertionError('No-solver control cannot ask for an objective solve.')
    run_args=args('full_run_without_solver');summary=D.run(run_args,backend=NoConclusionBackend)
    assert NoConclusionBackend.calls==1
    assert summary['actual_LP_backend_used']is False and summary['actual_positive_corner_weight_gate_passed']is False
    assert(summary['nodes'],summary['excluded_leaves'],summary['open_leaves'])==(1,0,1)
    assert not summary['fresh_scalar_replayed_in_cold_gate']
    optimized=subprocess.run([sys.executable,'-O','-B','-S',str(HERE/'strengthened_discovery.py'),'--help'],capture_output=True,text=True)
    assert optimized.returncode!=0 and 'Exact discovery checks reject optimized Python.'in optimized.stderr
    assert sources=={name:digest(HERE/name)for name in sources}
    assert not any(name.split('.')[0]in{'numpy','scipy','sympy','z3','highspy'}for name in sys.modules)
    result=dict(status='PASS_PREPARED_STRENGTHENED_DISCOVERY_CONTROLS_NO_SOLVER',
        source_hashes=sources,exact_core_and_store_reused_byte_identical=True,
        complete_store_cover=dict(nodes=15,excluded=1,open=11,unions=cover['complete_unions']),
        phase_loop=dict(phase_calls=3,row_counts=snapshots,new_rows=len(rows)-starting_rows,
                        returned_dual_matches_final_solved_rows=True),
        rejected_controls=rejected,optimized_python_rejected=True,
        atomic_failure_preserved_exact_whole_root=True,
        actual_run_entry_with_fake_backend_exact_root_passed=True,
        real_numerical_backend_constructed=False,optimization_function_called=False,
        fake_backend_corner_uses_counted_as_actual=False,
        actual_positive_corner_weight_gate_passed=False,successful_true_guard_gate_passed=False,
        numerical_launch_authorized=False,original_cell_credit=0,whole_mask_credit=0)
    write(output/'PREPARATION_CONTROLS.json',result)
    print(json.dumps(dict(status=result['status'],phase_new_rows=len(rows)-starting_rows,
                         report_sha256=digest(output/'PREPARATION_CONTROLS.json'))))
if __name__=='__main__':main()

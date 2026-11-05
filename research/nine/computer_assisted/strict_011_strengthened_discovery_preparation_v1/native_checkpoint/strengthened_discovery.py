#!/usr/bin/env python3
"""Bounded LP proposals using the separately reviewed strengthened verifier.

The accepted dual/residual/rounding core and atomic complete-frontier store are
imported unchanged. Only numeric orchestration and row/terminal proposals are
new. A fresh isolated complete-tree replay is the final proof gate.
"""
if not __debug__:
    raise RuntimeError('Exact discovery checks reject optimized Python.')
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
BASE_SHA='58a85d7976aff42bbda10137f0c951985c674e220568f93d9244dfdf1b92275e'
COMPLETE_BINDING='697d1d0f94c6b668baf7f48c193ea7af9a8d2c8d2c51d295d29a6cb79ff55910'
CORNER_BINDING='efcf09c0494c1f36875533aeb3e4562173f84c49e8856de2d25b81eba781f778'
GUARD_BINDING='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
SCHEMA='fresh_full_strict011_strengthened_representative_tree_v1'
PREFIX='physical_unit_four_corner_'

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path,expected):
    assert digest(path)==expected,str(path)
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module
B=load('strengthened011_unchanged_numeric_and_storage_core',HERE/'accepted_base_discovery.py',BASE_SHA)
NumericalLP=B.NumericalLP

def checked_packet(folder,filename,expected):
    folder=Path(folder).resolve();assert digest(folder/filename)==expected
    value=json.loads((folder/filename).read_text())
    hashes={str(folder/filename):expected}
    for name,entry in value['files'].items():
        path=(folder/name).resolve()
        assert path.is_relative_to(folder)and not(folder/name).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
        hashes[str(path)]=entry['sha256']
    return value,hashes

def verify_driver_binding(expected):
    value,hashes=checked_packet(HERE,'SOURCE_FREEZE.json',expected)
    assert value['schema']=='prepared_strict011_strengthened_numerical_driver_v1'
    assert value['no_actual_solver_run_claimed_at_freeze']is True
    assert value['base_numeric_core_sha256']==BASE_SHA
    return value,hashes

def bootstrap(args):
    bundle=B.bootstrap(args.checkpoint)
    complete,complete_hashes=checked_packet(args.complete_folder,'PREMISE_BINDINGS.json',COMPLETE_BINDING)
    corners,corner_hashes=checked_packet(args.corner_folder,'PREMISE_BINDINGS.json',CORNER_BINDING)
    guards,guard_hashes=checked_packet(args.guard_folder,'PREMISE_BINDINGS.json',GUARD_BINDING)
    def member(folder,inventory,name,label):
        return load(label,Path(folder)/name,inventory['files'][name]['sha256'])
    T=member(args.complete_folder,complete,'verify_strengthened_complete_tree.py','strengthened011_discovery_complete_gate')
    E=member(args.complete_folder,complete,'strengthened_adapter.py','strengthened011_discovery_exact_attachment')
    C=member(args.corner_folder,corners,'strict011_four_product_rows.py','strengthened011_discovery_corner_factory')
    N=member(args.corner_folder,corners,'suggest_four_product_parameters.py','strengthened011_discovery_corner_suggestions')
    GP=member(args.guard_folder,guards,'strict021_guards.py','strengthened011_discovery_guard_proposals')
    document=json.loads((bundle['checkpoint']/B.MODEL_NAME/'snapshots/ROOT_DOCUMENT.json').read_text())
    output=Path(args.output).resolve()
    exact=E.Adapter(bundle['checkpoint'],args.corner_folder,args.guard_folder,document,output/'DISCOVERY_FRESH_SCALAR')
    original_I=bundle['I']
    class CachedAdapter:
        def __new__(cls):return exact
        @staticmethod
        def verify_early_terminal(state,terminal):return exact.verify_early_terminal(state,terminal)
    facade=SimpleNamespace(**{name:getattr(original_I,name)for name in dir(original_I)if not name.startswith('__')})
    facade.Adapter=CachedAdapter
    bundle.update(I=facade,raw_I=original_I,T=T,E=E,exact=exact,
        corner=C.Context(bundle['checkpoint'],document),suggest=N.suggest,guard=GP,document=document,
        complete_folder=Path(args.complete_folder).resolve(),corner_folder=Path(args.corner_folder).resolve(),
        guard_folder=Path(args.guard_folder).resolve(),
        extra_source_hashes={**complete_hashes,**corner_hashes,**guard_hashes},diagnostic_counter=0)
    assert bundle['corner'].model.fresh_state()==bundle['P'].fresh_state()
    return bundle

def verify_tree(bundle,manifest,scalar_folder):
    return bundle['T'].verify(manifest,bundle['checkpoint']/'dependencies/workspace',
        bundle['checkpoint']/B.MODEL_NAME,bundle['corner_folder'],bundle['guard_folder'],scalar_folder)

def initialize(bundle,source,output):
    source=Path(source).resolve();output=Path(output).resolve();assert not output.exists()
    before=digest(source)
    input_scalar=output.with_name(output.name+'_fresh_input_scalar')
    assert not input_scalar.exists()
    report=verify_tree(bundle,source,input_scalar)
    assert digest(source)==before and report['root_id']==bundle['P'].ROOT_ID
    assert report['mask']=='011/00'and report['radius_mode']=='strict'
    manifest=json.loads(source.read_text());assert manifest['schema']==SCHEMA
    output.mkdir(parents=True,exist_ok=False);(output/'nodes').mkdir();(output/'diagnostics').mkdir()
    document=source.parent/manifest['root_document']['file'];raw=document.read_bytes()
    assert sha256(raw).hexdigest()==manifest['root_document']['sha256']
    with (output/'root_document.json').open('xb')as stream:
        stream.write(raw);stream.flush();os.fsync(stream.fileno())
    store=B.Store(bundle,output,dict(schema=SCHEMA,root_document=dict(file='root_document.json',sha256=sha256(raw).hexdigest()),root=manifest['root'],nodes=[]))
    installed=deepcopy(store.manifest);old_rounds={};old_terminal_hashes={}
    for entry in manifest['nodes']:
        path=source.parent/entry['file'];assert digest(path)==entry['sha256']
        record=json.loads(path.read_text());old_rounds[entry['id']]=len(record['rounds'])
        if 'terminal'in record:old_terminal_hashes[entry['id']]=sha256(json.dumps(record['terminal'],sort_keys=True).encode()).hexdigest()
        copied=store.put_immutable(entry['id'],record)
        if 'split'in entry:copied['split']=deepcopy(entry['split'])
        installed['nodes'].append(copied)
    assert digest(source)==before
    store.install(installed)
    bundle['A'].write_json(output/'INPUT_EXACT_REPLAY.json',report)
    bundle['A'].write_json(output/'DISCOVERY_SOURCE_BINDING.json',dict(
        source_manifest=str(source),source_manifest_sha256=before,checkpoint_sha256=B.CHECKPOINT_SHA,
        driver_sha256=digest(__file__),base_numeric_core_sha256=BASE_SHA,atomic_helper_sha256=B.ATOMIC_SHA,
        complete_wrapper_binding_sha256=COMPLETE_BINDING,corner_binding_sha256=CORNER_BINDING,guard_binding_sha256=GUARD_BINDING,
        root_id=bundle['P'].ROOT_ID,mask='011/00',radius_mode='strict',physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
        extra_row_family='accepted four-product unit-frame original corners',new_auxiliary_variables=0,
        legacy_geometry_context_imported=False,lost_search_suffix_recovered=False,
        numeric_results_are_only_proposals=True,original_cell_credit=0,whole_mask_credit=0))
    bundle['source_round_counts']=old_rounds;bundle['source_terminal_hashes']=old_terminal_hashes
    return store,report

def parameters_from_record(record):
    result=[];names=set()
    for rr in record['rounds']:
        for row in rr['printed_rows']:
            name=row['name']
            if not name.startswith(PREFIX)or name in names:continue
            names.add(name);fields=name[len(PREFIX):].split('_');assert len(fields)==9
            i,e,t=map(int,fields[:3]);px,py=map(F,fields[3:5]);bits=tuple(map(int,fields[5:]))
            result.append((i,e,t,px,py,bits))
    return result

def diagnostic(bundle,store,node,extra,stage,phase,rows):
    number=bundle['diagnostic_counter'];bundle['diagnostic_counter']+=1
    value=dict(node=node,extra_round=extra,phase_stage=stage,row_count=len(rows),
        numerical_only=True,ignored_by_exact_verifier=True,phase=phase)
    bundle['A'].write_json(store.folder/'diagnostics'/f'phase_{number:06d}.json',value)

def phase_with_corner_cuts(bundle,store,node,extra,state,current,rows,bounds,parameters,args,backend):
    names={row[2]for row in rows}
    for stage in range(args.corner_passes+1):
        solver=backend(rows,bounds,args.lp_seconds)
        phase=solver.phase()
        diagnostic(bundle,store,node,extra,stage,phase,rows)
        if not phase['optimal']:return solver,phase
        # Return before appending rows on the last allowed pass. Every returned
        # dual therefore belongs to precisely the final current row list.
        if B.reserve_from_weights(rows,bounds,B.weights_from_dual(phase['dual']))is not None:return solver,phase
        if stage==args.corner_passes:return solver,phase
        added=[];new_parameters=[]
        for parameter,violation in bundle['suggest'](phase['point'],current,bundle['corner'],tolerance=1e-6):
            row=bundle['corner'].row_on_current(current,parameter)
            if row[2]in names:continue
            names.add(row[2]);added.append(row);new_parameters.append(parameter)
        if not added:return solver,phase
        literals=[dict(index=len(rows)+k,name=row[2],coefficients=[[j,str(v)]for j,v in row[0]],rhs=str(row[1]))for k,row in enumerate(added)]
        rebuilt,checked_bounds,checked_state=bundle['exact'].rebuild(state,literals)
        assert checked_bounds==bounds and checked_state==current
        assert rebuilt=={len(rows)+k:row for k,row in enumerate(added)}
        rows.extend(added);parameters.extend(new_parameters)
        print(json.dumps(dict(node=node,event='VALIDATED_CORNER_PHASE_ROWS',rows=len(added),total_rows=len(rows),next_phase=stage+1)),flush=True)
    raise AssertionError('Every phase iteration returns or solves its newly appended rows.')

def propose_guard(bundle,current):
    for middle,mode in ((2,'C'),(7,'HI'),(8,'HI')):
        guard=bundle['guard'].evaluate(current,bundle['document'],middle,mode)
        if guard['status']=='PASS_STRICT011_UNIVERSAL021_GUARD':
            return dict(kind=bundle['E'].TERMINAL_KIND,attachment_binding_sha256=GUARD_BINDING,guard=guard)
    return None

def search_node(bundle,store,node,args,backend):
    P,I,G=[bundle[name]for name in('P','I','G')]
    record=store.record(node);initial=P.parse_state(record['initial'])
    audit,state=G.check_record(record,initial,I.Adapter());assert state is not None
    parameters=parameters_from_record(record);point=None
    for extra in range(args.rounds+1):
        rows,bounds,current,terminal=bundle['corner'].collect(state,parameters,seed_midpoints=True)
        if terminal is None and args.enable_guards:terminal=propose_guard(bundle,current)
        if terminal is not None:
            assert I.Adapter.verify_early_terminal(state,terminal)
            record=dict(record,status='CANDIDATE_CLOSED',terminal=terminal);record.pop('final',None)
            store.update_record(node,record)
            print(json.dumps(dict(node=node,event='EXACT_GUARDED_OR_INTERVAL_EXCLUSION',kind=terminal['kind'])),flush=True)
            return None,None
        solver,phase=phase_with_corner_cuts(bundle,store,node,extra,state,current,rows,bounds,parameters,args,backend)
        if not phase['optimal']:
            print(json.dumps(dict(node=node,event='LP_NO_CONCLUSION',status=phase)),flush=True)
            return state,None
        point=phase['point']
        certificate=B.reserve_from_weights(rows,bounds,B.weights_from_dual(phase['dual']))
        if certificate is not None:
            G.replay_reserve(I.Adapter(),state,certificate)
            record=dict(record,status='CANDIDATE_CLOSED',terminal_state=P.state_view(state),terminal=certificate);record.pop('final',None)
            store.update_record(node,record)
            print(json.dumps(dict(node=node,event='EXACT_CONDITIONAL_EXCLUSION',reserve=certificate['reserve'])),flush=True)
            return None,None
        if extra==args.rounds:break
        rr,after,terminal=B.bound_round(bundle,state,rows,bounds,current,solver,args.objectives,len(record['rounds']))
        if rr is None:break
        record=deepcopy(record);record['rounds'].append(rr)
        if terminal is not None:record.update(status='CANDIDATE_CLOSED',terminal=terminal);record.pop('final',None)
        else:record['final']=P.state_view(after)
        store.update_record(node,record)
        print(json.dumps(dict(node=node,event='EXACT_BOUND_ROUND',proposals=len(rr['proposals']),rows=len(rr['printed_rows']),rounds=len(record['rounds']))),flush=True)
        if terminal is not None:return None,None
        state=after
    return state,point

def corner_weight_audit(bundle,store):
    uses=[]
    for entry in store.manifest['nodes']:
        node=entry['id'];record=store.record(node)
        for number,rr in enumerate(record['rounds']):
            if number<bundle['source_round_counts'].get(node,0):continue
            rows={row['index']:row for row in rr['printed_rows']}
            for proposal in rr['proposals']:
                for index,weight in proposal['weights']:
                    if rows[index]['name'].startswith(PREFIX):
                        assert type(weight)is int and weight>0
                        uses.append(dict(node=node,round=number,row=index,name=rows[index]['name'],weight=weight,
                                         objective=proposal['objective'],literal_sha256=sha256(json.dumps(rows[index],sort_keys=True).encode()).hexdigest()))
        terminal=record.get('terminal')
        if terminal and terminal.get('kind')=='positive_exact_reserve':
            terminal_hash=sha256(json.dumps(terminal,sort_keys=True).encode()).hexdigest()
            if terminal_hash==bundle['source_terminal_hashes'].get(node):continue
            rows={row['index']:row for row in terminal['rows']}
            for index,weight in terminal['weights']:
                if rows[index]['name'].startswith(PREFIX):
                    assert type(weight)is int and weight>0
                    uses.append(dict(node=node,terminal=True,row=index,name=rows[index]['name'],weight=weight,
                        literal_sha256=sha256(json.dumps(rows[index],sort_keys=True).encode()).hexdigest()))
    return dict(new_positive_corner_weight_uses=len(uses),weights_denominator=B.DENOMINATOR,uses=uses,
                inherited_input_round_uses_excluded=True,diagnostic_points_used_as_proof=False)

def run(args,backend=NumericalLP):
    started=time.monotonic();bundle=bootstrap(args)
    store,input_report=initialize(bundle,args.input,args.output)
    frontier=list(input_report['open_leaf_ids'])
    while frontier:
        node=frontier.pop(0);state,point=search_node(bundle,store,node,args,backend)
        if state is None or point is None:continue
        if len(state['path'])>=args.max_depth:continue
        kind,argument,cut=B.choose_split(state,point)
        count=2 if kind=='angle'else 4 if kind=='proxy'else 8
        if len(store.manifest['nodes'])+count>args.max_nodes:continue
        children=store.split(node,kind,argument,cut);frontier=children+frontier
        print(json.dumps(dict(event='COMPLETE_CLOSED_SPLIT',node=node,kind=kind,children=children,nodes=len(store.manifest['nodes']))),flush=True)
    output=Path(args.output).resolve()
    command=[sys.executable,'-B','-S',str(bundle['complete_folder']/'verify_strengthened_complete_tree.py'),
        str(output/'manifest.json'),str(output/'EXACT_REPLAY.json'),'--workspace',str(bundle['checkpoint']/'dependencies/workspace'),
        '--model-folder',str(bundle['checkpoint']/B.MODEL_NAME),'--corner-folder',str(bundle['corner_folder']),
        '--guard-folder',str(bundle['guard_folder']),'--scalar-output-folder',str(output/'COLD_FRESH_SCALAR')]
    with(output/'EXACT_REPLAY.log').open('x')as log:subprocess.run(command,check=True,stdout=log,stderr=subprocess.STDOUT)
    report=json.loads((output/'EXACT_REPLAY.json').read_text())
    assert report['manifest_sha256']==digest(output/'manifest.json')
    assert report['root_id']==bundle['P'].ROOT_ID and report['mask']=='011/00'and report['radius_mode']=='strict'
    assert (report['physical_originals'],report['original_corners'],report['original_pairs'],report['marked_cones'])==(9,36,36,5)
    audit=corner_weight_audit(bundle,store)
    actual_backend=backend is NumericalLP
    actual_gate=actual_backend and audit['new_positive_corner_weight_uses']>0
    audit.update(complete_exact_report_sha256=digest(output/'EXACT_REPLAY.json'),
                 actual_LP_backend_used=actual_backend,actual_positive_corner_weight_gate_passed=actual_gate)
    bundle['A'].write_json(output/'CORNER_WEIGHT_USE_AUDIT.json',audit)
    for path,expected in bundle['extra_source_hashes'].items():assert digest(path)==expected
    summary=dict(status='PASS_ACTUAL_WEIGHTED_CORNER_DISCOVERY_CHECKPOINT'if actual_gate else'PASS_EXACT_CHECKPOINT_CORNER_ACTUAL_USE_NOT_OBSERVED',
        root_id=bundle['P'].ROOT_ID,mask='011/00',radius_mode='strict',nodes=report['nodes'],
        excluded_leaves=report['excluded_leaves'],open_leaves=report['open_leaves'],
        actual_LP_backend_used=actual_backend,new_positive_corner_weight_uses=audit['new_positive_corner_weight_uses'],
        actual_positive_corner_weight_gate_passed=actual_gate,conditional_terminals=report['strengthened_attachment']['conditional_terminals'],
        fresh_scalar_replayed_in_cold_gate=report['strengthened_attachment']['fresh_scalar_replay']is not None,
        whole_mask_proved_by_exact_tree=report['whole_mask_proved'],automatic_mask_credit=0,
        exact_report_sha256=digest(output/'EXACT_REPLAY.json'),manifest_sha256=digest(output/'manifest.json'),
        driver_sha256=digest(__file__),seconds=time.monotonic()-started)
    bundle['A'].write_json(output/'DISCOVERY_COMPLETION.json',summary)
    print(json.dumps(summary),flush=True)
    return summary

def main():
    parser=argparse.ArgumentParser()
    for flag in('checkpoint','complete-folder','corner-folder','guard-folder','input','output'):
        parser.add_argument('--'+flag,type=Path,required=True)
    parser.add_argument('--source-binding',required=True)
    parser.add_argument('--rounds',type=int,default=1);parser.add_argument('--objectives',type=int,default=108)
    parser.add_argument('--max-nodes',type=int,default=1);parser.add_argument('--max-depth',type=int,default=0)
    parser.add_argument('--corner-passes',type=int,default=2);parser.add_argument('--lp-seconds',type=float,default=2)
    parser.add_argument('--enable-guards',action='store_true')
    parser.add_argument('--require-positive-corner-weight',action='store_true')
    args=parser.parse_args()
    assert 0<=args.rounds<=20 and 1<=args.objectives<=252
    assert args.max_nodes>=1 and args.max_depth>=0 and 0<=args.corner_passes<=4 and args.lp_seconds>0
    _,hashes=verify_driver_binding(args.source_binding)
    summary=run(args)
    assert all(digest(path)==expected for path,expected in hashes.items())
    if args.require_positive_corner_weight and not summary['actual_positive_corner_weight_gate_passed']:raise SystemExit(3)

if __name__=='__main__':main()

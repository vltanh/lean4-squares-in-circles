#!/usr/bin/env python3
"""Source/local conditional controls; no actual theorem-cover use or solver.

Valid height candidates are prepared, not globally replayed here. The new
complete checker is exercised only on no-height roots and rejection cases.
Its first successful height union still requires the fresh scalar gate.
"""
if not __debug__:
    raise RuntimeError('Exact height preparation rejects optimized Python.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import argparse
import ast
import errno
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def normalize(objective):return tuple(sorted((column,F(value))for column,value in objective))

def main():
    parser=argparse.ArgumentParser()
    for name in('foundation','corner-folder','guard-folder','height-folder','output-folder','scalar-parent'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();out=args.output_folder.resolve();out.mkdir(parents=True,exist_ok=False)
    scalar_parent=args.scalar_parent.resolve();scalar_parent.mkdir(parents=True,exist_ok=False)
    D=load('height_preparation_discovery',HERE/'height_discovery_attachment.py')
    T=load('height_preparation_complete_gate',HERE/'verify_height_complete_tree.py')
    source_hashes={str(path):digest(path)for path in HERE.glob('*.py')}
    ctx=D.Context(args.foundation,args.corner_folder,args.guard_folder,args.height_folder,
        scalar_parent/'conditional_guard_scalar',scalar_parent/'conditional_height_scalar')
    B,H,P,G= D.B,D.H,ctx.bundle['P'],ctx.bundle['G']
    root=P.fresh_state();root_view=P.state_view(root)
    def complete_verify(manifest,label,height_output=None):
        return T.verify(manifest,args.foundation/'dependencies/workspace',args.foundation/B.MODEL_NAME,
            args.corner_folder,args.guard_folder,scalar_parent/(label+'_guard'),args.height_folder,
            height_output if height_output is not None else scalar_parent/(label+'_height'))
    baseline=D.FreshHeightStore(ctx,out/'baseline_no_height')
    root_report=complete_verify(baseline.folder/'manifest.json','baseline')
    assert(root_report['nodes'],root_report['excluded_leaves'],root_report['open_leaves'])==(1,0,1)
    assert root_report['height_cover_attachment']['complete_height_unions']==0
    assert root_report['height_cover_attachment']['fresh_scalar_replay']is None
    write(out/'BASELINE_NO_HEIGHT_COMPLETE_REPLAY.json',root_report)

    # This is a prepared first-use candidate, with four locally checked exact
    # consequences. No complete height-cover verifier is run on it here.
    first=D.FreshHeightStore(ctx,out/'first_height_cover_candidate')
    height_children=first.split(0,H.HEIGHT_KIND)
    assert height_children==[1,2,3,4]
    local_rounds=[]
    for branch,node in enumerate(height_children):
        record=first.record(node);expected=first.expected_context(node)
        assert record['initial']==root_view and expected['branch']==branch
        audit,state=first.checked_final(node);assert state==root
        rows,bounds,current,terminal=ctx.collect(state,expected,seed_midpoints=True)
        assert terminal is None
        height_index=next(k for k,row in enumerate(rows)if row[2]==H.ROW_PREFIX+str(branch))
        if branch==0:target=[(7,-1),(3,1)];weights={height_index:F(1)}
        elif branch==3:target=[(7,1),(3,-1)];weights={height_index:F(1)}
        else:
            sign=-1 if branch==1 else 1
            target=[(5,sign)];weights={height_index:F(1,2)}
            for column in(3,7):
                index=next(k for k,row in enumerate(rows)if row[2]==f'strict011v2:bound:{column}:{sign}')
                assert rows[index][0]==((column,F(sign)),)
                weights[index]=F(1,2)
        class HandWeights:
            calls=0
            def maximum(self,objective):
                self.calls+=1
                if normalize(objective)!=normalize(target):return None
                return [-float(weights.get(k,F(0)))for k in range(len(rows))]
        hand=HandWeights()
        rr,after,terminal=B.bound_round(ctx.conditional_bundle(expected),state,rows,bounds,current,hand,252,0)
        assert hand.calls==252 and rr is not None and terminal is None and len(rr['proposals'])==1
        proposal=rr['proposals'][0]
        assert proposal['residual_coefficients']==[]and proposal['residual_correction']=='0'
        assert any(k==height_index and weight>0 for k,weight in proposal['weights'])
        record=deepcopy(record);record['rounds'].append(rr);record['final']=P.state_view(after)
        checked,final=first.update_record(node,record);assert final==after
        local_rounds.append(dict(branch=branch,node=node,hand_chosen_weights=True,
            conditional_arithmetic=checked,objective=proposal['objective'],upper=proposal['upper'],
            weights=proposal['weights'],printed_rows=rr['printed_rows'],residual_correction='0',
            full_caller_coverage_or_scalar_gate_claimed=False))
    assert ctx.manager.scalar_audit is None and ctx.manager.unions==[]
    write(out/'FOUR_LOCAL_CONDITIONAL_HEIGHT_BOUND_ROUNDS.json',dict(
        status='PASS_LOCAL_CONDITIONAL_ARITHMETIC_ONLY_COMPLETE_HEIGHT_COVER_GATE_PENDING',
        rounds=local_rounds,real_optimizer_called=False,fresh_scalar_replayed=False,
        complete_height_cover_replayed=False,original_cell_credit=0,whole_mask_credit=0))

    # All old split methods remain the accepted Store implementation, with a
    # fixed inherited context supplied separately to its adapter constructor.
    mixed=D.FreshHeightStore(ctx,out/'mixed_height_old_cover_candidate')
    h=mixed.split(0,H.HEIGHT_KIND);p=mixed.split(h[0],'proxy',(0,1))
    s=mixed.split(p[1],'sat',(0,8));a=mixed.split(s[0],'angle',3,F(1,2))
    assert len(mixed.manifest['nodes'])==19 and len(h)==len(p)==4 and len(s)==8 and len(a)==2
    record=mixed.record(p[0]);audit,state=mixed.checked_final(p[0]);scope=mixed.expected_context(p[0])
    rows,bounds,current,terminal=ctx.collect(state,scope);assert terminal is None
    names={'strict011v2:inset_tangent:0:1','strict011v2:inset_tangent:1:1',
           'strict011v2:mask:0:1:0','strict011v2:proxy:0:1:0:-1'}
    weights=[[k,B.DENOMINATOR//4]for k,row in enumerate(rows)if row[2]in names]
    assert len(weights)==4
    reserve=B.reserve_from_weights(rows,bounds,weights);assert reserve is not None and reserve['reserve']=='1/2'
    record=dict(record,status='CANDIDATE_CLOSED',terminal_state=P.state_view(state),terminal=reserve);record.pop('final')
    mixed.update_record(p[0],record)
    conditional_nodes=[]
    for entry in mixed.manifest['nodes']:
        audit,state=mixed.checked_final(entry['id'])
        conditional_nodes.append(dict(node=entry['id'],height_context=mixed.expected_context(entry['id']),arithmetic=audit))
    assert sum(item['arithmetic']['status']=='PASS_EXCLUDED_PHYSICAL_DOMAIN'for item in conditional_nodes)==1
    write(out/'MIXED_LOCAL_CONDITIONAL_NODE_AUDITS.json',dict(
        status='PASS_LOCAL_NODE_AND_INHERITED_CONTEXT_CONTROLS_ONLY_GLOBAL_COVER_GATE_PENDING',
        nodes=conditional_nodes,declared_nodes=19,local_excluded_leaves=1,
        real_optimizer_called=False,fresh_scalar_replayed=False,complete_height_cover_replayed=False))

    rejected=[]
    def reject(name,callback,errors=(AssertionError,KeyError,ValueError,TypeError,RuntimeError,OSError)):
        try:callback()
        except errors:rejected.append(name)
        else:raise AssertionError('Invalid height preparation accepted: '+name)
    split=deepcopy(first.manifest['nodes'][0]['split'])
    for mode in('missing','duplicate_choice','duplicate_node','parent_node','parent_state','binding','literal','boolean_choice'):
        bad=deepcopy(split)
        if mode=='missing':bad['children'].pop()
        if mode=='duplicate_choice':bad['children'][3]['branch']=0
        if mode=='duplicate_node':bad['children'][3]['node']=1
        if mode=='parent_node':bad['parent_node']=9
        if mode=='parent_state':bad['parent_state_sha256']='0'*64
        if mode=='binding':bad['cover_binding_sha256']='0'*64
        if mode=='literal':bad['cover_literal']['branches'][0]['threshold']='1/5'
        if mode=='boolean_choice':bad['children'][0]['branch']=False
        reject('height_union:'+mode,lambda bad=bad:ctx.manager.validate_union(0,root,None,bad))
    reordered=deepcopy(split);reordered['children'].reverse()
    successors=ctx.manager.validate_union(0,root,None,reordered)
    assert [value[2]['branch']for value in successors]==[3,2,1,0]
    before=(first.folder/'manifest.json').read_bytes()
    reject('second_height_union_on_path',lambda:first.split(height_children[0],H.HEIGHT_KIND))
    assert(first.folder/'manifest.json').read_bytes()==before
    scope=first.expected_context(1);record=first.record(1)
    for field,value in(('branch',1),('origin_node',9),('parent_state_sha256','0'*64),
                       ('cover_binding_sha256','0'*64),('caller_root_document_sha256','0'*64),('branch',False)):
        bad=deepcopy(record);bad['height_context'][field]=value
        reject('record_context:'+field+':'+str(value),lambda bad=bad:ctx.manager.check_record_envelope(bad,scope))
    bad=deepcopy(record);bad.pop('height_context')
    reject('missing_record_context',lambda:ctx.manager.check_record_envelope(bad,scope))
    reject('selected_context_at_root',lambda:ctx.manager.check_record_envelope(record,None))
    reject('active_child_before_fresh_cover_gate',lambda:ctx.manager.assert_active_context(scope))
    raw=ctx.manager.height_row(scope);printed=dict(index=9999,**raw)
    expected_row=ctx.manager.verify_height_literal(printed,scope)
    assert expected_row[1]==F(-21,100)
    reject('height_row_without_selected_context',lambda:ctx.manager.verify_height_literal(printed,None))
    for mode in('other_branch','coefficient','rhs','boolean_index'):
        bad=deepcopy(printed)
        if mode=='other_branch':bad.update(ctx.manager.height_row(first.expected_context(2)))
        if mode=='coefficient':bad['coefficients'][0][1]='0'
        if mode=='rhs':bad['rhs']='-1/5'
        if mode=='boolean_index':bad['index']=True
        reject('height_literal:'+mode,lambda bad=bad:ctx.manager.verify_height_literal(bad,scope))
    reject('height_row_adapter_without_context',lambda:ctx.manager.adapter(None).rebuild(root,[printed]))
    # Narrowing an expected child remains a failure in the unchanged generic
    # initial-state equality check, independent of the theorem cover gate.
    narrow=deepcopy(first.record(2));narrow['initial']['positions'][0][0]='-1'
    reject('arbitrary_narrowed_height_child',lambda:G.check_record(narrow,root,ctx.manager.adapter(first.expected_context(2))))
    for node in(p[0],p[1],s[0],a[0],a[1]):
        rec=mixed.record(node);assert rec['height_context']==mixed.expected_context(node)
        bad=deepcopy(rec);bad['height_context']=None
        reject('lost_inheritance_at_old_child:'+str(node),lambda bad=bad,node=node:ctx.manager.check_record_envelope(bad,mixed.expected_context(node)))

    # Atomic failure during the new union retains the exact old whole root.
    failure=D.FreshHeightStore(ctx,out/'height_union_atomic_failure')
    saved=(failure.folder/'manifest.json').read_bytes();old_manifest=deepcopy(failure.manifest)
    old_map=deepcopy(failure._expected_contexts);original_write=ctx.bundle['A'].write_json
    def injected(path,value):
        if Path(path)==failure.folder/'manifest.json':raise OSError(errno.ENOSPC,'injected height-union manifest failure')
        return original_write(path,value)
    ctx.bundle['A'].write_json=injected
    try:reject('height_union_ENOSPC_before_manifest_replace',lambda:failure.split(0,H.HEIGHT_KIND),(OSError,))
    finally:ctx.bundle['A'].write_json=original_write
    assert(failure.folder/'manifest.json').read_bytes()==saved and failure.manifest==old_manifest
    assert failure._expected_contexts==old_map
    retained=complete_verify(failure.folder/'manifest.json','failure')
    assert(retained['nodes'],retained['excluded_leaves'],retained['open_leaves'])==(1,0,1)
    write(out/'ATOMIC_FAILURE_RETAINED_NO_HEIGHT_REPLAY.json',retained)

    # Reject an attempted complete height run with an existing scalar folder.
    # This never executes the scalar checker and produces no accepted report.
    blocked=scalar_parent/'existing_height_scalar';blocked.mkdir()
    write(blocked/'SCALAR_REPLAY.json',dict(status='untrusted old header'))
    reject('old_scalar_folder_cannot_admit_height_cover',lambda:complete_verify(first.folder/'manifest.json','blocked',blocked))
    optimized=subprocess.run([sys.executable,'-O','-B','-S',str(HERE/'verify_height_complete_tree.py'),'--help'],capture_output=True,text=True)
    assert optimized.returncode!=0 and 'rejects optimized Python'in optimized.stderr
    assert ctx.manager.scalar_audit is None and ctx.manager.unions==[]
    assert not(scalar_parent/'conditional_height_scalar').exists()
    assert not(scalar_parent/'conditional_guard_scalar').exists()
    assert source_hashes=={str(path):digest(path)for path in HERE.glob('*.py')}
    assert not any(name.split('.')[0]in{'numpy','scipy','sympy','z3','highspy'}for name in sys.modules)
    for name in('height_context_adapter.py','height_discovery_attachment.py','verify_height_complete_tree.py'):
        source=ast.parse((HERE/name).read_text())
        assert not any(isinstance(node,ast.Call)and isinstance(node.func,ast.Attribute)
            and node.func.attr in{'linprog','solve','phase','maximum'}for node in ast.walk(source))
    report=dict(status='PASS_PREPARED_C_HEIGHT_TREE_AND_LOCAL_CONDITIONAL_CONTROLS_NO_ACTUAL_COVER_USE',
        local_source_sha256=source_hashes,height_binding_sha256=H.HEIGHT_BINDING,
        fresh_root_no_height_complete_replays=2,first_use_candidate_nodes=5,
        local_exact_height_bound_rounds=4,local_exact_height_deductions=4,
        local_height_residual_corrections=['0']*4,
        mixed_candidate_nodes=19,old_unions_prepared=dict(proxy=1,sat=1,angle=1),height_unions_prepared=1,
        root_context_exactly_null=True,base_state_dictionaries_unchanged=True,
        ordinary_child_contexts_checked=True,parent_node_and_final_state_hash_bound=True,
        fresh_scalar_or_optimizer_called=False,global_height_cover_replayed=False,
        preparation_damages_rejected=len(rejected),rejected_controls=rejected,
        optimized_python_rejected=True,atomic_failure_preserved_exact_old_root=True,
        first_actual_cover_gate_still_pending=True,original_cell_credit=0,whole_mask_credit=0)
    write(out/'PREPARATION_CONTROLS.json',report)
    print(json.dumps(dict(status=report['status'],damages=len(rejected),report_sha256=digest(out/'PREPARATION_CONTROLS.json'))))
if __name__=='__main__':main()

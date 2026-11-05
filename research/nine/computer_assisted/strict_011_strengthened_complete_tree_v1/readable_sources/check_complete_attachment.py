#!/usr/bin/env python3
"""Whole-root 4/8/2 fixtures for the prepared strengthened exact verifier.

The corner weights are deliberately constructed rational arithmetic controls,
not LP discoveries. No accepted theorem terminal or scalar replay is claimed.
"""
if not __debug__:
    raise RuntimeError('Exact complete-attachment controls reject optimized Python.')
import argparse
import ast
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
SCHEMA='fresh_full_strict011_strengthened_representative_tree_v1'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def row_view(row,index):
    co,rhs,name=row
    return dict(index=index,name=name,coefficients=[[k,str(v)]for k,v in co],rhs=str(rhs))
def function_asts(path):
    return {node.name:ast.dump(node,include_attributes=False)for node in ast.walk(ast.parse(path.read_text()))if isinstance(node,ast.FunctionDef)}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--corner-folder',type=Path,required=True);parser.add_argument('--guard-folder',type=Path,required=True)
    parser.add_argument('--output-folder',type=Path,required=True);args=parser.parse_args()
    foundation=args.foundation.resolve();corners=args.corner_folder.resolve();guards=args.guard_folder.resolve()
    output=args.output_folder.resolve();output.mkdir(parents=True,exist_ok=False)
    model_folder=foundation/'strict_011_representative_root_v1'
    workspace=foundation/'dependencies/workspace'
    T=load('prepared_strict011_strengthened_complete_tree',HERE/'verify_strengthened_complete_tree.py')
    P=load('prepared_strict011_corner_fixture_producer',corners/'strict011_four_product_rows.py')
    GP=load('prepared_strict011_guard_fixture_producer',guards/'strict021_guards.py')
    G=load('prepared_strict011_frozen_arithmetic',workspace/'b_work/independent_physical_sat_replay.py')
    document=json.loads((model_folder/'snapshots/ROOT_DOCUMENT.json').read_text())
    context=P.Context(foundation,document)
    root=context.model.fresh_state()
    same=('walk','local_file','digest','read_module','pin')
    original=function_asts(HERE/'accepted_base_wrapper.py');extended=function_asts(HERE/'verify_strengthened_complete_tree.py')
    assert all(original[name]==extended[name]for name in same)
    assert digest(HERE/'accepted_base_wrapper.py')=='c66b6e08616b49623fb6253c28ab2fb6aba1c5d70e0d645ae56b019a5a7bacae'
    sources={name:digest(HERE/name)for name in ('strengthened_adapter.py','verify_strengthened_complete_tree.py',
             'build_strengthened_wrapper.py','accepted_base_wrapper.py','WRAPPER_TRANSFORMATION.json','check_complete_attachment.py')}

    rows,bounds,current,terminal=context.collect(root,seed_midpoints=True)
    assert terminal is None
    chosen=next(row for row in rows if row[2].startswith('physical_unit_four_corner_'))
    co=[F(0)]*len(bounds)
    for column,value in chosen[0]:co[column]+=value
    co[45]-=1
    correction=sum(b*abs(c)for b,c in zip(bounds,co));proved=chosen[1]+correction;upper=G.ceiling_grid(proved)
    after=deepcopy(current);scalar=[list(box)for box in current['scalar']]
    scalar[27][1]=min(scalar[27][1],upper);after['scalar']=tuple(map(tuple,scalar))
    assert all(a<=b for a,b in after['scalar'])
    proposal=dict(kind='scalar',key=45,sign=1,objective=[[45,1]],weights=[[0,G.DENOMINATOR]],
        summed_rhs=str(chosen[1]),residual_coefficients=[[k,str(v)]for k,v in enumerate(co)if v],
        residual_correction=str(correction),proved_upper=str(proved),upper=str(upper))
    rr=dict(before=G.state_view(root),printed_rows=[row_view(chosen,0)],propagated=G.state_view(current),
        absolute_variable_bounds=list(map(str,bounds)),proposals=[proposal],physical_frame_inferences=[],after=G.state_view(after))
    root_record=dict(initial=G.state_view(root),rounds=[rr],status='OPEN',final=G.state_view(after))
    def open_record(state):return dict(initial=G.state_view(state),rounds=[],status='OPEN',final=G.state_view(state))
    def negative_AB_record(state):
        rows,bounds,now,early=context.collect(state)
        assert early is None
        names=('strict011v2:inset_tangent:0:1','strict011v2:inset_tangent:1:1',
               'strict011v2:mask:0:1:0','strict011v2:proxy:0:1:0:-1')
        selected=[next(row for row in rows if row[2]==name)for name in names]
        coefficients=[F(0)]*len(bounds);rhs=F(0)
        for row in selected:
            rhs+=row[1]/4
            for column,value in row[0]:coefficients[column]+=value/4
        payment=sum(b*abs(c)for b,c in zip(bounds,coefficients));reserve=-rhs-payment
        assert reserve==F(1,2)and not any(coefficients)
        terminal=dict(kind='positive_exact_reserve',rows=[row_view(row,k)for k,row in enumerate(selected)],
            weights=[[k,G.DENOMINATOR//4]for k in range(4)],absolute_variable_bounds=list(map(str,bounds)),
            weighted_coefficients=list(map(str,coefficients)),weighted_rhs=str(rhs),reserve=str(reserve))
        return dict(initial=G.state_view(state),rounds=[],status='CANDIDATE_CLOSED',
                    terminal_state=G.state_view(state),terminal=terminal)
    def tree(kind):
        records={0:deepcopy(root_record)};entries={0:dict(id=0)};states={0:after};nextid=1
        def split(node,splitkind,pair=None,original=None,cut=None):
            nonlocal nextid
            children=[]
            choices=list(product(tuple(pair),(0,1),(-1,1)))if splitkind=='sat'else list(product((0,1),(-1,1)))if splitkind=='proxy'else(0,1)
            for choice in choices:
                child=nextid;nextid+=1
                if splitkind=='angle':state=context.model.angle_child(states[node],original,F(cut),choice)
                else:state=context.model.physical_child(states[node],splitkind,pair,choice)
                states[child]=state;entries[child]=dict(id=child)
                records[child]=negative_AB_record(state)if splitkind=='proxy'and pair==(0,1)and choice==(0,-1)else open_record(state)
                children.append(dict(side=choice,node=child)if splitkind=='angle'else dict(choice=list(choice),node=child))
            if splitkind=='angle':entries[node]['split']=dict(kind='angle',original=original,cut=str(F(cut)),children=children)
            else:entries[node]['split']=dict(kind=splitkind,pair=list(pair),children=children)
            return [x['node']for x in children]
        if kind=='proxy_four':split(0,'proxy',pair=(0,1))
        elif kind=='sat_eight':split(0,'sat',pair=(0,8))
        elif kind=='angle_two':split(0,'angle',original=0,cut='0')
        elif kind=='mixed':
            proxies=split(0,'proxy',pair=(0,1));owned=split(proxies[1],'sat',pair=(0,8))
            split(owned[0],'angle',original=0,cut='0')
        else:assert kind=='root_corner_open'
        return records,entries
    def materialize(name,records,entries,doc=document,schema=SCHEMA):
        folder=output/name;folder.mkdir()
        raw=json.dumps(doc,indent=2).encode()+b'\n'
        # Preserve exact pinned bytes for the undamaged complete caller.
        if doc==document:raw=(model_folder/'snapshots/ROOT_DOCUMENT.json').read_bytes()
        with (folder/'root_document.json').open('xb')as stream:stream.write(raw)
        manifest=dict(schema=schema,root=0,root_document=dict(file='root_document.json',sha256=digest(folder/'root_document.json')),nodes=[])
        for node,record in sorted(records.items()):
            file='node_'+str(node)+'.json';write(folder/file,record)
            entry=deepcopy(entries[node]);entry.update(file=file,sha256=digest(folder/file));manifest['nodes'].append(entry)
        write(folder/'manifest.json',manifest)
        return folder
    def verify(folder):
        return T.verify(folder/'manifest.json',workspace,model_folder,corners,guards,folder/'fresh_scalar_must_not_exist')

    fixtures={};source_trees={}
    expected={'root_corner_open':(1,0,1,{}),'proxy_four':(5,1,3,{'proxy':1}),
              'sat_eight':(9,0,8,{'sat':1}),'angle_two':(3,0,2,{'angle':1}),
              'mixed':(15,1,11,{'proxy':1,'sat':1,'angle':1})}
    for kind,counts in expected.items():
        records,entries=tree(kind);source_trees[kind]=(records,entries)
        folder=materialize(kind,records,entries);report=verify(folder)
        assert (report['nodes'],report['excluded_leaves'],report['open_leaves'],report['complete_unions'])==counts
        assert report['complete']is False and report['whole_mask_proved']is False
        assert report['exact_totals']['rounds']==report['exact_totals']['deductions']==1
        assert report['strengthened_attachment']['conditional_terminals']==0
        assert report['strengthened_attachment']['fresh_scalar_replay']is None
        assert not (folder/'fresh_scalar_must_not_exist').exists()
        write(folder/'EXACT_REPLAY.json',report)
        fixtures[kind]={key:report[key]for key in ('status','nodes','excluded_leaves','open_leaves','complete_unions','exact_totals')}
    rejected=[]
    def reject(name,callback):
        try:callback()
        except (AssertionError,ValueError,TypeError,KeyError,IndexError,RuntimeError):rejected.append(name)
        else:raise AssertionError('Damaged complete-tree fixture accepted: '+name)
    def damage(name,kind,change,doc=document,schema=SCHEMA):
        records,entries=deepcopy(source_trees[kind]);change(records,entries)
        folder=materialize('damaged_'+name,records,entries,doc,schema)
        reject(name,lambda:verify(folder))
        assert not (folder/'fresh_scalar_must_not_exist').exists()
    damage('missing_proxy_child','proxy_four',lambda r,e:e[0]['split']['children'].pop())
    damage('duplicate_sat_choice','sat_eight',lambda r,e:e[0]['split']['children'][1].update(choice=e[0]['split']['children'][0]['choice']))
    damage('missing_angle_side','angle_two',lambda r,e:e[0]['split']['children'].pop())
    damage('narrowed_child_initial','proxy_four',lambda r,e:r[2]['initial']['positions'][0].__setitem__(0,'0'))
    damage('changed_corner_rhs','root_corner_open',lambda r,e:r[0]['rounds'][0]['printed_rows'][0].update(rhs='-100'))
    damage('unpaid_residual','root_corner_open',lambda r,e:r[0]['rounds'][0]['proposals'][0].update(residual_correction='0'))
    damage('old_schema','root_corner_open',lambda r,e:None,schema='fresh_full_strict011_representative_complete_tree_v1')
    bad_doc=deepcopy(document);bad_doc['exact_mask_edges'][1]['bit']=0
    damage('actual_BC_caller','root_corner_open',lambda r,e:None,doc=bad_doc)
    for middle,mode in ((2,'C'),(7,'HI'),(8,'HI')):
        # A claimed theorem on the actual broad root must fail before any
        # scalar replay: its quantitative guard is not implied.
        guard=GP.evaluate(root,document,middle,mode);assert guard['status']=='GUARD_NOT_IMPLIED'
        guard['status']='PASS_STRICT011_UNIVERSAL021_GUARD'
        terminal=dict(kind='strict011_conditional_universal021_terminal_v1',
                      attachment_binding_sha256='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023',guard=guard)
        record=dict(initial=G.state_view(root),rounds=[],status='CANDIDATE_CLOSED',terminal=terminal)
        folder=materialize('damaged_unproved_guard_'+str(middle),{0:record},{0:dict(id=0)})
        reject('unproved_root_guard_'+str(middle),lambda folder=folder:verify(folder))
        assert not (folder/'fresh_scalar_must_not_exist').exists()
        # A valid literal on arbitrarily narrowed intervals cannot replace
        # the complete root's exact initial state.
        narrowed=deepcopy(root);positions=list(narrowed['positions'])
        for i in (1,middle,3):positions[2*i+1]=(F(0),F(0))
        positions[2]=(F(-3,5),F(-3,5));positions[2*middle]=(F(0),F(0));positions[6]=(F(3,5),F(3,5))
        narrowed['positions']=tuple(positions)
        guard=GP.evaluate(narrowed,document,middle,mode);assert guard['status']=='PASS_STRICT011_UNIVERSAL021_GUARD'
        record=dict(initial=G.state_view(narrowed),rounds=[],status='CANDIDATE_CLOSED',
                    terminal=dict(terminal,guard=guard))
        folder=materialize('damaged_unproved_narrowing_'+str(middle),{0:record},{0:dict(id=0)})
        reject('unproved_root_narrowing_'+str(middle),lambda folder=folder:verify(folder))
        assert not (folder/'fresh_scalar_must_not_exist').exists()
    records,entries=source_trees['root_corner_open']
    folder=materialize('damaged_reused_scalar_output',records,entries)
    (folder/'fresh_scalar_must_not_exist').mkdir()
    reject('existing_scalar_output',lambda:verify(folder))
    assert len(rejected)==15
    assert sources=={name:digest(HERE/name)for name in sources}
    assert not any(name.split('.')[0]in{'numpy','scipy','sympy','z3','highspy'}for name in sys.modules)
    report=dict(status='PASS_PREPARED_STRENGTHENED_STRICT011_COMPLETE_ATTACHMENT_CONTROLS',
        source_hashes=sources,unchanged_function_asts=list(same),fixtures=fixtures,rejected_controls=rejected,
        all_fixture_roots_exact_whole_representative_caller=True,
        positive_synthetic_corner_weight_uses=5,actual_LP_weighted_use_gate_passed=False,
        successful_conditional_terminal_use_exercised=False,fresh_scalar_replay_performed=False,
        no_unproved_narrowing_or_incomplete_union_accepted=True,numerical_solver_called=False,
        original_cell_credit=0,whole_mask_credit=0)
    write(output/'COMPLETE_ATTACHMENT_CONTROLS.json',report)
    print(json.dumps(dict(status=report['status'],fixtures=len(fixtures),damages=len(rejected),
        report_sha256=digest(output/'COMPLETE_ATTACHMENT_CONTROLS.json'))))
if __name__=='__main__':main()

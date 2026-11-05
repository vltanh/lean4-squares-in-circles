#!/usr/bin/env python3
"""Extend a complete saved cover without recomputing accepted closed leaves.

Discovery only. Refresh phases and branch early on large corner error.
Prepared after complete A1: retain its original-wide necessary height row.
Add the stronger unsplit post-A1 bound state only in component3.
Immutable closed and nonleaf records are hard-linked; OPEN leaves are copied.
Each OPEN leaf first copies applicable shared bounds through an ordinary exact
round, then obtains a fresh numerical phase. No new row or checker rule.
Component-3 shared bounds retain their separate conditional scope.
Records are loaded only for the current OPEN leaf.
Every saved cover always includes all closed alternatives.
Exact arithmetic replay of the resulting tree remains the authority.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from itertools import product
import argparse, hashlib, json, os, shutil, time
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'ac_work/tree'))
import physical_tree_v6_proxy as DRIVER
import a_normalized_corner_split_v2 as SPLIT
import ac_completed_round_angle_search_v3 as SEARCH
from ac_a_c744_component3_post_a1_bounds_runtime import Context,E,stateview,state_from_view
import ac_a_c744_component3_post_a1_bounds_runtime as CONDITIONAL
import direct_shared_bound_round as DIRECT
import direct_shared_bound_precheck as DIRECT_PRECHECK
import ac_objective_unit_four_corner_runtime as ALLGUARDS
import ac_physical_gram_runtime as GRAM
import ac_physical_context_ownerfree as OFCTX
import ac_physical_context_ownerfree_v2 as OFCTX2
import active_highs_checked_warning_snapshot as WARN
import ac_physical_context_caps as CAPCTX
import physical_preflight as PREFLIGHT
import owner_free_relative_support_snapshot as OF

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--rounds',type=int,default=1);ap.add_argument('--proxy-rounds',type=int,default=0)
    ap.add_argument('--max-depth',type=int,default=24);ap.add_argument('--max-new-nodes',type=int,default=1000)
    ap.add_argument('--extra-existing-rounds',type=int,default=0)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    raw=(args.source/'manifest.json').read_bytes();manifest=json.loads(raw)
    assert manifest['schema']=='same_original_physical_SAT_proxy_angle_tree_discovery_v1'
    assert manifest['status']in('OPEN','CANDIDATE_COVER_CLOSED')
    (args.output/'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes(raw)
    nodes=deepcopy(manifest['nodes']);assert [n['index'] for n in nodes]==list(range(len(nodes)))
    original_count=len(nodes)
    root_path=Path(manifest['conditional_parent']['path']);assert sha(root_path)==manifest['conditional_parent']['sha256']
    whole=json.loads(root_path.read_text());assert whole['record']['status']=='OPEN'
    context=Context(state_from_view(whole['record']['final']),manifest['component']);started=time.monotonic();visited=[]
    for n in nodes:
        p=args.source/n['file'];assert sha(p)==n['sha256']
        target=args.output/n['file']
        if n['status'] in ('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED') or n['children']:
            os.link(p,target)
            assert target.stat().st_ino == p.stat().st_ino
        else:
            shutil.copyfile(p,target)
            assert target.stat().st_ino != p.stat().st_ino
        assert sha(target)==n['sha256'] and sha(p)==n['sha256']
        # Closed and nonleaf nodes return before any payload write; OPEN leaves are separate.
        # The independent exact checker still replays every retained record.
        assert n['status'] in ('OPEN','CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED')
        if n['children']:assert n['complete_children'] is True
    manifest['source_sha256'][str((args.output/'PREVIOUS_COMPLETE_MANIFEST.json').resolve())]=sha(args.output/'PREVIOUS_COMPLETE_MANIFEST.json')
    manifest['source_sha256'][str(Path(__file__).resolve())]=sha(__file__)
    manifest['source_sha256'][str(Path(SPLIT.__file__).resolve())]=sha(SPLIT.__file__)
    manifest['source_sha256'][str(Path(SEARCH.__file__).resolve())]=sha(SEARCH.__file__)
    manifest['source_sha256'][str(Path(DIRECT.__file__).resolve())]=sha(DIRECT.__file__)
    manifest['source_sha256'][str(Path(DIRECT_PRECHECK.__file__).resolve())]=sha(DIRECT_PRECHECK.__file__)
    manifest['source_sha256'][str(Path(OFCTX.__file__).resolve())]=sha(OFCTX.__file__)
    manifest['source_sha256'][str(Path(OFCTX2.__file__).resolve())]=sha(OFCTX2.__file__)
    manifest['source_sha256'][str(Path(WARN.__file__).resolve())]=sha(WARN.__file__)
    for p in (CAPCTX.__file__,CAPCTX.CAP.__file__,PREFLIGHT.__file__,CAPCTX.CAP_PACKET/'PREMISE_BINDINGS.json'):
        manifest['source_sha256'][str(Path(p).resolve())]=sha(p)
    manifest['source_sha256'][str(Path(OF.__file__).resolve())]=sha(OF.__file__)
    manifest['source_sha256'].update(GRAM.sources())
    manifest['source_sha256'].update(ALLGUARDS.sources())
    manifest['source_sha256'].update(CONDITIONAL.sources())
    manifest['component3_shared_bound_state']=context.component3_bound_reference
    manifest['component1_closed_consequence']=context.completed_component1_reference
    manifest['component3_post_a1_bound_state']=context.component3_post_a1_bound_reference
    manifest['retained_record_storage']=dict(immutable_closed_and_nonleaf_records_hard_linked=True,
        open_leaf_records_separate_copies=True,all_source_and_target_hashes_checked=True)
    direct_prefixes=('certified_a_c744_component3_post_a1_root_bound_',)
    manifest['direct_shared_bound_policy']=dict(prefixes=list(direct_prefixes),
        ordinary_exact_round_schema=True,numerical_solves_for_direct_round=0,
        fresh_phase_after_direct_round_required=True)
    manifest['continuation']=dict(source=str(args.source.resolve()),initial_nodes=original_count,
        retained_closed_leaves=sum(n['status']=='CANDIDATE_CLOSED'for n in nodes),visited_nodes=visited)
    def save():
        manifest['nodes']=nodes
        manifest['status']='CANDIDATE_COVER_CLOSED'if nodes[0]['status']=='CANDIDATE_CLOSED'else nodes[0]['status']
        manifest['seconds']=time.monotonic()-started
        dump(args.output/'manifest.json',manifest)
    def write_record(n,record,persist=True):
        record=dict(record,id=manifest['id'],original_path=manifest['original_path'])
        p=args.output/n['file'];dump(p,record);n['sha256']=sha(p)
        n['status']=record['status']
        if persist:save()
    def merge(old,new):
        assert old['status']=='OPEN'and new['initial']==old['final']
        result=deepcopy(new);result['initial']=deepcopy(old['initial'])
        result['rounds']=deepcopy(old['rounds'])+deepcopy(new['rounds'])
        result['seconds']=old.get('seconds',0)+new.get('seconds',0)
        result['continued_completed_rounds']=len(old['rounds'])
        return result
    def child_state(after,r):
        if r['kind']=='physical_proxy':return context.proxy_child(after,tuple(r['pair']),r['choice'])
        if r['kind']=='physical_sat':return context.child(after,tuple(r['pair']),r['choice'])
        assert r['kind']=='closed_angle'
        return context.angle_child(after,r['owner'],F(r['cut']),r['side'])
    def restrictions(split):
        if split['kind']=='complete_physical_proxy':
            values=list(product((0,1),(-1,1)));values.sort(key=lambda c:(c!=(0,1),c))
            return [dict(kind='physical_proxy',pair=split['pair'],choice=list(c))for c in values]
        if split['kind']=='complete_physical_sat':
            values=list(product(split['pair'],(0,1),(-1,1)));values.sort(key=lambda c:(c[1]!=0 or c[2]!=1,c))
            return [dict(kind='physical_sat',pair=split['pair'],choice=list(c))for c in values]
        assert split['kind']=='closed_angle_bisection'
        return [dict(kind='closed_angle',owner=split['owner'],cut=split['cut'],side=s)for s in(0,1)]
    def update_cover(n):
        n['status']='CANDIDATE_COVER_CLOSED'if all(nodes[k]['status']in('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED')for k in n['children'])else'OPEN'
    def visit(index):
        n=nodes[index]
        if n['status']in('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED'):return
        if n['children']:
            for k in n['children']:
                visit(k);update_cover(n);save()
            return
        if len(nodes)-original_count>=args.max_new_nodes:return
        old=json.loads((args.output/n['file']).read_text());assert old['status']=='OPEN'
        state=state_from_view(old['final']);restriction=n['restriction']
        budget=args.proxy_rounds if restriction and restriction['kind']=='physical_proxy'else args.rounds
        if index<original_count and ('point'in old or old.get('rounds')):budget=args.extra_existing_rounds
        visited.append(index)
        # The cheap screen is discovery only; a real round always rebuilds
        # the necessary rows through the same domain-bound context.
        copied_after,copied_round,copied_terminal=(
            DIRECT.bound_round(E,context,state,direct_prefixes)
            if DIRECT_PRECHECK.may_improve(E,state,context.component3_post_a1_rows,direct_prefixes)
            else (None,None,None))
        if copied_round is not None:
            extra=dict(status='CANDIDATE_CLOSED' if copied_terminal is not None else 'OPEN',
                initial=stateview(state),rounds=[copied_round],seconds=0)
            if copied_terminal is not None:
                extra['terminal']=copied_terminal
            else:
                assert copied_after is not None
                extra['final']=stateview(copied_after)
            old=merge(old,extra)
            write_record(n,old)
            print('DIRECT_SHARED_BOUND_ROUND',index,'DEDUCTIONS',len(copied_round['proposals']),
                'NUMERICAL_SOLVES',0,'STATUS',n['status'],flush=True)
            if copied_terminal is not None:return
            state=copied_after
        # A context early terminal with no direct round is delegated to the
        # unchanged preflight/engine path below. Every surviving copied state
        # receives a fresh phase, including a zero-bound-round proxy visit.
        def checkpoint(new):
            if new.get('terminal')is not None:
                new=dict(new,status='CANDIDATE_CLOSED')
            elif new.get('latest')is not None:
                new=dict(new,status='OPEN',final=new['latest'])
                new.pop('terminal',None);new.pop('latest',None)
            elif new.get('final') is not None and new.get('status')=='OPEN':
                new=dict(new)
            else:return
            write_record(n,merge(old,new))
        def search_with_early_angle():
            placed=(sum(kind=='sat'for pair,kind,choice in state['choices'])>=2 or
                    sum(kind=='proxy'for pair,kind,choice in state['choices'])>=5)
            if budget<=1 or not placed or n['depth']>=args.max_depth:
                return E.search_node(context,state,budget,checkpoint)
            def completed_round_choice(after,point,completed_rounds):
                selected=SPLIT.split_choice(after,point)
                if selected is not None and selected['kind']=='closed_angle_bisection':
                    owner=selected['owner'];lo,hi=after['angles'][owner]
                    if selected.get('normalized_corner_excess',0)>=0.1 and hi-lo>=F(1,16):
                        print('EARLY_NORMALIZED_ANGLE',index,owner,selected['normalized_corner_excess'],
                            'AFTER_ROUNDS',completed_rounds,flush=True)
                        return selected
                return None
            return SEARCH.search_node(E,context,state,budget,checkpoint,early_angle=completed_round_choice)
        try:
            preflight=PREFLIGHT.search(context,state)
            if preflight is not None:
                new,after,point=preflight,None,None
            else:
                # A saved point can predate a newly added necessary row.
                # Budget0 still gets the phase of the current model.
                new,after,point=search_with_early_angle()
            assert new['status']in('OPEN','CANDIDATE_CLOSED')
        except Exception as error:
            import traceback
            dump(args.output/f'discovery_error_{index:05d}.json',dict(error=repr(error),traceback=traceback.format_exc()))
            print('CONTINUATION_ERROR',index,repr(error),flush=True);return
        write_record(n,merge(old,new))
        print('RESUMED_NODE',index,'DEPTH',n['depth'],n['status'],'NEW_DEDUCTIONS',sum(len(r['proposals'])for r in new['rounds']),'SECONDS',round(time.monotonic()-started,2),flush=True)
        if n['status']!='OPEN'or n['depth']>=args.max_depth:return
        split=SPLIT.split_choice(after,point)
        if split is None:return
        if split['kind']=='complete_physical_sat' and restriction and restriction['kind']=='physical_proxy' and budget==0:
            old=json.loads((args.output/n['file']).read_text())
            try:
                extra,after,point=E.search_node(context,after,1,checkpoint)
                assert extra['status']in('OPEN','CANDIDATE_CLOSED')
            except Exception as error:
                import traceback
                dump(args.output/f'parent_propagation_error_{index:05d}.json',dict(error=repr(error),traceback=traceback.format_exc()))
                return
            write_record(n,merge(old,extra))
            print('BEFORE_SAT_PARENT_BOUND',index,n['status'],'DEDUCTIONS',sum(len(r['proposals'])for r in extra['rounds']),flush=True)
            if n['status']!='OPEN':return
            split=SPLIT.split_choice(after,point)
            if split is None:return
        rs=restrictions(split)
        if len(nodes)-original_count+len(rs)>args.max_new_nodes:return
        n['split']=split;n['children']=[];n['complete_children']=True
        for r in rs:
            child=child_state(after,r);view=stateview(child);k=len(nodes)
            c=dict(index=k,parent=index,depth=n['depth']+1,restriction=r,file=f'node_{k:05d}.json',children=[],status='OPEN')
            nodes.append(c);n['children'].append(k)
            write_record(c,dict(status='OPEN',initial=view,rounds=[],final=deepcopy(view),unsearched_closed_domain=True),persist=False)
        save()
        for k in n['children']:
            visit(k);update_cover(n);save()
    save();visit(0);save()
    print('CONTINUED_TREE_RESULT',manifest['status'],'NODES',len(nodes),'NEW_NODES',len(nodes)-original_count,
        'OPEN_LEAVES',sum(n['status']=='OPEN'and not n['children']for n in nodes),'SECONDS',time.monotonic()-started,flush=True)

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Extend a complete saved cover without recomputing accepted closed leaves.

Discovery only. Every saved cover always includes all closed alternatives.
Exact arithmetic replay of the resulting tree remains the authority.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'ac_work/tree'))
from fractions import Fraction as F
from copy import deepcopy
from itertools import product
import argparse, hashlib, json, shutil, time
import physical_tree_v6_proxy as DRIVER
import physical_split_normalized_corner_five_proxy as SPLIT
from cb882_shared_height_bounds_runtime import Context,E,stateview,state_from_view
import cb882_shared_height_bounds_runtime as CONDITIONAL
import ac_objective_unit_four_corner_runtime as ALLGUARDS
import ac_physical_gram_runtime as GRAM
import ac_physical_context_ownerfree as OFCTX
import ac_physical_context_ownerfree_v2 as OFCTX2
import active_highs_checked_warning_snapshot as WARN
import ac_physical_context_caps as CAPCTX
import physical_preflight as PREFLIGHT
import owner_free_relative_support_snapshot as OF

import atomic_json_checkpoint as ATOMIC
ATOMIC_SHA = '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
if hashlib.sha256(Path(ATOMIC.__file__).read_bytes()).hexdigest() != ATOMIC_SHA:
    raise RuntimeError('Atomic checkpoint helper hash mismatch.')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):ATOMIC.write_json(p,x)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--rounds',type=int,default=1);ap.add_argument('--proxy-rounds',type=int,default=0)
    ap.add_argument('--max-depth',type=int,default=24);ap.add_argument('--max-new-nodes',type=int,default=1000)
    ap.add_argument('--extra-existing-rounds',type=int,default=0)
    ap.add_argument('--prepare-only',action='store_true')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    raw=(args.source/'manifest.json').read_bytes();manifest=json.loads(raw)
    assert manifest['schema']=='same_original_physical_SAT_proxy_angle_tree_discovery_v1'
    assert manifest['status']in('OPEN','CANDIDATE_COVER_CLOSED')
    (args.output/'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes(raw)
    nodes=deepcopy(manifest['nodes']);assert [n['index'] for n in nodes]==list(range(len(nodes)))
    original_count=len(nodes);
    seed_path=Path(manifest['parent']['path']);assert sha(seed_path)==manifest['parent']['sha256']
    seed=CONDITIONAL.read_seed(seed_path)
    assert manifest['scope']==CONDITIONAL.SCOPE and manifest['component']==seed['component']
    assert manifest['conditional_parent']==seed['parent'] and manifest['closed_domain']==seed['conditional_row']
    context=Context(seed);started=time.monotonic();visited=[]
    manifest['whole_original_height_exclusion_consequences']=context.consequence_reference
    manifest['whole_original_height_bound_state']=context.whole_height_bound_reference
    for n in nodes:
        p=args.source/n['file'];assert sha(p)==n['sha256']
        shutil.copyfile(p,args.output/n['file'])
        if n['children']:assert n['complete_children'] is True
    manifest['source_sha256'][str((args.output/'PREVIOUS_COMPLETE_MANIFEST.json').resolve())]=sha(args.output/'PREVIOUS_COMPLETE_MANIFEST.json')
    manifest['source_sha256'][str(Path(__file__).resolve())]=sha(__file__)
    manifest['source_sha256'][str(Path(ATOMIC.__file__).resolve())]=ATOMIC_SHA
    manifest['source_sha256'][str(Path(SPLIT.__file__).resolve())]=sha(SPLIT.__file__)
    manifest['source_sha256'][str(Path(OFCTX.__file__).resolve())]=sha(OFCTX.__file__)
    manifest['source_sha256'][str(Path(OFCTX2.__file__).resolve())]=sha(OFCTX2.__file__)
    manifest['source_sha256'][str(Path(WARN.__file__).resolve())]=sha(WARN.__file__)
    for p in (CAPCTX.__file__,CAPCTX.CAP.__file__,PREFLIGHT.__file__,CAPCTX.CAP_PACKET/'PREMISE_BINDINGS.json'):
        manifest['source_sha256'][str(Path(p).resolve())]=sha(p)
    manifest['source_sha256'][str(Path(OF.__file__).resolve())]=sha(OF.__file__)
    manifest['source_sha256'].update(GRAM.sources())
    manifest['source_sha256'].update(ALLGUARDS.sources())
    manifest['source_sha256'].update(CONDITIONAL.sources(seed_path))
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
        def checkpoint(new):
            if new.get('terminal')is not None:
                new=dict(new,status='CANDIDATE_CLOSED')
            elif new.get('latest')is not None:
                new=dict(new,status='OPEN',final=new['latest'])
                new.pop('terminal',None);new.pop('latest',None)
            elif new.get('final')is not None and new.get('status')=='OPEN':
                new=dict(new)
            else:return
            write_record(n,merge(old,new))
        def search_with_early_angle():
            placed=(sum(kind=='sat'for pair,kind,choice in state['choices'])>=2 or
                    sum(kind=='proxy'for pair,kind,choice in state['choices'])>=5)
            if budget<=1 or not placed or n['depth']>=args.max_depth:
                return E.search_node(context,state,budget,checkpoint)
            first,after,point=E.search_node(context,state,1,checkpoint)
            if first['status']=='CANDIDATE_CLOSED':return first,after,point
            assert first['status']=='OPEN'
            selected=SPLIT.split_choice(after,point)
            if selected is not None and selected['kind']=='closed_angle_bisection':
                owner=selected['owner'];lo,hi=after['angles'][owner]
                if selected.get('normalized_corner_excess',0)>=0.1 and hi-lo>=F(1,16):
                    first=dict(first,discovery_early_angle=dict(
                        requested_rounds=budget,completed_rounds=1,split=selected))
                    print('EARLY_NORMALIZED_ANGLE',index,owner,selected['normalized_corner_excess'],flush=True)
                    return first,after,point
            def continued_checkpoint(partial):
                if partial.get('terminal')is not None:
                    partial=dict(partial,status='CANDIDATE_CLOSED')
                elif partial.get('latest')is not None:
                    partial=dict(partial,status='OPEN',final=partial['latest'])
                    partial.pop('terminal',None);partial.pop('latest',None)
                else:return
                checkpoint(merge(first,partial))
            remainder,after,point=E.search_node(context,after,budget-1,continued_checkpoint)
            return merge(first,remainder),after,point
        try:
            preflight=PREFLIGHT.search(context,state)
            if preflight is not None:
                new,after,point=preflight,None,None
            else:
                new,after,point=search_with_early_angle()
            assert new['status']in('OPEN','CANDIDATE_CLOSED')
        except OSError:
            raise
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
            except OSError:
                raise
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
    save()
    if not args.prepare_only:visit(0);save()
    print('CONTINUED_TREE_RESULT',manifest['status'],'NODES',len(nodes),'NEW_NODES',len(nodes)-original_count,
        'OPEN_LEAVES',sum(n['status']=='OPEN'and not n['children']for n in nodes),'SECONDS',time.monotonic()-started,flush=True)

if __name__=='__main__':main()

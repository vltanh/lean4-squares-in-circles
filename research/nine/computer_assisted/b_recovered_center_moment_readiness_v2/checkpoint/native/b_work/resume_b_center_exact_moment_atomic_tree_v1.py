#!/usr/bin/env python3
"""Continue a complete B cover with lazy payloads and early physical angle splits.

Closed node payloads are hash-checked and copied byte-for-byte. OPEN payloads
are parsed one at a time, and only the current leaf's records remain live
during a search. All new children are installed before their searches begin.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
import argparse,hashlib,json,os,time
import atomic_json_checkpoint_snapshot as ATOMIC
import b_center_exact_moment_runtime_v1 as RT
import b_five_proxy_corner_split as SPLIT
import b_physical_preflight as PREFLIGHT
import b_completed_round_angle_search_explicit as SEARCH
from b_proxy_cap_tree import proxy_child
from b_mixed_physical_tree import angle_child
from run_coupled_sat_cover import restore
E=RT.E
CLOSED=('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED')

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
    return h.hexdigest()

def dump(p,v):
    return ATOMIC.write_json(p,v)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent/'b16a_I32_complete_H_checkpoint')
    ap.add_argument('--rounds',type=int,default=6);ap.add_argument('--existing-rounds',type=int,default=3)
    ap.add_argument('--proxy-rounds',type=int,default=0);ap.add_argument('--max-depth',type=int,default=24)
    ap.add_argument('--max-new-nodes',type=int,default=1000);ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    raw=(a.source/'manifest.json').read_bytes();manifest=json.loads(raw)
    assert sha(ATOMIC.__file__)=='2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
    for group in ('sources','accepted_geometric_sources'):
        for path,expected in manifest[group].items():assert sha(path)==expected
    assert manifest['schema']=='B_proxy_first_complete_physical_tree_discovery_v1'and manifest['completed']is True
    (a.output/'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes(raw)
    nodes=[];hashes=[];opaque=set();dirty=set();started=time.monotonic();ctx=RT.Context(a.packet)
    def nodepath(index):return a.output/f'node_{index:04d}.json'
    def seed_record(record):
        ctx.AH.add_seed_record(record)
        for rr in record.get('rounds',[]):
            for printed in rr.get('printed_rows',[]):
                parts=printed['name'].split('_')
                if parts[:3]==['physical','pair','square']:
                    ctx.frame_squares.setdefault((int(parts[4]),int(parts[5])),set()).add(tuple(map(F,parts[6:])))
                elif parts[:3]==['physical','projection','square']:
                    ctx.projection_squares.setdefault((int(parts[4]),int(parts[5])),set()).add(tuple(map(F,parts[6:])))
    for entry in manifest['nodes']:
        index=len(nodes);assert entry['index']==index and entry['file']==f'node_{index:04d}.json'
        source=a.source/entry['file'];assert sha(source)==entry['sha256']
        # Subsequent writes always replace an inode atomically. Earlier source
        # payloads therefore remain unchanged even when an OPEN child advances.
        os.link(source,nodepath(index));hashes.append(entry['sha256'])
        assert entry['status']in('OPEN',)+CLOSED
        if entry['status']in CLOSED:
            nodes.append(dict(index=index,depth=entry['depth'],status=entry['status'],children=[]));opaque.add(index)
            continue
        payload=json.loads(nodepath(index).read_text());record=payload.pop('record')
        assert payload['index']==index and payload['depth']==entry['depth']and payload['status']=='OPEN'
        assert record['status']=='OPEN'
        if payload['children']:assert payload['complete_closed_children']is True
        seed_record(record);nodes.append(payload);del record,payload
    original_count=len(nodes);visits=[]
    manifest['sources'].update(RT.source_bindings())
    for p in(__file__,ATOMIC.__file__,SPLIT.__file__,PREFLIGHT.__file__,SEARCH.__file__,a.output/'PREVIOUS_COMPLETE_MANIFEST.json'):
        manifest['sources'][str(Path(p).resolve())]=sha(p)
    manifest['continuation']=dict(source=str(a.source.resolve()),initial_nodes=original_count,
        retained_closed_leaves=sum(n['status']=='CANDIDATE_CLOSED'for n in nodes),visits=visits,
        node_payloads_loaded_lazily=True,closed_payload_bytes_preserved=True)
    def save():
        for n in sorted(nodes,key=lambda n:n['depth'],reverse=True):
            if n['index']in opaque:continue
            if n['children']:
                status='CANDIDATE_COVER_CLOSED'if all(nodes[k]['status']in CLOSED for k in n['children'])else'OPEN'
                if n['status']!=status:n['status']=status;dirty.add(n['index'])
        for index in sorted(dirty):
            assert index not in opaque
            payload=json.loads(nodepath(index).read_text());payload.update(nodes[index])
            dump(nodepath(index),payload);hashes[index]=sha(nodepath(index));del payload
        dirty.clear()
        manifest.update(nodes=[dict(index=n['index'],file=nodepath(n['index']).name,sha256=hashes[n['index']],status=n['status'],depth=n['depth'])for n in nodes],
            status=nodes[0]['status'],seconds=time.monotonic()-started)
        dump(a.output/'manifest.json',manifest)
    def merge(old,new):
        assert old['status']=='OPEN'and new['initial']==old['final']
        record=deepcopy(new);record['initial']=deepcopy(old['initial'])
        record['rounds']=deepcopy(old['rounds'])+deepcopy(new['rounds'])
        record['seconds']=old.get('seconds',0)+new.get('seconds',0)
        record['continued_completed_rounds']=len(old['rounds'])
        return record
    def write_record(n,record,persist=True):
        n['status']=record['status'];dump(nodepath(n['index']),dict(n,record=record));hashes[n['index']]=sha(nodepath(n['index']))
        dirty.discard(n['index'])
        if persist:save()
    def process_leaf(index):
        n=nodes[index];payload=json.loads(nodepath(index).read_text());old=payload.pop('record');assert payload==n;del payload
        state=restore(ctx,old)
        budget=a.existing_rounds if index<original_count and not old.get('unsearched_closed_domain')else a.proxy_rounds if isinstance(n['choice'],list)and len(n['choice'])==2 else a.rounds
        visits.append(index)
        def checkpoint(new):
            if new.get('terminal')is not None:new=dict(new,status='CANDIDATE_CLOSED')
            elif new.get('latest')is not None:
                new=dict(new,status='OPEN',final=new['latest']);new.pop('latest',None);new.pop('terminal',None)
            else:return
            write_record(n,merge(old,new))
        def adaptive_search():
            placed=(sum(kind=='sat'for pair,kind,ch in state['choices'])>=2 or
                    sum(kind=='proxy'for pair,kind,ch in state['choices'])>=5)
            if budget<=1 or not placed or n['depth']>=a.max_depth:
                return SEARCH.search_node(E,ctx,state,budget,checkpoint)
            def completed_round_choice(after,point,probe):
                selected=SPLIT.split_choice(after,point,probe)
                if selected['kind']=='angle':
                    owner=selected['owner'];lo,hi=after['angles'][owner]
                    corner=selected.get('normalized_corner_excess',0)>=.1
                    frame=selected.get('defect',0)>=.2
                    if (corner or frame) and hi-lo>=F(1,16):
                        trigger='normalized_corner_excess'if corner else'frame_defect'
                        selected=dict(selected,discovery_early_trigger=trigger)
                        print('EARLY_NORMALIZED_ANGLE'if corner else'EARLY_FRAME_ANGLE',
                            index,owner,selected.get('normalized_corner_excess',selected.get('defect')),
                            'AFTER_ROUNDS',probe['completed_rounds'],flush=True)
                        return selected
                return None
            return SEARCH.search_node(E,ctx,state,budget,checkpoint,early_angle=completed_round_choice)
        quick=PREFLIGHT.search(ctx,state,ctx.preflight_phase)
        if quick is not None:new,after,point=quick,None,None
        else:new,after,point=adaptive_search()
        if new['status']not in('OPEN','CANDIDATE_CLOSED'):
            dump(a.output/f'discovery_no_conclusion_{index:04d}.json',new);return
        write_record(n,merge(old,new))
        print('RESUMED_NODE',index,'DEPTH',n['depth'],n['status'],'DEDUCTIONS',sum(len(r['proposals'])for r in new['rounds']),
            'OPEN_LEAVES',sum(x['status']=='OPEN'and not x['children']for x in nodes),'SECONDS',round(time.monotonic()-started,2),flush=True)
        if n['status']!='OPEN'or n['depth']>=a.max_depth:return
        split=SPLIT.split_choice(after,point,new)
        if split['kind']=='sat'and budget==0:
            saved=json.loads(nodepath(index).read_text())['record']
            def precheckpoint(extra):
                if extra.get('terminal')is not None:extra=dict(extra,status='CANDIDATE_CLOSED')
                elif extra.get('latest')is not None:
                    extra=dict(extra,status='OPEN',final=extra['latest']);extra.pop('latest',None);extra.pop('terminal',None)
                else:return
                write_record(n,merge(saved,extra))
            extra,after,point=SEARCH.search_node(E,ctx,after,1,precheckpoint)
            if extra['status']not in('OPEN','CANDIDATE_CLOSED'):return
            write_record(n,merge(saved,extra))
            print('PRE_SAT_PROPAGATION',index,n['status'],'DEDUCTIONS',sum(len(r['proposals'])for r in extra['rounds']),flush=True)
            if n['status']!='OPEN':return
            new=extra;split=SPLIT.split_choice(after,point,new)
        if split['kind']=='proxy':
            pair=tuple(split['pair']);children=[(list(ch),proxy_child(ctx,after,pair,*ch))for ch in product((0,1),(-1,1))]
        elif split['kind']=='sat':
            pair=tuple(split['pair']);children=[(list(ch),ctx.child(after,pair,ch))for ch in product(pair,(0,1),(-1,1))]
        else:children=[(side,angle_child(ctx,after,split['owner'],F(split['cut']),side))for side in(0,1)]
        if len(nodes)-original_count+len(children)>a.max_new_nodes:return
        n['split']=split;n['children']=[];n['complete_closed_children']=True;dirty.add(index)
        for choice,child in children:
            k=len(nodes);view=E.stateview(child)
            node=dict(index=k,parent=index,depth=n['depth']+1,choice=choice,initial=deepcopy(view),status='OPEN',children=[])
            nodes.append(node);hashes.append(None);n['children'].append(k)
            write_record(node,dict(status='OPEN',initial=deepcopy(view),rounds=[],final=deepcopy(view),unsearched_closed_domain=True),persist=False)
        save()
        # Returning releases all current-leaf record buffers before descendants
        # are visited. The recursive traversal retains only small metadata.
    def visit(index):
        n=nodes[index]
        if n['status']in CLOSED:return
        if not n['children']:
            if len(nodes)-original_count>=a.max_new_nodes:return
            process_leaf(index)
        for k in list(n['children']):visit(k)
        save()
    save()
    if not a.prepare_only:visit(0);save()
    for p,h in manifest['sources'].items():assert sha(p)==h
    for index in opaque:assert sha(nodepath(index))==hashes[index]
    print('LAZY_CONTINUATION_RESULT',manifest['status'],'NODES',len(nodes),'OPEN_LEAVES',sum(n['status']=='OPEN'and not n['children']for n in nodes),
        'PREPARE_ONLY',a.prepare_only,'SECONDS',time.monotonic()-started,flush=True)

if __name__=='__main__':main()

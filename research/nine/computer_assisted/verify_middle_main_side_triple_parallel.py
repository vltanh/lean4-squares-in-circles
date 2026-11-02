#!/usr/bin/env python3
"""Parallel scheduling of the independently reconstructed exact leaf checker.

The arithmetic and geometric evaluator are imported from the separately
reviewed verifier. This driver validates the complete original preorder tree,
partitions it into disjoint complete subtrees with exact rational entry boxes,
and requires their exact totals to reproduce the whole certificate. No
producer module, floating arithmetic, external solver, Lean or CI is used.
"""
from array import array
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,json,multiprocessing,time
import verify_middle_main_side_triple as checked

EVENTS=None
KIND=None

def split_box(box,axis):
    mid=(box[axis][0]+box[axis][1])/2
    assert box[axis][0]<mid<box[axis][1]
    left=list(box);right=list(box)
    left[axis]=(box[axis][0],mid);right[axis]=(mid,box[axis][1])
    return tuple(left),tuple(right)

def subtree(task):
    start,end,entry,entry_depth=task
    stack=[(entry,entry_depth)];leaves=0;depth=entry_depth;least=None;rules=Counter()
    for j in range(start,end):
        assert stack,('subtree trailing event',j)
        box,d=stack.pop();depth=max(depth,d);tag=EVENTS[j]
        if tag>=0:
            left,right=split_box(box,tag)
            stack.append((right,d+1));stack.append((left,d+1))
        else:
            code=-tag-1;m=checked.margin(box,code,KIND)
            assert m<0,('unproved leaf',j,code,str(F(m,checked.SCALE)),box)
            reserve=-m;least=reserve if least is None else min(least,reserve)
            leaves+=1;rules[code]+=1
    assert not stack,('incomplete subtree',start,end,len(stack))
    assert end-start==2*leaves-1
    return {'start':start,'end':end,'nodes':end-start,'leaves':leaves,'depth':depth,'least':least,'rules':dict(rules)}

def preflight(events,kind):
    # Exact postfix boundaries of every complete subtree; this pass has no
    # geometric acceptance role. Each leaf later receives an exact replay.
    n=len(events);assert n>0
    ends=array('I',[0])*n;stack=[];leaves=0
    assert n<2**32
    for j,tag in enumerate(events):
        assert type(tag) is int,('noninteger tag',j)
        assert not(j>0 and not stack and ends[0]),('trailing root',j)
        if tag>=0:
            assert tag<7,('unknown split',j,tag)
            stack.append([j,2])
        else:
            code=-tag-1;assert 0<=code<(6 if kind=='low_floor' else 5),('unknown leaf',j,tag)
            ends[j]=j+1;leaves+=1
            while stack:
                stack[-1][1]-=1
                if stack[-1][1]:break
                k,remaining=stack.pop();assert remaining==0;ends[k]=j+1
    assert not stack and ends[0]==n,('incomplete root',len(stack),ends[0],n)
    assert n==2*leaves-1
    return ends,leaves

def partition(events,ends,kind,limit):
    tasks=[];prefix=0;prefix_depth=0
    def visit(j,box,depth):
        nonlocal prefix,prefix_depth
        end=ends[j];assert end>j
        if end-j<=limit or events[j]<0:
            tasks.append((j,end,box,depth));return
        axis=events[j];assert 0<=axis<7
        prefix+=1;prefix_depth=max(prefix_depth,depth)
        left,right=split_box(box,axis)
        first=j+1;second=ends[first]
        assert first<second<end and ends[second]==end
        visit(first,left,depth+1);visit(second,right,depth+1)
    visit(0,checked.root(kind),0)
    assert prefix+sum(end-start for start,end,box,depth in tasks)==len(events)
    return tasks,prefix,prefix_depth

def main():
    global EVENTS,KIND
    base=Path(__file__).resolve().parent
    p=argparse.ArgumentParser();p.add_argument('--certificate',type=Path,default=base/'middle_main_low_floor_candidate.json');p.add_argument('--report',type=Path,default=base/'middle_main_low_floor_parallel_exact_replay.json');p.add_argument('--workers',type=int,default=6);p.add_argument('--task-nodes',type=int,default=40000);a=p.parse_args()
    assert 1<=a.workers<=16 and a.task_nodes>=1
    start=time.monotonic();blob=a.certificate.read_bytes();data=json.loads(blob)
    assert data['status']=='COMPLETE_UNTRUSTED_DISCOVERY'
    KIND=data['kind'];assert KIND in ('low_floor','low_right')
    EVENTS=data['events'];assert isinstance(EVENTS,list)
    ends,total_leaves=preflight(EVENTS,KIND)
    assert data['nodes']==len(EVENTS) and data['leaves']==total_leaves
    tasks,prefix,prefix_depth=partition(EVENTS,ends,KIND,a.task_nodes)
    print(json.dumps({'status':'COMPLETE_TREE_PREFLIGHT_PASSED','nodes':len(EVENTS),'leaves':total_leaves,'subtrees':len(tasks),'prefix_nodes':prefix,'workers':a.workers,'seconds':time.monotonic()-start}),flush=True)
    del ends
    nodes=prefix;leaves=0;depth=prefix_depth;least=None;rules=Counter();completed=0
    with ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('fork')) as pool:
        futures=[pool.submit(subtree,task) for task in tasks]
        for future in as_completed(futures):
            r=future.result();nodes+=r['nodes'];leaves+=r['leaves'];depth=max(depth,r['depth']);least=r['least'] if least is None else min(least,r['least']);rules.update(r['rules']);completed+=1
            if completed%10==0 or completed==len(tasks):
                print(json.dumps({'status':'EXACT_SUBTREES_PASSED','completed':completed,'total':len(tasks),'nodes':nodes,'leaves':leaves,'seconds':time.monotonic()-start}),flush=True)
    assert completed==len(tasks) and nodes==len(EVENTS) and leaves==total_leaves
    assert depth==data['max_depth'] and least>0
    report={'status':'EXACT_REPLAY_PASSED','kind':KIND,'nodes':nodes,'leaves':leaves,'max_depth':depth,'leaf_rules':dict(sorted(rules.items())),'root':[[str(x),str(y)] for x,y in checked.root(KIND)],'scale':checked.SCALE,'minimum_exact_reserve':str(F(least,checked.SCALE)),'certificate_sha256':hashlib.sha256(blob).hexdigest(),'checker_sha256':hashlib.sha256(Path(checked.__file__).read_bytes()).hexdigest(),'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'partition_subtrees':len(tasks),'verified_prefix_split_nodes':prefix,'workers':a.workers,'seconds':time.monotonic()-start,'arithmetic':'Directed80-bit integer dyadics, exact rational midpoint boxes, integer square roots; no floating point. The complete tree is partitioned only for scheduling. Every leaf is reconstructed by the independently reviewed verifier.','scope':'Original actual cone four-chain and both-weak side-endpoint cone triple; low-floor uses yMain>=-17/50 from the original lower side unit. All original nine units remain in the caller.'}
    a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()

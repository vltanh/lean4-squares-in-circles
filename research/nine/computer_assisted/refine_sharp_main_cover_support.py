#!/usr/bin/env python3
"""Refine an existing complete exact tree for the direct-support enclosure.

Every existing split is retained.  Only exact rational split refinements
are introduced; the final independent checker accepts no producer bounds.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import time
from certify_sharp_small_main_tilt_toll import evaluate

HERE=Path(__file__).resolve().parent
def main():
    source=HERE/'sharp_small_main_tilt_toll_cover.json';data=json.loads(source.read_text());begin=time.monotonic()
    for row in data['trees']:
        ch=row['channel'];rootbox=tuple(tuple(map(F,p))for p in row['root']);olditer=iter(row['events'])
        todo=[(rootbox,0,True)];events=[];leaves=0;depthmax=0;least=None;added=0
        while todo:
            box,depth,old=todo.pop();depthmax=max(depthmax,depth)
            tag=next(olditer) if old else -1
            if tag==-1:
                low=evaluate(ch,box,True).lo
                if low>F(1,1000000000000):
                    events.append(-1);leaves+=1;least=low if least is None else min(least,low);continue
                assert depth<45
                scores=[(hi-lo)*(1 if i==0 else 2)for i,(lo,hi)in enumerate(box)]
                tag=max(range(len(box)),key=lambda i:scores[i]);old=False;added+=1
            assert 0<=tag<len(box)
            lo,hi=box[tag];mid=(lo+hi)/2;left=list(box);right=list(box)
            left[tag]=(lo,mid);right[tag]=(mid,hi);events.append(tag)
            todo.extend([(tuple(right),depth+1,old),(tuple(left),depth+1,old)])
        assert next(olditer,None)is None
        row.update(events=events,leaves=leaves,nodes=len(events),maximum_depth=depthmax,minimum_fraction_reserve=str(least))
        print(ch,leaves,'added splits',added,'seconds',round(time.monotonic()-begin,3),flush=True)
    data['status']='complete_pending_independent_replay';data['refinement_seconds']=time.monotonic()-begin
    data['refinement']='All prior splits retained; exact rational direct-support leaf refinements'
    source.write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()

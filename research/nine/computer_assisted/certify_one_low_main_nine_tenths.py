#!/usr/bin/env python3
"""Exact Fraction discovery for the one-low-main central obstruction."""
from pathlib import Path
from fractions import Fraction as F
import json,sys,time

HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'interval_fraction.py').exists()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from interval_fraction import I
Q=F(1105,256);ROOT=((F(1,3),F(29,60)),(F(0),F(1)))

def envelope(bounds):
    vals=[]
    for t in bounds:
        d=I(1+t*t).sqrt(80);vals.append((1/d,t/d,(1+t)/(2*d),(1-t)/(2*d)))
    return tuple(I(min(p[j].lo for p in vals),max(p[j].hi for p in vals))for j in range(4))

def rule(box):
    x=I(*box[0]);a,b,h,k=envelope(box[1])
    c1=(Q-(x+h).sq()).sqrt(80)-k;c2=(Q-(x-k).sq()).sqrt(80)-h
    u=I(min(c1.lo,c2.lo,F(91,60)),min(c1.hi,c2.hi,F(91,60)))
    v=u-F(9,10)-F(15,31)
    if v.hi<=0:return -1,str(-v.hi)
    d=x+F(1,60)
    bound=max((a*d+b*v).hi,(b*d+a*v).hi)-F(1,2)
    if bound<0:return -2,str(-bound)
    return None

def main():
    stack=[(ROOT,0)];events=[];counts=[0,0];reserves=[[],[]];depthmax=0;started=time.monotonic()
    while stack:
        box,depth=stack.pop();depthmax=max(depthmax,depth)
        answer=rule(box)
        if answer:
            tag,res=answer;events.append(tag);counts[-tag-1]+=1;reserves[-tag-1].append(F(res))
        else:
            assert depth<40,(box,depth)
            j=max(range(2),key=lambda i:(box[i][1]-box[i][0])/(ROOT[i][1]-ROOT[i][0]))
            m=sum(box[j])/2;lo,hi=list(box),list(box);lo[j]=(box[j][0],m);hi[j]=(m,box[j][1])
            events.append(j);stack.extend([(tuple(hi),depth+1),(tuple(lo),depth+1)])
    data={'type':'one_low_main_nine_tenths_cover_v1','root':[[str(a),str(b)]for a,b in ROOT],
          'proof_status':'complete_pending_independent_replay','events':events,'nodes':len(events),
          'leaves':sum(counts),'leaf_counts':counts,'maximum_depth':depthmax,
          'minimum_reserves':[str(min(v))if v else None for v in reserves],
          'seconds':time.monotonic()-started}
    (HERE/'one_low_main_nine_tenths_cover.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items()if k!='events'}))

if __name__=='__main__':main()

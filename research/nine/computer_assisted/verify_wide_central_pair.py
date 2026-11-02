#!/usr/bin/env python3
"""Exact integer replay of the wide-main two-central-square floor cover.

This checker never imports the numerical producer. The interval arithmetic
kernel is the previously audited standalone 64-bit directed integer kernel.
The present formulas and complete physical reduction require a separate
hand review. A successful tree replay alone does not close a whole mask.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import copy
import gzip
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
BASE = HERE if (HERE/'verify_joint_five_dyadic.py').exists() else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0, str(BASE))
from verify_joint_five_dyadic import I, SCALE

ROOT = ((F(1,2),F(13,20)),(F(1,2),F(13,20)),
        (F(0),F(1)),(F(0),F(1)),(F(0),F(29,60)))

@dataclass
class Shape:
    a: I
    b: I
    h: I
    g: I
    eta: I

def mainshape(hlo,hhi):
    def point(z):
        h=I(z);k=(I(F(1,2))-h.sq()).sqrt()
        return h+k,h-k,h+1/(4*h)-1
    low,high=point(hlo),point(hhi)
    return Shape(I.raw(high[0].lo,low[0].hi),
                 I.raw(max(0,low[1].lo),high[1].hi),I(hlo,hhi),
                 I(F(1,4)/hhi,F(1,4)/hlo),
                 I.raw(max(0,low[2].lo),high[2].hi))

def free_shape(tlo,thi):
    def point(z):
        t=I(z);a=1/(1+t.sq()).sqrt();b=t*a
        return a,b,(a+b)/2
    low,high=point(tlo),point(thi)
    return Shape(I.raw(high[0].lo,low[0].hi),
                 I.raw(low[1].lo,high[1].hi),
                 I.raw(low[2].lo,high[2].hi),I(0),I(0))

def clearance(s,t,D):
    """Lower dyadic bound for the union of all four unsigned owners.

    D is a nonnegative rational upper bound for the horizontal gap.
    For a zero vertical owner, a positive required numerator makes that
    owner impossible. A nonpositive numerator allows zero clearance.
    """
    assert D>=0
    sig=(1+s.a*t.a+s.b*t.b+(s.a*t.b-s.b*t.a).abs())/2
    sigma=I.raw(max(SCALE,sig.lo),max(SCALE,sig.hi))
    candidates=[]
    for nx,ny in ((s.a,s.b),(s.b,s.a),(t.a,t.b),(t.b,t.a)):
        numerator=(sigma-nx*I(D)).lo
        if numerator<=0:
            candidates.append(0)
        elif ny.hi>0:
            candidates.append(numerator*SCALE//ny.hi)
        else:
            assert ny.lo==0
    assert candidates
    return F(min(candidates),SCALE)

def values(box):
    b=mainshape(*box[0]);c=mainshape(*box[1])
    f=free_shape(*box[2]);g=free_shape(*box[3]);x=I(*box[4])
    V=b.eta+c.eta
    bl=b.h-F(61,60);br=I(F(1,60))-b.g-c.eta
    cl=c.g+b.eta-F(1,60);cr=I(F(61,60))-c.h
    def lower(z):return F(z.lo,SCALE)
    def upper(z):return F(z.hi,SCALE)
    def distance(z):return upper((x-z).abs())
    left=min(-upper(bl)+clearance(b,f,distance(bl)),
             -upper(br)+clearance(b,f,distance(br)))
    right=min(lower(cl)+clearance(c,f,distance(cl)),
              lower(cr)+clearance(c,f,distance(cr)))
    cb=clearance(b,f,max(distance(bl),distance(br)))
    cc=clearance(c,f,max(distance(cl),distance(cr)))
    middle=clearance(b,c,upper(cr-bl))
    middle_y=middle-F(129,80)+min(-upper(br)+cc,lower(cl)+cb)
    y=max(F(-3,10),-F(129,80)+left,-F(129,80)+right,
          -F(379,240)+F(16,9)*lower(V)+(left+right)/2,middle_y)
    floor=y+clearance(f,g,F(1,2))-upper(g.h)
    return lower(V)-F(1,30),floor-F(1,10)

def verify(data):
    assert data['type']=='wide_main_central_pair_floor_v1'
    assert tuple(tuple(map(F,row))for row in data['root'])==ROOT
    assert type(data['events']) is list
    # Check the complete binary tree before any expensive arithmetic replay.
    pending=1
    for tag in data['events']:
        assert pending>0 and type(tag)is int and -2<=tag<=4
        pending+=1 if tag>=0 else -1
    assert pending==0
    todo=[(ROOT,0)];leaves=0;depthmax=0;least=None;counts=[0,0]
    for position,tag in enumerate(data['events']):
        box,depth=todo.pop();depthmax=max(depthmax,depth)
        if tag>=0:
            lo,hi=box[tag];mid=(lo+hi)/2;assert lo<mid<hi
            a=list(box);b=list(box);a[tag]=(lo,mid);b[tag]=(mid,hi)
            todo.extend([(tuple(b),depth+1),(tuple(a),depth+1)])
        else:
            rule=-tag-1;reserve=values(box)[rule]
            assert reserve>0,(position,rule,str(reserve),box)
            least=reserve if least is None else min(least,reserve)
            leaves+=1;counts[rule]+=1
        if position and position%100000==0:
            print(f'EXACT_REPLAY progress: {position} nodes, {leaves} leaves',flush=True)
    assert not todo
    assert leaves==data['leaves']
    assert len(data['events'])==data['nodes']==2*leaves-1
    assert depthmax==data['maximum_depth']
    return {'status':'EXACT_REPLAY_PASSED','leaves':leaves,
            'nodes':len(data['events']),'maximum_depth':depthmax,
            'minimum_exact_reserve':str(least),'leaf_rules':counts,
            'root':[[str(a),str(b)]for a,b in ROOT],
            'arithmetic':'64-bit directed integer enclosures with exact rational tree endpoints',
            'scope':'Two original upper central squares with horizontal gap at most 1/2; outer main links actual, middle arbitrary; higher whole floor strictly above 1/10. Not a whole-mask closure.'}

def controls(data):
    damaged=[]
    q=copy.deepcopy(data);q['root'][4][0]='1/100';damaged.append(('omitted_root_face',q))
    q=copy.deepcopy(data);q['events'][0]=5;damaged.append(('unknown_split_axis',q))
    q=copy.deepcopy(data);q['events']=q['events'][:-1];damaged.append(('missing_child',q))
    q=copy.deepcopy(data);q.update(events=[-2],nodes=1,leaves=1,maximum_depth=0);damaged.append(('false_unsplit_terminal',q))
    answers=[]
    for name,q in damaged:
        try:verify(q)
        except (AssertionError,ValueError,ZeroDivisionError) as e:
            answers.append({'control':name,'status':'REJECTED','reason':str(e)[:300]})
        else:raise AssertionError('Damaged control accepted: '+name)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':answers}

def main():
    source=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'wide_central_pair_candidate.json'
    raw=source.read_bytes();blob=gzip.decompress(raw)if source.suffix=='.gz'else raw
    data=json.loads(blob);start=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(blob).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  kernel_sha256=hashlib.sha256((BASE/'verify_joint_five_dyadic.py').read_bytes()).hexdigest(),
                  seconds=time.monotonic()-start)
    (HERE/'wide_central_pair_exact_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    (HERE/'wide_central_pair_negative_controls.json').write_text(json.dumps(controls(data),indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

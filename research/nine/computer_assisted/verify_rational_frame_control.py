"""Exact integer/Fraction verification of a fixed physical frame obstruction.

No numerical optimizer or floating evaluator is imported.  The proof reducing
all real frame directions to this finite event set is in the accompanying
hand manuscript. This checker certifies a fixed ABOVE-Q control, not a
counterexample to the nine-square sharp-radius theorem or the Q extraction.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd
import argparse
import hashlib
import json

BASE = Path(__file__).resolve().parent


def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]


def perp(a):
    return (-a[1],a[0])


def diff(a,b):
    return (a[0]-b[0],a[1]-b[1])


def primitive(e):
    g=gcd(e[0],e[1])
    if g==0:
        return None
    e=(e[0]//g,e[1]//g)
    if e[0]<0 or (e[0]==0 and e[1]<0):
        e=(-e[0],-e[1])
    return e


def verify(path):
    raw=path.read_bytes(); d=json.loads(raw)
    C=d['center_denominator']; A=d['frame_denominator']
    c=[tuple(p) for p in d['centers']];u=[tuple(p) for p in d['first_axes']];v=[perp(p) for p in u]
    n=len(c); q=F(d['q_upper'])
    assert n==9 and len(u)==n and C>0 and A>0
    assert all(dot(w,w)==A*A for w in u)
    radii=[F(dot(p,p),C*C)+F(1,2)+F(abs(dot(p,s))+abs(dot(p,t)),C*A) for p,s,t in zip(c,u,v)]
    assert max(radii)<=q
    physical=[]
    for i,j in combinations(range(n),2):
        z=diff(c[j],c[i]); gaps=[]
        for w in (u[i],v[i],u[j],v[j]):
            sup=F(abs(dot(w,u[i]))+abs(dot(w,v[i]))+abs(dot(w,u[j]))+abs(dot(w,v[j])),2*A*A)
            gaps.append(F(abs(dot(w,z)),C*A)-sup)
        physical.append(max(gaps)); assert physical[-1]>=0
    corners=[]
    for p,s,t in zip(c,u,v):
        corners.append([(2*A*p[0]+C*(e*s[0]+f*t[0]),2*A*p[1]+C*(e*s[1]+f*t[1])) for e,f in product((-1,1),repeat=2)])
    events={primitive((1,0))}
    cone_events=set(); actual_events=set()
    for i,j in combinations(range(n),2):
        z=diff(c[j],c[i])
        assert z!=(0,0)
        for e in ((z[0]-z[1],z[1]+z[0]),(z[0]+z[1],z[1]-z[0])):
            cone_events.add(primitive(e))
        for p,t in product(corners[i],corners[j]):
            e=primitive(perp(diff(t,p)))
            if e is not None:actual_events.add(e)
    events|=cone_events|actual_events
    assert None not in events
    count_outer_four=0; count_four_three=0
    for e in sorted(events):
        f=perp(e)
        xx=[dot(e,p) for p in c];yy=[dot(f,p) for p in c]
        h=[abs(dot(e,p))+abs(dot(e,t)) for p,t in zip(u,v)]
        order=sorted(range(n),key=lambda i:(xx[i],i))
        cone=[[False]*n for _ in range(n)];act=[[False]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i==j:continue
                cone[i][j]=xx[j]-xx[i]>=abs(yy[j]-yy[i])
                act[i][j]=2*A*(xx[j]-xx[i])>=C*(h[i]+h[j])
        for p,r,s,t in combinations(order,4):
            if not (cone[p][r] and cone[r][s] and cone[s][t] and act[p][r] and act[s][t]):
                continue
            count_outer_four+=1
            remain=[i for i in order if i not in (p,r,s,t)]
            for i,j,k in combinations(remain,3):
                if cone[i][j] and cone[j][k]:
                    count_four_three+=1
                    raise AssertionError(('found forbidden 4+3',e,(p,r,s,t),(i,j,k)))
    assert count_outer_four==0
    return {'status':'PASS','claim':'fixed nine original squares above Q have no frame with a cone4 having both outer links actual',
            'input_sha256':hashlib.sha256(raw).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'q_upper':str(q),'q_upper_minus_Q':str(q-F(1105,256)),
            'max_corner_norm_squared':str(max(radii)),'minimum_original_pair_margin':str(min(physical)),
            'cone_event_count':len(cone_events),'actual_event_count':len(actual_events),'union_event_count':len(events),
            'outer_actual_four_chains_at_events':count_outer_four,'outer_actual_four_plus_three_at_events':count_four_three,
            'all_pairs_checked':len(physical),'original_corner_count':4*n,
            'uses_floating_arithmetic':False,'uses_optimizer':False}


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('input',nargs='?',type=Path,default=BASE/'rational_nine_no_outer_control.json');ap.add_argument('--report',type=Path);args=ap.parse_args()
    report=verify(args.input);out=args.report or BASE/'rational_nine_no_outer_control_replay.json'
    out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

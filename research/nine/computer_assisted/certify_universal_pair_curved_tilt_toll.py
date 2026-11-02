#!/usr/bin/env python3
"""Exact Fraction discovery of a universal weighted pair shoulder-tilt toll.

Only a complete, separately replayed scalar cover may certify the result.
No optimizer output, floating arithmetic, Lean, or CI is used here.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,time

HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'interval_fraction.py').exists()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from interval_fraction import I

W=F(46);V=F(27,2);K=F(207,16);T=F(211,4);Q=F(1105,256)
ROOTS=[(0,F(-1),F(-1,32)),(0,F(1,32),F(1)),
       (1,F(-1),F(-1,32)),(1,F(1,32),F(1)),
       (2,F(-1),F(1)),(3,F(-1),F(1)),(4,F(-1),F(1))]

def rt(x):return x.sqrt(80)
def minimum(*xs):return I(min(x.lo for x in xs),min(x.hi for x in xs))
def maximum(*xs):return I(max(x.lo for x in xs),max(x.hi for x in xs))
def hull(xs):return I(min(x.lo for x in xs),max(x.hi for x in xs))
def sine(c):return rt(1-c.sq())
def length(w,c):return rt(w*w+K*K+2*w*K*c)

def E(w,c):return w+K*(sine(c)+maximum(c,I(0)))

def N(w,c):
    regions=[(F(-1),-K/w,0),(-K/w,F(0),1),(F(0),F(1),2)]
    out=[]
    for a,b,kind in regions:
        low,high=max(a,c.lo),min(b,c.hi)
        if low>high:continue
        z=I(low,high);s=sine(z)
        out.append(w*(s-z) if kind==0 else K+w*s if kind==1 else K+w*(z+s))
    return hull(out)

def D(w,c):
    out=[]
    for a,b,kind in [(F(-1),-K/w,0),(-K/w,F(1),1)]:
        low,high=max(a,c.lo),min(b,c.hi)
        if low>high:continue
        z=I(low,high);s=sine(z);ell=length(w,z)
        out.append(w*(w+K*z+K*s)/ell if kind==0 else ell+w*K*s/ell)
    return hull(out)

def margin(channel,bounds):
    c=I(*bounds);s=sine(c)
    la=length(W,c);lb=length(V,-c);hh=rt(I(Q))*(la+lb)
    sn=minimum(c.abs(),s)
    toll=6*sn-V*(1-maximum(c.abs(),s))
    if channel==0:return T-hh+E(W,c)+N(V,-c)-toll
    if channel==1:return T-hh+N(W,c)+N(V,-c)-toll
    if channel==2:return T-hh+D(W,c)+N(V,-c)-toll
    if channel==3:
        sd=minimum(V-K*c,K*s)/lb
        return T-hh+N(W,c)+D(V,-c)-6*sd+V*(1-maximum(V-K*c,K*s)/lb)
    assert channel==4
    pb=(V+maximum(V-K*c,K*s)+K*maximum(c.abs(),s))/rt(I(2))
    return T-hh+N(W,c)+pb-(6+V)/rt(I(2))+V

def support_margin(channel,bounds):
    """A second Fraction enclosure from the unsplit absolute support sums.

    Requiring both Fraction enclosures makes the final cells small enough
    for the independent integer verifier's support-derived formulas.
    """
    c=I(*bounds);s=sine(c);la=length(W,c);lb=length(V,-c)
    hh=rt(I(Q))*(la+lb)
    def nn(w,z):return (w*z.abs()+2*w*s+(w*z+K).abs()+K)/2
    def dd(w,z,ell):
        return (ell.sq()+w*w+w*K*z+2*w*K*s+K*(w*z+K).abs())/(2*ell)
    sn=minimum(c.abs(),s)
    toll=6*sn-V*(1-maximum(c.abs(),s))
    if channel==0:return T-hh+E(W,c)+nn(V,-c)-toll
    if channel==1:return T-hh+nn(W,c)+nn(V,-c)-toll
    if channel==2:return T-hh+dd(W,c,la)+nn(V,-c)-toll
    if channel==3:return T-hh+nn(W,c)+dd(V,-c,lb)-6*minimum(V-K*c,K*s)/lb+V*(1-maximum(V-K*c,K*s)/lb)
    adjusted=V+(maximum(V-K*c,K*s)+K*maximum(c.abs(),s)-6)/rt(I(2))
    return T-hh+nn(W,c)+adjusted

def main():
    start=time.monotonic();trees=[]
    for channel,a,b in ROOTS:
        todo=[((a,b),0)];events=[];leaves=0;depthmax=0;reserve=None
        while todo:
            box,depth=todo.pop();depthmax=max(depthmax,depth)
            lower=min(margin(channel,box).lo,support_margin(channel,box).lo)
            if lower>0:
                events.append(-1);leaves+=1
                reserve=lower if reserve is None else min(reserve,lower)
            else:
                assert depth<35,(channel,box,lower)
                mid=sum(box)/2;events.append(0)
                todo.extend([((mid,box[1]),depth+1),((box[0],mid),depth+1)])
        tree={'channel':channel,'root':[str(a),str(b)],'events':events,
              'nodes':len(events),'leaves':leaves,'maximum_depth':depthmax,
              'minimum_fraction_reserve':str(reserve)}
        trees.append(tree)
        print(json.dumps({k:v for k,v in tree.items()if k!='events'}),flush=True)
    data={'type':'universal_pair_shoulder_curved_tilt_toll_v1','toll':'6*sin(theta)-(27/2)*(1-cos(theta))',
          'status':'complete_pending_independent_replay','trees':trees,'seconds':time.monotonic()-start}
    (HERE/'universal_pair_curved_tilt_toll_cover.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'nodes':sum(t['nodes']for t in trees),'leaves':sum(t['leaves']for t in trees),'seconds':data['seconds']}),flush=True)

if __name__=='__main__':main()

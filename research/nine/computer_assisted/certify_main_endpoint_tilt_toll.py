#!/usr/bin/env python3
"""Exact rational cover producer for the original MAIN endpoint tilt toll.

The original shoulder is unrestricted.  This theorem is a reusable
inequality, not a full 001/00 exclusion.  Acceptance requires the separate
integer replay and the hand owner/frame reduction.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'interval_fraction.py').exists() else HERE.parents[1]/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from interval_fraction import I

A=F(46); B=F(27,2); K=F(207,16); T=F(211,4); Q=F(1105,256)
ROOTS=[(0,F(-1),F(-1,32)),(0,F(1,32),F(1)),
       (1,F(-1),F(-1,32)),(1,F(1,32),F(1)),
       (2,F(-1),F(1)),(3,F(-1),F(1)),(4,F(-1),F(1))]
def root(x):return x.sqrt(80)
def mini(*x):return I(min(y.lo for y in x),min(y.hi for y in x))
def maxi(*x):return I(max(y.lo for y in x),max(y.hi for y in x))
def hull(x):return I(min(y.lo for y in x),max(y.hi for y in x))
def sine(c):return root(1-c.sq())
def length(w,c):return root(w*w+K*K+2*w*K*c)
def E(w,c):return w+K*(sine(c)+maxi(c,I(0)))
def N(w,c):
    out=[]
    for low,high,kind in [(F(-1),-K/w,0),(-K/w,F(0),1),(F(0),F(1),2)]:
        l,u=max(low,c.lo),min(high,c.hi)
        if l>u:continue
        z=I(l,u);s=sine(z)
        out.append(w*(s-z) if kind==0 else K+w*s if kind==1 else K+w*(z+s))
    return hull(out)
def D(w,c):
    out=[]
    for low,high,kind in [(F(-1),-K/w,0),(-K/w,F(1),1)]:
        l,u=max(low,c.lo),min(high,c.hi)
        if l>u:continue
        z=I(l,u);s=sine(z);ell=length(w,z)
        out.append(w*(w+K*z+K*s)/ell if kind==0 else ell+w*K*s/ell)
    return hull(out)
def toll(alpha,beta):return maxi(4*beta,10*beta-A*(1-alpha))

def margin(channel,lo,hi,support=False):
    c=I(lo,hi);s=sine(c);la=length(A,c);lb=length(B,-c)
    H=root(I(Q))*(la+lb)
    if support:
        def nn(w,z):return (w*z.abs()+2*w*s+(w*z+K).abs()+K)/2
        def dd(w,z,ell):return (ell.sq()+w*w+w*K*z+2*w*K*s+K*(w*z+K).abs())/(2*ell)
        na=nn(A,c);nb=nn(B,-c);da=dd(A,c,la);db=dd(B,-c,lb)
    else:na=N(A,c);nb=N(B,-c);da=D(A,c);db=D(B,-c)
    tn=toll(maxi(c.abs(),s),mini(c.abs(),s))
    if channel==0:return T-H+na+E(B,-c)-tn
    if channel==1:return T-H+na+nb-tn
    if channel==2:return T-H+na+db-tn
    if channel==3:
        td=toll(maxi(A+K*c,K*s)/la,mini(A+K*c,K*s)/la)
        return T-H+da+nb-td
    assert channel==4
    rt2=root(I(2));pm=(A+maxi(A+K*c,K*s)+K*maxi(c.abs(),s))/rt2
    return T-H+pm+nb-toll(1/rt2,1/rt2)

def main():
    begin=time.monotonic();trees=[]
    for channel,a,b in ROOTS:
        todo=[(a,b,0)];events=[];leaves=0;depthmax=0;reserve=None
        while todo:
            lo,hi,depth=todo.pop();depthmax=max(depthmax,depth)
            lower=min(margin(channel,lo,hi).lo,margin(channel,lo,hi,True).lo)
            if lower>0:
                events.append(-1);leaves+=1
                reserve=lower if reserve is None else min(reserve,lower)
            else:
                assert depth<35,(channel,str(lo),str(hi),str(lower))
                mid=(lo+hi)/2;events.append(0)
                todo.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
        row={'channel':channel,'root':[str(a),str(b)],'events':events,
             'leaves':leaves,'nodes':len(events),'maximum_depth':depthmax,
             'minimum_fraction_reserve':str(reserve)}
        trees.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='events'}),flush=True)
    data={'type':'universal_main_endpoint_tilt_toll_v1',
          'toll':'max(4*beta,10*beta-46*(1-alpha))',
          'status':'complete_pending_independent_replay','trees':trees,
          'seconds':time.monotonic()-begin}
    (HERE/'main_endpoint_tilt_toll_cover.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'status':data['status'],'leaves':sum(t['leaves'] for t in trees),'seconds':data['seconds']}),flush=True)
if __name__=='__main__':main()

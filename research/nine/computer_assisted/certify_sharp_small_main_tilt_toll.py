#!/usr/bin/env python3
"""Exact cover discovery for k*beta-(a+k)*(1-alpha) on the original main.

The near-zero normal collar is proved analytically.  For a B-owned normal,
the original main tilt t>=1/3 is covered by the previously proved4beta
toll.  All other scalar and two-dimensional roots are covered here.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from certify_main_endpoint_tilt_toll import I,A,B,K,T,Q,E,N,D,root,mini,maxi,length,sine

ROOTS=[(0,((F(-1),F(-1,32)),)),(0,((F(1,32),F(1)),)),
       (1,((F(-1),F(-1,32)),)),(1,((F(1,32),F(1)),)),
       (2,((F(-1),F(1)),)),
       (3,((F(-1),F(-1,32)),(F(0),F(1,3)))),
       (3,((F(1,32),F(1)),(F(0),F(1,3)))),
       (4,((F(-1),F(-1,32)),(F(0),F(1,3)))),
       (4,((F(1,32),F(1)),(F(0),F(1,3))))]

def sharp(alpha,beta):return K*beta-(A+K)*(1-alpha)

def evaluate(channel,box,support=False):
    c=I(*box[0]);s=sine(c);la=length(A,c);lb=length(B,-c)
    H=root(I(Q))*(la+lb)
    def nn(w,z):return (w*z.abs()+2*w*s+(w*z+K).abs()+K)/2
    def dd(w,z,ell):return (ell.sq()+w*w+w*K*z+2*w*K*s+K*(w*z+K).abs())/(2*ell)
    if channel<=2:
        tau=sharp(maxi(c.abs(),s),mini(c.abs(),s))
        if support:
            other=[lambda:E(B,-c),lambda:nn(B,-c),lambda:dd(B,-c,lb)][channel]()
            return T-H+nn(A,c)+other-tau
        other=[lambda:E(B,-c),lambda:N(B,-c),lambda:D(B,-c)][channel]()
        return T-H+N(A,c)+other-tau
    t=I(*box[1]);alpha=1/root(1+t.sq());beta=t*alpha;eps=1 if channel==3 else -1
    def support(x,y):return ((x*alpha+eps*y*beta).abs()+(-eps*x*beta+y*alpha).abs())/2
    pm=A*(alpha+beta)/2+support(A+K*c,K*s)+K*support(c,s)
    return T-H+pm+(nn(B,-c) if support else N(B,-c))-sharp(alpha,beta)

def main():
    begin=time.monotonic();trees=[]
    for channel,rootbox in ROOTS:
        todo=[(rootbox,0)];events=[];leaves=0;depthmax=0;least=None
        while todo:
            box,depth=todo.pop();depthmax=max(depthmax,depth)
            lower=min(evaluate(channel,box).lo,evaluate(channel,box,True).lo)
            if lower>F(1,1000000000000):
                events.append(-1);leaves+=1;least=lower if least is None else min(least,lower)
            else:
                assert depth<45,(channel,[[str(x)for x in a]for a in box],str(lower))
                scores=[(hi-lo)*(1 if i==0 else 2) for i,(lo,hi) in enumerate(box)]
                dim=max(range(len(box)),key=lambda i:scores[i]);lo,hi=box[dim];mid=(lo+hi)/2
                left=list(box);right=list(box);left[dim]=(lo,mid);right[dim]=(mid,hi)
                events.append(dim);todo.extend([(tuple(right),depth+1),(tuple(left),depth+1)])
            if len(events)%50000==0:print('progress',channel,len(events),leaves,depthmax,round(time.monotonic()-begin,2),flush=True)
        row={'channel':channel,'root':[[str(x)for x in a]for a in rootbox],
             'events':events,'leaves':leaves,'nodes':len(events),'maximum_depth':depthmax,
             'minimum_fraction_reserve':str(least)}
        trees.append(row)
        print(json.dumps({k:v for k,v in row.items()if k!='events'}),flush=True)
        data={'type':'sharp_small_main_endpoint_tilt_toll_v1',
              'toll':'(207/16)*beta-(943/16)*(1-alpha)',
              'status':'complete_pending_independent_replay' if len(trees)==len(ROOTS) else 'INCOMPLETE',
              'trees':trees,'seconds':time.monotonic()-begin}
        (HERE/'sharp_small_main_tilt_toll_cover.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'status':data['status'],'leaves':sum(r['leaves']for r in trees),'seconds':data['seconds']}),flush=True)
if __name__=='__main__':main()

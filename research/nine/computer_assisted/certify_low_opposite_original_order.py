#!/usr/bin/env python3
"""Exact two-variable cover: a low opposite-half original lies below P.
Independent reconstruction is required before mathematical acceptance.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time
from ownhalf_interval_kernel import I,SCALE,frame,mn,mx

ROOT=((F(0),F(1)),(F(7,10),F(13,12)))
Q=F(1105,256);M=F(1129,3000);J=F(29927,30000)

def expressions(box,sign):
 t,X=[I(*p)for p in box];a,b,r,k=frame(t)
 c=mx(I(F(4421,12000)),1-(I(Q)-(I(F(59,60))+J).sq()).sqrt())
 q=F(503,480)-X
 loss=mx(I(0),t*(k+q))if sign>0 else mx(I(0),(q-k)/mx(t,I(F(1,4))))
 lower=mx(I(F(3,5)),c+r-loss)
 if sign>0:
  upper=mn((I(Q)-(X+k).sq()).sqrt()-r,(I(Q)-(X+r).sq()).sqrt()+k)
 else:
  upper=mn((I(Q)-(X+r).sq()).sqrt()-k,(I(Q)-(X-k).sq()).sqrt()-r)
 dmin=mx(1/(4*r)+F(707,2000),mn(1/(2*r),I(F(1,2))+F(12,17)*(1-r)),I(F(707,1000)))
 pm=mn(I(M),X-dmin)
 def B(v):return v+(1-(v+F(147,250)).sq()).sqrt()
 endpoint_min=mn(B(I(0)),B(pm))
 tau=mx(2*b,6*b-F(27,2)*(1-a))
 return [pm,upper-lower,F(9,16)-lower+X-endpoint_min,r+F(451,810)-X-F(2,27)*tau]

def main():
 start=time.monotonic();nodes=[{},{}];roots=[{'index':0,'sign':-1},{'index':1,'sign':1}]
 todo=[(1,ROOT,1,0),(0,ROOT,-1,0)];counts=[0]*4;maxdepth=0
 while todo:
  i,box,s,depth=todo.pop();maxdepth=max(maxdepth,depth);vv=expressions(box,s)
  rule=min(range(4),key=lambda j:vv[j].hi)
  if vv[rule].hi<-SCALE//1000000:
   nodes[i]={'rule':rule,'upper':str(F(vv[rule].hi,SCALE))};counts[rule]+=1;continue
  assert depth<60,('unresolved',box,s)
  axis=max(range(2),key=lambda j:(box[j][1]-box[j][0])/(ROOT[j][1]-ROOT[j][0]))
  lo,hi=box[axis];mid=(lo+hi)/2;aa,bb=list(box),list(box);aa[axis]=(lo,mid);bb[axis]=(mid,hi)
  ids=[len(nodes),len(nodes)+1];nodes[i]={'axis':axis,'children':ids};nodes.extend([{},{}])
  todo.extend([(ids[1],tuple(bb),s,depth+1),(ids[0],tuple(aa),s,depth+1)])
 out={'schema':'low_opposite_original_order_v1','status':'COMPLETE_PENDING_INDEPENDENT_REPLAY','root':[[str(a),str(b)]for a,b in ROOT],
      'roots':roots,'nodes':nodes,'counts':counts,'leaves':sum(counts),'maximum_depth':maxdepth,'remaining':0,'pending':[],'seconds':time.monotonic()-start}
 p=Path(__file__).with_name('low_opposite_original_order_cover.json');p.write_text(json.dumps(out,separators=(',',':'))+'\n')
 print('complete',len(nodes),'nodes',sum(counts),'leaves','counts',counts,'depth',maxdepth,'seconds',round(time.monotonic()-start,2),flush=True)

if __name__=='__main__':main()

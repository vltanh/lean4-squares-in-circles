#!/usr/bin/env python3
"""Exact directed-integer discovery cover for the 3D own-half side theorem.

The producer's finite forest must pass a separate arithmetic reconstruction.
Only the arithmetic kernel is reused; the physical evaluator is new here.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,itertools,json,time

from ownhalf_interval_kernel import I,SCALE,frame,mn,mx

ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(0),F(1)))
SIGNS=list(itertools.product((-1,1),repeat=3))
DELTA=F(331,20000);EPS=F(1,20)

def main_frame(pair):
 lo,hi=pair;fl=[]
 for v in (lo,hi):
  h=I(v);k=(I(F(1,2))-h.sq()).sqrt();fl.append((h+k,h-k))
 return I.raw(fl[1][0].lo,fl[0][0].hi),I.raw(fl[0][1].lo,fl[1][1].hi)

def support(f,g,s,t):
 a,b=f;c,d=g
 return mx(I(1),(1+(a*c+s*t*b*d).abs()+(t*a*d-s*b*c).abs())/2)

def clearance(dx,f,g,s,t,sig):
 terms=[]
 for (a,b),sg in ((f,s),(g,t)):
  terms.extend(((sig-sg*a*dx)/mx(b,I(EPS)),(sig+sg*b*dx)/a))
 return mn(*terms)

def main_lower(pair):
 lo,hi=pair
 def value(v):return F(32,9)*I(v)+F(41,36)/I(v)-F(32,9)-F(199,120)
 critical=F(41,128)
 if hi*hi<=critical:return value(hi)
 if lo*lo>=critical:return value(lo)
 return 4*I(82).sqrt()/9-F(32,9)-F(199,120)

def bound(box,signs):
 h=I(*box[0]);g=1/(4*h)
 fm=main_frame(box[0]);ap,bp,hp,kp=frame(I(*box[1]));ass,bs,hs,ks=frame(I(*box[2]))
 fp=(ap,bp);fs=(ass,bs);sm,sp,ss=signs
 sigms=support(fm,fs,sm,ss);sigsp=support(fs,fp,ss,sp)
 choices=[]
 for xs in (F(29,60),F(147,250)):
  cm=mn(*(clearance(I(xs)-xm,fm,fs,sm,ss,sigms)for xm in(g-DELTA,1+DELTA-h)))
  cp=mn(*(clearance(I(xp-xs),fs,fp,ss,sp,sigsp)for xp in(F(0),F(1129,3000))))
  choices.append(cm+cp)
 return hp+F(1,10)-main_lower(box[0])-mn(*choices)

def split(box,axis):
 lo,hi=box[axis];mid=(lo+hi)/2
 a,b=list(box),list(box);a[axis]=(lo,mid);b[axis]=(mid,hi)
 return tuple(a),tuple(b)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=2000000)
 ap.add_argument('--resume',action='store_true');args=ap.parse_args()
 path=Path(__file__).with_name('ownhalf_above_side_cover.json')
 roots=[{'index':i,'signs':list(s)}for i,s in enumerate(SIGNS)]
 nodes=[{}for _ in SIGNS];todo=[(i,ROOT,s,0)for i,s in reversed(list(enumerate(SIGNS)))]
 processed=leaves=maximum_depth=0;largest=None;start=last=time.monotonic()
 if args.resume:
  old=json.loads(path.read_text());nodes=old['nodes'];roots=old['roots'];processed=old['processed'];leaves=old['leaves'];maximum_depth=old['maximum_depth']
  largest=F(old['largest_upper'])if old['largest_upper']is not None else None
  todo=[(v['index'],tuple(tuple(map(F,p))for p in v['box']),tuple(v['signs']),v['depth'])for v in old['pending']]
 def save():
  out={'schema':'ownhalf_above_side_v1','status':'COMPLETE_PENDING_INDEPENDENT_REPLAY'if not todo else'INCOMPLETE',
       'root':[[str(a),str(b)]for a,b in ROOT],'roots':roots,'nodes':nodes,'processed':processed,
       'leaves':leaves,'maximum_depth':maximum_depth,'largest_upper':str(largest)if largest is not None else None,
       'remaining':len(todo),'pending':[{'index':i,'box':[[str(a),str(b)]for a,b in box],'signs':list(s),'depth':d}for i,box,s,d in todo],
       'seconds':time.monotonic()-start}
  path.write_text(json.dumps(out,separators=(',',':'))+'\n')
 limit=processed+args.max_nodes
 while todo and processed<limit:
  i,box,signs,depth=todo.pop();processed+=1;maximum_depth=max(maximum_depth,depth)
  ans=bound(box,signs)
  if ans.hi<-SCALE//100000:
   up=F(ans.hi,SCALE);nodes[i]={'rule':0,'upper':str(up)};leaves+=1;largest=up if largest is None else max(largest,up)
  else:
   assert depth<60,('unresolved',signs,box,str(F(ans.hi,SCALE)))
   axis=max(range(3),key=lambda j:(box[j][1]-box[j][0])/(ROOT[j][1]-ROOT[j][0]))
   a,b=split(box,axis);ids=[len(nodes),len(nodes)+1];nodes[i]={'axis':axis,'children':ids};nodes.extend([{},{}])
   todo.extend([(ids[1],b,signs,depth+1),(ids[0],a,signs,depth+1)])
  if time.monotonic()-last>20:
   save();print('progress',processed,'leaves',leaves,'pending',len(todo),'seconds',round(time.monotonic()-start,1),flush=True);last=time.monotonic()
 save();print('complete'if not todo else'incomplete',len(nodes),'nodes',leaves,'leaves','depth',maximum_depth,'seconds',round(time.monotonic()-start,2),flush=True)

if __name__=='__main__':main()

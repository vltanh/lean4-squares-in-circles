#!/usr/bin/env python3
"""Floating discovery only: five physical frames and original E<=A.

No numerical outcome is a proof until a separate exact forest replay.
All physical rows retain original centers, frames, and marked comparisons.
"""
from itertools import product, combinations
from functools import lru_cache
from math import sqrt
from pathlib import Path
import argparse,json,time,signal
import numpy as np
from scipy.optimize import linprog
from weak_outer_hand_right_lower_search import hbounds,supportlo,nbounds,reqlo,mulup,cap_tilt_bounds
from weak_outer_hand_C_slant_search import DIRS,EXTRA_DIRS

# Discovery-only memoization: these functions depend solely on their
# immutable interval/direction arguments.  No proof row is changed.
supportlo=lru_cache(maxsize=262144)(supportlo)
hbounds=lru_cache(maxsize=32768)(hbounds)
nbounds=lru_cache(maxsize=32768)(nbounds)
reqlo=lru_cache(maxsize=32768)(reqlo)
cap_tilt_bounds=lru_cache(maxsize=32768)(cap_tilt_bounds)

Q=1105/256;R=sqrt(Q);RHO=91/60;A=46.;B=13.5;V=2/3
PHYS=(0,2,3,4,6);PINDEX={i:k for k,i in enumerate(PHYS)}
HINDEX={1:14,5:15};GINDEX={1:16,5:17};N=18
ROOTS=tuple(product(((-.2,0.),(0.,.2)),*((((-1.,0.),(0.,1.)),)*4)))
SAT_PAIRS=((0,4),(2,3),(3,6))
INSET_PAIRS=((1,5),(1,4),(0,4),(2,4),(3,5))
TANGENTS=tuple(k/32 for k in range(16,24))
PDIRS=tuple(DIRS)+tuple(EXTRA_DIRS)

@lru_cache(maxsize=8192)
def context(box,pose):
 hs={i:hbounds(box[k]) for k,i in enumerate(PHYS)}
 hs[0]=(hs[0][0],min(hs[0][1],37/64))
 for i in HINDEX:hs[i]=(max(.5,pose[HINDEX[i]][0]),min(sqrt(.5),pose[HINDEX[i]][1],69/64-hs[0][0] if i==1 else sqrt(.5)))
 gs={i:.25/hs[i][1] for i in range(7)}
 xs=[(-RHO,-59/64-hs[0][0]),(-31/60,-27/64),
     (hs[2][0]-1/60,min(RHO-gs[2]-gs[3],133/64-1-gs[2],hs[2][1]+5/64)),
     (max(4/3,hs[2][0]-1/60+gs[2]+gs[3]),min(RHO,133/64-hs[3][0])),
     (-RHO,min(RHO-hs[4][0]-hs[6][0]-1,31/60-hs[4][0]-hs[5][0])),
     (-115/432,31/60),
     (hs[6][0]+101/432,min(RHO,133/64-hs[6][0]))]
 cb=[]
 for i in range(7):
  lo=max(xs[i][0],pose[2*i][0]);hi=min(xs[i][1],pose[2*i][1]);yl,yu=-RHO,RHO
  if i in PINDEX:
   hlo,hhi=hs[i];klo=sqrt(max(0,.5-hhi*hhi));xabs=max(0,lo,-hi)
   cap=min(RHO,max(sqrt(max(0,Q-(xabs+hlo)**2))-klo,sqrt(max(0,Q-(xabs+klo)**2))-hlo)+1e-11)
   yl,yu=-cap,cap
  cb.extend([(lo,hi),(max(yl,pose[2*i+1][0]),min(yu,pose[2*i+1][1]))])
 cb[1]=(max(cb[1][0],-.25/hs[0][0]+3/40),min(cb[1][1],.25/hs[0][0]-3/40))
 cb[5]=(cb[5][0],min(cb[5][1],-7/32-(7/8)*cb[4][0]))
 clearance=max(gs[3]+gs[6],(7/8)*(hs[3][0]+hs[6][0])-41/120)
 cb[7]=(max(cb[7][0],cb[5][0]+V),min(cb[7][1],cb[13][1]-clearance))
 cb[5]=(cb[5][0],min(cb[5][1],cb[7][1]-V))
 cb[13]=(max(cb[13][0],cb[7][0]+clearance),cb[13][1])
 cb[11]=(max(cb[11][0],cb[5][0]+gs[2]+1/sqrt(8)),cb[11][1])
 cb[9]=(cb[9][0],min(cb[9][1],cb[1][1]))
 for i in (1,5):cb.append(hs[i])
 for i in (1,5):cb.append((max(1/sqrt(8),.25/hs[i][1],pose[GINDEX[i]][0]),min(.5,.25/hs[i][0],pose[GINDEX[i]][1])))
 universal,signed=cap_tilt_bounds(box[PINDEX[3]]);dmax=min(31/30,1-hs[2][0]+universal)
 if signed is not None:dmax=min(dmax,2-hs[2][0]-signed)
 return hs,gs,cb,clearance,dmax

def diff(box,pose,i,j,xy):
 hs,gs,cb,clear,dmax=context(box,pose)
 lo,hi=cb[2*j+xy][0]-cb[2*i+xy][1],cb[2*j+xy][1]-cb[2*i+xy][0]
 if (i,j)==(2,3):lo=max(lo,gs[2]+gs[3] if xy==0 else V);hi=min(hi,dmax)
 if (i,j)==(3,6):
  if xy==0:lo=max(lo,-1459/1728);hi=min(hi,11/60)
  else:lo=max(lo,clear)
 if (i,j)==(0,4) and xy==1:hi=min(hi,0.)
 return lo,hi

def matrix(box,pose,choices):
 hs,gs,cb,clear,dmax=context(box,pose);rows=[];rhs=[]
 def add(terms,right=0.,widths=(),insets=()):
  rr=np.zeros(N)
  for j,c in terms:rr[j]+=c
  for i,c in widths:
   if i in HINDEX:rr[HINDEX[i]]+=c
   else:right-=c*(hs[i][0] if c>=0 else hs[i][1])
  for i,c in insets:
   if i in GINDEX:rr[GINDEX[i]]+=c
   else:right-=c*gs[i]
  rows.append(rr);rhs.append(right)
 for k,(lo,hi) in enumerate(cb):add(((k,1),),hi);add(((k,-1),),-lo)
 for i in range(7):
  for p,q in PDIRS:
   norm=sqrt(p*p+q*q)
   if i in PINDEX:add(((2*i,p),(2*i+1,q)),R*norm-supportlo(box[PINDEX[i]],(p,q)))
   else:
    add(((2*i,p),(2*i+1,q)),RHO*norm)
    add(((2*i,p),(2*i+1,q)),R*norm,insets=((i,abs(p)+abs(q)),))
  for xy,sg in product((0,1),(-1,1)):add(((2*i+xy,sg),),R,widths=((i,1),))
 for i in (1,5):
  for q in TANGENTS:add(((HINDEX[i],-1/(4*q*q)),(GINDEX[i],-1)),-1/(2*q))
  add(((GINDEX[i],1),(HINDEX[i],.7)),.85)
 for i,j in ((0,1),(1,2),(4,5),(5,6)):
  add(((2*i,1),(2*j,-1)),widths=((i,1),(j,1)))
 for i,j in ((0,1),(1,2),(2,3),(4,5),(5,6)):
  for sg in (-1,1):add(((2*i,1),(2*j,-1),(2*i+1,-sg),(2*j+1,sg)))
 add(((4,1),(6,-1)),insets=((2,1),(3,1)))
 add(((5,1),(7,-1)),-V)
 add(((4,-1),(6,1)),widths=((2,-1),(3,-1)))
 add(((9,1),(1,-1)))
 add(((4,-A),(12,-B)),-B/2,widths=((2,A),(6,B)))
 add(((6,1),(12,-1)),1459/1728);add(((6,-1),(12,1)),11/60)
 add(((7,1),(13,-1)),-clear)
 add(((4,7/8),(5,1)),-7/32)
 add(((5,1),(13,-1)),-97/4480,widths=((2,1),(6,1)))
 add(((5,1),(11,-1)),insets=((2,1),(5,1)))
 for sg in (-1,1):add(((5,1),(11,-1),(10,sg),(4,-sg)),-1/25)
 # Exact original AE cap, with the accepted linear A tilt toll.
 add(((0,-A),(8,-B)),211/4+17/2,widths=((0,-29),(4,-B)))
 universal,signed=cap_tilt_bounds(box[PINDEX[3]])
 add(((4,-1),(6,1)),1+universal,widths=((2,1),))
 add(((6,A),(12,B)),211/4+A*universal,widths=((6,-B),))
 if signed is None:add((),0);add((),0)
 else:
  add(((4,-1),(6,1)),2-signed,widths=((2,1),))
  add(((6,A),(12,B)),211/4+A-A*signed,widths=((6,-B),))
 # Unit-center separation, relaxed by the exact square secants on boxes.
 for i,j in combinations(range(7),2):
  lx,ux=diff(box,pose,i,j,0);ly,uy=diff(box,pose,i,j,1)
  add(((2*i,lx+ux),(2*j,-lx-ux),(2*i+1,ly+uy),(2*j+1,-ly-uy)),-1-lx*ux-ly*uy)
 for ch in choices:
  kind,i,j,axis,sg,owner=ch
  if kind=='inset':add(((2*i+axis,sg),(2*j+axis,-sg)),insets=((i,1),(j,1)))
  else:
   nn=nbounds(box[PINDEX[owner]],axis,sg);nm=[round((lo+hi)/2*2**30)/2**30 for lo,hi in nn];error=0.
   for xy in (0,1):error+=mulup((nn[xy][0]-nm[xy],nn[xy][1]-nm[xy]),diff(box,pose,i,j,xy))
   add(((2*i,nm[0]),(2*i+1,nm[1]),(2*j,-nm[0]),(2*j+1,-nm[1])),-reqlo(box[PINDEX[i]],box[PINDEX[j]])+error)
 add((),69/64,widths=((0,1),(1,1)))
 signed_A=cap_tilt_bounds(box[PINDEX[0]])[1]
 down_AE=any(kind=="sat" and (i,j)==(0,4) and nbounds(box[PINDEX[owner]],axis,sg)[1][1]<0 for kind,i,j,axis,sg,owner in choices)
 if signed_A is not None and down_AE:add(((0,-A),(8,-B)),211/4+A-A*signed_A,widths=((4,-B),))
 else:add((),0.)
 # Append-only consequences of the complete original G-edge table.
 # Every earlier row index, context bound, and secant is unchanged.
 add(((12,1),),49/64,widths=((6,-1),))
 add(((9,1),(1,-1)),insets=((0,1),(4,1)))
 for sg in (-1,1):add(((9,1),(1,-1),(8,sg),(0,-sg)),-3/20)
 add(((3,1),(11,-1)),insets=((1,1),(5,1)))
 add(((3,1),(11,-1),(10,1),(2,-1)),-1/7104)
 if signed_A is not None:add(((0,-A),(8,-B)),211/4+A-A*signed_A,widths=((4,-B),))
 else:add((),0.)
 return np.array(rows),np.array(rhs),cb

def impossible_option(box,option):
 kind,i,j,axis,sg,owner=option
 if kind=='inset':
  if (i,j)==(0,4):return (axis,sg)!=(1,-1)
  if (i,j)==(1,5):return (axis,sg)!=(1,1)
  return False
 lo,hi=box[PINDEX[owner]]
 if (i,j)==(2,3):return sg<0 or (axis==1 and lo>=0) or (axis==0 and hi<=0)
 if (i,j)==(3,6):return (axis==1 and sg<0) or (axis==0 and ((sg>0 and hi<=0) or (sg<0 and lo>=0)))
 if (i,j)==(0,4):return (axis==1 and sg>0) or (axis==0 and ((sg>0 and lo>=0) or (sg<0 and hi<=0)))
 return False

def options(box,kind,i,j):
 owners=(-1,) if kind=='inset' else (i,j)
 return [option for owner in owners for axis,sg in product((0,1),(-1,1))
         if not impossible_option(box,option:=(kind,i,j,axis,sg,owner))]

def excluded_selected_separator(box,choices):
 # All exclusions are proved for the strict original caller, including
 # its new G-edge consequences.  Signed angle endpoints handle zero
 # faces exactly rather than testing padded floating normal intervals.
 return any(impossible_option(box,option) for option in choices)

def solve(box,pose,ch):
 aa,bb,cb=matrix(box,pose,ch)
 rr=linprog(np.r_[np.zeros(N),1.],A_ub=np.c_[aa,-np.ones(len(bb))],b_ub=bb,bounds=[(None,None)]*(N+1),method='highs',options={'threads':1})
 if rr.success and rr.x[-1]>1e-7:
  lam=-rr.ineqlin.marginals;weights=[(int(i),int(round(v*2**40))) for i,v in enumerate(lam) if v>1e-13];ll=np.zeros(len(bb))
  for i,w in weights:ll[i]=w/2**40
  reserve=-ll@bb-RHO*sum(abs(ll@aa))
  if reserve>1e-8:return {'weights':weights,'power':40,'discovery_reserve':float(reserve)},rr.x[:N],cb
 return None,(rr.x[:N] if rr.success else None),cb

def next_branch(box,pose,ch,point,cb):
 selected={(z[0],z[1],z[2]) for z in ch}
 if point is not None:
  C=point[:14].reshape(7,2);angles={i:sum(box[k])/2 for k,i in enumerate(PHYS)}
  h={i:hbounds((angles[i],angles[i]))[0] for i in PHYS};h.update({i:point[HINDEX[i]] for i in (1,5)})
  candidates=[]
  for i,j in INSET_PAIRS:
   if ('inset',i,j) not in selected:
    defect=.25/h[i]+.25/h[j]-max(abs(C[j]-C[i]))
    if defect>1e-6:candidates.append((defect,('sep','inset',i,j)))
  for i,j in SAT_PAIRS:
   if ('sat',i,j) not in selected:
    req=reqlo((angles[i],angles[i]),(angles[j],angles[j]));best=-1e10
    for owner in (i,j):
     t=angles[owner];r=sqrt(1+t*t)
     best=max(best,abs(np.dot((1/r,t/r),C[j]-C[i])),abs(np.dot((-t/r,1/r),C[j]-C[i])))
    if req-best>1e-6:candidates.append((req-best,('sep','sat',i,j)))
  if candidates:return max(candidates,key=lambda z:z[0])[1]
  # Center-distance secants need position refinement when genuinely loose.
  bad=[]
  for i,j in combinations(range(7),2):
   defect=1-float(np.dot(C[j]-C[i],C[j]-C[i]))
   if defect>1e-4:
    choices=[2*i,2*i+1,2*j,2*j+1];k=max(choices,key=lambda k:cb[k][1]-cb[k][0]);bad.append((defect,k))
  if bad and max(u-l for l,u in box)<.25:return ('pose',max(bad)[1])
  for i in (1,5):
   if .25/point[HINDEX[i]]-point[GINDEX[i]]>1e-4 and max(u-l for l,u in box)<.125:return ('pose',HINDEX[i])
  # Refine the original angle responsible for a concrete physical corner
  # or width violation; this changes only search order, never proof rows.
  angle_bad=[]
  for i in PHYS:
   t=angles[i];r=sqrt(1+t*t);u=np.array((1/r,t/r));w=np.array((-t/r,1/r))
   defect=max(float(np.dot(C[i]+(sx*u+sy*w)/2,C[i]+(sx*u+sy*w)/2))-Q for sx,sy in product((-1,1),repeat=2))
   k=PINDEX[i]
   if defect>1e-5 and box[k][1]-box[k][0]>1/4096:angle_bad.append((defect,k))
  for i,j in ((0,1),(1,2),(4,5),(5,6)):
   defect=h[i]+h[j]-(C[j,0]-C[i,0])
   for owner in (i,j):
    if owner in PINDEX:
     k=PINDEX[owner]
     if defect>1e-5 and box[k][1]-box[k][0]>1/4096:angle_bad.append((defect,k))
  if angle_bad:return ('angle',max(angle_bad)[1])
 widths=[u-l for l,u in box];k=int(np.argmax(widths))
 if widths[k]>1/1024:return ('angle',k)
 k=max(range(N),key=lambda k:cb[k][1]-cb[k][0]);return ('pose',k)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--nodes',type=int,default=5000);ap.add_argument('--depth',type=int,default=40);ap.add_argument('--root-ids');ap.add_argument('--resume',type=Path);ap.add_argument('--checkpoint-every',type=int,default=5000);args=ap.parse_args();start=time.time()
 initpose=tuple([(-RHO,RHO)]*14+[(.5,5/7)]*2+[(7/20,.5)]*2)
 ids=set(range(32)) if not args.root_ids else {int(v) for v in args.root_ids.split(',')}
 stack=[(i,box,initpose,(),0,{'root':i}) for i,box in enumerate(ROOTS) if i in ids];leaves=[];front=[];nodes=0;maxdepth=0
 if args.resume:
  old=json.loads(args.resume.read_text());leaves=old['leaves'];nodes=old['nodes'];maxdepth=old['max_depth'];stack=[]
  for z in old['frontier']:
   bo=tuple(tuple(v) for v in z['box']);ch=tuple(tuple(v) for v in z['choice'])
   if not excluded_selected_separator(bo,ch):stack.append((z['root'],bo,tuple(tuple(v) for v in z['pose']),ch,z['depth'],z['path']))
 stop=[False]
 def request_stop(signum,frame):stop[0]=True
 signal.signal(signal.SIGINT,request_stop)
 def save():
  pending=list(front)
  pending.extend({'root':r,'box':bo,'pose':po,'choice':ch,'path':pa,'depth':dep} for r,bo,po,ch,dep,pa in stack)
  out={'proof':False,'scope':'Floating five-frame E-order discovery; exact replay and physical-source review required','nodes':nodes,'leaves':leaves,'frontier':pending,'max_depth':maxdepth,'seconds':time.time()-start}
  temporary=args.out.with_suffix(args.out.suffix+'.tmp');temporary.write_text(json.dumps(out,separators=(',',':'))+'\n');temporary.replace(args.out)
  return len(pending)
 while stack and nodes<args.nodes and not stop[0]:
  root,box,pose,ch,depth,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,depth);hit,point,cb=solve(box,pose,ch)
  if hit:leaves.append({'root':root,'box':box,'pose':pose,'choice':ch,'path':path,**hit})
  elif depth>=args.depth:front.append({'root':root,'box':box,'pose':pose,'choice':ch,'path':path,'depth':depth,'point':point.tolist() if point is not None else None})
  else:
   br=next_branch(box,pose,ch,point,cb)
   if br[0]=='sep':
    _,kind,i,j=br
    for option in options(box,kind,i,j):stack.append((root,box,pose,ch+(option,),depth+1,{'parent':path,'sep':option}))
   elif br[0]=='angle':
    k=br[1];l,u=box[k];m=(l+u)/2
    for side,T in enumerate(((l,m),(m,u))):
     bo=list(box);bo[k]=T;stack.append((root,tuple(bo),pose,ch,depth+1,{'parent':path,'angle':k,'side':side}))
   else:
    k=br[1];l,u=cb[k];mid=round((l+u)/2*2**20);m=mid/2**20
    if not pose[k][0]<m<pose[k][1]:
     front.append({'root':root,'box':box,'pose':pose,'choice':ch,'path':path,'depth':depth,'point':point.tolist() if point is not None else None});continue
    for side,T in enumerate(((pose[k][0],m),(m,pose[k][1]))):
     po=list(pose);po[k]=T;stack.append((root,box,tuple(po),ch,depth+1,{'parent':path,'pose':k,'cut_integer':mid,'cut_power':20,'side':side}))
  if nodes%100==0:print(nodes,len(leaves),len(stack),len(front),maxdepth,'root',root,'seconds',round(time.time()-start,1),flush=True)
  if args.checkpoint_every and nodes%args.checkpoint_every==0:save()
 remaining=save();print('finished',nodes,'leaves',len(leaves),'frontier',remaining,'seconds',round(time.time()-start,2),flush=True)
if __name__=='__main__':main()

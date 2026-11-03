#!/usr/bin/env python3
"""Floating discovery of the three-original DG vertical-gap upper exclusion for v>=2/3."""
from itertools import product
from math import sqrt, gcd
from functools import lru_cache
import warnings
warnings.filterwarnings("ignore", message="Unrecognized options detected.*")
from pathlib import Path
import argparse, json, time
import numpy as np
from scipy.optimize import linprog
from weak_outer_hand_right_lower_search import hbounds, supportlo, nbounds, reqlo, mulup, cap_tilt_bounds

Q=1105/256;rho=91/60;a=46.;b=13.5;V=2/3
_dirs={(x,y) for x in range(-4,5) for y in range(-4,5) if (x or y) and gcd(x,y)==1}
for p,q in ((32,9),(128,35),(128,37),(24,23),(96,91),(32,31)):
 for x,y in ((p,q),(q,p)):
  for sx,sy in product((-1,1),repeat=2):_dirs.add((sx*x,sy*y))
DIRS=sorted(_dirs)
EXTRA_DIRS=sorted({(sx*(1024-k*k)/(1024+k*k),sy*(64*k)/(1024+k*k)) for k in range(33) for sx,sy in product((-1,1),repeat=2)})
ANGLE_ROOTS=tuple(product(((-1.,0.),(0.,1.)),repeat=3))
ROOTS=tuple((('DG_upper',None),box) for box in ANGLE_ROOTS)
PAIRS=((0,1),(1,2),(0,2))

@lru_cache(maxsize=8192)
def center_bounds(root,box):
 domain=ROOTS[root][0];hs=[hbounds(T) for T in box];gs=[.25/h[1] for h in hs]
 X=[(hs[0][0]-1/60,min(rho-gs[0]-gs[1],133/64-1-gs[0],hs[0][1]+5/64)),
    (max(4/3,hs[0][0]-1/60+gs[0]+gs[1]),min(rho,133/64-hs[1][0])),
    (hs[2][0]+101/432,min(rho,133/64-hs[2][0]))]
 Y=[]
 for i in range(3):
  hlo,hhi=hs[i];klo=sqrt(max(0,.5-hhi*hhi));xlo=X[i][0]
  cap=min(rho,max(sqrt(max(0,Q-(xlo+hlo)**2))-klo,sqrt(max(0,Q-(xlo+klo)**2))-hlo)+1e-11)
  Y.append((-cap,cap))
 Y[0]=(Y[0][0],min(Y[0][1],-7/32-(7/8)*X[0][0]))
 clearance=max(79/50,(7/8)*(hs[1][0]+hs[2][0])-41/120,gs[1]+gs[2])
 Y[1]=(max(Y[1][0],Y[0][0]+V),min(Y[1][1],Y[2][1]-clearance))
 Y[0]=(Y[0][0],min(Y[0][1],Y[1][1]-V))
 Y[2]=(max(Y[2][0],Y[1][0]+clearance),Y[2][1])
 universal,signed=cap_tilt_bounds(box[1]);dmax=min(31/30,1-hs[0][0]+universal)
 if signed is not None:dmax=min(dmax,2-hs[0][0]-signed)
 return hs,gs,[z for i in range(3) for z in (X[i],Y[i])],clearance,dmax

def difference_interval(root,box,k,xy):
 hs,gs,CB,clearance,dmax=center_bounds(root,box);i,j=PAIRS[k]
 dr=(CB[2*j+xy][0]-CB[2*i+xy][1],CB[2*j+xy][1]-CB[2*i+xy][0])
 if k==0:dr=(max(dr[0],gs[0]+gs[1]),min(dr[1],dmax)) if xy==0 else (max(dr[0],V),min(dr[1],dmax))
 if k==1:dr=(max(dr[0],-1459/1728),min(dr[1],11/60)) if xy==0 else (max(dr[0],clearance),dr[1])
 if k==2 and xy==1:dr=(max(dr[0],V+clearance,hs[0][0]+hs[2][0]+97/4480),dr[1])
 return dr

def matrix(root,box,choice):
 hs,gs,CB,clearance,dmax=center_bounds(root,box);domain=ROOTS[root][0]
 rows=[];rhs=[]
 def add(row,right):rows.append(row);rhs.append(right)
 def basis(i,v):r=np.zeros(6);r[i]=v;return r
 for k,(l,u) in enumerate(CB):add(basis(k,1),u);add(basis(k,-1),-l)
 for i in range(3):
  for p,q in DIRS:
   rr=np.zeros(6);rr[2*i:2*i+2]=(p,q)
   add(rr,sqrt(Q*(p*p+q*q))-supportlo(box[i],(p,q)))
 rr=np.zeros(6);rr[0]=-a;rr[4]=-b;add(rr,-6.75-a*hs[0][0]-b*hs[2][0])
 rr=np.zeros(6);rr[0]=1;rr[2]=-1;add(rr,-gs[0]-gs[1])
 rr=np.zeros(6);rr[1]=1;rr[3]=-1;add(rr,-V)
 rr=np.zeros(6);rr[0]=1;rr[2]=-1;rr[1]=-1;rr[3]=1;add(rr,0.)
 rr=np.zeros(6);rr[0]=-1;rr[2]=1;add(rr,hs[0][1]+hs[1][1])
 rr=np.zeros(6);rr[3]=1;rr[5]=-1;add(rr,0.)
 rr=np.zeros(6);rr[2]=1;rr[4]=-1;add(rr,1459/1728)
 rr=np.zeros(6);rr[2]=-1;rr[4]=1;add(rr,11/60)
 rr=np.zeros(6);rr[3]=1;rr[5]=-1;add(rr,-79/50)
 rr=np.zeros(6);rr[0]=7/8;rr[1]=1;add(rr,-7/32)
 for k,(owner,axis,sgn) in enumerate(choice):
  i,j=PAIRS[k];nn=nbounds(box[owner],axis,sgn);nm=np.array([round((lo+hi)/2*2**30)/2**30 for lo,hi in nn]);error=0.
  for xy in (0,1):error+=mulup((nn[xy][0]-nm[xy],nn[xy][1]-nm[xy]),difference_interval(root,box,k,xy))
  rr=np.zeros(6);rr[2*i:2*i+2]=nm;rr[2*j:2*j+2]=-nm;add(rr,-reqlo(box[i],box[j])+error)
 rr=np.zeros(6);rr[3]=1;rr[5]=-1;add(rr,-clearance)
 universal,signed=cap_tilt_bounds(box[1]);rr=np.zeros(6);rr[0]=-1;rr[2]=1
 add(rr,1-hs[0][0]+universal);add(rr if signed is not None else np.zeros(6),2-hs[0][0]-signed if signed is not None else 0.)
 rr=np.zeros(6);rr[2]=a;rr[4]=b
 add(rr,211/4+a*universal+b*hs[2][1]);add(rr if signed is not None else np.zeros(6),211/4+a-a*signed+b*hs[2][1] if signed is not None else 0.)
 for i in range(3):
  for p,q in EXTRA_DIRS:
   rr=np.zeros(6);rr[2*i:2*i+2]=(p,q)
   add(rr,sqrt(Q)-supportlo(box[i],(p,q)))
 rr=np.zeros(6);rr[1]=1;rr[5]=-1;add(rr,-hs[0][0]-hs[2][0]-97/4480)
 return np.array(rows),np.array(rhs)

def contradiction(root,box,ch):
 AA,BB=matrix(root,box,ch)
 rr=linprog(np.r_[np.zeros(6),1.],A_ub=np.c_[AA,-np.ones(len(BB))],b_ub=BB,bounds=[(None,None)]*7,method='highs',options={'threads':1})
 if rr.success and rr.x[-1]>1e-7:
  lam=-rr.ineqlin.marginals;terms=[(int(i),int(round(v*2**40))) for i,v in enumerate(lam) if v>1e-13];ll=np.zeros(len(BB))
  for i,v in terms:ll[i]=v/2**40
  reserve=-ll@BB-rho*sum(abs(ll@AA))
  if reserve>1e-8:return {'weights':terms,'power':40,'discovery_reserve':float(reserve)}
 return None

def options(box,k):
 i,j=PAIRS[k];out=[]
 for owner in (i,j):
  for axis in (0,1):
   for sgn in (-1,1):
    nn=nbounds(box[owner],axis,sgn)
    if k==1 and ((axis==1 and sgn<0) or (axis==0 and ((sgn>0 and box[owner][1]<=0) or (sgn<0 and box[owner][0]>=0)))):continue
    # This uses the original strict weak-cone sign theorem. The matrix's
    # closed weak row is only a necessary relaxation of that original caller.
    if k==0 and (sgn<0 or (axis==1 and box[owner][0]>=0) or (axis==0 and box[owner][1]<=0)):continue
    out.append((owner,axis,sgn))
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--nodes',type=int,default=100000);ap.add_argument('--depth',type=int,default=40);ap.add_argument('--root-ids');ap.add_argument('--pairs',type=int,default=1);ap.add_argument('--resume',type=Path);args=ap.parse_args();start=time.time()
 stack=[(i,box,(),0,{'root':i}) for i,(_,box) in enumerate(ROOTS)];leaves=[];front=[];nodes=0;maxdep=0
 if args.root_ids:
  ids={int(s) for s in args.root_ids.split(',')};assert ids<=set(range(len(ROOTS)));stack=[z for z in stack if z[0]in ids]
 if args.resume:
  old=json.loads(args.resume.read_text());leaves=old['leaves'];nodes=old['nodes'];maxdep=old['max_depth'];stack=[]
  for z in old['frontier']:stack.append((z['root'],tuple(tuple(v) for v in z['box']),tuple(tuple(v) for v in z['choice']),z['depth'],z['path']))
 while stack and nodes<args.nodes:
  root,box,ch,depth,path=stack.pop();nodes+=1;maxdep=max(maxdep,depth);hit=contradiction(root,box,ch)
  if hit:leaves.append({'root':root,'box':box,'choice':ch,'path':path,**hit})
  elif depth>=args.depth:front.append({'root':root,'box':box,'choice':ch,'depth':depth,'path':path})
  else:
   widths=[u-l for l,u in box]
   if len(ch)<args.pairs and max(widths)<=.5:
    for option in options(box,len(ch)):stack.append((root,box,ch+(option,),depth+1,{'parent':path,'sep':option}))
   else:
    k=int(np.argmax(widths));l,u=box[k];m=(l+u)/2
    for side,T in enumerate(((l,m),(m,u))):
     bo=list(box);bo[k]=T;stack.append((root,tuple(bo),ch,depth+1,{'parent':path,'axis':k,'side':side}))
  if nodes%100==0:print(nodes,len(leaves),len(stack),len(front),maxdep,'root',root,'seconds',round(time.time()-start,1),flush=True)
 if stack:front.extend({'root':root,'box':bo,'choice':ch,'depth':dep,'path':path} for root,bo,ch,dep,path in stack)
 obj={'proof':False,'scope':'Floating discovery; independent exact replay required','nodes':nodes,'leaves':leaves,'frontier':front,'max_depth':maxdep,'seconds':time.time()-start}
 with args.out.open('w') as f:json.dump(obj,f,separators=(',',':'));f.write('\n')
 print({k:obj[k] for k in ('nodes','max_depth','seconds')},'leaves',len(leaves),'frontier',len(front),flush=True)

if __name__=='__main__':main()

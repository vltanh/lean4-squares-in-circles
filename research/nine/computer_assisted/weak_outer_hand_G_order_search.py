#!/usr/bin/env python3
"""DISCOVERY ONLY: orientation-box LP cover for G_y <= D_y in 001/00.

Floating calculations propose rational Farkas rows; a separate exact replay is
required before any exclusion is accepted. No Lean/Lake/CI.
"""
from itertools import product
from math import sqrt,gcd
from pathlib import Path
import argparse,json,time
import numpy as np
from scipy.optimize import linprog
Q=1105/256; R=sqrt(Q); rho=91/60;a=46.;b=13.5
DIRS=[(x,y) for x in range(-4,5) for y in range(-4,5) if (x or y) and gcd(x,y)==1]
PAIRS=[(1,2),(0,2),(0,1)]
def supportlo(T,w):
 l,h=T; x,y=w; ts=[l,h]
 if y and l<=-x/y<=h:ts.append(-x/y)
 if x and l<=y/x<=h:ts.append(y/x)
 return min((abs(x+y*t)+abs(y-x*t))/(2*sqrt(1+t*t)) for t in ts)-1e-12

def hbounds(T):
 l,u=T;f=lambda t:(1+abs(t))/(2*sqrt(1+t*t));vals=[f(l),f(u)]
 return (.5 if l<=0<=u else min(vals))-1e-12,max(vals)+1e-12

def nbounds(T,axis,sgn):
 l,h=T; m=0 if l<=0<=h else min(abs(l),abs(h));M=max(abs(l),abs(h))
 A=(1/sqrt(1+M*M)-1e-12,1/sqrt(1+m*m)+1e-12)
 B=(l/sqrt(1+l*l)-1e-12,h/sqrt(1+h*h)+1e-12)
 if axis: A,B=(-B[1],-B[0]),A
 if sgn<0:A=(-A[1],-A[0]);B=(-B[1],-B[0])
 return A,B

def reqlo(T,U):
 if max(T[0],U[0])<=min(T[1],U[1]):return 1.
 ts=[(T[0],U[1]),(T[1],U[0])]
 return .5*(1+min((1+t*u+abs(t-u))/sqrt((1+t*t)*(1+u*u)) for t,u in ts))-1e-12

def mulup(A,B):return max(x*y for x in A for y in B)

def matrix(box,choice):
 hs=[hbounds(T) for T in box];gs=[.25/h[1] for h in hs]
 X=[(hs[0][0]-1/60,rho-gs[0]-gs[1]),(hs[0][0]-1/60+gs[0]+gs[1],rho),(hs[2][0]-1/60,rho)]
 Y=[]
 for i in range(3):
  hlo,hhi=hs[i];klo=sqrt(max(0,.5-hhi*hhi));xlo=X[i][0]
  cap=max(sqrt(max(0,Q-(xlo+hlo)**2))-klo,sqrt(max(0,Q-(xlo+klo)**2))-hlo)
  Y.append((-min(rho,cap+1e-11),min(rho,cap+1e-11)))
 CB=[q for i in range(3) for q in (X[i],Y[i])]
 # Strict physical statements are relaxed to closed inequalities throughout.
 rows=[];rhs=[];names=[]
 def add(co,rv,name):rows.append(co);rhs.append(rv);names.append(name)
 def unit(k,s):v=np.zeros(6);v[k]=s;return v
 for k,(l,u) in enumerate(CB):add(unit(k,1),u,'bound_up_'+str(k));add(unit(k,-1),-l,'bound_lo_'+str(k))
 for i in range(3):
  for p,q in DIRS:
   rr=np.zeros(6);rr[2*i:2*i+2]=(p,q)
   add(rr,sqrt(Q*(p*p+q*q))-supportlo(box[i],(p,q)),f'circle_{i}_{p}_{q}')
 rr=np.zeros(6);rr[0]=-a;rr[4]=-b
 add(rr,-6.75-a*hs[0][0]-b*hs[2][0],'left_cap_and_chains')
 rr=np.zeros(6);rr[0]=1;rr[2]=-1;add(rr,-gs[0]-gs[1],'CD_inset')
 rr=np.zeros(6);rr[1]=1;rr[3]=-1;add(rr,-7/30,'CD_transverse')
 rr=np.zeros(6);rr[0]=1;rr[2]=-1;rr[1]=-1;rr[3]=1;add(rr,0,'CD_cone')
 rr=np.zeros(6);rr[0]=-1;rr[2]=1;add(rr,hs[0][1]+hs[1][1],'CD_weak')
 rr=np.zeros(6);rr[3]=-1;rr[5]=1;add(rr,0,'G_below_D')
 rr=np.zeros(6);rr[2]=1;rr[4]=-1;add(rr,1459/1728,'DG_horizontal_cap')
 for k,ch in enumerate(choice):
  i,j=PAIRS[k];owner,ax,sgn=ch
  nn=nbounds(box[owner],ax,sgn)
  nm=np.array([round((v[0]+v[1])/2*2**30)/2**30 for v in nn])
  error=0
  for xy in (0,1):
   v=nn[xy];ee=(v[0]-nm[xy],v[1]-nm[xy]);dr=(CB[2*j+xy][0]-CB[2*i+xy][1],CB[2*j+xy][1]-CB[2*i+xy][0])
   if k==0:
    if xy==0:dr=(max(dr[0],-1459/1728),min(dr[1],1))
    else:dr=(dr[0],min(dr[1],0))
   if k==2:
    if xy==0:dr=(max(dr[0],gs[0]+gs[1]),min(dr[1],31/30))
    else:dr=(max(dr[0],7/30),min(dr[1],31/30))
   error+=mulup(ee,dr)
  rr=np.zeros(6);rr[2*i:2*i+2]=nm;rr[2*j:2*j+2]=-nm
  add(rr,-reqlo(box[i],box[j])+error,'sep_'+str(k))
 return np.array(rows),np.array(rhs),names

def contradiction(box,choice):
 A,B,names=matrix(box,choice)
 # Phase I keeps every center unrestricted; all necessary bounds are rows.
 c=np.r_[np.zeros(6),1.]
 rr=linprog(c,A_ub=np.c_[A,-np.ones(len(B))],b_ub=B,bounds=[(None,None)]*7,method='highs')
 if rr.success and rr.x[-1]>1e-7:
  lam=-rr.ineqlin.marginals;terms=[(int(i),int(round(v*2**40))) for i,v in enumerate(lam) if v>1e-13]
  ll=np.zeros(len(B))
  for i,v in terms:ll[i]=v/2**40
  reserve=-ll@B-rho*sum(abs(ll@A))
  if reserve>1e-8:return {'weights':terms,'power':40,'discovery_reserve':float(reserve)}
 return None

def options(box,pairindex):
 i,j=PAIRS[pairindex];ans=[]
 for owner in (i,j):
  for ax in (0,1):
   for sgn in (-1,1):
    n=nbounds(box[owner],ax,sgn)
    if pairindex==0 and n[1][0]>=-1e-10:continue
    if pairindex==2 and n[0][1]<=0 and n[1][1]<=0:continue
    ans.append((owner,ax,sgn))
 return ans

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--nodes',type=int,default=20000);ap.add_argument('--depth',type=int,default=40);ap.add_argument('--initial-width',type=float,default=.5);ap.add_argument('--resume',type=Path);args=ap.parse_args()
 start=time.time();roots=list(product(((-1.,0.),(0.,1.)),repeat=3));stack=[(box,(),0,{'root':i}) for i,box in enumerate(roots)]; leaves=[];front=[];nodes=0;maxdep=0
 if args.resume:
  old=json.loads(args.resume.read_text());leaves=old['leaves'];nodes=old['nodes'];maxdep=old['max_depth'];stack=[]
  def recoverpath(target,choice):
   root=next(i for i,bo in enumerate(roots) if all(bo[k][0]<=target[k][0] and target[k][1]<=bo[k][1] for k in range(3)))
   box=roots[root];ch=();path={'root':root};depth=0
   while box!=target or ch!=choice:
    widths=[v[1]-v[0] for v in box]
    if len(ch)<3 and max(widths)<=args.initial_width:
     o=choice[len(ch)];ch=ch+(o,);path={'parent':path,'sep':o}
    else:
     k=int(np.argmax(widths));l,u=box[k];m=(l+u)/2
     side=0 if target[k][1]<=m else 1
     new=list(box);new[k]=(l,m) if side==0 else (m,u);box=tuple(new);path={'parent':path,'axis':k,'side':side}
    depth+=1
    if depth>100:raise ValueError('path reconstruction failed')
   return path,depth
  for ff in old['frontier']:
   bo=tuple(tuple(v) for v in ff['box']);ch=tuple(tuple(v) for v in ff['choice']);path,dep=recoverpath(bo,ch)
   assert dep==ff['depth'];stack.append((bo,ch,dep,path))
 while stack and nodes<args.nodes:
  box,ch,depth,path=stack.pop();nodes+=1;maxdep=max(maxdep,depth)
  hit=contradiction(box,ch)
  if hit:
   leaves.append({'box':box,'choice':ch,'path':path,**hit})
  elif depth>=args.depth:front.append({'box':box,'choice':ch,'depth':depth,'path':path})
  else:
   widths=[v[1]-v[0] for v in box]
   if len(ch)<3 and max(widths)<=args.initial_width:
    opts=options(box,len(ch))
    for o in opts:stack.append((box,ch+(o,),depth+1,{'parent':path,'sep':o}))
   else:
    k=int(np.argmax(widths));l,u=box[k];m=(l+u)/2
    for side,(x,y) in enumerate(((l,m),(m,u))):
     new=list(box);new[k]=(x,y);stack.append((tuple(new),ch,depth+1,{'parent':path,'axis':k,'side':side}))
  if nodes%100==0:
   print(nodes,len(leaves),len(stack),len(front),maxdep,'seconds',round(time.time()-start,1),flush=True)
 if stack:front.extend({'box':bo,'choice':c,'depth':d,'path':p} for bo,c,d,p in stack)
 obj={'proof':False,'scope':'Floating discovery only; exact replay required','nodes':nodes,'leaves':leaves,'frontier':front,'max_depth':maxdep,'seconds':time.time()-start,'directions':DIRS}
 args.out.write_text(json.dumps(obj,separators=(',',':'))+'\n')
 print({k:obj[k] for k in ('nodes','max_depth','seconds')},'leaves',len(leaves),'frontier',len(front),flush=True)
if __name__=='__main__':main()

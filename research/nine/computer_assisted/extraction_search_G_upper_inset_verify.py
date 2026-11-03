#!/usr/bin/env python3
"""Independent exact replay for the three-original G upper-inset forest for v>=2/3.

The imported helpers are exact Fraction/radical formulas from the separately
reviewed rational replayer, never numerical discovery or optimizer code.
Both exact-source hashes are included in the final report.
"""
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import argparse,gzip,json,hashlib,time
from weak_outer_hand_right_lower_verify import (
 F,Q,RHO,A,B,ROOT_BITS,root_bounds,quotient_bounds,h_bounds,support_lower,
 normal_bounds,pair_support_lower,cap_tilt_bounds)

_dirs={(x,y) for x in range(-4,5) for y in range(-4,5) if (x or y) and gcd(x,y)==1}
for p,q in ((32,9),(128,35),(128,37),(24,23),(96,91),(32,31)):
 for x,y in ((p,q),(q,p)):
  for sx,sy in product((-1,1),repeat=2):_dirs.add((sx*x,sy*y))
DIRS=tuple(sorted(_dirs))
EXTRA_DIRS=tuple(sorted({(F(sx*(1024-k*k),1024+k*k),F(sy*64*k,1024+k*k)) for k in range(33) for sx,sy in product((-1,1),repeat=2)}))
V=F(2,3)
ANGLE_ROOTS=tuple(product(((F(-1),F(0)),(F(0),F(1))),repeat=3))
ROOTS=tuple((('G_upper_inset',None),box) for box in ANGLE_ROOTS)
PAIRS=((0,1),(1,2),(0,2))

@lru_cache(maxsize=4096)
def context(root,box):
 domain=ROOTS[root][0];hs=tuple(h_bounds(T) for T in box);gs=tuple(F(1,4)/h[1] for h in hs)
 xs=[(hs[0][0]-F(1,60),min(RHO-gs[0]-gs[1],F(133,64)-1-gs[0],hs[0][1]+F(5,64))),
     (max(F(4,3),hs[0][0]-F(1,60)+gs[0]+gs[1]),min(RHO,F(133,64)-hs[1][0])),
     (hs[2][0]+F(101,432),min(RHO,F(133,64)-hs[2][0],F(49,64)+hs[2][1]))]
 ys=[]
 for i in range(3):
  hlo,hhi=hs[i];klo=root_bounds(max(F(0),F(1,2)-hhi*hhi))[0];xlo=xs[i][0]
  cap=min(RHO,max(root_bounds(max(F(0),Q-(xlo+hlo)**2))[1]-klo,root_bounds(max(F(0),Q-(xlo+klo)**2))[1]-hlo))
  ys.append((-cap,cap))
 ys[0]=(ys[0][0],min(ys[0][1],-F(7,32)-F(7,8)*xs[0][0]))
 ys[2]=(ys[2][0],min(ys[2][1],F(3,40)+F(1,4)/hs[2][0]))
 clearance=max(F(7,8)*(hs[1][0]+hs[2][0])-F(41,120),gs[1]+gs[2])
 ys[1]=(max(ys[1][0],ys[0][0]+V),min(ys[1][1],ys[2][1]-clearance))
 ys[0]=(ys[0][0],min(ys[0][1],ys[1][1]-V))
 ys[2]=(max(ys[2][0],ys[1][0]+clearance),ys[2][1])
 universal,signed=cap_tilt_bounds(box[1]);dmax=min(F(31,30),1-hs[0][0]+universal)
 if signed is not None:dmax=min(dmax,2-hs[0][0]-signed)
 cb=tuple(z for i in range(3) for z in (xs[i],ys[i]))
 return hs,gs,cb,clearance,dmax

def difference_interval(root,box,k,xy):
 hs,gs,cb,clearance,dmax=context(root,box);i,j=PAIRS[k]
 dr=(cb[2*j+xy][0]-cb[2*i+xy][1],cb[2*j+xy][1]-cb[2*i+xy][0])
 if k==0:dr=(max(dr[0],gs[0]+gs[1]),min(dr[1],dmax)) if xy==0 else (max(dr[0],V),min(dr[1],dmax))
 if k==1:dr=(max(dr[0],-F(1459,1728)),min(dr[1],F(11,60))) if xy==0 else (max(dr[0],clearance),dr[1])
 if k==2 and xy==1:dr=(max(dr[0],V+clearance,hs[0][0]+hs[2][0]+F(97,4480)),dr[1])
 return dr

def interval_witness(root,box,ch):
 for k,(lo,hi) in enumerate(context(root,box)[2]):
  if lo>hi:return ['coordinate',k],lo-hi
 for k in range(len(ch)):
  for xy in (0,1):
   lo,hi=difference_interval(root,box,k,xy)
   if lo>hi:return ['difference',k,xy],lo-hi
 return None,None

def basis(i,v):
 row=[F(0)]*6;row[i]=v;return row

def rational_row(index,root,box,ch):
 hs,gs,cb,clearance,dmax=context(root,box);domain=ROOTS[root][0];row=[F(0)]*6
 if index<12:
  k=index//2
  return (basis(k,F(1)),cb[k][1]) if index%2==0 else (basis(k,F(-1)),-cb[k][0])
 index-=12
 if index<3*len(DIRS):
  i,j=divmod(index,len(DIRS));p,q=DIRS[j];row[2*i]=F(p);row[2*i+1]=F(q)
  return row,root_bounds(Q*(p*p+q*q))[1]-support_lower(box[i],(p,q))
 index-=3*len(DIRS)
 if index==0:row[0]=-A;row[4]=-B;return row,-F(27,4)-A*hs[0][0]-B*hs[2][0]
 if index==1:row[0]=1;row[2]=-1;return row,-gs[0]-gs[1]
 if index==2:row[1]=1;row[3]=-1;return row,-V
 if index==3:row[0]=1;row[2]=-1;row[1]=-1;row[3]=1;return row,F(0)
 if index==4:row[0]=-1;row[2]=1;return row,hs[0][1]+hs[1][1]
 if index==5:row[3]=1;row[5]=-1;return row,F(0)
 if index==6:row[2]=1;row[4]=-1;return row,F(1459,1728)
 if index==7:row[2]=-1;row[4]=1;return row,F(11,60)
 if index==8:row[5]=1;return row,F(3,40)+F(1,4)/hs[2][0]
 if index==9:row[0]=F(7,8);row[1]=1;return row,-F(7,32)
 k=index-10
 if k==len(ch):row[3]=1;row[5]=-1;return row,-clearance
 if k==len(ch)+1:row[0]=-1;row[2]=1;return row,1-hs[0][0]+cap_tilt_bounds(box[1])[0]
 if k==len(ch)+2:
  signed=cap_tilt_bounds(box[1])[1]
  if signed is None:return row,F(0)
  row[0]=-1;row[2]=1;return row,2-hs[0][0]-signed
 if k==len(ch)+3:row[2]=A;row[4]=B;return row,F(211,4)+A*cap_tilt_bounds(box[1])[0]+B*hs[2][1]
 if k==len(ch)+4:
  signed=cap_tilt_bounds(box[1])[1]
  if signed is None:return row,F(0)
  row[2]=A;row[4]=B;return row,F(211,4)+A-A*signed+B*hs[2][1]
 if k==len(ch)+6+3*len(EXTRA_DIRS):row[4]=1;return row,F(49,64)+hs[2][1]
 if k==len(ch)+5+3*len(EXTRA_DIRS):row[1]=1;row[5]=-1;return row,-hs[0][0]-hs[2][0]-F(97,4480)
 if k>=len(ch)+5:
  i,j=divmod(k-len(ch)-5,len(EXTRA_DIRS));assert 0<=i<3
  p,q=EXTRA_DIRS[j];row[2*i]=p;row[2*i+1]=q
  return row,root_bounds(Q)[1]-support_lower(box[i],(p,q))
 assert 0<=k<len(ch)
 i,j=PAIRS[k];owner,axis,sgn=ch[k];nn=normal_bounds(box[owner],axis,sgn)
 nm=[F(round((lo+hi)/2*(1<<30)),1<<30) for lo,hi in nn];error=F(0)
 for xy in (0,1):
  dr=difference_interval(root,box,k,xy);assert dr[0]<=dr[1],('empty difference requires explicit terminal',root,box,ch,k,xy)
  ee=(nn[xy][0]-nm[xy],nn[xy][1]-nm[xy]);error+=max(e*d for e in ee for d in dr)
 row[2*i:2*i+2]=nm;row[2*j:2*j+2]=[-v for v in nm]
 return row,-pair_support_lower(box[i],box[j])+error

def all_options(k):
 i,j=PAIRS[k]
 return tuple((owner,axis,sgn) for owner in (i,j) for axis in (0,1) for sgn in (-1,1))

def omitted_option_impossible(box,k,option):
 owner,axis,sgn=option;nn=normal_bounds(box[owner],axis,sgn)
 if k==1:return nn[1][1]<=0
 if k==0:return sgn<0 or (axis==1 and box[owner][0]>=0) or nn[1][1]<=0
 return False

def pack(discovery,target):
 assert not discovery['frontier'],'Incomplete discovery frontier.'
 roots=[{} for _ in ROOTS]
 for leaf in discovery['leaves']:
  pp=leaf['path'];steps=[]
  while 'parent'in pp:
   steps.append(('angle',pp['axis'],pp['side']) if 'axis'in pp else ('sep',tuple(pp['sep'])))
   pp=pp['parent']
  root=pp['root'];assert root==leaf['root'];cur=roots[root]
  for step in reversed(steps):
   assert 'w'not in cur and 'empty_interval'not in cur
   kind=step[0]
   if 'kind'in cur:assert cur['kind']==kind
   else:cur['kind']=kind;cur['children']={}
   key=str(step[2]) if kind=='angle' else ','.join(map(str,step[1]))
   if kind=='angle':
    if 'axis'in cur:assert cur['axis']==step[1]
    else:cur['axis']=step[1]
   cur=cur['children'].setdefault(key,{})
  assert not cur and leaf['power']==40
  box=tuple(tuple(F(str(v)) for v in T) for T in leaf['box']);ch=tuple(tuple(v) for v in leaf['choice'])
  empty,_=interval_witness(root,box,ch)
  if empty is not None:cur['empty_interval']=empty
  else:cur['w']=leaf['weights']
 data={'schema':'weak-outer-G-upper-inset-farkas-v1','root_bits':ROOT_BITS,'weight_power':40,'roots':roots}
 with gzip.open(target,'wt',compresslevel=9) as f:json.dump(data,f,separators=(',',':'));f.write('\n')
 return data

def verify(data):
 assert data['schema']=='weak-outer-G-upper-inset-farkas-v1'
 assert data['root_bits']==ROOT_BITS and data['weight_power']==40 and len(data['roots'])==len(ROOTS)
 stats={'nodes':0,'leaves':0,'angle_splits':0,'separator_splits':0,'farkas_leaves':0,'empty_interval_leaves':0,'max_depth':0};least=None;by_root=[]
 def visit(node,root,box,ch,depth):
  nonlocal least
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  if 'empty_interval'in node:
   assert set(node)=={'empty_interval'};tag=node['empty_interval'];assert type(tag)is list
   if tag[0]=='coordinate':
    assert len(tag)==2 and type(tag[1])is int and 0<=tag[1]<6
    lo,hi=context(root,box)[2][tag[1]]
   else:
    assert len(tag)==3 and tag[0]=='difference' and type(tag[1])is int and type(tag[2])is int and 0<=tag[1]<len(ch) and tag[2]in(0,1)
    lo,hi=difference_interval(root,box,tag[1],tag[2])
   reserve=lo-hi;assert reserve>0,('false empty interval',root,tag,box,ch)
   stats['leaves']+=1;stats['empty_interval_leaves']+=1;least=reserve if least is None else min(least,reserve)
  elif 'w'in node:
   assert set(node)=={'w'};rr=[F(0)]*6;bb=F(0);seen=set()
   for index,weight in node['w']:
    assert type(index)is int and type(weight)is int and weight>0 and index not in seen
    assert 0<=index<12+3*len(DIRS)+17+len(ch)+3*len(EXTRA_DIRS);seen.add(index)
    row,rhs=rational_row(index,root,box,ch);bb+=weight*rhs
    for j in range(6):rr[j]+=weight*row[j]
   reserve=(-bb-RHO*sum(abs(v) for v in rr))/(1<<40)
   assert reserve>0,('nonpositive exact leaf',str(reserve),root,box,ch,node)
   stats['leaves']+=1;stats['farkas_leaves']+=1;least=reserve if least is None else min(least,reserve)
   if stats['leaves']%10000==0:print('exact leaves',stats['leaves'],'nodes',stats['nodes'],flush=True)
  elif node.get('kind')=='angle':
   assert set(node)=={'kind','axis','children'} and set(node['children'])=={'0','1'}
   k=node['axis'];assert type(k)is int and 0<=k<3;stats['angle_splits']+=1;l,u=box[k];m=(l+u)/2
   for side,T in enumerate(((l,m),(m,u))):
    bo=list(box);bo[k]=T;visit(node['children'][str(side)],root,tuple(bo),ch,depth+1)
  else:
   assert set(node)=={'kind','children'} and node['kind']=='sep';k=len(ch);assert k<3;stats['separator_splits']+=1
   children={tuple(map(int,key.split(','))):value for key,value in node['children'].items()};assert set(children)<=set(all_options(k))
   for option in all_options(k):
    if option in children:visit(children[option],root,box,ch+(option,),depth+1)
    else:assert omitted_option_impossible(box,k,option),('uncovered owned separator',root,k,option,box)
 for root,(node,(_,box)) in enumerate(zip(data['roots'],ROOTS)):
  before=(stats['nodes'],stats['leaves']);visit(node,root,box,(),0)
  by_root.append({'root':root,'domain':ROOTS[root][0][0],'nodes':stats['nodes']-before[0],'leaves':stats['leaves']-before[1]})
 stats.update(status='PASS',frontier=0,roots=len(ROOTS),minimum_reserve=str(least),minimum_reserve_floor_1e12=str(F((least*10**12).numerator//(least*10**12).denominator,10**12)),by_root=by_root)
 return stats

def main():
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--pack-discovery',type=Path);ap.add_argument('--report',type=Path);args=ap.parse_args();start=time.time()
 if args.pack_discovery:data=pack(json.loads(args.pack_discovery.read_text()),args.certificate)
 else:
  with gzip.open(args.certificate,'rt') as f:data=json.load(f)
 stats=verify(data);stats['seconds']=time.time()-start;stats['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
 stats['verifier_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();helper=Path(__file__).with_name('weak_outer_hand_right_lower_verify.py');stats['exact_helper_sha256']=hashlib.sha256(helper.read_bytes()).hexdigest()
 if args.report:args.report.write_text(json.dumps(stats,indent=2)+'\n')
 print(json.dumps(stats,indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact whole-domain radial endpoint cover for the physical-two opposite return."""
from n9_physical_two_side_certificate import I,D,ceildiv
from pathlib import Path
from collections import Counter
from fractions import Fraction
import argparse,gzip,hashlib,json,time
from n9_core_capacity_family import verify as verify_capacity, verify_actual_vertex_dyadic_boxes

ROOT=((0,ceildiv(2*D,3)),(D//68,ceildiv(2*D,5)),(D//2,D))
KIND='physical_two_opposite_return_all_physical_radial_endpoints'
HALF=I.q(1,2)
CAPDIR=Path(__file__).resolve().parent.parent/'research/nine/certificates'
CAPFILES=['physical_two_opposite_side_five_core_capacity.json',
 'physical_two_opposite_side_loaded_low_five_core_capacity.json',
 'physical_two_opposite_side_loaded_radius_two_wide_five_core_capacity.json']
CAPDATA=[json.loads((CAPDIR/name).read_text()) for name in CAPFILES]
CAPHASHES={name:hashlib.sha256((CAPDIR/name).read_bytes()).hexdigest() for name in CAPFILES}
SOURCEHASHES={name:hashlib.sha256((Path(__file__).resolve().parent/name).read_bytes()).hexdigest()
 for name in ['n9_physical_two_side_certificate.py','n9_core_capacity_family.py']}
for data in CAPDATA:verify_capacity(data)

class Empty(Exception):pass
class Divide(Exception):pass
def div(x,y):
 if y.lo<=0:raise Divide()
 return x*I(D*D//y.hi,ceildiv(D*D,y.lo))
def clip(x,lo,hi):
 l=max(x.lo,lo);h=min(x.hi,hi)
 if l>h:raise Empty()
 return I(l,h)
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(t,a):return (t*a[0],t*a[1])
def misses(x):return x.lo>0 or x.hi<0
def quad(p,v,w):return [p,add(p,v),add(add(p,v),w),add(p,w)]
def capacity_entry(rows,R2):
 raw=[[[[z.lo,z.hi] for z in p] for p in row] for row in rows]
 for data in CAPDATA:
  capQ=Fraction(*map(int,data['radius_squared_upper']))
  if R2.hi*capQ.denominator>capQ.numerator*D:continue
  eps=I.q(*map(int,data['vertex_error_bound']));den=data['reference_denominator']
  near=True
  for row,refs in zip(rows,data['reference_vertices']):
   for p,ref in zip(row,refs):
    error=(p[0]-I.q(ref[0],den)).sq()+(p[1]-I.q(ref[1],den)).sq()
    if error.hi>eps.sq().lo:near=False;break
   if not near:break
  if near:return True
  if max(z.hi-z.lo for row in rows for p in row for z in p)<D//4:
   if verify_actual_vertex_dyadic_boxes(data,raw,precision_bits=40)['verified']:return True
 return False

def evaluate(box,which):
 try:
  s,b,H=[I(*x) for x in box]
  a=(1-b.sq()).sqrt();c=(1-s.sq()).sqrt()
  if c.hi<=I.q(3,4).lo:return 'c_domain'
  D0=1-a+H*s;N0=1-H*c+b
  u=a*c-b*s;y=a*s+b*c;ee=u-y
  if ee.hi<=0:return 'return_direction'
  if (5*ee-18*b).lo>=0:return 'return_ratio'
  for label,z in [('x',1-D0),('l',1-N0)]:
   if z.hi<=0 or z.lo>=D:return label+'_domain'
  W=D0.sq()+N0.sq();rw=W.sqrt()
  X=-c*D0+s*N0;Y=s*D0+c*N0
  CX=b+s*ee;CY=c*ee;rc=(b.sq()+ee.sq()+2*b*s*ee).sqrt()
  if which=='B':
   d=div(D0+N0.sq()+Y*HALF,rw-X)
  else:
   d=div((u+y)*CX-(HALF-H+y-u)*CY,CX+rc)
  d=clip(d,I.q(9,10).lo,I.q(61,60).hi)
  R2=(d+1).sq()+I.q(1,4)
  if R2.lo>I.q(1105,256).hi or R2.hi<I.q(79,40).sq().lo:return 'radius'
  R2=clip(R2,I.q(79,40).sq().lo,I.q(1105,256).hi)
  eq=b*(H-HALF)*N0-(d*s+HALF*c)*ee*D0
  if misses(eq):return 'full_hub_torque'
  bv=(div(X,rw),div(Y,rw));cv=(div(CX,rc),div(CY,rc))
  wB=(bv[1],-bv[0]);wC=(-cv[1],cv[0])
  K=(d-c+s*N0,HALF+s+c*N0)
  L=(d-u-y,HALF-H+y-u)
  Kb=dot(K,bv);Kw=dot(K,wB);Lc=dot(L,cv);Lw=dot(L,wC)
  if which=='B':
   if Kw.hi<=0 or Kw.lo>=D//2:return 'radial_B_port'
   if (-Lc-d).lo>0:return 'other_support'
   xB=HALF-Kw
   rad=R2-(Lc-1).sq()
   if rad.hi<D//4:return 'C_circle'
   tangent=clip(rad,D//4,10*D).sqrt()
   xC=Lw+tangent
  else:
   if Lw.lo>=0 or Lw.hi<=-D//2:return 'radial_C_port'
   if (Kb-d).lo>0:return 'other_support'
   xC=HALF+Lw
   rad=R2-(Kb+1).sq()
   if rad.hi<D//4:return 'B_circle'
   tangent=clip(rad,D//4,10*D).sqrt()
   xB=-Kw+tangent
  if xB.hi<=0 or xB.lo>=D or xC.hi<=0 or xC.lo>=D:return 'physical_port'
  xB=clip(xB,0,D);xC=clip(xC,0,D)
  T=sub(K,mul(1-xB,wB));U=add(L,mul(1-xC,wC));nn=sub(T,U)
  if misses(dot(nn,nn)-1):return 'side_length'
  nb=dot(nn,bv);nw=dot(nn,wB);nc=dot(nn,cv);nz=dot(nn,wC)
  if nb.hi<=0 or nw.hi<=0 or nc.hi<=0 or nz.hi<=0:return 'strict_side_direction'
  # Both endpoint moments use their complete true-two original stars.
  # The radial endpoint determines the same original positive channel ratio.
  PB=ee*rw;PC=N0*rc
  if which=='B':
   moment=d*nw+HALF*nb
   ZC=sub(sub(L,cv),mul(xC,wC))
   force=cross(ZC,add(mul(PC*moment,cv),mul(PB*Kw,nn)))
   if tangent.lo>D//2 and misses(force):return 'unique_C_force'
  else:
   moment=d*nz+HALF*nc
   ZB=add(add(K,bv),mul(xB,wB))
   force=cross(ZB,add(mul(PB*moment,bv),mul(PC*(-Lw),nn)))
   if tangent.lo>D//2 and misses(force):return 'unique_B_force'
  V=quad((d,-HALF),(I.q(1),I.q(0)),(I.q(0),I.q(1)))
  A=quad((d-c-(1-N0)*s,HALF+s-(1-N0)*c),(c,-s),(s,c))
  DD=quad((d,HALF-H),(-u,y),(-y,-u))
  BB=quad(T,bv,wB)
  CC=quad(sub(sub(L,cv),mul(xC,wC)),cv,wC)
  if capacity_entry([V,A,DD,BB,CC],R2):return 'actual_nine_square_capacity'
  return None
 except Empty:return 'empty_range'
 except Divide:return None

def split(box,k):
 lo,hi=box[k];mid=(lo+hi)//2
 if not lo<mid<hi:raise ValueError('precision exhausted')
 le=list(box);ri=list(box);le[k]=(lo,mid);ri[k]=(mid,hi)
 return tuple(le),tuple(ri)
def require(x,msg):
 if not x:raise ValueError(msg)
def generate(limit):
 nodes=[None,None];stack=[(1,ROOT,'C',0),(0,ROOT,'B',0)];counts=Counter();depth=0;started=time.monotonic()
 while stack:
  i,box,which,lev=stack.pop();depth=max(depth,lev);rule=evaluate(box,which)
  if rule is not None:nodes[i]=[rule];counts[which+':'+rule]+=1
  else:
   if len(nodes)+2>limit:return None,dict(status='OPEN',nodes=len(nodes),pending=len(stack)+1,box=box,which=which,depth=depth,counts=dict(counts))
   k=max(range(3),key=lambda j:Fraction(box[j][1]-box[j][0],ROOT[j][1]-ROOT[j][0]))
   le,ri=split(box,k);ii=len(nodes);nodes.extend([None,None]);nodes[i]=['split',k,ii,ii+1]
   stack.extend([(ii+1,ri,which,lev+1),(ii,le,which,lev+1)])
  if len(nodes)%20000==0:print(json.dumps(dict(nodes=len(nodes),pending=len(stack),which=which,depth=depth)),flush=True)
 data=dict(version=1,kind=KIND,precision_bits=40,root_box=ROOT,roots={'B':0,'C':1},capacity_sha256=CAPHASHES,source_sha256=SOURCEHASHES,nodes=nodes)
 return data,dict(status='CLOSED',nodes=len(nodes),leaves=sum(counts.values()),depth=depth,counts=dict(counts),seconds=round(time.monotonic()-started,2))
def verify(data):
 require(data['version']==1 and data['kind']==KIND and data['precision_bits']==40,'wrong specification')
 require(tuple(map(tuple,data['root_box']))==ROOT and data['roots']=={'B':0,'C':1},'wrong root')
 require(data['capacity_sha256']==CAPHASHES,'changed capacity certificate')
 require(data['source_sha256']==SOURCEHASHES,'changed arithmetic or capacity helper')
 nodes=data['nodes'];seen=set();counts=Counter();stack=[(0,ROOT,'B'),(1,ROOT,'C')]
 while stack:
  i,box,which=stack.pop();require(0<=i<len(nodes) and i not in seen,'invalid/repeated node');seen.add(i);row=nodes[i]
  if row[0]=='split':
   require(len(row)==4 and row[1] in range(3),'invalid split');le,ri=split(box,row[1]);stack.extend([(row[2],le,which),(row[3],ri,which)])
  else:require(len(row)==1 and evaluate(box,which)==row[0],'unproved leaf');counts[which+':'+row[0]]+=1
 require(len(seen)==len(nodes),'unvisited nodes')
 return dict(status='EXACT COMPLETE RADIAL COVER REPLAYED',nodes=len(nodes),counts=dict(counts),Lean_verified=False)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--verify',type=Path);ap.add_argument('--limit',type=int,default=1000000);args=ap.parse_args()
 if args.verify:
  raw=gzip.decompress(args.verify.read_bytes()) if args.verify.suffix=='.gz' else args.verify.read_bytes()
  print(json.dumps(verify(json.loads(raw)),indent=2));return
 data,stats=generate(args.limit);print(json.dumps(stats,indent=2),flush=True)
 if data is not None:
  print(json.dumps(verify(data),indent=2),flush=True)
  if args.output:
   raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
   args.output.write_bytes(gzip.compress(raw,mtime=0) if args.output.suffix=='.gz' else raw)

if __name__=='__main__':main()

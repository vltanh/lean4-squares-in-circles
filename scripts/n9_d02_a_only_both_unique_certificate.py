#!/usr/bin/env python3
"""Exact necessary-system cover for D02 L135 A-only both-unique side.

All interval predicates use integer arithmetic with outward dyadic rounding.
The generated tree records closed-box splits and both necessary-domain
contractions. Physical completion leaves invoke independently checked
five-core center-cover data. Python is an untrusted certificate generator
and replay implementation; no Lean or independent-kernel result is claimed.
"""
from pathlib import Path
from fractions import Fraction
import argparse,gzip,hashlib
from math import isqrt
import time,json
P=44;SCALE=1<<P
class Bad(Exception):pass
class I:
 __slots__=('l','h')
 def __init__(self,l,h=None,raw=False):
  if raw:self.l=l;self.h=l if h is None else h
  else:
   if not isinstance(l,int) or (h is not None and not isinstance(h,int)):raise TypeError('exact integer endpoints required')
   self.l=l*SCALE;self.h=self.l if h is None else h*SCALE
 def __add__(self,o):
  o=iv(o);return I(self.l+o.l,self.h+o.h,True)
 __radd__=__add__
 def __neg__(self):return I(-self.h,-self.l,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  o=iv(o);a=[self.l*o.l,self.l*o.h,self.h*o.l,self.h*o.h];return I(min(a)//SCALE,-((-max(a))//SCALE),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o)
  if o.l<=0<=o.h:raise Bad('division')
  if o.h<0:return -self/-o
  a=[(self.l*SCALE)//o.l,(self.l*SCALE)//o.h,(self.h*SCALE)//o.l,(self.h*SCALE)//o.h];b=[-((-self.l*SCALE)//o.l),-((-self.l*SCALE)//o.h),-((-self.h*SCALE)//o.l),-((-self.h*SCALE)//o.h)];return I(min(a),max(b),True)
 def sq(self):
  lo=0 if self.l<=0<=self.h else min(self.l*self.l,self.h*self.h)
  hi=max(self.l*self.l,self.h*self.h);return I(lo//SCALE,-((-hi)//SCALE),True)
 def sqrt(self):
  if self.h<0:raise Bad('sqrt')
  lo=isqrt(max(0,self.l)*SCALE);hi=isqrt(self.h*SCALE)
  if hi*hi<self.h*SCALE:hi+=1
  return I(lo,hi,True)
 def pos(self):return I(max(0,self.l),max(0,self.h),True)
 def intr(self,l,h):
  a=max(self.l,iv(l).l);b=min(self.h,iv(h).h)
  if a>b:raise Bad('empty')
  return I(a,b,True)
 def zero(self):return self.l<=0<=self.h
 def tup(self):return (self.l/SCALE,self.h/SCALE)
 def __repr__(self):return str(self.tup())
def iv(o):return o if isinstance(o,I) else I(o)
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(t,a):return (t*a[0],t*a[1])
def norm(a):return (a[0].sq()+a[1].sq()).sqrt()
def normalized(a):
 n=norm(a);return (a[0]/n,a[1]/n)
def atanhalf(a):
 if not isinstance(a,I):
  aa=a.sq();ss=2*a/(1+aa);cc=(1-aa)/(1+aa)
  if hasattr(a,'v'):ss.v,cc.v=atanhalf(a.v)
  return ss,cc
 def endpoint(x):
  den=SCALE*SCALE+x*x;ns=2*x*SCALE*SCALE;nc=(SCALE*SCALE-x*x)*SCALE
  return I(ns//den,-((-ns)//den),True),I(nc//den,-((-nc)//den),True)
 sl,cl=endpoint(a.l);sh,ch=endpoint(a.h)
 return I(sl.l,sh.h,True),I(ch.l,cl.h,True)
def angle_sum_intervals(a,b):
 def endpoint(x,y):
  den=(SCALE*SCALE+x*x)*(SCALE*SCALE+y*y)
  nh=2*(x+y)*(SCALE*SCALE-x*y)*SCALE*SCALE
  nk=(4*x*y*SCALE*SCALE-(SCALE*SCALE-x*x)*(SCALE*SCALE-y*y))*SCALE
  return I(nh//den,-((-nh)//den),True),I(nk//den,-((-nk)//den),True)
 hl,kl=endpoint(a.l,b.l);hh,kh=endpoint(a.h,b.h)
 hi=SCALE if kl.l<=0<=kh.h else max(hl.h,hh.h)
 return I(min(hl.l,hh.l),hi,True),I(kl.l,kh.h,True)
def reqpos(x):
 if x.h<=0:raise Bad('excluded')
 return x
ucache={}
def get_u(a,b,s,c,S,C,H,k,p):
 key=(a.l,a.h,b.l,b.h)
 if key in ucache:return ucache[key]
 rhs=p.pos()*(s-c).pos()*S.sq()*(S-C).pos()
 def ff(u):return u*(S-s+s*u).pos()*(S-H+H*u).pos()-rhs
 l=0;h=SCALE
 for _ in range(35):
  m=(l+h)//2;z=ff(I(m,raw=True))
  if z.h<=0:l=m
  else:h=m
 lower=l;l=0;h=SCALE
 for _ in range(35):
  m=(l+h)//2;z=ff(I(m,raw=True))
  if z.l>=0:h=m
  else:l=m
 upper=h
 ret=I(lower,upper,True);ucache[key]=ret
 return ret

from n9_five_core_capacity import prepare_actual_vertex_box_check,verify_actual_vertex_boxes,verify_actual_vertex_dyadic_boxes
CAPROOT=Path(__file__).resolve().parents[1]/'research/nine/certificates'
CAPFILES=['d02_type_ii_a_only_five_core_capacity_midpoint_balls.json','d02_type_ii_a_only_five_core_capacity_curve_45.json','d02_type_ii_a_only_five_core_capacity_curve_47.json','d02_type_ii_a_only_five_core_capacity_wide.json']
CAPDATA=[json.load(open(CAPROOT/path)) for path in CAPFILES]
CAPPREP=[prepare_actual_vertex_box_check(data) for data in CAPDATA]
def pin(x):return I(x,raw=True)
def frame(v):
 al=I(1)/(1+pin(v.h).sq()).sqrt()
 ah=I(1)/(1+pin(v.l).sq()).sqrt()
 bl=pin(v.l)/(1+pin(v.l).sq()).sqrt();bh=pin(v.h)/(1+pin(v.h).sq()).sqrt()
 return I(al.l,ah.h,True),I(bl.l,bh.h,True)
def phase(v,m):
 def point(x,y):
  a0=I(1)/(1+x.sq()).sqrt();cY=I(1)/(1+y.sq()).sqrt();fac=a0*cY
  return (1+x*y)*fac,(y-x)*fac,(1+y+x*y-x)*fac
 sl,tl,kl=point(pin(v.h),pin(m.l))
 if v.l<=m.h:sh=I(1);th=I(0);kh=I(1)
 else:sh,th,kh=point(pin(v.l),pin(m.h))
 return I(sl.l,sh.h,True),I(tl.l,th.h,True),I(kl.l,kh.h,True)
def ratio_v(u,a):
 def cot(x):return (1-x.sq())/(2*x)
 zl=cot(pin(a.h));zh=cot(pin(a.l))
 def f(uu,zz):return uu/(1-zz+uu*zz)
 lo=f(pin(u.l),pin(zl.l));hi=f(pin(u.h),pin(zh.h))
 return I(lo.l,hi.h,True)
def ratio_m(t,k):
 def f(tt,kk):
  hh=(1-kk.sq()).sqrt();return (tt+kk*(hh-kk))/((hh-kk)*hh)
 lo=f(pin(t.l),pin(k.l));hi=f(pin(t.h),pin(k.h))
 return I(lo.l,hi.h,True)
def evaluate(box,vertices=False):
 try:
  a,b,w=[I(*x,raw=True) for x in box]
  s,c=atanhalf(a);S,C=atanhalf(b)
  if (s-c).h<=(I(1)/625).l or (S-C).h<=0:return 'angle'
  delta=(s-c).intr(I(1)/625,1)
  H,k=angle_sum_intervals(a,b);p=H-k;q=H+k
  if k.h<=0 or k.l>=SCALE//2:return 'angle'
  H=H.intr(I(3).sqrt()/2,1);k=k.intr(0,I(1)/2);p=p.intr((I(3).sqrt()-1)/2,1);q=q.intr(1,(I(3).sqrt()+1)/2)
  u=get_u(a,b,s,c,S,C,H,k,p).intr(I(1)/12,s/(s+S)).intr(0,I(3)/5)
  t=(1-(s/S)*(1-u)).intr(0,S/(s+S)).intr(0,I(3)/5);omega=((1-u)*H/S).intr(0,1)
  mu=u*t;nu=delta*p;F=(mu*c-nu*k,mu*s+nu*H)
  fnormsq=mu.sq()+nu.sq()+2*mu*nu*C;q4=I(1105)/64
  if (q4*(nu*S).sq()-fnormsq).h<0 or (q4*(mu+nu*C).sq()-fnormsq).h<0:return 'V_corner'
  v=ratio_v(u,a).intr(0,1);m=ratio_m(t,k).intr(0,1)
  if m.l>=v.h:return 'obtuse'
  m=m.intr(0,v);v=v.intr(m,1)
  a0,b0=frame(v);cY,cX=frame(m)
  sig,tau,K=phase(v,m)
  if sig.l<=0:return None
  fac=1+m*v;pu=p-u
  AB=((1+q)*m+pu)/(a0*fac)-1;AC=((1+q)-v*pu)/(cY*fac)-1
  if AB.h<=0 or AC.h<=0:return 'gap'
  AB=AB.intr(0,1);AC=AC.intr(0,1)
  Tineq=AB.sq()+AC.sq()-2*tau*AB*AC
  if Tineq.l>=SCALE:return 'quadratic'
  wl=max(w.l,((1-v)/(1+v)).l,0);wh=min(w.h,((1-m)/(1+m)).h,SCALE)
  if wl>=wh:return 'sector'
  if 10*(wh-wl)<9*(w.h-w.l):return ('contract_sector',(box[0],box[1],(wl,wh)))
  w=I(wl,wh,True)
  Bden=u*c+delta;PB=t*Bden/a0;PC=delta*p*H/cY
  AT=sig*AB;BT=sig*AC
  kb0=b0-a0;kb1=a0+b0;kc0=cY-cX;kc1=-cY-cX
  qp0=PB*cX*kc0-PC*a0*kb0
  qp1=PB*(cX*kc1+cY*kc0)-PC*(a0*kb1-b0*kb0)
  qp2=PB*cY*kc1+PC*b0*kb1
  lp0=-PB*AT*kc0+PC*BT*kb0
  lp1=-PB*AT*kc1+PC*BT*kb1
  derivative=qp1+2*qp2*w+(lp1*(1+2*w.sq())+lp0*w)/(1+w.sq()).sqrt()
  if not derivative.zero():
   wm=pin((w.l+w.h)//2)
   fm=qp0+qp1*wm+qp2*wm.sq()+(1+wm.sq()).sqrt()*(lp0+lp1*wm)
   neww=wm-fm/derivative
   nl=max(w.l,neww.l);nh=min(w.h,neww.h)
   if nl>nh:return 'newton_empty'
   if 10*(nh-nl)<9*(w.h-w.l):return ('contract_newton',(box[0],box[1],(nl,nh)))
  W=(1+w.sq()).sqrt();d=(-I(1)/W,w/W)
  xB=1+((m+w)/W-m*(1+q)-pu)/(a0*fac)
  xC=1+((1-v*w)/W-(1+q)+v*pu)/(cY*fac)
  if xB.h<=0 or xB.l>=SCALE or xC.h<=0 or xC.l>=SCALE:return 'offset'
  xB=xB.intr(0,1);xC=xC.intr(0,1)
  kbnum=(v-1)+(1+v)*w;kcnum=(1-m)-(1+m)*w
  if kbnum.h<=0 or kcnum.h<=0:return 'sector'
  kB=a0*kbnum/W;kC=cY*kcnum/W
  Bden=u*c+delta;PB=t*Bden/a0;PC=delta*p*H/cY
  eq1=PB*xB*cY*kcnum-PC*xC*a0*kbnum
  if not eq1.zero():return 'torque'
  HB1=kbnum+xB*(1-v*w);HB2=xB*(v+w)
  HC1=kcnum+xC*(m+w);HC2=xC*(1-m*w)
  capfactor=I(1041)/64
  if (capfactor*HB1.sq()-HB2.sq()).h<0 or (capfactor*HB2.sq()-HB1.sq()).h<0:return 'B_corner'
  if (capfactor*HC1.sq()-HC2.sq()).h<0 or (capfactor*HC2.sq()-HC1.sq()).h<0:return 'C_corner'
  budget=b0*xB+cY*xC-(b0+cY-q)
  if budget.l>0:return 'budget'
  bvec=(-a0,-b0);cvec=(-cX,cY);wB=(-b0,a0);wC=(-cY,-cX)
  east=(c,s);north=(-s,c);nd=(-k,H);td=(-H,-k)
  DB=add(add(east,mul(1-omega,north)),(I(1),I(1)));DC=add(add(east,north),add(nd,mul(t,td)))
  EB=sub(sub(DB,bvec),mul(xB,wB));EC=add(add(DC,cvec),mul(xC,wC))
  EBsq=EB[0].sq()+EB[1].sq();ECsq=EC[0].sq()+EC[1].sq();FEB=dot(F,EB);FEC=dot(F,EC)
  if FEB.h<=0 or FEC.h<=0:return 'circle_direction'
  eq2=EBsq*FEC-ECsq*FEB
  if not eq2.zero():return 'equal_circle'
  Fb=dot(F,bvec);Fw=dot(F,wB);Db=dot(DB,bvec);Dw=dot(DB,wB);cd=dot(d,bvec);sd=dot(d,wB)
  if Fb.l>=0 or Fw.h<=0 or cd.h<=0 or sd.h<=0:return 'force_sign'
  denom=(kB+xB*cd)*Fw-xB*sd*Fb
  numer=Dw*(kB+xB*cd)-xB*sd*Db+xB*(1-xB)*cd
  eq3=EBsq*denom-2*FEB*numer
  if not eq3.zero():return 'radial_moment'
  if FEB.l<=0:return None
  lam=EBsq/(2*FEB);Rsq=lam.sq()*fnormsq
  if Rsq.h<(I(79)/40).sq().l or Rsq.l>(I(1105)/256).h:return 'radius'
  fnorm=fnormsq.sqrt()
  if fnorm.l<=0:return None
  lam=lam.intr((I(79)/40)/fnorm,(I(1105).sqrt()/16)/fnorm)
  Z=mul(lam,F);ZB=sub(Z,EB);ZC=sub(Z,EC)
  if dot(ZB,bvec).h<SCALE//2 or dot(ZB,wB).h<SCALE//2 or dot(ZC,cvec).l>-SCALE//2 or dot(ZC,wC).l>-SCALE//2:return 'corner_sign'
  P0=sub(sub(Z,east),north);RA=add(P0,mul(omega,north));QB=sub(Z,DB);QC=sub(Z,DC)
  quad=lambda o,x,y:[o,add(o,x),add(add(o,x),y),add(o,y)]
  V=quad(P0,east,north);A=quad(sub(RA,(I(1),I(1))),(I(1),I(0)),(I(0),I(1)));D=quad(sub(P0,mul(t,td)),mul(-1,nd),td);B=quad(sub(QB,mul(1-xB,wB)),bvec,wB);CC=quad(sub(QC,mul(xC,wC)),mul(-1,cvec),wC)
  boxes=[V,A,D,B,CC]
  if vertices:return [[[[z.l,z.h] for z in pt] for pt in row] for row in boxes]
  for capidx,capdata in enumerate(CAPDATA):
   refs=capdata['reference_vertices'];near=True
   eps=I(int(capdata['vertex_error_bound'][0]))/int(capdata['vertex_error_bound'][1])
   for row,ref in zip(boxes,refs):
    for pt,rr in zip(row,ref):
     dif=(pt[0]-I(rr[0])/10000000).sq()+(pt[1]-I(rr[1])/10000000).sq()
     if dif.h>eps.sq().l:near=False
   if near:return 'near_'+str(capidx)
  vboxes=[[[[z.l,z.h] for z in pt] for pt in row] for row in boxes]
  for capidx,capdata in enumerate(CAPDATA):
   if verify_actual_vertex_dyadic_boxes(capdata,vboxes,precision_bits=44)['verified']:return 'capacity_'+str(capidx)
  return None
 except Bad as e:
  if str(e)=='empty':return 'empty_range'
  return None

def initial_box():
    lower_beta=isqrt(2*SCALE*SCALE)-SCALE
    return ((41487*SCALE//100000,SCALE),(lower_beta,SCALE),(0,SCALE))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def metadata():
    return {
        'version':1,'kind':'d02_l135_a_only_both_unique_cover',
        'precision_bits':P,'radius_squared_upper':['1105','256'],
        'radius_lower':['79','40'],'initial_box':initial_box(),
        'checker_sha256':digest(__file__),
        'capacity_inputs':[{'file':path,'sha256':digest(CAPROOT/path)} for path in CAPFILES],
    }


def write_json(path,data):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    if str(path).endswith('.gz'):
        with gzip.GzipFile(filename=str(path),mode='wb',mtime=0) as f:
            f.write(json.dumps(data,separators=(',',':')).encode())
    else:path.write_text(json.dumps(data,separators=(',',':'))+'\n')


def read_json(path):
    if str(path).endswith('.gz'):
        with gzip.open(path,'rt') as f:return json.load(f)
    return json.loads(Path(path).read_text())


def generate(destination,checkpoint,resume=False):
    start=time.monotonic()
    if resume:
        data=read_json(checkpoint)
        if data['metadata']!=json.loads(json.dumps(metadata())):
            raise ValueError('checkpoint metadata or exact source/input hash changed')
        nodes=data['nodes'];counts=data['counts'];stack=[(tuple(tuple(z) for z in b),d,i) for b,d,i in data['pending']]
        visited=data['visited'];open_leaves=data['open_leaves']
    else:
        data={'metadata':metadata(),'status':'OPEN'};nodes=[None];counts={}
        stack=[(initial_box(),0,0)];visited=0;open_leaves=[]
    while stack:
        box,depth,nodeid=stack.pop();visited+=1
        result=evaluate(box)
        if isinstance(result,tuple):
            child=len(nodes);nodes.append(None)
            nodes[nodeid]=[result[0],child]
            stack.append((result[1],depth,child))
            counts[result[0]]=counts.get(result[0],0)+1
        elif result:
            nodes[nodeid]=['exclude',result]
            counts[result]=counts.get(result,0)+1
        elif depth>=80:
            nodes[nodeid]=['open'];open_leaves.append([box,depth,nodeid])
        else:
            widths=[hi-lo for lo,hi in box]
            axis=max(range(3),key=lambda j:widths[j]*(10,6,1)[j])
            lo,hi=box[axis];mid=(lo+hi)//2
            if not lo<mid<hi:raise ValueError('no nontrivial exact split')
            left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi)
            li=len(nodes);ri=li+1;nodes.extend([None,None]);nodes[nodeid]=['split',axis,li,ri]
            stack.append((tuple(right),depth+1,ri));stack.append((tuple(left),depth+1,li))
            counts['split']=counts.get('split',0)+1
        if visited%10000==0:
            data.update(nodes=nodes,counts=counts,pending=stack,visited=visited,open_leaves=open_leaves)
            write_json(checkpoint,data)
            print(json.dumps({'visited':visited,'pending':len(stack),'open':len(open_leaves),'counts':counts,'seconds':round(time.monotonic()-start,2)}),flush=True)
    data.update(nodes=nodes,counts=counts,pending=[],visited=visited,open_leaves=open_leaves,
                status='CLOSED' if not open_leaves else 'OPEN')
    write_json(destination,data);write_json(checkpoint,data)
    print(json.dumps({'status':data['status'],'nodes':len(nodes),'counts':counts,'open':len(open_leaves),'seconds':round(time.monotonic()-start,2),'file':str(destination)}),flush=True)
    if open_leaves:raise SystemExit(2)


def replay(path):
    data=read_json(path)
    if data['metadata']!=json.loads(json.dumps(metadata())):
        raise ValueError('exact source/input metadata mismatch')
    if data['status']!='CLOSED' or data['pending'] or data['open_leaves']:
        raise ValueError('certificate is incomplete')
    nodes=data['nodes'];seen=set();stack=[(initial_box(),0)];counts={};start=time.monotonic()
    while stack:
        box,nodeid=stack.pop()
        if nodeid in seen or not 0<=nodeid<len(nodes):raise ValueError('cycle/duplicate/bad node')
        seen.add(nodeid);node=nodes[nodeid]
        if node[0]=='split':
            _,axis,li,ri=node
            if axis not in (0,1,2):raise ValueError('bad split axis')
            lo,hi=box[axis];mid=(lo+hi)//2
            if not lo<mid<hi:raise ValueError('degenerate split')
            left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi)
            stack.append((tuple(right),ri));stack.append((tuple(left),li))
            counts['split']=counts.get('split',0)+1
        else:
            result=evaluate(box)
            if node[0] in ('contract_sector','contract_newton'):
                if not isinstance(result,tuple) or result[0]!=node[0]:raise ValueError('invalid necessary contraction')
                stack.append((result[1],node[1]));counts[node[0]]=counts.get(node[0],0)+1
            elif node[0]=='exclude':
                if not isinstance(result,str) or result!=node[1]:raise ValueError('invalid exact leaf')
                counts[result]=counts.get(result,0)+1
            else:raise ValueError('open/unknown node')
        if len(seen)%50000==0:print(json.dumps({'replayed':len(seen),'remaining_stack':len(stack),'seconds':round(time.monotonic()-start,2)}),flush=True)
    if len(seen)!=len(nodes) or counts!=data['counts']:raise ValueError('unreachable nodes or accounting mismatch')
    print(json.dumps({'verified':True,'nodes':len(nodes),'counts':counts,'seconds':round(time.monotonic()-start,2)}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate',action='store_true')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--certificate',type=Path,default=CAPROOT/'d02_l135_a_only_both_unique_cover.json.gz')
    parser.add_argument('--checkpoint',type=Path,default=Path('/tmp/d02_a_only_cover_checkpoint.json.gz'))
    args=parser.parse_args()
    if args.generate:generate(args.certificate,args.checkpoint,args.resume)
    else:replay(args.certificate)

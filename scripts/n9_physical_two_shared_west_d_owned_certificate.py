#!/usr/bin/env python3
"""Exact candidate cover of the entire aligned shared-West D-owned L135 feature."""
from __future__ import annotations
import sys,importlib
from pathlib import Path
from fractions import Fraction
import n9_physical_two_d_owned_west_certificate as tree
from n9_d02_a_only_both_unique_certificate import I,Bad,SCALE,dot,mul,add,sub
tree.KIND='physical_two_shared_West_D_owned_AD_loaded_BC_unloaded_N'
tree.ROOT=((0,(I(1)/I(2).sqrt()).h),(0,SCALE),((I(9)/10).l,(I(61)/60).h))
tree.NAMES=('s','ell','d')
ONE=I(1);HALF=I(1)/2;QUARTER=I(1)/4
def absI(a):return I(0 if a.l<=0<=a.h else min(abs(a.l),abs(a.h)),max(abs(a.l),abs(a.h)),True)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def perp(a):return (-a[1],a[0])
def pts(p):
 z,a,b=p;return [z,add(z,a),add(z,b),add(add(z,a),b)]
def center(p):return add(p[0],mul(HALF,add(p[1],p[2])))
def contained(p,R2):
 return not any((dot(v,v)-R2).l>0 for v in pts(p))
def collide(A,B):
 # Strict overlap of both projections on all four edge axes proves interiors overlap.
 for n in [A[1],A[2],B[1],B[2]]:
  aa=[dot(v,n) for v in pts(A)];bb=[dot(v,n) for v in pts(B)]
  if min(x.h for x in aa)>=max(x.l for x in bb):return False
  if min(x.h for x in bb)>=max(x.l for x in aa):return False
 return True
def unique_circle(p):
 z,a,b=p;cen=center(p);x=dot(cen,a);y=dot(cen,b)
 if x.zero() or y.zero():return None
 return add(add(z,a if x.l>0 else (I(0),I(0))),b if y.l>0 else (I(0),I(0)))
def support(p,n,upper):
 cen=center(p);rad=(absI(dot(p[1],n))+absI(dot(p[2],n)))/2
 return dot(cen,n)+rad if upper else dot(cen,n)-rad
def allprojection(p,n):
 cen=center(p);rad=(absI(dot(p[1],n))+absI(dot(p[2],n)))/2
 return dot(cen,n)-rad,dot(cen,n)+rad
def mcheck(n,M,fb,fc,km,lm,ZB,ZC):
 # Original B and C moments require opposite/same signs respectively.
 if (km*M).l>0 or (lm*M).h<0:return False
 if ZB is not None and not (M*cross(fb,ZB)-km*cross(n,ZB)).zero():return False
 if ZC is not None and not (M*cross(fc,ZC)-lm*cross(n,ZC)).zero():return False
 return True
def side_possible(B,C,fb,fc,K,L):
 vb,vc=pts(B),pts(C);km=cross(K,fb);lm=cross(L,fc)
 ZB=unique_circle(B);ZC=unique_circle(C)
 for T in vb:
  for U in vc:
   n=sub(T,U)
   if not (dot(n,n)-1).zero():continue
   if any(dot(sub(x,T),n).h<0 for x in vb):continue
   if any(dot(sub(x,U),n).l>0 for x in vc):continue
   if mcheck(n,cross(T,n),fb,fc,km,lm,ZB,ZC):return True
 # Own-axis directions cover every original nonvertex application, including full means.
 for n0 in [B[1],B[2],C[1],C[2]]:
  for sign in [-1,1]:
   n=mul(sign,n0);loB=support(B,n,False);hiC=support(C,n,True)
   for width in [ONE,I(2).sqrt()]:
    if not (loB-hiC-width).zero():continue
    if width.l>SCALE:
     if not (dot(n,B[1]).zero() or dot(n,B[2]).zero()):continue
     if not (dot(n,C[1]).zero() or dot(n,C[2]).zero()):continue
    v=perp(n);bmin,bmax=allprojection(B,v);cmin,cmax=allprojection(C,v)
    try:
     zz=I(max(bmin.l,cmin.l),min(bmax.h,cmax.h),True)
     if zz.l>zz.h:continue
     M=-zz
     if ZB is not None:
      den=cross(fb,ZB)
      if not den.zero():
       mm=km*cross(n,ZB)/den;M=M.intr(mm,mm)
     if ZC is not None:
      den=cross(fc,ZC)
      if not den.zero():
       mm=lm*cross(n,ZC)/den;M=M.intr(mm,mm)
     if mcheck(n,M,fb,fc,km,lm,ZB,ZC):return True
    except Bad as ex:
     if str(ex)!='empty':return True
 return False

def evaluator(box):
 try:
  s,ell,d=[I(*x,raw=True) for x in box]
  c=(1-s.sq()).sqrt();p=c-s;u=1-ell;kap=d*s+c/2
  if p.h<=0 or u.h<=0:return 'strict_domain'
  p=p.intr(0,1);u=u.intr(0,1)
  K=(d-c+u*s,HALF+s+u*c);L=(d-1,-HALF-ell*c)
  # Necessary j<=1 supplies a positive lower ray bound even at the p=u=0 corner.
  rr=2*kap*ell*c/(1-ell*s)
  sy=s+rr
  fy=sy/(c.sq()+sy.sq()).sqrt()
  if (K[1]+fy-I(1105).sqrt()/16).l>0:return 'B_vertical_point'
  A=u*(1-ell*s);B0=p*kap;den=A+B0
  if den.l<=0:return None
  j=(A/2+B0*(1+ell*c))/den;tau=B0*(HALF+ell*c)/den
  if j.h<=SCALE//2 or j.l>SCALE or (j-ell*c).h<0:return 'roof_mean'
  j=j.intr(HALF,1)
  if (2*(d+1)*tau*s-tau*c-kap).l>0:return 'V_weights'
  R2=(d+1).sq()+QUARTER
  if R2.l>(I(1105)/256).h or R2.h<(I(79)/40).sq().l:return 'radius'
  h=(c,-s);e=(s,c);P=(d,HALF)
  V=((d,-HALF),(ONE,I(0)),(I(0),ONE))
  Ash=(sub(sub(P,h),mul(ell,e)),h,e)
  Dsh=(L,(ONE,I(0)),(I(0),ONE))
  if not contained(Ash,R2):return 'A_containment'
  if not contained(Dsh,R2):return 'D_containment'
  fb0=(-p*c,p*s+u);fn=dot(fb0,fb0).sqrt()
  if fn.l<=0:return None
  fb=(fb0[0]/fn,fb0[1]/fn);wb=(fb[1],-fb[0])
  fc0=(-den,-u*(HALF+ell*c));cn=dot(fc0,fc0).sqrt()
  if cn.l<=0:return None
  fc=(fc0[0]/cn,fc0[1]/cn);wc=perp(fc)
  # Full original endpoint torques summed through the unloaded channel.
  PB=(HALF+ell*c)*fn;PC=cn
  if not (PB*cross(K,fb)+PC*cross(L,fc)).zero():return 'endpoint_torque_sum'
  beta=dot(K,fb)+HALF;radB=R2-(absI(beta)+HALF).sq()
  if radB.h<SCALE//4:return 'B_circle'
  TB=radB.intr(QUARTER,radB).sqrt()-HALF
  Bposes=[]
  for sb in [-1,1]:
   shift=sb*TB-dot(K,wb)
   if shift.l>SCALE//2 or shift.h<-SCALE//2:continue
   cen=add(mul(beta,fb),mul(sb*TB,wb));Bsh=(sub(cen,mul(HALF,add(fb,wb))),fb,wb)
   if not contained(Bsh,R2):continue
   if any(collide(Bsh,X) for X in [V,Ash,Dsh]):continue
   Bposes.append(Bsh)
  if not Bposes:return 'B_placements'
  Cposes=[]
  betaC=dot(L,fc)+HALF;radC=R2-(absI(betaC)+HALF).sq()
  if radC.h>=SCALE//4:
   TC=radC.intr(QUARTER,radC).sqrt()-HALF
   for sc in [-1,1]:
    shift=sc*TC-dot(L,wc)
    if shift.l>SCALE//2 or shift.h<-SCALE//2:continue
    cen=add(mul(betaC,fc),mul(sc*TC,wc));Cposes.append((sub(cen,mul(HALF,add(fc,wc))),fc,wc))
  L2=dot(L,L);pL=perp(L)
  for diag in [1,2]:
   ar=(R2-L2-diag)/2;rad=diag*L2-ar.sq()
   if rad.h<0:continue
   radical=rad.pos().sqrt()
   for sig in [-1,1]:
    vv=mul(ONE/L2,add(mul(ar,L),mul(sig*radical,pL)))
    if diag==2:
     aa=mul(HALF,add(vv,perp(vv)));bb=mul(HALF,sub(vv,perp(vv)));Cposes.append((L,aa,bb))
    else:
     Cposes.extend([(L,vv,perp(vv)),(L,vv,mul(-1,perp(vv)))])
  for Csh in Cposes:
   if dot(fc,sub(L,Csh[0])).h<0:continue
   # L must be a minimum-fc support of the unchanged C.
   if any(dot(sub(v,L),fc).h<0 for v in pts(Csh)):continue
   if not contained(Csh,R2):continue
   if any(collide(Csh,X) for X in [V,Ash,Dsh]):continue
   for Bsh in Bposes:
    if collide(Bsh,Csh):continue
    if side_possible(Bsh,Csh,fb,fc,K,L):return None
  return 'all_physical_masks_and_N_widths'
 except Bad as ex:
  return 'empty_range' if str(ex)=='empty' else None

def choose(box):
 widths=[Fraction(h-l,tree.ROOT[k][1]-tree.ROOT[k][0])*(Fraction(1,3) if k==2 else 1) for k,(l,h) in enumerate(box)]
 return max(range(3),key=lambda k:widths[k])
# Generalize only the local wrapper's split dimension validation and root.
tree.evaluator=evaluator
tree.choose=choose
_original_verify=tree.verify
# Its generic replay validates range(4), a harmless superset; k=3 would fail
# the three-coordinate split and is never generated.
if __name__=='__main__':
 if '--verify' in sys.argv:
  target=Path(sys.argv[sys.argv.index('--verify')+1])
  if target.suffix=='.gz':
   import gzip,json
   print(json.dumps(tree.verify(json.loads(gzip.decompress(target.read_bytes()))),indent=2))
  else:tree.main()
 else:tree.main()

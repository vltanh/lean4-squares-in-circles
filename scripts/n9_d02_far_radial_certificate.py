#!/usr/bin/env python3
"""Exact full physical radial endpoint cover for the Type II far side.

Uses the entire original ell,q chart, without angle samples or a parallel
channel assumption. The generic two-root certificate traversal is shared
with the separate A-only radial theorem.
"""
import n9_d02_a_only_radial_certificate as engine
from n9_d02_a_only_both_unique_certificate import I,SCALE,Bad,dot,mul,sub

engine.ROOT=((0,SCALE//2),(0,-((-5*SCALE)//6)))
engine.KIND='d02_l135_type_ii_far_all_physical_radial_endpoints'

def evaluate(box,which):
 try:
  e,q=[I(*x,raw=True) for x in box]
  if e.h<=0 or e.l>=SCALE//2 or q.h<=0:return 'strict_domain'
  if (q*(1+q)-(1+e)).l>=0:return 'side_width'
  J=(1+e.sq()).sqrt();AA=1+e;BB=1-e
  M=(AA.sq()+(1+q).sq()).sqrt();H=AA/M;k=(1+q)/M
  v=k+e*H
  if v.l>=SCALE:return 'D_port'
  v=v.intr(0,1)
  d=BB/J;L=AA/J
  z=(L-H*(1+e.sq()))/d
  W=I(8)/15+(I(67)/105)*e-(I(2)/15)*e.sq()
  if (z-W).h<=0 or z.l>=SCALE:return 'roof_slope'
  z=z.intr(W,1);u=(z-e).intr(I(3)/10,1);T=q+e
  delta=T*v/(T+u)
  DB=(d+H*(1+e)+k,L-k);DC=(d+delta,L+1)
  unit=(1+q.sq()).sqrt();a=I(1)/unit;b=q/unit
  fB=(-a,b);wB=(-b,-a)
  F=(I(1),z);Fsq=1+z.sq()
  if which=='B':f=fB;ww=mul(-1,wB);D=DB;other=DC;of=(I(0),I(-1))
  else:f=(I(0),I(-1));ww=(I(1),I(0));D=DC;other=DB;of=fB
  LL=1-dot(D,f);Ff=dot(F,f);Fw=dot(F,ww)
  den=(LL.sq()*Fsq+Fw.sq()/4).sqrt()-LL*Ff
  if den.l<=0:return None
  lam=(LL.sq()+I(1)/4)/den;Rsq=lam.sq()*Fsq
  if Rsq.h<(I(79)/40).sq().l or Rsq.l>(I(1105)/256).h:return 'radius'
  fn=Fsq.sqrt();lam=lam.intr((I(79)/40)/fn,(I(1105).sqrt()/16)/fn)
  Z=mul(lam,F);AR=lam*Ff+LL
  AR=AR.intr(((I(79)/40).sq()-I(1)/4).sqrt(),((I(1105)/256)-I(1)/4).sqrt())
  qr=dot(sub(Z,D),ww)
  if qr.h<=0 or qr.l>=SCALE//2:return 'radial_port'
  if (dot(sub(Z,other),of)-(AR-1)).l>0:return 'other_support'
  # Prior whole side cap: the actual B lower tangent port satisfies beta*a>=k.
  # At radial B, beta=1/2-QB.wB=1/2+qr.
  if which=='B' and ((I(1)/2+qr)*a-k).h<0:return 'B_side_port'
  QB=sub(Z,DB);QC=sub(Z,DC)
  if which=='B':beta=I(1)/2+qr
  else:
   bx=dot(QB,fB);by=dot(QB,wB)
   discriminant=Rsq-(bx+1).sq()
   if discriminant.h<SCALE//4:return 'B_circle'
   tangent=discriminant.sqrt().intr(I(1)/2,I(5)/2)
   beta=1-by-tangent
   if beta.h<=0 or beta.l>=SCALE:return 'B_port'
   beta=beta.intr(0,1)
   if (beta*a-k).h<0:return 'B_side_port'
  endpointT=(QB[0]+beta*wB[0],QB[1]+beta*wB[1])
  gap=endpointT[1]-QC[1]
  # gap>1/sqrt(2) forces the actual channel angle below45 degrees.
  # The full acute common-side/open-cone theorem then forces C radial;
  # the complete tangent theorem aligns its physical radial axis with -n.
  if which=='C' or gap.l>(I(1)/I(2).sqrt()).h:
   radial_eq=QC[1]-(1-AR)
   if not radial_eq.zero():return 'forced_C_radial'
   endpointU=(I(-1)/2,1-AR);dn=sub(endpointT,endpointU)
   if not (dot(dn,dn)-1).zero():return 'side_length'
   if dn[0].l>=0 or dn[1].h<=0:return 'side_direction'
   if dot(dn,fB).h<=0 or dot(dn,wB).l>=0:return 'side_direction'
   c_moment=dn[1]/2-(AR-1)*dn[0]
   b_moment=endpointT[0]*dn[1]-endpointT[1]*dn[0]
   full_torque=unit*dot(QB,wB)*c_moment-(q+z)*QC[0]*b_moment
   if not full_torque.zero():return 'endpoint_full_torque'
  return None
 except Bad as err:
  return 'empty_range' if str(err)=='empty' else None

engine.evaluate=evaluate

if __name__=='__main__':engine.main()

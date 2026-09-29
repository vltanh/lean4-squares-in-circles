#!/usr/bin/env python3
"""N0-only exact box checker for the n=6 normalization repair.

The state is the central centre (cx,cy), five genuine Seven markers in cyclic
order, and five exterior admissible chart states.  No core bound, sector,
pin, side-nearest, or canonical separator conclusion is assumed.

This is a discovery/audit checker.  A complete hand proof must still replace
any finite search by scalar endpoint inequalities before the Lean draft starts.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q

from n6_normalization_exact import (
    FI, PI, Q0_FI, SCALE, ONE, cos_interval, sin_interval
)

HALF = FI.frac(Q(1,2))
CORE = FI.frac(Q(23,200))
GAP_LO = PI.div_int(3)
GAP_HI = (PI*2).div_int(3)
QUARTER_PI = PI.div_int(4)
TWO_PI = PI*2


def hull_min(*xs: FI) -> FI:
    return FI(min(x.lo for x in xs), min(x.hi for x in xs))


def sn(x: FI) -> FI:
    return sin_interval(x.lo,x.hi)


def cs(x: FI) -> FI:
    return cos_interval(x.lo,x.hi)


def abs_lower(x: FI) -> int:
    if x.lo <= 0 <= x.hi:
        return 0
    return min(abs(x.lo),abs(x.hi))


def abs_upper(x: FI) -> int:
    return max(abs(x.lo),abs(x.hi))


def label_interval(a: FI, u: FI) -> FI:
    axial = FI.frac(Q(5,4))*u
    side = PI.div_int(6) + (u-HALF).div_int(3) + FI.frac(Q(3,4))*(ONE-a)
    return hull_min(axial, side, QUARTER_PI)


def width_lower(delta: FI) -> int:
    c=cs(delta); s=sn(delta)
    return (abs_lower(c)+abs_lower(s))//2


@dataclass
class Box:
    # cx,cy,m0,g0..g3,a0..a4,u0..u4
    iv: list[FI]
    signs: tuple[int,...]
    depth: int=0

    def copy(self):
        return Box(list(self.iv),self.signs,self.depth)

    @property
    def cx(self): return self.iv[0]
    @property
    def cy(self): return self.iv[1]
    @property
    def m0(self): return self.iv[2]
    def gap(self,i): return self.iv[3+i]
    def a(self,i): return self.iv[7+i]
    def u(self,i): return self.iv[12+i]

    def gaps(self):
        gs=[self.gap(i) for i in range(4)]
        g5=TWO_PI
        for g in gs: g5=g5-g
        return gs+[g5]

    def markers(self):
        out=[self.m0]
        cur=self.m0
        for i in range(4):
            cur=cur+self.gap(i); out.append(cur)
        return out

    def phases(self):
        ms=self.markers(); out=[]
        for i in range(5):
            L=label_interval(self.a(i),self.u(i))
            out.append(ms[i]-L if self.signs[i]>0 else ms[i]+L)
        return out

    def centers(self):
        ph=self.phases(); out=[]
        for i in range(5):
            c=cs(ph[i]); s=sn(ph[i]); a=self.a(i); u=self.u(i)
            if self.signs[i]>0:
                x=a*c-u*s; y=a*s+u*c
            else:
                x=a*c+u*s; y=a*s-u*c
            out.append((x,y))
        return out


def square_width_lower(theta_sq: FI, theta_axis: FI) -> int:
    return width_lower(theta_axis-theta_sq)


def dot_abs_upper(dx: FI,dy: FI,theta: FI) -> int:
    v=dx*cs(theta)+dy*sn(theta)
    return abs_upper(v)


def sep_margin_upper(c1,th1,c2,th2,axis: FI) -> int:
    dx=c2[0]-c1[0];dy=c2[1]-c1[1]
    return dot_abs_upper(dx,dy,axis)-square_width_lower(th1,axis)-square_width_lower(th2,axis)


def outer_pair_unavoidable_overlap(box: Box,i:int,j:int,centers,phases) -> bool:
    axes=(phases[i],phases[i]+PI.div_int(2),phases[j],phases[j]+PI.div_int(2))
    return all(sep_margin_upper(centers[i],phases[i],centers[j],phases[j],ax)<0 for ax in axes)


def central_pair_unavoidable_overlap(box: Box,i:int,centers,phases) -> bool:
    cc=(box.cx,box.cy); z=FI.integer(0)
    axes=(z,PI.div_int(2),phases[i],phases[i]+PI.div_int(2))
    return all(sep_margin_upper(cc,z,centers[i],phases[i],ax)<0 for ax in axes)


def lower_sq(x: FI) -> int:
    a=abs_lower(x)
    return (a*a)//SCALE


def reject(box: Box) -> str | None:
    # Dihedral wedge: 0 <= cy <= cx, and target bad region cx >= 23/200.
    if box.cy.lo<0 or box.cx.hi<CORE.lo or box.cy.lo>box.cx.hi:
        return 'wedge'

    # C contains O and itself fits in the Q0 disk.  In this wedge its far
    # corner is (cx+1/2,cy+1/2).
    if box.cx.lo>=HALF.hi or box.cy.lo>=HALF.hi:
        return 'central_origin'
    if lower_sq(box.cx+HALF)+lower_sq(box.cy+HALF)>Q0_FI.hi:
        return 'containment'

    gs=box.gaps()
    if gs[4].hi < GAP_LO.lo or gs[4].lo > GAP_HI.hi:
        return 'marker_gap'

    # Exterior admissibility at the stronger rational Q0 ceiling.
    for i in range(5):
        a=box.a(i);u=box.u(i)
        if a.hi<HALF.lo or u.hi<0 or u.lo>a.hi:
            return 'chart'
        if lower_sq(a+HALF)+lower_sq(u+HALF)>Q0_FI.hi:
            return 'containment'

    phases=box.phases(); centers=box.centers()
    for i in range(5):
        if central_pair_unavoidable_overlap(box,i,centers,phases):
            return 'unavoidable_overlap'
        for j in range(i):
            if outer_pair_unavoidable_overlap(box,j,i,centers,phases):
                return 'unavoidable_overlap'
    return None


def init_box(signs: tuple[int,...]) -> Box:
    # m0 is the first marker counterclockwise from angle 0; the preceding
    # cyclic gap is < 2pi/3, hence 0 <= m0 <= 2pi/3.
    rho_hi=FI.frac(Q(1113,1000))
    umax=FI.frac(Q(7,10))
    iv=[
        FI(CORE.lo,HALF.hi),
        FI(0,HALF.hi),
        FI(0,GAP_HI.hi),
    ]
    iv += [FI(GAP_LO.lo,GAP_HI.hi) for _ in range(4)]
    iv += [FI(HALF.lo,rho_hi.hi) for _ in range(5)]
    iv += [FI(0,umax.hi) for _ in range(5)]
    return Box(iv,signs)

# Characteristic scales only affect search order, never validity.
SCALES=[.385,.5,2.1]+[1.05]*4+[.62]*5+[.7]*5


def split(box: Box):
    scores=[]
    for x,sc in zip(box.iv,SCALES):
        scores.append((x.hi-x.lo)/SCALE/sc)
    k=max(range(len(scores)),key=scores.__getitem__)
    x=box.iv[k]; m=(x.lo+x.hi)//2
    if m<=x.lo:m=x.lo+1
    if m>=x.hi:m=x.hi-1
    a=box.copy();b=box.copy();a.iv[k]=FI(x.lo,m);b.iv[k]=FI(m,x.hi)
    a.depth=b.depth=box.depth+1
    return a,b


def run(signs: tuple[int,...],nodes:int,depth:int):
    q=[init_box(signs)];st={'visited':0,'split':0,'survivor':0,'reject':{},'max_depth':0}
    while q and st['visited']<nodes:
        b=q.pop();st['visited']+=1;st['max_depth']=max(st['max_depth'],b.depth)
        why=reject(b)
        if why:
            st['reject'][why]=st['reject'].get(why,0)+1;continue
        if b.depth>=depth:
            st['survivor']+=1;continue
        x,y=split(b);q.extend((x,y));st['split']+=1
    st['queue']=len(q);st['complete']=not q and not st['survivor']
    return st


def audit_source() -> None:
    # Audit only the logical state constructor and rejector, not comments or
    # this audit routine itself.
    import inspect
    src=inspect.getsource(init_box)+inspect.getsource(reject)
    for token in ('177/200','223/200','117/250','pinok','sector','pattern'):
        assert token not in src.lower(), token


def self_test() -> None:
    # Exact arithmetic smoke test and a small N0 traversal for both sign
    # extremes.  This is not claimed to close N16.
    audit_source()
    for signs in ((1,1,1,1,1),(-1,-1,-1,-1,-1)):
        st=run(signs,200,12)
        assert st['visited']>0
    print('n=6 N0 normalization checker: PASS')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mask',default='0')
    ap.add_argument('--nodes',type=int,default=2000)
    ap.add_argument('--depth',type=int,default=40)
    args=ap.parse_args()
    if args.mask=='all': masks=range(32)
    else: masks=[int(args.mask)]
    for mask in masks:
        signs=tuple(1 if (mask>>i)&1 else -1 for i in range(5))
        print(mask,run(signs,args.nodes,args.depth),flush=True)

if __name__=='__main__':
    self_test()
    main()

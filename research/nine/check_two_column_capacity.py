#!/usr/bin/env python3
"""Exact finite checks for the all-angle cap-section and TL.6 manuscripts.

This does not replace the analytic proof, independent review or Lean.
"""
from __future__ import annotations
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import product, combinations
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, platform

H=F(1,2); Q=F(17,4)
V=tuple[F,F]
COUNTS={}
def ck(x:bool,k:str):
    if not x:raise AssertionError(k)
    COUNTS[k]=COUNTS.get(k,0)+1

def add(a:V,b:V)->V:return (a[0]+b[0],a[1]+b[1])
def sub(a:V,b:V)->V:return (a[0]-b[0],a[1]-b[1])
def sc(t:F,v:V)->V:return (t*v[0],t*v[1])
def dot(a:V,b:V)->F:return a[0]*b[0]+a[1]*b[1]
def ortho(a:V)->V:return (-a[1],a[0])
def angle(t:F)->V:return ((1-t*t)/(1+t*t),2*t/(1+t*t))

@dataclass(frozen=True)
class Square:
    c:V
    u:V=(F(1),F(0))
    @property
    def v(self)->V:return ortho(self.u)
    @property
    def h(self)->F:return (abs(self.u[0])+abs(self.u[1]))/2
    def corners(self):
        return [add(self.c,add(sc(F(s,2),self.u),sc(F(t,2),self.v))) for s,t in product((-1,1),repeat=2)]
    def radius2(self)->F:
        return dot(self.c,self.c)+H+abs(dot(self.c,self.u))+abs(dot(self.c,self.v))
    def support(self,e:V)->F:return (abs(dot(self.u,e))+abs(dot(self.v,e)))/2
    def section(self,y:F=F(1))->tuple[F,F]|None:
        lo=None;hi=None
        for e in (self.u,self.v):
            c=e[0];r=e[1]*(y-self.c[1])
            if c==0:
                if abs(r)>H:return None
                continue
            one=self.c[0]+(-H-r)/c;two=self.c[0]+(H-r)/c
            l,h=min(one,two),max(one,two)
            lo=l if lo is None else max(lo,l)
            hi=h if hi is None else min(hi,h)
        if lo is None or hi is None or lo>hi:return None
        return lo,hi
    def contains(self,p:V)->bool:
        d=sub(p,self.c);return abs(dot(d,self.u))<=H and abs(dot(d,self.v))<=H

def physical(squares:list[Square],name:str)->dict:
    for s in squares:
        ck(dot(s.u,s.u)==1,'unit_frames')
        ck(s.radius2()<=Q,'physical_containment')
        ck(s.radius2()==max(dot(p,p) for p in s.corners()),'corner_identity')
    for a,b in combinations(squares,2):
        z=sub(b.c,a.c)
        ck(any(abs(dot(z,e))>=a.support(e)+b.support(e) for e in (a.u,a.v,b.u,b.v)),'physical_SAT')
    return {'name':name,'squares':len(squares),'SAT_pairs':len(squares)*(len(squares)-1)//2,
            'max_squared_radius':str(max(s.radius2() for s in squares)),
            'centers':[[str(t) for t in s.c] for s in squares],
            'axes':[[str(t) for t in s.u] for s in squares]}

def algebra():
    ck(F(209,100)**2>Q,'section_length_rational_margin')
    ck(F(25,17)>F(36,25),'section_angle_threshold')
    for k in range(1,101):
        a,b=angle(F(k,250));h=(a+b)/2
        ck((a-4*b)*(4*a-b)==4-17*a*b,'length_threshold_identity')
        ck(1+h-F(3,2)*a-a*b/2==(1-a)*(1+b/2),'small_angle_length_identity')
        w=a+b
        ck(1+w-a*b/2==F(5,4)+w-w*w/4,'large_angle_length_identity')
        # Endpoint proof, upward-facing side normal.
        if b<=H:
            bound=(F(3,2)+b/2)**2+(H+a)**2
            ck(bound==F(9,2)+(a-1)+F(3,2)*b-F(3,4)*b*b,'upward_endpoint_identity')
            ck(bound>Q,'upward_endpoint_strict')
        # Downward-facing side normal, exact polynomial lower bound.
        if 0<b<F(3,5):
            K0=F(3,2)+b-F(5,18)*b*b
            V0=F(3,2)-b/2-F(65,72)*b*b
            polynomial=F(3,2)*b-F(55,24)*b*b+F(25,72)*b**3+F(4625,5184)*b**4
            ck(K0*K0+V0*V0-F(9,2)==polynomial,'downward_endpoint_factorization')
            ck(polynomial>b/8>0,'downward_endpoint_positive')
            K=1+a/2+b;V=1+a-b/2-1/(2*a)
            ck(K>=K0>0 and V>=V0>0,'endpoint_lower_bounds')
        if b>=F(3,5):
            ck(a/2+b>=1,'steep_normal_bound')
    # The only algebraic equality candidate in the steep branch violates floor.
    a,b,lam=F(4,5),F(3,5),F(1)
    ck(1+a/2+b==2 and lam*a>H,'steep_equality_floor_exclusion')


def sample_sections()->dict:
    tested=0;nonaxis=0;minimum=None;closest_right=None;closest_left=None
    for k in range(0,25):
        for sign in (-1,1):
            u=angle(F(sign*k,60))
            for ix in range(-20,21):
                for iy in range(20,31):
                    s=Square((F(ix,20),F(iy,20)),u)
                    if s.c[1]-s.h < H or s.radius2()>Q:continue
                    tested+=1;nonaxis+=int(k>0)
                    interval=s.section()
                    ck(interval is not None,'sample_section_exists')
                    lo,hi=interval
                    if s.c[1]-s.h==1:
                        ck(s.c==(F(0),F(3,2)) and k==0,'unique_north_exception')
                        continue
                    ck(s.c[1]-s.h<1<s.c[1]+s.h,'sample_interior_section')
                    ck(hi-lo>H,'sample_strict_half_length')
                    ck(lo<H and hi>-H,'sample_strict_window')
                    minimum=hi-lo if minimum is None else min(minimum,hi-lo)
                    closest_right=hi if closest_right is None else min(closest_right,hi)
                    closest_left=lo if closest_left is None else max(closest_left,lo)
    # Exact near-axis radial side-normal square has section <1: length-one shortcut false.
    u=(F(399,401),F(40,401));s=Square(sc(F(3,2),ortho(u)),u)
    ck(s.radius2()==Q and s.c[1]-s.h>=H,'near_axis_radial_cap')
    lo,hi=s.section();ck(H<hi-lo<1,'negative_control_length_not_one')
    # At the larger radius 9/2 the strict window is false.
    boundary=Square((F(-1),F(1)))
    ck(boundary.radius2()==F(9,2) and boundary.c[1]-boundary.h==H,'larger_radius_negative_control')
    ck(boundary.section()[1]==-H,'larger_radius_window_failure')
    return {'admissible_rational_squares':tested,'nonaxis_samples':nonaxis,
            'minimum_sample_length':str(minimum),'minimum_right_endpoint':str(closest_right),
            'maximum_left_endpoint':str(closest_left),'scope':'Finite rational regressions, not an angle-cover proof.'}

def cage_examples()->list[dict]:
    ends=[Square((F(-3,2),F(0))),Square((F(3,2),F(0)))]
    out=[]
    # Centered solid block, both exceptional north and south squares.
    center=[Square((x,y)) for x in (-H,H) for y in (-H,H)]
    out.append(physical(ends+center+[Square((F(0),F(3,2))),Square((F(0),F(-3,2)))],
                        'central_block_eight_square_equality'))
    # Both columns shifted up; two additional lower cap squares.
    cols=[Square((x,y)) for x in (-H,H) for y in (F(-1,5),F(4,5))]
    free=[Square((x,F(-6,5))) for x in (-H,H)]
    out.append(physical(ends+cols+free,'both_columns_up_two_lower_squares'))
    # Oppositely shifted columns; free squares genuinely turn and cross x=0.
    cols=[Square((-H,F(-1,5))),Square((-H,F(4,5))),
          Square((H,F(-4,5))),Square((H,F(1,5)))]
    u=(F(399,401),F(40,401))
    free=[Square((F(13,25),F(5,4)),u),Square((F(-13,25),F(-5,4)),u)]
    out.append(physical(ends+cols+free,'mixed_columns_oblique_axis_crossing_free_pair'))
    for s in free:
        ck(s.c[0]-s.h<0<s.c[0]+s.h,'negative_control_free_square_not_one_quadrant')
    # Strict positive gaps demonstrate why inaccessible holes, rather than a solid block,
    # must be included in the proof.
    cols=[Square((x,y)) for x in (-H,H) for y in (F(-3,5),F(3,5))]
    out.append(physical(ends+cols,'six_body_with_positive_internal_hole'))
    return out

def slot_cases()->dict:
    records=[]
    centers=[F(i,10) for i in range(-9,10)]
    columns=[(a,b) for a,b in product(centers,repeat=2) if a<b and b-a>=1]
    for (a,b),(c,d) in product(columns,repeat=2):
        lows=[a-H,c-H];highs=[b+H,d+H]
        upper=sum(h<1 for h in highs);lower=sum(l>-1 for l in lows)
        ck(upper+lower<=2,'exhaustive_finite_slot_regression')
        north=all(h<=1 for h in highs)
        south=all(l>=-1 for l in lows)
        if north:ck(all(l<=-1 for l in lows),'north_forces_lower_slots_blocked')
        if south:ck(all(h>=1 for h in highs),'south_forces_upper_slots_blocked')
        if north and south:ck(lows==[F(-1),F(-1)] and highs==[F(1),F(1)],'both_exceptions_force_central_block')
        records.append((upper,lower,north,south))
    return {'column_pairs_checked':len(records),'distinct_slot_states':sorted(set(records)),
            'proof_basis':'General inequality h_i-l_i>=2, not these finite pairs.'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-commit',default='LOCAL_UNCOMMITTED');p.add_argument('--output',type=Path)
    a=p.parse_args();start=datetime.now(timezone.utc).isoformat()
    algebra();sections=sample_sections();examples=cage_examples();slots=slot_cases()
    raw=Path(__file__).read_bytes()
    result={'status':'PASS','started_utc':start,'finished_utc':datetime.now(timezone.utc).isoformat(),
            'python':platform.python_version(),'source_commit':a.source_commit,
            'source_sha256':hashlib.sha256(raw).hexdigest(),
            'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
            'exact_assertions':sum(COUNTS.values()),'assertions_by_category':COUNTS,
            'cap_section_samples':sections,'physical_cage_witnesses':examples,'slot_regressions':slots,
            'scope':'Exact finite checks only. No universal proof by sampling, independent full audit, Lean or CI.'}
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text,encoding='utf-8')
    print(text,end='')
if __name__=='__main__':main()

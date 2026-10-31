#!/usr/bin/env python3
"""Finite exact regressions for TREE.03 and TREE.02.P, not a universal proof."""
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import platform

V = tuple[F, F]
HALF = F(1, 2)
Q = F(17, 4)

def vec(x, y):
    return F(x), F(y)

def add(a, b):
    return a[0]+b[0], a[1]+b[1]

def sub(a, b):
    return a[0]-b[0], a[1]-b[1]

def scale(t, a):
    return t*a[0], t*a[1]

def dot(a, b):
    return a[0]*b[0]+a[1]*b[1]

def rot(a):
    return -a[1], a[0]

@dataclass(frozen=True)
class Square:
    c: V
    u: V = (F(1), F(0))
    v: V = (F(0), F(1))

    def corners(self):
        return [add(self.c, add(scale(F(a,2),self.u), scale(F(b,2),self.v)))
                for a in (-1,1) for b in (-1,1)]

    def support(self, d):
        return (abs(dot(d,self.u))+abs(dot(d,self.v)))/2

    def contains(self, p):
        d=sub(p,self.c)
        return abs(dot(d,self.u))<=HALF and abs(dot(d,self.v))<=HALF

def pack(squares):
    for s in squares:
        assert dot(s.u,s.u)==dot(s.v,s.v)==1 and dot(s.u,s.v)==0
        assert all(dot(p,p)<=Q for p in s.corners())
    for a,b in combinations(squares,2):
        delta=sub(b.c,a.c)
        assert any(abs(dot(delta,d))>=a.support(d)+b.support(d)
                   for d in (a.u,a.v,b.u,b.v))
    return {"squares":len(squares), "corners":4*len(squares),
            "SAT_pairs":len(squares)*(len(squares)-1)//2}

def s_terminal(d):
    return Square(scale(F(3,2),d),d,rot(d))

def equilibrium(squares, contacts, loads):
    """Contacts use directed force vectors, avoiding normalizing radicals."""
    pack(squares)
    total=sum((weight/4 for _,_,weight in loads),F(0))
    forces=[vec(0,0) for _ in squares]
    torques=[F(0) for _ in squares]
    atoms=0
    for i,d,w in loads:
        assert w>0
        for sign in (-1,1):
            p=add(scale(F(2),d),scale(F(sign,2),rot(d)))
            assert p in squares[i].corners() and dot(p,p)==Q
            lam=w/(8*total)
            force=scale(2*lam,p)
            forces[i]=add(forces[i],force)
            torques[i]+=dot(force,rot(sub(p,squares[i].c)))
            atoms+=1
    for i,j,p,raw_force in contacts:
        assert raw_force!=vec(0,0)
        assert squares[i].contains(p) and squares[j].contains(p)
        assert dot(raw_force,sub(p,squares[i].c))==squares[i].support(raw_force)
        assert dot(raw_force,sub(p,squares[j].c))==-squares[j].support(raw_force)
        force=scale(1/total,raw_force)
        for k,sgn in ((i,1),(j,-1)):
            fk=scale(sgn,force)
            forces[k]=add(forces[k],fk)
            torques[k]+=dot(fk,rot(sub(p,squares[k].c)))
    assert all(f==vec(0,0) for f in forces) and all(t==0 for t in torques)
    return {"contacts":len(contacts), "circle_atoms":atoms,
            "normalized_force_and_torque":"exactly zero"}

def run(commit):
    start=datetime.now(timezone.utc).isoformat()
    checks=0
    def ok(c):
        nonlocal checks
        assert c
        checks+=1
    # Exact radical comparisons in the annular thirty-degree lemma.
    ok(F(3)>F(14,9)**2)
    ok(54>49)
    # Pocket box and center-distance comparisons.
    ok(62900<63001)
    ok(4489<4500)
    ok(20*1627**2 < 81*810**2)
    ok(F(9,4)+2-4==F(1,4))
    for j in range(42,62):
        t=F(j,100)
        c=(1-t*t)/(1+t*t)
        s=2*t/(1+t*t)
        if not (s>=c>0 and s<=2*c):
            continue
        ok(s*s+c*c==1)
        ok(s*c>=F(2,5))
        ok((s+c)**2>=F(9,5))
        for k in range(41):
            z=F(k,100)
            a=(1-z*z)/(1+z*z)
            b=2*z/(1+z*z)
            actual=max(s*a,c*b)+max(s*b,c*a)
            ok(actual>=s*(s+c))
            ok(a*a+b*b==1 and a>=b>=0)
    e,n,w,south=vec(1,0),vec(0,1),vec(-1,0),vec(0,-1)
    central=[Square(vec(x,y)) for x in (-HALF,HALF) for y in (-HALF,HALF)]
    eight=central+[s_terminal(d) for d in (e,n,w,south)]
    cage=pack(eight)
    # Three origin-vertex squares can be completed to eight: the bound is sharp.
    selected_origins=[0,1,2]
    ok(all(eight[i].contains(vec(0,0)) for i in selected_origins))
    for i in range(len(eight)):
        if i not in selected_origins:
            ok(F(1,2)<=dot(eight[i].c,eight[i].c)<=F(9,4))
    right_pocket=pack([Square(vec(HALF,HALF)),s_terminal(e),s_terminal(n)])
    # Point-only TREE.02 core at its sharp terminal-gap threshold.
    u,v=vec(F(-4,5),F(3,5)),vec(F(-3,5),F(-4,5))
    roots=[Square(vec(HALF,HALF)),Square(scale(HALF,add(u,v)),u,v)]
    squares=roots+[s_terminal(d) for d in (e,n,u,v)]
    contacts=[(0,1,vec(0,0),vec(F(-7,5),F(-1,5))),
              (0,2,e,scale(F(7,5),e)),(0,3,n,scale(F(1,5),n)),
              (1,4,u,u),(1,5,v,v)]
    loads=[(2,e,F(7,5)),(3,n,F(1,5)),(4,u,F(1)),(5,v,F(1))]
    core=pack(squares)
    core.update(equilibrium(squares,contacts,loads))
    force=contacts[0][3]
    ok(dot(force,roots[0].u)<0 and dot(force,roots[0].v)<0)
    ok(dot(force,roots[1].u)>0 and dot(force,roots[1].v)>0)
    ok(dot(n,u)==F(3,5))  # cos(2 arctan(1/2))=3/5
    # Shared-edge TREE.02.E remains physically feasible as a four-body core.
    edge_path=[Square(vec(F(-3,2),0)),Square(vec(-HALF,HALF)),
               Square(vec(HALF,HALF)),Square(vec(F(3,2),0))]
    edge_report=pack(edge_path)
    edge_report.update(equilibrium(edge_path,
        [(0,1,vec(-1,0),e),(1,2,vec(0,0),e),(2,3,vec(1,0),e)],
        [(0,w,F(1)),(3,e,F(1))]))
    # Opposite endpoint sliders admit a NON-STRICT zero-point force, not the
    # strict-normal selected certificate used by TREE.02.P.
    nonstrict=[Square(vec(F(-3,2),0)),Square(vec(-HALF,HALF)),
               Square(vec(HALF,-HALF)),Square(vec(F(3,2),0))]
    nonstrict_report=pack(nonstrict)
    nonstrict_report.update(equilibrium(nonstrict,
        [(0,1,vec(-1,0),e),(1,2,vec(0,0),e),(2,3,vec(1,0),e)],
        [(0,w,F(1)),(3,e,F(1))]))
    ok(dot(e,nonstrict[1].v)==0)
    raw=Path(__file__).read_bytes()
    return {"status":"PASS", "source_commit":commit,
            "source_sha256":hashlib.sha256(raw).hexdigest(),
            "source_git_blob_sha1":hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
            "started_utc":start, "finished_utc":datetime.now(timezone.utc).isoformat(),
            "python":platform.python_version(), "exact_rational_checks":checks,
            "three_vertex_capacity_eight_square_attainment":cage,
            "right_angle_pocket_attainment":right_pocket,
            "strict_point_contact_six_square_core":core,
            "shared_edge_boundary_four_square_core":edge_report,
            "nonstrict_normal_negative_control":nonstrict_report,
            "scope":"Finite exact regressions only; not an all-angle proof, independent audit or Lean certificate."}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-commit',default='LOCAL_UNCOMMITTED')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    result=run(args.source_commit)
    out=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(out,encoding='utf-8')
    print(out,end='')

if __name__=='__main__':
    main()

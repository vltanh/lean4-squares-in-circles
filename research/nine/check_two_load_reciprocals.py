#!/usr/bin/env python3
"""Exact regressions for two-load reciprocal rigidity and C1.4.b0.

Finite examples and identities only: NOT a universal proof, independent
full audit, or Lean certificate. Uses the Python standard library only.
"""
from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import cmp_to_key
import hashlib
from itertools import combinations
import json
from pathlib import Path
import platform

Vec = tuple[F, F]
Z: Vec = (F(0), F(0))
E: Vec = (F(1), F(0))
H = F(1, 2)
Q0 = F(17, 4)


def vec(x=0, y=0) -> Vec:
    return F(x), F(y)


def add(a: Vec, b: Vec) -> Vec:
    return a[0]+b[0], a[1]+b[1]


def sub(a: Vec, b: Vec) -> Vec:
    return a[0]-b[0], a[1]-b[1]


def scale(t: F, a: Vec) -> Vec:
    return t*a[0], t*a[1]


def dot(a: Vec, b: Vec) -> F:
    return a[0]*b[0]+a[1]*b[1]


def det(a: Vec, b: Vec) -> F:
    return a[0]*b[1]-a[1]*b[0]


def turn(a: Vec) -> Vec:
    return -a[1], a[0]


def angle_cmp(a: Vec, b: Vec) -> int:
    """Exact counterclockwise ordering from +x; no atan/float."""
    def half(v):
        return 0 if v[1] > 0 or (v[1] == 0 and v[0] >= 0) else 1
    ha, hb = half(a), half(b)
    if ha != hb:
        return -1 if ha < hb else 1
    cross = det(a, b)
    return -1 if cross > 0 else 1 if cross < 0 else 0


def ordered(items, directions):
    return sorted(items, key=cmp_to_key(lambda i,j: angle_cmp(directions[i], directions[j])))


class Square:
    def __init__(self, c: Vec, u: Vec = E):
        self.c, self.u, self.v = c, u, turn(u)
        assert dot(u, u) == 1

    def corners(self):
        return [add(self.c, add(scale(F(s,2),self.u),scale(F(t,2),self.v)))
                for s in (-1,1) for t in (-1,1)]

    def halfwidth(self, e: Vec):
        return (abs(dot(e,self.u))+abs(dot(e,self.v)))/2

    def contains(self, p: Vec):
        v=sub(p,self.c)
        return abs(dot(v,self.u)) <= H and abs(dot(v,self.v)) <= H


# A contact is (tail,head,normal from tail to head,actual point,positive weight).
# A circle atom is (body,actual corner,positive weight).
def circle_pair(i, e, force):
    return [(i, add(scale(F(2),e),scale(s,turn(e))),force/8) for s in (-H,H)]


def geometry(squares, contacts, atoms, q=Q0):
    pairs=0
    for s in squares:
        assert all(dot(p,p) <= q for p in s.corners())
    for a,b in combinations(squares,2):
        delta=sub(b.c,a.c)
        assert any(abs(dot(delta,e)) >= a.halfwidth(e)+b.halfwidth(e)
                   for e in (a.u,a.v,b.u,b.v))
        pairs += 1
    total=sum(w for _,_,w in atoms)
    assert total>0
    contacts=[(i,j,n,p,w/total) for i,j,n,p,w in contacts]
    atoms=[(i,p,w/total) for i,p,w in atoms]
    forces=[Z for _ in squares]
    torques=[F(0) for _ in squares]
    loads=[Z for _ in squares]
    load_weights=[F(0) for _ in squares]
    contact_force={}
    for i,p,w in atoms:
        assert w>0 and dot(p,p)==q and p in squares[i].corners()
        f=scale(2*w,p)
        forces[i]=add(forces[i],f)
        loads[i]=add(loads[i],f)
        load_weights[i]+=w
        torques[i]+=2*w*dot(p,turn(sub(p,squares[i].c)))
    for i,j,n,p,w in contacts:
        assert w>0 and dot(n,n)==1
        assert squares[i].contains(p) and squares[j].contains(p)
        assert dot(n,sub(p,squares[i].c))==squares[i].halfwidth(n)
        assert dot(n,sub(p,squares[j].c))==-squares[j].halfwidth(n)
        for body,sign in ((i,1),(j,-1)):
            f=scale(sign*w,n)
            forces[body]=add(forces[body],f)
            torques[body]+=sign*w*dot(n,turn(sub(p,squares[body].c)))
            key=(body,p)
            contact_force[key]=add(contact_force.get(key,Z),f)
    assert all(f==Z for f in forces) and all(t==0 for t in torques)
    assert sum(load_weights)==1 and all(v!=Z for v in contact_force.values())
    return contacts, loads, contact_force, {
        "bodies":len(squares),"corners":4*len(squares),"SAT_pairs":pairs,
        "positive_body_contacts":len(contacts),
        "loaded_bodies":sum(w>0 for w in load_weights),
        "force_and_torque_residuals_exactly_zero":True}


def faces_of(rotation):
    darts={(v,w) for v,ns in rotation.items() for w in ns}
    face={}; cycles=[]
    for d in sorted(darts):
        if d in face:
            continue
        fid=len(cycles); walk=[]; cur=d
        while cur not in face:
            face[cur]=fid; walk.append(cur)
            u,v=cur
            ns=rotation[v]
            cur=(v,ns[(ns.index(u)-1)%len(ns)])
        assert cur==d, "invalid rotation-system face walk"
        cycles.append(walk)
    assert len(rotation)-len(darts)//2+len(cycles)==2, "not a spherical embedding"
    return face,cycles


def reciprocal(rotation, f):
    face,walks=faces_of(rotation)
    for u,ns in rotation.items():
        assert sum((f[u,v][0] for v in ns),F(0))==0
        assert sum((f[u,v][1] for v in ns),F(0))==0
        for v in ns:
            assert f[v,u]==scale(F(-1),f[u,v]) and f[u,v]!=Z
    adj={i:[] for i in range(len(walks))}
    for u,ns in rotation.items():
        for v in ns:
            left,right=face[u,v],face[v,u]
            jump=turn(f[u,v])
            adj[right].append((left,jump))
    potential={0:Z}; todo=deque([0])
    while todo:
        a=todo.popleft()
        for b,jump in adj[a]:
            p=add(potential[a],jump)
            if b in potential:
                assert potential[b]==p, "dual increments fail exact integration"
            else:
                potential[b]=p;todo.append(b)
    assert len(potential)==len(walks)
    twice_area={}; convex={}
    for u,ns in rotation.items():
        pts=[potential[face[v,u]] for v in ns]
        area=sum(det(pts[i],pts[(i+1)%len(pts)]) for i in range(len(pts)))
        twice_area[u]=area
        convex[u]=all(det(sub(pts[(i+1)%len(pts)],pts[i]),sub(p,pts[i]))>=0
                      for i in range(len(pts)) for p in pts)
    assert sum(twice_area.values())==0
    return twice_area,convex,len(walks)


def physical_reciprocal(name,squares,contacts,atoms):
    contacts,loads,aggregate,result=geometry(squares,contacts,atoms)
    points=sorted({p for _,p in aggregate})
    point_names={p:f"p{k}" for k,p in enumerate(points)}
    positions={f"b{i}":s.c for i,s in enumerate(squares)}
    positions.update({point_names[p]:p for p in points})
    rotation={k:[] for k in positions};rotation["outside"]=[]
    f={};directions={k:{} for k in positions};directions["outside"]={}
    def connect(a,b,force,da,db):
        assert (a,b) not in f and force!=Z
        rotation[a].append(b);rotation[b].append(a)
        f[a,b]=force;f[b,a]=scale(F(-1),force)
        directions[a][b]=da;directions[b][a]=db
    for (i,p),force in aggregate.items():
        a,b=f"b{i}",point_names[p]
        connect(a,b,force,sub(p,squares[i].c),sub(squares[i].c,p))
    for i,g in enumerate(loads):
        if g!=Z:
            a=f"b{i}"
            # All test terminals are radial S bodies. The exterior port is on
            # the far side along their center direction; no fake body-pair edge.
            connect(a,"outside",g,squares[i].c,squares[i].c)
    for u in rotation:
        rotation[u]=ordered(rotation[u],directions[u])
    rotation["outside"].reverse()
    areas,convex,nfaces=reciprocal(rotation,f)
    assert all(ok for node,ok in convex.items() if node!="outside")
    assert all(a>=0 for node,a in areas.items() if node!="outside")
    loaded=result["loaded_bodies"]
    if loaded==2:
        assert areas["outside"]==0 and all(a==0 for a in areas.values())
        n=contacts[0][2]
        assert all(det(n,e[2])==0 for e in contacts)
    else:
        assert areas["outside"]<0
    result.update(name=name,incidence_nodes=len(rotation),faces=nfaces,
        twice_reciprocal_polygon_areas={k:str(v) for k,v in areas.items()},
        finite_force_polygons_weakly_convex=True,
        all_pair_normals_parallel=all(det(contacts[0][2],e[2])==0 for e in contacts))
    return result


def examples():
    ex=[]
    def ends():
        return [Square(vec(F(-3,2),0)),Square(vec(F(3,2),0))]
    def atoms():
        return circle_pair(0,vec(-1,0),F(1))+circle_pair(1,E,F(1))
    s=ends()+[Square(vec(-H,F(1,3))),Square(vec(H,F(-2,5)))]
    edges=[(0,2,E,vec(-1,0),F(1)),(2,3,E,vec(0,0),F(1)),(3,1,E,vec(1,0),F(1))]
    ex.append(physical_reciprocal("four_body_staggered_path",s,edges,atoms()))
    s=ends()+[Square(vec(-H,0)),Square(vec(H,-H)),Square(vec(H,H))]
    edges=[(0,2,E,vec(-1,0),F(1)),
           (2,3,E,vec(0,F(-1,4)),H),(2,4,E,vec(0,F(1,4)),H),
           (3,1,E,vec(1,F(-1,4)),H),(4,1,E,vec(1,F(1,4)),H)]
    ex.append(physical_reciprocal("five_body_cycle_with_bridge",s,edges,atoms()))
    s=ends()+[Square(vec(x,y)) for x in (-H,H) for y in (F(-3,5),F(3,5))]
    edges=[(0,2,E,vec(-1,F(-1,5)),H),(2,4,E,vec(0,F(-1,5)),H),(4,1,E,vec(1,F(-1,5)),H),
           (0,3,E,vec(-1,F(1,5)),H),(3,5,E,vec(0,F(1,5)),H),(5,1,E,vec(1,F(1,5)),H)]
    ex.append(physical_reciprocal("six_cycle_inner_heights_outside_P_domain",s,edges,atoms()))
    s=ends()+[Square(vec(-H,F(-2,5))),Square(vec(-H,F(3,5))),
              Square(vec(H,F(-3,5))),Square(vec(H,F(2,5)))]
    edges=[(0,2,E,vec(-1,F(-1,6)),F(3,5)),(0,3,E,vec(-1,F(1,4)),F(2,5)),
           (2,4,E,vec(0,F(-1,4)),F(2,5)),(2,5,E,vec(0,0),F(1,5)),
           (3,5,E,vec(0,F(1,4)),F(2,5)),(4,1,E,vec(1,F(-1,4)),F(2,5)),
           (5,1,E,vec(1,F(1,6)),F(3,5))]
    ex.append(physical_reciprocal("six_body_theta_not_just_simple_cycle",s,edges,atoms()))
    up,u,v=vec(0,1),vec(F(3,5),F(-4,5)),vec(F(-4,5),F(-3,5))
    s=[Square(vec(0,H)),Square(scale(H,add(u,v)),u),
       Square(scale(F(3,2),up),up),Square(scale(F(3,2),u),u),Square(scale(F(3,2),v),v)]
    edges=[(0,2,up,up,F(1)),(0,1,vec(0,-1),Z,F(1)),
           (1,3,u,u,F(4,5)),(1,4,v,v,F(3,5))]
    at=circle_pair(2,up,F(1))+circle_pair(3,u,F(4,5))+circle_pair(4,v,F(3,5))
    ex.append(physical_reciprocal("negative_control_three_loaded_nonaligned_Y",s,edges,at))
    return ex


def graph_checks():
    edge_list=list(combinations(range(4),2)); total=0; counts={"C4":0,"DIAMOND":0,"K4":0};residual=[]
    def connected(vertices,edges):
        if not vertices:return True
        seen={next(iter(vertices))}; todo=list(seen)
        while todo:
            i=todo.pop()
            for a,b in edges:
                if i in (a,b):
                    j=b if i==a else a
                    if j in vertices and j not in seen: seen.add(j);todo.append(j)
        return seen==vertices
    for mask in range(1<<6):
        edges={e for k,e in enumerate(edge_list) if mask>>k&1}
        if not all(connected(set(range(4))-{i},edges) for i in range(4)):
            continue
        if not connected(set(range(4)),edges):continue
        kind={4:"C4",5:"DIAMOND",6:"K4"}[len(edges)]
        counts[kind]+=1;total+=1
        for k in range(2,5):
            for L in combinations(range(4),k):
                nontouch={e for e in combinations(L,2) if e not in edges}
                if connected(set(L),nontouch):
                    assert k==2
                    residual.append({"graph":kind,"loaded":list(L)})
    assert total==10 and counts=={"C4":3,"DIAMOND":6,"K4":1}
    assert len(residual)==12
    return {"all_labelled_simple_graphs":64,"biconnected_graphs":total,
            "by_adjacency_type":counts,"load_patterns_surviving_noncontact_rule":residual,
            "scope":"Graph/load bookkeeping only; physical exclusion is the hand theorem."}


def algebra_checks():
    q=F(79,40)**2
    checks=[q>F(15,4),F(7,4)**2>3,
            q-F(1,4)>F(19,10)**2,
            F(1105,256)-F(1,4)<F(101,50)**2,
            F(57,40)**2>2,F(1105,256)<F(21,10)**2,
            F(7,5)**2<2,F(29,20)**2>2,F(43,25)<2,
            F(9,5)**2>2,F(61,20)-2<F(7,5),
            4>F(61,20)]
    assert all(checks)
    # Abstract plane diamond with two outer-port edges: arbitrary vector
    # equilibrium is NOT sufficient if finite force polygons have wrong order.
    rotation={"o":["b","a"],"a":["o","b","c"],
              "b":["c","a","o"],"c":["b","a"]}
    face,cycles=faces_of(rotation)
    coords={"o":vec(0,0),"a":vec(3,1),"b":vec(3,-1),"c":vec(6,0)}
    areas=[sum(det(coords[u],coords[v]) for u,v in cyc) for cyc in cycles]
    outer=next(i for i,a in enumerate(areas) if a<0)
    inside=[i for i in range(len(cycles)) if i!=outer]
    pot={outer:Z,inside[0]:vec(1,0),inside[1]:vec(0,1)}
    f={}
    for u,ns in rotation.items():
        for v in ns:
            jump=sub(pot[face[u,v]],pot[face[v,u]])
            f[u,v]=scale(F(-1),turn(jump))
    signed,convex,_=reciprocal(rotation,f)
    assert signed["o"]==0 and any(signed[k]<0 for k in signed if k!="o")
    assert not all(convex[k] for k in convex if k!="o")
    return {"exact_radius_inequalities":len(checks),
            "negative_control_without_direction_order":{k:str(v) for k,v in signed.items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-commit",default="LOCAL_UNCOMMITTED")
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    start=datetime.now(timezone.utc).isoformat()
    alg=algebra_checks(); graphs=graph_checks(); samples=examples()
    raw=Path(__file__).read_bytes()
    report={"status":"PASS","started_utc":start,"finished_utc":datetime.now(timezone.utc).isoformat(),
            "python":platform.python_version(),"source_commit":args.source_commit,
            "source_sha256":hashlib.sha256(raw).hexdigest(),
            "source_git_blob_sha1":hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
            "algebra":alg,"four_body_graph_inventory":graphs,"physical_reciprocal_examples":samples,
            "scope":"Finite exact regression of algebra, planar face integration, signed-area cancellation, physical examples and graph bookkeeping. NOT universal optimality, independent full audit or Lean verification."}
    text=json.dumps(report,indent=2)+"\n"
    if args.output: args.output.write_text(text,encoding="utf-8")
    print(text,end="")


if __name__=="__main__":
    main()

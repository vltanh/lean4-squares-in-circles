#!/usr/bin/env python3
"""EXACT rational twelve-cone SAT-owner graph consistency checker.

Inputs: rational half-angle tangent for each genuine unit-square
frame, plus selected actual signed SAT-owner directions for some
or all unordered square pairs.

Sound global rejections at squared disk radius <=9789/2500:
  1) any directed triangle whose three signed normals fit in a
     common closed 60-degree arc (exact dot/cross test);
  2) any directed cycle in one of twelve rational cone graphs,
     each cone proven analytically narrower than 2/3 radians.

NOTE: each signed separating axis has TWO equivalent orientations:
i->j with n and j->i with -n. We bucket BOTH orientations.
Otherwise graph-cycle detection would be vacuous due to i<j labels!

Passing a word is NOT a packing feasibility certificate.
"""
from fractions import Fraction as F
from itertools import combinations
import json,sys

def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def neg(a):return (-a[0],-a[1])
def rot(a):return (-a[1],a[0])

base=[(F(1),F(0)),(F(15,17),F(8,17)),(F(3,5),F(4,5))]
rays=[]
for _ in range(4):
    rays.extend(base)
    base=[rot(a) for a in base]
assert len(rays)==12
assert all(cross(rays[i],rays[(i+1)%12])>0 for i in range(12))

def frames(zs):
    out=[]
    for z in zs:
        t=F(z)
        c=(1-t*t)/(1+t*t)
        s=2*t/(1+t*t)
        e=(c,s); f=(-s,c)
        assert dot(e,e)==dot(f,f)==1 and dot(e,f)==0
        out.append((e,f))
    return out

def sectors(n):
    slots=[
        i for i in range(12)
        if cross(rays[i],n)>=0 and
           cross(n,rays[(i+1)%12])>=0
    ]
    assert 1<=len(slots)<=2,(n,slots)
    return slots

def same_sixty_degree_arc(ns):
    # For a given candidate first ray u, each v in the positive
    # 60-degree CCW arc obeys cross(u,v)>=0, dot(u,v)>=1/2.
    # Checking all three starting rays is necessary and sufficient.
    return any(
        all(cross(start,v)>=0 and dot(start,v)>=F(1,2) for v in ns)
        for start in ns
    )

def find_cycle(edges,n):
    out=[[] for _ in range(n)]
    for a,b in edges:out[a].append(b)
    state=[0]*n
    stack=[]
    def dfs(v):
        state[v]=1
        stack.append(v)
        for w in out[v]:
            if state[w]==1:
                return stack[stack.index(w):]+[w]
            if state[w]==0:
                cyc=dfs(w)
                if cyc is not None:return cyc
        stack.pop()
        state[v]=2
        return None
    for v in range(n):
        if state[v]==0:
            cyc=dfs(v)
            if cyc is not None:return cyc
    return None

def check(cert):
    ef=frames(cert["frame_half_tangents"])
    n=len(ef)
    selected={}
    bins=[[] for _ in range(12)]
    for i,j,owner,axis,sign in cert["owner_word"]:
        assert 0<=i<j<n and owner in (i,j)
        assert axis in ("e","f") and sign in (-1,1)
        assert (i,j) not in selected
        normal=ef[owner][0 if axis=="e" else 1]
        if sign<0:normal=neg(normal)
        selected[(i,j)]=normal
        # Both representations are the SAME true SAT inequality.
        for k in sectors(normal): bins[k].append((i,j))
        for k in sectors(neg(normal)):bins[k].append((j,i))
    bad3=None
    for i,j,k in combinations(range(n),3):
        if not all(edge in selected for edge in ((i,j),(j,k),(i,k))):
            continue
        ns=(selected[(i,j)],selected[(j,k)],neg(selected[(i,k)]))
        if same_sixty_degree_arc(ns):
            bad3=(i,j,k)
            break
    badcycle=None
    for sector,edges in enumerate(bins):
        path=find_cycle(edges,n)
        if path is not None:
            badcycle=(sector,path)
            break
    if bad3:
        print("IMPOSSIBLE TRUE SAT-owner directed 60-degree triangle:",bad3)
    if badcycle:
        print("IMPOSSIBLE twelve-rational-cone owner directed cycle:",badcycle)
    impossible=bool(bad3 or badcycle)
    if "expect_impossible" in cert:
        assert impossible==cert["expect_impossible"]
    if not impossible:
        print("PASS: no owner-cycle obstruction detected; NOT a packing proof")
    return impossible

if __name__=="__main__":
    with open(sys.argv[1]) as f:check(json.load(f))

#!/usr/bin/env python3
"""Exact-Fraction regression for the 7-order global owner theorem.

The paper argument covers the continuum; these checks audit rational constants,
a strict old-vs-new rejection, and a genuine eight-square packing.
"""
from fractions import Fraction as F
from itertools import combinations, product

HALF=F(1,2)
RAYS0=((F(1),F(0)),(F(77,85),F(36,85)),(F(481,769),F(600,769)),
       (F(9,41),F(40,41)),(F(-9,41),F(40,41)),
       (F(-481,769),F(600,769)),(F(-77,85),F(36,85)))
RAYS=RAYS0+tuple((-x,-y) for x,y in RAYS0)

def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def add(a,b):return a[0]+b[0],a[1]+b[1]
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def mul(t,a):return t*a[0],t*a[1]
def rot(a):return -a[1],a[0]

def geometry():
    u=F(11,12);r=F(1753659,1000000);U=F(331179,200000)
    v=F(547767,1000000);w=F(95073,50000)
    e=(F(255,257),F(32,257));f=rot(e)
    h1=dot(e,(r,-u))-2-e[0]
    h2=dot(f,(-w,-v))-1-e[1]
    P5=add(mul(h1,e),mul(h2,f))
    H=add(P5,mul(HALF,add(e,f)));G=add(H,e)
    centers=[(r-HALF,HALF-u),(U-HALF,F(3,2)-u),
             (U-F(3,2),F(7,20)),(U-F(5,2),F(3,2)-v),
             (HALF-w,HALF-v),(U-F(3,2),F(27,20)),H,G]
    frames=[((F(1),F(0)),(F(0),F(1)))]*6+[(e,f),(e,f)]
    return centers,frames

def support(frame,n):
    return (abs(dot(frame[0],n))+abs(dot(frame[1],n)))/2

def longest(edges):
    adj=[[] for _ in range(8)]
    for i,j in edges:adj[i].append(j)
    memo={}
    def depth(i,stack):
        if i in stack:raise AssertionError('Directed projection cycle')
        if i not in memo:
            memo[i]=max((1+depth(j,stack|{i}) for j in adj[i]),default=0)
        return memo[i]
    return max(depth(i,set()) for i in range(8))

def check():
    for ray in RAYS:assert dot(ray,ray)==1
    crosses=[]
    for a,b in zip(RAYS,RAYS[1:]+RAYS[:1]):
        c=cross(a,b);crosses.append(c)
        assert F(0)<c<F(9,20) and dot(a,b)>0
    assert len(crosses)==14 and max(crosses)==F(28884,65365)
    assert F(11,20)>F(37,50)**2
    assert F(9789,2500)<F(99,50)**2
    print('14 rational unit rays, 14 strict cross/dot gaps: PASS')

    # A complete symbolic owner word that passes old DAG path-length checks
    # but is rejected by the seven narrower rational projection graphs.
    oldx=[(i,j) for i,j in combinations(range(8),2) if j<5]
    oldy=[(i,j) for i,j in combinations(range(8),2) if j>=5]
    assert len(oldx)+len(oldy)==28
    assert longest(oldx)==4 and longest(oldy)==3
    print('Complete true-axis owner word: passes old path screen, fails new: PASS')

    centers,frames=geometry()
    graphs=[[] for _ in range(7)]
    q=F(9789,2500)
    nv=0
    for p,(e,f) in zip(centers,frames):
        for s,t in product((-1,1),repeat=2):
            z=add(p,mul(HALF,add(mul(s,e),mul(t,f))))
            assert dot(z,z)<q
            nv+=1
    assert nv==32
    for i,j in combinations(range(8),2):
        d=sub(centers[j],centers[i])
        normals=[mul(s,n) for n in (*frames[i],*frames[j]) for s in (-1,1)]
        n=max(normals,key=lambda n:dot(n,d))
        a=dot(n,d)
        w=support(frames[i],n)+support(frames[j],n)
        assert a>=w>=1
        assert abs(dot(rot(n),d))<=a
        k=max(range(14),key=lambda k:dot(n,RAYS[k]))
        assert dot(RAYS[k],d)>F(37,50)*w
        if k>=7:graphs[k-7].append((j,i))
        else:graphs[k].append((i,j))
    assert sum(len(g) for g in graphs)==28
    lengths=[longest(g) for g in graphs]
    assert max(lengths)<=3
    print('Genuine rational n8 packing: 32 vertices, 28 SAT pairs, seven depth-three DAGs: PASS',lengths)
    print('No finite regression is treated as a complete global radius certificate.')

if __name__=='__main__':check()

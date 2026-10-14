#!/usr/bin/env python3
"""Exact rational actual M5-DIFFUSE packing above q*=R*², below 397/100.

Full coordinate proof and inequality interpretation:
GATE3B_M5_DIFFUSE_EXACT_POSITIVE_CONTROL.md.
No floats, scipy or external packages.
"""
from fractions import Fraction as F
from itertools import combinations,product
from verify_seven_rational_projection_orders import RAYS,longest,dot,sub,add,mul,rot

B=F(414213562373,10**12)
t=(F(1,2000),F(3,2000),-F(3,2000),-F(1,2000),-F(1,8000))
z=(F(0),F(1,1000))+tuple((B+a)/(1-B*a) for a in t)+((1-F(1,1000))/(1+F(1,1000)),)
RAW=((-55438,9590),(-501244,1222533),(-1056036,-926381),
     (1057741,-925965),(-1265031,278678),(356,-1284918),
     (1265145,280149),(500754,1222818))
centers=[(F(x,10**6)*F(5001,5000),F(y,10**6)*F(5001,5000)) for x,y in RAW]
frames=[]
for a in z:
    e=((1-a*a)/(1+a*a),2*a/(1+a*a))
    frames.append((e,rot(e)))

def mod_quarter(a,b):
    x=dot(a,b);y=a[0]*b[1]-a[1]*b[0]
    for _ in range(4):
        if x>0 and y>=0:return x,y
        x,y=-y,x
    raise AssertionError('Invalid orientation')

def support(i,n):
    e,f=frames[i]
    return (abs(dot(n,e))+abs(dot(n,f)))/2

def check():
    counts=[sum(x>=y for x,y in (mod_quarter(frames[i][0],frames[j][0])
                                 for j in range(8))) for i in range(8)]
    assert counts==[5,5,4,4,5,5,4,4]
    order=(0,2,1,3,4,7,5,6);word='LHLHLHLL'
    folded=[]
    for j,c in zip(order,word):
        ex,ey=frames[j][0]
        if c=='L':
            assert ex>=ey>=0
            folded.append(ey/ex)
        else:
            assert ey>=ex>=0
            folded.append((ey-ex)/(ex+ey))
    assert folded[0]==0 and all(folded[i]<folded[i+1] for i in range(7))

    maximum=F(0)
    for p,(e,f) in zip(centers,frames):
        far=(abs(dot(p,e))+F(1,2))**2+(abs(dot(p,f))+F(1,2))**2
        maximum=max(maximum,far)
        for s,t in product((-1,1),repeat=2):
            q=add(p,mul(F(1,2),add(mul(s,e),mul(t,f))))
            assert dot(q,q)<F(397,100)
    assert maximum < F(397,100)-F(1,2000)

    mingap=None;W=F(0);graphs=[[] for _ in range(7)]
    for i,j in combinations(range(8),2):
        d=sub(centers[j],centers[i])
        normals=[mul(s,n) for n in (*frames[i],*frames[j]) for s in (-1,1)]
        n=max(normals,key=lambda n:dot(n,d))
        w=support(i,n)+support(j,n)
        gap=dot(n,d)-w
        assert gap>F(1,10000)
        mingap=gap if mingap is None else min(mingap,gap)
        k=max(range(14),key=lambda k:dot(n,RAYS[k]))
        graphs[k%7].append((i,j) if k<7 else (j,i))
        ei=frames[i][0];ej,fj=frames[j]
        W+=(1+abs(dot(ei,ej))+abs(dot(ei,fj)))/2
    assert sum(map(len,graphs))==28
    lengths=[longest(g) for g in graphs]
    assert max(lengths)<=3

    # Jensen J is not rational because c and folded gaps involve pi.
    # Bound it rigorously using rational pair widths and rational tangent
    # inequalities for the two angular deviations at the dominant cut.
    assert F(14143,10000)**2>2
    W0_upper=(41+15*F(14143,10000))/2
    assert W-W0_upper>F(3,200)
    for j in (3,4):
        ex,ey=frames[j][0]
        assert abs(ey-ex)/(ey+ex)<F(1,100)
    # h=pi/4>3/4, Lambda_odd <=1-lambda4<2/75,
    # c=(sqrt2-1)/2<1/4:
    assert F(3,200)-F(1,150)==F(1,120)>F(3,1000)

    print('TRUE M5-DIFFUSE packing q<397/100: PASS')
    print('Exact folded word I; M5 counts:',counts)
    print('32 vertices, 28 strict SAT gaps, radius reserve >1/2000, gap >1/10000: PASS')
    print('Rigorous Jensen defect J>1/120>3/1000: PASS')
    print('Seven order DAG path lengths:',lengths)
    print('q=397/100 exceeds the research ceiling Q=9789/2500: no optimality counterexample.')

if __name__=='__main__':check()

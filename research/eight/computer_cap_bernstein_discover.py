#!/usr/bin/env python3
"""Computer-guided rational Bernstein certificate discovery (NOT an n=8 proof).

Scans rational cap offset H and candidate center-height ceiling Y for
a hand-reducible true-square one-cap proof under q<=9789/2500:
  1) 3 strict true-vertex endpoint / negative-tilt margins;
  2) positivity of P(h,y,z) at 4 rational parameter vertices,
     over the entire z interval [0,1/2], certified by recursively
     splitting into exact degree-6 Bernstein coefficient intervals.
The mathematical implication of these checks is proved separately
in HUMAN_CAP_ENVELOPE_79_250.md. Negative results from this search
mean only this proof template failed, NOT that the theorem is false.
"""
from fractions import Fraction as F
from math import comb
Q=F(9789,2500)
SQRT2_LO=F(141,100)  # squared <2
PH=[F(v) for v in (0,-4,12,0,16,4,4)]
PY=[F(v) for v in (2,-8,-2,-8,-2,0,2)]
P0=[F(v) for v in (1,-3,6,14,5,1,0)]
def poly(h,y):return [P0[i]+h*PH[i]+y*PY[i] for i in range(7)]
def bern(p,a,b):
    ct=[sum(p[j]*comb(j,i)*a**(j-i)*(b-a)**i for j in range(i,7)) for i in range(7)]
    return [sum(ct[i]*F(comb(k,i),comb(6,i)) for i in range(k+1)) for k in range(7)]
def cover(p,a=F(0),b=F(1,2),depth=0,maxdepth=10):
    vals=bern(p,a,b)
    if min(vals)>0:return [(a,b,min(vals))]
    if depth>=maxdepth:return None
    mid=(a+b)/2
    left=cover(p,a,mid,depth+1,maxdepth)
    if left is None:return None
    right=cover(p,mid,b,depth+1,maxdepth)
    if right is None:return None
    return left+right
def candidate(H,Y):
    if H<=0 or Y<=0 or H+Y>=F(7,5):return None
    qa=(1+H)**2+(Y+F(1,2))**2-Q
    negdiag=(H+SQRT2_LO)**2+Y*Y-Q
    negexcess=2*H*F(2,5)+F(3,4)-Y
    if min(qa,negdiag,negexcess)<=0:return None
    verts=[(H,F(0)),(F(7,5),F(0)),(H,Y),(F(7,5)-Y,Y)]
    certificates=[]
    for h,y in verts:
        vals=cover(poly(h,y))
        if vals is None:return None
        certificates.append(vals)
    return {'H':str(H),'Y':str(Y),
            'smallest_endpoint_margin':str(min(qa,negdiag,negexcess)),
            'smallest_bernstein_coefficient':str(min(v for cells in certificates for _,_,v in cells)),
            'subinterval_count':sum(map(len,certificates))}
if __name__=='__main__':
    Hs=[F(31,100),F(39,125),F(5,16),F(63,200),F(79,250),F(8,25),F(1,3)]
    Ys=[F(49,50),F(491,500),F(983,1000),F(123,125),F(197,200),F(39,40)]
    for H in Hs:
        successes=[c for Y in Ys if (c:=candidate(H,Y)) is not None]
        print('H:',str(H),'certified templates:',successes)

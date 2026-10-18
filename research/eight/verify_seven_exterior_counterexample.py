#!/usr/bin/env python3
"""Seven exterior unit squares fit below the eight-square candidate radius.

Exact rational verification; standard library only. This disproves the proposed
reduction that seven exterior squares alone require radius 1.9787708653....
It does not construct eight squares or refute the Cantrell candidate.
"""
from fractions import Fraction as F
from itertools import product, combinations

R = F(197865, 100000)
CENTERS = [
    (F(10000001,20000000), F(-1450326431,25000000000)),
    (F(10666400317,12500000000), F(94390109519,100000000000)),
    (F(-11516549481,50000000000), F(4337263617,3125000000)),
    (F(-27616753203,25000000000), F(197344331,312500000)),
    (F(-36971710767,50000000000), F(-32030853837,100000000000)),
    (F(-32043407907,100000000000), F(-125890890037,100000000000)),
    (F(16905444919,25000000000), F(-112506208709,100000000000)),
]
HALF_TANGENTS = [F(0), F(-638499821,100000000000), F(1160022143,12500000000),
    F(10182015477,100000000000), F(4791805591,50000000000),
    F(9472925579,100000000000), F(1126860849,12500000000)]


def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]


def perpendicular(e):
    return -e[1],e[0]


def verify():
    axes=[((1-h*h)/(1+h*h),2*h/(1+h*h)) for h in HALF_TANGENTS]
    cm,pm,em=[],[],[]
    for C,e in zip(CENTERS,axes):
        f=perpendicular(e)
        assert dot(e,e)==1 and dot(e,f)==0
        for s,t in product((-1,1),repeat=2):
            v=tuple(C[k]+(s*e[k]+t*f[k])/2 for k in range(2))
            cm.append(R*R-dot(v,v))
        em.append(max(abs(dot(C,e)),abs(dot(C,f)))-F(1,2))
    for i,j in combinations(range(7),2):
        directions=(axes[i],perpendicular(axes[i]),axes[j],perpendicular(axes[j]))
        d=tuple(CENTERS[i][k]-CENTERS[j][k] for k in range(2))
        pm.append(max(abs(dot(d,n))-sum(abs(dot(n,e)) for e in directions)/2
                      for n in directions))
    assert min(cm)>F(1,20000)
    assert min(pm)>F(1,10000000)
    assert min(em)>=F(1,20000000)
    print('Verified 7 unit squares, 28 corners, 21 pair separators.')
    print('All closed squares avoid the origin.')
    print('All squares fit in R=197865/100000=1.97865.')
    print('Therefore a sharp n=8 argument must retain the central obstacle.')


if __name__=='__main__':
    verify()

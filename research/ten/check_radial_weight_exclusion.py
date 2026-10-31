#!/usr/bin/env python3
"""Exact finite certificate for RADIAL_WEIGHT_EXCLUSION.md.

This is a computer-assisted exclusion of five inner centres, not a hand
proof of the unrestricted ten-square theorem. Uses only the standard library.
"""
from array import array
from math import isqrt
from functools import lru_cache
from collections import Counter

D=20*2**12
D2=D*D
RADII=[D//2,4*D//5,21*D//20,27*D//20]
PRIMITIVES={}
for M in RADII:
    # On each unit interval [j-1,j], sqrt(M²-t²) decreases.  Its integral
    # lies between floor(sqrt(M²-j²)) and floor(sqrt(M²-(j-1)²))+1.
    lo=array('q', [0])
    hi=array('q', [0])
    previous_height=M
    for j in range(1,M+1):
        height=isqrt(M*M-j*j)
        lo.append(lo[-1]+height)
        hi.append(hi[-1]+previous_height+1)
        previous_height=height
    PRIMITIVES[M]=(lo,hi)

@lru_cache(maxsize=None)
def rectangle_cdf(M,x,y):
    """Bounds on D² times area of disk∩[0,x/D]×[0,y/D], signed."""
    sign=(1 if x>=0 else -1)*(1 if y>=0 else -1)
    x=min(abs(x),M);y=min(abs(y),M)
    if x*x+y*y<=M*M:
        l=u=x*y
    else:
        lo,hi=PRIMITIVES[M]
        l=int(lo[x])+int(lo[y])-int(hi[M])
        u=int(hi[x])+int(hi[y])-int(lo[M])
    return (l,u) if sign>0 else (-u,-l)

@lru_cache(maxsize=None)
def square_cdf(M,a,b):
    if b>a:return square_cdf(M,b,a)
    l=u=0
    for sx,sy,s in [(1,1,1),(-1,1,-1),(1,-1,-1),(-1,-1,1)]:
        ll,uu=rectangle_cdf(M,a+sx*(D//2),b+sy*(D//2))
        if s>0:l+=ll;u+=uu
        else:l-=uu;u-=ll
    return l,u

def score_lower(a0,a1,b0,b1):
    # Ten times the weighted area, in integer units 1/D².
    return (34*square_cdf(RADII[1],a1,b1)[0]
            -13*square_cdf(RADII[0],a0,b0)[1]
            +40*square_cdf(RADII[3],a1,b1)[0]
            -40*square_cdf(RADII[2],a0,b0)[1])

counts=Counter();depths=Counter()
stack=[(0,2*D,0,2*D,0)]
while stack:
    a0,a1,b0,b1,depth=stack.pop()
    if b0>a1:
        counts['outside_symmetry_wedge']+=1;continue
    if 2*((a0+D//2)**2+(b0+D//2)**2)>9*D2:
        counts['outside_containing_disk']+=1;continue
    intersects_inner=a0*a0+b0*b0<=D2
    target=20 if intersects_inner else 10
    lower=score_lower(a0,a1,b0,b1)
    if lower>=target*D2:
        counts['certified_inner' if intersects_inner else 'certified_outer']+=1
        depths[depth]+=1;continue
    if depth>=13:
        raise AssertionError(('uncertified',a0,a1,b0,b1,depth,lower,target*D2))
    am=(a0+a1)//2;bm=(b0+b1)//2
    assert 2*am==a0+a1 and 2*bm==b0+b1
    stack.extend([(a0,am,b0,bm,depth+1),(am,a1,b0,bm,depth+1),
                  (a0,am,bm,b1,depth+1),(am,a1,bm,b1,depth+1)])
print('PASS',dict(counts),'depths',dict(sorted(depths.items())))
print('All accepted comparisons and circle-area bounds use exact integers.')
assert 4731*22<15*1000*7
print('Total radial weight < (4731/1000)*(22/7) < 15.')

"""Independent exact audit of the SAME 208-box radius-two measure witness.

This checker does not import or call the original verifier. The explicit
423-symbol forest is an alternative encoding of its same 208 charged leaves,
6 empty leaves and 209 binary splits; it is not a second witness or packet.
Every split, empty test and leaf charge is checked independently below.

Inverse trigonometry uses two half-angle reductions and 32 alternating atan
terms at scale 2^80. Pi comes from 40-term exact rational Machin bounds. No float
or nonstandard dependency is used. See the accompanying independent review.
Run directly with standard Python 3.
"""
from math import isqrt
from fractions import Fraction as Fr
from functools import lru_cache
from collections import Counter
import hashlib
import json

S=1<<80
B=5*(1<<24)
WEIGHTS=((1,10,714),(1,1,3858),(11,10,2424),(27,20,1709))
ORIGINAL_SCALE=1<<56
ORIGINAL_PI_LO=226375608064909912
ORIGINAL_PI_HI=226375608064910268
EXPECTED_DIGEST='d86a26a628643d32387e0ba9800dcfc1830335f7828d0335bcd9c2172767b0c5'
TRACE=(
    'SSSSSSCCCCSCSCCSSSCCSCSCCSSSCCSCCSSCSCCSSCCSCCSSSSSSCCSCCSSCCSCCSSSSCCSCCSSCCSCC'
    'SSSCCSCCSSCCCSSSSCCSCCSSCCSCCSSSCCSCCSSCCSCCSSSSSCCSCCSSCCSCCSSSSCCSCCSSCCSCCSSS'
    'CCSCCSSCCSCCSSSSSCCSCCSSCCSCCSSSCCSCEEESCCSSSSCSESCESSCSCCSSCCCSECSSCSSCCCCSSSCS'
    'CCSSCCSSCCSCCSSSSCCSCCSSSCCSCCSSCCSCCSSSSCCSCCSSSCCSCCSSCCSCCSSSSCCSCCSSCCSCCSSS'
    'CSCCSSCCSCCSSSCCSCCSSCSCCSSCCSCSCSCSCCSSSSCSCCSSCSCCSSCCSCCSSSSCCSCCSSCCSCCSSCCS'
    'CCSSSCCCSCSCSCSCSCSCSCC'
)

def ceildiv(n,d):return (n+d-1)//d

def arctan_fraction(x):
    z=sum(((-1)**k*x**(2*k+1)/Fr(2*k+1) for k in range(40)),Fr(0))
    return z,z+x**81/81
p5=arctan_fraction(Fr(1,5));p239=arctan_fraction(Fr(1,239))
pilo=16*p5[0]-4*p239[1];pihi=16*p5[1]-4*p239[0]
assert Fr(ORIGINAL_PI_LO,ORIGINAL_SCALE)<pilo<pihi<Fr(ORIGINAL_PI_HI,ORIGINAL_SCALE)
PL=(pilo*S).__floor__();PH=(pihi*S).__ceil__()

@lru_cache(None)
def atansmall(z):
    assert 0<=z<=S//2
    square=(z*z//S,ceildiv(z*z,S))
    power=(z,z);acc=[0,0]
    for j in range(32):
        term=(power[0]//(2*j+1),ceildiv(power[1],2*j+1))
        if j&1:acc[0]-=term[1];acc[1]-=term[0]
        else:acc[0]+=term[0];acc[1]+=term[1]
        power=(power[0]*square[0]//S,ceildiv(power[1]*square[1],S))
    acc[1]+=ceildiv(power[1],65)
    return tuple(acc)

@lru_cache(None)
def arcsin(n,d):
    if n<=0:return (0,0)
    if n>=d:return (PL//2,ceildiv(PH,2))
    # Enclose q=t/(1+sqrt(1-t^2)) using exact rational radicands.
    rad=d*d-n*n
    rootlo=isqrt(rad*S*S)//d
    roothi=ceildiv(isqrt(rad*S*S)+1,d)
    qlo=n*S*S//(d*(S+roothi))
    qhi=ceildiv(n*S*S,d*(S+rootlo))
    # Halve arctan once more. q/(1+sqrt(1+q^2))<=sqrt(2)-1<1/2.
    rlo=isqrt(S*S+qlo*qlo)
    rhi=isqrt(S*S+qhi*qhi)+1
    vlo=qlo*S//(S+rhi)
    vhi=ceildiv(qhi*S,S+rlo)
    assert vhi<S//2
    return 4*atansmall(vlo)[0],4*atansmall(vhi)[1]

def angle(x,rn,rd):return arcsin(x*rd,B*rn)
def arccos(x,rn,rd):
    lo,hi=angle(x,rn,rd)
    return PL//2-hi,ceildiv(PH,2)-lo

def arc(box,rn,rd):
    al,ah,bl,bh=box;xx=(ah-B,al);yy=(bh-B,bl);ans=0
    for reflection_x in [False,True]:
        xl,xh=((-xx[1],-xx[0]) if reflection_x else xx)
        xl=max(xl,0)
        if xl>=xh:continue
        for reflection_y in [False,True]:
            yl,yh=((-yy[1],-yy[0]) if reflection_y else yy)
            yl=max(yl,0)
            if yl>=yh:continue
            low=max(arccos(xh,rn,rd)[1],angle(yl,rn,rd)[1])
            high=min(arccos(xl,rn,rd)[0],angle(yh,rn,rd)[0])
            ans+=max(high-low,0)
    return ans

def audit_charge(box):
    al,ah,bl,bh=box
    score=sum(ww*arc(box,rn,rd) for rn,rd,ww in WEIGHTS)
    atom=292 if ah<B and bh<B else 0
    margin=score-(1000-atom)*2*PH
    assert margin>0,(box,margin)
    return margin

def verify():
    roots=[
        ('line',9*B//10,B,B//2,B//2,0),
        ('line',B,11*B//10,B//2,B//2,0),
        ('corner',9*B//10,11*B//10,9*B//10,11*B//10,0),
        ('middle',11*B//10,27*B//20,B,27*B//20,0),
        ('outer',0,0,B//2,3*B//2,0),
    ]
    stack=roots[:];count=Counter();minimum=None;cursor=0;depth=0
    digest=hashlib.sha256()
    while stack:
        typ,al,ah,bl,bh,dep=stack.pop()
        assert cursor<len(TRACE),'incomplete forest'
        step=TRACE[cursor];cursor+=1
        if typ=='outer':
            invalid=bl*bl>2*B*B
            if not invalid:
                al=isqrt(4*B*B-bh*bh)
                ah=isqrt(4*B*B-bl*bl)+1
        else:
            invalid=typ!='line' and (bl>ah or al*al+bl*bl>4*B*B)
        box=(al,ah,bl,bh)
        if step=='E':
            assert invalid,('unproved empty box',typ,box)
            count['empty']+=1
        elif step=='C':
            assert not invalid
            margin=audit_charge(box)
            minimum=margin if minimum is None else min(minimum,margin)
            count['charged']+=1
        else:
            assert step=='S' and not invalid
            count['split']+=1
            if typ!='outer' and ah-al>=bh-bl:
                mid=(al+ah)//2;assert al<mid<ah
                stack.extend([(typ,mid,ah,bl,bh,dep+1),(typ,al,mid,bl,bh,dep+1)])
            else:
                mid=(bl+bh)//2;assert bl<mid<bh
                stack.extend([(typ,al,ah,mid,bh,dep+1),(typ,al,ah,bl,mid,dep+1)])
            continue
        depth=max(depth,dep)
        digest.update((typ+':'+step+':'+','.join(map(str,box))+'\\n').encode())
    assert cursor==len(TRACE),'unused forest suffix'
    assert count==Counter(split=209,empty=6,charged=208)
    assert count['charged']+count['empty']==count['split']+len(roots)
    assert digest.hexdigest()==EXPECTED_DIGEST
    assert 292+sum(ww for _,_,ww in WEIGHTS)==8997
    result={
        'independent_scale':S,
        'coordinate_denominator':B,
        'charged_leaves':count['charged'],
        'empty_leaves':count['empty'],
        'splits':count['split'],
        'maximum_depth':depth,
        'minimum_independent_margin_integer':minimum,
        'same_leaf_sha256':digest.hexdigest(),
        'original_pi_enclosure_independently_verified':True,
    }
    print(json.dumps(result,sort_keys=True),flush=True)
    return result


if __name__=='__main__':
    verify()

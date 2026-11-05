"""Necessary rational chords from disjoint original half-unit incircles."""
from fractions import Fraction as F
from math import isqrt
PREFIX='physical_incircle_chord_'

def sqrt_lower(q,bits=30):
    q=F(q);assert q>=0
    scale=1<<bits
    return F(isqrt((q.numerator*scale*scale)//q.denominator),scale)

def row(i,j,axis,sign,lo,hi,a,b):
    lo,hi,a,b=map(F,(lo,hi,a,b));assert 0<=i<j<9 and axis in(0,1)and sign in(-1,1)
    assert -1<=lo<hi<=1 and a>=0 and b>=0 and a*a+lo*lo<=1 and b*b+hi*hi<=1
    slope=(b-a)/(hi-lo);co={2*i+axis:F(sign),2*j+axis:F(-sign),2*i+1-axis:-slope,2*j+1-axis:slope}
    rhs=slope*lo-a;name=PREFIX+'_'.join(map(str,(i,j,axis,sign,lo,hi,a,b)))
    return tuple((k,v)for k,v in sorted(co.items())if v),rhs,name

def generate(differences):
    answer=[]
    for (i,j),box in sorted(differences.items()):
        for axis in(0,1):
            lower,upper=box[axis];lo,hi=box[1-axis]
            sign=1 if lower>=0 else -1 if upper<=0 else None
            if sign is None or not -1<=lo<hi<=1:continue
            a,b=sqrt_lower(1-lo*lo),sqrt_lower(1-hi*hi)
            answer.append(row(i,j,axis,sign,lo,hi,a,b))
    return answer

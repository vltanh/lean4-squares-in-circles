#!/usr/bin/env python3
"""Exact scalar checks for the printed continuous hand strengthening."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib

def add(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,c in enumerate(a):out[i]+=c
    for i,c in enumerate(b):out[i]+=c
    return out

def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):out[i+j]+=c*d
    return out

def scale(a,k):return [c*k for c in a]
def value(a,x):return sum(c*x**i for i,c in enumerate(a))
def deriv(a):return [i*c for i,c in enumerate(a)][1:]

def main():
    U=F(11,30);cut=F(105,88);L=[F(1),F(0),F(1,2),F(0),-F(1,8)]
    rdiff=add([F(1),F(0),F(1)],scale(mul(L,L),-1))
    assert rdiff==[F(0)]*6+[F(1,8),F(0),-F(1,64)]
    p=scale(add(mul([F(4301,10000),-U],L),[F(0),F(-1),F(1)]),240000)
    assert p==list(map(F,[103224,-328000,291612,-44000,-12903,11000]))
    pp=deriv(deriv(p));assert pp==list(map(F,[583224,-264000,-154836,220000]))
    assert add([F(164388)],add([F(264000),F(-264000)],add([F(154836),F(0),F(-154836)],[F(0),F(0),F(0),F(220000)])))==pp
    s=F(2,3);p0=value(p,s);p1=value(deriv(p),s)
    assert p0==F(6184,243) and p1==-F(184592,81)
    reserve=p0-p1*p1/(2*164388)
    assert reserve==F(2602608088,269637417)>0
    assert F(7,16)-U*cut==0
    assert 2*cut-2-U==F(13,660)>0
    assert (cut-1)**2==F(289,7744)>0
    radical=2*34375**2-48602**2;assert radical==1126846>0
    assert F(1)-U*U==F(779,900) and F(779,900)>U*U
    out={'status':'PASS','scope':'Exact scalar arithmetic for a continuous hand proof; zero whole-mask closures',
         'total_variation_bound':str(U),'polynomial_lower_reserve':str(reserve),
         'first_branch_derivative_reserve':'13/660','radical_squared_reserve':radical,
         'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()

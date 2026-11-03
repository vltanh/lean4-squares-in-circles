#!/usr/bin/env python3
"""Exact scalar/polynomial checks for the positive-D separator hand gate."""
from fractions import Fraction as F
import json

def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]
def mul(a,b):
    r=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    return r
def scale(a,c):return [c*x for x in a]
def diff(a):return [i*a[i] for i in range(1,len(a))]
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

# L=N/W. The exact second derivative has denominator W^3.
N=[0,0,2,-4,2];W=[1,2,0,2,-1]
P2=add(mul(diff(diff(N)),mul(W,W)),scale(mul(mul(N,diff(diff(W))),W),-1))
P2=add(P2,scale(mul(mul(diff(N),W),diff(W)),-2))
P2=add(P2,scale(mul(N,mul(diff(W),diff(W))),2))
P=[1,-6,-6,-6,36,6,-18,6,3]
assert trim(P2)==scale(P,4)
assert F(227,160)**2-2==F(329,25600)>0
assert F(17,12)**2-2==F(1,144)>0
assert 2-F(24,17)**2==F(2,289)>0
assert F(61,8)**2-58==F(9,64)>0
assert 5*(1-2*F(3,10))**2-1==F(-1,5)<0
assert 1-6*F(7,32)==-F(5,16)
assert 6*F(5,12)**2==F(25,24)
assert -F(5,16)+F(25,576)==-F(155,576)<0
z=F(7,32)
L=2*z*z*(1-z)**2/((1+z*z)*(1+2*z-z*z))
assert L==F(61250,1526879)
right=F(1,17)+L-F(91,960)
left=F(1,17)+F(11,305)-F(91,960)
assert right==F(103322027,24918665280)>0
assert left==F(97,995520)>0
assert F(2011,960)-2==F(91,960)
print(json.dumps({'claim':'positive-D original weak-link upward/shallow separator reduction',
                  'status':'PASS','right_endpoint_reserve':str(right),
                  'left_endpoint_reserve':str(left),'whole_mask_closed':False},indent=2))

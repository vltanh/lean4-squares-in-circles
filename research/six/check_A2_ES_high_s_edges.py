#!/usr/bin/env python3
"""Exact scalar edges for the high-s E/S source extensions.

This checker supports the hand chamber reductions used to repair the
Pattern-12 and Pattern-13 ranges 1/6 <= s <= 2/5.  It is deliberately
one-dimensional after the hand derivative reductions; it is not a 2D box
certificate.
"""
from fractions import Fraction as F
import n6_a2_scalar as X

I,J=X.I,X.J
jj,jsin,jcos=X.jj,X.jsin,X.jcos

# Exact candidate outer-edge weights.
h=X.h
ss=X.ss
tt=(-20+30*h)*ss+F(7,2)-F(9,2)*h
r=(ss+F(1,2))/(ss+F(3,2))
k=(tt+F(1,2))/(F(3,2)-ss)
m=(1+r)*k

def rel(q,src):
    sq,cq=jsin(q),jcos(q)
    if src=="Sp": return sq,cq,J(-1),J(0)
    if src=="Ss": return cq,-sq,J(0),J(1)
    if src=="Ep": return J(1),J(0),-sq,cq
    if src=="Es": return J(0),J(1),-cq,-sq
    raise KeyError(src)

def B(e,s,pat13,src):
    e,s=jj(e),jj(s)
    se,ce=jsin(e),jcos(e)
    sn,cs=jsin(s),jcos(s)
    q=e-s
    sq,cq=jsin(q),jcos(q)
    HCE=J(F(1,2))+(ce+X.jabs(se))/2
    HSC=J(F(1,2))+(cs+X.jabs(sn))/2
    HSE=J(F(1,2))+(cq+X.jabs(sq))/2
    cE,sE,cS,sS=rel(q,src)
    if pat13:
        muE=J(1)/ce
        muS=J(1)+se/ce
        GEx=muE+J(r)*cE
        GEy=J(r)*sE
    else:
        muE=muS=J(1)
        GEx=ce+J(r)*cE
        GEy=-se+J(r)*sE
    GSx=muS*cs-J(r)*cS
    GSy=-muS*sn-J(r)*sS+J(m)
    return (muE*HCE+muS*HSC+J(r)*HSE+J(m)/2
            -X.support_any(GEx,GEy)-X.support_any(GSx,GSy))

# At e=0 the two central patterns coincide.
def delta(s):
    return B(J(0),s,False,"Sp")-B(J(0),s,False,"Es")

dlo=F(100)
for a,b in X.parts(F(1,6),F(2,5),F(1,200)):
    z=delta(J(I(a,b),1)).d
    dlo=min(dlo,z.lo)
assert dlo>F(13,50),dlo

# S-secondary: the hand e-calculus sends the minimum to e=0.
def ss_edge(s):
    return B(J(0),s,False,"Ss")-B(J(0),s,False,"Es")
ssmin=X.minval(ss_edge,F(1,6),F(2,5),F(1,1000))
assert ssmin>F(1,10000),ssmin

# Pattern 12 E-primary: its same-e comparison with S-primary decreases in s,
# so the hand reduction sends s to 2/5.  Audit the remaining scalar e-edge.
def p12_ep_edge(e):
    s=J(F(2,5))
    return B(e,s,False,"Ep")-B(e,s,False,"Sp")
p12ep=X.minval(p12_ep_edge,F(-2,5),F(2,5),F(1,1000))
assert p12ep>F(3,1000),p12ep

# Pattern 13 E-primary: on the positive-e high-s chamber the only interior
# source wall is e=s; the hand derivative reduction sends minima to that wall
# or to the already-strong e<=0 boundary.  Audit the tight scalar wall.
def p13_ep_wall(s):
    return B(s,s,True,"Ep")-B(J(0),s,True,"Es")
p13ep=X.minval(p13_ep_wall,F(1,6),F(3,10),F(1,1000))
assert p13ep>F(1,20),p13ep

print("high-s E/S scalar edges: PASS")
print("Delta' >",float(dlo))
print("S-secondary edge >",float(ssmin))
print("P12 E-primary edge >",float(p12ep))
print("P13 E-primary wall >",float(p13ep))

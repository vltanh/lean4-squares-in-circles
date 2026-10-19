#!/usr/bin/env python3
"""Exact-rational arithmetic audit of HUMAN_LOCAL_ANGLE_MISMATCH_BACKBONE.md.

The analytical proof (independent-angle SAT ownership and
mismatch inequality) is in the Markdown file. This script
reconstructs the five exact oriented true candidate edges and
checks every stated rational comparison.

The global sharp R8 >= Rhat theorem and the minimizer-level
five-corner support extraction remain UNPROVED.
"""
from fractions import Fraction as F

one=F(1)
zero=F(0)
r=F(1753659,1000000)
U=F(331179,200000)
u=F(11,12)
v=F(547767,1000000)
w=F(95073,50000)
c=F(255,257)
s=F(32,257)
assert c*c+s*s==1
dot=lambda a,b:a[0]*b[0]+a[1]*b[1]
J=lambda a:(-a[1],a[0])
minus=lambda a,b:(a[0]-b[0],a[1]-b[1])
plus=lambda a,b:(a[0]+b[0],a[1]+b[1])
e=(c,s)
f=(-s,c)
h1=c*r-s*u-2-c
h2=s*w-c*v-1-s
P5=plus((h1*c,h1*s),(h2*f[0],h2*f[1]))
pH=plus(P5,((c-s)/2,(s+c)/2))
pG=plus(pH,e)
P={
 "A":(r-F(1,2),F(1,2)-u),
 "B":(U-F(1,2),F(3,2)-u),
 "T":(U-F(3,2),F(27,20)),
 "D":(U-F(5,2),F(3,2)-v),
 "E":(F(1,2)-w,F(1,2)-v),
 "H":pH,
 "G":pG,
}
cases=[
 ("AB","A","B",(zero,one), F(24441,250000)),
 ("TB","T","B",(one,zero),-F(23,30)),
 ("DT","D","T",(one,zero),F(397767,1000000)),
 ("ED","E","D",(zero,one),-F(111471,200000)),
 ("HG","H","G",e,zero),
]
for name,i,j,n,Y0 in cases:
    d=minus(P[j],P[i])
    assert dot(n,n)==one
    assert dot(n,d)==one,(name,"normal",dot(n,d))
    assert dot(J(n),d)==Y0,(name,"transverse",dot(J(n),d))
    assert abs(Y0)<=F(23,30)
    assert dot(d,d)==one+Y0*Y0 < F(9,4)
    print(name, "transverse =",Y0)

eps=F(1,50)
Ybound=F(23,30)+F(7,2)*eps
assert Ybound==F(251,300)
assert F(17,20)-Ybound==F(1,75)>0
# Any incorrect perpendicular SAT owner nperp has its
# projected center gap less than 17/20, while the
# sum of halfwidths of two unit squares is >=1.
assert F(17,20)<1
# All positively oriented correct axes retain positive projection.
assert 1-F(7,2)*eps==F(93,100)>0
# For frame half-difference |delta|<=eps, cosine(delta)
# is at least 1-eps^2/2. Exact angle penalty beta=7/100.
eta=one-eps*eps/2-F(17,20)
beta=F(7,100)
assert eta>0
assert eta/2-beta==F(49,10000)>0
print("PASS: 5 genuine backbone pair normals and transverse coords")
print("PASS: within Euclidean center/frame eps=1/50, wrong")
print("      SAT owner axes impossible, desired axes forced")
print("PASS: g_mid >= (7/100)*|angle_p-angle_q|")

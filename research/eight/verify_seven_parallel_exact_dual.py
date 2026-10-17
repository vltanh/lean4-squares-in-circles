#!/usr/bin/env python3
"""Exact rational certificate for all-parallel, zero-tilt, seven-directed supports.

For EVERY seven centers (not only the candidate), the weighted
circle-vertex identity yields:
 q >= 2257/576 + quadratic four-anchor-center error + seven
 weighted genuine directed separator gaps.

Checks the entire polynomial identity with SymPy (exact rationals),
all vertex and actual SAT inequalities in an explicit attaining
seven-square packing, and rational dual normalization.

This is a boundary-fiber regression certificate, NOT a global n8 proof.
"""
import sympy as s
from itertools import combinations, product

Q=s.Rational
names=('A','B','T','D','E','H','G')
ref={'A':(Q(29,24),-Q(1,2)),
     'B':(Q(29,24),Q(1,2)),
     'T':(Q(5,24),Q(5,4)),
     'D':(-Q(19,24),Q(1)),
     'E':(-Q(7,5),Q(0)),
     'H':(-Q(19,24),-Q(1)),
     'G':(Q(5,24),-Q(1))}
p={i:s.Matrix(s.symbols('p'+i+'x p'+i+'y',real=True)) for i in names}
p0={i:s.Matrix(ref[i]) for i in names}
frame={'A':(Q(1,2),-Q(1,2)),
       'B':(Q(1,2),Q(1,2)),
       'D':(-Q(1,2),Q(1,2)),
       'H':(-Q(1,2),-Q(1,2))}
circle_weight={'A':Q(31,144),'B':Q(31,144),
               'D':Q(41,144),'H':Q(41,144)}
a=s.Matrix([1,0]);b=s.Matrix([0,1]);v=lambda x:s.Matrix(x)
L=Q(1271,1728)
edges=[
 ('A','B',b,Q(31,72)),
 ('T','B',a,L),
 ('D','T',a,L),
 ('E','D',b,Q(41,48)),
 ('G','A',a,L),
 ('H','G',a,L),
 ('H','E',b,Q(41,48))
]
q0=Q(2257,576)
assert sum(circle_weight.values())==1
gaps=[n.dot(p[j]-p[i])-1 for i,j,n,w in edges]
weighted_circle=sum(
    circle_weight[i]*((p[i]+v(frame[i])).dot(p[i]+v(frame[i])))
    for i in circle_weight
)
sos=(q0+
     sum(circle_weight[i]*(p[i]-p0[i]).dot(p[i]-p0[i])
         for i in circle_weight)+
     sum(weight*g for g,(_,_,_,weight) in zip(gaps,edges)))
assert s.expand(weighted_circle-sos)==0
reference_subs={p[i][j]:p0[i][j] for i in names for j in range(2)}
assert all(s.simplify(g.subs(reference_subs))==0 for g in gaps)
assert all(s.simplify((p0[i]+v(frame[i])).dot(p0[i]+v(frame[i]))-q0)==0
           for i in circle_weight)

# Validate all 21 true pair SAT separations and 28 true square vertices.
verts={}
for i in names:
    verts[i]=[p0[i]+s.Matrix([sx*Q(1,2),sy*Q(1,2)])
              for sx,sy in product((-1,1),repeat=2)]
    assert all(vv.dot(vv)<=q0 for vv in verts[i])
for i,j in combinations(names,2):
    dif=p0[j]-p0[i]
    assert abs(dif[0])>=1 or abs(dif[1])>=1,(i,j,dif)

print("PASS: exact rational SOS identity for every seven-center tuple")
print("PASS: four anchored circle weights and seven weighted support gaps")
print("PASS: attainment by seven genuine axis-parallel unit squares at 2257/576")
print("PASS: all 21 true square pairs SAT-separated and all 28 vertices contained")

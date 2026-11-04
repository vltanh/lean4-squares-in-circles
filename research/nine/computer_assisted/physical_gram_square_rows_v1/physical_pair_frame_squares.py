"""Necessary affine rows from a square of six retained physical vectors.

For a selected SAT pair i,j the existing auxiliaries encode
C=alpha_i alpha_j+beta_i beta_j and S=alpha_i beta_j-beta_i alpha_j.
For arbitrary rational weights q, ||q0 ex+q1 ey+q2 ui+q3 vi+q4 uj+q5 vj||²>=0.
This module only expands that identity; no bounds or optimizer are imported.
"""
from fractions import Fraction as F

def selected(choices):return [tuple(pair)for pair,kind,choice in choices if kind=='sat']

def row(choices,slot,weights):
    pairs=selected(choices);assert type(slot)is int and 0<=slot<len(pairs)
    i,j=pairs[slot];assert 0<=i<j<9
    q=tuple(map(F,weights));assert len(q)==6
    x,y,a,b,c,d=q;cosine=a*c+b*d;sine=b*c-a*d;z=54+6*slot
    co={}
    def add(k,v):co[k]=co.get(k,F(0))+v
    for k,v in((18+i,-2*(x*a+y*b)),(27+i,-2*(y*a-x*b)),
            (18+j,-2*(x*c+y*d)),(27+j,-2*(y*c-x*d)),
            (z+2,-2*cosine),(z+3,-2*cosine),(z+4,-2*sine),(z+5,2*sine)):add(k,v)
    name='physical_pair_square_'+str(slot)+'_'+str(i)+'_'+str(j)+'_'+'_'.join(map(str,q))
    return tuple((k,v)for k,v in sorted(co.items())if v),sum(v*v for v in q),name

def rows(choices,parameters):
    return [row(choices,slot,q)for slot,q in parameters]

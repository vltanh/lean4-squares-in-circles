"""Optional numeric suggestions only; proof rows are always rebuilt exactly.

This source calls no solver and is not imported by the independent attachment.
It returns parameter tuples, never persisted coefficients or new proof bounds.
"""
if not __debug__:
    raise RuntimeError('Corner suggestion source requires assertions.')
from fractions import Fraction as F
from itertools import product
from math import isfinite

def suggest(point,current,context,tolerance=1e-7,denominator=65536):
    assert type(denominator)is int and denominator>0
    assert len(point)>=54 and all(isfinite(float(x))for x in point)
    assert isfinite(float(tolerance))and tolerance>=0
    context.model.validate_state(current)
    selected=[]
    for i,e,t in product(range(9),(-1,1),(-1,1)):
        px=F(round(float(point[2*i])*denominator),denominator)
        py=F(round(float(point[2*i+1])*denominator),denominator)
        bits=[]
        for frame,coordinate,sign in ((i,2*i,e),(i,2*i+1,t),(9+i,2*i+1,e),(9+i,2*i,-t)):
            fbox=tuple(map(F,current['scalar'][frame]))
            gbox=tuple(sorted(sign*F(z)for z in current['positions'][coordinate]))
            f=float(point[18+frame]);g=sign*float(point[coordinate])
            value=[float(fbox[k])*g+float(gbox[k])*f-float(fbox[k]*gbox[k])for k in(0,1)]
            bits.append(0 if value[0]>=value[1]else 1)
        parameters=(i,e,t,px,py,tuple(bits))
        coefficients,rhs,name=context.row_on_current(current,parameters)
        violation=sum(float(value)*float(point[column])for column,value in coefficients)-float(rhs)
        if violation>tolerance:selected.append((parameters,violation))
    return sorted(selected,key=lambda item:item[1],reverse=True)

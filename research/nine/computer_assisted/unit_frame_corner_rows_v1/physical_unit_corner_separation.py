"""Numerical suggestions for exact original unit-frame corner rows."""
from fractions import Fraction as F
from itertools import product
import physical_unit_corner_rows as EXACT

def violated_parameters(point,positions,scalar,tolerance=1e-9,denominator=65536):
    suggestions=[]
    for i,e,t in product(range(9),(-1,1),(-1,1)):
        px=F(round(point[2*i]*denominator),denominator);py=F(round(point[2*i+1]*denominator),denominator)
        best=None
        for aside,bside in product((0,1),repeat=2):
            parameters=i,e,t,px,py,aside,bside
            co,rhs,name=EXACT.row(positions,scalar,*parameters)
            violation=sum(float(v)*point[k]for k,v in co)-float(rhs)
            if best is None or violation>best[1]:best=parameters,violation
        if best[1]>tolerance:suggestions.append(best)
    return sorted(suggestions,key=lambda item:item[1],reverse=True)

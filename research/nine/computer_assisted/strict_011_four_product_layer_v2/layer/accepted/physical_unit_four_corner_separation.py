"""Numerical suggestions; the selected four rectangle planes remain exact."""
from fractions import Fraction as F
from itertools import product
import physical_unit_four_corner_rows as EXACT

def violated_parameters(point,positions,scalar,tolerance=1e-7,denominator=65536):
    out=[]
    for i,e,t in product(range(9),(-1,1),(-1,1)):
        px=F(round(point[2*i]*denominator),denominator);py=F(round(point[2*i+1]*denominator),denominator)
        terms=((i,2*i,e),(i,2*i+1,t),(9+i,2*i+1,e),(9+i,2*i,-t));choices=[]
        for frame,coordinate,sign in terms:
            fb=tuple(map(F,scalar[frame]));gb=tuple(sorted(sign*F(z)for z in positions[coordinate]))
            f=point[18+frame];g=sign*point[coordinate]
            values=[float(fb[k])*g+float(gb[k])*f-float(fb[k]*gb[k])for k in(0,1)]
            choices.append(0 if values[0]>=values[1]else 1)
        parameters=(i,e,t,px,py,tuple(choices));co,rhs,name=EXACT.row(positions,scalar,*parameters)
        violation=sum(float(v)*point[k]for k,v in co)-float(rhs)
        if violation>tolerance:out.append((parameters,violation))
    return sorted(out,key=lambda x:x[1],reverse=True)

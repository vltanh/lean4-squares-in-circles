"""Unit-frame corner lower planes with four independent rectangle choices."""
from fractions import Fraction as F
Q=F(1105,256)
PREFIX='physical_unit_four_corner_'

def row(positions,scalar,original,epsilon,tau,px,py,choices):
    assert len(positions)==18 and len(scalar)==36
    assert type(original)is int and 0<=original<9
    assert epsilon in(-1,1)and tau in(-1,1)
    choices=tuple(choices);assert len(choices)==4 and all(type(k)is int and k in(0,1)for k in choices)
    px,py=F(px),F(py);i=original
    co={2*i:2*px,2*i+1:2*py};rhs=Q-F(1,2)+px*px+py*py
    terms=((i,2*i,epsilon),(i,2*i+1,tau),(9+i,2*i+1,epsilon),(9+i,2*i,-tau))
    for (frame,coordinate,sign),side in zip(terms,choices):
        fl,fu=map(F,scalar[frame]);xl,xu=map(F,positions[coordinate]);assert fl<=fu and xl<=xu
        gl,gu=sorted((sign*xl,sign*xu));f0=(fl,fu)[side];g0=(gl,gu)[side]
        co[coordinate]=co.get(coordinate,F(0))+sign*f0
        co[18+frame]=co.get(18+frame,F(0))+g0;rhs+=f0*g0
    name=PREFIX+'_'.join(map(str,(original,epsilon,tau,px,py,*choices)))
    return tuple((k,v)for k,v in sorted(co.items())if v),rhs,name

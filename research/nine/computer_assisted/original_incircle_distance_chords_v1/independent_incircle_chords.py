"""Literal reconstruction only; no producer, square-root rounding or optimizer."""
from fractions import Fraction as F
PREFIX='physical_incircle_chord_'

def verify_literal(literal,differences):
    coefficients,rhs,name=literal;assert isinstance(name,str)and name.startswith(PREFIX)
    fields=name[len(PREFIX):].split('_');assert len(fields)==8
    i,j,axis,sign=map(int,fields[:4]);assert fields[:4]==list(map(str,(i,j,axis,sign)))
    assert 0<=i<j<9 and axis in(0,1)and sign in(-1,1)
    lo,hi,a,b=map(F,fields[4:]);assert -1<=lo<hi<=1 and a>=0 and b>=0
    assert a*a+lo*lo<=1 and b*b+hi*hi<=1
    box=differences[i,j];assert len(box)==2
    assert all(len(v)==2 and v[0]<=v[1]for v in box)
    dl,du=box[axis];tl,tu=box[1-axis]
    assert (dl>=0 if sign==1 else du<=0)
    assert lo<=tl<=tu<=hi
    slope=(b-a)/(hi-lo);expected=[]
    for original,sg in((i,1),(j,-1)):
        expected.extend([(2*original+axis,F(sg*sign)),(2*original+1-axis,-sg*slope)])
    expected=tuple(sorted((k,v)for k,v in expected if v))
    assert tuple(coefficients)==expected and F(rhs)==slope*lo-a
    return literal

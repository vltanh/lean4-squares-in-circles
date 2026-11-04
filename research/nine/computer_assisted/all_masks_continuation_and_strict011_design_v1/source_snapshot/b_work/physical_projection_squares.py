"""Exact squared-norm rows tying selected unit normals to center gaps."""
from fractions import Fraction as F

def selections(choices):return [(tuple(pair),tuple(ch))for pair,kind,ch in choices if kind=='sat']

def row(choices,differences,slot,weights):
    items=selections(choices);assert type(slot)is int and 0<=slot<len(items)
    (i,j),(owner,axis,sign)=items[slot];assert 0<=i<j<9 and owner in(i,j)and axis in(0,1)and sign in(-1,1)
    q=tuple(map(F,weights));assert len(q)==4
    x,y,a,b=q;co={};constant=x*x+y*y+a*a;z=54+6*slot
    def add(k,v):co[k]=co.get(k,F(0))+v
    for coordinate,w in enumerate((x,y)):
        lo,hi=map(F,differences[i,j][coordinate]);assert lo<=hi
        coefficient=-b*b*(lo+hi)-2*b*w
        add(2*j+coordinate,coefficient);add(2*i+coordinate,-coefficient)
        constant-=b*b*lo*hi
    if axis==0:
        add(18+owner,-2*a*x*sign);add(27+owner,-2*a*y*sign)
    else:
        add(27+owner,2*a*x*sign);add(18+owner,-2*a*y*sign)
    add(z,-2*a*b);add(z+1,-2*a*b)
    name='physical_projection_square_'+str(slot)+'_'+str(i)+'_'+str(j)+'_'+'_'.join(map(str,q))
    return tuple((k,v)for k,v in sorted(co.items())if v),constant,name

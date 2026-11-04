"""Independent Gram expansion with a proved upper squared-distance secant."""
from fractions import Fraction as F

def rebuild(name,choices,differences):
    p=name.split('_');assert len(p)==10 and p[:3]==['physical','projection','square']
    slot,i,j=map(int,p[3:6]);q=tuple(map(F,p[6:]));assert all(str(v)==s for v,s in zip(q,p[6:]))
    entries=[(tuple(pair),tuple(ch))for pair,kind,ch in choices if kind=='sat']
    assert 0<=slot<len(entries)and entries[slot][0]==(i,j)and 0<=i<j<9
    owner,axis,sign=entries[slot][1];assert owner in(i,j)and axis in(0,1)and sign in(-1,1)
    z=54+6*slot
    # Basis ex, ey, selected unit n, d=center_j-center_i.
    nx=((18+owner,F(sign)),)if axis==0 else((27+owner,F(-sign)),)
    ny=((27+owner,F(sign)),)if axis==0 else((18+owner,F(sign)),)
    dx=((2*j,F(1)),(2*i,F(-1)));dy=((2*j+1,F(1)),(2*i+1,F(-1)))
    gram={(0,2):nx,(1,2):ny,(0,3):dx,(1,3):dy,(2,3):((z,F(1)),(z+1,F(1)))}
    co={};rhs=q[0]**2+q[1]**2+q[2]**2
    def add(k,v):co[k]=co.get(k,F(0))+v
    for(a,b),terms in gram.items():
        for k,v in terms:add(k,-2*q[a]*q[b]*v)
    for terms,interval in zip((dx,dy),differences[i,j]):
        lo,hi=map(F,interval);assert lo<=hi
        # (d-lo)(hi-d)>=0 gives ||d||²<=sum((lo+hi)d-lo*hi).
        for k,v in terms:add(k,-q[3]**2*(lo+hi)*v)
        rhs-=q[3]**2*lo*hi
    return tuple((k,v)for k,v in sorted(co.items())if v),rhs,name

def verify_literal(row,choices,differences):
    expected=rebuild(row[2],choices,differences)
    assert tuple(row[0])==expected[0]and F(row[1])==expected[1]
    return True

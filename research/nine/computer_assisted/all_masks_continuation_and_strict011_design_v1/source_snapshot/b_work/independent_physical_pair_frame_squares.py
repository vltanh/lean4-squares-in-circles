"""Independent symbolic Gram expansion; imports no row producer/optimizer."""
from fractions import Fraction as F

def rebuild(name,choices):
    p=name.split('_');assert len(p)==12 and p[:3]==['physical','pair','square']
    slot,i,j=map(int,p[3:6]);q=tuple(map(F,p[6:]));assert all(str(v)==s for v,s in zip(q,p[6:]))
    pairs=[tuple(pair)for pair,kind,ch in choices if kind=='sat']
    assert 0<=slot<len(pairs)and pairs[slot]==(i,j)and 0<=i<j<9
    z=54+6*slot
    # Sparse symbolic off-diagonal entries of the actual six-vector Gram.
    # Basis vectors: ex, ey, ui, vi, uj, vj. Every diagonal equals one.
    entries={
      (0,2):((18+i,1),),(0,3):((27+i,-1),),
      (1,2):((27+i,1),),(1,3):((18+i,1),),
      (0,4):((18+j,1),),(0,5):((27+j,-1),),
      (1,4):((27+j,1),),(1,5):((18+j,1),),
      (2,4):((z+2,1),(z+3,1)),(3,5):((z+2,1),(z+3,1)),
      (2,5):((z+4,-1),(z+5,1)),(3,4):((z+4,1),(z+5,-1))}
    coefficients={}
    for(a,b),terms in entries.items():
        for k,v in terms:coefficients[k]=coefficients.get(k,F(0))-2*q[a]*q[b]*v
    return tuple((k,v)for k,v in sorted(coefficients.items())if v),sum(v*v for v in q),name

def verify_literal(row,choices):
    expected=rebuild(row[2],choices)
    assert tuple(row[0])==expected[0]and F(row[1])==expected[1]
    return True

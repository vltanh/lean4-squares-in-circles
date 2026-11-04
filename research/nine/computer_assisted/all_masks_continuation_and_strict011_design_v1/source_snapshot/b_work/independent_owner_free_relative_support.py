"""Independent affine expansion of all-pair relative-support consequences.

No producer, numerical library, or root approximation is imported. Product
planes are reconstructed as nonnegative rectangle-slack products, while the
distance term is the exact upper square secant. See the companion hand proof.
"""
from fractions import Fraction as F

def rebuild(name,positions,scalar,differences):
    parts=name.split('_')
    assert len(parts)==9 and parts[:2]==['owner','free']
    family=parts[2];assert family in('signed','folded')
    i,j,sign,num,den=map(int,parts[3:8]);code=parts[8]
    assert 0<=i<j<9 and sign in(-1,1) and den>0
    tau=F(num,den);assert tau>=0 and str(tau.numerator)==parts[6] and str(tau.denominator)==parts[7]
    assert len(code)==4 and set(code)<=set('01')
    assert len(positions)==18 and len(scalar)==36
    assert all(F(lo)<=F(hi)for lo,hi in tuple(positions)+tuple(scalar))
    ds=differences[i,j];assert len(ds)==2
    coefficients={};constant=F(0)
    def add(k,v):
        coefficients[k]=coefficients.get(k,F(0))+v
    # -(l+u)d+l*u is no larger than -d^2 on the closed interval.
    for axis,(lo,hi)in enumerate(ds):
        lo,hi=F(lo),F(hi);assert lo<=hi
        add(2*i+axis,lo+hi);add(2*j+axis,-lo-hi)
        constant+=lo*hi
    offset=27 if family=='signed'else 36
    terms=((18+i,18+j,1),(offset+i,offset+j,1),
           (18+i,offset+j,sign),(offset+i,18+j,-sign))
    for (x,y,sg),digit in zip(terms,code):
        xl,xu=map(F,scalar[x-18]);yl,yu=map(F,scalar[y-18])
        if sg>0:
            # xy - [(x-lx)(y-ly)] or xy - [(ux-x)(uy-y)].
            anchor_x,anchor_y=(xl,yl)if digit=='0'else(xu,yu)
            add(x,tau*anchor_y);add(y,tau*anchor_x)
            constant-=tau*anchor_x*anchor_y
        else:
            # -xy - [(ux-x)(y-ly)] or -xy - [(x-lx)(uy-y)].
            anchor_x,anchor_y=(xu,yl)if digit=='0'else(xl,yu)
            add(x,-tau*anchor_y);add(y,-tau*anchor_x)
            constant+=tau*anchor_x*anchor_y
    rhs=tau*tau-tau-constant
    return tuple((k,v)for k,v in sorted(coefficients.items())if v),rhs,name

def verify_literal(row,positions,scalar,differences):
    co,rhs,name=row
    actual=rebuild(name,positions,scalar,differences)
    assert tuple(co)==actual[0] and F(rhs)==actual[1] and name==actual[2]
    return True

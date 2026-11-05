"""Independent exact literal decoder for original-pair support chords.
Imports only Fraction. It reconstructs rectangle slack-product lower planes
without importing a producer, optimizer, square-root routine, or generator.
Input scalar and difference intervals must be independently proved for the
same current physical state by the enclosing certificate checker.
"""
from fractions import Fraction as F

PREFIX='physical_relative_support_chord_'
H=F(121,100)

def rebuild(name,scalar,differences):
    assert isinstance(name,str) and name.startswith(PREFIX)
    fields=name[len(PREFIX):].split('_')
    assert len(fields)==11
    family=fields[0];assert family in ('signed','folded')
    i,j,axis,sign,epsilon=map(int,fields[1:6])
    assert fields[1:6]==list(map(str,(i,j,axis,sign,epsilon)))
    assert 0<=i<j<9 and axis in (0,1) and sign in (-1,1) and epsilon in (-1,1)
    zl,zu,al,au=map(F,fields[6:10])
    assert fields[6:10]==list(map(str,(zl,zu,al,au)))
    code=fields[10];assert len(code)==4 and set(code)<=set('01')
    assert len(scalar)==36
    assert all(len(v)==2 and F(v[0])<=F(v[1]) for v in scalar)
    box=differences[i,j];assert len(box)==2
    assert all(len(v)==2 and F(v[0])<=F(v[1]) for v in box)
    dl,du=map(F,box[axis]);tl,tu=map(F,box[1-axis])
    assert dl>=0 if sign==1 else du<=0
    # These are the exact extrema of t/h over t in [tl,tu], h in [1,H].
    ratio_lower=min(tl,tl/H);ratio_upper=max(tu,tu/H)
    assert -1<=zl<=ratio_lower<=ratio_upper<=zu<=1
    assert al>=0 and au>=0 and al*al+zl*zl<=1 and au*au+zu*zu<=1
    if zl==zu:
        assert zl==0 and al==au==1
        m,b=F(0),F(1)
    else:
        m=(au-al)/(zu-zl);b=al-m*zl
    assert b>=0
    co={}
    def add(k,v):co[k]=co.get(k,F(0))+v
    add(2*i+axis,sign);add(2*j+axis,-sign)
    add(2*i+1-axis,-m);add(2*j+1-axis,m)
    offset=27 if family=='signed' else 36
    products=((18+i,18+j,1),(offset+i,offset+j,1),
              (18+i,offset+j,epsilon),(offset+i,18+j,-epsilon))
    K=F(0)
    for (x,y,sg),digit in zip(products,code):
        xl,xu=map(F,scalar[x-18]);yl,yu=map(F,scalar[y-18])
        if sg==1:
            # xy minus (x-xl)(y-yl), or minus (xu-x)(yu-y).
            px,py=(xl,yl) if digit=='0' else (xu,yu)
            add(x,b*py/2);add(y,b*px/2);K-=px*py
        else:
            # -xy minus (xu-x)(y-yl), or minus (x-xl)(yu-y).
            px,py=(xu,yl) if digit=='0' else (xl,yu)
            add(x,-b*py/2);add(y,-b*px/2);K+=px*py
    return tuple((k,v)for k,v in sorted(co.items())if v),-b*(1+K)/2,name

def verify_literal(literal,scalar,differences):
    co,rhs,name=literal
    expected=rebuild(name,scalar,differences)
    assert tuple(co)==expected[0] and F(rhs)==expected[1]
    return True

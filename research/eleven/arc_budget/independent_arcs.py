"""Independent rational bounds for a rectangle's occupied circle angle."""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt

if not __debug__:
    raise RuntimeError('Run without -O; proof checks use assertions.')

SCALE = 10**16

def atan_small(x, count=20):
    assert 0 <= x <= F(1, 2)
    term = x
    total = F(0)
    assert count % 2 == 0
    for k in range(count):
        total += (-1 if k % 2 else 1) * term / (2*k+1)
        term *= x*x
    return total, total+term/(2*count+1)

a,b=atan_small(F(1,5),32);c,d=atan_small(F(1,239),32)
PI=(16*a-4*d,16*b-4*c)

def atan_bound(x):
    assert 0<=x<=1
    if x<=F(1,2):return atan_small(x)
    lo,hi=atan_small((1-x)/(1+x))
    return PI[0]/4-hi,PI[1]/4-lo

@lru_cache(None)
def asin_bound(x):
    assert 0<=x<=1
    # asin(x)=2 atan(x/(1+sqrt(1-x*x))), including x=1.
    z=1-x*x
    lo=F(isqrt(z.numerator*SCALE*SCALE//z.denominator),SCALE)
    hi=lo+F(1,SCALE)
    assert lo*lo<=z<=hi*hi
    return 2*atan_bound(x/(1+hi))[0],2*atan_bound(x/(1+lo))[1]

def acos_bound(x):
    lo,hi=asin_bound(x)
    return PI[0]/2-hi,PI[1]/2-lo

def rectangle_angle_lower(xlo,xhi,ylo,yhi,radius):
    """Sum four first-quadrant intervals; boundary rays have zero measure."""
    answer=F(0)
    for sx in (1,-1):
        for sy in (1,-1):
            xl,xh=(xlo,xhi) if sx==1 else (-xhi,-xlo)
            yl,yh=(ylo,yhi) if sy==1 else (-yhi,-ylo)
            xl,xh=max(F(0),xl),min(radius,xh)
            yl,yh=max(F(0),yl),min(radius,yh)
            if xl>=xh or yl>=yh:continue
            # cos decreases and sin increases on a first quadrant.
            lower_upper=max(acos_bound(xh/radius)[1],asin_bound(yl/radius)[1])
            upper_lower=min(acos_bound(xl/radius)[0],asin_bound(yh/radius)[0])
            answer+=max(F(0),upper_lower-lower_upper)
    return answer

def box_weight_lower(alo,ahi,blo,bhi):
    # This rectangle is contained in every square with own-frame center
    # in [alo,ahi] x [blo,bhi], regardless of the frame's global rotation.
    xlo,xhi=ahi-F(1,2),alo+F(1,2)
    ylo,yhi=bhi-F(1,2),blo+F(1,2)
    if xlo>=xhi or ylo>=yhi:return F(0)
    return sum(w*rectangle_angle_lower(xlo,xhi,ylo,yhi,r)
               for w,r in [(F(6,200),F(3,10)),(F(85,200),F(3,5)),
                           (F(109,200),F(5,4))])

if __name__=='__main__':
    assert PI[0]>F('3.141592653589793238462643383279')
    assert PI[1]<F('3.141592653589793238462643383280')
    assert abs(float(rectangle_angle_lower(-1,1,-1,1,F(1)))-6.283185307179586)<1e-12
    for x in ['0','0.555','1.065']:
        z=F(x)
        print(x,float(box_weight_lower(z,z,z,z)))
    print('PASS independent rational angle primitives')

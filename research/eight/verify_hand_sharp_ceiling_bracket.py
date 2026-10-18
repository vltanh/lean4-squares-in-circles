#!/usr/bin/env python3
"""Exact rational check of eight displayed square-root brackets and two poses.

There is no square-root routine, solver, interval subdivision or sampled input.
All square-root bounds are explicit rational numbers checked by squaring.
"""
from fractions import Fraction as F

class R:
    def __init__(self,lo,hi=None):self.lo,self.hi=F(lo),F(lo if hi is None else hi)
    @staticmethod
    def coerce(v):return v if isinstance(v,R) else R(v)
    def __add__(a,b):
        b=R.coerce(b);return R(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return R(-a.hi,-a.lo)
    def __sub__(a,b):return a+-R.coerce(b)
    def __rsub__(a,b):return R.coerce(b)+-a
    def __mul__(a,b):
        b=R.coerce(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return R(min(v),max(v))
    __rmul__=__mul__
    def reciprocal(a):
        assert not a.lo<=0<=a.hi
        return R(1/a.hi,1/a.lo)
    def __truediv__(a,b):return a*R.coerce(b).reciprocal()
    def __rtruediv__(a,b):return R.coerce(b)*a.reciprocal()
    def square(a):
        return R(0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
    def abs_upper(a):return max(abs(a.lo),abs(a.hi))

DEN=10**30
QC=F('3.91553413751747532652')
Y=F('-.92065667800760613175')
Z=F('.06189741100766035970')
DATA=[
    (QC-F(2,10**16),[
        (1751549433717893721308920688242,1751549433717893721308920688243),
        (1658478860518848668734905536484,1658478860518848668734905536485),
        (1454597940959173928318723969998,1454597940959173928318723970000),
        (1902122690972247036667590000343,1902122690972247036667590000345)]),
    (QC+F(1,10**16),[
        (1751549433717893806947382904866,1751549433717893806947382904867),
        (1658478860518848759179229893487,1658478860518848759179229893488),
        (1454597940959174114853411962263,1454597940959174114853411962265),
        (1902122690972247169012577055225,1902122690972247169012577055227)])]

def main():
    c,s=F(1-Z*Z,1+Z*Z),2*Z/(1+Z*Z)
    for index,(q,pairs) in enumerate(DATA):
        x1,x2,y3,minus_x4=[R(F(a,DEN),F(b,DEN)) for a,b in pairs]
        x3=x2-3;y4=y3-2;x4=-minus_x4
        radicands=[R(q-Y*Y),R(q-(Y+2)**2),q-x3.square(),q-y4.square()]
        for root,rad in zip((x1,x2,y3,minus_x4),radicands):
            assert 0<root.lo and root.lo**2<rad.lo<=rad.hi<root.hi**2
        h1=c*x1+s*Y-2-c;h2=-s*x4+c*y4-1-s
        defect=h1.square()+h2.square()-q
        x1y=-Y/x1;x2y=-(Y+2)/x2;y4y=-x3*x2y/y3;x4y=-y4*y4y/x4
        h1y=c*x1y+s;h2y=-s*x4y+c*y4y
        h1t=-s*(x1-1)+c*Y;h2t=-c*(x4+1)-s*y4
        fy=2*(h1*h1y+h2*h2y);ft=2*(h1*h1t+h2*h2t)
        assert fy.abs_upper()<F(1,10**14) and ft.abs_upper()<F(1,10**14)
        if index==0:assert defect.lo>F(7,10**16)
        else:assert defect.hi<-F(3,10**16)
    lower=F(7,10**16)-F(1,10**14)**2/12-F(2,3)*(F(2,10**14))**2
    assert lower>0
    print('PASS: eight explicit radical brackets, each checked by exact rational squaring')
    print('PASS: lower-ceiling defect>7e-16; upper-ceiling defect<-3e-16; |Fy|,|Ft|<1e-14')
    print('PASS: the two-stage convexity lower bound is strictly positive')

if __name__=='__main__':main()

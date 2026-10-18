#!/usr/bin/env python3
"""Check the displayed finite arithmetic appendix, with no search or root solver.

Every interval has rational endpoints with denominator10^12. Integer division
and integer square roots round outward. The only domains are the nine stated
endpoint brackets, four stated rectangles, and four slider corners.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt

SCALE=10**12

class I:
    def __init__(self,lo=0,hi=None):
        if isinstance(lo,I):
            assert hi is None
            self.lo,self.hi=lo.lo,lo.hi
            return
        lo,hi=F(lo),F(lo if hi is None else hi)
        self.lo=lo.numerator*SCALE//lo.denominator
        self.hi=-((-hi.numerator*SCALE)//hi.denominator)
        assert self.lo<=self.hi
    @classmethod
    def raw(cls,lo,hi):
        x=object.__new__(cls);x.lo,x.hi=lo,hi;assert lo<=hi;return x
    @staticmethod
    def coerce(x):return x if isinstance(x,I) else I(x)
    def __add__(a,b):
        b=I.coerce(b);return I.raw(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I.raw(-a.hi,-a.lo)
    def __sub__(a,b):return a+-I.coerce(b)
    def __rsub__(a,b):return I.coerce(b)+-a
    def __mul__(a,b):
        b=I.coerce(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I.raw(min(v)//SCALE,-((-max(v))//SCALE))
    __rmul__=__mul__
    def reciprocal(a):
        assert not a.lo<=0<=a.hi
        return I.raw(SCALE*SCALE//a.hi,-((-SCALE*SCALE)//a.lo))
    def __truediv__(a,b):return a*I.coerce(b).reciprocal()
    def __rtruediv__(a,b):return I.coerce(b)*a.reciprocal()
    def __abs__(a):
        if a.lo>=0:return a
        if a.hi<=0:return -a
        return I.raw(0,max(-a.lo,a.hi))
    def sqrt(a):
        assert a.lo>=0
        lo=isqrt(a.lo*SCALE);hi=isqrt(a.hi*SCALE)
        if hi*hi<a.hi*SCALE:hi+=1
        return I.raw(lo,hi)
    def gt(a,b):
        b=F(b);assert a.lo*b.denominator>b.numerator*SCALE,(a.lo,a.hi,'>',str(b))
    def lt(a,b):
        b=F(b);assert a.hi*b.denominator<b.numerator*SCALE,(a.lo,a.hi,'<',str(b))

class J:
    def __init__(self,v,y=0,t=0):self.v,self.y,self.t=I(v),I(y),I(t)
    @staticmethod
    def coerce(x):return x if isinstance(x,J) else J(x)
    def __add__(a,b):
        b=J.coerce(b);return J(a.v+b.v,a.y+b.y,a.t+b.t)
    __radd__=__add__
    def __neg__(a):return J(-a.v,-a.y,-a.t)
    def __sub__(a,b):return a+-J.coerce(b)
    def __rsub__(a,b):return J.coerce(b)+-a
    def __mul__(a,b):
        b=J.coerce(b);return J(a.v*b.v,a.y*b.v+a.v*b.y,a.t*b.v+a.v*b.t)
    __rmul__=__mul__
    def reciprocal(a):return J(1/a.v,-a.y/(a.v*a.v),-a.t/(a.v*a.v))
    def __truediv__(a,b):return a*J.coerce(b).reciprocal()
    def __rtruediv__(a,b):return J.coerce(b)*a.reciprocal()
    def sqrt(a):
        v=a.v.sqrt();return J(v,a.y/(2*v),a.t/(2*v))

def calculus(q,y,z,root_bounds=None):
    def radical(radicand,index):
        if root_bounds is None:return radicand.sqrt()
        lo,hi=root_bounds[index]
        assert (I(lo)*I(lo)).hi<radicand.lo and radicand.hi<(I(hi)*I(hi)).lo
        return I(lo,hi)
    c=(1-z*z)/(1+z*z);s=2*z/(1+z*z)
    x1=radical(q-y*y,0);x2=radical(q-(y+2)*(y+2),1);x3=x2-3
    y3=radical(q-x3*x3,2);y4=y3-2;x4=-radical(q-y4*y4,3)
    h1=c*x1+s*y-2-c;h2=-s*x4+c*y4-1-s
    x1y=-y/x1;x1yy=-q/(x1*x1*x1)
    x2y=-(y+2)/x2;x2yy=-q/(x2*x2*x2)
    y4y=-x3*x2y/y3;y4yy=-q*x2y*x2y/(y3*y3*y3)-x3*x2yy/y3
    x4y=-y4*y4y/x4;x4yy=-q*y4y*y4y/(x4*x4*x4)-y4*y4yy/x4
    h1y=c*x1y+s;h1yy=c*x1yy;h2y=-s*x4y+c*y4y;h2yy=-s*x4yy+c*y4yy
    h1t=-s*(x1-1)+c*y;h2t=-c*(x4+1)-s*y4
    Fy=2*(h1*h1y+h2*h2y);Ft=2*(h1*h1t+h2*h2t)
    Fyy=2*(h1y*h1y+h1*h1yy+h2y*h2y+h2*h2yy)
    Fyt=2*(h1t*h1y+h1*(-s*x1y+c)+h2t*h2y+h2*(-c*x4y-s*y4y))
    Ftt=2*(h1t*h1t+h2t*h2t-h1*(h1+2)-h2*(h2+1))
    A=c/(2*x1);ab=s-c*y/x1;B=ab/(2*(y+2));tb=ab*x2/(y+2)
    D=-tb/(2*x3);ed=2*D*y3;H=-1/(2*h1);he=h2/h1;E=-s*he/(2*x4)
    W=1/(A+B+D+E+H)
    mu=[W*v for v in (A,B,D,E,H)]
    ab,tb,ed,he=[W*v for v in (ab,tb,ed,he)]
    weights=[ab,tb,tb,ed,he,W,W]
    incidence=[ab+W,ab+tb,tb+ed,ed+he,W+he]
    young=sum(((2*m+j)*(2*m+j)/(2*m) for m,j in zip(mu,incidence)),I(0))
    return locals()

def nine(q,y,z):
    q=J(q);y=J(y,1,0);z=J(z,0,(1+z*z)/2)
    c=(1-z*z)/(1+z*z);s=2*z/(1+z*z)
    x1=(q-y*y).sqrt();x2=(q-(y+2)*(y+2)).sqrt();x3=x2-3
    y3=(q-x3*x3).sqrt();y4=y3-2;x4=-(q-y4*y4).sqrt()
    h1=c*x1+s*y-2-c;h2=-s*x4+c*y4-1-s;h2t=-c*(x4+1)-s*y4
    A=c/(2*x1);ab=s-c*y/x1;B=ab/(2*(y+2));tb=ab*x2/(y+2)
    D=-tb/(2*x3);ed=2*D*y3;H=-1/(2*h1);he=h2/h1;E=-s*he/(2*x4)
    W=1/(A+B+D+E+H)
    ab,tb,ed,he=[W*v for v in (ab,tb,ed,he)]
    aux=he*c/tb-y3*x4/x3;X=tb*(y+2+aux);K=tb*(y3+aux)
    L=he*s*y4/x4;N=-he*(h1+h2t)
    return [X,ab*(1-x1+x2)-X,K,tb-K,tb*(-F(9,10)-aux),
            tb*(F(27,25)+aux),L,N-F(37,100)*W,W/2-N]

Q=I(F(7831,2000),F(9789,2500))
Z=[F(400+31*k,8000) for k in range(9)]
Y=[(-9357,-9356),(-9308,-9307),(-9259,-9258),(-9211,-9209),
   (-9162,-9161),(-9114,-9113),(-9066,-9065),(-9018,-9017),(-8971,-8969)]
Y=[(F(a,10000),F(b,10000)) for a,b in Y]
C=list(map(F,['.0345','.3633','.3211','.4102','.0760','.0425','.0238','.0371','.0549']))
D=list(map(F,['2.04','2.16','1.27','1.51','1.53','1.52','.26','.33','.35']))

def main():
    for z,(lo,hi) in zip(Z,Y):
        calculus(Q,I(lo),I(z))['Fy'].lt(-F(1,10000))
        calculus(Q,I(hi),I(z))['Fy'].gt(F(1,20000))
    full=calculus(Q,I(F(-937,1000),F(-895,1000)),I(Z[0],Z[-1]))
    full['Fyy'].gt(F(6723,1000));full['Fyy'].lt(F(8637,1000))
    full['Fyt'].gt(F(-5327,1000));full['Fyt'].lt(F(-423,100))
    h2prime=full['h2t']-full['h2y']*full['Fyt']/full['Fyy']
    h2prime.gt(F(413,1000));h2prime.lt(F(88,125))
    for k in range(4):
        a,m,b=Z[2*k:2*k+3];yl,yh=Y[2*k][0],Y[2*k+2][1]
        d=calculus(Q,I(yl,yh),I(a,b))
        curvature=d['Ftt']-d['Fyt']*d['Fyt']/d['Fyy']
        curvature.gt(F(88+2*k,100))
        d['young'].lt([F('106.2'),F('96.1'),F('88.4'),F('82.3')][k])
        for v in d['mu']:v.gt([F('.0195'),F('.0223'),F('.0250'),F('.0276')][k])
        for v in d['weights']:v.gt(0);v.lt([F('.8418'),F('.8340'),F('.8263'),F('.8188')][k])
        sum(d['weights'],I(0)).lt(F(26,5))
        for i,v in enumerate(nine(Q,I(*Y[2*k+1]),I(m))):v.v.gt(C[i])
        yp=-d['Fyt']/d['Fyy']
        for i,v in enumerate(nine(Q,I(yl,yh),I(a,b))):abs(v.t+v.y*yp).lt(D[i])
    for c,d in zip(C,D):assert c-F(31,4000)*d>F(9,500)
    endpoint_ranges=[(F('-1.44369'),F('-1.44356'),F('3.91619')),
                     (F('-1.40827'),F('-1.40806'),F('3.91703'))]
    for i,k in enumerate((0,8)):
        d=calculus(Q,I(*Y[k]),I(Z[k]));lo,hi,bound=endpoint_ranges[i]
        d['h2'].gt(lo);d['h2'].lt(hi)
        (d['h1']*d['h1']+d['h2']*d['h2']).lt(bound)
        if i==0:d['Ft'].lt(-F(3211,100000))
        else:d['Ft'].gt(F(1071,20000))
    point_bounds=[(F(a,10**8),F(b,10**8)) for a,b in
        [(175156947,175156948),(165843168,165843169),(145454269,145454271),(190209787,190209788)]]
    p=calculus(I(F(7831,2000)),I(F(-4603,5000)),I(F(619,10000)),point_bounds)
    (p['h1']*p['h1']+p['h2']*p['h2']-F(7831,2000)).gt(F(1,8000))
    abs(p['Fy']).lt(F(1,2000));abs(p['Ft']).lt(F(1,4000))
    assert F(1,8000)-F(1,2000)**2/12-F(2,3)*(F(1,2000)+F(1,4000))**2==F(5981,48000000)>0
    # The reference norm claim uses the single full rectangle, not subdivision.
    d=dict(full);half=F(1,2)
    coordinate_bounds={'x1':('1.7428','1.7649'),'x2':('1.6414','1.6691'),
        'y3':('1.4387','1.4643'),'x4':('-1.9049','-1.8974'),
        'h1':('-1.4263','-1.3198'),'h2':('-1.5316','-1.3202')}
    for name,(lo,hi) in coordinate_bounds.items():
        d[name].gt(F(lo));d[name].lt(F(hi));d[name]=I(F(lo),F(hi))
    d['x3']=d['x2']-3;d['y4']=d['y3']-2
    pA=(d['x1']-half,d['y']+half);pB=(d['x2']-half,d['y']+F(3,2))
    pD=(d['x3']+half,d['y3']-half);pE=(d['x4']+half,d['y4']+half)
    pH=((d['h1']+half)*d['c']-(d['h2']+half)*d['s'],(d['h1']+half)*d['s']+(d['h2']+half)*d['c'])
    norm2=lambda p:abs(p[0])*abs(p[0])+abs(p[1])*abs(p[1])
    for height,eta in product((F(29,50),F(7,5)),(F(-1,2),F(37,100))):
        pT=(d['x2']-F(3,2),I(height));pG=(pH[0]+d['c']-eta*d['s'],pH[1]+d['s']+eta*d['c'])
        poses=dict(A=pA,B=pB,D=pD,E=pE,H=pH,T=pT,G=pG)
        for a,b in [('A','B'),('T','B'),('D','T'),('E','D'),('G','A'),('H','G'),('H','E')]:
            norm2((poses[b][0]-poses[a][0],poses[b][1]-poses[a][1])).lt(3)
        norm2(pT).lt(3);norm2(pG).lt(3)
    assert F(9,500)-130*F(1,10000)==F(1,200)
    print('PASS: all displayed nine endpoint, four rectangle, nine owner, radius and norm comparisons')
    print('PASS: integer arithmetic at denominator10^12; no search, root solver or adaptive subdivision')

if __name__=='__main__':main()

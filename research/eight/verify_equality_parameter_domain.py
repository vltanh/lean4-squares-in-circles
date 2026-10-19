"""Fixed rational arithmetic for COMPLETE_EQUALITY_PARAMETER_DOMAIN.md.

No optimizer, sampled pose or variable subdivision is used. Square roots
are bounded only by the eight integer brackets printed in the proof.
"""
from fractions import Fraction as F
import json
from pathlib import Path

checks = []

def check(name, reserve):
    reserve = F(reserve)
    assert reserve > 0, (name, reserve)
    checks.append({'name': name, 'positive_reserve': str(reserve)})

class I:
    def __init__(self, a, b=None):
        if isinstance(a, I):
            self.a, self.b = a.a, a.b
            return
        self.a = F(str(a))
        self.b = self.a if b is None else F(str(b))
        assert self.a <= self.b
    def __add__(a, b):
        b = I(b)
        return I(a.a+b.a, a.b+b.b)
    __radd__ = __add__
    def __neg__(a):
        return I(-a.b, -a.a)
    def __sub__(a, b):
        return a + -I(b)
    def __rsub__(a, b):
        return I(b) + -a
    def __mul__(a, b):
        b = I(b)
        p = [x*y for x in (a.a, a.b) for y in (b.a, b.b)]
        return I(min(p), max(p))
    __rmul__ = __mul__
    def __truediv__(a, b):
        b = I(b)
        assert not b.a <= 0 <= b.b
        return a * I(1/b.b, 1/b.a)
    def __rtruediv__(a, b):
        return I(b) / a
    def __pow__(a, n):
        if n == 2:
            return I(0 if a.a <= 0 <= a.b else min(a.a*a.a, a.b*a.b),
                     max(a.a*a.a, a.b*a.b))
        r = I(1)
        for _ in range(n):
            r = r*a
        return r
    def sqrt_bracket(a, name, lo, hi):
        lo, hi = F(lo, 10**12), F(hi, 10**12)
        assert lo > 0
        check(name+' lower square', a.a-lo*lo)
        check(name+' upper square', hi*hi-a.b)
        return I(lo, hi)
    def bound(a, name, lo, hi):
        check(name+' lower', a.a-F(str(lo)))
        check(name+' upper', F(str(hi))-a.b)
    def lower(a, name, lo):
        check(name, a.a-F(str(lo)))
    def upper(a, name, hi):
        check(name, F(str(hi))-a.b)

q = I('3.9155341', '3.9155342')
y0, z0 = I('-.92065'), I('.0619')
x1 = (q-y0*y0).sqrt_bracket('test x1', 1751552933113, 1751552961661)
x2 = (q-(y0+2)**2).sqrt_bracket('test x2', 1658474503120, 1658474533269)
x3 = x2-3
y3 = (q-x3*x3).sqrt_bracket('test y3', 1454593909385, 1454593971565)
y4 = y3-2
x4 = -(q-y4*y4).sqrt_bracket('test -x4', 1902121525118, 1902121569235)
c0 = (1-z0*z0)/(1+z0*z0)
s0 = 2*z0/(1+z0*z0)
h1 = c0*x1+s0*y0-2-c0
h2 = -s0*x4+c0*y4-1-s0
x1y = -y0/x1
x2y = -(y0+2)/x2
y4y = -x3*x2y/y3
x4y = -y4*y4y/x4
h1y = c0*x1y+s0
h2y = -s0*x4y+c0*y4y
h1t = -s0*(x1-1)+c0*y0
h2t = -c0*(x4+1)-s0*y4
Fy = 2*(h1*h1y+h2*h2y)
Ft = 2*(h1*h1t+h2*h2t)
Fy.bound('test Fy', '-.000027', '.000027')
Ft.bound('test Ft', '-.000010', '.000010')
check('tilt displacement below .00005', F('.00005')-F(4,3)*F('.000037'))
check('position displacement below .0000545', F('.0000545')-F('.000027')/6-F(4,3)*F('.000037'))
(c0+I('-.00005','.00005')).bound('stationary cosine', '.99231','.99242')
(s0+I('-.00005','.00005')).bound('stationary sine', '.12327','.12338')
(y0+I('-.0000545','.0000545')).bound('stationary y', '-.92071','-.92059')
check('stationary tilt below .125', F('.125')-2*F('.0619')-F('.00005'))

ys = I('-.92071','-.92059')
c, s = I('.99231','.99242'), I('.12327','.12338')
x1 = (q-ys*ys).sqrt_bracket('stationary x1', 1751521394645, 1751584497506)
x2 = (q-(ys+2)**2).sqrt_bracket('stationary x2', 1658435453040, 1658513580258)
x3 = x2-3
y3 = (q-x3*x3).sqrt_bracket('stationary y3', 1454557893773, 1454629982384)
y4 = y3-2
x4 = -(q-y4*y4).sqrt_bracket('stationary -x4', 1902111197789, 1902131894451)
h1 = c*x1+s*ys-2-c
h2 = -s*x4+c*y4-1-s
A = (x1-I('.5'),ys+I('.5'))
B = (x2-I('.5'),ys+I('1.5'))
D = (x3+I('.5'),y3-I('.5'))
E = (x4+I('.5'),y4+I('.5'))
H = ((h1+I('.5'))*c-(h2+I('.5'))*s,
     (h1+I('.5'))*s+(h2+I('.5'))*c)
xc = x2-I('1.5')
for name, value, lo, hi in [
 ('x1',x1,'1.75152','1.75159'),('x2',x2,'1.65843','1.65852'),
 ('y3',y3,'1.45455','1.45464'),('-x4',-x4,'1.90211','1.90214'),
 ('h1',h1,'-1.36797','-1.36748'),('h2',h2,'-1.43022','-1.42976'),
 ('H_x',H[0],'-.74678','-.74604'),('H_y',H[1],'-1.03026','-1.02954')]:
    value.bound(name,lo,hi)
xc.bound('T own horizontal center',0,'.5')
(h1+I('1.5')).bound('G own first center',0,'.5')
(h1+1).upper('H top first coefficient',0)
(h2+1).upper('H top second coefficient',0)
(ys+1).lower('B bottom',0)
(y3-1).lower('D bottom',0)
(x1-x2).lower('right column gap',0)
(-x4-(3-x2)).lower('left column gap',0)
(s*(h1+2)-c/12).upper('G largest top','-.004')
(c*(h1+1)+s/12).lower('G smallest left','-.355')
(x4+1).upper('E right edge','-.90211')
(-s*A[0]+c*A[1]).upper('A in negative-f halfplane',0)
(H[0]*A[1]-H[1]*A[0]).lower('H to A determinant',0)
B[0].lower('B in first quadrant x',0)
B[1].lower('B in first quadrant y',0)
D[0].upper('D in second quadrant x',0)
D[1].lower('D in second quadrant y',0)
(H[1]-H[0]).upper('H off diagonal y=x',0)
(H[1]+H[0]).upper('H off diagonal y=-x',0)
check('central square fits automatically', q.a-F(121,72))

# Whole five-parameter box. All interval arithmetic below uses only
# monotone rational trigonometric endpoint bounds and the printed data.
x, yy = I('.139','.141'), I('-.001','.001')
z, eta = I('1.349','1.351'), I('-.321','-.319')
a, b = I('.099'), I('.101')
cl, ch = (1-b*b)/(1+b*b), (1-a*a)/(1+a*a)
sl, sh = 2*a/(1+a*a), 2*b/(1+b*b)
C, S = I(cl.a,ch.b), I(sl.a,sh.b)
(c*S-s*C).lower('central angle strictly above outer tilt',0)
(C-S).lower('central frame below quarter diagonal',0)
G = (H[0]+c-eta*s,H[1]+s+eta*c)
T = (xc,z)
W0 = (1+C+S)/2
Wt = (1+c*C+s*S+c*S-s*C)/2
rows = [
 ('A',A,(I(1),I(0)),W0,'.020'),
 ('B',B,(C,S),W0,'.020'),
 ('D',D,(-S,C),W0,'.036'),
 ('E',E,(I(-1),I(0)),W0,'.450'),
 ('H',H,(-C,-S),Wt,'.031'),
 ('G',G,(s,-c),Wt,'.192'),
 ('T',T,(I(0),I(1)),W0,'.257')]
for name,P,n,W,lo in rows:
    ((P[0]-x)*n[0]+(P[1]-yy)*n[1]-W).lower('central separation '+name,lo)
(C*x+S*yy).bound('central own first center','-.139','.139')
(-S*x+C*yy).bound('central own second center','-.030','.030')
(z-I(F(7,12))).lower('T strict core avoidance',0)
(h2+I('.5')+eta).upper('G strict core avoidance',-F(7,12))
(q-(xc+I('.5'))**2-(z+I('.5'))**2).lower('T disk reserve','.055')
(q-(h1+2)**2-(-h2-eta)**2).lower('G disk reserve','.448')

result = {'status':'PASS','strict_comparisons':len(checks),
          'method':'Eight supplied radical brackets and fixed rational interval comparisons; no subdivision.',
          'checks':checks}
path=Path(__file__).with_name('equality_parameter_domain_arithmetic.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','strict_comparisons':len(checks)}))

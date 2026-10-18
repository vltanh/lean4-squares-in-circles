"""Independent exact reconstruction of the two nontrivial C/M scalar bounds.

The formulas are transcribed from the hand manuscript, not imported from
its JavaScript checker. All operations below use Python Fraction.
"""
from fractions import Fraction as F
from math import factorial, comb
import json

def add(*ps):
    out = [F(0)] * max(map(len, ps))
    for p in ps:
        for i, v in enumerate(p):
            out[i] += v
    return out

def scale(p, a):
    return [F(a)*v for v in p]

def mul(p, q):
    out = [F(0)]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out

def trig(parity, degree):
    out = [F(0)]*(degree+1)
    for j in range(parity, degree+1, 2):
        out[j] = F((-1)**((j-parity)//2), factorial(j))
    return out

def bern(p, lo, hi):
    lo, hi = F(lo), F(hi)
    n = len(p)-1
    powers = [sum(p[i]*comb(i,j)*lo**(i-j)*(hi-lo)**j
                  for i in range(j,n+1)) for j in range(n+1)]
    return [sum(powers[j]*F(comb(k,j),comb(n,j))
                for j in range(k+1)) for k in range(n+1)]

Q, p, q, g = map(F, ['3.9156','1.489593','1.580219','1.077372'])
cM, gam = F('-2.143075'), F('.9005')
KF = F('.09')-cM+(p+q+g)/2
T = add([KF-gam,F(1)], scale(trig(1,7),g-F('.09')),
        scale(trig(0,8),F('-.09')))
V = add([p*p+q*q+g*g],scale(trig(1,9),2*g*p),
        scale(trig(0,10),-2*g*q))
P = add(mul(T,T),scale(V,-Q))
bp, bt = bern(P,'.7','1.53'), bern(T,'.7','1.53')
nums = [930757,865698,798263,729205,659251,589108,519469,
        451021,384457,320478,259803,203178,151376,105205,
        65512,33176,9117]
assert len(bp)==17 and len(bt)==9
checks = []
def check(name, gap):
    assert gap > 0, (name,str(gap))
    checks.append({'name':name,'strict_gap':str(gap)})
for i,(b,n) in enumerate(zip(bp,nums)):
    check(f'P coefficient {i}',b-F(n,10**6))
for i,b in enumerate(bt):
    check(f'T coefficient {i}',b-4)

# These integers are the displayed decimal endpoint bounds in Section 6.
rows = [
    (56464,56465,82533,82534,179424,374711),
    (64421,64422,76484,76485,177007,353482),
    (71735,71736,69670,69671,174969,338316),
    (78332,78333,62160,62161,173272,327185),
    (84147,84148,54030,54031,171878,318896),
    (86240,86241,50622,50623,171398,316201),
    (88195,88196,47132,47133,170961,313805),
    (90010,90011,43568,43569,170563,311680),
    (91680,91681,39933,39934,170204,309802),
    (93203,93204,36235,36236,169882,308152),
]
bnums = [32188,28895,23320,15480,16819,12424,7672,2563,-2891]
dnums = [55193,46704,34899,22276,30005,23091,16401,9851,3183]
rows = [[F(n,10**5) for n in row] for row in rows]
for i,(a,b) in enumerate(zip(rows,rows[1:])):
    sl,sh,cl,ch,zu,nl = a
    SL,SH,CL,CH,ZU,NL = b
    B = (1+ch**2)*(1-zu)+F(13,6)*CL
    denominator = SH**3 if B>=0 else sl**3
    D = F('.09')*min(sl+cl,SL+CL)+g*B/denominator \
        -F('1.978788')*q*q*g*g*ch**2/(sl**4*NL**3)
    check(f'curvature B {i}',B-F(bnums[i],10**5))
    check(f'curvature D {i}',D-F(dnums[i],10**5))
    check(f'curvature exceeds .03 {i}',D-F('.03'))
    check(f'curvature B sign {i}',B if i<8 else -B)

sl,sh,cl,ch,rl,rh,nl,nh = map(F,[
    '.881957806','.881957807','.471328364','.471328365',
    '1.978787507','1.978787508','3.138070988','3.138070991'])
Flo = F('1.08')-F('.09')*(sh+ch-1)-cM+(p+q+g)/2 \
      +g/sh+F(13,12)*g*cl/sh-rh*nh
zl,zh = rl*(p+g/sh)/nh,rh*(p+g/sl)/nl
yl,yh = cl*(zl-1)-F(13,12),ch*(zh-1)-F(13,12)
fpl = 1+F('.09')*(sl-ch)+g*yl/sl**2
fph = 1+F('.09')*(sh-cl)+g*yh/sh**2
check('test value greater than .9006',Flo-F('.9006'))
check('derivative lower greater than -.0003',fpl+F('.0003'))
check('derivative upper less than .0003',F('.0003')-fph)
check('strong convexity lower exceeds target',
      F('.9006')-F('.0003')**2/F('.06')-gam)
print(json.dumps({'status':'PASS','independent_comparisons':len(checks),
                  'polynomial_comparisons':26,
                  'curvature_comparisons':36,
                  'test_point_comparisons':4,'checks':checks},indent=2))

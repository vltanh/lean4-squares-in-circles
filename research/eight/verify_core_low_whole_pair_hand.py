"""Exact arithmetic in CORE_LOW_WHOLE_PAIR_HAND_PROOF.md.

The five fixed polynomials and their entire intervals are specified in
the hand proof.  This script only expands their Bernstein coefficients
and replays the displayed rational comparisons.  There is no search,
optimization, sampling, or recursive subdivision.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

Q = F(9789, 2500)
beta, K, g, mu, q = map(F, ('.18', '7.506931', '1.077372', '.403875', '1.089065'))
ac, Rhi, gamma = F(7, 12), F('1.979'), F('.91')
a0lo, a0hi = F('1.4145'), F('1.415')
a1lo, a1hi = F('1.2987'), F('1.2988')
Elo, Ehi = F('.306'), F('.307')
pi_lo = F('3.1415')
checks = []


def check(name, lhs, rhs=F(0)):
    assert lhs > rhs, (name, lhs, rhs)
    checks.append({'name': name, 'strict_margin': str(lhs-rhs)})


def trig(degree, sine):
    return [F((-1)**((k-int(sine))//2), factorial(k))
            if k % 2 == int(sine) else F(0)
            for k in range(degree+1)]


def ev(p, x):
    return sum(c*x**i for i, c in enumerate(p))


def add(p, r):
    out = [F(0)]*max(len(p), len(r))
    for i, v in enumerate(p):
        out[i] += v
    for i, v in enumerate(r):
        out[i] += v
    return out


def scale(p, v):
    return [v*c for c in p]


def mul(p, r):
    out = [F(0)]*(len(p)+len(r)-1)
    for i, v in enumerate(p):
        for j, w in enumerate(r):
            out[i+j] += v*w
    return out


def bernstein(p, lo, hi):
    n = len(p)-1
    local = [sum(p[j]*comb(j, k)*lo**(j-k)*(hi-lo)**k
                 for j in range(k, n+1)) for k in range(n+1)]
    return [sum(local[j]*F(comb(k, j), comb(n, j))
                for j in range(k+1)) for k in range(n+1)]


def circle_at_cut(a):
    return (a+F(1, 2))**2+(a/4+F(1, 2))**2


check('a0 lower', Q-F(1, 4), (a0lo+F(1, 2))**2)
check('a0 upper', (a0hi+F(1, 2))**2, Q-F(1, 4))
check('a1 lower', Q, circle_at_cut(a1lo))
check('a1 upper', circle_at_cut(a1hi), Q)
check('R upper', Rhi**2, Q)
check('core diagonal lower', F(2), F('1.414')**2)
check('core diagonal upper', F('1.44')**2, F(2))
cc_lo = F(6707, 12000)
check('core marker upper', F('.786'), K*ac-(K-g)*cc_lo)
check('core marker slope', K, g)
check('low marker increasing', q, mu)
check('low marker cut lower', (mu+q/4)*a1lo-mu*a0hi, Elo)
check('low marker cut upper', Ehi, (mu+q/4)*a1hi-mu*a0lo)
check('low transverse bound', F('.325'), a1hi/4)
check('low radial slope upper', F('.46'), (a1lo/4+F(1, 2))/(a1lo+F(1, 2)))
check('global charge bound', F('1.42')**2, F(2))
check('pi over two upper', F('1.571'), F(355, 226))
check('pi over four upper', F('.786'), F(355, 452))
check('all relative angles exceed minus .3', F('.76')-F('.786')-F('.25'), -F('.3'))
check('large angle cost', F('2.05')-F('.786')-F('.31')-F('.0378'), gamma)
check('low/core secondary impossible', F('.5')-F('.325'), F('1.5')/12)
check('core/low secondary nonpositive angle impossible', F(1), F('.56')+F('.325'))
check('core/low primary nonpositive cosine impossible', F(1), ac+F('.325'))
check('low/core primary small angle impossible', F(0), F('.915')-F('1.058')*(1-F('.3')**2/2)+F('.06')*F('.3'))
check('negative core secondary lies on side', F('.5'), a0hi-1)

# Endpoint trigonometry.  The higher degrees are still fixed alternating
# Taylor sums, needed only at the three angles close to two radians.
trig_rows = [
    ('1.75', '.98', None, '-.185', None),
    ('1.9', '.946', None, '-.324', '-.32'),
    ('2', '.909', None, '-.417', '-.41'),
    ('2.05', '.887', None, '-.462', None),
    ('.6', '.564', None, None, None),
    ('1.2', None, '.933', None, '.363'),
]
for xx, sl, sh, cl, ch in trig_rows:
    x = F(xx)
    if sl is not None:
        check(f'sin {xx} lower', ev(trig(11, True), x), F(sl))
    if sh is not None:
        check(f'sin {xx} upper', F(sh), ev(trig(9, True), x))
    if cl is not None:
        check(f'cos {xx} lower', ev(trig(10, False), x), F(cl))
    if ch is not None:
        check(f'cos {xx} upper', F(ch), ev(trig(8, False), x))

# Core source, negative primary separator.
Bforced = F(1, 2)-(F(1, 12)+F('.915')*F('.185'))/F('.98')
check('negative-target core-primary forced B', Bforced)
check('negative-target core-primary short interval', pi_lo/2-F('.786')-F('.0378')+(q-mu)*Bforced, gamma)
check('negative-target core-primary tail', F('1.75')-F('.786')-F('.0378'), gamma)
check('positive-target core-primary angle barrier', F(0), F(1, 12)+F('.915')/3-F('.9')/2)
core_primary_constant = -F('.0378')-F('.786')+mu*F('1.41')+(mu+q)/2-F('.06')
assert core_primary_constant == F(345707, 800000)
for xx, nup in [('2', '.84'), ('2.05', '.889')]:
    x, n = F(xx), F(nup)
    nsq_upper = mu*mu+q*q+1-2*(mu*ev(trig(10, False), x)+q*ev(trig(11, True), x))
    check(f'core-primary norm at {xx}', n*n, nsq_upper)
check('positive-target core-primary first interval', F('1.9')+F('.32')+core_primary_constant-Rhi*F('.84'), gamma)
check('positive-target core-primary second interval', F(2)+F('.41')+core_primary_constant-Rhi*F('.889'), gamma)

# Five whole-interval polynomial positivity assertions.
A, C = (g+beta)/2, (g-beta)/2
S5, S7, S9 = (trig(n, True) for n in (5, 7, 9))
C6, C8 = (trig(n, False) for n in (6, 8))
U = list(map(F, ('.405', '1.086', '-.037', '-.048')))
check('positive norm upper polynomial', F('1.086')-F('.037')*F('1.2')-F('.048')*F('1.2')**2)

Pminus = add([A-gamma, F(1)], add(scale(C6, C), scale(S5, -(g*a0hi-C))))
Nupper = add([mu*mu+q*q+g*g], scale(add(scale(S9, mu), scale(C6, -q)), 2*g))
Pnorm = add(mul(U, U), scale(Nupper, -1))
Pfull = add([(g+beta+mu+q)/2+mu*a0lo-gamma, F(1)],
            add(scale(S7, g-beta/2), scale(C8, -beta/2)))
Pfull = add(Pfull, scale(U, -Rhi))
Pcut = add([A-Ehi-gamma, F(1)],
           add(scale(C6, C+g*a1lo/4), scale(S5, -(g*a1hi-C))))
Pmid = mul([beta/2-Ehi+g/2-gamma, F(1)], S7)
Pmid = add(Pmid, scale(mul(S5, S5), -beta/2))
Pmid = add(Pmid, scale(mul(S5, C8), -beta/2))
Pmid = add(Pmid, scale(C6, g*F(13, 12)))
Pmid[0] -= g*(a1hi-F(1, 2))

fixed = [
    ('negative-target axial support', Pminus, F(0), F('1.571'),
     [167371,147526,90767,31856,13144,70276,208525]),
    ('positive-target radical upper', Pnorm, F(0), F('1.2'),
     [773,2028,2327,2200,2095,2300,2842,3356,2969,178]),
    ('positive-target whole circle cost', Pfull, F(0), F('1.2'),
     [144942,120668,102475,88215,75631,62718,48109,31369,13139]),
    ('positive-target low cut cost', Pcut, F('1.2'), F('1.571'),
     [14274,8519,5400,5338,8710,15824,26898]),
    ('low-source middle interval', Pmid, F('.6'), F('1.571'),
     [38649,23617,13318,7443,5538,7011,11130,17038,23760,30225,35283,37730,36330,29843]),
]
polynomial_rows = []
for name, polynomial, lo, hi, nums in fixed:
    bb = bernstein(polynomial, lo, hi)
    assert len(bb) == len(nums)
    for k, (value, num) in enumerate(zip(bb, nums)):
        assert num > 0
        check(f'{name}: Bernstein coefficient {k}', value, F(num, 10**6))
    polynomial_rows.append({'name': name, 'interval': [str(lo), str(hi)],
                            'degree': len(polynomial)-1,
                            'coefficient_lower_numerators_over_1000000': nums,
                            'exact_coefficients': [str(v) for v in bb]})

# Endpoint supports and their monotonic continuations.
check('negative-target secondary B positive', g*a1lo-C)
check('negative-target secondary B upper', F('.952'), g*a1hi-C)
check('negative-target secondary D positive', C-g*a1hi/4)
check('negative-target secondary D upper', F('.1'), C-g*a1lo/4)
check('negative-target secondary derivative', F(1), F('.952')**2+F('.1')**2)
check('negative-target secondary endpoint cost', g+Elo-g*F('.325'), gamma)
check('positive-target cut support at 1.2', q-g*F('.363'), F('.46')*(mu+g*F('.933')))
check('positive-target cut support monotonicity', F('.887')-F('.46')*F('.363'))
check('positive-target secondary quadrant-II cosine sign', C, g*a1hi/4)

# Low source, negative primary separator, small-angle interval.
check('core corner support curvature', K-3, F('4.5'))
check('core corner support loss', F('.005')*24*(K-3), (3*F('.6')-g)**2)
N3up = F('3.574')
check('small-angle source norm upper', N3up*N3up, (mu+3)**2+q*q)
Slow = mu*a0lo+(mu+3+q)/2-Rhi*N3up
small_rows = []
for x in (F('.3'), F('.6')):
    ca, sl, sh = ev(C6, x), ev(S7, x), ev(S5, x)
    f1 = x+(3+beta)/2+Slow+g/2+F('3.16')*ca-F('.09')*sh-F('.005')
    f2 = x+(3+beta)/2+Slow-g/2+F('3.16')*ca+F('2.91')*sl-F('.005')
    for which, value in [('minus sine', f1), ('plus sine', f2)]:
        check(f'low-source small interval {which} at {x}', value, gamma)
        small_rows.append({'x': str(x), 'branch': which, 'cost_lower': str(value)})
check('small-angle envelope concavity', F('3.16')*(1-F('.6')**2/2), F('.09')*F('.6'))
check('variable multiplier forces low cut', q, (mu+g/F('.564'))*F('.46'))
check('variable multiplier core support', K, g/F('.564'))
check('middle-interval positive sine coefficient', F('.6')+beta/2-Ehi+g/2-gamma)
check('quadrant-II continuation derivative', 1-beta/2-g*(F('.8')*F('.462')+F(1,12))/F('.887')**2)

# Positive core target on its corner: two coarse intervals.
check('corner target excludes first quadrant', F(1), F('.915'))
check('corner target angle exceeds 1.9', F('.5')+F('.946')-F('.324')/12, a0hi)
a_first = F('.5')+F('.909')-F('.417')/12
a_second = F('.5')+F('.887')-F('.462')/12
check('corner target first transverse cap', (a_first+F('.5'))**2+F('.64')**2, Q)
check('corner target second transverse cap', (a_second+F('.5'))**2+F('.73')**2, Q)
check('corner target first cost', F('1.9')-F('.0378')-F('.786')-q*F('.14'), gamma)
check('corner target second cost', F(2)-F('.0378')-F('.786')-q*F('.23'), gamma)

out = {'status': 'PASS', 'strict_comparisons': len(checks),
       'fixed_polynomial_rows': polynomial_rows,
       'small_angle_endpoint_rows': small_rows, 'comparisons': checks}
Path(__file__).with_name('core_low_whole_pair_hand_arithmetic.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'strict_comparisons': len(checks),
                  'polynomial_rows': len(fixed),
                  'positive_bernstein_coefficients': sum(len(r[-1]) for r in fixed),
                  'small_angle_endpoint_rows': small_rows}, indent=2))

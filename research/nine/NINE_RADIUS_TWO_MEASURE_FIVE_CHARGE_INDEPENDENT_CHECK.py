"""Independent exact evaluation of the SAME five fixed mass checks.

This uses the separately reviewed alternative inverse-trigonometric evaluator:
40-term exact rational Machin bounds and two half-angle reductions followed by
32-term atan bounds at scale 2^80. It does not import any other repo file.

The five coordinate boxes and their selected circles are exactly those of
NINE_RADIUS_TWO_MEASURE_FIVE_CHARGE_CHECK.py. This audits the same measure
witness and fixed obligations; it is not an additional certificate packet.
Continuous minima, branch coverage, atom boundaries and the derivative/Taylor
bounds are proved in the three analytic sources and their separate reviews.
"""
from math import isqrt
from fractions import Fraction as Fr
from functools import lru_cache
import json

S=1<<80
B=5*(1<<24)
WEIGHTS=((1,10,714),(1,1,3858),(11,10,2424),(27,20,1709))
ORIGINAL_SCALE=1<<56
ORIGINAL_PI_LO=226375608064909912
ORIGINAL_PI_HI=226375608064910268

def ceildiv(n,d):return (n+d-1)//d

def arctan_fraction(x):
    z=sum(((-1)**k*x**(2*k+1)/Fr(2*k+1) for k in range(40)),Fr(0))
    return z,z+x**81/81
p5=arctan_fraction(Fr(1,5));p239=arctan_fraction(Fr(1,239))
pilo=16*p5[0]-4*p239[1];pihi=16*p5[1]-4*p239[0]
assert Fr(ORIGINAL_PI_LO,ORIGINAL_SCALE)<pilo<pihi<Fr(ORIGINAL_PI_HI,ORIGINAL_SCALE)
PL=(pilo*S).__floor__();PH=(pihi*S).__ceil__()

@lru_cache(None)
def atansmall(z):
    assert 0<=z<=S//2
    square=(z*z//S,ceildiv(z*z,S))
    power=(z,z);acc=[0,0]
    for j in range(32):
        term=(power[0]//(2*j+1),ceildiv(power[1],2*j+1))
        if j&1:acc[0]-=term[1];acc[1]-=term[0]
        else:acc[0]+=term[0];acc[1]+=term[1]
        power=(power[0]*square[0]//S,ceildiv(power[1]*square[1],S))
    acc[1]+=ceildiv(power[1],65)
    return tuple(acc)

@lru_cache(None)
def arcsin(n,d):
    if n<=0:return (0,0)
    if n>=d:return (PL//2,ceildiv(PH,2))
    # Enclose q=t/(1+sqrt(1-t^2)) using exact rational radicands.
    rad=d*d-n*n
    rootlo=isqrt(rad*S*S)//d
    roothi=ceildiv(isqrt(rad*S*S)+1,d)
    qlo=n*S*S//(d*(S+roothi))
    qhi=ceildiv(n*S*S,d*(S+rootlo))
    # Halve arctan once more. q/(1+sqrt(1+q^2))<=sqrt(2)-1<1/2.
    rlo=isqrt(S*S+qlo*qlo)
    rhi=isqrt(S*S+qhi*qhi)+1
    vlo=qlo*S//(S+rhi)
    vhi=ceildiv(qhi*S,S+rlo)
    assert vhi<S//2
    return 4*atansmall(vlo)[0],4*atansmall(vhi)[1]

def angle(x,rn,rd):return arcsin(x*rd,B*rn)
def arccos(x,rn,rd):
    lo,hi=angle(x,rn,rd)
    return PL//2-hi,ceildiv(PH,2)-lo

def arc(box,rn,rd):
    al,ah,bl,bh=box;xx=(ah-B,al);yy=(bh-B,bl);ans=0
    for reflection_x in [False,True]:
        xl,xh=((-xx[1],-xx[0]) if reflection_x else xx)
        xl=max(xl,0)
        if xl>=xh:continue
        for reflection_y in [False,True]:
            yl,yh=((-yy[1],-yy[0]) if reflection_y else yy)
            yl=max(yl,0)
            if yl>=yh:continue
            low=max(arccos(xh,rn,rd)[1],angle(yl,rn,rd)[1])
            high=min(arccos(xl,rn,rd)[0],angle(yh,rn,rd)[0])
            ans+=max(high-low,0)
    return ans


def verify():
    critical = Fr(9 * 2424**2 + 11 * 714**2, 10 * (2424**2 - 714**2))
    assert critical == Fr(324943, 298110)
    left = (927 * B // 1000, ceildiv(928 * B, 1000), B // 2, B // 2)
    right = (critical.numerator * B // critical.denominator,
             ceildiv(critical.numerator * B, critical.denominator), B // 2, B // 2)
    b0 = B // 2
    a0 = isqrt(4 * B * B - b0 * b0)
    bl, bh = 13 * B // 12, ceildiv(13 * B, 12)
    tangent = (isqrt(4 * B * B - bh * bh),
               isqrt(4 * B * B - bl * bl) + 1, bl, bh)
    diag = isqrt(2 * B * B)
    fixed = [
        ('line_left', left, WEIGHTS[:2], 1000),
        ('line_right', right, WEIGHTS[:3], 1000),
        ('outer_left', (a0, a0 + 1, b0, b0), WEIGHTS[1:], 1005),
        ('outer_tangent', tangent, WEIGHTS[1:], 1005),
        ('outer_diagonal', (diag, diag + 1, diag, diag + 1), WEIGHTS[1:], 1005),
    ]
    assert [list(row[1]) for row in fixed] == [
        [77762396, 77846283, 41943040, 41943040],
        [91436699, 91436700, 41943040, 41943040],
        [162444695, 162444696, 41943040, 41943040],
        [141028166, 141028167, 90876586, 90876587],
        [118632832, 118632833, 118632832, 118632833],
    ]
    rows = []
    for name, box, circles, target in fixed:
        al, ah, bl, bh = box
        atom = 292 if ah < B and bh < B else 0
        score = sum(weight * arc(box, rn, rd) for rn, rd, weight in circles)
        margin = score - (target - atom) * 2 * PH
        assert margin > 0, (name, margin)
        rows.append({'name': name, 'box': list(box), 'origin_atom': bool(atom),
                     'target': [target, 1000], 'margin_integer': margin})
    result = {
        'same_fixed_mass_checks': 5,
        'independent_scale': S,
        'coordinate_denominator': B,
        'original_pi_enclosure_independently_verified': True,
        'rows': rows,
    }
    print(json.dumps(result, sort_keys=True), flush=True)
    return result


if __name__ == '__main__':
    verify()

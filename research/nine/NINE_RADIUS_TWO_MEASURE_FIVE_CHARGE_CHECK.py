"""Five fixed mass checks for the uniform radius-two measure theorem.

The complete continuous cover is proved by the three analytic replacement
sources and assembled in NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.
This self-contained checker has no adaptive subdivisions, empty-domain tests,
float arithmetic, external certificate input or imports of the old checker.

It contains exactly two line and three outer-curve mass checks, the single
outer derivative enclosure, and explicit rational Taylor/endpoint identities.
The original 208-charge checker remains a historical independent alternative.
Status: accepted after full analytic-source and exact-arithmetic reviews;
see the source's root and separate C6 reviews and the five-point assembly.
"""
from functools import lru_cache
from math import isqrt, gcd
import json

Q=1<<56
B=5*(1<<24)
WEIGHTS=((1,10,714),(1,1,3858),(11,10,2424),(27,20,1709))
ATOM=292

def up(n,d):
    return -((-n)//d)

@lru_cache(None)
def atan_small(x):
    assert 0<=x<=Q//2
    xxlo=x*x//Q;xxhi=up(x*x,Q)
    pl=ph=x;lo=hi=0
    for k in range(16):
        tl=pl//(2*k+1);th=up(ph,2*k+1)
        if k%2:lo-=th;hi-=tl
        else:lo+=tl;hi+=th
        pl=pl*xxlo//Q;ph=up(ph*xxhi,Q)
    # Sixteen terms end in a negative term; the next positive term bounds
    # the alternating remainder.  pl,ph now enclose x^33.
    hi+=up(ph,33)
    return lo,hi

def atan_base_fraction(n,d):
    return atan_small(n*Q//d)[0],atan_small(up(n*Q,d))[1]

A5=atan_base_fraction(1,5);A239=atan_base_fraction(1,239)
PI_LO=16*A5[0]-4*A239[1]
PI_HI=16*A5[1]-4*A239[0]
assert 3*Q<PI_LO<PI_HI<4*Q

@lru_cache(None)
def atan_fixed(x):
    assert 0<=x<=Q
    if x<=Q//2:return atan_small(x)
    vl=(Q-x)*Q//(Q+x);vh=up((Q-x)*Q,Q+x)
    al=atan_small(vl)[0];ah=atan_small(vh)[1]
    return PI_LO//4-ah,up(PI_HI,4)-al

@lru_cache(None)
def asin_fraction(n,d):
    assert d>0
    if n<=0:return 0,0
    if n>=d:return PI_LO//2,up(PI_HI,2)
    tl=n*Q//d;th=up(n*Q,d)
    sl2=max(0,Q-up(th*th,Q));sh2=max(0,Q-tl*tl//Q)
    sl=isqrt(sl2*Q);sh=isqrt(sh2*Q)+1
    ql=tl*Q//(Q+sh);qh=min(Q,up(th*Q,Q+sl))
    return 2*atan_fixed(ql)[0],2*atan_fixed(qh)[1]

def asin_coord(x,rn,rd):
    n=x*rd;d=B*rn;g=gcd(n,d)
    return asin_fraction(n//g,d//g)

def acos_coord(x,rn,rd):
    lo,hi=asin_coord(x,rn,rd)
    return PI_LO//2-hi,up(PI_HI,2)-lo

def rect_arc_lower(xlo,xhi,ylo,yhi,rn,rd):
    total=0
    for sx in (1,-1):
        xl=max(0,xlo if sx==1 else -xhi)
        xh=xhi if sx==1 else -xlo
        if xh<=xl:continue
        for sy in (1,-1):
            yl=max(0,ylo if sy==1 else -yhi)
            yh=yhi if sy==1 else -ylo
            if yh<=yl:continue
            upper_lo=min(acos_coord(xl,rn,rd)[0],asin_coord(yh,rn,rd)[0])
            lower_hi=max(acos_coord(xh,rn,rd)[1],asin_coord(yl,rn,rd)[1])
            total+=max(0,upper_lo-lower_hi)
    return total

from fractions import Fraction as F

def verify_line():
    from fractions import Fraction as F
    H = lambda a: 3858 ** 2 * (a - F(9, 10)) * (F(11, 10) - a) - 714 ** 2 * (1 - a * a)
    assert H(F(927, 1000)) == F(-68424471, 31250) < 0
    assert H(F(928, 1000)) == F(14285817, 15625) > 0
    a_star = F(9 * 2424 ** 2 + 11 * 714 ** 2, 10 * (2424 ** 2 - 714 ** 2))
    assert a_star == F(324943, 298110)
    assert F(1) < a_star < F(11, 10)
    fixed = [('left', 927 * B // 1000, up(928 * B, 1000), WEIGHTS[:2]), ('right', a_star.numerator * B // a_star.denominator, up(a_star.numerator * B, a_star.denominator), WEIGHTS[:3])]
    rows = []
    for name, al, ah, weights in fixed:
        bl = bh = B // 2
        origin = ah < B and bh < B
        score = sum((w * rect_arc_lower(ah - B, al, bh - B, bl, rn, rd) for rn, rd, w in weights))
        margin = score - (1000 - ATOM * origin) * 2 * PI_HI
        assert margin > 0, (name, margin)
        rows.append({'name': name, 'box': [al, ah, bl, bh], 'circle_radii': [[rn, rd] for rn, rd, _ in weights], 'origin_atom': origin, 'margin_integer': margin})
    assert rows[0]['margin_integer'] == 1153182092959159440
    assert rows[1]['margin_integer'] == 2475502032000671400
    result = {'charged_fixed_boxes': 2, 'scale': Q, 'coordinate_denominator': B, 'pi_lower_integer': PI_LO, 'pi_upper_integer': PI_HI, 'right_critical_point': [a_star.numerator, a_star.denominator], 'rows': rows}
    return result

def verify_outer():
    from fractions import Fraction as F
    b = F(13, 12)
    w = b - 1
    a0, a1 = (F(1681, 1000), F(1682, 1000))
    t10, t11 = (F(731, 1000), F(733, 1000))
    t20, t21 = (F(863, 1000), F(864, 1000))
    v10, v11 = (F(996, 1000), F(997, 1000))
    v20, v21 = (F(1096, 1000), F(1097, 1000))
    u0, u1 = (F(805, 1000), F(806, 1000))
    v30, v31 = (F(1347, 1000), F(1348, 1000))
    for rad, lo, hi in [(4 - b * b, a0, a1), (1 - w * w, v10, v11), (F(121, 100) - w * w, v20, v21), (F(729, 400) - b * b, u0, u1), (F(729, 400) - w * w, v30, v31)]:
        assert 0 < lo < hi and lo * lo < rad < hi * hi
    assert t10 * t10 < 1 - (a1 - 1) ** 2
    assert 1 - (a0 - 1) ** 2 < t11 * t11
    assert t20 * t20 < F(121, 100) - (a1 - 1) ** 2
    assert F(121, 100) - (a0 - 1) ** 2 < t21 * t21
    derivative_lo = 3858 * (b / (a1 * t11) - 1 / v10) + 2424 * (b / (a1 * t21) - 1 / v20) + 1709 * (1 / u1 - 1 / v30)
    derivative_hi = 3858 * (b / (a0 * t10) - 1 / v11) + 2424 * (b / (a0 * t20) - 1 / v21) + 1709 * (1 / u0 - 1 / v31)
    assert -40 < derivative_lo < derivative_hi < 0
    assert derivative_lo == F(-1254291053647768750, 34246309814693847)
    assert derivative_hi == F(-798076820624315593050, 62929379411568326209)
    assert PI_LO > 3 * Q
    assert F(4800, 19683) - F(250, 2197) - F(1, 8) == F(585083, 115316136) > 0
    assert F(1709, 16000) * F(7, 22) - F(1, 30) == F(689, 1056000) > 0
    assert F(201, 200) - F(1, 1500) == 1 + F(13, 3000)
    bb = B // 2
    aa = isqrt(4 * B * B - bb * bb)
    bl = 13 * B // 12
    bh = up(13 * B, 12)
    middle = (isqrt(4 * B * B - bh * bh), isqrt(4 * B * B - bl * bl) + 1, bl, bh)
    diagonal = isqrt(2 * B * B)
    boxes = [('left', (aa, aa + 1, bb, bb)), ('tangent', middle), ('diagonal', (diagonal, diagonal + 1, diagonal, diagonal + 1))]
    rows = []
    for name, box in boxes:
        al, ah, bl, bh = box
        score = sum((ww * rect_arc_lower(ah - B, al, bh - B, bl, rn, rd) for rn, rd, ww in WEIGHTS[1:]))
        margin = score - 1005 * 2 * PI_HI
        assert margin > 0, (name, box, margin)
        rows.append({'name': name, 'box': list(box), 'margin_integer': margin})
    assert [row['margin_integer'] for row in rows] == [2486115696770948576, 1716983502928824028, 336341375099883104]
    result = {'charged_fixed_boxes': 3, 'fixed_derivative_enclosures': 1, 'charge_target': [201, 200], 'uniform_outer_charge_exceeds': [3013, 3000], 'scale': Q, 'coordinate_denominator': B, 'derivative_raw_lower': [derivative_lo.numerator, derivative_lo.denominator], 'derivative_raw_upper': [derivative_hi.numerator, derivative_hi.denominator], 'rows': rows}
    return result

def verify_rectangles():
    lower = [(F(9, 10), F(223, 200), F(64180522657, 38400000000000)), (F(9, 11), F(191, 200), F(729120878539, 422400000000000)), (F(10, 11), F(227, 200), F(880201511023, 422400000000000)), (F(21, 22), F(63, 50), F(203016009, 137500000000)), (F(2, 3), F(18, 25), F(1063804, 146484375)), (F(7, 9), F(89, 100), F(2229221653, 3600000000000)), (F(20, 27), F(83, 100), F(29765234213, 10800000000000)), (F(22, 27), F(19, 20), F(4363109, 3456000000)), (F(8, 9), F(109, 100), F(6858681353, 3600000000000))]
    upper = [(F(1, 10), F(1, 9), F(119, 10935)), (F(7, 20), F(9, 25), F(139, 62500)), (F(1, 5), F(21, 100), F(16913, 2000000)), (F(2, 11), F(19, 100), F(464551, 66000000)), (F(7, 22), F(13, 40), F(4633, 4224000))]
    for z, t, reserve in lower:
        assert 0 < t <= F(63, 50) < F(3, 2)
        assert z - (t - t ** 3 / 6 + t ** 5 / 120) == reserve > 0
    for z, t, reserve in upper:
        assert 0 < t <= F(63, 50)
        assert t - t ** 3 / 6 - z == reserve > 0
    w0, w1, w2, w3 = (F(n, 1000) for n in (714, 3858, 2424, 1709))
    corner = [F(292, 1000) + w0 / 4 - (w1 + w2) / 4 + (w1 * F(223, 200) + w2 * F(191, 200)) * F(7, 22), (w1 - w2) / 4 - w1 / 27 + w2 * F(11, 10) * F(7, 22), w0 / 6 - w2 / 4 + (w1 * F(223, 200) + w2 * F(418, 200)) * F(7, 44), -(w2 + w3) / 4 + (w1 * (F(223, 200) + F(1, 10)) + w2 * (F(191, 200) + F(63, 50)) + w3 * (F(18, 25) + F(89, 100))) * F(7, 44)]
    numer1 = -w1 * F(57, 100) + w2 * F(189, 200) + w3 * F(89, 50)
    numer2 = -w1 * F(18, 25) - w2 * F(13, 20) + w3 * F(109, 50)
    assert numer1 == F(78341, 25000) > 0
    assert numer2 == -F(31387, 50000) < 0
    middle = [(w1 - w3) / 4 + numer1 * F(7, 44), (w1 + w2 - w3) / 4 + numer2 / 6]
    reserves = [x - 1 for x in corner + middle]
    assert reserves == [F(11613, 2200000), F(5761, 90000), F(14681, 4400000), F(2423, 550000), F(19681, 550000), F(2897, 75000)]
    assert all((x > 0 for x in reserves))
    assert 1 - 2 * F(1, 10) ** 2 == F(49, 50) > F(9, 10)
    assert F(121, 100) - F(21, 20) ** 2 > F(1, 100)
    assert F(729, 400) - F(21, 20) ** 2 > F(1, 100)
    assert 400 + 49 < 484
    assert 400 + 49 < 729 and 484 + 16 < 729 < 400 + 484
    assert F(8, 9) ** 2 + F(7, 27) ** 2 == F(625, 729) < 1
    assert 2 * F(8, 9) ** 2 > 1
    result = {'lower_sine_identities': len(lower), 'upper_sine_identities': len(upper), 'whole_region_mass_reserves': [[x.numerator, x.denominator] for x in reserves], 'replaced_corner_charge_checks': 14, 'replaced_middle_charge_checks': 2, 'replaced_corner_empty_tests': 3, 'new_interval_charge_checks': 0}
    return result

def verify():
    assert ATOM + sum(w for _, _, w in WEIGHTS) == 8997 < 9000
    assert ATOM + 714 == 1006 > 1000
    assert 3 * Q < PI_LO < PI_HI and 7 * PI_HI < 22 * Q
    # The original whole middle-strip proof, retained unchanged.
    x = F(47, 100)
    assert F(5, 11) - (x - x**3 / 6 + x**5 / 120) == F(21887804923, 13200000000000) > 0
    assert F(3858, 6000) + F(2424, 1000) * F(47, 100) * F(7, 22) - 1 == F(189, 34375) > 0
    line = verify_line()
    outer = verify_outer()
    rectangles = verify_rectangles()
    assert line['charged_fixed_boxes'] + outer['charged_fixed_boxes'] == 5
    assert outer['fixed_derivative_enclosures'] == 1
    result = {
        'weight_total': [8997, 1000],
        'charged_fixed_boxes': 5,
        'fixed_derivative_enclosures': 1,
        'adaptive_splits': 0,
        'empty_domain_tests': 0,
        'coordinate_denominator': B,
        'angular_scale': Q,
        'line': line,
        'outer': outer,
        'rectangle_rational_identities': rectangles,
    }
    print(json.dumps(result, sort_keys=True), flush=True)
    return result


if __name__ == '__main__':
    verify()

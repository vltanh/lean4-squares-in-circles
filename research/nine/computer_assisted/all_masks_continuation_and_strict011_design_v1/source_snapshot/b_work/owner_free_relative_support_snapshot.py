#!/usr/bin/env python3
"""Exact owner-free original-pair rows; no optimizer or producer imports.

Physical premise: the two original unit squares have disjoint interiors.
Inputs must be proved intervals for the same original center/frame variables.
See OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md for the complete implication.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt

VERSION='owner_free_signed_folded_relative_support_v1'
TAUS=(F(1),F(9,8),F(6,5))


def root_interval(value,bits=48):
    value=F(value);assert value>=0
    denominator=1<<bits
    numerator=isqrt((value.numerator<<(2*bits))//value.denominator)
    lower=F(numerator,denominator)
    return lower,lower if lower*lower==value else F(numerator+1,denominator)


def support_radius_lower(first,second):
    """Exact lower bound for (1+cos(delta)+abs(sin(delta)))/2.

    Both original slope intervals lie in [-1,1]. The angular difference is
    monotone in both slopes; on either side of zero the cosine-plus-sine
    function has its minimum at an endpoint of its interval.
    """
    a,b=map(F,first);c,d=map(F,second)
    assert -1<=a<=b<=1 and -1<=c<=d<=1
    if max(a,c)<=min(b,d):return F(1)
    values=[]
    for t,u in ((a,d),(b,c)):
        numerator=1+t*u+abs(t-u)
        lower,upper=root_interval((1+t*t)*(1+u*u))
        assert numerator>=0 and lower>0
        values.append(numerator/upper)
    return max(F(1),(1+min(values))/2)


def signed_product_lower_planes(x,y,x_bounds,y_bounds,sign):
    """The two exact affine lower planes for sign*x*y on a rectangle."""
    xl,xu=map(F,x_bounds);yl,yu=map(F,y_bounds)
    assert xl<=xu and yl<=yu and sign in (-1,1)
    if sign==1:
        return ((((x,yl),(y,xl)),-xl*yl),(((x,yu),(y,xu)),-xu*yu))
    return ((((x,-yl),(y,-xu)),xu*yl),(((x,-yu),(y,-xl)),xl*yu))


def relative_support_rows(positions,scalar,*,differences=None,taus=TAUS,families=('signed','folded')):
    """Return exact necessary rows for all 36 pairs, with no SAT selection.

    positions has 18 proved center intervals. scalar has the 36 proved
    intervals for alpha[0:9], beta[0:9], absbeta[0:9], inset[0:9]. Optional
    differences maps pairs (i,j) to two independently proved intervals for
    center_j-center_i. If omitted, coordinate interval differences are used.
    Every returned row is (coefficients, rhs, name) with coefficients for the
    existing shared variables only. No auxiliary products are introduced.
    """
    positions=tuple(tuple(map(F,p))for p in positions)
    scalar=tuple(tuple(map(F,p))for p in scalar)
    assert len(positions)==18 and len(scalar)==36
    assert all(l<=u for l,u in positions+scalar)
    assert all(F(t)>=0 for t in taus)
    result=[]
    for i in range(9):
        for j in range(i+1,9):
            pair=(i,j)
            dr=tuple((positions[2*j+k][0]-positions[2*i+k][1],positions[2*j+k][1]-positions[2*i+k][0])for k in (0,1)) if differences is None else tuple(tuple(map(F,p))for p in differences[pair])
            assert len(dr)==2 and all(l<=u for l,u in dr)
            secant_constant=sum(l*u for l,u in dr)
            negative_secant={2*i+k:l+u for k,(l,u)in enumerate(dr)}
            negative_secant.update({2*j+k:-l-u for k,(l,u)in enumerate(dr)})
            for family in families:
                assert family in ('signed','folded')
                offset=27 if family=='signed' else 36
                ai,aj,bi,bj=18+i,18+j,offset+i,offset+j
                for sine_sign in (-1,1):
                    terms=((ai,aj,1),(bi,bj,1),(ai,bj,sine_sign),(bi,aj,-sine_sign))
                    planes=[signed_product_lower_planes(x,y,scalar[x-18],scalar[y-18],sign)for x,y,sign in terms]
                    for tau in map(F,taus):
                        for choices in product((0,1),repeat=4):
                            coefficients=dict(negative_secant);constant=F(0)
                            for alternatives,choice in zip(planes,choices):
                                entries,shift=alternatives[choice];constant+=shift
                                for k,value in entries:coefficients[k]=coefficients.get(k,F(0))+tau*value
                            rhs=tau*tau-tau-tau*constant-secant_constant
                            row=tuple(sorted((k,v)for k,v in coefficients.items()if v))
                            code=''.join(map(str,choices))
                            name=f'owner_free_{family}_{i}_{j}_{sine_sign}_{tau.numerator}_{tau.denominator}_{code}'
                            result.append((row,rhs,name))
    return result


def interval_radius_rows(positions,angles,*,differences=None):
    """Necessary secant rows using the exact inherited orientation radius."""
    result=[]
    for i in range(9):
        for j in range(i+1,9):
            dr=tuple((positions[2*j+k][0]-positions[2*i+k][1],positions[2*j+k][1]-positions[2*i+k][0])for k in (0,1))if differences is None else differences[(i,j)]
            h=support_radius_lower(angles[i],angles[j])
            row=[];constant=F(0)
            for k,(lower,upper)in enumerate(dr):
                lower,upper=F(lower),F(upper);assert lower<=upper
                row.extend(((2*i+k,lower+upper),(2*j+k,-lower-upper)));constant+=lower*upper
            result.append((tuple((k,v)for k,v in row if v),-h*h-constant,f'owner_free_interval_radius_{i}_{j}'))
    return result

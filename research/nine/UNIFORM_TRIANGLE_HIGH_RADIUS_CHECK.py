#!/usr/bin/env python3
"""Exact identity checks for NEGATIVE_TRIANGLE_UPPER_LEFT_UNIFORM_HIGH_RADIUS.md.

Requires SymPy. There are no pose samples, floating-point proof inputs,
Bernstein tables, external solver certificates, or Lean/CI invocations.
This verifies algebra; it does not constitute independent geometric review.
"""
from __future__ import annotations
import sympy as S


def equal(lhs: S.Expr, rhs: S.Expr, label: str) -> None:
    if S.cancel(lhs-rhs) != 0:
        raise AssertionError(label)


def on_unit_circle(expr: S.Expr, u: S.Symbol, v: S.Symbol, label: str) -> None:
    _, remainder = S.div(S.expand(expr), u*u+v*v-1, v)
    if S.expand(remainder) != 0:
        raise AssertionError(label)


def main() -> None:
    R = S.Rational
    a,b,u,v,r = S.symbols('a b u v r', real=True)
    pressure = a*a+b*b-a-b-(a*u+b*v)/2+(r-R(1,2))*(b*u-a*v)
    A0 = 1+(u-v)/2+u*v
    B0 = 1+(u+v)/2-u*u
    on_unit_circle(pressure.subs(r,u)-(a*a+b*b-a*A0-b*B0), u,v, 'r=u pressure')
    on_unit_circle(A0*A0+B0*B0-(R(5,2)+u-u*u+2*u*v),u,v,'r=u coefficient norm')
    C1,C2 = 1+(u+v)/2,1+(v-u)/2
    equal(pressure.subs(r,1),a*a+b*b-a*C1-b*C2,'r=1 pressure')
    on_unit_circle(C1*C1+C2*C2-(R(5,2)+2*v),u,v,'r=1 coefficient norm')

    rho,m,tau = S.symbols('rho m tau', positive=True)
    c,s = (1-m*m)/(1+m*m),2*m/(1+m*m)
    ratio = 1+c*(1-rho)/(s*rho)
    endpoint = S.factor(ratio.subs(m,rho))
    equal(S.diff(ratio,m),-(1-rho)*(1+1/m**2)/(2*rho),'ratio decreases in m')
    equal(S.diff(endpoint,rho),(rho-1)*(rho*rho+rho+2)/(2*rho**3),'endpoint derivative')
    equal(endpoint.subs(rho,R(5,9)),R(337,225),'endpoint ratio')
    equal(endpoint-rho,(1-rho)*(1+rho*rho)/(2*rho*rho),'positive endpoint difference')
    equal(1-1/(c+s*rho),s*(rho-m)/(c+s*rho),'tau comparison')
    equal(1-m*(s+c/rho),(1-m*m)*(rho-m)/(rho*(1+m*m)),'key coefficient comparison')
    equal(s/(1+c),m,'half-angle identity 1')
    equal(s*s/(2*(1+c)),m*m/(1+m*m),'half-angle identity 2')

    aa = ratio*b
    x = aa-1
    L,h = x*s+b*c,-x*c+b*s
    equal(L,b*(s+c/rho)-s,'L identity')
    equal(h-x,-(1+c)*(x-b*m),'h-x identity')
    equal((L+tau)**2+(h+1)**2-(aa*aa+b*b),2*(h-x)+2*L*tau+tau*tau,'corner radius difference')
    e = rho-m
    bracket = x-b*m-L*m*e-m*m*e*e/(1+m*m)
    positive_remainder = b*e*(1-m*(s+c/rho))+m*m*e*(2-e)/(1+m*m)
    equal(bracket-(aa-b*rho-1),positive_remainder,'whole-domain bracket remainder')

    J = S.factor((endpoint*endpoint+1)/(endpoint-rho)**2)
    equal(J,(rho**4+2*rho**3+2*rho*rho-2*rho+1)/((1-rho)**2*(1+rho*rho)),'J identity')
    equal(S.diff(J,rho),4*rho*rho*(rho**3+rho*rho-rho+3)/((1-rho)**3*(1+rho*rho)**2),'J derivative')
    equal(J.subs(rho,R(5,9)),R(1549,424),'J endpoint')

    q0,Q = R(6241,1600),R(1105,256)
    reserves = {
        'r<=u pressure': (q0-R(15,4))/2,
        'a>8/5': q0*R(49,74)-R(64,25),
        'small lower-g corner': q0-R(725,196),
        'T radius': R(9,4)-(Q-R(11,5)),
        'J comparison': q0-R(1549,424),
        'b<4/5': R(16,25)*(1+R(61,25)**2)-Q,
        'perpendicular corner': q0-R(841,225),
        'high pressure squared': R(49,64)-R(81,106),
        'v>13/15 squared': R(81,106)-R(169,225),
        'u<1/2 squared': R(1,4)-R(25,106),
        'delta0>6/7 squared': R(81,106)-R(36,49),
    }
    expected = {
        'r<=u pressure': R(241,3200),
        'a>8/5': R(541,23680),
        'small lower-g corner': R(15809,78400),
        'T radius': R(171,1280),
        'J comparison': R(20973,84800),
        'b<4/5': R(535591,4000000),
        'perpendicular corner': R(469,2880),
        'high pressure squared': R(5,3392),
    }
    for label, value in reserves.items():
        assert value > 0, label
        if label in expected:
            assert value == expected[label], label
        print(f'{label}: {value} > 0')
    equal(R(2,15)**2+R(3,10)**2,R(97,900),'perpendicular Cauchy constant')
    equal(1+(1-R(5,9))/R(5,9)**2,R(61,25),'perpendicular ratio')
    print('PASS: all exact identities, derivative formulas and rational reserves.')
    print('No independent geometric/dependency review or Lean compilation is claimed.')


if __name__ == '__main__':
    main()

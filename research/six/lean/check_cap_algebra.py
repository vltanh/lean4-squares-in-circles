#!/usr/bin/env python3
"""Exact algebra sanity checks for the new cap proof bodies.

This script neither parses Lean nor executes its compiler/kernel. It checks
polynomial identities and rational margins used in CapBounds, CapSupport,
PiercingPolynomial, CapGeometry, CapPiercing and OwnEastExclusion. Passing is
NOT acceptance of those Lean proof bodies or of the unrestricted n=6 theorem.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp


def main(output: Path | None = None) -> dict:
    Q = sp.Rational
    A, B, a, b, c, s, t, h, k, r, R, p, q = sp.symbols('A B a b c s t h k r R p q')
    q0 = Q(142559, 50000)
    rows = []

    def zero(name, expr):
        residual = sp.expand(expr)
        if residual != 0:
            raise AssertionError((name, residual))
        rows.append({'name': name, 'result': 'PASS', 'exact_residual': '0'})

    def positive(name, expr):
        expr = sp.cancel(expr)
        if not bool(expr > 0):
            raise AssertionError((name, expr))
        rows.append({'name': name, 'result': 'PASS', 'exact_positive_margin': str(expr)})

    zero('disk Cauchy identity',
         (A*c+B*s)**2+(A*s-B*c)**2-(A*A+B*B)*(c*c+s*s))
    zero('corner supporting line from squared distance',
         2*(a*(A-a)+b*(B-b))+(A-a)**2+(B-b)**2-(A*A+B*B-a*a-b*b))
    zero('corner support slope decomposition',
         a*(A*c+B*s-a*c-b*s)-c*(a*(A-a)+b*(B-b))+(b*c-a*s)*(B-b))
    zero('cap low-branch gap',
         k-t/2-(k*c-s/2)-(k*(1-c)-(t-s)/2))
    zero('cap low-branch Taylor substitution',
         k-t/2-(k*(1-t*t/5)-(t-t**3/6)/2)-t*t*(k/5-t/12))
    zero('cap high-branch Taylor substitution',
         r-Q(1,2)-t/2-(R-(1-t*t/2)-(t-t**3/6))
         -(r+Q(1,2)-R+t*(Q(1,2)-t/2-t*t/6)))
    positive('pi squared below ten', 10-Q(22,7)**2)
    positive('R0 above three halves squared', q0-Q(3,2)**2)
    positive('R0 below 1689/1000 squared', Q(1689,1000)**2-q0)
    positive('cap switch sine exceeds 29/100', 1-Q(29,100)*2*Q(1689,1000))
    positive('sin(2/5) cubic lower bound exceeds one third', Q(2,5)-Q(2,5)**3/6-Q(1,3))
    positive('low-branch tilt coefficient', (Q(111,100)-Q(1,2))/5-Q(2,5)/12)
    zero('high-branch coefficient endpoint', Q(1,2)-Q(2,5)/2-Q(2,5)**2/6-Q(41,150))
    positive('high-branch tilt reserve', Q(111,100)+Q(1,2)-Q(1689,1000)+Q(29,100)*Q(41,150))
    positive('cap at two fifths below core',
             Q(3,2)-Q(1113,1000)-(Q(1689,1000)-(1-Q(2,5)**2/2)-(Q(2,5)-Q(2,5)**3/6)))
    positive('first cap branch at quarter below half',
             Q(1,2)-(Q(1113,1000)-Q(1,2)-(Q(1,4)-Q(1,4)**3/6)/2))
    positive('second cap branch at quarter below half',
             Q(1,2)-(Q(1689,1000)-(1-Q(1,4)**2/2)-(Q(1,4)-Q(1,4)**3/6)))
    H = h+Q(1,2)
    V = 1-H*s
    zero('piercing polynomial factorization',
         (h+1+V*s)**2+V*V-(h+1)**2-1
         -s*(1+(1-H-H*H)*s-2*H*s*s+H*H*s**3))
    positive('piercing H plus H squared bound', Q(12,5)-Q(9,8)-Q(9,8)**2)
    positive('piercing bracket uniform lower bound', 1-Q(7,5)*Q(2,5)-2*Q(9,8)*Q(4,25))
    positive('piercing polynomial baseline above Q0', (Q(77,200)+1)**2+1-q0)
    positive('piercing transverse failure forces positive b', Q(1,2)-Q(9,8)*Q(2,5))
    x, y = a*c-b*s, a*s+b*c
    zero('oriented square first local coordinate',
         c*(p-x)+s*(q-y)-(p*c+q*s-a)+a*(c*c+s*s-1))
    zero('oriented square second local coordinate',
         -s*(p-x)+c*(q-y)-(-p*s+q*c-b)+b*(c*c+s*s-1))
    zero('cap minimizing vertex first coordinate',
         x-c/2-s/2-(a*c-b*s-(c+s)/2))
    zero('reflected local X', p*c+q*(-s)-a-(p*c+(-q)*s-a))
    zero('reflected local Y', -p*(-s)+q*c+b+(-p*s+(-q)*c-b))
    zero('reflection preserves disk square', p*p+(-q)**2-(p*p+q*q))
    positive('deep cap excludes nonpositive primary coordinate',
             Q(177,200)-Q(1113,1000)*Q(2,5))
    positive('disk coordinate sum below twelve fifths', Q(12,5)**2-2*q0)
    zero('sorted-frame linear form decomposition',
         (A+B)*(c+s)-2*(A*c+B*s)-(B-A)*(c-s))
    positive('nonprimary cap height below core', Q(77,200)-Q(3,10))
    positive('piercing normal lower margin',
             Q(177,200)*Q(23,25)-(Q(1113,1000)-Q(1,2)))
    positive('piercing height ceiling', Q(5,8)-(Q(1113,1000)-Q(1,2)))
    positive('secondary separators coarse margin', 1-Q(117,250)-2*Q(23,200))
    positive('sqrt2 over two exceeds seven tenths squared', Q(1,2)-Q(7,10)**2)
    zero('first-octant sine lower line',
         9*(s*s-Q(49,9)*(1-c)**2)-(1-c)*(58*c-40)-9*(c*c+s*s-1))
    positive('first-octant coefficient at c lower bound', 58*Q(7,10)-40)
    positive('OWN east strict reserve coefficient', Q(7,3)*(Q(9,10)-Q(613,1000))-Q(613,1000))
    zero('OWN positive angle comparison',
         (a-Q(1,2))*c+b*s+(c+s)/2-(a*c+(Q(9,10)-a)*s)
         -(a+b-Q(2,5))*s)
    zero('OWN negative angle comparison',
         (a-Q(1,2))*c-b*s+(c+s)/2-(a*c+(Q(9,10)-a)*s)
         -(a-b-Q(2,5))*s)
    zero('strict-boundary OWN witness remains equality', r-Q(1,2)-(r-1)-Q(1,2))
    zero('strict-boundary cap witness remains equality',
         r-((r-Q(1,2))+Q(1,2)))

    report = {
        'scope': 'exact algebra sanity only; NOT Lean compilation or kernel acceptance',
        'sympy_version': sp.__version__,
        'checks': rows,
        'passed': len(rows),
        'lean_compilation_performed': False,
        'unrestricted_n6_theorem_proved': False,
    }
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    main(args.json)

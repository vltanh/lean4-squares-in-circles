#!/usr/bin/env python3
"""Exact symbolic checks of the draft's polynomial certificates.

This is a development sanity check with Sympy and rational arithmetic. It does
not parse Lean, run tactics, or establish Lean kernel acceptance.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp


def main(output: Path | None = None) -> dict:
    h, s, d, x, y, z, k = sp.symbols('h s d x y z k')
    Q = sp.Rational
    hlo, hhi = Q(707106781, 10**9), Q(707106782, 10**9)
    slo, shi = Q(2,25), Q(842457,10**7)
    q0 = Q(142559,50000)
    A, B = (1466+1940*h)/267, (327+432*h)/712
    t = (-20+30*h)*s+Q(7,2)-9*h/2
    dc = Q(1,2)+h-t
    q = 2*s*s+4*s+Q(5,2)
    P, H = s*s-A*s+B, h*h-Q(1,2)
    checks = []

    def zero(name, value):
        residual = sp.factor(value)
        if residual != 0: raise AssertionError((name, residual))
        checks.append({'name': name, 'result': 'PASS', 'exact_residual': '0'})

    def positive(name, value):
        value = sp.cancel(value)
        if not bool(value > 0): raise AssertionError((name, value))
        checks.append({'name': name, 'result': 'PASS', 'exact_positive_margin': str(value)})

    positive('sqrt2 lower endpoint squared', 2-(2*hlo)**2)
    positive('sqrt2 upper endpoint squared', (2*hhi)**2-2)
    for v, tag in ((hlo,'lo'), (hhi,'hi')):
        positive('A > 10 at h '+tag, A.subs(h,v)-10)
        positive('A < 11 at h '+tag, 11-A.subs(h,v))
        positive('B > 4/5 at h '+tag, B.subs(h,v)-Q(4,5))
        positive('B < 1 at h '+tag, 1-B.subs(h,v))
        positive('P(2/25) at h '+tag, P.subs({h:v,s:slo}))
        positive('-P(842457/10000000) at h '+tag, -P.subs({h:v,s:shi}))
    assert sp.Poly(P.subs(s,slo), h).degree() == 1
    assert sp.Poly(P.subs(s,shi), h).degree() == 1
    positive('strict candidate ceiling at s upper endpoint', q0-q.subs(s,shi))
    zero('small-root denominator polynomial',
         (2*B)**2-A*(2*B)*(A+k)+B*(A+k)**2-B*(k*k-(A*A-4*B)))
    zero('east active radius', q-((s+Q(1,2))**2+(s+Q(3,2))**2))
    zero('west active radius certificate',
         q-(Q(3,2)-s)**2-(t+Q(1,2))**2
         -(1200*h-849)*P+(320400*s*s-3200120*s+266409)/356*H)
    zero('diagonal active radius certificate',
         q-2*dc**2-2*h*dc-Q(1,2)
         -(2400*h-1698)*P+(320400*s*s-3232160*s+271927)/178*H)
    L = (Q(231,10)-9*z)/11
    G0 = Q(277,200)**2+((Q(231,10)-9*Q(277,200))/11)**2
    zero('chart supporting-line identity',
         z*z+L*L-G0-(200*z-277)*(20200*z-13603)/2420000)
    positive('chart supporting-line endpoint minus Q0', G0-q0)
    positive('corner-nearest contradiction', Q(77,200)**2+2*Q(77,200)+2-q0)
    positive('rho lower endpoint squared', q0-Q(1,4)-(Q(111,100)+Q(1,2))**2)
    positive('rho upper endpoint squared', (Q(1113,1000)+Q(1,2))**2-(q0-Q(1,4)))
    positive('uniform transverse squared upper bound', Q(121,125)**2-(6*Q(1113,1000)-Q(23,4)))
    lx, ly = h*(x+d)+h*(y+d), -h*(x+d)+h*(y+d)
    zero('diagonal inverse x coordinate', x+d-h*(lx-ly)+2*(x+d)*H)
    zero('diagonal inverse y coordinate', y+d-h*(lx+ly)+2*(y+d)*H)
    zero('diagonal farthest-vertex identity',
         (2*h*d+Q(1,2))**2+Q(1,4)-(2*d*d+2*h*d+Q(1,2))-4*d*d*H)
    positive('central-diagonal clearance', slo+Q(1,2)+hlo-Q(211,500)-Q(43,50))
    positive('diagonal normal separation', hlo*Q(18,25)-Q(1,2))

    # Each separator margin is affine: exact endpoint checking on this box
    # is just a sanity check of the ten chosen elementary axis separations.
    st = sp.symbols('t')
    centers = [(s,s),(s,s+1),(s+1,s),(s-1,st),(st,s-1)]
    vertices = [(sv,tv) for sv in (slo,Q(17,200)) for tv in (Q(2,5),Q(211,500))]
    for i in range(5):
        for j in range(i+1,5):
            a,b = centers[i],centers[j]
            margins = [b[0]-a[0]-1,a[0]-b[0]-1,b[1]-a[1]-1,a[1]-b[1]-1]
            accepted = []
            for axis,m in enumerate(margins):
                assert sp.Poly(m,s,st).total_degree() <= 1
                lower = min(m.subs({s:sv,st:tv}) for sv,tv in vertices)
                if lower >= 0: accepted.append((axis,str(lower)))
            if not accepted: raise AssertionError(('parallel separation',i,j))
            checks.append({'name': f'parallel pair {i}/{j}', 'result': 'PASS',
                           'axis': accepted[0][0], 'exact_lower_margin': accepted[0][1]})
    report = {'scope': 'exact algebra sanity only; NOT Lean compilation or proof acceptance',
              'sympy_version': sp.__version__, 'checks': checks, 'passed': len(checks),
              'lean_compilation_performed': False, 'unrestricted_n6_theorem_proved': False}
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',type=Path)
    args = parser.parse_args()
    main(args.json)

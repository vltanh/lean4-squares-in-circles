#!/usr/bin/env python3
"""Exact rational conditions in the wide asymmetric physical row proof.

This is arithmetic evidence, not a replacement for the continuous proof
or a certificate that any fixed original cell implies the row guard.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json


def add(p, q):
    return tuple((p[i] if i < len(p) else F(0)) +
                 (q[i] if i < len(q) else F(0))
                 for i in range(max(len(p), len(q))))


def scale(p, c):
    return tuple(F(c)*v for v in p)


def mul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return tuple(r)


def deriv(p):
    return tuple(i*p[i] for i in range(1, len(p)))


def value(p, x):
    return sum(c*x**i for i,c in enumerate(p))


def main():
    checks = []
    def eq(name, p, q):
        assert not any(add(p, scale(q, -1))), (name, p, q)
        checks.append({'kind': 'polynomial_identity', 'name': name,
                       'coefficients': [str(c) for c in p]})
    def positive(name, x):
        assert x > 0, (name, x)
        checks.append({'kind': 'positive_rational', 'name': name,
                       'reserve': str(x)})
    u, delta = F(2,5), F(1,10)
    z2 = (F(1), F(0), F(1))
    t = (F(0), F(1))
    # Exact squared comparison for every shallow positive signed owner.
    A = (F(2), F(1), F(1))
    B = (F(2), F(4,5))
    diff = add(mul(A,A), scale(mul(mul(B,B),z2),-1))
    cubic = (F(20),F(9),F(-30),F(9))
    eq('upward signed pair squared difference', diff,
       scale(mul(t,cubic),F(1,25)))
    eq('concave cubic second derivative',deriv(deriv(cubic)),
       (F(-60),F(54)))
    positive('cubic at zero',value(cubic,F(0)))
    positive('cubic at one',value(cubic,F(1)))
    positive('negative cubic second derivative on unit interval', F(60)-54)
    positive('steep signed owner squared comparison',2-(1+u)**2)
    positive('first-link incircle comparison',1-2*u*u)
    positive('last-link incircle comparison',1-2*delta*delta)
    positive('w exceeds nine tenths squared',1-u*u-F(9,10)**2)
    positive('k less than one half squared',F(1,4)-u*u/(1-u*u))
    positive('sqrt2 exceeds seven fifths squared',F(2)-F(7,5)**2)
    positive('last gap below accepted one eighth',F(1,8)-delta)
    positive('middle endpoint coefficient', (F(9,10)-u)/2-delta)
    positive('middle endpoint reserve',2*F(9,10)+u-2-F(1,8))
    positive('last endpoint reserve',F(7,5)+F(9,10)-2-F(1,8)-delta)
    positive('steep last-link reserve',F(7,5)-delta-1-F(1,10))
    assert u+delta == F(1,2)
    checks.append({'kind':'rational_identity','name':'positive-D total variation',
                   'value':str(u+delta)})
    # Same continuous derivative expressions, independently expanded.
    a=(F(1),F(0),F(0),F(1))
    eq('derivative of cosine-cube plus sine-cube',
       add(mul(deriv(a),z2),scale(mul(t,a),-3)),
       (F(0),F(-3),F(3)))
    eq('strict A-plus-r derivative numerator remainder',
       add((F(1),F(2),F(0),F(3)),scale(mul((F(1),F(1)),z2),-1)),
       (F(0),F(1),F(-1),F(2)))
    positive('one minus t plus two t squared discriminant',8-1)
    for z in (F(0),F(1)):
        a=(1-z/2,-z/2,F(0),F(1))
        eq('first concavity derivative z='+str(z),
           add(mul(deriv(a),z2),scale(mul(t,a),-3)),
           (-z/2,-3+3*z/2,3+z))
    q=(F(-1,2),F(-3,2),F(4))
    positive('z=1 concavity endpoint zero',-value(q,F(0)))
    positive('z=1 concavity endpoint one half',-value(q,F(1,2)))
    eq('zero-X endpoint radical comparison',
       add(mul(mul((F(2),F(1)),(F(2),F(1))),z2),
           scale(mul(A,A),-1)),
       (F(0),F(0),F(0),F(2)))
    positive('last-gap versus retained transverse gap',F(2,3)-delta)
    assert F(3,2)-F(2,3)-F(1,2)==F(1,3)
    # Original equality exclusion p^2+(1-p)^2=1-2p(1-p).
    eq('original C-X equality comparison',(F(1),F(-2),F(2)),
       add((F(1),),scale(mul(t,(F(1),F(-1))),-2)))
    report={'status':'PASS','scope':'continuous conditional physical theorem plus exact arithmetic; no whole original cell closure',
            'first_vertical_interval':['0',str(u)],'last_vertical_absolute_bound':str(delta),
            'checks':checks,'check_count':len(checks),'whole_mask_closed':False,
            'new_original_cells_closed':0,'new_masks_closed':0}
    script=Path(__file__)
    proof=script.parent.parent/'WEAK_OUTER_TWO_FIFTHS_ONE_TENTH_ROW_HAND_TERMINAL.md'
    report['source_sha256']={script.name:hashlib.sha256(script.read_bytes()).hexdigest(),
                             proof.name:hashlib.sha256(proof.read_bytes()).hexdigest()}
    script.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()

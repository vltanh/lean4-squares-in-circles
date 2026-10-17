#!/usr/bin/env python3
"""Exact finite regressions for the frame-majority covering lemma."""
from fractions import Fraction as Q
from random import Random
from verify_ordered_rational_gate import frame, dot
from verify_gated_fiber_and_canonical_owner import construction


def quarter_representative(x,y):
    for _ in range(4):
        if x>0 and y>=0:
            return x,y
        x,y=-y,x
    raise AssertionError('Zero direction or missing representative')


def counts(directions):
    result=[]
    for a in directions:
        count=0
        for b in directions:
            c=dot(a,b)
            s=a[0]*b[1]-a[1]*b[0]
            c,s=quarter_representative(c,s)
            count+=c>=s
        result.append(count)
    return result


def main():
    # Unnormalized direction vectors also give exact angular comparisons.
    examples=[[(Q(1),Q(0))]*8,
              [(Q(1),Q(0))]*4+[(Q(1),Q(1))]*4,
              [(Q(x),Q(y)) for x,y in
               ((8,0),(8,2),(8,3),(8,5),(8,8),(5,8),(3,8),(2,8))]]
    rng=Random(20261013)
    for _ in range(500):
        examples.append([frame(Q(rng.randint(-32,32),32))[3] for _ in range(8)])
    observed=set()
    for directions in examples:
        cs=counts(directions)
        assert sum(cs)>=36 and 5<=max(cs)<=8
        observed.add(max(cs))
    for generic in (False,True):
        _,fs=construction(generic)
        assert max(counts([e for e,f in fs]))==8
    assert observed=={5,6,7,8}
    print(f'{len(examples)} exact eight-frame tests: sum of window counts >=36, maximum >=5: PASS')
    print('All four majority sizes 5,6,7,8 occurred in the regression inputs.')
    print('Exact 45-degree ties and both genuine n8 packing regressions retained: PASS')
    print('The continuous covering statement is proved by pair counting, not these tests.')

if __name__=='__main__':
    main()

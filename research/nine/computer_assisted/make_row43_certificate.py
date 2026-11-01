#!/usr/bin/env python3
"""Construct an exact quadratic certificate for the full 4-over-3 row family.

This is a proper continuous subdomain of the unrestricted nine-square problem.
It is NOT a classification or exclusion of every nine-square packing.
The verifier does not import this file or its calculation of the weights.
"""
from fractions import Fraction as F
import json


def generate():
    # Maximize lambda*(4/2)^2+(1-lambda)*(3/2)^2+4*lambda*(1-lambda).
    # Derivative is 16/4-9/4+4-8*lambda, giving this exact optimum.
    w = (F(16, 4) - F(9, 4) + 4) / 8
    v = 1 - w
    bound = w*4 + v*F(9, 4) + 4*w*v
    def square(weight, **linear):
        return {'weight': str(weight), 'affine': {k: str(z) for k, z in linear.items()}}
    return {
        'schema': 'row43-quadratic-v1',
        'scope': 'four horizontal unit squares in an upper row, three in a lower row; '
                 'all five consecutive x gaps >=1, upper-minus-lower y gap >=1; '
                 'two other physical unit squares arbitrary and retained',
        'target': str(bound),
        'weighted_hypotheses': {
            'corner_0_1': str(w/2), 'corner_3_3': str(w/2),
            'corner_4_0': str(v/2), 'corner_6_2': str(v/2),
            'gap_0_1': str(2*w), 'gap_1_2': str(2*w), 'gap_2_3': str(2*w),
            'gap_4_5': str(3*v/2), 'gap_5_6': str(3*v/2), 'row_gap': str(4*w*v),
        },
        'squares': [
            square(w, x_0=F(1, 2), x_3=F(1, 2)),
            square(v, x_4=F(1, 2), x_6=F(1, 2)),
            square(1, ya=w, yb=v, ONE=(w-v)/2),
            square(w/4, x_3=1, x_0=-1, ONE=-3),
            square(v/4, x_6=1, x_4=-1, ONE=-2),
            square(w*v, ya=1, yb=-1, ONE=-1),
        ],
        'claim': 'q-target is exactly sum(weight*nonnegative_hypothesis)+sum(weight*affine^2)',
        'global_infeasibility_proved': False,
    }


if __name__ == '__main__':
    print(json.dumps(generate(), indent=2, sort_keys=True))

#!/usr/bin/env python3
"""Certify the contact family's two nonparallel mandatory separator normals.

This imports the existing exact root certificate without changing it. The
geometric consequence is proved in NO_COMMON_SEPARATING_FRAME.md.
"""
from fractions import Fraction
from contact_family import family
from isolate_contact_root import certificate


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check():
    box = certificate()
    _, centers, angles, extra = family(box[0], box[1], lambda x: x.sqrt())
    (_, b), (_, d) = centers[0], centers[2]
    (cosine, sine), _ = angles
    _, _, _, z = extra
    vertical_displacement = d - b
    require(vertical_displacement.lo > Fraction(-9, 10), 'pair 0,2 overlap lower bound failed')
    require(vertical_displacement.hi < 0, 'pair 0,2 vertical order failed')
    require(z.lo > 0 and z.hi < Fraction(1, 20), 'pair 7,8 overlap bound failed')
    require(cosine.lo > 0 and sine.lo > 0, 'tilted normal must be oblique to both coordinate axes')
    print('PASS: -9/10 < d-b < 0, so pair (0,2) shares a vertical edge segment of length > 1/10.')
    print('PASS: 0 < z < 1/20, so pair (7,8) shares an edge segment parallel to j of length > 19/20.')
    print('PASS: c > 0 and s > 0, so their mandatory normal u=(c,s) is neither horizontal nor vertical.')
    print('Conclusion, using the shared-edge lemma: no common orthogonal separating frame exists.')
    print('Scope: the exact constructed family; no global optimality or exhaustive classification claim.')


if __name__ == '__main__':
    check()

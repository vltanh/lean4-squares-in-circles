#!/usr/bin/env python3
"""Exact 7-ray combinatorics for the k7/B3 four-square positive core.

For J={C,X,Y,Z}, central C has positive degree three.
Nonzero moment cycle and outer-angular visibility force
at least one positive outer pair. Two positive outer pairs
would require three consecutive outer center rays and violate
the physical circle-force semicircle theorem.
Thus X,Y is the unique adjacent outer pair and Z cannot
be either angular neighbor immediately outside that pair.

The script counts label templates; it does not assert
that any of them is geometrically feasible.
"""
from itertools import combinations
pairs=set()
for triple in combinations(range(7),3):
    E=[frozenset((i,j)) for i,j in combinations(triple,2)
       if (i-j)%7 in (1,6)]
    if len(E)==1:
        pairs.add((E[0],frozenset(triple)))
assert len(pairs)==21
assert sum(1 for t in combinations(range(7),3)
           if sum((i-j)%7 in (1,6) for i,j in combinations(t,2))==2)==7
assert sum(1 for t in combinations(range(7),3)
           if not any((i-j)%7 in (1,6) for i,j in combinations(t,2)))==7
for i in range(7):
    XY=frozenset((i,(i+1)%7))
    candidates={next(iter(Z-XY)) for edge,Z in pairs if edge==XY}
    assert candidates=={(i+3)%7,(i+4)%7,(i+5)%7}
print("PASS: k7 B3 core has 21 triple-label graph templates")
print("      7 choices of unique positive outer pair X-Y")
print("      times 3 non-neighboring ray positions for radial C leaf Z")

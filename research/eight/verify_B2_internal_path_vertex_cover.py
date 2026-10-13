#!/usr/bin/env python3
"""Exact finite combinatorics behind the B2 stressed-path internal cover.

The geometry is established in HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md:
if consecutive internal path squares were both circle-free and had
no additional C actual contact, they would be adjacent interior
actual-degree-two transmitters, which is impossible at R<2.

This script only verifies the path vertex-cover cardinalities and
the allowed minimal binary anchor patterns for m=3,4,5,6.
"""
from collections import Counter

expected={3:0,4:1,5:1,6:2}
expected_minimal={
    3:[(0,)],
    4:[(0,1),(1,0)],
    5:[(0,1,0)],
    6:[(0,1,0,1),(0,1,1,0),(1,0,1,0)]
}
for m in range(3,7):
    k=m-2
    covers=[]
    for mask in range(1<<k):
        vals=tuple(int(bool(mask & (1<<i))) for i in range(k))
        if all(vals[i] or vals[i+1] for i in range(k-1)):
            covers.append(vals)
    smallest=min(sum(v) for v in covers)
    minimal=sorted(v for v in covers if sum(v)==smallest)
    assert smallest==expected[m]
    assert minimal==sorted(expected_minimal[m]),(m,minimal)
    print(f"m={m}: {k} internal path squares, minimum {smallest} "
          f"boundary-or-chord anchors; {len(minimal)} minimum patterns")
print("PASS: all internal-edge vertex cover minima and classifications")

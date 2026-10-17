#!/usr/bin/env python3
"""Exact graph audit for HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md.

C actually touches only three positively stressed neighbors X,Y,Z.
The unique positive outer pair X-Y has consecutive ray labels, and Z
is at index +3,+4,+5 in the seven-center circular order. All optional
outer actual edges lie on the Y-Z and Z-X complementary arcs.

If a selected proper subset creates a noncentral actual degree-1
spectator, the contact-minimal genuine-square leaf theorem forbids it.
This script checks the GRAPH step only, not the physical lemma or any
semialgebraic realization of the 63 remaining graphs.
"""
from collections import Counter

totals=Counter()
modes=Counter()
for start in range(7):
    for dz in (3,4,5):
        X,Y,Z=start,(start+1)%7,(start+dz)%7
        key=lambda i,j:frozenset((i,j))
        arc_yz=[key((start+i)%7,(start+i+1)%7)
                for i in range(1,dz)]
        arc_zx=[key((start+i)%7,(start+i+1)%7)
                for i in range(dz,7)]
        optional=arc_yz+arc_zx
        assert len(optional)==6
        assert len(arc_yz)>=2 and len(arc_zx)>=2
        admitted=[]
        for mask in range(1<<6):
            selected={optional[i] for i in range(6)
                      if mask & (1<<i)}
            if len(selected)==6:
                totals["full_ring_forbidden"]+=1
                continue
            spectator_degrees={
                j:sum(j in edge for edge in selected)
                for j in range(7) if j not in (X,Y,Z)
            }
            if any(degree==1 for degree in spectator_degrees.values()):
                totals["partial_forbidden_noncentral_leaf"]+=1
                continue
            admitted.append(selected)
            totals["admitted"]+=1
            if not selected: modes["isolated"]+=1
            elif selected==set(arc_yz): modes["whole_YZ_arc"]+=1
            elif selected==set(arc_zx): modes["whole_ZX_arc"]+=1
            else: raise AssertionError("unexpected spectator graph")
        assert len(admitted)==3
        totals["positive_label_patterns"]+=1

assert totals=={
    "positive_label_patterns":21,
    "full_ring_forbidden":21,
    "partial_forbidden_noncentral_leaf":1260,
    "admitted":63,
}
assert modes=={"isolated":21,"whole_YZ_arc":21,"whole_ZX_arc":21}
assert 21*64==63+1260+21
print("PASS: 21 positive label patterns x 64 optional-edge masks")
print("      1260 partially selected outer spectator arcs force")
print("      forbidden noncentral actual leaves; 21 full rings excluded")
print("      Exactly 63 actual-graph templates survive: empty, YZ, ZX")

#!/usr/bin/env python3
"""Enumerate the optional OUTER-actual-contact supergraphs of k7/B2 m=3..6.

The hand proof in HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md
uses outer angular visibility and the adjacent-interior-transmitter
theorem. This script checks only combinatorial edge counts and
the forced spectator-gap conclusion, not full square feasibility.
"""
from collections import Counter

stats=Counter()
both_circle_free_masks=Counter()
for m in range(3,7):
    for start in range(7):
        path=[(start+i)%7 for i in range(m)]
        spectators=[(start+m+j)%7 for j in range(7-m)]
        fixed={frozenset((path[i],path[i+1])) for i in range(m-1)}
        cycle=[frozenset((i,(i+1)%7)) for i in range(7)]
        optional=[e for e in cycle if e not in fixed]
        assert len(optional)==8-m

        # For m<7, endpoint adjacency across the complementary
        # angular arc is to the first/last spectator, respectively.
        left=frozenset((path[0],spectators[-1]))
        right=frozenset((path[-1],spectators[0]))
        assert left in optional and right in optional
        middle={frozenset((spectators[i],spectators[i+1]))
                for i in range(len(spectators)-1)}
        assert set(optional)==({left,right}|middle)

        for mask in range(1<<len(optional)):
            chosen={optional[i] for i in range(len(optional)) if mask>>i&1}
            E=fixed|chosen
            if E==set(cycle):  # forbidden full 7-outer actual cycle
                continue
            stats[m]+=1
            # The true geometric endpoint theorem says:
            # if its spectator edge is absent, that endpoint must
            # be on the circle, not that its radius test is automatic.
            if left not in E:
                assert sum(path[0] in e for e in E)==1
            if right not in E:
                assert sum(path[-1] in e for e in E)==1

            if left in E and right in E:
                both_circle_free_masks[m]+=1
                assert len(spectators)>=2
                assert any(e not in E for e in middle)
                if m==5:
                    assert len(middle)==1 and not (middle<=E)
                if m==6:
                    raise AssertionError("Both circle-free cannot occur in m6")
assert dict(stats)=={3:217,4:105,5:49,6:21}
assert dict(both_circle_free_masks)=={3:49,4:21,5:7}
assert sum(stats.values())==392
print("PASS: 392 k7/B2 m3..6 outer actual-graph templates")
print("      m6 forbids both circle-free endpoints")
print("      m5 with both circle-free endpoints has exactly one")
print("      missing spectator-spectator contact edge")

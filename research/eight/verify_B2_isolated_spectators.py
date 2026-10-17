#!/usr/bin/env python3
"""Finite graph audit for HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md.

Enumerates every labeled seven-outer, positive-path m=3..6 actual-graph
supertemplate. In the C-actual-degree-two case spectators cannot contact C.
Then any nonempty proper complementary spectator-path edge subset creates
an actual-degree-one spectator whose ONLY neighbor is noncentral. The
contact-minimal true-square leaf theorem rules this out.

This script is a combinatorial cross-check, NOT a full square-packing
feasibility oracle or a substitute for the hand actual-leaf theorem.
"""
from collections import Counter

admitted=Counter()
eliminated=Counter()
for m in range(3,7):
    for start in range(7):
        stressed=[(start+i)%7 for i in range(m)]
        spectators=[(start+m+i)%7 for i in range(7-m)]
        key=lambda i,j:frozenset((i,j))
        cycle={key(i,(i+1)%7) for i in range(7)}
        core={key(stressed[i],stressed[i+1]) for i in range(m-1)}
        optional=list(cycle-core)
        assert len(optional)==8-m
        for mask in range(1<<len(optional)):
            actual=core|{optional[i] for i in range(len(optional))
                         if mask & (1<<i)}
            if actual==cycle:
                # Full seven-outer ACTUAL cycle is a separate root A.
                continue
            if not (actual-core):
                admitted[m]+=1
                assert all(sum(v in e for e in actual)==0
                           for v in spectators)
            else:
                eliminated[m]+=1
                leaves=[v for v in spectators
                        if sum(v in e for e in actual)==1]
                assert leaves, (m,start,mask,actual)

assert dict(admitted)=={3:7,4:7,5:7,6:7},admitted
assert dict(eliminated)=={3:210,4:98,5:42,6:14},eliminated
assert sum(admitted.values())==28
assert sum(eliminated.values())==364
assert sum(admitted.values())+sum(eliminated.values())==392

print("PASS: all 392 outer actual graph templates audited")
print("      364 additional spectator-edge templates produce")
print("      a noncentral actual leaf and are therefore impossible")
print("      for C actual degree two in a contact-minimal minimizer")
print("      Only 28 bare positive-cycle actual graph supports remain")

#!/usr/bin/env python3
"""Graph enumeration for the k7 m6 positive-stress path and one spectator.

Computational *graph* cross-check only. The true packing and stress
implications are proved analytically in HUMAN_M6_SPECTATOR_ENDPOINT_BOUNDARY.md.
Seven outer labels appear in cyclic order 0..6. Six consecutive labels
support the five positive outer edges, while the remaining label
is a zero-positive-stress spectator. Since the *actual* outer graph
is not the full seven-cycle, at most one optional spectator contact
may be present.
"""
from collections import Counter

total=0
cases=Counter()
for start in range(7):
    path=[(start+i)%7 for i in range(6)]
    spectator=(start+6)%7
    fixed={frozenset((path[i],path[i+1])) for i in range(5)}
    extra_a=frozenset((spectator,path[0]))
    extra_b=frozenset((spectator,path[-1]))
    for option in (0,1,2):
        extras=set()
        if option==1:
            extras.add(extra_a)
        elif option==2:
            extras.add(extra_b)
        actual=fixed|extras
        allowed={frozenset((i,(i+1)%7)) for i in range(7)}
        assert actual<=allowed
        assert len(actual)<7
        assert all(frozenset((path[i],path[i+1])) in actual
                   for i in range(5))
        deg=lambda u:sum(u in edge for edge in actual)
        # Each endpoint has 1 path neighbor and maybe 1 spectator
        endpoint_without_spectator=[
            u for u in (path[0],path[-1]) if deg(u)==1]
        assert len(endpoint_without_spectator)==(2 if option==0 else 1)
        # Add the one actual central contact to each endpoint:
        # at least one stressed endpoint has full actual degree exactly 2.
        assert any(deg(u)+1==2 for u in (path[0],path[-1]))
        cases[option]+=1
        total+=1
assert total==21
assert cases=={0:7,1:7,2:7}
print("PASS: 7 cyclic placements x 3 optional spectator edges = 21")
print("      Every surviving m6 template has a stressed path endpoint")
print("      of actual square-contact degree two (when C actual degree=2)")
print("      Its true circle contact follows from the adjacent-transmitter hand theorem")

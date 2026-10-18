#!/usr/bin/env python3
"""Exact finite vertex-cover audit for positive physical circle multipliers.

For a C-rooted stressed cycle C-S1-...-Sm-C, with m>=3,
positive force balance and R<2 forbid two adjacent
zero-total-circle-multiplier squares. The central C has
zero multiplier, forcing S1, Sm positive. This enumerates
the remaining internal Boolean support patterns only.
It is not a packing feasibility search or substitute for
the hand four-square projection-chain proof.
"""
from collections import Counter

expected={3:2,4:3,5:3,6:4}
expected_minimal={
  3:[(1,0,1)],
  4:[(1,1,0,1),(1,0,1,1)],
  5:[(1,0,1,0,1)],
  6:[(1,0,1,0,1,1),(1,0,1,1,0,1),(1,1,0,1,0,1)]
}
for m in range(3,7):
    supports=[]
    for mask in range(1<<m):
        pos=tuple(int(bool(mask & (1<<i))) for i in range(m))
        # C is circle-free, so both neighboring cycle vertices need µ>0.
        if not (pos[0] and pos[-1]):
            continue
        if not all(pos[i] or pos[i+1] for i in range(m-1)):
            continue
        supports.append(pos)
    mini=min(sum(s) for s in supports)
    minimum_patterns=sorted(s for s in supports if sum(s)==mini)
    assert mini==expected[m],(m,mini)
    assert minimum_patterns==sorted(expected_minimal[m]),(m,minimum_patterns)
    print(f"m={m}: >= {mini} distinct positive circle-multiplier "
          f"outer squares; {len(minimum_patterns)} minimal supports")
print("PASS: positive-circle-stress support is a cycle vertex cover")
print("      with central square multiplier zero; m6 needs >=4")

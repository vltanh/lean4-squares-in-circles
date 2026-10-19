#!/usr/bin/env python3
"""Exhaustive finite support audit of seven-outer C-degree-two stress cycles.

All seven outer labels are numbered cyclically modulo seven and C has
label 7. This verifies only the GRAPH reduction proved in
HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md:

* The actual outer graph is a proper subgraph of the 7-cycle.
* The positive-stress graph has exactly two central C spokes, C-A and C-B.
* All positive outer edges carry nonzero moment; hence are on a
  C-rooted directed cycle (torque conservation).
* Opposed central contact normals forbid A-B actual contact.

The script is NOT a geometric packing classifier or Lean proof.
"""
from collections import Counter

def path_in_edges(edges, a, b):
    adj={i:set() for i in range(7)}
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    stack=[(a,[a])]
    visited={a}
    while stack:
        u,path=stack.pop()
        if u==b:
            return path
        for v in adj[u]:
            if v not in visited:
                visited.add(v)
                stack.append((v,path+[v]))
    return None

outer_edges=[(i,(i+1)%7) for i in range(7)]
raw=Counter()
allowed=Counter()
for mask in range(1<<7):
    if mask==(1<<7)-1:
        continue  # full outer actual-contact cycle is a separate case
    E=[outer_edges[i] for i in range(7) if (mask>>i)&1]
    for a in range(7):
        for b in range(a+1,7):
            path=path_in_edges(E,a,b)
            if path is None:
                continue
            edges_on_path={frozenset((path[i],path[i+1]))
                           for i in range(len(path)-1)}
            # If ANY other positive outer edge existed, it would be a
            # bridge/tail with zero moment, contradicting the hand lemma.
            if edges_on_path!={frozenset(e) for e in E}:
                continue
            m=len(path)
            raw[m]+=1
            if m>=3:
                allowed[m]+=1
assert dict(raw)=={2:7,3:7,4:7,5:7,6:7,7:7},raw
assert dict(allowed)=={3:7,4:7,5:7,6:7,7:7},allowed
assert sum(allowed.values())==35
print("PASS: 42 graph-theoretic cycles; seven two-outer triangles")
print("      excluded by opposite central forces; 35 supports remain")
print("      Seven cyclic placements per outer path size m=3,...,7")

#!/usr/bin/env python3
"""Exact 3-bit contact incidence audit for the unique k7/m6 spectator.

T can only contact its two circularly neighboring outer squares S1,S6
and the one central inner square C. True geometry additionally forbids
both outer contacts (would complete the full outer seven-cycle), and
a sole outer contact without C (actual leaf theorem).

This script checks the *finite incidence* only, not an n=8
packing proof or a complete numerical feasibility classifier.
"""
legal=[]
excluded_full=[]
excluded_noncentral_leaf=[]
for s1 in (False,True):
    for s6 in (False,True):
        for c in (False,True):
            if s1 and s6:
                excluded_full.append((s1,s6,c))
            elif (s1 or s6) and not c:
                excluded_noncentral_leaf.append((s1,s6,c))
            else:
                legal.append((s1,s6,c))
assert len(excluded_full)==2
assert len(excluded_noncentral_leaf)==2
assert sorted(legal)==sorted([(0,0,0),(0,0,1),(1,0,1),(0,1,1)])
print("PASS: 8 raw spectator contact words -> 4 legal labeled incidences")
print("      isolated, C-only leaf, C+S1 triangle, C+S6 triangle")

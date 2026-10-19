#!/usr/bin/env python3
"""NONCERTIFYING diagnostic: sample raw true SAT owner words and prune
directed three-square cycles by the PROVED global 60-degree cone theorem.

This measures search-tree utility. It does NOT certify full coverage
of all 8^28 words or an n8 radius lower bound. Mathematical theorem:
HUMAN_GLOBAL_SAT_OWNER_CYCLE_CONE_EXCLUSION.md.
"""
from itertools import combinations
from math import pi
import numpy as np

rng=np.random.default_rng(20261013)
N=8
pairs=list(combinations(range(N),2))
triples=list(combinations(range(N),3))

def span3(normals):
    a=np.sort(np.mod(np.arctan2(normals[:,1],normals[:,0]),2*pi))
    return 2*pi-max(a[1]-a[0],a[2]-a[1],a[0]+2*pi-a[2])

def run(case,samples):
    bad_words=0
    numbers=[]
    for j in range(samples):
        if case=="aligned":
            angles=np.zeros(N)
        elif case=="candidate":
            angles=np.r_[np.zeros(6),.123,.123]
        else:
            angles=rng.uniform(-pi/4,pi/4,N)
        ee=np.column_stack((np.cos(angles),np.sin(angles)))
        ff=np.column_stack((-np.sin(angles),np.cos(angles)))
        owners={}
        for i,k in pairs:
            opts=np.array([ee[i],-ee[i],ff[i],-ff[i],
                           ee[k],-ee[k],ff[k],-ff[k]])
            owners[(i,k)]=opts[rng.integers(8)]
        bad=0
        for i,k,l in triples:
            ns=np.array([owners[(i,k)],owners[(k,l)],-owners[(i,l)]])
            if span3(ns)<=pi/3+1e-10:
                bad+=1
        numbers.append(bad)
        bad_words+=bad>0
    print(case,"samples",samples,"fraction_pruned",bad_words/samples,
          "mean_forbidden_triangles",np.mean(numbers),
          "max",max(numbers))

if __name__=="__main__":
    for case in ("aligned","candidate","random"):
        run(case,2000)
    print("DIAGNOSTIC ONLY: random owner samples are NOT exhaustive.")

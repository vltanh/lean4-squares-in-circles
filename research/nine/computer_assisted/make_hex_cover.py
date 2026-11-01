#!/usr/bin/env python3
"""Generate the exhaustive 19-hexagon root cover and five exact center exclusions.

This is NOT the unrestricted n=9 lower-bound proof. Every unexcluded root is OPEN.
No orientation or contact-graph premise is imposed. NumPy accelerates integer
geometry only; verify_hex_cover.py independently checks the proof using Python ints.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import combinations
import json
from pathlib import Path
import numpy as np

M = 6
SIDE = F(49, 100)
RHO = F(91, 60)
CELLS = sorted((q, r) for q in range(-2, 3) for r in range(-2, 3)
               if max(abs(q), abs(r), abs(q+r)) <= 2)
INDEX = {c: i for i, c in enumerate(CELLS)}
HEX = ((2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1))
CORES = (447, 507, 2255, 4303, 5559)

def bits(n: int) -> list[int]:
    return [i for i in range(n.bit_length()) if n >> i & 1]

def dot(p, q):
    return p[0]*q[0] + 3*p[1]*q[1]

def minimum_norm(triangle):
    turns = []
    values = []
    for i, p in enumerate(triangle):
        q = triangle[(i+1) % 3]
        v = (q[0]-p[0], q[1]-p[1])
        turns.append(v[0]*(-p[1]) - v[1]*(-p[0]))
        t = min(F(1), max(F(0), F(-dot(p,v), dot(v,v))))
        values.append(dot(p,p) + 2*t*dot(p,v) + t*t*dot(v,v))
    if all(x >= 0 for x in turns) or all(x <= 0 for x in turns):
        return F(0)
    return min(values)

def geometry():
    all_triangles = []
    for cell, (q,r) in enumerate(CELLS):
        cx, cy = 3*q*M, (q+2*r)*M
        for k in range(6):
            a, b = HEX[k], HEX[(k+1) % 6]
            def point(i,j):
                return cx+i*a[0]+j*b[0], cy+i*a[1]+j*b[1]
            for i in range(M):
                for j in range(M-i):
                    all_triangles.append((cell, tuple(sorted((point(i,j), point(i+1,j), point(i,j+1))))))
                    if i+j <= M-2:
                        all_triangles.append((cell, tuple(sorted((point(i+1,j), point(i+1,j+1), point(i,j+1))))))
    all_triangles = sorted(set(all_triangles))
    assert len(all_triangles) == 19*6*M*M
    retained = [t for t in all_triangles
                if SIDE*SIDE*minimum_norm(t[1]) <= 4*M*M*RHO*RHO]
    groups = [0]*19
    for i, (c,t) in enumerate(retained):
        groups[c] |= 1 << i
    coords = np.array([t for c,t in retained], dtype=np.int64)
    assert int(np.max(np.abs(coords))) <= 12*M
    n = len(retained)
    largest = np.zeros((n,n), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            delta = coords[:,None,i,:] - coords[None,:,j,:]
            largest = np.maximum(largest, delta[:,:,0]**2 + 3*delta[:,:,1]**2)
    # These integers are < 2^31 for M=6, hence no int64 overflow occurs.
    allowed = 2401*largest >= 40000*M*M
    for c in range(19):
        ids = bits(groups[c])
        allowed[np.ix_(ids,ids)] = False
    adjacency = [sum(1 << int(v) for v in np.flatnonzero(row)) for row in allowed]
    return retained, groups, adjacency, len(all_triangles)-len(retained)

def symmetries():
    perms = []
    for reflect in (False,True):
        for turns in range(6):
            perm = []
            for q,r in CELLS:
                if reflect:
                    q,r = q,-q-r
                for _ in range(turns):
                    q,r = -r,q+r
                perm.append(INDEX[q,r])
            perms.append(perm)
    return perms

def transform(mask, perm):
    return sum(1 << perm[i] for i in bits(mask))

def cover(perms):
    seen = set()
    representatives = []
    sizes = Counter()
    for choice in combinations(range(19),9):
        mask = sum(1 << c for c in choice)
        if mask in seen:
            continue
        orbit = {transform(mask, p) for p in perms}
        seen.update(orbit)
        representatives.append(min(orbit))
        sizes[len(orbit)] += 1
    assert len(seen) == 92378
    return sorted(representatives), dict(sorted(sizes.items()))

def prove_cores(groups, adjacency):
    nodes = []  # ID 0 denotes an empty-domain leaf, checked in its actual context.
    memo = {}
    calls = [0]
    def refute(state):
        calls[0] += 1
        state = tuple(sorted(state))
        if any(domain == 0 for cell,domain in state):
            return 0
        if not state:
            raise ValueError('The alleged exclusion has a compatible discrete assignment')
        if state in memo:
            return memo[state]
        cell, domain = min(state, key=lambda x:(x[1].bit_count(),x[0]))
        rest = [(c,d) for c,d in state if c != cell]
        children = []
        for vertex in bits(domain):
            child = refute([(c,d & adjacency[vertex]) for c,d in rest])
            children.append([vertex,child])
        nodes.append([cell,children])
        result = len(nodes)
        memo[state] = result
        return result
    proofs = []
    for mask in CORES:
        root = refute([(c,groups[c]) for c in bits(mask)])
        proofs.append({'mask':mask,'cells':bits(mask),'proof_node':root})
    return proofs,nodes,calls[0]

def canonical_bytes(obj):
    return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    triangles,groups,adjacency,discarded = geometry()
    perms = symmetries()
    representatives,orbit_sizes = cover(perms)
    proofs,nodes,calls = prove_cores(groups,adjacency)
    patterns = [(k,j,transform(core,p)) for k,core in enumerate(CORES)
                for j,p in enumerate(perms)]
    records = []
    counts = Counter()
    for number,mask in enumerate(representatives):
        match = next(((k,j) for k,j,p in patterns if mask & p == p),None)
        row = {'id':number,'mask':mask,'cells':bits(mask),'status':'OPEN'}
        if match is not None:
            row.update(status='EXCLUDED',core=match[0],symmetry=match[1])
        records.append(row)
        counts[row['status']] += 1
    certificate = {'schema':'n9_hex_center_exclusions_v1','subdivision':M,
                   'cores':proofs,'nodes':nodes}
    cert_bytes = canonical_bytes(certificate)
    manifest = {'schema':'n9_hex_cover_v1','target_q':'1105/256','hex_side':'49/100',
                'center_radius_bound':'91/60','cells':CELLS,'symmetries':perms,
                'unquotiented_subsets':92378,'orbit_size_counts':orbit_sizes,
                'certificate_sha256':hashlib.sha256(cert_bytes).hexdigest(),
                'roots':records,'global_lower_bound_proved':False}
    report = {'result':'GENERATED_NOT_INDEPENDENTLY_VERIFIED','root_count':len(records),
              'statuses':dict(counts),'fine_triangles_retained':len(triangles),
              'fine_triangles_discarded':discarded,'proof_nodes':len(nodes),
              'producer_recursion_calls':calls,'core_count':len(CORES),
              'global_lower_bound_proved':False,'full_equality_classified':False,
              'separate_human_review_performed':False,
              'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certificate_sha256':hashlib.sha256(cert_bytes).hexdigest()}
    (args.out/'hex_exclusion_certificate.json').write_bytes(cert_bytes)
    (args.out/'hex_root_manifest.json').write_bytes(canonical_bytes(manifest))
    (args.out/'hex_generation_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()

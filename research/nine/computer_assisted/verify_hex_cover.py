#!/usr/bin/env python3
"""Independent standard-library replay of the finite n=9 hex cover.

Does not import the producer, NumPy, an optimizer, or any stress code. Geometry,
root enumeration, and every proof branch are reconstructed with Python integers
and Fraction. A passing report proves ONLY the listed center-pattern exclusions.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)

def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask -= bit

def scalar(p,q):
    return p[0]*q[0]+3*p[1]*q[1]

def cross(p,q):
    return p[0]*q[1]-p[1]*q[0]

def minus(p,q):
    return p[0]-q[0],p[1]-q[1]

def lower_squared_norm(t):
    # Origin membership by oriented determinants; edge minima by orthogonal projection.
    signs = [cross(t[i],t[(i+1)%3]) for i in range(3)]
    if min(signs) >= 0 or max(signs) <= 0:
        return F(0)
    best = min(F(scalar(p,p)) for p in t)
    for p,q in zip(t,t[1:]+t[:1]):
        edge = minus(q,p)
        denominator = scalar(edge,edge)
        numerator = -scalar(p,edge)
        if 0 < numerator < denominator:
            best = min(best,F(scalar(p,p)*denominator-numerator*numerator,denominator))
    return best

class Geometry:
    def __init__(self):
        self.m = 6
        # Independent cell enumeration using the triangular-lattice quadratic form.
        self.cells = sorted((q,r) for q,r in product(range(-3,4),repeat=2)
                            if q*q+q*r+r*r <= 4)
        require(len(self.cells)==19,'cell count')
        self.index = {c:i for i,c in enumerate(self.cells)}
        m = self.m
        kept = []
        dropped = 0
        for c,(q,r) in enumerate(self.cells):
            center = (3*q*m,(q+2*r)*m)
            triangles = set()
            # Triangular lattice with horizontal base, rather than the producer's fan.
            def inside(p):
                x,y = p
                return abs(y)<=m and abs(x+y)<=2*m and abs(x-y)<=2*m
            for y in range(-m,m+1):
                for x in range(-2*m,2*m+1):
                    if (x-y)%2:
                        continue
                    for sign in (-1,1):
                        t = ((x,y),(x+2,y),(x+1,y+sign))
                        if all(inside(p) for p in t):
                            t = tuple(sorted((p[0]+center[0],p[1]+center[1]) for p in t))
                            triangles.add(t)
            require(len(triangles)==216,'mesh completeness')
            for t in sorted(triangles):
                if 2401*lower_squared_norm(t) > 3312400:
                    dropped += 1
                else:
                    kept.append((c,t))
        self.triangles = sorted(kept)
        self.groups = [0]*19
        for i,(c,t) in enumerate(self.triangles):
            self.groups[c] |= 1<<i
        self.dropped = dropped
        # Construct D6 from physical (X,Y) transformations, not axial recursion.
        permutations = []
        for mirror in (-1,1):
            for turns in range(6):
                perm = []
                for q,r in self.cells:
                    X,Y = 3*q, mirror*(q+2*r)
                    for _ in range(turns):
                        require((X-3*Y)%2==0 and (X+Y)%2==0,'rotation parity')
                        X,Y = (X-3*Y)//2,(X+Y)//2
                    require(X%3==0 and (Y-X//3)%2==0,'axial inverse')
                    perm.append(self.index[X//3,(Y-X//3)//2])
                permutations.append(tuple(perm))
        self.permutations = set(permutations)
        require(len(self.permutations)==12,'dihedral group')

    @lru_cache(maxsize=None)
    def adjacency(self,v):
        cell,t = self.triangles[v]
        result = 0
        for w,(other,u) in enumerate(self.triangles):
            if cell == other:
                continue
            for p in t:
                for q in u:
                    dx,dy = p[0]-q[0],p[1]-q[1]
                    if 2401*(dx*dx+3*dy*dy) >= 1440000:
                        result |= 1<<w
                        break
                else:
                    continue
                break
        return result


def transform(mask,perm):
    return sum(1<<perm[i] for i in bits(mask))

def validate_cover(manifest,g):
    require(manifest['schema']=='n9_hex_cover_v1','manifest schema')
    require(manifest['target_q']=='1105/256','target')
    require(manifest['hex_side']=='49/100','side')
    require(manifest['center_radius_bound']=='91/60','radius')
    require(manifest['cells']==[list(c) for c in g.cells],'cells changed')
    perms = [tuple(p) for p in manifest['symmetries']]
    require(len(perms)==12 and set(perms)==g.permutations,'missing or invalid symmetry')
    # Independently enumerate complementary ten-subsets, canonicalizing every one.
    full = (1<<19)-1
    expected = set()
    for omitted in combinations(range(19),10):
        mask = full ^ sum(1<<i for i in omitted)
        expected.add(min(transform(mask,p) for p in perms))
    require(len(expected)==7915,'independent root count')
    rows = manifest['roots']
    require(len(rows)==7915 and [r['mask'] for r in rows]==sorted(expected),'incomplete root cover')
    orbit_counts = Counter()
    for i,row in enumerate(rows):
        require(row['id']==i and row['cells']==list(bits(row['mask'])),'root identifiers')
        orbit_counts[len({transform(row['mask'],p) for p in perms})] += 1
    require(sum(k*v for k,v in orbit_counts.items())==92378,'unquotiented cover count')
    require(manifest['unquotiented_subsets']==92378,'raw count')
    require({int(k):v for k,v in manifest['orbit_size_counts'].items()}==dict(orbit_counts),'orbit table')
    # Independent Burnside count, using cycle-length generating polynomials.
    fixed = []
    for p in perms:
        unvisited = set(range(19)); lengths = []
        while unvisited:
            start = next(iter(unvisited)); v = start; length = 0
            while v in unvisited:
                unvisited.remove(v); length += 1; v = p[v]
            lengths.append(length)
        coefficients = [1]+[0]*19
        for length in lengths:
            for k in range(19,length-1,-1):
                coefficients[k] += coefficients[k-length]
        fixed.append(coefficients[9])
    require(sum(fixed)==12*7915,'Burnside count')
    return fixed


def replay(certificate,g):
    require(certificate['schema']=='n9_hex_center_exclusions_v1','certificate schema')
    require(certificate['subdivision']==6,'subdivision')
    nodes = certificate['nodes']
    memo = set(); reached = set(); checks = [0]
    def visit(node,state):
        state = tuple(sorted(state))
        checks[0] += 1
        require(type(node) is int and 0<=node<=len(nodes),'bad node reference')
        if node==0:
            require(any(d==0 for c,d in state),'false empty-domain leaf')
            return
        require(state and all(d!=0 for c,d in state),'nonterminal empty or feasible leaf')
        key = node,state
        if key in memo:
            return
        cell,children = nodes[node-1]
        domains = dict(state)
        require(cell in domains,'branching on absent cell')
        require([v for v,child in children]==list(bits(domains[cell])),'missing or duplicate branch')
        reached.add(node)
        rest = [(c,d) for c,d in state if c!=cell]
        for v,child in children:
            require(type(child) is int and 0<=child<node,'cyclic or forward proof edge')
            neighbors = g.adjacency(v)
            visit(child,[(c,d & neighbors) for c,d in rest])
        memo.add(key)
    for core in certificate['cores']:
        require(core['cells']==list(bits(core['mask'])),'core cell list')
        require(0<core['mask']<1<<19,'core mask')
        visit(core['proof_node'],[(c,g.groups[c]) for c in core['cells']])
    require(reached==set(range(1,len(nodes)+1)),'unreplayed proof nodes')
    return checks[0],len(memo)


def classify(manifest,certificate):
    patterns = [(k,j,transform(core['mask'],p)) for k,core in enumerate(certificate['cores'])
                for j,p in enumerate(manifest['symmetries'])]
    counts = Counter(); increments = [0]*len(certificate['cores'])
    for row in manifest['roots']:
        match = next(((k,j) for k,j,p in patterns if row['mask'] & p == p),None)
        if match is None:
            require(row['status']=='OPEN' and 'core' not in row and 'symmetry' not in row,'false root exclusion')
        else:
            require(row['status']=='EXCLUDED' and (row['core'],row['symmetry'])==match,'wrong exclusion transfer')
            increments[match[0]] += 1
        counts[row['status']] += 1
    require(manifest['global_lower_bound_proved'] is False,'unsupported global theorem flag')
    return dict(counts),increments


def sign_sqrt3(a,b):
    if b==0:return (a>0)-(a<0)
    if a==0:return (b>0)-(b<0)
    if (a>0)==(b>0):return (a>0)-(a<0)
    delta=a*a-3*b*b
    return ((a>0)-(a<0))*((delta>0)-(delta<0))

def witness_control(manifest,g):
    centers=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
    centers += [(F(x),-F(15,16)) for x in (-1,0,1)]
    centers += [(F(x,20),F(19,16)) for x in (-11,11)]
    poses=[(x,y,F(1),F(0)) if i<7 else (x,y,F(99,101),F(20,101))
           for i,(x,y) in enumerate(centers)]
    norms=[]
    for x,y,a,b in poses:
        require(a*a+b*b==1,'witness frame')
        for s,t in product((-1,1),repeat=2):
            X,Y=x+(s*a-t*b)/2,y+(s*b+t*a)/2
            norms.append(X*X+Y*Y)
    require(max(norms)==F(1105,256),'witness containment')
    for p,q in combinations(poses,2):
        x,y,a,b=p;X,Y,A,B=q
        C,S=a*A+b*B,a*B-b*A
        projections=[(X-x)*u+(Y-y)*v for u,v in ((a,b),(-b,a),(A,B),(-B,A))]
        require(2*max(map(abs,projections))>=1+abs(C)+abs(S),'witness pair')
    assignments=[]
    for x,y in centers:
        X=F(200,49)*x
        beta=F(200,147)*y  # Y=beta*sqrt(3)
        eligible=[]
        for i,(q,r) in enumerate(g.cells):
            values=[(-q-2*r,beta,1),(X-4*q-2*r,beta,2),(X-2*q+2*r,-beta,2)]
            if all(sign_sqrt3(bound-a,-b)>=0 and sign_sqrt3(bound+a,b)>=0 for a,b,bound in values):
                eligible.append(i)
        require(eligible,'witness uncovered by hexes')
        assignments.append(min(eligible))
    require(len(set(assignments))==9,'witness cell collision')
    mask=sum(1<<i for i in assignments)
    canonical=min(transform(mask,p) for p in manifest['symmetries'])
    root=next(r for r in manifest['roots'] if r['mask']==canonical)
    require(root['status']=='OPEN','equality witness falsely excluded')
    return {'assigned_cells':assignments,'canonical_root_id':root['id'],
            'canonical_mask':canonical,'max_squared_corner_norm':'1105/256'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--negative-controls',action='store_true')
    args=ap.parse_args();d=args.directory
    manifest=json.loads((d/'hex_root_manifest.json').read_text())
    raw=(d/'hex_exclusion_certificate.json').read_bytes();cert=json.loads(raw)
    require(hashlib.sha256(raw).hexdigest()==manifest['certificate_sha256'],'certificate hash')
    g=Geometry()
    require(F(91,60)**2+F(91,60)+F(1,2)-F(1105,256)==F(31,57600),'center margin')
    require(1-4*F(49,100)**2==F(99,2500)>0,'diameter margin')
    require(21*F(49,100)**2-(F(91,60)+F(49,100))**2==F(18277,18000)>0,'outer-ring margin')
    fixed=validate_cover(manifest,g)
    checked,states=replay(cert,g)
    counts,increments=classify(manifest,cert)
    witness=witness_control(manifest,g)
    negatives=[]
    if args.negative_controls:
        import copy
        def must_fail(name,fun):
            try:fun()
            except ValueError:negatives.append(name)
            else:raise ValueError('mutation accepted: '+name)
        missing=copy.deepcopy(manifest);missing['roots'].pop()
        must_fail('missing global root',lambda:validate_cover(missing,g))
        false=copy.deepcopy(manifest)
        next(r for r in false['roots'] if r['status']=='OPEN')['status']='EXCLUDED'
        must_fail('unproved root marked excluded',lambda:classify(false,cert))
        bad=copy.deepcopy(cert)
        # Removing an actual alternative must fail, even with a freshly valid hash.
        bad['nodes'][bad['cores'][0]['proof_node']-1][1].pop()
        must_fail('omitted proof child',lambda:replay(bad,g))
        bad=copy.deepcopy(cert);bad['cores'][0]['proof_node']=0
        must_fail('false contradiction at the root',lambda:replay(bad,g))
    report={'result':'PASS','arithmetic':'Python int and Fraction; independent verifier',
            'root_count':7915,'unquotiented_subsets':92378,'statuses':counts,
            'burnside_fixed_subset_counts':fixed,'fine_triangles_retained':len(g.triangles),
            'fine_triangles_discarded':g.dropped,'proof_nodes':len(cert['nodes']),
            'proof_visits':checked,'distinct_proof_contexts':states,
            'newly_excluded_roots_per_core':increments,'witness_control':witness,
            'negative_controls_rejected':negatives,'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'manifest_sha256':hashlib.sha256((d/'hex_root_manifest.json').read_bytes()).hexdigest(),
            'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'global_lower_bound_proved':False,'full_equality_classified':False,
            'separate_human_review_performed':False,'lean_or_ci_run':False}
    (d/'hex_verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

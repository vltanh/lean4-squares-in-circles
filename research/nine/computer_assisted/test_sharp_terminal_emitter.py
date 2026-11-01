#!/usr/bin/env python3
"""Exact emitted-text controls for the common-frame sharp-terminal interface.

These tests do not prove global chart coverage. The source proves the exact
coordinate transformation; the wide-slide manuscript supplies the terminal.
"""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import hashlib,json
from emit_sharp_terminal import build_terminal
from test_hex_root_emitter import K,parse,evaluate
from verify_hex_cover import require
HERE=Path(__file__).resolve().parent


def check_structure(model,root):
    variables,defs,predicates=parse(model.smt2())
    require(len(variables)==36+int(root),'unexpected extra variable/gauge')
    require(len(predicates)==130+56*int(root),'assertion count')
    require(sum(n.startswith('guard_') for n in predicates)==49,'guard cover')
    require(sum(n.startswith('corner_') for n in predicates)==36,'lost original corner')
    require(sum(n.startswith('pair_') for n in predicates)==36,'lost original pair')
    require(sum(n.startswith('unit_') for n in predicates)==9,'lost independent frame')
    require(sum(n.startswith('hex_') for n in predicates)==54*int(root),'lost hex guards')
    cache={}
    def degree(t):
        if isinstance(t,str):
            try:F(t);return 0
            except ValueError:pass
            if t in variables:return 1
            if t not in cache:cache[t]=degree(defs[t])
            return cache[t]
        ds=[degree(a) for a in t[1:]]
        return sum(ds) if t[0]=='*' else max(ds,default=0)
    require(max(degree(t) for t in predicates.values())<=2,'nonquadratic guard')
    return variables,defs,predicates


def base_poses(slide):
    cc=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
    cc += [(F(x),-F(15,16)) for x in (-1,0,1)]
    cc[5]=(cc[5][0],cc[5][1]+slide)
    cc += [(F(x,20),F(19,16)) for x in (-11,11)]
    return [tuple(map(K,(x,y,F(1) if i<7 else F(99,101),F(0) if i<7 else F(20,101))))
            for i,(x,y) in enumerate(cc)]


def physical(poses):
    def absolute(x):return x if x>=0 else -x
    norms=[]
    for x,y,a,b in poses:
        require(a*a+b*b==1,'physical unit')
        for s,t in product((-1,1),repeat=2):
            X=x+(s*a-t*b)*F(1,2);Y=y+(s*b+t*a)*F(1,2)
            norms.append(X*X+Y*Y)
    require(max(norms)==F(1105,256),'physical equality disk')
    for (x,y,a,b),(X,Y,A,B) in combinations(poses,2):
        C=a*A+b*B;S=a*B-b*A
        projections=[absolute((X-x)*u+(Y-y)*v) for u,v in ((a,b),(-b,a),(A,B),(-B,A))]
        require(2*max(projections)>=1+absolute(C)+absolute(S),'physical pair')


def transform(poses,turns,mirror):
    out=[]
    for x,y,a,b in poses:
        if mirror==-1:y,b=-y,-b
        for _ in range(turns):
            x,y=F(1,2)*x-K(0,F(1,2))*y,K(0,F(1,2))*x+F(1,2)*y
            a,b=F(1,2)*a-K(0,F(1,2))*b,K(0,F(1,2))*a+F(1,2)*b
        out.append((x,y,a,b))
    return out


def assign(poses):
    env={'sqrt_three':K(0,1)}
    for i,pose in enumerate(poses):env.update({f'{v}_{i}':z for v,z in zip(('x','y','a','b'),pose)})
    return env


def main():
    count=hex_count=0
    hexdata=json.loads((HERE/'hex_root_manifest.json').read_text())
    original_cells=(1,5,14,17,3,8,12,6,15)
    permutation=(4,8,2,6,0,7,3,5,1) # old square ID -> new square ID
    for slide,turns,mirror in product((F(0),F(-9,16)),range(6),(1,-1)):
        poses=transform(base_poses(slide),turns,mirror);physical(poses)
        for relabel in (False,True):
            selected=tuple(range(7));testposes=poses
            if relabel:
                testposes=[None]*9
                for i,p in enumerate(poses):testposes[permutation[i]]=p
                selected=tuple(permutation[i] for i in range(7))
            for radius in ('closed','strict'):
                _,defs,predicates=check_structure(build_terminal(selected,mirror,radius),False)
                env=assign(testposes)
                bad=[n for n,t in predicates.items() if not evaluate(t,env,defs)]
                if radius=='closed':require(not bad,'valid chart packing rejected')
                else:require(len(bad)==4 and all(n.startswith('corner_') for n in bad),'strict boundary')
                count+=1
        if slide==0:
            perm=hexdata['symmetries'][turns+(6 if mirror==-1 else 0)]
            pairs=sorted((perm[c],i,poses[i]) for i,c in enumerate(original_cells))
            row={'cells':[c for c,i,p in pairs]};testposes=[p for c,i,p in pairs]
            selected=tuple(next(j for j,(_,old,_) in enumerate(pairs) if old==i) for i in range(7))
            for radius in ('closed','strict'):
                _,defs,predicates=check_structure(build_terminal(selected,mirror,radius,row,hexdata['cells']),True)
                env=assign(testposes);bad=[n for n,t in predicates.items() if not evaluate(t,env,defs)]
                if radius=='closed':require(not bad,'fixed hex-root chart rejected')
                else:require(len(bad)==4 and all(n.startswith('corner_') for n in bad),'fixed root strict boundary')
                hex_count+=1
    # Test exact closed guard endpoints algebraically, independently of the
    # other square constraints. These assignments are not claimed packings.
    model=build_terminal(radius='closed');_,defs,predicates=check_structure(model,False)
    endpoints=0
    yintervals=[(F(-1,16),F(3,16)),(F(-1,16),F(3,4)),(F(-1,16),F(3,4)),
                (F(-1,16),F(3,16)),(F(-17,16),F(-13,16)),(F(-49,32),F(-13,16)),(F(-17,16),F(-13,16))]
    for i,(low,high) in enumerate(yintervals):
        for y in (low,high):
            env=assign(base_poses(F(0)));env[f'y_{i}']=K(y)
            require(all(evaluate(predicates[f'guard_y_{side}_{i}'],env,defs) for side in ('low','high')),'closed guard endpoint lost')
            endpoints+=1
    env=assign(base_poses(F(0)));env['y_1']=K(F(3,4)+F(1,1000))
    require(not evaluate(predicates['guard_y_high_1'],env,defs),'escaped guard accepted')
    env=assign(transform(base_poses(F(0)),1,-1))
    require(any(not evaluate(t,env,defs) for n,t in predicates.items() if n.startswith('guard_')),'wrong mirror accepted')
    rejects=0
    for selected,mirror in (((0,0,2,3,4,5,6),1),(tuple(range(7)),0),((0,1,2,3,4,5,9),1)):
        try:build_terminal(selected,mirror)
        except ValueError:rejects+=1
        else:raise ValueError('invalid interface accepted')
    report={'result':'PASS','arithmetic':'Fraction pairs in Q(sqrt(3))',
            'physical_witness_models_evaluated':count,'fixed_hex_root_models_evaluated':hex_count,
            'closed_vertical_guard_endpoints':endpoints,'invalid_interface_inputs_rejected':rejects,
            'wrong_mirror_and_escaped_guard_rejected':True,'all_original_pairs_retained':36,
            'chart_guards':49,'new_real_variables':0,'polynomial_degree_at_most':2,
            'independent_square_gauge_used':False,'global_coverage_proved':False,
            'scope':'sufficient terminal interface; finite regression tests, not global extraction',
            'source_sha256':{f:hashlib.sha256((HERE/f).read_bytes()).hexdigest() for f in
                             ('emit_sharp_terminal.py','test_sharp_terminal_emitter.py')},
            'lean_or_ci_run':False}
    (HERE/'sharp_terminal_emitter_test_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

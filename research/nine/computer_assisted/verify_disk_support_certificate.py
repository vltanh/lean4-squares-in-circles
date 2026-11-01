#!/usr/bin/env python3
"""Independent exact geometry and replay for disk-support certificates.

Reconstructs the old pose model independently, derives the new support bounds,
enumerates halfplane intersections rather than clipping, and checks every
propagation row and every root transfer. No producer or graph cache is trusted.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import argparse,hashlib,json,copy,gc
from square_pose_independent import reconstruct,graph_hash,require,CELLS
from disk_support_pose_independent import contract_independent
from verify_square_pose_certificate import replay_core, classify as check_prior
from test_hex_root_emitter import K
from verify_hex_cover import Geometry,validate_cover

HERE=Path(__file__).resolve().parent

def bits(mask):
    while mask:
        b=mask&-mask;mask-=b;yield b.bit_length()-1

def ka(x):return x if x>=0 else -x

def digest(obj):
    return hashlib.sha256((json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()

def witness_checks(g,perms):
    m=g['m'];k=g['k'];cap_checks=0;states={(t,o):v for v,(c,t,o) in enumerate(g['states'])}
    by_cell=[[] for c in CELLS]
    vertices=[]
    for t,(c,tri) in enumerate(g['triangles']):
        by_cell[c].append(t)
        vertices.append([(K(F(49*X,200*m)),K(0,F(49*Y,200*m))) for X,Y in tri])
    def contained(p,t):
        signs=[]
        for i in range(3):
            a,b=vertices[t][i],vertices[t][(i+1)%3]
            signs.append(((b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])).sign())
        return min(signs)>=0 or max(signs)<=0
    def locate(pose,cell=None):
        nonlocal cap_checks
        x,y,a,b=pose
        for _ in range(4):
            if a>=0 and b>=0:break
            a,b=-b,a
        require(a>=0 and b>=0 and a*a+b*b==1,'normalized frame')
        angles=[o for o in range(k) if K(o)*(1+a)<=k*b<=K(o+1)*(1+a)]
        require(angles,'uncovered angle')
        for o in angles:
            for j,(nx,ny) in enumerate(g['contraction']['normals']):
                require((nx*x+ny*y)*g['denominator']<=K(g['contraction']['rhs'][o][j]),
                        'actual center rejected by support halfplane')
                cap_checks+=1
        if cell is None:
            X=x*F(200,49);Y=y*K(0,F(200,147))
            choices=[c for c,(q,r) in enumerate(CELLS)
                     if ka(Y-(q+2*r))<=1 and ka(X+Y-(4*q+2*r))<=2 and ka(X-Y-(2*q-2*r))<=2]
        else:choices=[cell]
        require(choices,'uncovered center cell')
        selected=[]
        for c in choices:
            for t in by_cell[c]:
                if contained((x,y),t):
                    for o in angles:
                        require((t,o) in states,'valid pose removed by unary filter')
                        require(g['groups'][c]>>states[t,o]&1,'actual unary state removed by contraction')
                        selected.append(states[t,o])
        require(selected,'uncovered actual pose')
        return min(selected)
    def check_pose(p):
        x,y,a,b=p
        require(a*a+b*b==1,'nonunit witness')
        for s in (-1,1):
            for t in (-1,1):
                X=x+F(1,2)*(s*a-t*b);Y=y+F(1,2)*(s*b+t*a)
                require(X*X+Y*Y<=K(F(1105,256)),'escaped witness corner')
    centers=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
    centers += [(F(x),-F(15,16)) for x in (-1,0,1)]
    centers += [(F(x,20),F(19,16)) for x in (-11,11)]
    poses=[tuple(map(K,(x,y,F(1) if i<7 else F(99,101),F(0) if i<7 else F(20,101))))
           for i,(x,y) in enumerate(centers)]
    occupied=[1,5,14,17,3,8,12,6,15]
    def rot(x,y):return F(1,2)*x-K(0,F(1,2))*y,K(0,F(1,2))*x+F(1,2)*y
    for si,perm in enumerate(perms):
        chosen=[]
        for cell,pose in zip(occupied,poses):
            x,y,a,b=pose
            if si>=6:y,b=-y,-b
            for _ in range(si%6):x,y=rot(x,y);a,b=rot(a,b)
            check_pose((x,y,a,b));chosen.append(locate((x,y,a,b),perm[cell]))
        for v,w in combinations(chosen,2):require(g['adjacency'][v]>>w&1,'equality witness edge removed')
    touching=0
    for t in [F(i,2*k) for i in range(2*k+1)]:
        a,b=K((1-t*t)/(1+t*t)),K(2*t/(1+t*t))
        p=(-F(1,2)*a,-F(1,2)*b,a,b);q=(F(1,2)*a,F(1,2)*b,a,b)
        check_pose(p);check_pose(q)
        v,w=locate(p),locate(q)
        require(g['adjacency'][v]>>w&1,'weak touching pair removed')
        touching+=1
    return {'equality_symmetries':12,'equality_pair_controls':432,
            'touching_pair_controls':touching,'all_angle_endpoints_retained':True,'exact_support_plane_controls':cap_checks}

def rational_square_controls(g):
    """Exact actual squares at all arc endpoints and midpoints; no sampling proof."""
    k=g['k'];D=g['denominator'];number=0
    centers=set()
    for a,b in ((F(3,2),F(1,16)),(F(1),F(15,16)),(F(3,2),F(0)),(F(0),F(0))):
        for sx in (-1,1):
            for sy in (-1,1):
                centers.add((sx*a,sy*b));centers.add((sy*b,sx*a))
    for i in range(2*k+1):
        t=F(i,2*k);a,b=(1-t*t)/(1+t*t),2*t/(1+t*t)
        arcs=[o for o in range(k) if F(o,k)<=t<=F(o+1,k)]
        for X,Y in centers:
            require((abs(X)+F(1,2))**2+(abs(Y)+F(1,2))**2<=F(1105,256),'control square containment')
            x,y=a*X-b*Y,b*X+a*Y
            for o in arcs:
                for j,(nx,ny) in enumerate(g['contraction']['normals']):
                    require(D*(nx*x+ny*y)<=g['contraction']['rhs'][o][j],'physical square violates support table')
                    number+=1
    return number

def validate_parameters(certificate):
    require(certificate['schema']=='n9_disk_support_certificate_v1','certificate schema')
    require(certificate['target_q']=='1105/256' and certificate['physical_scope']=='q<=Q','physical scope')
    require(certificate['scale']==2**20 and certificate['normal_grid']==4,'support domain constants')
    require(certificate['support_scheme']=='exact-center-support-v1','support bound semantics')
    parameters=[(f['mesh'],f['angle_bins']) for f in certificate['families']]
    require(len(parameters)==len(set(parameters)) and all(m in (6,8) and k in (12,24) for m,k in parameters),'geometry family list')

def check_roots(certificate,manifest,prior,hex_manifest):
    require(manifest['schema']=='n9_disk_support_roots_v1' and manifest['target_q']=='1105/256','root schema')
    require(len(manifest['roots'])==7915,'missing global root')
    patterns=[]
    for fi,family in enumerate(certificate['families']):
        for ci,core in enumerate(family['cores']):
            for si,p in enumerate(hex_manifest['symmetries']):
                patterns.append((fi,ci,si,sum(1<<p[c] for c in core['cells'])))
    counts=Counter();increments=Counter()
    for row,old in zip(manifest['roots'],prior['roots']):
        expected={key:old[key] for key in ('id','mask','cells')}
        if old['status']=='EXCLUDED':
            expected.update(status='EXCLUDED',evidence='prior_square_pose',
                            family=old['family'],core=old['core'],symmetry=old['symmetry'])
        else:
            matches=[(f,c,s) for f,c,s,p in patterns if row['mask']&p==p]
            if not matches:expected['status']='OPEN'
            else:
                f,c,s=matches[0]
                expected.update(status='EXCLUDED',evidence='disk_support',family=f,core=c,symmetry=s)
                increments[f,c]+=1
        require(row==expected,'changed root or unsupported exclusion transfer')
        counts[row['status']]+=1
    require(manifest['roots'][7820]['mask']==177242 and manifest['roots'][7820]['status']=='OPEN','equality root removed')
    require(manifest['global_lower_bound_proved'] is False and manifest['equality_classified'] is False,'false completion flag')
    return dict(counts),[dict(family=f,core=c,new_roots=n) for (f,c),n in sorted(increments.items())]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,default=HERE)
    ap.add_argument('--negative-controls',action='store_true')
    args=ap.parse_args();d=args.directory
    hex_raw=(d/'hex_root_manifest.json').read_bytes();hex_manifest=json.loads(hex_raw)
    prior_raw=(d/'square_pose_root_manifest.json').read_bytes();prior=json.loads(prior_raw)
    old_raw=(d/'square_pose_certificate.json').read_bytes();old=json.loads(old_raw)
    raw=(d/'disk_support_certificate.json').read_bytes();certificate=json.loads(raw)
    roots_raw=(d/'disk_support_root_manifest.json').read_bytes();manifest=json.loads(roots_raw)
    require(prior['baseline_manifest_sha256']==hashlib.sha256(hex_raw).hexdigest(),'prior baseline hash')
    require(prior['certificate_sha256']==hashlib.sha256(old_raw).hexdigest(),'prior certificate hash')
    require(manifest['prior_manifest_sha256']==hashlib.sha256(prior_raw).hexdigest(),'prior manifest hash')
    require(manifest['certificate_sha256']==hashlib.sha256(raw).hexdigest(),'certificate hash')
    validate_parameters(certificate);validate_cover(hex_manifest,Geometry())
    prior_counts,_=check_prior(old,prior,hex_manifest)
    require(prior_counts=={'EXCLUDED':886,'OPEN':7029},'prior statuses changed')
    pending={(f['mesh'],f['angle_bins']):f for f in old['families']}
    summaries=[];negatives=[];prior_replays=0
    def reject(name,fun):
        try:fun()
        except (ValueError,KeyError,IndexError):negatives.append(name)
        else:raise ValueError('mutation accepted: '+name)
    for family in certificate['families']:
        m,k=family['mesh'],family['angle_bins'];base=reconstruct(m,k)
        base_hash=graph_hash(base['adjacency'])
        require(base_hash==family['base_graph_sha256'],'old geometry mismatch')
        if (m,k) in pending:
            previous=pending.pop((m,k));require(base_hash==previous['graph_sha256'],'prior graph fingerprint')
            for core in previous['cores']:replay_core(core,base);prior_replays+=1
        g=contract_independent(base)
        require(len(base['states'])==family['base_states'] and len(base['triangles'])==family['position_triangles'],'base counts')
        require(sum(mask.bit_count() for mask in g['groups'])==family['live_states'],'live state count')
        require(len(g['contraction']['polygons'])==family['contracted_polygons'],'polygon count')
        gh=graph_hash(g['adjacency']);require(gh==family['graph_sha256'],'independent contracted graph mismatch')
        metadata_hash=digest(g['contraction']);require(metadata_hash==family['geometry_sha256'],'independent polygon/bound table mismatch')
        deletions=sum(replay_core(core,g) for core in family['cores'])
        controls=witness_checks(g,hex_manifest['symmetries'])
        controls['rational_physical_square_plane_tests']=rational_square_controls(g)
        if args.negative_controls:
            bad=copy.deepcopy(family['cores'][0]);bad['steps'].pop()
            reject(f'missing terminal row {m}/{k}',lambda:replay_core(bad,g))
            bad=copy.deepcopy(family['cores'][0]);bad['steps'][0][1][0][2]+=1
            reject(f'corrupted domain count {m}/{k}',lambda:replay_core(bad,g))
            bad=copy.deepcopy(family['cores'][0]);bad['mask']^=1<<18
            reject(f'inconsistent core identity {m}/{k}',lambda:replay_core(bad,g))
        summaries.append(dict(mesh=m,angle_bins=k,base_states=len(base['states']),
                              live_states=family['live_states'],contracted_polygons=family['contracted_polygons'],
                              position_triangles=len(base['triangles']),core_count=len(family['cores']),
                              propagation_rows=sum(len(c['steps']) for c in family['cores']),
                              candidate_deletions=deletions,graph_sha256=gh,geometry_sha256=metadata_hash,controls=controls))
        print('INDEPENDENTLY VERIFIED',m,k,'cores',len(family['cores']),flush=True)
        del base,g;gc.collect()
    # Prior evidence is fully replayed even if the new selected cores omit a family.
    for (m,k),family in pending.items():
        g=reconstruct(m,k);require(graph_hash(g['adjacency'])==family['graph_sha256'],'remaining prior graph')
        for core in family['cores']:replay_core(core,g);prior_replays+=1
        del g;gc.collect()
    counts,increments=check_roots(certificate,manifest,prior,hex_manifest)
    if args.negative_controls:
        bad=copy.deepcopy(manifest);bad['roots'][7820]['status']='EXCLUDED'
        reject('false equality-root exclusion',lambda:check_roots(certificate,bad,prior,hex_manifest))
        bad=copy.deepcopy(manifest);bad['roots'].pop()
        reject('omitted original root',lambda:check_roots(certificate,bad,prior,hex_manifest))
        bad=copy.deepcopy(manifest);bad['roots'][0]['mask']^=1
        reject('changed original root mask',lambda:check_roots(certificate,bad,prior,hex_manifest))
        bad=copy.deepcopy(certificate);bad['normal_grid']=3
        reject('altered support domain',lambda:validate_parameters(bad))
        bad=copy.deepcopy(certificate);bad['support_scheme']='unproved'
        reject('unproved support semantics',lambda:validate_parameters(bad))
    names=['square_pose_graph.py','square_pose_independent.py','disk_support_pose_graph.py',
           'disk_support_pose_independent.py','make_disk_support_certificate.py','verify_disk_support_certificate.py']
    report=dict(result='PASS',arithmetic='Python int/Fraction plus bounded NumPy int64; no floating comparisons',
                families=summaries,root_count=7915,statuses=counts,previous_excluded=886,
                newly_excluded=counts['EXCLUDED']-886,prior_cores_replayed=prior_replays,
                core_count=sum(f['core_count'] for f in summaries),
                propagation_rows=sum(f['propagation_rows'] for f in summaries),core_increments=increments,
                negative_controls_rejected=negatives,certificate_sha256=hashlib.sha256(raw).hexdigest(),
                manifest_sha256=hashlib.sha256(roots_raw).hexdigest(),
                source_sha256={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
                global_lower_bound_proved=False,full_equality_classified=False,
                separate_human_review_performed=False,lean_or_ci_run=False)
    (d/'disk_support_verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='core_increments'},indent=2))

if __name__=='__main__':main()

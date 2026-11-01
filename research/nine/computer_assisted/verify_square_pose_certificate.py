#!/usr/bin/env python3
"""Independent exact replay of square-pose exclusions, not global optimality.

Rebuilds the complete compatibility graph with square_pose_independent.py;
never imports the new producer. Replays domain deletions candidate-by-candidate,
rather than using the producer's neighbor-union algorithm. Verifies all root
transfers and exact Q(sqrt(3)) physical witness controls. NumPy computations in
the separate graph builder use only explicitly bounded int64 arithmetic.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import argparse,hashlib,json,copy
from square_pose_independent import reconstruct,graph_hash,require,CELLS
from test_hex_root_emitter import K
from verify_hex_cover import Geometry,validate_cover

HERE=Path(__file__).resolve().parent

def bits(mask):
    while mask:
        bit=mask&-mask;mask-=bit;yield bit.bit_length()-1

def replay_core(core,g):
    cells=core['cells'];mask=core['mask']
    require(cells==list(bits(mask)) and cells and 0<mask<1<<19,'invalid core cells')
    domains={c:g['groups'][c] for c in cells}
    require(all(domains.values()),'initial empty domain unsupported')
    for source,expected in core['steps']:
        require(source in domains and all(domains.values()),'bad propagation source/state')
        origin=domains[source];changes=[]
        for c in cells:
            if c==source:continue
            # A candidate survives iff it has some neighbor in the source domain.
            new=sum(1<<v for v in bits(domains[c]) if g['adjacency'][v]&origin)
            if new!=domains[c]:
                changes.append([c,domains[c].bit_count(),new.bit_count()]);domains[c]=new
        require(changes and changes==expected,'propagation table mismatch')
    empty=[c for c in cells if not domains[c]]
    require(empty and core['empty_cell']==min(empty),'no proved empty domain')
    return sum(before-after for source,change in core['steps'] for c,before,after in change)

def classify(certificate,manifest,baseline):
    require(manifest['schema']=='n9_square_pose_roots_v1','root schema')
    require(manifest['target_q']=='1105/256','target changed')
    require(len(manifest['roots'])==7915,'missing root')
    patterns=[]
    for f,family in enumerate(certificate['families']):
        for c,core in enumerate(family['cores']):
            for s,p in enumerate(baseline['symmetries']):
                patterns.append((f,c,s,sum(1<<p[i] for i in core['cells'])))
    count=Counter();increments=Counter()
    for new,old in zip(manifest['roots'],baseline['roots']):
        require(all(new[k]==old[k] for k in ('id','mask','cells')),'root ID changed')
        matches=[(f,c,s) for f,c,s,p in patterns if new['mask']&p==p]
        if matches:
            require(new['status']=='EXCLUDED','missing proved exclusion')
            require((new['family'],new['core'],new['symmetry'])==matches[0],'wrong core transfer')
            increments[matches[0][:2]]+=1
        else:require(new=={**{k:old[k] for k in ('id','mask','cells')},'status':'OPEN'},'unsupported exclusion')
        if old['status']=='EXCLUDED':require(new['status']=='EXCLUDED','old exclusion lost')
        count[new['status']]+=1
    require(manifest['global_lower_bound_proved'] is False and manifest['equality_classified'] is False,'unsupported global claim')
    require(manifest['roots'][7820]['mask']==177242 and manifest['roots'][7820]['status']=='OPEN','equality root excluded')
    return dict(count),[{'family':f,'core':c,'new_roots':n} for (f,c),n in sorted(increments.items())]

def ka(x):return x if x>=0 else -x

def witness_checks(g,perms):
    m=g['m'];states={(t,o):v for v,(c,t,o) in enumerate(g['states'])}
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
        x,y,a,b=pose
        for _ in range(4):
            if a>=0 and b>=0:break
            a,b=-b,a
        require(a>=0 and b>=0 and a*a+b*b==1,'normalized frame')
        angles=[o for o in range(12) if K(o)*(1+a)<=12*b<=K(o+1)*(1+a)]
        require(angles,'uncovered angle')
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
    for t in [F(i,24) for i in range(25)]:
        a,b=K((1-t*t)/(1+t*t)),K(2*t/(1+t*t))
        p=(-F(1,2)*a,-F(1,2)*b,a,b);q=(F(1,2)*a,F(1,2)*b,a,b)
        check_pose(p);check_pose(q)
        v,w=locate(p),locate(q)
        require(g['adjacency'][v]>>w&1,'weak touching pair removed')
        touching+=1
    return {'equality_symmetries':12,'equality_pair_controls':432,
            'touching_pair_controls':touching,'all_angle_endpoints_retained':True}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,default=HERE)
    ap.add_argument('--negative-controls',action='store_true')
    args=ap.parse_args();d=args.directory
    base_raw=(d/'hex_root_manifest.json').read_bytes();base=json.loads(base_raw)
    cert_raw=(d/'square_pose_certificate.json').read_bytes();cert=json.loads(cert_raw)
    out_raw=(d/'square_pose_root_manifest.json').read_bytes();manifest=json.loads(out_raw)
    require(cert['schema']=='n9_square_pose_certificate_v1' and cert['scale']==2**20,'certificate schema/scale')
    require(cert['target_q']=='1105/256' and cert['physical_scope']=='q<=Q','certificate scope')
    require(manifest['baseline_manifest_sha256']==hashlib.sha256(base_raw).hexdigest(),'baseline hash')
    require(manifest['certificate_sha256']==hashlib.sha256(cert_raw).hexdigest(),'certificate hash')
    validate_cover(base,Geometry())
    summaries=[];negatives=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,KeyError,IndexError):negatives.append(name)
        else:raise ValueError('mutation accepted: '+name)
    for family in cert['families']:
        g=reconstruct(family['mesh'],family['angle_bins'])
        require(len(g['states'])==family['states'] and len(g['triangles'])==family['position_triangles'],'pose cover counts')
        digest=graph_hash(g['adjacency']);require(digest==family['graph_sha256'],'independent graph mismatch')
        removed=sum(replay_core(core,g) for core in family['cores'])
        controls=witness_checks(g,base['symmetries'])
        if args.negative_controls:
            bad=copy.deepcopy(family['cores'][0]);bad['steps'].pop()
            reject('missing terminal propagation m='+str(g['m']),lambda:replay_core(bad,g))
            bad=copy.deepcopy(family['cores'][0]);bad['steps'][0][1][0][2]+=1
            reject('corrupted survivor count m='+str(g['m']),lambda:replay_core(bad,g))
            bad=copy.deepcopy(family['cores'][0]);bad['steps'][0][0]=19
            reject('nonexistent source cell m='+str(g['m']),lambda:replay_core(bad,g))
        summaries.append({'mesh':g['m'],'angle_bins':g['k'],'states':len(g['states']),
                          'position_triangles':len(g['triangles']),'core_count':len(family['cores']),
                          'propagation_steps':sum(len(c['steps']) for c in family['cores']),
                          'candidate_deletions':removed,'graph_sha256':digest,'controls':controls})
        print('VERIFIED FAMILY',g['m'],len(family['cores']),flush=True)
        del g
    counts,increments=classify(cert,manifest,base)
    if args.negative_controls:
        bad=copy.deepcopy(manifest);bad['roots'][7820]['status']='EXCLUDED'
        reject('false equality-root exclusion',lambda:classify(cert,bad,base))
        bad=copy.deepcopy(manifest);bad['roots'].pop()
        reject('omitted global root',lambda:classify(cert,bad,base))
        bad=copy.deepcopy(manifest);bad['roots'][0]['mask']^=1
        reject('changed root identity',lambda:classify(cert,bad,base))
    report={'result':'PASS','arithmetic':'Python int/Fraction and bounded NumPy int64; no floats',
            'families':summaries,'root_count':7915,'statuses':counts,
            'previous_excluded':81,'newly_excluded':counts['EXCLUDED']-81,
            'core_increments':increments,'negative_controls_rejected':negatives,
            'certificate_sha256':hashlib.sha256(cert_raw).hexdigest(),
            'manifest_sha256':hashlib.sha256(out_raw).hexdigest(),
            'source_sha256':{p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in
                             ['square_pose_graph.py','square_pose_independent.py','make_square_pose_certificate.py','verify_square_pose_certificate.py']},
            'global_lower_bound_proved':False,'full_equality_classified':False,
            'separate_human_review_performed':False,'lean_or_ci_run':False}
    (d/'square_pose_verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='core_increments'},indent=2))

if __name__=='__main__':main()

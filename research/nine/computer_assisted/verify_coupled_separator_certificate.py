#!/usr/bin/env python3
"""Fresh independent replay of the full dependency chain and new refutations.

No graph cache is read. All meshes, contracted polygons and separator graphs are
rebuilt using the independent geometry implementations. All core inferences are
checked candidate-by-candidate. An unknown or incomplete branch is rejected.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from itertools import product
import argparse, copy, gc, hashlib, json, time
from square_pose_independent import reconstruct, graph_hash, require
from disk_support_pose_independent import contract_independent
from coupled_separator_independent import refine_independent
from verify_hex_cover import Geometry, validate_cover
from verify_square_pose_certificate import replay_core, classify as classify_square
from coupled_controls import witness_checks
HERE=Path(__file__).resolve().parent


def data_bytes(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(x):return hashlib.sha256(data_bytes(x)).hexdigest()
def bits(x):
    while x:
        a=x&-x;x-=a;yield a.bit_length()-1


def metadata_hash(k):
    # Solve tangents independently, then verify the canonical unreduced encoding.
    ends=[(F(k*k-i*i,k*k+i*i),F(2*k*i,k*k+i*i)) for i in range(k+1)]
    arcs=[];thresholds=[];coefficients=[];D=2**20
    for i in range(k):
        p,q=ends[i:i+2];det=p[0]*q[1]-p[1]*q[0]
        require(det>0,'angle interval')
        tan=((q[1]-p[1])/det,(p[0]-q[0])/det)
        denominators=(k*k+i*i,k*k+i*(i+1),k*k+(i+1)**2)
        raw=[];tt=[];cc=[]
        for z,den in zip((p,tan,q),denominators):
            x,y=z[0]*den,z[1]*den
            require(x.denominator==y.denominator==1,'canonical arc encoding')
            a,b=int(x),int(y);raw.append([a,b,den])
            bounds=[]
            for j in range(k):
                if j==i:value=F(2)
                else:
                    vals=[]
                    for w in ends[j:j+2]:
                        dot=z[0]*w[0]+z[1]*w[1];cross=z[0]*w[1]-z[1]*w[0]
                        vals.append(1+dot+(cross if i<j else -cross))
                    value=min(vals)
                v=value*D*D;bounds.append(v.numerator//v.denominator)
            tt.extend((bounds,bounds));cc.extend(((a,b,den),(-b,a,den)))
        arcs.append(raw);thresholds.append(tt);coefficients.append(cc)
    return digest({'scheme':'coupled-endpoint-tangent-v1','scale':D,'arc_vertices':arcs,
                   'thresholds':thresholds,'coefficients':coefficients})


def replay_tree(core,g):
    require(set(core)=={'mask','cells','root','nodes'},'core fields')
    cells=core['cells'];mask=core['mask'];nodes=core['nodes']
    require(type(mask) is int and 0<mask<1<<19 and cells==list(bits(mask)),'core identity')
    require(nodes and type(core['root']) is int and core['root']==len(nodes)-1,'root index')
    reached=set();memo=set();visits=0;deletions=0
    def visit(index,domains):
        nonlocal visits,deletions
        require(type(index) is int and 0<=index<len(nodes),'node index')
        key=index,tuple(domains[c] for c in cells)
        if key in memo:return
        memo.add(key);reached.add(index);visits+=1
        node=nodes[index]
        allowed=({'propagate','empty_cell'} if 'empty_cell' in node else
                 {'propagate','split_cell','cutoff','left','right'})
        require(set(node)==allowed,'incomplete or unsupported proof node')
        domains=dict(domains)
        for source,expected in node['propagate']:
            require(source in domains and all(domains.values()),'invalid propagation state')
            support_domain=domains[source];actual=[]
            for c in cells:
                if c==source:continue
                # Opposite algorithm from producer union-of-neighbors.
                survivors=0
                for v in bits(domains[c]):
                    if g['adjacency'][v]&support_domain:survivors|=1<<v
                if survivors!=domains[c]:
                    before,after=domains[c].bit_count(),survivors.bit_count()
                    actual.append([c,before,after]);deletions+=before-after
                    domains[c]=survivors
            require(actual and actual==expected,'false propagation row')
        if 'empty_cell' in node:
            empty=[c for c in cells if domains[c]==0]
            require(empty and node['empty_cell']==min(empty),'false contradiction')
            return
        c=node['split_cell'];cut=node['cutoff']
        require(c in domains and all(domains.values()),'split on invalid state')
        require(type(cut) is int and 0<=cut<len(g['states']),'invalid cutoff')
        left,right=node['left'],node['right']
        require(type(left) is int and type(right) is int and 0<=left<index and 0<=right<index,'missing or cyclic child')
        # Filter the actual finite state IDs, rather than assuming a bit mask partition.
        a=sum(1<<v for v in bits(domains[c]) if v<=cut)
        b=sum(1<<v for v in bits(domains[c]) if v>cut)
        require(a and b and not(a&b) and (a|b)==domains[c],'nonexhaustive or empty split')
        L=dict(domains);L[c]=a;R=dict(domains);R[c]=b
        visit(left,L);visit(right,R)
    start={c:g['groups'][c] for c in cells}
    require(all(start.values()),'unsupported initial empty state')
    visit(core['root'],start)
    require(reached==set(range(len(nodes))),'unreplayed nodes')
    return {'visits':visits,'candidate_deletions':deletions}


def patterns(cert,base):
    return [(f,c,s,sum(1<<p[v] for v in core['cells']))
            for f,family in enumerate(cert['families']) for c,core in enumerate(family['cores'])
            for s,p in enumerate(base['symmetries'])]


def classify_disk(cert,manifest,prior,base):
    require(manifest['schema']=='n9_disk_support_roots_v1','disk manifest schema')
    require(manifest['target_q']=='1105/256','disk target')
    require(len(manifest['roots'])==len(prior['roots'])==7915,'disk root cover')
    pats=patterns(cert,base);counts=Counter()
    for new,old in zip(manifest['roots'],prior['roots']):
        expected={k:old[k] for k in ('id','mask','cells')}
        if old['status']=='EXCLUDED':
            expected.update(status='EXCLUDED',evidence='prior_square_pose',
                            family=old['family'],core=old['core'],symmetry=old['symmetry'])
        else:
            match=next(((f,c,s) for f,c,s,p in pats if old['mask']&p==p),None)
            if match is None:expected['status']='OPEN'
            else:expected.update(status='EXCLUDED',evidence='disk_support',family=match[0],core=match[1],symmetry=match[2])
        require(new==expected,'invalid disk proof transfer');counts[new['status']]+=1
    require(manifest['global_lower_bound_proved'] is False and manifest['equality_classified'] is False,'disk global flags')
    return dict(counts)


def classify_new(cert,manifest,prior,base):
    require(manifest['schema']=='n9_coupled_separator_roots_v1' and manifest['target_q']=='1105/256','new manifest semantics')
    require(len(manifest['roots'])==len(prior['roots'])==7915,'missing original root')
    pats=patterns(cert,base);counts=Counter();increments=Counter()
    for row,old in zip(manifest['roots'],prior['roots']):
        expected={k:old[k] for k in ('id','mask','cells')}
        if old['status']=='EXCLUDED':expected.update(status='EXCLUDED',evidence='prior_disk_support',prior_root=old['id'])
        else:
            match=next(((f,c,s) for f,c,s,p in pats if old['mask']&p==p),None)
            if match is None:expected['status']='OPEN'
            else:
                expected.update(status='EXCLUDED',evidence='coupled_separator',family=match[0],core=match[1],symmetry=match[2])
                increments[match[:2]]+=1
        require(row==expected,'unsupported root transfer or changed identity');counts[row['status']]+=1
    require(manifest['roots'][7820]['mask']==177242 and manifest['roots'][7820]['status']=='OPEN','attaining root excluded')
    require(manifest['global_lower_bound_proved'] is False and manifest['equality_classified'] is False,'unsupported global claim')
    return dict(counts),[{'family':f,'core':c,'new_roots':n} for (f,c),n in sorted(increments.items())]


def semantics(cert):
    require(cert['schema']=='n9_coupled_separator_certificate_v1','certificate schema')
    require(cert['target_q']=='1105/256' and cert['physical_scope']=='q<=Q','radius scope')
    require(cert['scale']==2**20 and cert['support_scheme']=='exact-center-support-v1','support domain')
    require(cert['separator_scheme']=='coupled-endpoint-tangent-v1','separator semantics')
    require([(f['mesh'],f['angle_bins']) for f in cert['families']]==[(6,12),(6,24)],'family cover inputs')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--directory',type=Path,default=HERE)
    ap.add_argument('--negative-controls',action='store_true');args=ap.parse_args();d=args.directory
    def read(name):
        raw=(d/name).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
    base,_=read('hex_root_manifest.json');sq,sh=read('square_pose_certificate.json');sm,smh=read('square_pose_root_manifest.json')
    disk,dh=read('disk_support_certificate.json');dm,dmh=read('disk_support_root_manifest.json')
    cert,ch=read('coupled_separator_certificate.json');manifest,mh=read('coupled_separator_root_manifest.json')
    semantics(cert)
    require(sm['certificate_sha256']==sh and dm['certificate_sha256']==dh,'prior certificate hashes')
    require(dm['prior_manifest_sha256']==smh and manifest['prior_manifest_sha256']==dmh,'dependency manifests')
    require(manifest['certificate_sha256']==ch,'new certificate hash')
    require(disk['schema']=='n9_disk_support_certificate_v1' and disk['target_q']=='1105/256'
            and disk['physical_scope']=='q<=Q' and disk['scale']==2**20 and disk['normal_grid']==4
            and disk['support_scheme']=='exact-center-support-v1','prior disk semantics')
    require(sq['schema']=='n9_square_pose_certificate_v1' and sq['target_q']=='1105/256'
            and sq['physical_scope']=='q<=Q' and sq['scale']==2**20,'prior square semantics')
    require(sm['baseline_manifest_sha256']==hashlib.sha256((d/'hex_root_manifest.json').read_bytes()).hexdigest(),'hex dependency hash')
    validate_cover(base,Geometry())
    negatives=[];families=[];prior_square=prior_disk=0
    def rejects(label,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError):negatives.append(label)
        else:raise ValueError('mutation accepted: '+label)
    for m,k in ((6,12),(8,12),(6,24)):
        start=time.time();print('FRESH INDEPENDENT BASE',m,k,flush=True);g=reconstruct(m,k)
        sf=next((f for f in sq['families'] if (f['mesh'],f['angle_bins'])==(m,k)),None)
        if sf:
            require(graph_hash(g['adjacency'])==sf['graph_sha256'],'old square graph differs')
            for c in sf['cores']:replay_core(c,g);prior_square+=1
        df=next(f for f in disk['families'] if (f['mesh'],f['angle_bins'])==(m,k))
        require(graph_hash(g['adjacency'])==df['base_graph_sha256'],'disk base graph')
        print('FRESH INDEPENDENT DISK',m,k,flush=True);g=contract_independent(g)
        require(graph_hash(g['adjacency'])==df['graph_sha256'] and digest(g['contraction'])==df['geometry_sha256'],'disk geometry')
        require(sum(v.bit_count() for v in g['groups'])==df['live_states'],'disk live count')
        for c in df['cores']:replay_core(c,g);prior_disk+=1
        nf=next((f for f in cert['families'] if (f['mesh'],f['angle_bins'])==(m,k)),None)
        if nf:
            require(graph_hash(g['adjacency'])==nf['disk_graph_sha256'],'new disk dependency')
            print('FRESH COUPLED GRAPH',m,k,flush=True);g=refine_independent(g)
            require(graph_hash(g['adjacency'])==nf['graph_sha256'],'new graph differs')
            require(metadata_hash(k)==nf['separator_metadata_sha256'],'coupled coefficients')
            require(len(g['states'])==nf['states'] and sum(v.bit_count() for v in g['groups'])==nf['live_states'],'new state count')
            totals=[replay_tree(c,g) for c in nf['cores']]
            controls=witness_checks(g,base['symmetries'])
            if args.negative_controls:
                terminal=next(c for c in nf['cores'] if len(c['nodes'])==1)
                bad=copy.deepcopy(terminal);bad['nodes'][0]['propagate'].pop()
                rejects('missing terminal row '+str(k),lambda:replay_tree(bad,g))
                bad=copy.deepcopy(terminal);bad['nodes'][0]['propagate'][0][1][0][2]+=1
                rejects('wrong candidate count '+str(k),lambda:replay_tree(bad,g))
                bad=copy.deepcopy(terminal);bad['mask']^=1
                rejects('changed core identity '+str(k),lambda:replay_tree(bad,g))
                branch=next(c for c in nf['cores'] if any('split_cell' in n for n in c['nodes']))
                bad=copy.deepcopy(branch);n=next(n for n in bad['nodes'] if 'split_cell' in n);del n['right']
                rejects('missing exhaustive child '+str(k),lambda:replay_tree(bad,g))
                bad=copy.deepcopy(branch);n=next(n for n in bad['nodes'] if 'split_cell' in n);n['cutoff']=len(g['states'])
                rejects('nonexhaustive cutoff '+str(k),lambda:replay_tree(bad,g))
                bad=copy.deepcopy(terminal);bad['nodes'][0]['propagate']=[]
                rejects('false empty root '+str(k),lambda:replay_tree(bad,g))
            families.append({'mesh':m,'angle_bins':k,'core_count':len(nf['cores']),
                'proof_nodes':sum(len(c['nodes']) for c in nf['cores']),
                'branch_nodes':sum('split_cell' in n for c in nf['cores'] for n in c['nodes']),
                'propagation_rows':sum(len(n['propagate']) for c in nf['cores'] for n in c['nodes']),
                'candidate_deletions':sum(v['candidate_deletions'] for v in totals),
                'graph_sha256':nf['graph_sha256'],'controls':controls})
        print('PASS FAMILY',m,k,'elapsed_seconds',round(time.time()-start,2),flush=True)
        del g;gc.collect()
    square_counts,_=classify_square(sq,sm,base);disk_counts=classify_disk(disk,dm,sm,base)
    counts,increments=classify_new(cert,manifest,dm,base)
    require(square_counts=={'EXCLUDED':886,'OPEN':7029} and disk_counts=={'EXCLUDED':3986,'OPEN':3929},'prior replay counts')
    if args.negative_controls:
        bad=copy.deepcopy(manifest);bad['roots'][7820]['status']='EXCLUDED'
        rejects('false equality-root exclusion',lambda:classify_new(cert,bad,dm,base))
        bad=copy.deepcopy(manifest);bad['roots'].pop()
        rejects('omitted original root',lambda:classify_new(cert,bad,dm,base))
        bad=copy.deepcopy(manifest);bad['roots'][0]['mask']^=1
        rejects('changed original root mask',lambda:classify_new(cert,bad,dm,base))
        for field,value in (('target_q','1106/256'),('support_scheme','sampled'),('separator_scheme','decoupled')):
            bad=copy.deepcopy(cert);bad[field]=value
            rejects('altered '+field,lambda:semantics(bad))
    image_masks={sum(1<<p[v] for v in (0,3,7)) for p in base['symmetries']}
    covered=[r for r in dm['roots'] if any(r['mask']&m==m for m in image_masks)]
    report={'result':'PASS','graph_reconstruction':'fresh independent geometry; no graph cache read',
        'arithmetic':'Python int/Fraction and bounded NumPy int64; no floating proof comparisons',
        'families':families,'root_count':7915,'statuses':counts,'previous_excluded':3986,
        'newly_excluded':counts['EXCLUDED']-3986,'prior_square_cores_replayed':prior_square,
        'prior_disk_cores_replayed':prior_disk,'core_count':sum(f['core_count'] for f in families),
        'proof_nodes':sum(f['proof_nodes'] for f in families),'branch_nodes':sum(f['branch_nodes'] for f in families),
        'propagation_rows':sum(f['propagation_rows'] for f in families),'core_increments':increments,
        'three_cell_core':{'mask':137,'cells':[0,3,7],'symmetry_images':len(image_masks),
                          'total_roots_covered':len(covered),'new_roots':sum(r['status']=='OPEN' for r in covered)},
        'negative_controls_rejected':negatives,'certificate_sha256':ch,'manifest_sha256':mh,
        'prior_disk_certificate_sha256':dh,'prior_disk_manifest_sha256':dmh,
        'source_sha256':{p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in
          ['coupled_separator_graph.py','coupled_separator_independent.py','make_coupled_separator_certificate.py',
           'verify_coupled_separator_certificate.py','coupled_controls.py']},
        'global_lower_bound_proved':False,'full_equality_classified':False,'separate_human_review_performed':False,'lean_or_ci_run':False}
    (d/'coupled_separator_verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='core_increments'},indent=2),flush=True)

if __name__=='__main__':main()

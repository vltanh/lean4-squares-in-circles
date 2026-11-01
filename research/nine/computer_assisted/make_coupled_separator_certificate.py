#!/usr/bin/env python3
"""Generate finite coupled-angle refutations for an explicit selected core list.

The physical domains are closed and cover arbitrary orientations. Unknown
searches are rejected, not converted into exclusions. Default execution rebuilds
all producer geometry. Discovery is not a premise of any accepted certificate.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, gc
from square_pose_graph import build
from disk_support_pose_graph import contract
from coupled_separator_graph import refine
from make_square_pose_certificate import bits, canonical_bytes, graph_hash
HERE=Path(__file__).resolve().parent


def prove_core(mask,g,budget=100000):
    cells=list(bits(mask))
    if not cells or not 0<mask<1<<19:raise ValueError('invalid occupied-cell core')
    nodes=[];visits=0;adj=g['adjacency']
    def visit(domains):
        nonlocal visits
        visits+=1
        if visits>budget:raise ValueError('budget exhausted; NOT a refutation')
        queue=sorted(cells,key=lambda c:(domains[c].bit_count(),c),reverse=True)
        pending=set(queue);steps=[]
        while queue and all(domains.values()):
            source=queue.pop();pending.remove(source);support=0;target=0
            for c in cells:
                if c!=source:target|=domains[c]
            for v in bits(domains[source]):
                support |= adj[v]
                if support & target == target:break
            changes=[]
            for c in cells:
                if c==source:continue
                new=domains[c]&support
                if new!=domains[c]:
                    changes.append([c,domains[c].bit_count(),new.bit_count()]);domains[c]=new
                    if c not in pending:queue.append(c);pending.add(c)
            if changes:steps.append([source,changes])
        if any(not d for d in domains.values()):
            nodes.append({'propagate':steps,'empty_cell':min(c for c in cells if not domains[c])})
            return len(nodes)-1
        candidates=[c for c in cells if domains[c].bit_count()>1]
        if not candidates:raise ValueError('compatible discrete assignment; NOT a refutation')
        c=min(candidates,key=lambda c:(domains[c].bit_count(),c))
        values=list(bits(domains[c]));cut=values[len(values)//2-1];low=(1<<(cut+1))-1
        left,right=dict(domains),dict(domains);left[c]&=low;right[c]&=~low
        if not left[c] or not right[c]:raise ValueError('empty split child')
        a=visit(left);b=visit(right)
        nodes.append({'propagate':steps,'split_cell':c,'cutoff':cut,'left':a,'right':b})
        return len(nodes)-1
    root=visit({c:g['groups'][c] for c in cells})
    return {'mask':mask,'cells':cells,'root':root,'nodes':nodes}


def classify(certificate,prior,base):
    patterns=[]
    for f,family in enumerate(certificate['families']):
        for c,core in enumerate(family['cores']):
            for s,perm in enumerate(base['symmetries']):
                patterns.append((f,c,s,sum(1<<perm[v] for v in core['cells'])))
    rows=[];increments=Counter()
    for old in prior['roots']:
        row={key:old[key] for key in ('id','mask','cells')}
        if old['status']=='EXCLUDED':row.update(status='EXCLUDED',evidence='prior_disk_support',prior_root=old['id'])
        elif old['status']=='OPEN':
            match=next(((f,c,s) for f,c,s,m in patterns if row['mask']&m==m),None)
            if match is None:row['status']='OPEN'
            else:
                row.update(status='EXCLUDED',evidence='coupled_separator',family=match[0],core=match[1],symmetry=match[2])
                increments[match[:2]]+=1
        else:raise ValueError('invalid prior status')
        rows.append(row)
    return rows,[{'family':f,'core':c,'new_roots':v} for (f,c),v in sorted(increments.items())]


def generate(directory=HERE, builder=None):
    d=Path(directory)
    spec=json.loads((d/'coupled_separator_core_list.json').read_text())
    if spec['schema']!='n9_coupled_separator_core_list_v1':raise ValueError('core-list schema')
    prior_raw=(d/'disk_support_root_manifest.json').read_bytes();prior=json.loads(prior_raw)
    base=json.loads((d/'hex_root_manifest.json').read_text())
    certificate={'schema':'n9_coupled_separator_certificate_v1','target_q':'1105/256','physical_scope':'q<=Q',
                 'scale':2**20,'support_scheme':'exact-center-support-v1',
                 'separator_scheme':'coupled-endpoint-tangent-v1','families':[]}
    for family in spec['families']:
        m,k=family['mesh'],family['angle_bins']
        if builder is None:
            old=contract(build(m,k));before=graph_hash(old['adjacency']);g=refine(old);del old
        else:g,before=builder(m,k)
        cores=[prove_core(mask,g) for mask in family['masks']]
        certificate['families'].append({'mesh':m,'angle_bins':k,'states':len(g['states']),
            'live_states':sum(x.bit_count() for x in g['groups']),
            'disk_graph_sha256':before,'graph_sha256':graph_hash(g['adjacency']),
            'separator_metadata_sha256':hashlib.sha256(canonical_bytes(g['coupled_separator'])).hexdigest(),'cores':cores})
        print('GENERATED COUPLED',m,k,len(cores),flush=True);del g;gc.collect()
    raw=canonical_bytes(certificate);(d/'coupled_separator_certificate.json').write_bytes(raw)
    rows,increments=classify(certificate,prior,base)
    manifest={'schema':'n9_coupled_separator_roots_v1','target_q':'1105/256',
              'prior_manifest_sha256':hashlib.sha256(prior_raw).hexdigest(),
              'certificate_sha256':hashlib.sha256(raw).hexdigest(),'roots':rows,
              'global_lower_bound_proved':False,'equality_classified':False}
    out=canonical_bytes(manifest);(d/'coupled_separator_root_manifest.json').write_bytes(out)
    counts=dict(Counter(r['status'] for r in rows));previous=sum(r['status']=='EXCLUDED' for r in prior['roots'])
    report={'result':'GENERATED_REQUIRES_INDEPENDENT_REPLAY','root_count':len(rows),'statuses':counts,
            'previous_excluded':previous,'newly_excluded':counts['EXCLUDED']-previous,
            'core_count':sum(len(f['cores']) for f in certificate['families']),
            'proof_nodes':sum(len(c['nodes']) for f in certificate['families'] for c in f['cores']),
            'branch_nodes':sum('split_cell' in n for f in certificate['families'] for c in f['cores'] for n in c['nodes']),
            'propagation_rows':sum(len(n['propagate']) for f in certificate['families'] for c in f['cores'] for n in c['nodes']),
            'core_increments':increments,'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'manifest_sha256':hashlib.sha256(out).hexdigest(),
            'global_lower_bound_proved':False,'full_equality_classified':False,'separate_human_review_performed':False,'lean_or_ci_run':False}
    (d/'coupled_separator_generation_report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--directory',type=Path,default=HERE)
    args=ap.parse_args();r=generate(args.directory)
    print(json.dumps({k:v for k,v in r.items() if k!='core_increments'},indent=2))

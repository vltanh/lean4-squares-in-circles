#!/usr/bin/env python3
"""Generate exact disk-support core certificates on the unchanged root cover.

The explicit core list is input; discovery is not part of the trusted result.
Every root without an earlier proof or a matching newly certified core stays OPEN.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, gc
from square_pose_graph import build
from disk_support_pose_graph import contract
from make_square_pose_certificate import prove, graph_hash, canonical_bytes, bits

HERE=Path(__file__).resolve().parent
SCHEME='exact-center-support-v1'

def digest(obj):
    return hashlib.sha256(canonical_bytes(obj)).hexdigest()

def classify(certificate, prior, hex_manifest):
    patterns=[]
    for fi,family in enumerate(certificate['families']):
        for ci,core in enumerate(family['cores']):
            for si,perm in enumerate(hex_manifest['symmetries']):
                patterns.append((fi,ci,si,sum(1<<perm[c] for c in core['cells'])))
    rows=[]; increments=Counter()
    for old in prior['roots']:
        row={key:old[key] for key in ('id','mask','cells')}
        if old['status']=='EXCLUDED':
            row.update(status='EXCLUDED',evidence='prior_square_pose',
                       family=old['family'],core=old['core'],symmetry=old['symmetry'])
        else:
            match=next(((f,c,s) for f,c,s,mask in patterns if row['mask']&mask==mask),None)
            if match is None: row['status']='OPEN'
            else:
                row.update(status='EXCLUDED',evidence='disk_support',
                           family=match[0],core=match[1],symmetry=match[2])
                increments[match[:2]]+=1
        rows.append(row)
    return rows,[dict(family=f,core=c,new_roots=n) for (f,c),n in sorted(increments.items())]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,default=HERE)
    args=ap.parse_args();d=args.directory
    prior_raw=(d/'square_pose_root_manifest.json').read_bytes();prior=json.loads(prior_raw)
    hex_manifest=json.loads((d/'hex_root_manifest.json').read_text())
    spec=json.loads((d/'disk_support_core_list.json').read_text())
    if spec['schema']!='n9_disk_support_core_list_v1':raise ValueError('core-list schema')
    certificate=dict(schema='n9_disk_support_certificate_v1',target_q='1105/256',
                     physical_scope='q<=Q',scale=2**20,normal_grid=4,
                     support_scheme=SCHEME,families=[])
    for family in spec['families']:
        m,k=family['mesh'],family['angle_bins']
        base=build(m,k);base_hash=graph_hash(base['adjacency'])
        g=contract(base)
        cores=[prove(mask,g) for mask in family['masks']]
        result=dict(mesh=m,angle_bins=k,base_states=len(base['states']),
                    live_states=sum(mask.bit_count() for mask in g['groups']),
                    position_triangles=len(base['triangles']),
                    contracted_polygons=len(g['contraction']['polygons']),
                    base_graph_sha256=base_hash,graph_sha256=graph_hash(g['adjacency']),
                    geometry_sha256=digest(g['contraction']),cores=cores)
        certificate['families'].append(result)
        print('GENERATED',m,k,'cores',len(cores),'live states',result['live_states'],flush=True)
        del base,g;gc.collect()
    raw=canonical_bytes(certificate)
    (d/'disk_support_certificate.json').write_bytes(raw)
    rows,increments=classify(certificate,prior,hex_manifest)
    manifest=dict(schema='n9_disk_support_roots_v1',target_q='1105/256',
                  prior_manifest_sha256=hashlib.sha256(prior_raw).hexdigest(),
                  certificate_sha256=hashlib.sha256(raw).hexdigest(),roots=rows,
                  global_lower_bound_proved=False,equality_classified=False)
    out=canonical_bytes(manifest);(d/'disk_support_root_manifest.json').write_bytes(out)
    statuses=dict(Counter(r['status'] for r in rows));previous=sum(r['status']=='EXCLUDED' for r in prior['roots'])
    report=dict(result='GENERATED_REQUIRES_INDEPENDENT_REPLAY',root_count=len(rows),
                statuses=statuses,previous_excluded=previous,
                newly_excluded=statuses['EXCLUDED']-previous,
                core_count=sum(len(f['cores']) for f in certificate['families']),
                propagation_rows=sum(len(c['steps']) for f in certificate['families'] for c in f['cores']),
                core_increments=increments,certificate_sha256=hashlib.sha256(raw).hexdigest(),
                manifest_sha256=hashlib.sha256(out).hexdigest(),
                global_lower_bound_proved=False,full_equality_classified=False,
                separate_human_review_performed=False,lean_or_ci_run=False)
    (d/'disk_support_generation_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='core_increments'},indent=2))

if __name__=='__main__':main()

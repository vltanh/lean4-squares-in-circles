#!/usr/bin/env python3
"""Replay specified exact square-pose cores and classify the fixed 7,915 roots.

The core list is explicit input. There is no exploratory search in this producer.
Generate the original hex manifest first. The independent verifier rebuilds
all geometry, all compatibility edges, and all root transfers from scratch.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
from square_pose_graph import build

HERE=Path(__file__).resolve().parent

def bits(mask):
    while mask:
        b=mask&-mask;mask-=b;yield b.bit_length()-1

def canonical_bytes(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def graph_hash(rows):
    h=hashlib.sha256();width=(len(rows)+7)//8
    for row in rows:h.update(row.to_bytes(width,'little'))
    return h.hexdigest()

def prove(mask,g):
    domains={c:g['groups'][c] for c in bits(mask)}
    if not domains or any(not d for d in domains.values()):raise ValueError('invalid initial core')
    queue=sorted(domains,key=lambda c:(domains[c].bit_count(),c),reverse=True)
    steps=[]
    while queue:
        source=queue.pop();support=0
        for v in bits(domains[source]):support |= g['adjacency'][v]
        changes=[]
        for c in domains:
            if c==source:continue
            new=domains[c]&support
            if new!=domains[c]:
                changes.append([c,domains[c].bit_count(),new.bit_count()])
                domains[c]=new
                if c not in queue:queue.append(c)
        if changes:steps.append([source,changes])
        empty=[c for c,d in domains.items() if d==0]
        if empty:
            return {'mask':mask,'cells':list(bits(mask)),'steps':steps,'empty_cell':min(empty)}
    raise ValueError('core not refuted: '+str(mask))

def transfer(certificate,baseline):
    patterns=[]
    for fi,family in enumerate(certificate['families']):
        for ci,core in enumerate(family['cores']):
            for si,p in enumerate(baseline['symmetries']):
                mask=sum(1<<p[i] for i in core['cells'])
                patterns.append((fi,ci,si,mask))
    rows=[];increment=Counter()
    for old in baseline['roots']:
        row={k:old[k] for k in ('id','mask','cells')}
        match=next(((f,c,s) for f,c,s,p in patterns if row['mask']&p==p),None)
        if match is None:row['status']='OPEN'
        else:
            row.update(status='EXCLUDED',family=match[0],core=match[1],symmetry=match[2])
            increment[match[:2]]+=1
        if old['status']=='EXCLUDED' and row['status']!='EXCLUDED':
            raise ValueError('previous exclusion not covered by new certificates')
        rows.append(row)
    return rows,[{'family':f,'core':c,'new_roots':n} for (f,c),n in sorted(increment.items())]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,default=HERE)
    args=ap.parse_args();d=args.directory
    raw=(d/'hex_root_manifest.json').read_bytes();baseline=json.loads(raw)
    spec=json.loads((d/'square_pose_core_list.json').read_text())
    if spec['schema']!='n9_square_pose_core_list_v1':raise ValueError('core-list schema')
    cert={'schema':'n9_square_pose_certificate_v1','target_q':'1105/256',
          'physical_scope':'q<=Q','scale':2**20,'families':[]}
    for family in spec['families']:
        m,k=family['mesh'],family['angle_bins']
        g=build(m,k)
        print('graph',m,k,len(g['states']),flush=True)
        cores=[prove(mask,g) for mask in family['masks']]
        cert['families'].append({'mesh':m,'angle_bins':k,'states':len(g['states']),
                                'position_triangles':len(g['triangles']),
                                'graph_sha256':graph_hash(g['adjacency']),'cores':cores})
        del g
    cert_raw=canonical_bytes(cert)
    (d/'square_pose_certificate.json').write_bytes(cert_raw)
    rows,increments=transfer(cert,baseline)
    manifest={'schema':'n9_square_pose_roots_v1','target_q':'1105/256',
              'baseline_manifest_sha256':hashlib.sha256(raw).hexdigest(),
              'certificate_sha256':hashlib.sha256(cert_raw).hexdigest(),
              'roots':rows,'global_lower_bound_proved':False,'equality_classified':False}
    (d/'square_pose_root_manifest.json').write_bytes(canonical_bytes(manifest))
    status=dict(Counter(r['status'] for r in rows))
    report={'result':'GENERATED_REQUIRES_INDEPENDENT_REPLAY','statuses':status,
            'root_count':len(rows),'core_count':sum(len(f['cores']) for f in cert['families']),
            'propagation_steps':sum(len(c['steps']) for f in cert['families'] for c in f['cores']),
            'core_increments':increments,'global_lower_bound_proved':False,
            'separate_human_review_performed':False,'lean_or_ci_run':False,
            'certificate_sha256':hashlib.sha256(cert_raw).hexdigest()}
    (d/'square_pose_generation_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='core_increments'},indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Direct exact full-nine 111/00 equality witness with strict marked margins."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import argparse,copy,hashlib,json

def require(test,message):
    if not test:raise ValueError(message)

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def perpendicular(a):return -a[1],a[0]

def verify(data,source):
    require(data['schema']=='n9_11100_closed_Q_boundary_v1','schema')
    require(data['mask']=='111/00' and data['target_q']=='1105/256','literal original predicate')
    require(data['new_strict_mask_closures']==0 and data['strict_subcritical_counterexample']is False,
            'strict-radius scope')
    require(data['all_marked_cones_and_bits_strict']is True,'strict marked margins')
    C,A=source['center_denominator'],source['frame_denominator']
    require(type(C)is int and C>0 and type(A)is int and A>0,'positive rational denominators')
    require(len(source['centers'])==len(source['first_axes'])==9,'all nine originals')
    centers=[tuple(F(z,C)for z in p)for p in source['centers']]
    u=[tuple(F(z,A)for z in p)for p in source['first_axes']]
    v=[perpendicular(p)for p in u]
    corners=[];radii=[];Q=F(1105,256)
    for i in range(9):
        require(dot(u[i],u[i])==dot(v[i],v[i])==1 and dot(u[i],v[i])==0,'original unit frame')
        row=[tuple(centers[i][k]+(s*u[i][k]+t*v[i][k])/2 for k in range(2))
             for s,t in product((-1,1),repeat=2)]
        norms=[dot(p,p)for p in row]
        require(all(q<=Q for q in norms),'original corner outside Q')
        radii.append(str(max(norms)));corners.append(row)
    require(radii==data['maximum_corner_norms_squared'],'printed radius table')
    require(max(map(F,radii))==Q,'exact boundary radius')
    pairs=list(combinations(range(9),2));rows=data['physical_pairs']
    require(len(rows)==36,'all36 physical pairs')
    for (i,j),row in zip(pairs,rows):
        require(row['pair']==[i,j] and row['owner']in [i,j] and
                row['axis']in ['u','v'] and row['sign']in [-1,1],'literal owned physical separator')
        n=(u if row['axis']=='u'else v)[row['owner']]
        n=tuple(row['sign']*z for z in n)
        reserve=min(dot(n,p)for p in corners[j])-max(dot(n,p)for p in corners[i])
        require(reserve>=0 and str(reserve)==row['reserve'],'original physical pair reserve')
    p,q=data['witness_frame']['direction_numerator'];N=p*p+q*q
    require(type(p)is int and type(q)is int and N>0,'nonzero witness direction')
    require(N==data['witness_frame']['normalizer_squared'],'positive symbolic square-root denominator')
    require(dot((p,q),(-q,p))==0 and dot((-q,p),(-q,p))==N,'orthonormal witness frame')
    labels=data['main']+data['short']+data['extras']
    require(len(data['main'])==4 and len(data['short'])==3 and len(data['extras'])==2 and
            sorted(labels)==list(range(9)),'full nine-original permutation')
    require(len(data['marked_edges'])==5,'all five marked edges')
    edges=((0,1),(1,2),(2,3),(4,5),(5,6));bits='11100';computed=[]
    widths=[(abs(dot((p,q),a))+abs(dot((p,q),b)))/2 for a,b in zip(u,v)]
    for (a,b),bit,printed in zip(edges,bits,data['marked_edges']):
        i,j=labels[a],labels[b]
        d=tuple(centers[j][k]-centers[i][k]for k in range(2))
        dx,dy=dot((p,q),d),dot((-q,p),d)
        width=widths[i]+widths[j]
        cone=dx-abs(dy);margin=width-dx if bit=='1'else dx-width
        require(dx>0 and cone>0 and margin>0,'strict original cone/bit margin')
        row={'pair':[i,j],'dx_times_sqrt_N':str(dx),'dy_times_sqrt_N':str(dy),
             'sum_halfwidths_times_sqrt_N':str(width),'bit':bit,
             'cone_reserve_times_sqrt_N':str(cone),'bit_reserve_times_sqrt_N':str(margin)}
        require(row==printed,'literal printed marked edge')
        computed.append(row)
    return {'all_nine_original_frames_verified':True,'original_corner_checks':36,
            'original_pair_checks':36,'maximum_corner_norms_squared':radii,
            'full_nine_permutation':labels,'witness_frame':data['witness_frame'],
            'marked_edges':computed,'all_marked_cones_and_bits_strict':True,
            'marked_equality_faces_essential':False,
            'minimum_cone_margin_times_sqrt_N':str(min(F(r['cone_reserve_times_sqrt_N'])for r in computed)),
            'minimum_actual_margin_times_sqrt_N':str(min(F(r['bit_reserve_times_sqrt_N'])for r in computed if r['bit']=='0')),
            'minimum_weak_margin_times_sqrt_N':str(min(F(r['bit_reserve_times_sqrt_N'])for r in computed if r['bit']=='1'))}

def main():
    p=argparse.ArgumentParser();p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--output',type=Path);p.add_argument('--negative-controls',action='store_true')
    a=p.parse_args();folder=a.directory.resolve();mp=folder/'MANIFEST.json';mh=digest(mp)
    manifest=json.loads(mp.read_text())
    require(manifest['schema']=='n9_11100_closed_Q_boundary_packet_v1','manifest schema')
    needed={'boundary_11100.json','source_control.json','verify_11100_boundary.py',
            'CLOSED_Q_11100_BOUNDARY_HAND_PROOF.md','sources/A2_COVERAGE_AND_CLOSURE_CONTRACT.md'}
    require(needed<=set(manifest['sha256']),'complete portable input set')
    frozen={}
    for name,h in manifest['sha256'].items():
        f=(folder/name).resolve();require(f.is_relative_to(folder),'packet local dependency')
        require(digest(f)==h,'frozen input '+name);frozen[f]=h
    require(Path(__file__).resolve()==folder/'verify_11100_boundary.py','packet local checker')
    data=json.loads((folder/'boundary_11100.json').read_text())
    source=json.loads((folder/'source_control.json').read_text())
    require(data['source_control_sha256']==digest(folder/'source_control.json'),'source binding')
    result=verify(data,source);rejected=[]
    if a.negative_controls:
        bad=copy.deepcopy(source);bad['centers'].pop()
        candidates=[('omit ninth physical original',data,bad)]
        bad=copy.deepcopy(data);bad['physical_pairs'].pop()
        candidates.append(('omit physical pair',bad,source))
        bad=copy.deepcopy(data);bad['main'][0],bad['main'][1]=bad['main'][1],bad['main'][0]
        candidates.append(('reverse first marked edge',bad,source))
        bad=copy.deepcopy(data);bad['marked_edges'][-1]['bit_reserve_times_sqrt_N']='0'
        candidates.append(('erase strict actual reserve',bad,source))
        bad=copy.deepcopy(data);bad['strict_subcritical_counterexample']=True
        candidates.append(('claim strict-radius counterexample',bad,source))
        for name,d,s in candidates:
            try:verify(d,s)
            except (ValueError,KeyError,IndexError):rejected.append(name)
            else:raise ValueError('damaged boundary witness accepted: '+name)
    require(digest(mp)==mh and all(digest(f)==h for f,h in frozen.items()),'input changed during replay')
    report={'status':'PASS','mask':'111/00','closed_Q_domain':'NONEMPTY',
            'new_strict_mask_closures':0,'new_original_cell_closures':0,
            'strict_subcritical_counterexample':False,'arithmetic':'integer and Fraction only',
            'negative_controls_rejected':rejected,'manifest_sha256':mh,
            'frozen_input_sha256':{str(f.relative_to(folder)):h for f,h in frozen.items()},**result}
    out=a.output or folder/'EXACT_11100_BOUNDARY_REPLAY.json'
    require(not out.exists(),'refusing to overwrite replay');out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','mask':'111/00','closed_Q_domain':'NONEMPTY',
                     'all_marked_cones_and_bits_strict':True,'negative_controls_rejected':len(rejected),
                     'new_strict_mask_closures':0,'report':str(out)}),flush=True)

if __name__=='__main__':main()

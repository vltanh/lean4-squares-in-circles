#!/usr/bin/env python3
"""Exact full-nine witnesses at Q for four unchanged fixed-mask predicates.

Standard library only. No numerical solver, source producer, Lean, or external
geometry library is used. This proves nonemptiness at closed Q, not a strict
subcritical counterexample and not a strict-mask closure.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import copy
import hashlib
import json

Q=F(1105,256)
EDGES=((0,1),(1,2),(2,3),(4,5),(5,6))
EXPECTED=('101/11','111/01','111/10','111/11')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def require(v,why):
    if not v: raise ValueError(why)

def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]

def verify(data,source):
    require(data['schema']=='n9_four_closed_Q_boundary_witnesses_v1','schema')
    require(data['target_q']=='1105/256','target Q')
    require(data['strict_subcritical_counterexample'] is False,'strict scope')
    require(data['new_strict_mask_closures']==0,'closure scope')
    require(data['all_32_mask_predicates_unchanged'] is True,'unchanged predicates')
    D=data['center_denominator']
    require(type(D)is int and D>0,'positive center denominator')
    originals=data['originals']
    require(len(originals)==9 and [v['label']for v in originals]==list(range(9)),
            'all nine original labels')
    require(D==source['center_denominator'],'source denominator')
    require([v['center_numerator']for v in originals]==source['centers'],'source centers')
    points=[];corners=[];radius_rows=[]
    for item in originals:
        require(item['first_axis']==['1','0'] and item['second_axis']==['0','1'],
                'literal independent original frame')
        center=tuple(F(z,D)for z in item['center_numerator'])
        u=tuple(map(F,item['first_axis']));v=tuple(map(F,item['second_axis']))
        require(dot(u,u)==dot(v,v)==1 and dot(u,v)==0,'original orthonormality')
        row=[tuple(center[k]+F(s,2)*u[k]+F(t,2)*v[k]for k in range(2))
             for s,t in product((-1,1),repeat=2)]
        norms=[dot(z,z)for z in row]
        require(all(z<=Q for z in norms),'original corner escaped Q')
        maximum=max(norms)
        require(str(maximum)==item['maximum_corner_norm_squared'],'printed corner maximum')
        radius_rows.append({'original':item['label'],'maximum_squared_norm':str(maximum),
                            'corners_on_Q':sum(z==Q for z in norms)})
        points.append(center);corners.append(row)
    require(max(F(r['maximum_squared_norm'])for r in radius_rows)==Q,
            'this is specifically a boundary witness')
    axis_word=data['physical_pair_axis_word']
    pairs=list(combinations(range(9),2))
    require(len(axis_word)==len(pairs)==36,'all 36 physical pair certificates')
    unit_axes=((F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(0),F(-1)))
    physical_rows=[]
    for (i,j),digit in zip(pairs,axis_word):
        require(digit in '0123','owned separating axis')
        n=unit_axes[int(digit)]
        # Compare full original corner projections, retaining weak contact.
        reserve=min(dot(n,p)for p in corners[j])-max(dot(n,p)for p in corners[i])
        require(reserve>=0,'original pair lacks its printed physical separator')
        physical_rows.append({'pair':[i,j],'owned_normal':list(map(str,n)),
                              'separation_reserve':str(reserve)})
    require(tuple(sorted(c['mask']for c in data['witnesses']))==EXPECTED,
            'literal four original-mask IDs')
    results=[]
    for witness in data['witnesses']:
        mask=witness['mask'];p,q=witness['direction_numerator']
        require(type(p)is int and type(q)is int and p*p+q*q>0,'nonzero rational direction')
        N=p*p+q*q
        require(N==witness['frame_normalizer_squared'],'printed positive frame denominator')
        # e=(p,q)/sqrt(N), f=(-q,p)/sqrt(N). Orthonormality follows from
        # the two exact diagonal Gram entries N and zero cross entry.
        require(dot((p,q),(-q,p))==0 and dot((p,q),(p,q))==dot((-q,p),(-q,p))==N,
                'witness orthonormality')
        labels=witness['four']+witness['three']+witness['extras']
        require(len(witness['four'])==4 and len(witness['three'])==3 and
                len(witness['extras'])==2 and sorted(labels)==list(range(9)),
                'full nine-original witness permutation')
        threshold=D*(abs(p)+abs(q))
        require(threshold==witness['twice_halfwidth_scaled'],'printed physical widths')
        bits=mask.replace('/','');rows=[]
        require(len(witness['edge_table'])==5,'all five marked edges')
        for k,((a,b),bit,printed) in enumerate(zip(EDGES,bits,witness['edge_table'])):
            i,j=labels[a],labels[b]
            xi,yi=originals[i]['center_numerator'];xj,yj=originals[j]['center_numerator']
            dx=p*(xj-xi)+q*(yj-yi)
            dy=-q*(xj-xi)+p*(yj-yi)
            require(dx>0 and dx-dy>=0 and dx+dy>=0,'original center cone')
            require((dx>=threshold) if bit=='0' else (dx<threshold),'exact original bit')
            row={'pair':[i,j],'dx_scaled':dx,'dy_scaled':dy,
                 'sum_halfwidths_scaled':threshold,'bit':bit,
                 'cone_reserve_scaled':dx-abs(dy),
                 'bit_reserve_scaled':dx-threshold if bit=='0' else threshold-dx}
            require(row==printed,'printed exact edge table')
            rows.append(row)
        results.append({'mask':mask,'status':'NONEMPTY_AT_CLOSED_Q',
                        'full_nine_permutation':labels,
                        'frame_denominator':'sqrt('+str(N)+')',
                        'center_comparison_denominator':str(D)+'*sqrt('+str(N)+')',
                        'all_denominators_positive':True,'edge_table':rows})
    return {'original_corner_checks':36,'original_pair_checks':36,
            'radius_table':radius_rows,'physical_pair_table':physical_rows,
            'witnesses':results}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--negative-controls',action='store_true')
    args=parser.parse_args();folder=args.directory.resolve()
    manifest=folder/'MANIFEST.json';manifest_hash=sha(manifest)
    inventory=json.loads(manifest.read_text())
    require(inventory['schema']=='n9_four_closed_Q_boundary_packet_v1','packet schema')
    required={'boundary_witnesses.json','verify_closed_q_boundary_witnesses.py',
              'CLOSED_Q_BOUNDARY_WITNESSES_HAND_PROOF.md',
              'sources/limit_frame_family_table.json',
              'sources/A2_COVERAGE_AND_CLOSURE_CONTRACT.md'}
    require(required<=set(inventory['sha256']),'complete portable ancestry')
    files={}
    for name,h in inventory['sha256'].items():
        path=(folder/name).resolve()
        require(path.is_relative_to(folder),'packet-local input')
        require(sha(path)==h,'immutable packet input '+name)
        files[path]=h
    require(Path(__file__).resolve()==(folder/'verify_closed_q_boundary_witnesses.py').resolve(),
            'checker must resolve inside this packet')
    data=json.loads((folder/'boundary_witnesses.json').read_text())
    source=json.loads((folder/'sources/limit_frame_family_table.json').read_text())
    require(data['source_limit_control_sha256']==sha(folder/'sources/limit_frame_family_table.json'),
            'original control source binding')
    result=verify(data,source);rejected=[]
    if args.negative_controls:
        bad=copy.deepcopy(data);bad['originals'].pop()
        damaged=[('omit ninth original',bad)]
        bad=copy.deepcopy(data);bad['physical_pair_axis_word']=bad['physical_pair_axis_word'][:-1]
        damaged.append(('omit physical pair',bad))
        bad=copy.deepcopy(data);bad['witnesses'][0]['four'].reverse()
        damaged.append(('reverse only the main chain',bad))
        bad=copy.deepcopy(data);bad['witnesses'][0]['edge_table'][0]['bit_reserve_scaled']+=1
        damaged.append(('corrupt strict bit reserve',bad))
        bad=copy.deepcopy(data);bad['strict_subcritical_counterexample']=True
        damaged.append(('misclassify equality as strict counterexample',bad))
        for name,bad in damaged:
            try:verify(bad,source)
            except (ValueError,KeyError,IndexError):rejected.append(name)
            else:raise ValueError('damaged witness accepted: '+name)
    require(sha(manifest)==manifest_hash,'manifest changed during replay')
    require(all(sha(path)==h for path,h in files.items()),'packet changed during replay')
    report={'schema':'n9_four_closed_Q_boundary_replay_v1','status':'PASS',
            'claim':'Four unchanged full-nine fixed-mask domains are nonempty at closed Q',
            'target_q':'1105/256','arithmetic':'integer and Fraction only',
            'new_strict_mask_closures':0,'new_original_cell_closures':0,
            'all_32_mask_predicates_unchanged':True,
            'strict_subcritical_counterexample':False,
            'negative_controls_rejected':rejected,'manifest_sha256':manifest_hash,
            'frozen_input_sha256':{str(path.relative_to(folder)):h for path,h in files.items()},
            **result}
    output=args.output or folder/'EXACT_BOUNDARY_REPLAY.json'
    require(not output.exists(),'refusing to overwrite an existing replay')
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','masks':list(EXPECTED),'corner_checks':36,
                      'physical_pair_checks':36,'marked_edge_checks':20,
                      'negative_controls_rejected':len(rejected),
                      'new_strict_mask_closures':0,'report':str(output)}),flush=True)

if __name__=='__main__':
    main()

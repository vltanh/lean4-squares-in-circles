#!/usr/bin/env python3
"""Fresh rational guard and caller controls; no optimizer or scalar replay.

Conditional interval fixtures are not packing witnesses and do not supply
state ancestry. Original-C order is separately reconstructed from the frozen
fresh-root cone rows for both complete caller documents.
"""
if not __debug__:
    raise RuntimeError('Exact guard controls reject optimized Python.')

import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import strict021_guards as P
import independent_strict021_guards as I
import source_bindings as S

FOUNDATION_SHA='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module
def point(state,original,axis,value):
    state['positions'][2*original+axis]=[str(value),str(value)]
def coordinate_box(state,original,axis,lower,upper):
    state['positions'][2*original+axis]=[str(lower),str(upper)]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    foundation=args.foundation.resolve()
    output=args.output.resolve()
    assert not output.exists()
    assert digest(foundation/'CHECKPOINT_MANIFEST.json')==FOUNDATION_SHA
    inventory=json.loads((foundation/'CHECKPOINT_MANIFEST.json').read_text())
    assert len(inventory['files'])==184
    for relative,entry in inventory['files'].items():
        path=(foundation/relative).resolve()
        assert path.is_relative_to(foundation) and not (foundation/relative).is_symlink()
        assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256']
    dependency=S.verify_dependencies()
    source_files=['strict021_guards.py','independent_strict021_guards.py',
                  'source_bindings.py','check_guards.py','PHYSICAL_ATTACHMENTS.md']
    source_hashes={name:digest(HERE/name) for name in source_files}
    documents=[json.loads((HERE/'callers'/name).read_text()) for name in ('base.json','representative.json')]
    rejected=[]
    def reject(name,callback):
        try:callback()
        except (AssertionError,ValueError,KeyError,IndexError,TypeError):rejected.append(name)
        else:raise AssertionError('Damaged control accepted: '+name)
    counts=dict(point_HI=0,point_C=0,passing_HI=0,passing_C=0,
                correlated_boxes=0,translation_checks=0,threshold_faces=0,
                order_faces=0,nonpassing_literals_rejected=0,root_cone_literals=0,
                root_cone_half_weight_sums=0,empty_interval_rejections=0)
    samples=[]
    def compare(state,document,middle,mode,expected):
        proposed=P.evaluate(state,document,middle,mode)
        rebuilt=I.reconstruct(state,document,middle,mode)
        assert proposed==rebuilt
        passed=proposed['status']=='PASS_STRICT011_UNIVERSAL021_GUARD'
        assert passed is expected
        if passed:
            assert I.verify_literal(proposed,state,document)==proposed
        else:
            reject('guard_not_implied:'+mode+':'+str(counts['nonpassing_literals_rejected']),
                   lambda:I.verify_literal(proposed,state,document))
            counts['nonpassing_literals_rejected']+=1
        return proposed

    roots=[]
    for document,folder in zip(documents,('strict_011_full_root_v2','strict_011_representative_root_v1')):
        adapter=load('guard_v2_'+folder,foundation/folder/'independent_strict_011_adapter.py')
        initial=adapter.verify_root(document)
        assert document==json.loads((foundation/folder/'snapshots/ROOT_DOCUMENT.json').read_text())
        assert P.caller(document)==I.assert_caller(document)
        certificate=P.cone_certificate()
        assert certificate==I.original_cone_order()
        printed=[dict(index=k,**row) for k,row in enumerate(certificate['premises'])]
        rows,bounds,current=adapter.Adapter.rebuild(initial,printed)
        assert len(bounds)==54 and len(rows)==4
        for k,row in enumerate(printed):
            expected=(tuple((j,F(v)) for j,v in row['coefficients']),F(row['rhs']),row['name'])
            assert rows[k]==expected
            counts['root_cone_literals']+=1
            for change in ('coefficient','rhs','name'):
                damaged=deepcopy(printed)
                if change=='coefficient':damaged[k]['coefficients'][0][1]='2'
                elif change=='rhs':damaged[k]['rhs']='-1/100'
                else:damaged[k]['name']='strict011v2:cone:0:8:1'
                reject(folder+':cone:'+str(k)+':'+change,
                       lambda damaged=damaged:adapter.Adapter.rebuild(initial,damaged))
        for offset,order in zip((0,2),certificate['resulting_order_rows']):
            co={};rhs=F(0)
            for k in (offset,offset+1):
                rhs+=rows[k][1]/2
                for column,value in rows[k][0]:co[column]=co.get(column,F(0))+value/2
            assert [[k,str(v)] for k,v in sorted(co.items()) if v]==order['coefficients']
            assert str(rhs)==order['rhs']
            counts['root_cone_half_weight_sums']+=1
        roots.append(dict(root_id=document['original_id'],document_sha256=I.assert_caller(document),
                          all_originals=9,corners=36,pairs=36,cones=5,
                          exact_C_order_certificate=certificate))

    heights=list(map(F,('-1/5','-21/200','0','21/200','1/5')))
    horizontal=list(map(F,('-4/5','-3/5','0','3/5','4/5')))
    for document in documents:
        for middle in (7,8):
            for x,(yb,yx,yd) in product(horizontal,product(heights,repeat=3)):
                state=deepcopy(document['initial'])
                for original,xx,yy in ((1,F(-3,5),yb),(middle,x,yx),(3,F(3,5),yd)):
                    point(state,original,0,xx);point(state,original,1,yy)
                w=abs(yx-yb)+abs(yd-yx)
                expected=F(-3,5)<=x<=F(3,5) and w<=F(21,100)
                literal=compare(state,document,middle,'HI',expected)
                assert F(literal['variation_upper'])==w
                counts['point_HI']+=1;counts['passing_HI']+=int(expected)
                counts['threshold_faces']+=int(w==F(21,100))
                counts['order_faces']+=int(x in (F(-3,5),F(3,5)))
                if expected and len(samples)<2:samples.append((deepcopy(state),document,middle,'HI',literal))
        for yb,yx,yd in product(heights,repeat=3):
            state=deepcopy(document['initial'])
            point(state,1,0,F(-3,5));point(state,3,0,F(3,5))
            coordinate_box(state,2,0,F(-1),F(1))
            for original,y in ((1,yb),(2,yx),(3,yd)):point(state,original,1,y)
            w=abs(yx-yb)+abs(yd-yx)
            literal=compare(state,document,2,'C',w<=F(21,100))
            assert F(literal['variation_upper'])==w
            counts['point_C']+=1;counts['passing_C']+=int(w<=F(21,100))
            counts['threshold_faces']+=int(w==F(21,100))
            if w==0:samples.append((deepcopy(state),document,2,'C',literal))

    # Difference records retain correlations that independent wide coordinate
    # intervals cannot express. Reverse X-D orientation is exercised for H/I.
    for document,middle,shift,slack in product(documents,(2,7,8),map(F,('-1/4','0','1/4')),map(F,('0','1/100','1/50'))):
        mode='C' if middle==2 else 'HI'
        state=deepcopy(document['initial'])
        centers={1:(F(-3,5),F(0)),middle:(F(0),F(1,20)),3:(F(3,5),F(1,10))}
        for original,(x,y) in centers.items():
            coordinate_box(state,original,0,x+shift-F(1,4),x+shift+F(1,4))
            coordinate_box(state,original,1,y+shift-F(1,4),y+shift+F(1,4))
        differences=[]
        for left,right in sorted({tuple(sorted(pair)) for pair in ((1,middle),(middle,3),(1,3))}):
            d=[centers[right][axis]-centers[left][axis] for axis in (0,1)]
            differences.append(dict(pair=[left,right],intervals=[
                [str(d[0]),str(d[0])],[str(d[1]-slack),str(d[1]+slack)]]))
        state['differences']=differences
        literal=compare(state,document,middle,mode,True)
        assert F(literal['variation_upper'])==F(1,10)+slack
        counts['correlated_boxes']+=1
        for dx,dy in product((F(-1,100),F(1,100)),repeat=2):
            translated=deepcopy(state)
            translated['positions']=[[str(F(a)+(dx if k%2==0 else dy)),str(F(b)+(dx if k%2==0 else dy))]
                                      for k,(a,b) in enumerate(state['positions'])]
            assert compare(translated,document,middle,mode,True)==literal
            counts['translation_checks']+=1
        for axis in (0,1):
            # On the used B-D vertical coordinate (and B-X horizontal for H/I),
            # a pair interval disjoint from the coordinate rectangle must fail.
            if axis==0 and mode=='C':continue
            bad=deepcopy(state)
            pair=sorted((1,middle)) if axis==0 else [1,3]
            target=next(row for row in bad['differences'] if row['pair']==pair)
            target['intervals'][axis]=['10','11']
            for module in (P,I):
                callback=module.evaluate if module is P else module.reconstruct
                reject('empty_intersection:'+mode+':'+str(counts['empty_interval_rejections']),
                       lambda callback=callback,bad=bad:callback(bad,document,middle,mode))
                counts['empty_interval_rejections']+=1

    # Direct scope, labeling and printed-bound damage controls on good literals.
    literal_damage=0
    for state,document,middle,mode,literal in samples:
        changes={
            'radius_mode':'closed','mask':'001/00','target_q':'17/4',
            'caller_root_id':'positive-821c9a2debeed0aa','caller_path':[['forged',0,0]],
            'variation_upper':'-1','variation_limit':'3/5',
            'physical_row':[0,1,7,3] if middle!=7 else [0,1,8,3],
            'selected_distinct_originals':[0,1,3,3,4,5,6],
            'all_nine_originals':list(range(8)),'original_corners':32,'original_pairs':28,
            'marked_cones':4,'actual_links_required':[[0,1],[1,2],[4,5],[5,6]],
            'strict_weak_links_retained':[[2,3]],'actual_BC_assumed':True,
            'closed_Q_equality_blocker_used':True,'fresh_scalar_replay_required_at_use':False,
            'certified_complete_state_ancestry_required':False,
            'installed_in_tree_replay':True,'whole_mask_cover_checked':True,'whole_mask_credit':1}
        for field,value in changes.items():
            bad=deepcopy(literal);bad[field]=value
            reject('literal:'+str(literal_damage)+':'+field,
                   lambda bad=bad:I.verify_literal(bad,state,document));literal_damage+=1
        bad=deepcopy(literal);bad['four_signed_height_upper_bounds'][0]='-99'
        reject('literal:'+str(literal_damage)+':height',lambda:I.verify_literal(bad,state,document));literal_damage+=1
        bad=deepcopy(literal)
        if mode=='C':bad['order']['certificate']['premises'][0]['coefficients'][0][1]='-1'
        else:bad['order']['intervals'][0][0]='-1'
        reject('literal:'+str(literal_damage)+':order',lambda:I.verify_literal(bad,state,document));literal_damage+=1

    caller_damage=state_damage=0
    for document in documents:
        changes={'mask':'001/00','radius_mode':'closed','target_q':'17/4',
                 'original_id':'negative-462e78d2e2d8be05','corner_relation':'corner_norm_squared <= Q',
                 'inherited_001_premises':['actual BC'],'inherited_original_cells':['old-cell'],
                 'extra_normalizations':['G above D'],'whole_mask_credit':1}
        mutations=[]
        for field,value in changes.items():
            bad=deepcopy(document);bad[field]=value;mutations.append((field,bad))
        for field in ('physical_originals','original_corners','original_pairs','owned_pair_cover','exact_mask_edges'):
            bad=deepcopy(document);bad[field].pop();mutations.append(('omitted '+field,bad))
        for edge in range(5):
            bad=deepcopy(document);bad['exact_mask_edges'][edge]['bit']^=1
            mutations.append(('wrong bit '+str(edge),bad))
        bad=deepcopy(document);bad['extra_hidden_premise']='yD=yB';mutations.append(('hidden premise',bad))
        for name,bad in mutations:
            for callback in (P.caller,I.assert_caller):
                reject('caller:'+str(caller_damage)+':'+name,lambda callback=callback,bad=bad:callback(bad))
                caller_damage+=1
        good=deepcopy(document['initial'])
        for original,x in ((1,F(-3,5)),(7,F(0)),(3,F(3,5))):
            point(good,original,0,x);point(good,original,1,F(0))
        changes=[]
        bad=deepcopy(good);bad['id']='old_registered_id';changes.append(('id',bad))
        bad=deepcopy(good);bad['path']='not-a-list';changes.append(('path',bad))
        bad=deepcopy(good);bad['positions'].pop();changes.append(('missing position',bad))
        bad=deepcopy(good);bad['positions'][3]=['1','-1'];changes.append(('reversed position',bad))
        for pair,intervals in (([7,1],[['0','1'],['0','1']]),([1,9],[['0','1'],['0','1']]),
                               ([1,7],[['1','-1'],['0','1']]),([1,7],[['0','1']])):
            bad=deepcopy(good);bad['differences']=[dict(pair=pair,intervals=intervals)];changes.append(('difference',bad))
        bad=deepcopy(good);row=dict(pair=[1,7],intervals=[['0','1'],['0','1']]);bad['differences']=[row,row]
        changes.append(('duplicate difference',bad))
        for name,bad in changes:
            for callback in (P.evaluate,I.reconstruct):
                reject('state:'+str(state_damage)+':'+name,lambda callback=callback,bad=bad:callback(bad,document,7,'HI'))
                state_damage+=1
        for middle,mode in ((2,'HI'),(7,'C'),(8,'C'),(True,'HI'),(6,'HI'),(7,'other')):
            for callback in (P.evaluate,I.reconstruct):
                reject('labels:'+str(state_damage),lambda callback=callback,middle=middle,mode=mode:callback(good,document,middle,mode))
                state_damage+=1

    assert counts['point_HI']==2500 and counts['point_C']==250
    assert counts['correlated_boxes']==54 and counts['translation_checks']==216
    assert counts['root_cone_literals']==8 and counts['root_cone_half_weight_sums']==4
    assert not any(name.split('.')[0] in {'numpy','scipy','sympy','z3','highspy'} for name in sys.modules)
    assert source_hashes=={name:digest(HERE/name) for name in source_files}
    assert digest(foundation/'CHECKPOINT_MANIFEST.json')==FOUNDATION_SHA
    S.verify_dependencies()
    report=dict(status='PASS_NEW_STRICT011_UNIVERSAL021_HI_AND_C_GUARD_CONTROLS',
        foundation_manifest_sha256=FOUNDATION_SHA,foundation_members_rehashed=184,
        dependency_manifest_sha256=S.DEPENDENCY_SHA,dependency_members_rehashed=len(dependency['files']),
        source_hashes=source_hashes,root_attachments=roots,counts=counts,
        literal_damages_rejected=literal_damage,caller_damages_rejected=caller_damage,
        state_and_label_damages_rejected=state_damage,total_rejections=len(rejected),
        damaged_control_names=rejected,conditional_interval_fixtures_not_packing_witnesses=True,
        missing_old_control_receipts_reused=False,fresh_scalar_replay_performed=False,
        complete_state_ancestry_replayed=False,installed_in_tree_replay=False,
        numerical_solver_called=False,original_cell_credit=0,whole_mask_credit=0)
    with output.open('x') as stream:json.dump(report,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status=report['status'],counts=counts,
                         damages=dict(literal=literal_damage,caller=caller_damage,state=state_damage),
                         report_sha256=digest(output),output=str(output))))

if __name__=='__main__':main()

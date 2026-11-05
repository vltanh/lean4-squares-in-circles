#!/usr/bin/env python3
"""Independent literal, complete-quadrant, caller and damage controls."""
if not __debug__:
    raise RuntimeError('C-height exact controls reject optimized Python.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def module(name):
    spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py'))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
def write(path,value):
    with path.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--guard-folder',type=Path,required=True)
    parser.add_argument('--output-folder',type=Path,required=True);args=parser.parse_args()
    out=args.output_folder.resolve();out.mkdir(parents=True,exist_ok=False)
    S=module('accepted_sources');P=module('c_height_cover');I=module('independent_c_height_cover')
    sources=S.Sources(args.guard_folder)
    local={str(path):digest(path)for path in HERE.glob('*.py')}
    algebra=I.symbolic_coverage();assert len(algebra['cases'])==4
    assert sum(len(case['nonnegative_W_minus_form_coefficients'])for case in algebra['cases'])==16
    write(out/'SYMBOLIC_ALL_QUADRANT_PROOF.json',algebra)
    rejected=[]
    def reject(label,function):
        try:function()
        except(AssertionError,KeyError,TypeError,ValueError):rejected.append(label)
        else:raise AssertionError('Malformed prepared cover accepted: '+label)
    literals=[];numeric_controls=0;thresholds=0;overlaps=0
    for name in('base','representative'):
        doc=json.loads((args.guard_folder/'callers'/(name+'.json')).read_text())
        literal=P.literal(doc,sources);assert I.verify_literal(literal,doc,sources)==literal
        write(out/(name.upper()+'_C_HEIGHT_COVER_LITERAL.json'),literal);literals.append(literal)
        for key,value in(
            ('radius_mode','closed'),('mask','001/00'),('all_nine_originals',list(range(7))),
            ('original_pairs',21),('original_corners',28),('marked_cones',4),
            ('actual_BC_assumed',True),('closed_Q_equality_blocker_used',True),
            ('D_frame_sign_or_DG_corridor_assumed',True),('fresh_scalar_replay_required_at_first_actual_use',False),
            ('arbitrary_relaxed_box_coverage_claimed',True),('cover_installed',True),
            ('caller_root_document_sha256','0'*64),('caller_initial_state_sha256','0'*64)):
            changed=deepcopy(literal);changed[key]=value
            reject(name+':literal:'+key,lambda changed=changed:I.verify_literal(changed,doc,sources))
        for branch in range(4):
            for field,value in(('relation','>'),('threshold','1/5'),('signs',[1,1])):
                changed=deepcopy(literal)
                if changed['branches'][branch][field]==value:value=['bad']if field=='signs'else'bad'
                changed['branches'][branch][field]=value
                reject(name+':branch:'+str(branch)+':'+field,lambda changed=changed:I.verify_literal(changed,doc,sources))
            changed=deepcopy(literal);changed['branches'][branch]['affine_row']['rhs']='-1/5'
            reject(name+':row_rhs:'+str(branch),lambda changed=changed:I.verify_literal(changed,doc,sources))
            changed=deepcopy(literal);changed['branches'][branch]['affine_row']['coefficients'][0][1]='0'
            reject(name+':row_coefficient:'+str(branch),lambda changed=changed:I.verify_literal(changed,doc,sources))
        for mode in('missing','duplicate','reordered'):
            changed=deepcopy(literal)
            if mode=='missing':changed['branches'].pop()
            if mode=='duplicate':changed['branches'][3]=deepcopy(changed['branches'][0])
            if mode=='reordered':changed['branches'][0],changed['branches'][1]=changed['branches'][1],changed['branches'][0]
            reject(name+':cover:'+mode,lambda changed=changed:I.verify_literal(changed,doc,sources))
        for key,value in(('radius_mode','closed'),('mask','001/00'),('target_q','5'),
                         ('physical_originals',list(range(7))),('original_pairs',doc['original_pairs'][:-1]),
                         ('original_corners',doc['original_corners'][:-1]),('inherited_001_premises',['not allowed'])):
            changed=deepcopy(doc);changed[key]=value
            reject(name+':caller:'+key,lambda changed=changed:I.verify_literal(literal,changed,sources))
        changed=deepcopy(doc);changed['exact_mask_edges'][1]['bit']=0
        reject(name+':caller:actual_BC',lambda:I.verify_literal(literal,changed,sources))
        changed=deepcopy(doc);changed['initial']['positions'][0][0]='-1'
        reject(name+':caller:narrowed_initial',lambda:I.verify_literal(literal,changed,sources))
        if name=='representative':
            changed=deepcopy(doc);changed['normalization_equivalence']['equality_faces_retained']=False
            reject(name+':caller:normalization_faces',lambda:I.verify_literal(literal,changed,sources))
        for yB,yC,yD in product((F(-2),F(-21,100),F(-7,100),F(0),F(7,100),F(21,100),F(2)),repeat=3):
            values={3:yB,5:yC,7:yD}
            height=abs(yC-yB)+abs(yD-yC)
            forms=[sum(F(v)*values[j]for j,v in branch['signed_height_form'])for branch in literal['branches']]
            rows=[sum(F(v)*values[j]for j,v in branch['affine_row']['coefficients'])<=F(branch['affine_row']['rhs'])for branch in literal['branches']]
            assert height==max(forms)
            assert rows==[value>=F(21,100)for value in forms]
            if height>F(21,100):assert any(rows)
            if height==F(21,100):thresholds+=1;assert any(rows)
            if sum(rows)>1:overlaps+=1
            numeric_controls+=1
    # An existing folder or old scalar receipt is not an accepted first-use gate.
    old=out/'existing_scalar_receipt';old.mkdir();write(old/'SCALAR_REPLAY.json',{'status':'old header only'})
    reject('old_scalar_folder_reuse',lambda:sources.fresh_scalar_gate_at_actual_use(old))
    # The checker may inspect all sources, but no proof/search/symbolic solver
    # package is loaded and the actual scalar entry point has not been called.
    assert not any(name.split('.')[0]in{'scipy','numpy','sympy','z3','highspy'}for name in sys.modules)
    assert local=={str(path):digest(path)for path in HERE.glob('*.py')}
    source_hashes=sources.check_unchanged()
    optimized=subprocess.run([sys.executable,'-O','-B','-S',str(HERE/'check_literal_cover_controls.py'),'--help'],capture_output=True,text=True)
    assert optimized.returncode!=0 and 'reject optimized Python'in optimized.stderr
    report=dict(status='PASS_PREPARED_C_HEIGHT_LITERAL_AND_SYMBOLIC_COMPLETE_COVER_CONTROLS',
        local_source_sha256=local,accepted_source_sha256=source_hashes,
        exact_callers=2,complete_closed_height_alternatives=4,
        complete_sign_quadrants=4,nonnegative_symbolic_residuals=16,attainment_identities=4,
        exact_height_triples=numeric_controls,threshold_face_controls=thresholds,overlap_controls=overlaps,
        damaged_literals_callers_or_source_reuse_rejected=len(rejected),rejected_controls=rejected,
        optimized_python_rejected=True,fresh_scalar_replayed=False,numerical_solver_called=False,
        ancestry_adapter_implemented=False,cover_installed=False,original_cell_credit=0,whole_mask_credit=0)
    write(out/'LITERAL_COVER_CONTROLS.json',report)
    print(json.dumps(dict(status=report['status'],damages=len(rejected),report_sha256=digest(out/'LITERAL_COVER_CONTROLS.json'))))
if __name__=='__main__':main()

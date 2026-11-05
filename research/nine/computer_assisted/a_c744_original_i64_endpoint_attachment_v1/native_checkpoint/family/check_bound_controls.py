#!/usr/bin/env python3
"""Literal/domain controls for the original-wide endpoint attachment."""
if not __debug__:raise RuntimeError('Exact controls require assertions.')
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
import hashlib,json,sys,tempfile
import independent_original_i64_bounds as I
import original_i64_bound_rows as P

def rejected(call):
    try:call()
    except (AssertionError,ValueError,KeyError,TypeError):return
    raise AssertionError('Damaged input accepted.')

def run(output):
    output=Path(output);assert not output.exists()
    binding=I.verify_binding();whole=I.read(binding['whole_original_parent']['path'])['record']['final']
    source_sha={str(p):I.sha(p)for p in I.HERE.rglob('*')if p.is_file()}
    rows=P.necessary_rows(whole,binding);assert len(rows)==414
    assert len({row[2]for row in rows})==414
    for row in rows:
        assert all(type(i)is int and 0<=i<54 for i,value in row[0])
        assert I.verify_literal(row,whole,binding)==row
    height=P.necessary_height_row(whole);assert I.verify_literal(height,whole,binding)==height
    descendant=deepcopy(whole);descendant['path'].append(['sat',[7,8],[7,0,1]])
    assert all(I.verify_literal(row,descendant,binding)==row for row in rows+[height])
    rejections=0
    for row in rows+[height]:
        co,rhs,name=row
        rejected(lambda co=co,rhs=rhs,name=name:I.verify_literal((co,rhs-F(1,10**8),name),whole,binding));rejections+=1
    sample=rows[0]
    for field,value in [('id','negative-887236b78100baf3'),('path',[]),('path',I.ORIGINAL_PATH[:-1]),
      ('angles',whole['angles'][:-1]),('positions',whole['positions'][:-1]),('scalar',whole['scalar'][:-1])]:
        bad=deepcopy(whole);bad[field]=value;rejected(lambda bad=bad:I.verify_literal(sample,bad,binding));rejections+=1
    for field,value in [('scope','ONE_CLOSED_MEMBER_OF_THE_COMPLETE_ACTUAL_AB_FIVE_COVER'),('valid_on_whole_original',False),
      ('original_id','foreign'),('original_path',[])]:
        bad=deepcopy(binding);bad[field]=value;rejected(lambda bad=bad:I.verify_literal(sample,whole,bad));rejections+=1
    co,rhs,name=sample
    for damaged in [(((54,F(1)),),rhs,name),(co,rhs,name.replace(I.BINDING_SHA,'0'*64)),
      (co,rhs,name+'_unknown'),(I.HEIGHT[0],F(-3,5),I.HEIGHT_NAME)]:
        rejected(lambda damaged=damaged:I.verify_literal(damaged,whole,binding));rejections+=1
    for field,value in [('id','foreign'),('path',[]),('angles',[['-1','1']]*9)]:
        bad=deepcopy(whole);bad[field]=value;rejected(lambda bad=bad:I.check_guard(bad));rejections+=1
    identity_cases=0
    for b,d,x in product(map(F,(-2,-1,0,1,2)),repeat=3):
        assert abs(x-b)+abs(d-x)==max(d-b,b-d,2*x-b-d,b+d-2*x);identity_cases+=1
    assert all(I.sha(path)==h for path,h in source_sha.items())
    I.verify_binding()
    report=dict(status='PASS_ORIGINAL_WIDE_I64_ENDPOINT_LITERAL_AND_DOMAIN_CONTROLS',binding_sha256=I.BINDING_SHA,
      endpoint_rows=414,separate_height_rows=1,original_and_descendant_literal_rebuilds=830,
      damaged_literals_or_callers_rejected=rejections,height_identity_cases=identity_cases,
      whole_original_implication_attached=True,source_arithmetic_rerun=False,historical_reuse_explicit=True,
      numerical_solver_run=False,source_sha256=source_sha,new_original_cells=0,new_masks=0)
    output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in('status','endpoint_rows','damaged_literals_or_callers_rejected')}),flush=True)

if __name__=='__main__':
    assert len(sys.argv)==2;run(sys.argv[1])

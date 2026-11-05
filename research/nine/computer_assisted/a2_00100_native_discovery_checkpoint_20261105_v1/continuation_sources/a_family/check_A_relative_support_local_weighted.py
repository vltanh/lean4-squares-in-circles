#!/usr/bin/env python3
"""Independent weighted arithmetic, conditional on saved intervals and old rows.
No original ancestry is replayed; no branch or original-cell closure is asserted.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'relative_support_chords_v1'))
import independent_relative_support_chords as VERIFY
source=HERE/'A_RELATIVE_SUPPORT_LOCAL_WEIGHTED_RECORD.json';raw=source.read_bytes();data=json.loads(raw);r=data['record']
state=r['propagated'];scalar=tuple(tuple(map(F,v))for v in state['scalar'])
diffs={tuple(e['pair']):tuple(tuple(map(F,v))for v in e['intervals'])for e in state['differences']}
rows={x['index']:x for x in r['printed_rows']};assert len(rows)==len(r['printed_rows'])
new={}
for i,x in rows.items():
    if not x['name'].startswith(VERIFY.PREFIX):continue
    lit=(tuple((k,F(v))for k,v in x['coefficients']),F(x['rhs']),x['name'])
    assert VERIFY.verify_literal(lit,scalar,diffs);new[i]=lit
assert new
bounds=list(map(F,r['absolute_variable_bounds']));assert all(b>=0 for b in bounds)
uses=0;used=set();deductions=0
for p in r['proposals']:
    coeff=[F(0)]*len(bounds);rhs=F(0);indices=set()
    for i,w in p['weights']:
        assert type(i)is int and type(w)is int and w>0 and i not in indices;indices.add(i)
        x=rows[i];weight=F(w,1<<40);rhs+=weight*F(x['rhs'])
        for k,v in x['coefficients']:coeff[k]+=weight*F(v)
        if i in new:used.add(i);uses+=1
    for k,c in p['objective']:coeff[k]-=F(c)
    assert rhs==F(p['summed_rhs'])
    assert [[k,str(v)]for k,v in enumerate(coeff)if v]==p['residual_coefficients']
    correction=sum(b*abs(c)for b,c in zip(bounds,coeff))
    assert correction==F(p['residual_correction'])
    assert rhs+correction==F(p['proved_upper'])<=F(p['upper'])
    deductions+=1
assert used==set(new)
# Two guarded negative controls on an actually weighted new literal.
first=next(iter(new.values()));damaged=0
try:VERIFY.verify_literal((first[0],first[1]+1,first[2]),scalar,diffs)
except AssertionError:damaged+=1
fields=first[2][len(VERIFY.PREFIX):].split('_');i,j,axis,sign=map(int,fields[1:5])
bad=deepcopy(diffs);ds=[list(v)for v in bad[i,j]]
if sign==1:ds[axis][0]=min(ds[axis][0],F(-1))
else:ds[axis][1]=max(ds[axis][1],F(1))
bad[i,j]=tuple(map(tuple,ds))
try:VERIFY.verify_literal(first,scalar,bad)
except AssertionError:damaged+=1
assert damaged==2
assert not any(n in sys.modules for n in('numpy','scipy','highspy','physical_relative_support_chords','owner_free_relative_support_snapshot'))
result={'status':'PASS_LOCAL_WEIGHTED_RELATIVE_SUPPORT_CONDITIONAL_ON_SAVED_INTERVALS_AND_OLD_ROWS','source_record_sha256':hashlib.sha256(raw).hexdigest(),'source':data['source'],'driver':data['driver'],'new_family_literals':len(new),'positive_multiplier_occurrences':uses,'deductions_exact_sum_checked':deductions,'damaged_literals_or_guards_rejected':damaged,'producer_imported':False,'numerical_library_imported':False,'original_ancestry_replayed':False,'all_old_row_geometry_rebuilt':False,'new_original_cells':0,'new_masks':0}
for name in('check_A_relative_support_local_weighted.py','verify_conditional_a3_relative_tree.py','relative_support_chords_v1/independent_relative_support_chords.py'):
    p=HERE/name;result.setdefault('checker_source_sha256',{})[name]=hashlib.sha256(p.read_bytes()).hexdigest()
(HERE/'A_RELATIVE_SUPPORT_LOCAL_WEIGHTED_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

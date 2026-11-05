"""Standalone generalized cone exact controls and conditional weighted replay."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import json,gzip,hashlib,sys
import independent_general_center_cone_rows as VERIFY
import verify_general_center_cone_controls as CONTROLS
HERE=Path(__file__).resolve().parent

def sha(raw):return hashlib.sha256(raw).hexdigest()
def literal(row):return tuple((j,F(c))for j,c in row['coefficients']),F(row['rhs']),row['name']
def rejected(label,callback):
 try:callback()
 except (AssertionError,ValueError,ZeroDivisionError,IndexError):return label
 raise AssertionError(('damaged control accepted',label))

def check_excerpt(data):
 assert data['schema']=='actual_weighted_original_center_cone_excerpt_v1'
 assert data['multiplier_denominator']==1<<40 and data['bound_rounding_grid']==1<<20
 assert data['other_printed_row_families_are_conditional_assumptions'] is True
 assert data['original_ancestry_or_mask_closure_claimed'] is False
 angles=tuple(tuple(map(F,a))for a in data['physical_angles'])
 bounds=tuple(map(F,data['absolute_variable_bounds']));n=len(bounds)
 assert n>=54 and all(b>=0 for b in bounds)
 rows={r['index']:r for r in data['rows']};assert len(rows)==len(data['rows'])
 cone=[]
 for index,row in rows.items():
  assert type(index)is int and index>=0
  terms,rhs,name=literal(row)
  assert all(type(j)is int and 0<=j<n and c for j,c in terms)
  assert list(terms)==sorted(terms)and len({j for j,c in terms})==len(terms)
  if name.startswith(VERIFY.PREFIX):VERIFY.verify_literal((terms,rhs,name),angles);cone.append(index)
 assert cone
 p=data['proposal'];kind,key,sign=p['kind'],p['key'],p['sign']
 assert type(sign)is int and sign in(-1,1)
 if kind=='scalar':
  assert type(key)is int and 0<=key<54;objective=[(key,sign)]
 else:
  assert kind in('difference','diagonal')and len(key)==3
  i,j,axis=key;assert all(type(t)is int for t in key)and 0<=i<j<9 and axis in(0,1)
  if kind=='difference':objective=[(2*j+axis,sign),(2*i+axis,-sign)]
  else:
   transverse=1 if axis==0 else -1
   objective=[(2*j,sign),(2*i,-sign),(2*j+1,sign*transverse),(2*i+1,-sign*transverse)]
 assert p['objective']==[list(t)for t in objective]
 weights=p['weights'];assert len(weights)==len({i for i,w in weights})
 assert {i for i,w in weights}==set(rows)
 coefficients=[F(0)]*n;rhs=F(0)
 for i,w in weights:
  assert type(i)is int and type(w)is int and w>0
  q=F(w,1<<40);terms,b,name=literal(rows[i]);rhs+=q*b
  for j,c in terms:coefficients[j]+=q*c
 for j,c in objective:coefficients[j]-=c
 correction=sum(b*abs(c)for b,c in zip(bounds,coefficients));proved=rhs+correction
 assert rhs==F(p['summed_rhs'])and correction==F(p['residual_correction'])and proved==F(p['proved_upper'])
 assert [[j,str(c)]for j,c in enumerate(coefficients)if c]==p['residual_coefficients']
 value=proved*(1<<20);ceiling=F(-((-value.numerator)//value.denominator),1<<20)
 assert F(p['upper'])==ceiling>=proved
 return dict(rows=len(rows),positively_weighted_cone_rows=len(cone),cone_indices=cone,proved_upper=str(proved),outward_upper=p['upper'],other_row_provenance_checked=False)

def main():
 assert __debug__
 provenance=json.loads((HERE/'PROVENANCE.json').read_text())
 for name,digest in provenance['files'].items():
  assert len(Path(name).parts)==1 and sha((HERE/name).read_bytes())==digest
 CONTROLS.main()
 controls=json.loads((HERE/'GENERAL_CENTER_CONE_CONTROLS.json').read_text())
 excerpt=json.loads((HERE/'ACTUAL_WEIGHTED_EXCERPT.json').read_text());actual=check_excerpt(excerpt)
 raw=gzip.decompress((HERE/'ACTUAL_WEIGHTED_BOUND_RECORD.json.gz').read_bytes());assert sha(raw)==excerpt['record_sha256']
 record=json.loads(raw);round=record['rounds'][excerpt['round_index']]
 assert round['proposals'][excerpt['proposal_index']]==excerpt['proposal']
 assert round['propagated']['angles']==excerpt['physical_angles']
 by_index={r['index']:r for r in round['printed_rows']}
 assert excerpt['rows']==[by_index[i]for i,w in excerpt['proposal']['weights']]
 general=[r for r in round['printed_rows']if r['name'].startswith(VERIFY.PREFIX)]
 for row in general:VERIFY.verify_literal(literal(row),round['propagated']['angles'])
 local=json.loads((HERE/'ACTUAL_WEIGHTED_LOCAL_REPLAY.json').read_text())
 assert local['status']=='PASS_INDEPENDENT_LOCAL_NEW_ROW_RECORD'and local['sha256']==sha(raw)
 assert local['numerical_modules_or_producers_imported']is False and local['new_row_counts']['general_cone']==len(general)>0
 rejects=[]
 damaged=deepcopy(excerpt);damaged['proposal']['weights'][0][1]*=-1;rejects.append(rejected('negative_dual_multiplier',lambda:check_excerpt(damaged)))
 damaged=deepcopy(excerpt);damaged['proposal']['upper']=str(F(damaged['proposal']['proved_upper'])-1);rejects.append(rejected('incorrect_outward_bound',lambda:check_excerpt(damaged)))
 damaged=deepcopy(excerpt);damaged['physical_angles']=[['-1','1']for _ in range(9)];rejects.append(rejected('actual_weighted_guard_removed',lambda:check_excerpt(damaged)))
 assert not any(n in sys.modules for n in('numpy','scipy','highspy'))
 report=dict(status='PASS_GENERAL_CENTER_CONE_PACKET',positive_literal_controls=controls['positive_literal_controls'],rejected_literal_guard_controls=controls['rejected_control_count'],weighted_rejection_controls=rejects,actual_weighted_excerpt=actual,full_saved_record_general_cone_rows=len(general),closed_endpoints_retained=True,new_original_cells=0,new_masks=0,packet_self_contained_for_new_row_family=True,full_older_row_provenance_or_original_ancestry_replayed=False,numerical_packages_imported=False)
 (HERE/'VERIFY_REPORT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()

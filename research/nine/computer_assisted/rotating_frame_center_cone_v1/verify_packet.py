"""Exact cone-family controls and a conditional actual weighted dual replay.
No numerical packages or external repository modules are required.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import json,gzip,hashlib,sys
import physical_center_cone_rows as PRODUCER
import independent_center_cone_rows as VERIFY
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
 # Exact polynomial coefficient identity underlying the universal support.
 r=F(91,60);cap=F(352321,232320);k=F(30,121)
 assert (2*r+1)*cap==F(977,256)+r*r and (2*r+1)*k==1
 lhs={(2,0):F(1),(0,2):F(1),(1,0):-2*r,(0,0):r*r}
 rhs={(2,0):F(1),(1,0):-2*r,(0,0):r*r,(0,2):F(1)}
 assert lhs==rhs
 positives=0;negative=[]
 for interval in [(F(0),F(0)),(-k,k),(-F(1,8),F(1,8)),(F(1,32),F(7,16)),(-F(7,16),-F(1,32))]:
  angles=tuple(interval for _ in range(9))
  generated=PRODUCER.generate(angles)
  assert generated
  for row in generated:assert VERIFY.verify_literal(row,angles)==row;positives+=1
 boundary=tuple((-k,k)for _ in range(9))
 for owner,axis,sign,nx,ny in [(0,0,1,1,0),(1,0,-1,-1,0),(2,1,1,0,1),(3,1,-1,0,-1)]:
  row=PRODUCER.row(boundary,owner,axis,sign,nx,ny);VERIFY.verify_literal(row,boundary);positives+=1
 valid=PRODUCER.row(boundary,0,0,1,1,0);terms,b,name=valid
 negative.append(rejected('changed_rhs',lambda:VERIFY.verify_literal((terms,b+F(1,1000),name),boundary)))
 altered=list(terms);altered[0]=(altered[0][0],altered[0][1]+F(1,1000))
 negative.append(rejected('changed_coefficient',lambda:VERIFY.verify_literal((tuple(altered),b,name),boundary)))
 negative.append(rejected('missing_coefficient',lambda:VERIFY.verify_literal((terms[:-1],b,name),boundary)))
 negative.append(rejected('duplicate_coefficient',lambda:VERIFY.verify_literal((terms+(terms[0],),b,name),boundary)))
 negative.append(rejected('wrong_owner',lambda:VERIFY.verify_literal((terms,b,VERIFY.PREFIX+'9_0_1_1_0'),boundary)))
 negative.append(rejected('wrong_axis',lambda:VERIFY.verify_literal((terms,b,VERIFY.PREFIX+'0_2_1_1_0'),boundary)))
 negative.append(rejected('wrong_sign',lambda:VERIFY.verify_literal((terms,b,VERIFY.PREFIX+'0_0_0_1_0'),boundary)))
 negative.append(rejected('zero_direction',lambda:VERIFY.verify_literal((terms,b,VERIFY.PREFIX+'0_0_1_0_0'),boundary)))
 negative.append(rejected('bad_parameter_encoding',lambda:VERIFY.verify_literal((terms,b,VERIFY.PREFIX+'0_0_1_bad_0'),boundary)))
 for side in(0,1):
  damaged=list(boundary);damaged[0]=(-k-F(1,4096),k)if side==0 else(-k,k+F(1,4096))
  negative.append(rejected('failed_closed_interval_guard_'+str(side),lambda damaged=damaged:VERIFY.verify_literal(valid,damaged)))
 zero_major=tuple((F(0),F(0))for _ in range(9))
 negative.append(rejected('zero_major_projection',lambda:VERIFY.verify_literal(((),F(0),VERIFY.PREFIX+'0_0_1_0_1'),zero_major)))
 excerpt=json.loads((HERE/'ACTUAL_WEIGHTED_EXCERPT.json').read_text());actual=check_excerpt(excerpt)
 source=gzip.decompress((HERE/'ACTUAL_WEIGHTED_BOUND_RECORD.json.gz').read_bytes())
 assert sha(source)==excerpt['record_sha256'];source_record=json.loads(source);source_round=source_record['rounds'][excerpt['round_index']]
 assert source_round['proposals'][excerpt['proposal_index']]==excerpt['proposal']
 assert source_round['propagated']['angles']==excerpt['physical_angles']
 by_index={row['index']:row for row in source_round['printed_rows']}
 assert excerpt['rows']==[by_index[i]for i,w in excerpt['proposal']['weights']]
 assert not any(row['name'].startswith('physical_rotating_frame_corner_tangent_')for row in source_round['printed_rows'])
 full_cones=[row for row in source_round['printed_rows']if row['name'].startswith(VERIFY.PREFIX)]
 for row in full_cones:VERIFY.verify_literal(literal(row),source_round['propagated']['angles'])
 replay=json.loads((HERE/'ACTUAL_WEIGHTED_LOCAL_REPLAY.json').read_text())
 assert replay['status']=='PASS_INDEPENDENT_LOCAL_NEW_ROW_RECORD'and replay['sha256']==sha(source)
 assert replay['numerical_modules_or_producers_imported']is False
 damaged=deepcopy(excerpt);damaged['proposal']['weights'][0][1]*=-1
 negative.append(rejected('negative_dual_multiplier',lambda:check_excerpt(damaged)))
 damaged=deepcopy(excerpt);damaged['proposal']['upper']=str(F(damaged['proposal']['proved_upper'])-1)
 negative.append(rejected('incorrect_outward_bound',lambda:check_excerpt(damaged)))
 damaged=deepcopy(excerpt);damaged['physical_angles']=[['-1','1']for _ in range(9)]
 negative.append(rejected('actual_weighted_guard_removed',lambda:check_excerpt(damaged)))
 assert not any(name in sys.modules for name in('numpy','scipy','highspy'))
 report=dict(status='PASS_ORIGINAL_CENTER_CONE_FAMILY_CONTROLS',positive_literal_controls=positives,rejected_control_count=len(negative),rejected_controls=negative,closed_endpoint_equality_retained=True,exact_completing_square_identity=True,actual_weighted_excerpt=actual,full_saved_record_cone_rows=len(full_cones),full_saved_record_local_replay_sha256=sha((HERE/'ACTUAL_WEIGHTED_LOCAL_REPLAY.json').read_bytes()),packet_self_contained_for_new_row_family=True,full_older_row_provenance_or_original_ancestry_replayed=False,new_original_cells=0,new_masks=0,numerical_packages_imported=False)
 (HERE/'VERIFY_REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))

if __name__=='__main__':main()

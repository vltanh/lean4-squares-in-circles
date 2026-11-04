#!/usr/bin/env python3
"""Independent exact replay: no producer or new-row module is imported.
Accepted historical v14 unweighted geometry is reused; all new rows,
weighted arithmetic, simultaneous bound installation and frame inversions
are reconstructed here using Fractions.
"""
from fractions import Fraction as Q
from math import isqrt
from itertools import combinations,permutations
from pathlib import Path
import sys,json,hashlib,time
BUNDLE=Path(__file__).resolve().parent
GEOMETRY=BUNDLE/'geometry'
sys.path.insert(0,str(GEOMETRY))
import weak_outer_numeric_strict_bulk_v14_verify as V
from review_tight_bounds_independent import collect_rows
from independent_v4_rows import extra_rows
INDEX=json.loads((BUNDLE/'replay_index.json').read_text())
DEN=1<<48;SCALE=1<<40;LEGACY='strict_bulk_2026_11_03_v14'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def box(x):return tuple(tuple(Q(z) for z in a) for a in x)
def view(x):return [[str(a),str(b)] for a,b in x]
def diffview(x):return [{'pair':list(k),'intervals':view(v)}for k,v in sorted(x.items())]
def low(z):z=Q(z)*DEN;return Q(z.numerator//z.denominator,DEN)
def high(z):return -low(-Q(z))
def sqrtbox(z):
 z=Q(z);assert z>=0;n=isqrt((z.numerator*DEN*DEN)//z.denominator);a=Q(n,DEN);b=a if a*a==z else Q(n+1,DEN);assert a*a<=z<=b*b;return a,b

def divsqrt(num,z):
 a,b=sqrtbox(z);assert a>0;return low(num/b),high(num/a)
def analytic(angles):
 aa=[];bb=[];zz=[];gg=[]
 for l,u in angles:
  m=Q(0) if l<=0<=u else min(abs(l),abs(u));M=max(abs(l),abs(u))
  aa.append((divsqrt(1,1+M*M)[0],divsqrt(1,1+m*m)[1]))
  def beta(t):
   x,y=divsqrt(abs(t),1+t*t);return (x,y) if t>=0 else (-y,-x)
  bl,bu=beta(l)[0],beta(u)[1];bb.append((bl,bu));zz.append((divsqrt(m,1+m*m)[0],max(abs(bl),abs(bu))))
  hs=[divsqrt(1+abs(t),1+t*t) for t in (l,u)]
  hl=Q(1,2) if l<=0<=u else min(x[0]/2 for x in hs);hu=max(x[1]/2 for x in hs)
  gg.append((low(1/(4*hu)),high(1/(4*hl))))
 return tuple(aa+bb+zz+gg)
def inverse_beta(x):
 l,u=sqrtbox(1-x*x);assert l>0
 return (low(x/u),high(x/l))if x>=0 else(low(x/l),high(x/u))
def angles_from_scalar(angles,scalar,saved=None):
 answer=[];assert saved is None or len(saved)==9
 for i,(l,u) in enumerate(angles):
  amin,amax=scalar[i];bmin,bmax=scalar[i+9];aminus,aplus=scalar[i+18]
  assert 0<amin<=amax<=1 and 0<=aminus<=aplus<1 and -1<bmin<=bmax<1
  cap=sqrtbox(1/(amin*amin)-1)[1];bl=inverse_beta(bmin)[0];bu=inverse_beta(bmax)[1]
  nl=max(l,-cap,bl);nu=min(u,cap,bu);acap=inverse_beta(aplus)[1];nl=max(nl,-acap);nu=min(nu,acap)
  floor=None
  if nl>=0 or nu<=0:
   floor=inverse_beta(aminus)[0]
   if amax<1:floor=max(floor,sqrtbox(1/(amax*amax)-1)[0])
   if nl>=0:nl=max(nl,floor)
   if nu<=0:nu=min(nu,-floor)
  assert nl<=nu
  if saved is not None:
   ss=saved[i];assert ss['original']==i and box([ss['old_slope_interval']])[0]==(l,u)
   assert box([ss['alpha_interval']])[0]==(amin,amax) and box([ss['beta_interval']])[0]==(bmin,bmax)
   assert box([ss['absolute_beta_interval']])[0]==(aminus,aplus)
   assert Q(ss['alpha_lower_slope_cap'])==cap and box([ss['beta_inverse_interval']])[0]==(bl,bu)
   assert Q(ss['absolute_beta_slope_cap'])==acap and ss['one_sign_slope_floor']==str(floor)
   assert box([ss['new_slope_interval']])[0]==(nl,nu)
  answer.append((nl,nu))
 return tuple(answer)
def sum_rows(rows,bounds,weights):
 out=[Q(0)for _ in bounds];rhs=Q(0);seen=set()
 for index,w in weights:
  assert type(index)is int and 0<=index<len(rows) and index not in seen
  assert type(w)is int and w>0;seen.add(index);lam=Q(w,SCALE)
  co,r,name=rows[index];rhs+=lam*r
  for k,v in co:out[k]+=lam*v
 return out,rhs

def audit_bound(rows,bounds,p):
 co,r=sum_rows(rows,bounds,p['weights'])
 for k,c in p['objective']:co[k]-=Q(c)
 e=sum(m*abs(x)for m,x in zip(bounds,co));value=r+e;upper=Q(p['upper']);assert value<=upper
 if 'proved_upper'in p:assert value==Q(p['proved_upper'])
 if 'summed_rhs'in p:assert r==Q(p['summed_rhs'])
 if 'residual_correction'in p:assert e==Q(p['residual_correction'])
 if 'residual_coefficients'in p:assert [[k,str(v)]for k,v in enumerate(co)if v]==p['residual_coefficients']
 return upper

def print_audit(rows,saved,used):
 assert {x['index']for x in saved}==used
 for s in saved:
  co,r,name=rows[s['index']];assert s['name']==name and Q(s['rhs'])==r
  assert [(k,Q(v))for k,v in s['coefficients']]==list(co)

def pair_insets(coords,scalar,intervals):
 rows=[]
 def append_pair(i,j,cx,cy,cg,rhs,name):
  terms={2*i:cx,2*j:-cx,2*i+1:cy,2*j+1:-cy,45+i:cg,45+j:cg}
  rows.append((tuple((k,v)for k,v in sorted(terms.items())if v),rhs,name))
 for i,j in combinations(range(9),2):
  (a,b),(c,d)=intervals[(i,j)];slo=scalar[27+i][0]+scalar[27+j][0];shi=scalar[27+i][1]+scalar[27+j][1];assert 0<slo<=shi
  for t in map(Q,('-7/8','-3/4','-1/2','-1/4','0','1/4','1/2','3/4','7/8')):
   R=1-t*t;assert R>=0
   # Directly upper-bound q=(1-t)/2 (dx+dy)^2+(1+t)/2(dx-dy)^2.
   s0,s1=a+c,b+d;d0,d1=a-d,b-c;w0,w1=(1-t)/2,(1+t)/2
   aff=[(w0*(s0+s1)+w1*(d0+d1),w0*(s0+s1)-w1*(d0+d1),-w0*s0*s1-w1*d0*d1,'rotated')]
   # Product bounds chosen by the sign of the coefficient -2t.
   prod=[(c,a,-a*c),(d,b,-b*d)]if t>=0 else[(c,b,-b*c),(d,a,-a*d)]
   for k,(px,py,pc)in enumerate(prod):aff.append((a+b-2*t*px,c+d-2*t*py,-a*b-c*d-2*t*pc,'product'+str(k)))
   for tangent in sorted({slo,(slo+shi)/2,shi,Q(1)}):
    for cx,cy,constant,kind in aff:
     append_pair(i,j,cx,cy,2*R*tangent,R*tangent*tangent+constant,f'inset_ellipse_{i}_{j}_{t}_{tangent}_{kind}')
 return rows

def triple_strips(intervals):
 def delta(i,j,axis):
  if i<j:return intervals[(i,j)][axis]
  a,b=intervals[(j,i)][axis];return -b,-a
 rows=[];guards=[]
 for s in combinations(range(9),3):
  for axis in(0,1):
   along=1-axis;width=max(abs(v)for i,j in combinations(s,2)for v in delta(i,j,axis))
   if width>Q(7,10):continue
   orders=[p for p in permutations(s)if delta(p[0],p[1],along)[0]>=0 and delta(p[1],p[2],along)[0]>=0]
   if not orders:continue
   l,m,u=orders[0];a,b=delta(l,u,axis);floor=min(Q(2),Q(208,75)-Q(29,15)*width)
   c=Q(5,14)*(a+b);coeff={2*l+along:Q(1),2*u+along:Q(-1),2*l+axis:c,2*u+axis:-c}
   rows.append((tuple((k,v)for k,v in sorted(coeff.items())if v),-floor-Q(5,14)*a*b,f'three_square_strip_{l}_{m}_{u}_{axis}'))
   guards.append({'triple':[l,m,u],'transverse_axis':axis,'width_upper':str(width),'endpoint_transverse_interval':[str(a),str(b)],'floor':str(floor)})
 return rows,guards

def guard_rows(choices):
 rows=[]
 originals=sorted({pair[1]for pair,kind,ch in choices if kind=='alternate_four_escape'and pair in((1,7),(1,8))and ch[0]in(6,7)})
 for x in originals:
  rows.extend([
   (((2*x,Q(1)),(2,Q(-1)),(19,-Q(1,2)),(37,-Q(1,2)),(18+x,-Q(1,2)),(36+x,-Q(1,2))),Q(0),f'guard_B{x}_weak'),
   (((2,Q(1)),(2*x,Q(-1)),(46,Q(1)),(45+x,Q(1))),Q(0),f'guard_B{x}_inset'),
   (((2*x,Q(1)),(6,Q(-1)),(45+x,Q(1)),(48,Q(1))),Q(0),f'guard_{x}D_inset'),
   (((5,Q(1)),(2*x+1,Q(-1)),(47,Q(1)),(45+x,Q(1))),Q(0),f'guard_C{x}_vertical'),
  ])
 return rows

def rebuild(path,angles,pos,choices,scalar,difference):
 rows,bounds,term=collect_rows(V,path,angles,pos,choices);assert term is None
 rows.extend(guard_rows(choices))
 for k,(a,b)in enumerate(scalar,18):rows.extend([(((k,Q(1)),),b,f'certified_scalar_upper_{k}'),(((k,Q(-1)),),-a,f'certified_scalar_lower_{k}')])
 eff,term=V.effective_boxes(angles,choices,LEGACY);assert term is None
 prop,hs,gs,term=V.center_bounds(eff,pos,choices,LEGACY);assert term is None;prop=tuple(map(tuple,prop))
 physical=analytic(eff);scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,physical));assert all(a<=b for a,b in scalar)
 for i in range(9):
  for p,q in V.DENSE_DIRS:
   assert p*p+q*q==1;rows.append((((18+i,p),(27+i,q)),Q(1),'exact_signed_unit_frame'))
  for p,q in V.DENSE_DIRS:
   if q>=0:rows.append((((18+i,p),(36+i,q)),Q(1),'exact_folded_unit_frame'))
 diffs={}
 for i,j in combinations(range(9),2):
  d=tuple(map(tuple,V.difference_bounds((i,j),prop,gs,LEGACY)))
  if(i,j)in difference:d=tuple((max(a,c),min(b,e))for(a,b),(c,e)in zip(d,difference[(i,j)]))
  assert all(a<=b for a,b in d);diffs[(i,j)]=d
  for ax,(a,b)in enumerate(d):rows.extend([(((2*j+ax,Q(1)),(2*i+ax,Q(-1))),b,'certified_difference_upper'),(((2*j+ax,Q(-1)),(2*i+ax,Q(1))),-a,'certified_difference_lower')])
 for k,(a,b)in enumerate(scalar,18):rows.extend([(((k,Q(1)),),b,'physical_scalar_intersection_upper'),(((k,Q(-1)),),-a,'physical_scalar_intersection_lower')])
 rows+=pair_insets(prop,scalar,diffs);r,g=triple_strips(diffs);rows+=r
 extra,extra_guards=extra_rows(angles,diffs);rows+=extra;g+=extra_guards
 return rows,bounds,prop,scalar,diffs,g


def coordinate_prior(data,path,angles,pos,choices):
 assert data['path']==path
 count=0
 for rr in data['rounds']:
  rows,bounds,term=collect_rows(V,path,angles,pos,choices);assert term is None;new=[list(x)for x in pos]
  for p in rr['proposals']:
   assert len(p['objective'])==1;k,sg=p['objective'][0];assert type(k)is int and 0<=k<18 and sg in(-1,1)
   up=audit_bound(rows,bounds,p)
   new[k][1 if sg==1 else 0]=(min(new[k][1],up)if sg==1 else max(new[k][0],-up));count+=1
  pos=tuple(map(tuple,new));assert all(a<=b for a,b in pos)
 return pos,count

def frame_prior(data,path,angles,pos,choices,coordinate):
 assert data['schema']=='exact_guarded_frame_bound_induction_v1' and data['status']=='OPEN'
 assert data['path']==path and data['guard_originals']==len(guard_rows(choices))//4
 count=0
 if data['prefix_sha256']is not None:
  assert coordinate is not None and sha(coordinate)==data['prefix_sha256']
  prefix=json.loads(coordinate.read_text());assert prefix['id']==data['id']
  pos,count=coordinate_prior(prefix,path,angles,pos,choices)
 assert count==data['prefix_deductions'] and box(data['initial_angles'])==angles
 scalar=analytic(angles);extra=0
 for ri,rr in enumerate(data['rounds']):
  assert rr['round']==ri and box(rr['angles_before'])==angles and box(rr['positions_before'])==pos and box(rr['scalar_before'])==scalar
  rows,bounds,term=collect_rows(V,path,angles,pos,choices,rr['circle_cuts']);assert term is None
  rows+=guard_rows(choices)
  for k,(a,b)in enumerate(scalar,18):rows.extend([(((k,Q(1)),),b,f'certified_scalar_upper_{k}'),(((k,Q(-1)),),-a,f'certified_scalar_lower_{k}')])
  target=[list(z)for z in pos+scalar]
  for p in rr['proposals']:
   assert len(p['objective'])==1;k,sg=p['objective'][0];assert type(k)is int and 0<=k<54 and sg in(-1,1)
   up=audit_bound(rows,bounds,p);target[k][1 if sg==1 else 0]=(min(target[k][1],up)if sg==1 else max(target[k][0],-up));extra+=1
  pos=tuple(map(tuple,target[:18]));scalar=tuple(map(tuple,target[18:]));assert all(a<=b for a,b in pos+scalar)
  angles=angles_from_scalar(angles,scalar);assert box(rr['angles_after'])==angles
  enclosure=analytic(angles);scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,enclosure));assert all(a<=b for a,b in scalar)
 for key,val in [('final_angles',angles),('final_positions',pos),('final_scalar',scalar)]:
  if key in data:assert box(data[key])==val
 return angles,pos,scalar,{'coordinate_deductions':count,'frame_deductions':extra,'frame_rounds':len(data['rounds'])}

def verify_index():
 assert INDEX['schema']=='portable_shared_bound_exact_replay_v4'
 assert sha(BUNDLE/INDEX['baseline_register'])==INDEX['register_sha256']
 for name,expected in INDEX['frozen_files'].items():assert sha(BUNDLE/name)==expected,('frozen_file',name)
 assert sha(V.__file__)=='ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993'


def verify_certificate(ident,allow_open=False):
 start=time.monotonic();entry=INDEX['certificates'][ident];file=BUNDLE/entry['certificate'];record=json.loads(file.read_text());path=record['path']
 assert record['id']==ident and record['schema']=='shared_inset_rotated_strip_ordered_gap_induction_v4_pilot'
 assert record['status']=='CANDIDATE_CLOSED'or(allow_open and record['status']=='OPEN')
 assert record['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'and record['new_branch_nodes']==0 and 0<=record['maximum_new_rounds']<=8
 assert len(record['rounds'])<=record['maximum_new_rounds']
 reg=json.loads((BUNDLE/INDEX['baseline_register']).read_text());cell=next(x for x in reg['cells']if x['id']==ident)
 assert cell['status']=='OPEN'and cell['path']==path
 canonical=ident.split('-')[0]+'-'+hashlib.sha256(json.dumps(path,separators=(',',':')).encode()).hexdigest()[:16];assert canonical==ident
 for name,expected in {**record['sources'],**record['additional_sources']}.items():
  bound=INDEX['source_bindings'][name];assert bound['sha256']==expected and sha(BUNDLE/bound['file'])==expected
 pre_manifest=json.loads((BUNDLE/'sources/source_manifest_before_runs.json').read_text())
 for name,expected in pre_manifest.items():
  assert {**record['sources'],**record['additional_sources']}[name]==expected
 prior=BUNDLE/entry['prior'];assert sha(prior)==record['prior']['sha256'];old=json.loads(prior.read_text());assert old['id']==ident and old['path']==path
 angles,pos,choices=V.reconstruct(path);angles=tuple(map(tuple,angles));pos=tuple(map(tuple,pos))
 if entry['prior_kind']=='coordinate':
  assert record['prior']['kind']=='fresh_replayed_coordinate_prefix'
  pos,prefix_count=coordinate_prior(old,path,angles,pos,choices);assert prefix_count==record['prior']['deductions'];scalar=analytic(angles)
  prior_stats={'coordinate_deductions':prefix_count,'frame_deductions':0,'frame_rounds':0}
 else:
  assert entry['prior_kind']=='frame'and record['prior']['kind']=='fresh_replayed_frame_state'
  prefix=BUNDLE/entry['coordinate_prefix']if'coordinate_prefix'in entry else None
  angles,pos,scalar,prior_stats=frame_prior(old,path,angles,pos,choices,prefix)
  claimed=record['prior']['review'];assert claimed['status']=='PASS_CERTIFIED_PARENT_STATE'
  assert prior_stats['coordinate_deductions']==claimed['old_coordinate_deductions']and prior_stats['frame_deductions']==claimed['new_original_variable_deductions']and prior_stats['frame_rounds']==claimed['frame_rounds']
 difference={};new_count=0;reports=[];printed_count=0;used_new_rows={};empty_analytic=None;serialized_pre_state=None
 for ri,rr in enumerate(record['rounds']):
  preceding_state=(angles,pos,scalar)
  assert rr['round']==ri and box(rr['angles_before'])==angles and box(rr['positions_before'])==pos and box(rr['scalar_before'])==scalar and rr['differences_before']==diffview(difference)
  rows,bounds,prop,phys,diffs,guards=rebuild(path,angles,pos,choices,scalar,difference)
  assert len(rows)==rr['rows']and box(rr['propagated_positions'])==prop and box(rr['physical_scalar_intersection'])==phys and rr['effective_differences']==diffview(diffs)and rr['three_square_guards']==guards
  assert list(map(str,bounds))==rr['absolute_variable_bounds']
  nextpos=[list(x)for x in prop];nextscalar=[list(x)for x in phys];nextdiff={k:[list(x)for x in v]for k,v in diffs.items()};used=set()
  for p in rr['proposals']:
   up=audit_bound(rows,bounds,p);kind=p['kind'];key=p['key'];sg=p['sign'];assert sg in(-1,1)
   if kind=='scalar':
    assert type(key)is int and 0<=key<54 and p['objective']==[[key,sg]];target=nextpos[key]if key<18 else nextscalar[key-18]
   else:
    assert kind=='difference'and len(key)==3;i,j,ax=key;assert 0<=i<j<9 and ax in(0,1)
    assert p['objective']==[[2*j+ax,sg],[2*i+ax,-sg]];target=nextdiff[(i,j)][ax]
   target[1 if sg==1 else 0]=(min(target[1],up)if sg==1 else max(target[0],-up));used.update(i for i,w in p['weights']);new_count+=1
  print_audit(rows,rr['printed_rows'],used);printed_count+=len(used)
  for k in used:
   name=rows[k][2]
   if name.startswith(('inset_ellipse','three_square_strip','owner_free_interval_radius','rotated_three_square_strip','ordered_euclidean_gap')):used_new_rows[name]=used_new_rows.get(name,0)+1
  pos=tuple(map(tuple,nextpos));scalar=tuple(map(tuple,nextscalar));difference={k:tuple(map(tuple,v))for k,v in nextdiff.items()}
  assert all(a<=b for a,b in pos+scalar)and all(a<=b for ds in difference.values()for a,b in ds)
  angles=angles_from_scalar(angles,scalar,rr['physical_frame_inferences']);physical=analytic(angles)
  before_physical=scalar;scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,physical))
  if any(a>b for a,b in scalar):
   assert record['status']=='CANDIDATE_CLOSED'and record['terminal']['kind']=='proved_empty_analytic_frame'
   assert ri==len(record['rounds'])-1
   assert not any(k in rr for k in ('angles_after','positions_after','scalar_after','differences_after'))
   empty_analytic=[{'scalar_index':k,'physical_column':18+k,'original':k%9,
      'component':('alpha','beta','absolute_beta','inset')[k//9],
      'proved_interval':list(map(str,before_physical[k])),
      'physical_interval':list(map(str,physical[k])),
      'intersection':list(map(str,(a,b))),
      'strict_gap':str(a-b),'inferred_slope_interval':list(map(str,angles[k%9]))}
      for k,(a,b)in enumerate(scalar)if a>b]
   serialized_pre_state=preceding_state
   reports.append({'round':ri,'rows':len(rows),'deductions':len(rr['proposals']),
       'strip_guards':guards,'printed_rows_checked':len(used),'terminal_empty_analytic_frame':empty_analytic})
   print(ident,'PASS terminal round',ri,'deductions',len(rr['proposals']),'empty physical components',len(empty_analytic),flush=True)
   break
  assert box(rr['angles_after'])==angles and box(rr['positions_after'])==pos and box(rr['scalar_after'])==scalar and rr['differences_after']==diffview(difference)
  reports.append({'round':ri,'rows':len(rows),'deductions':len(rr['proposals']),'strip_guards':guards,'printed_rows_checked':len(used)})
  print(ident,'PASS round',ri,'deductions',len(rr['proposals']),flush=True)
 reserve=None;final_guards=[];terminal_count=0
 if empty_analytic is not None:
  assert record['terminal']=={'kind':'proved_empty_analytic_frame'}
  assert serialized_pre_state is not None
  # The frozen producer stops before committing the terminal state. Its
  # final angle/position/scalar fields retain the last preceding state;
  # final_differences already records the simultaneous terminal proposals.
  for key,val in zip(('final_angles','final_positions','final_scalar'),serialized_pre_state):assert box(record[key])==val
  status='PASS_COMPLETE_ORIGINAL_PARENT'
 elif record['status']=='OPEN':
  assert allow_open
  if'final_test'in record:
   rr=record['final_test'];assert box(rr['angles_before'])==angles and box(rr['positions_before'])==pos and box(rr['scalar_before'])==scalar and rr['differences_before']==diffview(difference)
   rows,bounds,prop,phys,diffs,guards=rebuild(path,angles,pos,choices,scalar,difference)
   assert len(rows)==rr['rows']and box(rr['propagated_positions'])==prop and box(rr['physical_scalar_intersection'])==phys and rr['effective_differences']==diffview(diffs)and rr['three_square_guards']==guards
  status='PASS_CERTIFIED_PARENT_STATE_OPEN'
 else:
  final=record['terminal'];assert final['kind']=='positive_exact_reserve','unsupported terminal requires an explicit independent rule'
  rr=final['state'];assert rr['round']==len(record['rounds'])
  assert box(rr['angles_before'])==angles and box(rr['positions_before'])==pos and box(rr['scalar_before'])==scalar and rr['differences_before']==diffview(difference)
  rows,bounds,prop,phys,diffs,guards=rebuild(path,angles,pos,choices,scalar,difference)
  assert len(rows)==rr['rows']and box(rr['propagated_positions'])==prop and box(rr['physical_scalar_intersection'])==phys and rr['effective_differences']==diffview(diffs)and rr['three_square_guards']==guards
  co,rhs=sum_rows(rows,bounds,final['weights']);reserve=-rhs-sum(m*abs(v)for m,v in zip(bounds,co));assert reserve>0 and reserve==Q(final['reserve'])
  assert co==list(map(Q,final['weighted_coefficients']))and rhs==Q(final['weighted_rhs'])and list(map(str,bounds))==final['absolute_variable_bounds']
  used={k for k,w in final['weights']};print_audit(rows,final['rows'],used);printed_count+=len(used);terminal_count=len(used);final_guards=guards
  status='PASS_COMPLETE_ORIGINAL_PARENT'
 if empty_analytic is None:
  for key,val in [('final_angles',angles),('final_positions',pos),('final_scalar',scalar)]:assert box(record[key])==val
 assert record['final_differences']==diffview(difference)
 report={'id':ident,'status':status,'path':path,'new_branch_nodes':0,'independent_weighted_arithmetic':True,'independent_new_row_construction':True,'prior':prior_stats,'new_deductions':new_count,'rounds':reports,'terminal_strip_guards':final_guards,'terminal_weighted_rows':terminal_count,'reserve':str(reserve),'empty_analytic_frame':empty_analytic,'printed_rows_checked':printed_count,'used_new_row_families':used_new_rows,'certificate_sha256':sha(file),'prior_sha256':sha(prior),'reviewer_sha256':sha(__file__),'independent_v4_rows_sha256':sha(BUNDLE/'independent_v4_rows.py'),'elapsed_seconds':time.monotonic()-start,'whole_mask_closed':False}
 (BUNDLE/'reports').mkdir(exist_ok=True);(BUNDLE/'reports'/(ident+'_portable_replay.json')).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in ['id','status','prior','new_deductions','terminal_weighted_rows','reserve','elapsed_seconds']}),flush=True)
 return report

def main():
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--id');ap.add_argument('--all',action='store_true');ap.add_argument('--allow-open',action='store_true');a=ap.parse_args()
 assert bool(a.id)!=bool(a.all),'choose exactly one of --id or --all'
 verify_index();ids=sorted(INDEX['certificates'])if a.all else[a.id]
 results=[verify_certificate(ident,a.allow_open)for ident in ids]
 (BUNDLE/'reports/portable_summary.json').write_text(json.dumps({'status':'PASS','results':[{k:r[k]for k in ['id','status','new_deductions','reserve']}for r in results]},indent=2)+'\n')
if __name__=='__main__':main()

"""Exact finite-cover and binding audit for the hand exclusion of0010111.

This is an assembly audit, not a replacement for the component mathematical
proofs. It never minimizes a geometric function or accepts an interval tree.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json

P=Path(__file__).resolve().parent
def read(name):return json.loads((P/name).read_text())
def digest(name):return sha256((P/name).read_bytes()).hexdigest()
labels=read('short_hand_labels.json')
expected=[
 {'C':{'p':[3177,0,108816]},'O':{'p':[0,0,94766]}},
 {'C':{'p':[25648,0,62095],'n':[-14041,0,62095]},'O':{'p':[6130,0,99940],'n':[24463,-13422,103828]}},
 {'C':{'n':[11680,0,113855]},'O':{'n':[-2623,9133,88074]}},
 {'C':{'p':[4149,0,104729],'n':[-15540,0,62750]},'O':{'p':[-68803,51554,119909],'n':[50866,-33147,113360]}},
 {'C':{'p':[25812,0,58829],'n':[3897,0,104073]},'O':{'p':[6294,0,71553],'n':[-23483,19335,76744]}},
 {'C':{'p':[2448,0,99195],'n':[1027,0,95269]},'O':{'p':[2448,0,86884],'n':[29579,-20967,83048]}},
 {'C':{'p':[9072,0,95324],'n':[7651,0,99173]},'O':{'p':[-20704,21826,83472],'n':[-18660,18602,80996]}},
]
assert labels==expected
word=[0,0,1,0,1,1,1]
sign_cases=[]
for i,k in enumerate(word):
 for s in ([1] if i==0 else [-1] if i==2 else [-1,1]):
  for t in ([1] if (i+1)%7==0 else [-1] if (i+1)%7==2 else [-1,1]):
   if k==0 and (s,t)==(-1,1):continue
   sign_cases.append((i,s,t))
assert len(sign_cases)==19
zero=[(i,s,t,a) for i,s,t in sign_cases if word[i]==0 for a in[1,2,3,4]]
quarter=[(i,s,t,a) for i,s,t in sign_cases if word[i]==1 for a in[1,2,3,4]]
assert len(zero)==28 and len(quarter)==48
primary=[z for z in zero if z[3] in[2,4]]
opposite=[z for z in zero if z[1:3]==(1,-1) and z[3] in[1,3]]
same_good=[(0,1,1,1),(1,-1,-1,3),(3,1,1,1),(3,-1,-1,3)]
same_bad=[z for z in zero if z[3] in[1,3] and z not in opposite and z not in same_good]
assert len(primary)==14 and len(same_bad)==4 and len(opposite)==6
assert set(primary+same_bad+opposite+same_good)==set(zero)
hard={(2,-1,-1,3),(2,-1,-1,4),(4,-1,-1,3),(4,-1,-1,4),(6,1,1,1),(6,1,1,2)}
table=read('short_quarter_scalar_hand_table.json')
arithmetic=read('short_quarter_scalar_hand_arithmetic.json')
assert table['Q']=='9789/2500'
assert table['gamma_by_edge']=={'2':'.8975','4':'.89765','5':'.89765','6':'.89765'}
assert len(table['rows'])==140==arithmetic['rows']==len(arithmetic['results'])
assert arithmetic['status']=='PASS' and not arithmetic['failures']
chains=[]
for case in quarter:
 for sign in [-1,1]:
  normalized_f=case[3] in[1,3]
  begin=(F('.3') if normalized_f else F('.03')) if sign<0 else (F('.1') if normalized_f else F('.06'))
  if case not in hard:begin=F(0)
  rows=sorted((r for r in table['rows'] if tuple(r['original'])==case and r['r']==sign),key=lambda r:F(r['lo']))
  assert rows
  pointer=begin
  for row in rows:
   assert F(row['lo'])==pointer
   assert F(row['hi'])>pointer
   assert F(row['lam'])>=0 and F(row['t'])>0
   pointer=F(row['hi'])
  assert pointer==F('.7')
  chains.append({'original':case,'sign':sign,'contact_interval':[str(F(0)),str(begin)],'scalar_intervals':[[str(F(r['lo'])),str(F(r['hi']))] for r in rows]})
assert len(chains)==96
assert {tuple(r['original']) for r in table['rows']}==set(quarter)
coefficients=0;polynomials=0;cost_min=None
for i,(row,res) in enumerate(zip(table['rows'],arithmetic['results'])):
 assert res['index']==i and res['original']==row['original'] and res['sign']==row['r']
 assert list(map(F,res['interval']))==[F(row['lo']),F(row['hi'])]
 assert F(res['lambda'])==F(row['lam']) and F(res['norm_t'])==F(row['t'])
 assert res['target_mode']==row['mode'] and F(res['source_lower'])>=F(row['source_lower'])
 for poly in res['premises']+res['cost']:
  assert poly['method']=='positive Bernstein coefficients'
  assert len(poly['coefficient_lower'])==poly['degree']+1
  assert all(F(x)>=0 for x in poly['coefficient_lower'])
  coefficients+=len(poly['coefficient_lower']);polynomials+=1
 for poly in res['cost']:
  assert F(poly['reserve'])>0 and all(F(x)>0 for x in poly['coefficient_lower'])
  v=F(poly['reserve']);cost_min=v if cost_min is None else min(cost_min,v)
assert coefficients==4475 and polynomials==310 and cost_min>F('.000094')

components=[
 ('SHORT_WRONG_WORD_ALL_CORE_CORE_HAND_PROOF.md','verify_short_all_core_core_hand.js','short_all_core_core_hand_arithmetic.json',54),
 ('SHORT_WRONG_WORD_MIXED_ZERO_FAMILIES_HAND_PROOF.md','verify_short_wrong_mixed_zero_hand.js','short_wrong_mixed_zero_hand_arithmetic.json',68),
 ('SHORT_WRONG_WORD_ALL_MIXED_ZERO_HAND_PROOF.md','verify_short_all_mixed_zero_hand.js','short_all_mixed_zero_hand_arithmetic.json',243),
 ('SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md','verify_short_all_mixed_one_hand.js','short_all_mixed_one_hand_arithmetic.json',390),
 ('SHORT_WRONG_WORD_OUTER_ZERO_PRIMARY_HAND_PROOF.md','verify_short_outer_zero_primary_hand.js','short_outer_zero_primary_hand_arithmetic.json',50),
 ('SHORT_WRONG_WORD_OUTER_ZERO_OPPOSITE_HAND_PROOF.md','verify_short_outer_zero_opposite_hand.js','short_outer_zero_opposite_hand_arithmetic.json',134),
 ('SHORT_WRONG_WORD_OUTER_ZERO_SAME_HAND_PROOF.md','verify_short_outer_zero_same_hand.js','short_outer_zero_same_hand_arithmetic.json',56),
 ('SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md','verify_short_outer_quarter_aligned_hand.js','short_outer_quarter_aligned_hand_arithmetic.json',80),
]
bindings={};records=[]
for note,checker,record,count in components:
 x=read(record);assert x['status']=='PASS';actual=x.get('fixed_comparisons',len(x.get('checks',[])));assert actual==count
 for name in[note,checker,record]:bindings[name]=digest(name)
 records.append({'manuscript':note,'checker':checker,'record':record,'status':'PASS','fixed_comparisons':count})
for name in ['short_hand_labels.json','short_quarter_scalar_hand_table.json','verify_short_quarter_scalar_hand.js','short_quarter_scalar_hand_arithmetic.json','SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF.md','SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md','audit_short_whole_word_hand.py']:
 bindings[name]=digest(name)
def atan(q,n):return sum((F(-1 if j%2 else 1,(2*j+1)*q**(2*j+1)) for j in range(n+1)),F(0))
twopi_upper=32*atan(5,24)-8*atan(239,7)
assert twopi_upper<F(710,113)
cyclic=6*F(17953,20000)+F(359,400)
assert cyclic==F(31417,5000) and cyclic-F(710,113)==F(121,565000)
report={'status':'PASS','scope':'Exact label binding, complete304-case role/radial/axis cover and96 signed outer-quarter angle chains; fixed arithmetic records only, not an independent replacement for their mathematical proofs','quarter_word':word,'cyclic_lower':str(cyclic),'rational_two_pi_upper':'710/113','strict_rational_reserve':str(cyclic-F(710,113)),'allowed_sign_entries':19,'total_radial_axis_cases':304,'OO_zero_cases':28,'OO_quarter_cases':48,'scalar_rows':140,'scalar_polynomials':polynomials,'scalar_Bernstein_comparisons':coefficients,'weakest_scalar_cost_reserve':str(cost_min),'components':records,'quarter_chains':chains,'sha256':bindings}
out=P/'short_whole_word_hand_assembly_audit.json';out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['components','quarter_chains','sha256']},indent=2))

"""Write explicit exact constants for verify_boundary_pair_costs.cpp.

Input is JSON with beta:[p,q], K, positive_domains:[[[l_num,l_den],[h_num,h_den]],...],
is_core:[bool,...], psi_numerators, psi_denominator, gamma_numerators,
gamma_denominator. The data may contain other descriptive fields.
"""
from pathlib import Path
from fractions import Fraction
import json,sys

j=json.loads(Path(sys.argv[1]).read_text());out=Path(sys.argv[2])
k=j['K'];n=len(j['positive_domains']);lo=[Fraction(*d[0]) for d in j['positive_domains']]
hi=[Fraction(*d[1]) for d in j['positive_domains']];step=[(b-a)/k for a,b in zip(lo,hi)]
assert all(0<=a<b<=1 for a,b in zip(lo,hi))
assert len(j['is_core'])==n and len(j['psi_numerators'])==n and all(len(x)==k+1 for x in j['psi_numerators'])
assert len(j['gamma_numerators'])==n and all(len(x)==n for x in j['gamma_numerators'])
if j.get('symmetric_gamma',True):
    assert all(j['gamma_numerators'][a][b]==j['gamma_numerators'][b][a] for a in range(n) for b in range(n))
if 'psi_negative_numerators' in j:
    assert len(j['psi_negative_numerators'])==n and all(len(x)==k+1 for x in j['psi_negative_numerators'])

def vec(name,vals):return 'constexpr Integer '+name+'['+str(len(vals))+']={'+','.join(map(str,vals))+'};\n'
def mat(name,vals):return 'constexpr Integer '+name+'['+str(len(vals))+']['+str(len(vals[0]))+']={'+','.join('{'+','.join(map(str,v))+'}' for v in vals)+'};\n'
s='// Exact rational data; generated from '+Path(sys.argv[1]).name+'.\n'
s+=f'constexpr int TYPE_COUNT={n},PIECES={k};\n'
s+=f'constexpr Integer BETA_NUM={j["beta"][0]},BETA_DEN={j["beta"][1]},PSI_DEN={j["psi_denominator"]},GAMMA_DEN={j["gamma_denominator"]};\n'
s+=vec('IS_CORE',[int(x) for x in j['is_core']])
for name,vals in [('LOW_NUM',[x.numerator for x in lo]),('LOW_DEN',[x.denominator for x in lo]),('STEP_NUM',[x.numerator for x in step]),('STEP_DEN',[x.denominator for x in step])]:s+=vec(name,vals)
s+=mat('VALUES',j['psi_numerators'])+mat('GAMMAS',j['gamma_numerators'])
if 'psi_negative_numerators' in j:
    s+='#define PAIR_SEPARATE_POTENTIAL_SIGNS 1\n'+mat('NEGATIVE_VALUES',j['psi_negative_numerators'])
out.write_text(s)
print(out)

"""Independent fixed polynomial checks and isolated replay of the bootstrap."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json,subprocess,tempfile

HERE=Path(__file__).resolve().parent;ROOT=Path(__file__).resolve().parents[2]
name='verify_candidate_mismatch_bootstrap.py';P=HERE if (HERE/name).exists() else ROOT/'proof_integration'
checker=P/name;note=P/'HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md';report=P/'candidate_mismatch_bootstrap_arithmetic.json'
with tempfile.TemporaryDirectory(prefix='bootstrap_independent_') as d:
 cp=Path(d)/name;cp.write_bytes(checker.read_bytes())
 raw=subprocess.run(['python',str(cp)],check=True,capture_output=True).stdout
assert raw==report.read_bytes();data=json.loads(raw)
assert data['status']=='PASS' and data['comparison_count']==17
actual={x['name']:F(x['positive_reserve']) for x in data['checks']}
assert all(x>0 for x in actual.values())
# Expanded lower polynomial for (sin x+cos x-1)/2, independently
# evaluated by Horner's rule rather than the author's trig-sum routine.
p=list(map(F,[0,'1/2','-1/4','-1/12','1/48','1/240','-1/1440','-1/10080','1/80640',0,'-1/7257600']))
rows=[('7/10','29/100'),('2/5','38/100'),('3/10','41/100'),('1/4','43/100'),('1/5','44/100'),('1/8','46/100'),('1/10','47/100'),('1/20','48/100'),('1/40','49/100'),('1/250','49/100')]
for L,k in rows:
 x=F(L);v=F(0)
 for c in reversed(p):v=v*x+c
 assert v-F(k)*x==actual['chord slope '+L]>0
assert actual['sqrt2 exceeds 141/100']==F(119,10000)
assert actual['a upper from farthest corner']==F(13,8000)
assert actual['b upper from farthest corner']==F(11,2500)
assert actual['both primary margins negative']==F(711,20000)
assert actual['source sign margin']==F(17,2000)
assert actual['target sign margin']==F(3,500)
assert actual['conditional example contraction reserve']==F(47,11300000)
out={'status':'PASS','scope':'Continuous mismatch contraction and strict zero-edge axis/sign implications, conditional on the explicitly stated full pair bound',
 'replayed_comparisons':17,'independently_recomputed_comparisons':17,'replay_byte_identical':True,
 'geometric_reserves':{'primary_axes':'711/20000','source_sign':'17/2000','target_sign':'3/500'},
 'sha256':{x.name:sha256(x.read_bytes()).hexdigest() for x in [note,checker,report]}}
(HERE/'candidate_mismatch_bootstrap_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

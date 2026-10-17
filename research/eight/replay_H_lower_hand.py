"""Replay the fixed table and compare all compact records, without discovery."""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
import json
import subprocess
import sys

P=Path(__file__).resolve().parent
compact=json.loads((P/'H_LOWER_AFFINE_HAND_COMPACT_REPORT.json').read_text())
for name in ['H_LOWER_AFFINE_HAND_DATA.json','verify_H_lower_affine_hand.js']:
 assert sha256((P/name).read_bytes()).hexdigest()==compact['sha256'][name]
out=subprocess.run(['node',str(P/'verify_H_lower_affine_hand.js'),str(P/'H_LOWER_AFFINE_HAND_DATA.json')],check=True,capture_output=True).stdout
digest=sha256(out).hexdigest()
assert digest==compact['sha256']['H_LOWER_AFFINE_HAND_ARITHMETIC.json']
full=json.loads(out)
assert full['status']=='PASS' and full['cover']['status']=='PASS' and not full['failures']
assert full['rows']==full['passed']==compact['rows']==compact['passed']
assert full['cover']['angle_chains']==compact['cover']['angle_chains']
records=[]
for row in full['results']:
 rec=[]
 for field in ['premises','cost']:
  rec.append([[p['degree'],min(p['coefficient_lower'],key=Fraction)] for p in row[field]])
 records.append(rec)
assert len(records)==len(compact['row_records'])
for actual,stored in zip(records,compact['row_records']):
 for a,b in zip(actual,stored):
  assert len(a)==len(b)
  assert all(d==e and Fraction(v)==Fraction(w) for (d,v),(e,w) in zip(a,b))
assert sum(len(a)+len(b) for a,b in records)==compact['polynomials']
assert sum(d+1 for a,b in records for d,_ in a+b)==compact['coefficients']
if '--save-full' in sys.argv:
 (P/'H_LOWER_AFFINE_HAND_ARITHMETIC.json').write_bytes(out)
print(json.dumps({'status':'PASS','rows':full['rows'],'angle_chains':full['cover']['angle_chains'],
 'polynomials':compact['polynomials'],'coefficients':compact['coefficients'],
 'full_replay_sha256':digest},indent=2))

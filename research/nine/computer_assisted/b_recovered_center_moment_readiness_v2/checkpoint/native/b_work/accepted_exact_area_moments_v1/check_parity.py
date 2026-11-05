"""Portable complete literal comparison on the two recorded interval inputs."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import json,sys,time
import reference_square_area_moment_rows as REF
import fast_exact_area_moments as FAST
ROOT=Path(__file__).resolve().parent
assert __debug__
data=json.loads((ROOT/'PARITY_INPUTS.json').read_text())
assert sha256(Path(REF.__file__).read_bytes()).hexdigest()==data['reference_sha256']
matrices=list(REF.axes_matrices())+[((F(1),F(1)),(F(-1),F(1))),((F(2),F(1)),(F(0),F(1))),((F(2),F(-1)),(F(0),F(1))),((F(1),F(0)),(F(1),F(2))),((F(1),F(0)),(F(-1),F(2)))]
old=FAST.install(REF);audits=[]
for case in data['cases']:
    ds={tuple(e['pair']):tuple(tuple(map(F,ab))for ab in e['intervals'])for e in case['differences']}
    t=time.monotonic();reference=old(ds,matrices=matrices);before=time.monotonic()-t
    t=time.monotonic();result=REF.generate_linear(ds,matrices=matrices);after=time.monotonic()-t
    assert result==reference
    assert REF.generate_linear(ds,matrices=matrices)==reference
    audits.append(dict(case=case['id'],rows=len(reference),all_literals_and_order_identical=True,reference_seconds=before,optimized_seconds=after))
report=dict(status='PASS_COMPLETE_EXACT_LITERAL_PARITY',cases=len(audits),rows_compared=sum(a['rows']for a in audits),audits=audits,source_sha256={Path(p).name:sha256(Path(p).read_bytes()).hexdigest()for p in(__file__,REF.__file__,FAST.__file__,ROOT/'PARITY_INPUTS.json')},changed_geometric_rows=0,new_original_cells=0,new_masks=0)
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('source_sha256','audits')}))

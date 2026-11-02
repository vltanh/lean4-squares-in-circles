"""Deliberately corrupted finite covers must be rejected by the exact checker."""
import hashlib,json
from pathlib import Path
from verify_upper_central_floor import verify

HERE=Path(__file__).resolve().parent
path=HERE/'upper_central_floor_candidate.json'
raw=path.read_bytes();original=json.loads(raw)
cases={
    'missing_subtrees':original['nodes'][:2],
    'invalid_node_tag':[99],
    'false_whole_root_leaf':[11],
    'noninteger_tag':[0.5],
}
results={}
for label,nodes in cases.items():
    trial={**original,'nodes':nodes}
    try:verify(trial)
    except AssertionError:results[label]='REJECTED'
    else:raise AssertionError(('corruption was accepted',label))
report=dict(status='PASS',certificate_sha256=hashlib.sha256(raw).hexdigest(),
            controls=results,scope='Negative controls for exact table acceptance, not mathematical evidence beyond the independent replay')
(HERE/'upper_central_floor_negative_controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

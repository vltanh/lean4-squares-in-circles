"""Corruption controls for the independently reconstructed side envelope."""
import hashlib,json
from pathlib import Path
from verify_side_height_envelope import verify

HERE=Path(__file__).resolve().parent
path=HERE/'side_height_envelope_bump_plus_1_400_candidate.json'
raw=path.read_bytes();original=json.loads(raw)
cases={'missing_subtrees':original['nodes'][:2],
       'invalid_node_tag':[99],'false_whole_root_leaf':[3],
       'noninteger_tag':[0.5]}
results={}
for label,nodes in cases.items():
    try:verify({**original,'nodes':nodes})
    except AssertionError:results[label]='REJECTED'
    else:raise AssertionError(('corruption was accepted',label))
report=dict(status='PASS',certificate_sha256=hashlib.sha256(raw).hexdigest(),controls=results)
(HERE/'side_height_envelope_negative_controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

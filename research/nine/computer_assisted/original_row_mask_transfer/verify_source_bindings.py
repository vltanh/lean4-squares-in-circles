"""Verify immutable publication inputs; this is not a new polynomial replay."""
from pathlib import Path
import hashlib,json
here=Path(__file__).resolve().parent
repo=here.parents[3]
m=json.loads((here/'SOURCE_BINDINGS.json').read_text())
for row in m['sources']:
 p=(repo/row['repository_file']).resolve()
 assert p.is_relative_to(repo)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],row['repository_file']
assert m['new_original_cells']==m['new_masks']==m['new_positional_roots']==m['new_roadmap_gates']==0
print('PASS_PORTABLE_SOURCE_BINDINGS',len(m['sources']),'conditional cover only; no new closure credit')

#!/usr/bin/env python3
"""Restore the unchanged, hash-bound hand table from its ordered text parts."""
from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
EXPECTED = 'ffa48df0d02e18880314907a72a70fcc6aaceea4ee1060ea76b4fdb04c23a5fa'
manifest = json.loads((HERE/'CANDIDATE_COARSE_MISMATCH_INPUT_PARTS.json').read_text())
assert manifest['output'] == 'CANDIDATE_COARSE_MISMATCH_HAND_DATA.json'
assert manifest['sha256'] == EXPECTED
pieces = []
for i, part in enumerate(manifest['parts'], 1):
    assert part['name'] == 'CANDIDATE_COARSE_MISMATCH_HAND_DATA.part' + str(i).zfill(2)
    raw = (HERE/part['name']).read_bytes()
    assert len(raw) == part['bytes'] and sha256(raw).hexdigest() == part['sha256']
    pieces.append(raw)
raw = b''.join(pieces)
assert len(raw) == manifest['bytes'] and sha256(raw).hexdigest() == EXPECTED
output = HERE/manifest['output']
if output.exists():
    assert output.read_bytes() == raw, 'Existing hand input differs; no file was overwritten.'
else:
    output.write_bytes(raw)
print(json.dumps({'status': 'PASS', 'restored_input': output.name,
                  'bytes': len(raw), 'sha256': EXPECTED}))

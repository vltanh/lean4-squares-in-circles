#!/usr/bin/env python3
"""Restore the unchanged, hash-bound final hand inputs from raw text parts."""
from hashlib import sha256
from pathlib import Path
import json
import os

HERE=Path(__file__).resolve().parent
EXPECTED={
 'MISMATCH_015_TO_001_AFFINE_HAND_DATA.json':
 'da456f7eb49a2e0dc702054c684afc14da52a5e55c042add695ef862d7a6c1a2',
 'MISMATCH_015_TO_001_AFFINE_HAND_COMPACT_REPORT.json':
 '2818421ab2e711ae586fd88722676f0690cbc21c9f7ccc648de7f92f5fee9a45',
}
manifest=json.loads((HERE/'MISMATCH_015_TO_001_HAND_INPUT_PARTS.json').read_text())
assert manifest['format']=='ordered byte-exact UTF-8 parts'
assert len(manifest['outputs'])==len(EXPECTED)
assert {entry['output'] for entry in manifest['outputs']}==set(EXPECTED)
restored=[]
for entry in manifest['outputs']:
 name=entry['output'];assert entry['sha256']==EXPECTED[name]
 pieces=[]
 for i,part in enumerate(entry['parts'],1):
  assert part['name']==name[:-5]+'.part'+str(i).zfill(2)
  raw=(HERE/part['name']).read_bytes()
  assert len(raw)==part['bytes'] and sha256(raw).hexdigest()==part['sha256']
  pieces.append(raw)
 raw=b''.join(pieces)
 assert len(raw)==entry['bytes'] and sha256(raw).hexdigest()==EXPECTED[name]
 output=HERE/name
 if output.exists():
  assert output.read_bytes()==raw,'Existing hand input differs; no file was overwritten.'
 else:
  tmp=output.with_name(output.name+'.restore-tmp')
  with tmp.open('wb') as stream:
   stream.write(raw);stream.flush();os.fsync(stream.fileno())
  os.replace(tmp,output)
 restored.append({'name':name,'bytes':len(raw),'sha256':EXPECTED[name]})
print(json.dumps({'status':'PASS','restored_inputs':restored},indent=2))

#!/usr/bin/env python3
"""Restore the unchanged, hash-bound final hand inputs from raw text parts."""
from hashlib import sha256
from pathlib import Path
import json
import os

HERE=Path(__file__).resolve().parent
EXPECTED={
 'MISMATCH_026_TO_01_AFFINE_HAND_DATA.json':
 '3230d71cdb3f1aa513aa74de04dc49429bb6ff2759a115cd55d98b160e1fedf4',
 'MISMATCH_026_TO_01_AFFINE_HAND_COMPACT_REPORT.json':
 '9c0fcd59ed378dedf85e6134cc1bc5b7dee156ca781ef255b4564c9115a855ab',
}
manifest=json.loads((HERE/'MISMATCH_026_TO_01_HAND_INPUT_PARTS.json').read_text())
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

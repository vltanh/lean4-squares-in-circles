#!/usr/bin/env python3
"""Reassemble the exact C/D research archive from its two checked byte pieces."""
from pathlib import Path
import hashlib,json,tempfile,os
HERE=Path(__file__).resolve().parent

def digest(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()

def main():
 m=json.loads((HERE/'a2_00100_cd_open_archive_parts.json').read_text());assert m['schema']=='exact_archive_byte_pieces_v1'
 output=HERE/m['archive'];assert output.parent==HERE
 if output.exists():
  assert output.stat().st_size==m['archive_bytes']and digest(output)==m['archive_sha256'],'Existing output differs; refusing to overwrite it.'
  print(output.name+' already matches the complete archive hash.');return
 for p in m['parts']:
  source=HERE/p['file'];assert source.parent==HERE and source.stat().st_size==p['bytes']and digest(source)==p['sha256'],p['file']
 temporary=None
 try:
  with tempfile.NamedTemporaryFile(prefix='cd_open_reassembly_',dir=HERE,delete=False)as out:
   temporary=Path(out.name)
   for p in m['parts']:
    with(HERE/p['file']).open('rb')as source:
     for chunk in iter(lambda:source.read(1024*1024),b''):out.write(chunk)
  assert temporary.stat().st_size==m['archive_bytes']and digest(temporary)==m['archive_sha256']
  assert not output.exists(),'Output appeared during reassembly; refusing to overwrite it.'
  os.replace(temporary,output);temporary=None
 finally:
  if temporary is not None:temporary.unlink(missing_ok=True)
 print(output.name+' reassembled; every piece and the complete archive hash passed.')
 print('Extract it, then run: python -B -S cd_family_open_package_20261103/replay.py')
if __name__=='__main__':main()

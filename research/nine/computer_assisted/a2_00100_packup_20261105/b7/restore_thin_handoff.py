#!/usr/bin/env python3
"""Verify and restore a thin B7 delta against the two declared published inputs."""
from pathlib import Path
import argparse,hashlib,json,shutil,os,tarfile
O=Path(__file__).resolve().parent
cache={}
def sha(p):
 p=Path(p);s=p.stat();k=(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def read(p):return json.loads(Path(p).read_text())
def safe(base,name):
 p=(base/name).resolve();assert p.is_relative_to(base.resolve()),name;return p
ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--prior',type=Path,required=True);ap.add_argument('--destination',type=Path);ap.add_argument('--verify-only',action='store_true');a=ap.parse_args()
m=read(O/'MANIFEST.json');assert sha(O/'INPUTS.json')==m['inputs_sha256'];assert sha(O/'inputs.tar.xz')==m['archive_sha256'];index=read(O/'INPUTS.json')['files']
roots={'packet':a.packet.resolve(),'prior':a.prior.resolve()}
assert sha(roots['packet']/'INPUT_MANIFEST.json')==m['packet_manifest_sha256'];assert sha(roots['prior']/'SHA256_MANIFEST.json')==m['prior_manifest_sha256']
for kind,fn in [('packet','INPUT_MANIFEST.json'),('prior','SHA256_MANIFEST.json')]:
 for name,h in read(roots[kind]/fn)['files'].items():assert sha(safe(roots[kind],name))==h
blobs={}
with tarfile.open(O/'inputs.tar.xz','r:xz')as tar:
 for member in tar:
  assert member.isfile() and member.name.startswith('sources/');h=member.name.removeprefix('sources/');data=tar.extractfile(member).read();assert hashlib.sha256(data).hexdigest()==h;assert h not in blobs;blobs[h]=data
assert len(blobs)==m['new_input_blobs']
for e in index:
 s=e['storage']
 if s['root']=='delta':assert s['path']=='sources/'+e['sha256'] and e['sha256']in blobs
 else:assert sha(safe(roots[s['root']],s['path']))==e['sha256']
if a.verify_only:print('PASS_THIN_INPUT_RECONSTRUCTION',len(index),'paths',len(blobs),'new blobs');raise SystemExit
assert a.destination is not None;D=a.destination.resolve();assert not D.exists();D.mkdir(parents=True)
def linkcopy(src,dst):
 try:os.link(src,dst)
 except OSError:shutil.copy2(src,dst)
for kind,name in [('packet','b7_selected1011_open_packet_v1'),('prior','b16a_I32_complete_H_checkpoint')]:
 target=D/'restored'/name;shutil.copytree(roots[kind],target,copy_function=linkcopy);roots[kind]=target
aliases={}
for e in index:
 s=e['storage'];h=e['sha256'];target=safe(D,e['target'])if e['target']else safe(D,'retained_external/'+h)
 if not target.exists():
  target.parent.mkdir(parents=True,exist_ok=True)
  if s['root']=='delta':target.write_bytes(blobs[h])
  else:linkcopy(safe(roots[s['root']],s['path']),target)
 assert sha(target)==h;aliases[e['native_path']]={'path':str(target.relative_to(D)),'sha256':h}
(D/'RESTORED_NATIVE_ALIASES.json').write_text(json.dumps(aliases,indent=2)+'\n')
s=(D/'replay_continuation_v1.py').read_text();needle='    def audit(event,args):'
insert="    for native, item in json.loads((common/'RESTORED_NATIVE_ALIASES.json').read_text()).items():\n        p=(common/item['path']).resolve();assert p.is_relative_to(common) and sha(p)==item['sha256'];aliases[native]=p\n"
assert s.count(needle)==1;(D/'replay_handoff.py').write_text(s.replace(needle,insert+needle))
print('RESTORED',D)
print('Fresh exact replay (not performed by restoration):')
print('python -B -S',D/'replay_handoff.py','--prior',roots['prior'],'--tree',D/'restored/component156_one/manifest.json','--output',D/'fresh_replay')

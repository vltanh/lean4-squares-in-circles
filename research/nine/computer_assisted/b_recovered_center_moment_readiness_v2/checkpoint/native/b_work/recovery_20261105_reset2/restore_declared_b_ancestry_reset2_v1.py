#!/usr/bin/env python3
"""Recover pinned Git inputs, eight B archives and content-addressed sources.

Only missing files are installed. An existing path must already have the exact
expected bytes. Old receipts and proofs are never rewritten or promoted.
"""
from pathlib import Path, PurePosixPath
from io import BytesIO
import argparse
import hashlib
import json
import os
import subprocess
import tarfile
import tempfile

ROOT=Path('/workspace/scratch/f9f48fcfb253')
HERE=Path(__file__).resolve().parent
OLD=ROOT/'b_work/recovery_20261105'
REPO=ROOT/'repo'
GIT=OLD/'committed_b'
GIT_RECEIPT_SHA='b45bdd8d0dbd789504e44e3f31714b0b9caeac280a46965782f8b0b64918c9be'
RECIPES={
 'b340':'a2_00100_b340_complete_original/ARCHIVE_READY.json',
 'policy':'a2_00100_b_angle_policy_checkpoint_v1/ARCHIVE_READY.json',
 'i32':'a2_00100_b16a_I32_complete_H_manifest.json',
 'i10':'a2_00100_b16a_I10_complete_H_manifest.json',
 'i11':'a2_00100_b16a_I11_complete_H_manifest.json',
 'three_i':'a2_00100_b16a_three_I_complete_H_manifest.json',
 'complementary':'a2_00100_b16a_three_complementary_quarters_v1/ARCHIVE_PARTS.json',
 'availability':'a2_00100_b16a_replayable_cover_availability_v1/ARCHIVE_READY.json'}

def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb')as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()

def safe(name):
 p=PurePosixPath(name)
 assert not p.is_absolute()and p.parts and '..'not in p.parts and str(p)==name.rstrip('/')
 return p

def install(stream,target,size,digest,mode=0o644):
 target=Path(target);assert target.resolve().is_relative_to(ROOT)and not target.is_symlink()
 existing=target.exists()
 if existing:assert target.is_file()and target.stat().st_size==size and sha(target)==digest,str(target)
 target.parent.mkdir(parents=True,exist_ok=True)
 temp=None;out=None;h=hashlib.sha256();count=0
 if not existing:
  fd,temp=tempfile.mkstemp(prefix='exact-restore-',dir=target.parent);out=os.fdopen(fd,'wb')
 try:
  for b in iter(lambda:stream.read(1<<20),b''):
   h.update(b);count+=len(b)
   if out is not None:out.write(b)
  assert count==size and h.hexdigest()==digest,('input hash',target)
  if out is not None:
   out.flush();os.fsync(out.fileno());out.close();out=None;os.chmod(temp,mode&0o777)
   try:os.link(temp,target)
   except FileExistsError:assert not target.is_symlink()and sha(target)==digest
  assert sha(target)==digest
 finally:
  if out is not None:out.close()
  if temp is not None:os.unlink(temp)
 return not existing

def write_receipt(name,value):
 value=dict(value,restorer_sha256=sha(__file__),arithmetic_repeated=False,
            numerical_search_started=False,git_index_or_ref_mutated=False,
            existing_different_files_overwritten=False,new_original_cells=0,new_masks=0)
 path=HERE/name
 with path.open('x')as f:json.dump(value,f,indent=2);f.write('\n')
 print(json.dumps(dict(status=value['status'],receipt=str(path),sha256=sha(path))),flush=True)

def git_inputs():
 receipt=GIT/'GIT_RESTORATION_RECEIPT.json';assert sha(receipt)==GIT_RECEIPT_SHA
 d=json.loads(receipt.read_text());assert len(d['files'])==136
 installed=retained=0
 for i,(name,e)in enumerate(d['files'].items()):
  safe(name);assert e['mode']=='100644'
  target=GIT/name;source=REPO/name
  if source.is_file()and sha(source)==e['sha256']:
   raw=source.read_bytes()
  else:raw=subprocess.check_output(['git','-C',str(REPO),'cat-file','blob',e['git_blob']])
  assert len(raw)==e['bytes']and hashlib.sha256(raw).hexdigest()==e['sha256']
  assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['git_blob']
  added=install(BytesIO(raw),target,e['bytes'],e['sha256']);installed+=added;retained+=not added
  if i%20==19:print('GIT_INPUTS',i+1,'OF',len(d['files']),flush=True)
 for name,e in d['files'].items():assert sha(GIT/name)==e['sha256']
 write_receipt('FRESH_136_COMMITTED_ANCESTOR_INPUTS.json',dict(status='PASS_EXACT136_COMMITTED_B_ANCESTOR_FILES',
  source_commit=d['commit'],historical_git_receipt_sha256=GIT_RECEIPT_SHA,files=136,installed=installed,retained=retained,bytes=d['bytes']))

def source_archive():
 archive=REPO/'research/nine/recovered_source/2026_11_04_reset/sources.tar.xz'
 assert sha(archive)=='157bbd24c778cef8f44e0e357ac47322bbd527aac0dbc6c751b66d5b0eb7546d'
 dest=ROOT/'d_work/reset_sources_d989c83';seen={};installed=0
 with tarfile.open(archive,'r|xz')as t:
  for m in t:
   safe(m.name);assert m.isfile()and m.name not in seen
   if m.name=='PATHS.json':expected='87fa02855665f17f0375788b8d8a0f9372929fc34b695f01beb65d2d51045b05'
   elif m.name.startswith('sources/'):
    assert len(PurePosixPath(m.name).parts)==2 and len(PurePosixPath(m.name).name)==64
    expected=PurePosixPath(m.name).name
   else:assert m.name=='README.txt';expected=None
   stream=t.extractfile(m);assert stream is not None
   if expected is None:
    raw=stream.read();expected=hashlib.sha256(raw).hexdigest();stream=BytesIO(raw)
   installed+=install(stream,dest/m.name,m.size,expected,m.mode)
   seen[m.name]=dict(bytes=m.size,sha256=expected)
 assert len(seen)==3688
 mapping=json.loads((dest/'PATHS.json').read_text());assert len(mapping['files'])==22109
 for e in mapping['files']:
  p=dest/'sources'/e['sha256'];assert p.stat().st_size==e['bytes']and sha(p)==e['sha256']
 write_receipt('FRESH_RESET_SOURCE_ARCHIVE_RESTORATION.json',dict(status='PASS_EXACT_RESET_SOURCE_ARCHIVE_AND22109_MAPPINGS',
  archive_sha256=sha(archive),paths_sha256=sha(dest/'PATHS.json'),content_blobs=3686,members=3688,installed=installed,
  all_content_names_are_exact_sha256=True,destination=str(dest)))

def archive_one(which):
 historical=OLD/f'extracted_{which}/V2_READ_ONLY_ARCHIVE_MEMBER_VERIFICATION.json'
 manifest=json.loads((HERE/'published_35ac6d675d/transport/MEMBER_MANIFEST.json').read_text())
 expected=manifest['members']['native/'+str(historical.relative_to(ROOT))]
 assert sha(historical)==expected['sha256']
 old=json.loads(historical.read_text());assert old['status']=='PASS_ARCHIVE_AND_ALL_EXTRACTED_MEMBERS_MATCH'
 metadata=GIT/'research/nine/computer_assisted'/RECIPES[which]
 git=json.loads((GIT/'GIT_RESTORATION_RECEIPT.json').read_text())['files']
 def checked(path):
  e=git[str(path.relative_to(GIT))];assert path.stat().st_size==e['bytes']and sha(path)==e['sha256'];return e
 checked(metadata);spec=json.loads(metadata.read_text())
 assert spec['archive_sha256']==old['archive_sha256']
 compressed=HERE/f'{which}_restored_archive.tar.xz';assert not compressed.exists()
 h=hashlib.sha256();total=0
 with compressed.open('xb')as out:
  for item in spec['parts']:
   part=metadata.parent/item['file'];e=checked(part)
   assert(e['sha256'],e['bytes'])==(item['sha256'],item['bytes'])
   with part.open('rb')as f:
    for b in iter(lambda:f.read(1<<20),b''):out.write(b);h.update(b);total+=len(b)
 assert total==spec['archive_bytes']and h.hexdigest()==spec['archive_sha256']and sha(compressed)==h.hexdigest()
 unpacked=OLD/f'extracted_{which}/unpacked';expected_members=old['members'];seen=set();links=[];installed=0
 with tarfile.open(compressed,'r|xz')as t:
  for m in t:
   name=str(safe(m.name))
   if m.isdir():continue
   assert name in expected_members and name not in seen and(m.isfile()or m.islnk())
   e=expected_members[name]
   if m.islnk():
    safe(m.linkname);links.append((name,m.linkname,m.mode))
   else:
    assert m.size==e['bytes'];stream=t.extractfile(m);assert stream is not None
    installed+=install(stream,unpacked/name,e['bytes'],e['sha256'],m.mode)
   seen.add(name)
 assert seen==set(expected_members)
 while links:
  remaining=[];progress=False
  for name,link,mode in links:
   assert link in expected_members
   source=unpacked/link
   if not source.is_file():remaining.append((name,link,mode));continue
   e=expected_members[name]
   with source.open('rb')as f:installed+=install(f,unpacked/name,e['bytes'],e['sha256'],mode)
   progress=True
  assert progress;links=remaining
 for name,e in expected_members.items():assert sha(unpacked/name)==e['sha256']
 assert len(expected_members)==old['member_count']
 write_receipt(f'FRESH_{which.upper()}_ARCHIVE_RESTORATION.json',dict(status='PASS_EXACT_PUBLISHED_ARCHIVE_AND_ALL_MEMBER_BYTES_RESTORED',
  package=which,archive_sha256=sha(compressed),member_count=len(expected_members),member_bytes=old['member_bytes'],
  installed=installed,historical_member_audit_sha256=sha(historical),metadata_sha256=sha(metadata),packet=old['packet']))

if __name__=='__main__':
 if not __debug__:raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['git','source','archives']);ap.add_argument('packages',nargs='*')
 a=ap.parse_args()
 if a.mode=='git':git_inputs()
 elif a.mode=='source':source_archive()
 else:
  assert a.packages and all(p in RECIPES for p in a.packages)
  for p in a.packages:archive_one(p)

from pathlib import Path
import json,hashlib,shutil,tarfile
R=Path(__file__).resolve().parent;O=R/'publication';O.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
provenance={}
def copy(source,name):
 p=O/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,p);assert sha(p)==sha(source);provenance[str(source.resolve())]=dict(member=name,sha256=sha(source),bytes=source.stat().st_size)
base=json.loads((R/'retained165/manifest.json').read_text());new=json.loads((R/'checkpoint167/manifest.json').read_text());assembly=[]
for n in new['nodes']:
 i=n['index'];included=i>=165 or n['sha256']!=base['nodes'][i]['sha256']
 if included:copy(R/'checkpoint167'/n['file'],'tree/'+n['file'])
 assembly.append(dict(index=i,file=n['file'],sha256=n['sha256'],source='INCLUDED'if included else'PREVIOUS_ACCEPTED_A165_TREE'))
copy(R/'checkpoint167/manifest.json','tree/manifest.json')
for name in ('CHECKPOINT167_FULL_REPLAY.json','SCREEN_EXACT_SUFFIX_REPLAY.json','CHECKPOINT167_SOURCE_BINDINGS.json'):
 copy(R/name,'reports/'+name)
for name in ('build_checkpoint.py','replay_full.py','bound_screen.py','replay_screen.py','replay_bound.py'):
 copy(R/name,'sources/'+name)
for name in new['physical_continuation']['source_suffix_proofs']:
 p=Path(name);copy(p,'discovery_suffixes/'+p.parent.name+'/'+p.name)
write(O/'TREE_ASSEMBLY.json',dict(schema='A167_physical_continuation_thin_delta_v1',base_manifest_sha256=sha(R/'retained165/manifest.json'),base_publication='research/nine/computer_assisted/a_c744_finite_existing_correlations_v2',new_manifest_sha256=sha(R/'checkpoint167/manifest.json'),nodes=assembly))
write(O/'COPY_PROVENANCE.json',provenance)
write(O/'INPUT_MANIFEST.json',{str(p.relative_to(O)):sha(p)for p in sorted(O.rglob('*'))if p.is_file()})
archive=R/'a167_physical_continuation_v1.tar.xz'
with tarfile.open(archive,'w:xz',preset=1)as t:
 for p in sorted(O.rglob('*')):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)),recursive=False)
write(R/'A167_ARCHIVE_MANIFEST.json',dict(archive=archive.name,sha256=sha(archive),bytes=archive.stat().st_size,members=len([p for p in O.rglob('*')if p.is_file()]),changed_or_new_payloads=sum(e['source']=='INCLUDED'for e in assembly),all167_prefixes_and_records_replayed=True,nodes=167,excluded_leaves=124,open_leaves=9,new_originals=0,new_masks=0))
print('PACKET',archive,archive.stat().st_size,flush=True)

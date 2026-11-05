from pathlib import Path
from io import BytesIO
import hashlib,json,lzma,tarfile
R=Path(__file__).resolve().parent;TREE=R/'node192_from188_template';REPORT=R/'node192_stopped_replay.json';OUT=R/'node192_stopped_native_package'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 assert not OUT.exists();OUT.mkdir();r=json.loads(REPORT.read_text());m=json.loads((TREE/'manifest.json').read_text());assert r['status']=='PASS_PARTIAL_PHYSICAL_TREE' and (r['nodes'],r['excluded_leaves'],r['open_leaves'])==(281,133,77)
 checked=set(m['template_discovery']['checked_leaves']);nodes=[json.loads((TREE/e['file']).read_text())for e in m['nodes']];leaves=[n for n in nodes if not n['children']]
 stopped=dict(reason='Stopped at user request: pack up and hand off',saved_native_calls=m['template_discovery']['native_run_calls'],started_native_calls=json.loads((TREE/'NATIVE_RUN_COUNT.json').read_text())['native_run_calls'],tested_leaf_count=len(checked),tested_open_leaves=[n['index']for n in leaves if n['index']in checked and n['status']=='OPEN'],untested_open_leaves=[n['index']for n in leaves if n['index']not in checked],all_complete_closed_faces_retained=True,original_cells_closed=0,masks_closed=0)
 assert stopped['saved_native_calls']==909 and stopped['started_native_calls']==910 and stopped['tested_leaf_count']==134 and stopped['tested_open_leaves']==[49] and len(stopped['untested_open_leaves'])==76
 paths=dict(r['source_sha256']);paths[str(Path(__file__).resolve())]=sha(__file__);entries=[];blobs={}
 for name,h in sorted(paths.items()):
  p=Path(name);assert sha(p)==h,name;entries.append(dict(path=name,sha256=h,bytes=p.stat().st_size));blobs.setdefault(h,p)
 (OUT/'INPUTS.json').write_text(json.dumps(dict(schema='B16_NODE192_STOPPED_NATIVE_INPUT_MAP_V1',files=entries,complete_cold_portable_replay_claimed=False),indent=2)+'\n');archive=OUT/'inputs.tar.xz'
 with lzma.open(archive,'wb',preset=1) as z,tarfile.open(fileobj=z,mode='w|') as t:
  for h,p in sorted(blobs.items()):
   raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h;info=tarfile.TarInfo('sources/'+h);info.size=len(raw);info.mode=0o644;t.addfile(info,BytesIO(raw))
 seen=set()
 with tarfile.open(archive,'r|xz') as t:
  for info in t:
   assert info.isfile() and info.name.startswith('sources/');h=info.name.split('/')[1];assert h in blobs and h not in seen;assert hashlib.sha256(t.extractfile(info).read()).hexdigest()==h;seen.add(h)
 assert seen==set(blobs)
 for e in entries:assert sha(e['path'])==e['sha256']
 for p,name in ((REPORT,'EXACT_PARTIAL_REPLAY.json'),(TREE/'manifest.json','TREE_MANIFEST.json'),(Path(m['parent']['path']),'ANCESTRY_PREFIX.json'),(TREE/'NATIVE_RUN_COUNT.json','NATIVE_RUN_COUNT.json'),(Path(__file__),'package_stopped192.py')):(OUT/name).write_bytes(p.read_bytes())
 (OUT/'STOP_STATE.json').write_text(json.dumps(stopped,indent=2)+'\n')
 (OUT/'README.md').write_text('''# B16 node192 stopped complete physical cover\n\nNumerical search stopped at the user's request. Fresh exact replay returned `PASS_PARTIAL_PHYSICAL_TREE`: all281 nodes and all210 terminal domains are retained, with23 complete SAT unions and48 complete closed angle unions.133 terminal domains are excluded and77 remain OPEN. This is a complete cover, not a complete exclusion.\n\nThe sole tested OPEN leaf is49. The76 untested OPEN leaves are listed in STOP_STATE.json. The manifest contains909 completed-checkpoint native calls; the per-call file records910 started calls, including the interrupted attempt. Every saved node hash matches; no orphan or discarded complementary face was introduced. Exact replay checked3044 local printed rows,43 relative-support chord occurrences and0 central-nine occurrences, with no new bound rounds.\n\nAll states and terminal certificates were regenerated from original node192's own certified bounds and H/I owner alternative. Only the previously proved188 split template was reused; no188 terminal certificate or owner-specific literal was transported. Original188 is separately proved, but192 and its entire parent73 remain OPEN. The original-cell and mask ledgers are unchanged.\n\nINPUTS.json maps every retained native absolute input to content-addressed members of inputs.tar.xz. All members and native inputs were rehashed. This is a native input bundle; standalone cold-portable replay is not claimed.\n\nResume from this saved manifest rather than restarting the template generation. First process the76 untested leaves under a bounded leaf-only continuation, preserving the133 exact exclusions. Then refine tested survivor49 using complete physical-pair or closed angle covers with its own current bounds. The existing590-call remainder of the original1500-call allowance is explicit; never silently reset that allowance or claim completed calls from an interrupted solve.\n''')
 manifest=dict(schema='B16_NODE192_STOPPED_COMPLETE_COVER_V1',status=r['status'],scope='conditional original node192 only; region192 remains OPEN',complete_physical_cover_retained=True,whole_conditional_region_closed=False,nodes=281,excluded_terminal_domains=133,open_terminal_domains=77,complete_unions=r['complete_unions'],source_input_paths=len(entries),unique_input_blobs=len(blobs),input_archive_sha256=sha(archive),input_archive_bytes=archive.stat().st_size,files={p.name:sha(p)for p in sorted(OUT.iterdir())if p.is_file()},independent_arithmetic_replay_passed=True,independent_manuscript_review_performed=False,standalone_cold_replay_claimed=False,original_cells_closed=0,masks_closed=0)
 (OUT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k]for k in ('source_input_paths','unique_input_blobs','input_archive_bytes','input_archive_sha256')}))
if __name__=='__main__':main()

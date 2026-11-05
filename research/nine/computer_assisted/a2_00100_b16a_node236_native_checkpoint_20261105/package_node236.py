from pathlib import Path
from io import BytesIO
import hashlib,json,lzma,tarfile
ROOT=Path('/workspace/lean4-squares-in-circles/research/nine/.runs')
SRC=ROOT/'b16_geometry';OUT=ROOT/'b16_continue/node236_native_package'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 assert not OUT.exists();OUT.mkdir()
 report=SRC/'complete_node236_replay.json';r=json.loads(report.read_text())
 assert r['status']=='PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE' and r['complete'] and not r['whole_original_proved']
 assert (r['nodes'],r['excluded_leaves'],r['open_leaves'])==(11,6,0)
 paths=dict(r['source_sha256']);paths[str(Path(__file__).resolve())]=sha(__file__)
 entries=[];blobs={}
 for name,digest in sorted(paths.items()):
  p=Path(name);assert sha(p)==digest,name
  entries.append(dict(path=name,sha256=digest,bytes=p.stat().st_size));blobs.setdefault(digest,p)
 index=dict(schema='B16_NODE236_NATIVE_INPUT_MAP_V1',files=entries,complete_cold_portable_replay_claimed=False)
 (OUT/'INPUTS.json').write_text(json.dumps(index,indent=2)+'\n')
 archive=OUT/'inputs.tar.xz'
 with lzma.open(archive,'wb',preset=1) as z,tarfile.open(fileobj=z,mode='w|') as t:
  for digest,p in sorted(blobs.items()):
   raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==digest
   m=tarfile.TarInfo('sources/'+digest);m.size=len(raw);m.mode=0o644;t.addfile(m,BytesIO(raw))
 seen=set()
 with tarfile.open(archive,'r|xz') as t:
  for m in t:
   assert m.isfile() and m.name.startswith('sources/');digest=m.name.split('/')[1]
   assert digest in blobs and digest not in seen
   assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==digest;seen.add(digest)
 assert seen==set(blobs)
 for e in entries:assert sha(e['path'])==e['sha256']
 for src,name in ((report,'EXACT_REPLAY.json'),(SRC/'node236_ancestry_prefix.json','ANCESTRY_PREFIX.json'),(SRC/'source_0236.json','SOURCE_NODE236.json'),(SRC/'complete_node236_tree/manifest.json','TREE_MANIFEST.json'),(Path(__file__),'package_node236.py')):
  (OUT/name).write_bytes(src.read_bytes())
 readme='''# B16 node236 complete conditional exclusion\n\nThe whole physical region identified by native adaptive SAT node236 is excluded. The unchanged independent rational tree checker returned `PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE`: 11 nodes, five complete angle unions, six excluded terminal regions, zero OPEN regions, no new bound rounds, and 335 local printed rows. Its full initial path is retained in `EXACT_REPLAY.json`, with all 21 path entries and the 18-step exact ancestry certificate.\n\nThis is a conditional subregion of original `negative-16a2fc93c8d133f0`, inside the merged closed I21/I22 rectangle. It additionally fixes inherited proxy/angle branches and the physical H/I, B/I, and A/H SAT alternatives printed in `SOURCE_NODE236.json`. This packet does not close node206, the entire merged I21/I22 region, original B16, or any mask. The other fourteen original I rectangles retain their existing proofs; this packet does not re-partition them. Original-cell and mask credit are both zero.\n\nThe complete refinement uses exact slope cuts: G at −1/2; on its lower half I at −1/2; on I lower, H at −9/16; on I upper, C at −5/16; on the surviving C upper half, H at −9/16. Both closed halves are retained at every split. The six terminal contradictions have positive exact rational reserves reconstructed from accepted physical rows. Numerical points only chose cut locations. No stronger terminal premise or chosen central-pair assumption is used.\n\n`INPUTS.json` maps every retained absolute native input path to a content-addressed blob in `inputs.tar.xz`. The archive is read back and every member digest checked when packaged. It includes all checker-retained source, certificate, geometric-premise and ancestry bytes, plus the packaging script. This is a native input bundle, not a standalone cold-portable replay claim. Restore it only through a separately reviewed native restoration process.\n\nNative replay command after the listed paths exist:\n\n```sh\npython -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py /workspace/lean4-squares-in-circles/research/nine/.runs/b16_geometry/complete_node236_tree/manifest.json /tmp/b16_node236_replay.json --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1\n```\n\nDiscovery used 189 counted native LP calls after the first two uninstrumented phase searches. No bound rounds were run; these numerical counts are not proof premises. Fresh independent manuscript/attachment review is pending when this bundle is produced.\n'''
 (OUT/'README.md').write_text(readme)
 manifest=dict(schema='B16_NODE236_NATIVE_COMPLETE_COMPONENT_V1',status=r['status'],original_id=r['initial_original_id'],scope='exact native node236 conditional region only',initial_path=r['initial_path'],nodes=11,complete_angle_unions=5,excluded_terminal_domains=6,open_terminal_domains=0,local_rounds=0,local_printed_rows=335,source_input_paths=len(entries),unique_input_blobs=len(blobs),input_archive_sha256=sha(archive),input_archive_bytes=archive.stat().st_size,files={p.name:sha(p)for p in sorted(OUT.iterdir())if p.is_file()},independent_arithmetic_replay_passed=True,independent_manuscript_review_performed=False,standalone_cold_replay_claimed=False,whole_node206_closed=False,whole_original_closed=False,original_cells_closed=0,masks_closed=0)
 (OUT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({k:manifest[k]for k in ('source_input_paths','unique_input_blobs','input_archive_bytes','input_archive_sha256')}))
if __name__=='__main__':main()

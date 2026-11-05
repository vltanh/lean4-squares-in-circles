from pathlib import Path
from io import BytesIO
import argparse,hashlib,json,lzma,tarfile
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('index',type=int);a=ap.parse_args();label=f'node{a.index}'
 tree=R/f'complete_{label}_tree';report=R/f'complete_{label}_replay.json';out=R/f'{label}_native_package';assert not out.exists();out.mkdir()
 r=json.loads(report.read_text());m=json.loads((tree/'manifest.json').read_text())
 assert r['status']=='PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE' and r['complete'] and not r['whole_original_proved'] and r['open_leaves']==0
 paths=dict(r['source_sha256']);paths[str(Path(__file__).resolve())]=sha(__file__);entries=[];blobs={}
 for name,h in sorted(paths.items()):
  p=Path(name);assert sha(p)==h,name;entries.append(dict(path=name,sha256=h,bytes=p.stat().st_size));blobs.setdefault(h,p)
 (out/'INPUTS.json').write_text(json.dumps(dict(schema='B16_COMPLETE_COMPONENT_NATIVE_INPUT_MAP_V1',files=entries,complete_cold_portable_replay_claimed=False),indent=2)+'\n')
 archive=out/'inputs.tar.xz'
 with lzma.open(archive,'wb',preset=1) as z,tarfile.open(fileobj=z,mode='w|') as t:
  for h,p in sorted(blobs.items()):
   raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h;info=tarfile.TarInfo('sources/'+h);info.size=len(raw);info.mode=0o644;t.addfile(info,BytesIO(raw))
 seen=set()
 with tarfile.open(archive,'r|xz') as t:
  for info in t:
   assert info.isfile() and info.name.startswith('sources/');h=info.name.split('/')[1];assert h in blobs and h not in seen
   assert hashlib.sha256(t.extractfile(info).read()).hexdigest()==h;seen.add(h)
 assert seen==set(blobs)
 for e in entries:assert sha(e['path'])==e['sha256']
 for p,name in ((report,'EXACT_REPLAY.json'),(Path(m['parent']['path']),'ANCESTRY_PREFIX.json'),(tree/'manifest.json','TREE_MANIFEST.json'),(Path(__file__),'package_component_v1.py')):(out/name).write_bytes(p.read_bytes())
 explanation=f'''# B16 complete conditional region {a.index}\n\nThe entire inherited physical region identified by node{a.index} is excluded. Fresh unchanged independent rational replay returned `{r['status']}`: {r['nodes']} nodes, {r['excluded_leaves']} excluded terminal domains, zero OPEN, {r['local_printed_rows']} local printed rows, and {r['local_rounds']} new bound rounds. Complete union counts are `{r['complete_unions']}`.\n\nThe precise conditional domain is the full {len(r['initial_path'])}-entry original path in `EXACT_REPLAY.json`, with the independently replayed ancestry prefix. It remains inside B16 original `negative-16a2fc93c8d133f0` and the merged closed I21/I22 rectangle. All nine original squares, inherited original constraints, and closed equality faces remain present. The other fourteen original I rectangles retain their published proofs. This does not close region188, all merged I21/I22, the entire original B16, or a mask. Both original-cell and mask ledger credits are zero.\n\nThe proof covers all physical A/H separating alternatives, including both owners, axes and signs. Six alternatives close immediately; the other two are completed by closed G/I/H/C slope refinements. It joins the independently reviewed complete236 component with the complete242 angle component and six exact terminal siblings. Every new terminal has a positive rational reserve using the accepted original physical row families; no additional universal-row adapter is needed.\n\n`INPUTS.json` maps all retained native absolute paths to content-addressed `sources/<sha256>` members in `inputs.tar.xz`. Every archive member was read back and hashed, and every current native input was rehashed. Checker-retained proof sources, complete ancestry, all component records and discovery/packaging scripts are included. This is a native input bundle; standalone cold-portable replay is not claimed.\n\nNative replay after all listed paths exist:\n\n```sh\npython -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py {tree/'manifest.json'} /tmp/b16_{label}_replay.json --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1\n```\n\nIndependent manuscript, attachment and transport review of this combined component is pending at packaging time. No discovery solver status is a proof premise.\n'''
 (out/'README.md').write_text(explanation)
 manifest=dict(schema='B16_NATIVE_COMPLETE_CONDITIONAL_COMPONENT_V1',status=r['status'],original_id=r['initial_original_id'],scope=f'exact conditional original region {a.index} only',initial_path=r['initial_path'],nodes=r['nodes'],complete_unions=r['complete_unions'],excluded_terminal_domains=r['excluded_leaves'],open_terminal_domains=0,local_rounds=r['local_rounds'],local_printed_rows=r['local_printed_rows'],source_input_paths=len(entries),unique_input_blobs=len(blobs),input_archive_sha256=sha(archive),input_archive_bytes=archive.stat().st_size,files={p.name:sha(p)for p in sorted(out.iterdir())if p.is_file()},independent_arithmetic_replay_passed=True,independent_manuscript_review_performed=False,standalone_cold_replay_claimed=False,whole_original_closed=False,original_cells_closed=0,masks_closed=0)
 (out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k]for k in ('nodes','source_input_paths','unique_input_blobs','input_archive_bytes','input_archive_sha256')}))
if __name__=='__main__':main()

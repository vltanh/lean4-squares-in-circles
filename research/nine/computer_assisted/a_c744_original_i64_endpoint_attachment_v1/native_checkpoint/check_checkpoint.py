#!/usr/bin/env python3
"""File/header checks only; no weighted proof is replayed by this tool."""
if not __debug__:raise RuntimeError('Checkpoint checks require assertions.')
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 assert not a.output.exists()and not a.output.resolve().is_relative_to(HERE)
 m=read(HERE/'INPUT_MANIFEST.json');actual={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()}
 assert not any(p.is_symlink()for p in HERE.rglob('*'))
 assert actual==set(m['files'])|{'INPUT_MANIFEST.json'}
 for rel,item in m['files'].items():
  q=HERE/rel;assert q.resolve().is_relative_to(HERE)and q.stat().st_size==item['bytes']and sha(q)==item['sha256']
 f=read(HERE/'family/SOURCE_BINDINGS.json')
 assert sha(HERE/'family/SOURCE_BINDINGS.json')=='93d79d81b6f9f4b2499220b75aca0e6c2c400829261ff783a6ff068fa4301e78'
 for rel,h in f['files'].items():assert sha(HERE/'family'/rel)==h
 b=read(HERE/'family/PREMISE_BINDING.json');assert b['endpoint_rows']==414 and b['whole_original_height_rows']==1 and b['valid_on_whole_original']is True
 r=read(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json')
 assert sha(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json')=='3fc7996b0a2571cfd2d232d5b3811f4d27b39ced63c1b4c9330d551c1ad5f481'
 assert r['status']=='PASS_FIRST_EXACT_ORIGINAL_WIDE_I64_DIRECT_BOUND_USE'and r['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
 assert r['ordinary_exact_audit']['deductions']==r['ordinary_exact_audit']['printed_rows_checked']==r['weighted_endpoint_occurrences']==268
 assert sha(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3_RECORD.json')==r['record']['sha256']
 root=read(HERE/'reviews/A_ORIGINAL_I64_FIRST_DIRECT_ROOT_FRESH_REPLAY.json')
 assert root['exact_audit']==r['ordinary_exact_audit']and root['record_sha256']==r['record']['sha256']and root['final_state_matches']is True
 controls=read(HERE/'evidence/A_C744_ORIGINAL_I64_BOUND_CONTROLS_V2.json');assert controls['damaged_literals_or_callers_rejected']==432 and controls['endpoint_rows']==414
 for x in(r,root,controls):assert x['new_original_cells']==x['new_masks']==0
 deps=read(HERE/'DEPENDENCIES.json');assert deps['missing_unpreserved_dependencies']==[]and deps['full_cold_replay_claimed']is False
 for path,item in deps['paths'].items():
  if item['kind']=='INCLUDED_EXACT_ALIAS':assert sha(HERE/item['member'])==item['sha256']
 result=dict(status='PASS_ORIGINAL_I64_ENDPOINT_PACKET_BYTES_AND_HEADERS',files=len(actual),
   input_manifest_sha256=sha(HERE/'INPUT_MANIFEST.json'),endpoint_rows=414,separate_height_rows=1,
   saved_direct_deductions=268,weighted_arithmetic_replayed=False,historical_source_arithmetic_repeated=False,
   cold_proof_claimed=False,new_original_cells=0,new_masks=0)
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()

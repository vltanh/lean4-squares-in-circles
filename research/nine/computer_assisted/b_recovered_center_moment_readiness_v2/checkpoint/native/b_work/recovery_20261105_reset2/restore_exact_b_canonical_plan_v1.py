#!/usr/bin/env python3
"""Reapply the published exact2,215-path B restoration plan without overwrites."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

ROOT=Path('/workspace/scratch/f9f48fcfb253')
HERE=Path(__file__).resolve().parent
PLAN=ROOT/'b_work/recovery_20261105/B_CANONICAL_RESTORATION_PLAN.json'
PLAN_SHA='7e070a4aa2902fefff7ccac54c02a6f5fa402fe83e9669b80b243cef1839c028'

def main():
 if not __debug__:raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['sources','all']);a=ap.parse_args()
 helper=HERE/'restore_declared_b_ancestry_reset2_v1.py';before=hashlib.sha256(helper.read_bytes()).hexdigest()
 spec=importlib.util.spec_from_file_location('exact_B_restore_IO',helper);M=importlib.util.module_from_spec(spec);spec.loader.exec_module(M)
 assert M.sha(PLAN)==PLAN_SHA
 doc=json.loads(PLAN.read_text());assert len(doc['files'])==2215
 assert doc['source_map_sha256']=='87fa02855665f17f0375788b8d8a0f9372929fc34b695f01beb65d2d51045b05'
 plan={p:e for p,e in doc['files'].items()if a.mode=='all'or'/d_work/reset_sources_d989c83/'in e['source']}
 assert len(plan) == (2215 if a.mode == 'all' else 1744)
 checked=set()
 for name,e in plan.items():
  target=Path(name);source=Path(e['source'])
  assert target.is_absolute()and target.is_relative_to(ROOT/'b_work')and not target.is_symlink()
  assert source.is_file()and source.stat().st_size==e['bytes']
  if str(source)not in checked:assert M.sha(source)==e['sha256'];checked.add(str(source))
  if target.exists():assert target.is_file()and M.sha(target)==e['sha256'],name
 installed=0
 for name,e in plan.items():
  with Path(e['source']).open('rb')as f:installed+=M.install(f,Path(name),e['bytes'],e['sha256'])
 for name,e in plan.items():assert M.sha(name)==e['sha256']and M.sha(e['source'])==e['sha256']
 assert M.sha(PLAN)==PLAN_SHA and M.sha(helper)==before
 receipt=dict(status='PASS_EXACT_PUBLISHED_B_CANONICAL_PLAN_RESTORED',mode=a.mode,plan_sha256=PLAN_SHA,
  files=len(plan),installed=installed,existing_identical_retained=len(plan)-installed,
  source_and_destination_hashes_rechecked=True,helper_sha256=before,restorer_sha256=M.sha(__file__),
  historical_plan_or_receipt_rewritten=False,existing_drift_overwritten=False,
  mathematical_replay_performed=False,numerical_search_started=False,new_original_cells=0,new_masks=0)
 out=HERE/f'FRESH_B_CANONICAL_{a.mode.upper()}_RESTORATION.json'
 with out.open('x')as f:json.dump(receipt,f,indent=2);f.write('\n')
 print(json.dumps(dict(status=receipt['status'],mode=a.mode,files=len(plan),installed=installed,
  receipt_sha256=M.sha(out))),flush=True)

if __name__=='__main__':main()

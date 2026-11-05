#!/usr/bin/env python3
"""Assemble the exact complete A167 tree from its thin delta and accepted A165 base."""
from pathlib import Path
import argparse,json,hashlib,shutil

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--delta',type=Path,required=True);p.add_argument('--base',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 delta,base,out=a.delta.resolve(),a.base.resolve(),a.output.resolve();assert not out.exists()
 inputs=json.loads((delta/'INPUT_MANIFEST.json').read_text())
 for name,h in inputs.items():
  relative=Path(name);assert not relative.is_absolute() and '..'not in relative.parts
  assert sha(delta/relative)==h
 plan=json.loads((delta/'TREE_ASSEMBLY.json').read_text());assert sha(base/'manifest.json')==plan['base_manifest_sha256']
 assert sha(delta/'tree/manifest.json')==plan['new_manifest_sha256']
 out.mkdir(parents=True)
 for e in plan['nodes']:
  assert e['file']==f"node_{e['index']:05}.json"
  source=(delta/'tree'if e['source']=='INCLUDED'else base)/e['file'];assert sha(source)==e['sha256']
  shutil.copyfile(source,out/e['file']);assert sha(out/e['file'])==e['sha256']
 shutil.copyfile(delta/'tree/manifest.json',out/'manifest.json')
 print('PASS_EXACT_A167_MATERIALIZATION',len(plan['nodes']))
if __name__=='__main__':main()

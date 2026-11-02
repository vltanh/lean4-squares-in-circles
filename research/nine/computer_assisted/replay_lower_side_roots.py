#!/usr/bin/env python3
"""Independent fixed-root byte binding and exact replay. No producer imports."""
from pathlib import Path
import gzip,json,hashlib,array,subprocess,sys,time,argparse
BASE=Path(__file__).resolve().parent;ROOTS=BASE/'lower_side_roots';EXE=BASE/'verify_lower_side_exact';SOURCE=BASE/'verify_lower_side_exact.cpp'
def run(rid):
 assert type(rid)is int and 0<=rid<128
 record=ROOTS/f'root_{rid:03d}.record.json';gz=ROOTS/f'root_{rid:03d}.json.gz';report=ROOTS/f'root_{rid:03d}.exact.json'
 comp=gz.read_bytes();raw=gzip.decompress(comp);d=json.loads(raw)
 if d.get('schema')!='weak_middle_lower_side_coupled_cover_v1' or d.get('proof_status')!='discovery_complete_pending_independent_replay' or d.get('frontier_count')!=0:raise ValueError('wrong or incomplete certificate')
 n=d.get('nodes');l=d.get('leaves');ev=d.get('events');pr=d.get('leaves_per_root')
 if type(n)is not int or type(l)is not int or n!=2*l-1 or len(ev)!=n or d.get('root_count')!=128:raise ValueError('wrong counts')
 if pr!=[l if j==rid else 0 for j in range(128)]:raise ValueError('wrong fixed root record')
 if any(type(x)is not int or not -23<=x<=6 for x in ev):raise ValueError('unknown event')
 data=(f'{rid} {n} {l}\n').encode()+array.array('b',ev).tobytes()
 with (ROOTS/f'root_{rid:03d}.exact.log').open('wb')as log:
  p=subprocess.run([str(EXE)],input=data,stdout=subprocess.PIPE,stderr=log)
 if p.returncode:raise RuntimeError(f'exact root {rid} rejected; see log')
 r=json.loads(p.stdout)
 if r.get('result')!='PASS' or r.get('complete')is not True or r.get('root')!=rid or r.get('leaves')!=l or r.get('nodes')!=n or r.get('minimum_reserve_numerator',0)<=0:raise ValueError('unexpected exact report')
 r.update(certificate=gz.name,sha256=hashlib.sha256(comp).hexdigest(),payload_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic='independent exact directed 48-bit integer intervals, integer radicals, rational root bisections; no producer imports')
 report.write_text(json.dumps(r,indent=2)+'\n');return r
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=int);ap.add_argument('--all',action='store_true');args=ap.parse_args()
 if args.root is not None:print(json.dumps(run(args.root)),flush=True)
 else:
  for rid in range(128):
   while not (ROOTS/f'root_{rid:03d}.record.json').exists():time.sleep(2)
   report=ROOTS/f'root_{rid:03d}.exact.json'
   if report.exists():r=json.loads(report.read_text())
   else:r=run(rid)
   print(json.dumps(r),flush=True)

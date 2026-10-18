"""Run all closed pair branches. Accept only complete successful exit logs."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import subprocess, sys, time, hashlib, json, re

ROOT=Path(__file__).resolve().parent
EXE=Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/verify_fourtype_pairs_relaxed')
WORKERS=int(sys.argv[2]) if len(sys.argv)>2 else 3
OUT=Path(sys.argv[3]) if len(sys.argv)>3 else ROOT/'fourtype_pair_logs'
OUT.mkdir(exist_ok=True)
jobs=[(a,b,s,t) for a in range(4) for b in range(a,4) for s in [-1,1] for t in [-1,1]]
bound_hashes={'executable_sha256':hashlib.sha256(EXE.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((ROOT/'verify_fourtype_pairs.cpp').read_bytes()).hexdigest(),'arithmetic_source_sha256':hashlib.sha256((ROOT/'exact_dyadic_base.cpp').read_bytes()).hexdigest()}

def run(job):
    name='_'.join(map(str,job))
    logfile=OUT/(name+'.log')
    start=time.monotonic()
    p=subprocess.run([str(EXE),*map(str,job)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    txt=p.stdout
    logfile.write_text(txt)
    lines=txt.strip().splitlines();tail=lines[-1] if lines else ''
    expected_prefix='PIECE '+' '.join(map(str,job))+' '
    pieces=[line[len(expected_prefix):].split()[:2] for line in lines if line.startswith(expected_prefix)]
    complete=len(pieces)==64 and set(map(tuple,pieces))=={(str(i),str(j)) for i in range(8) for j in range(8)}
    complete=complete and tail.startswith('VERIFIED '+' '.join(map(str,job))+' ')
    result={'branch':job,'returncode':p.returncode,'complete':complete,'seconds':time.monotonic()-start,'summary':tail,'sha256':hashlib.sha256(txt.encode()).hexdigest()}
    if p.returncode or not complete:
        print('FAILED',result,flush=True)
    else: print(tail,flush=True)
    return result

with ThreadPoolExecutor(max_workers=WORKERS) as pool:
    results=[f.result() for f in as_completed([pool.submit(run,j) for j in jobs])]
ok=len(results)==40 and all(r['returncode']==0 and r['complete'] for r in results)
payload={'status':'ALL BRANCHES PASSED' if ok else 'INCOMPLETE/FAILED',**bound_hashes,'results':sorted(results,key=lambda r:r['branch'])}
(OUT/'manifest.json').write_text(json.dumps(payload,indent=2)+'\n')
print(payload['status'],flush=True)
sys.exit(0 if ok else 1)

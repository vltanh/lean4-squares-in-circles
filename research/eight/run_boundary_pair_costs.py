"""Run exactly the declared pair cover of a rational boundary-cost certificate.

Usage: python run_boundary_pair_costs.py EXE DATA_JSON DATA_HEADER OUT_DIR [WORKERS]
"""
from concurrent.futures import ThreadPoolExecutor,as_completed
from pathlib import Path
import subprocess,sys,time,hashlib,json,re

ROOT=Path(__file__).resolve().parent
EXE=Path(sys.argv[1]);DATA=Path(sys.argv[2]);HEADER=Path(sys.argv[3]);OUT=Path(sys.argv[4]);WORKERS=int(sys.argv[5]) if len(sys.argv)>5 else 3
j=json.loads(DATA.read_text());N=len(j['types']);K=j['K'];OUT.mkdir(parents=True,exist_ok=True)
pairs=j.get('required_pairs',[[a,b] for a in range(N) for b in range(a,N)])
assert len(set(map(tuple,pairs)))==len(pairs) and all(0<=a<N and 0<=b<N for a,b in pairs)
if j.get('unordered_pairs',True):assert all(a<=b for a,b in pairs)
jobs=[(a,b,s,t) for a,b in pairs for s in [-1,1] for t in [-1,1]]
bound={label:hashlib.sha256(path.read_bytes()).hexdigest() for label,path in [('executable_sha256',EXE),('source_sha256',ROOT/'verify_boundary_pair_costs.cpp'),('arithmetic_source_sha256',ROOT/'exact_dyadic_base.cpp'),('data_header_sha256',HEADER),('data_json_sha256',DATA)]}

def run(job):
    start=time.monotonic();p=subprocess.run([str(EXE),*map(str,job)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    txt=p.stdout;lines=txt.strip().splitlines();tail=lines[-1] if lines else ''
    prefix='PIECE '+' '.join(map(str,job))+' '
    pieces=[line[len(prefix):].split()[:2] for line in lines if line.startswith(prefix)]
    complete=len(lines)==K*K+1 and len(pieces)==K*K and set(map(tuple,pieces))=={(str(a),str(b)) for a in range(K) for b in range(K)} and tail.startswith('VERIFIED '+' '.join(map(str,job))+' ')
    (OUT/('_'.join(map(str,job))+'.log')).write_text(txt)
    r={'branch':job,'returncode':p.returncode,'complete':complete,'seconds':time.monotonic()-start,'summary':tail,'sha256':hashlib.sha256(txt.encode()).hexdigest()}
    print(tail if p.returncode==0 and complete else 'FAILED '+str(r),flush=True)
    return r

with ThreadPoolExecutor(max_workers=WORKERS) as pool:
    results=[f.result() for f in as_completed([pool.submit(run,x) for x in jobs])]
ok=len(results)==len(jobs) and all(r['returncode']==0 and r['complete'] for r in results)
payload={'status':'ALL REQUIRED BRANCHES PASSED' if ok else 'INCOMPLETE/FAILED','required_pairs':pairs,'K':K,**bound,'results':sorted(results,key=lambda r:r['branch'])}
(OUT/'manifest.json').write_text(json.dumps(payload,indent=2)+'\n');print(payload['status'],flush=True)
sys.exit(0 if ok else 1)

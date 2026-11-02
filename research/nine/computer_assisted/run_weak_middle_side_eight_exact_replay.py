#!/usr/bin/env python3
"""Archive the independent integer replay and four negative controls.

This wrapper does not make mathematical acceptance decisions beyond
requiring the standalone exact checker's complete PASS and exit zero.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import subprocess
import tempfile
import time

HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);args=ap.parse_args()
    cert=args.certificate.resolve();binary=HERE/'verify_weak_middle_side_eight_exact';source=binary.with_suffix('.cpp')
    data=json.loads(cert.read_text());kind=data['kind'];prefix=f'weak_middle_side_eight_{kind}_cpp'
    begin=time.monotonic();rows=[]
    proc=subprocess.Popen([str(binary),str(cert),'0','100000'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    for line in proc.stdout:
        print(line,end='',flush=True);rows.append(json.loads(line))
    error=proc.stderr.read();code=proc.wait()
    assert code==0,(code,error)
    assert rows and rows[-1]['status']=='EXACT_REPLAY_PASSED'
    report=rows[-1]
    report.update(certificate_sha256=sha(cert),checker_sha256=sha(source),
                  binary_sha256=sha(binary),wrapper_sha256=sha(Path(__file__)),
                  certificate_bytes=cert.stat().st_size,wall_seconds=time.monotonic()-begin,
                  compiler_command='g++ -std=c++17 -O3 -Wall -Wextra -pedantic verify_weak_middle_side_eight_exact.cpp -o verify_weak_middle_side_eight_exact',
                  scope='Original wide-main side cone triple bracketed by one original lower-left side square; no full010/11 closure claimed.')
    (HERE/(prefix+'_replay.json')).write_text(json.dumps(report,indent=2)+'\n')
    tests=[]
    x=copy.deepcopy(data);x['kind']='unknown';tests.append(('wrong_root_family',x))
    x=copy.deepcopy(data);x['events'][0]=10;tests.append(('unknown_split_or_leaf_rule',x))
    x=copy.deepcopy(data);x['events']=x['events'][:-1];tests.append(('missing_child',x))
    x=copy.deepcopy(data);x.update(events=[9],nodes=1,leaves=1,max_depth=0);tests.append(('false_whole_root_leaf',x))
    outcomes=[]
    with tempfile.TemporaryDirectory(prefix='damaged_',dir=HERE) as temp:
        for label,broken in tests:
            path=Path(temp)/(label+'.json');path.write_text(json.dumps(broken,separators=(',',':')))
            run=subprocess.run([str(binary),str(path),'0','0'],capture_output=True,text=True)
            assert run.returncode!=0,('damaged certificate accepted',label,run.stdout)
            outcomes.append({'control':label,'status':'REJECTED','exit_code':run.returncode,'reason':run.stderr.strip()})
    controls={'status':'ALL_DAMAGED_CONTROLS_REJECTED','certificate_sha256':report['certificate_sha256'],
              'checker_sha256':report['checker_sha256'],'controls':outcomes}
    (HERE/(prefix+'_negative_controls.json')).write_text(json.dumps(controls,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'leaves':report['leaves'],
                      'replay_report':prefix+'_replay.json','negative_controls':'ALL_REJECTED'}),flush=True)
if __name__=='__main__':main()

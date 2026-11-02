#!/usr/bin/env python3
"""Bind a JSON candidate to the independent directed-integer replay.

This wrapper imports neither the discovery producer nor any producer
arithmetic. Its C++ engine reconstructs all fixed rational roots and
midpoints, all original physical scalars, and every strict leaf.
"""
from array import array
from fractions import Fraction
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,time

HERE=Path(__file__).resolve().parent
CPP=HERE/'verify_two_shoulder_mainheight_exact.cpp'
EXE=HERE/'verify_two_shoulder_mainheight_exact.bin'


def metadata(data):
    assert data['schema']=='weak_middle_two_weak_short_mainheight_cover_v1'
    assert data['proof_status']=='discovery_complete_pending_independent_replay'
    assert data['Q']=='1105/256'and data['main_height']=='-1/4'and data['floor']=='1/10'
    assert data['root_count']==16
    if 'frontier_count'in data:assert data['frontier_count']==0
    if 'frontier'in data:assert data['frontier']==[]
    assert 'frontier_count'in data or'frontier'in data
    events=data['events']
    assert isinstance(events,list)and all(type(v)is int and -21<=v<=6 for v in events)
    assert type(data['leaves'])is int and data['leaves']>=16
    assert data['nodes']==len(events)==2*data['leaves']-16
    assert type(data['max_depth'])is int and 0<=data['max_depth']<=70
    assert len(data['leaves_per_root'])==16
    assert all(type(v)is int and v>=0 for v in data['leaves_per_root'])
    assert sum(data['leaves_per_root'])==data['leaves']
    counts=data['counts']
    if isinstance(counts,dict):
        assert all(k in {str(i)for i in range(21)}for k in counts)
        counts=[counts.get(str(i),0)for i in range(21)]
    assert len(counts)==21 and all(type(v)is int and v>=0 for v in counts)
    assert sum(counts)==data['leaves']
    return events


def compile_checker():
    subprocess.run(['g++','-std=c++17','-O3','-fno-fast-math',str(CPP),'-o',str(EXE)],check=True)


def run(data):
    events=metadata(data)
    payload=f"{len(events)} {data['leaves']}\n".encode()+array('b',events).tobytes()
    process=subprocess.run([str(EXE)],input=payload,stdout=subprocess.PIPE,check=False)
    output=json.loads(process.stdout)if process.stdout else{}
    if process.returncode:
        return False,{'return_code':process.returncode,**output}
    assert output['complete']is True
    assert output['nodes']==len(events)and output['strict_leaves']==data['leaves']
    assert output['maximum_depth']==data['max_depth']
    counts=data['counts']
    if isinstance(counts,dict):counts=[counts.get(str(i),0)for i in range(21)]
    assert output['counts']==counts
    assert output['leaves_per_root']==data['leaves_per_root']
    return True,output


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',nargs='?',type=Path,default=HERE/'two_shoulder_mainheight_cover.json')
    ap.add_argument('--no-compile',action='store_true');args=ap.parse_args()
    raw=args.certificate.read_bytes()
    packed=args.certificate.name.endswith('.gz')
    json_bytes=gzip.decompress(raw)if packed else raw
    data=json.loads(json_bytes);metadata(data)
    if not args.no_compile:compile_checker()
    start=time.monotonic();passed,result=run(data)
    result.update(proof_status='independent_exact_replay_passed'if passed else'independent_exact_replay_failed',
        certificate_sha256=hashlib.sha256(raw).hexdigest(),
        certificate_file=args.certificate.name,
        certificate_encoding='gzip'if packed else'utf-8 JSON',
        decompressed_json_sha256=hashlib.sha256(json_bytes).hexdigest(),
        decompressed_json_bytes=len(json_bytes),
        checker_cpp_sha256=hashlib.sha256(CPP.read_bytes()).hexdigest(),
        checker_wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        checker_executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest(),
        arithmetic='standalone 48-bit directed integer intervals; signed 128-bit intermediates; integer square roots',
        wall_seconds=time.monotonic()-start)
    if passed:result['least_positive_reserve']=str(Fraction(int(result['least_positive_reserve_numerator']),1<<result['scale_bits']))
    base=args.certificate.name.removesuffix('.gz').removesuffix('.json')
    destination=args.certificate.with_name(base+'_independent_exact_replay.json')
    destination.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    if not passed:raise SystemExit(2)


if __name__=='__main__':main()

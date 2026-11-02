#!/usr/bin/env python3
"""Small independent rejection controls for the final upper-extra package.

This does not rerun the accepted complete arithmetic forest.
"""
from pathlib import Path
from array import array
import gzip,hashlib,importlib.util,json,subprocess,sys

BASE=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
CERT=BASE/'bad_upper_extra_floor_cover.json'
if not CERT.exists():CERT=BASE/'bad_upper_extra_floor_cover.json.gz'
WRAPPER=BASE/'verify_bad_upper_extra_floor_exact.py'
ENGINE=BASE/'verify_bad_upper_extra_floor_exact.bin'
spec=importlib.util.spec_from_file_location('final_upper_extra_checker',WRAPPER)
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
raw_certificate=CERT.read_bytes()
json_bytes=gzip.decompress(raw_certificate) if CERT.name.endswith('.gz') else raw_certificate
data=json.loads(json_bytes)
results=[]

def metadata_control(label,mutate):
    trial=dict(data);mutate(trial)
    try: checker.metadata(trial)
    except (AssertionError,KeyError,TypeError,ValueError,OverflowError) as exc:
        results.append({'control':label,'rejected':True,'stage':'metadata','exception':type(exc).__name__})
    else: raise AssertionError('unexpectedly accepted '+label)

metadata_control('changed target Q',lambda d:d.__setitem__('Q','1106/256'))
metadata_control('nonempty frontier',lambda d:d.__setitem__('frontier_count',1))
metadata_control('omitted last node',lambda d:d.__setitem__('events',data['events'][:-1]))

def binary_control(label,tags,leaves):
    raw=f'{len(tags)} {leaves}\n'.encode()+array('b',tags).tobytes()
    result=subprocess.run([str(ENGINE)],input=raw,capture_output=True,check=False)
    assert result.returncode!=0,(label,result.stdout)
    results.append({'control':label,'rejected':True,'stage':'exact engine',
                    'return_code':result.returncode,
                    'stderr':result.stderr.decode().strip(),
                    'stdout':result.stdout.decode().strip()})

# A 24-root all-leaf forest has valid structural counts. Its first claimed
# channel is not strictly negative on the whole first root.
binary_control('false whole-root scalar leaf',[-1]*24,24)
# These direct-engine controls bypass the wrapper intentionally.
binary_control('unknown split coordinate six',[6]+[-1]*23,24)
binary_control('unknown scalar channel twenty-one',[-22]+[-1]*23,24)

report={'status':'all six independent damaged controls rejected',
        'certificate_sha256':hashlib.sha256(raw_certificate).hexdigest(),
        'decompressed_json_sha256':hashlib.sha256(json_bytes).hexdigest(),
        'checker_cpp_sha256':hashlib.sha256((BASE/'verify_bad_upper_extra_floor_exact.cpp').read_bytes()).hexdigest(),
        'checker_wrapper_sha256':hashlib.sha256(WRAPPER.read_bytes()).hexdigest(),
        'checker_executable_sha256':hashlib.sha256(ENGINE.read_bytes()).hexdigest(),
        'complete_forest_replayed_here':False,'controls':results}
out=Path(__file__).with_name('bad_upper_extra_floor_independent_controls.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))

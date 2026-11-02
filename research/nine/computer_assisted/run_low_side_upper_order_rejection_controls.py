#!/usr/bin/env python3
"""Targeted rejection controls for the source-bound upper-order replay."""
from copy import deepcopy
from pathlib import Path
import hashlib,json,subprocess
from run_low_side_upper_order_exact_replay import build_checker,events_for,no_duplicates

HERE=Path(__file__).resolve().parent


def main():
    certificate=HERE/'low_side_upper_order_compact_cover.json'
    raw=certificate.read_bytes()
    original=json.loads(raw,object_pairs_hook=no_duplicates)
    events,_=events_for(original)
    payload=(str(len(events))+' '+str(original['leaves'])+'\n').encode()+events
    controls=[]

    def wrapper_control(name,mutate):
        data=deepcopy(original)
        mutate(data)
        try:
            events_for(data)
        except (AssertionError,KeyError,TypeError,ValueError):
            controls.append({'name':name,'result':'REJECTED','layer':'wrapper'})
        else:
            raise AssertionError(('malformed metadata accepted',name))

    wrapper_control('wrong_schema',lambda d:d.update(schema='not_the_certificate_schema'))
    wrapper_control('nonempty_frontier',lambda d:d.update(remaining=1))
    wrapper_control('truncated_tree',lambda d:d['events'].pop())
    wrapper_control('invalid_split',lambda d:d['events'].__setitem__(0,6))
    wrapper_control('invalid_scalar_code',lambda d:d['events'].__setitem__(0,-14))
    wrapper_control('boolean_event',lambda d:d['events'].__setitem__(0,True))
    wrapper_control('wrong_per_root_counts',lambda d:d['leaves_per_root'].__setitem__(0,d['leaves_per_root'][0]+1))
    wrapper_control('wrong_leaf_counts',lambda d:d.update(leaves=d['leaves']+1))

    with build_checker()as(executable,build_metadata):
        def binary_control(name,data):
            run=subprocess.run([str(executable)],input=data,capture_output=True,check=False)
            assert run.returncode!=0,('malformed exact event stream accepted',name)
            controls.append({'name':name,'result':'REJECTED','layer':'standalone exact C++',
                             'reason':run.stderr.decode().strip()})

        binary_control('false_whole_root_leaves',b'8 8\n'+bytes([255])*8)
        binary_control('truncated_binary_events',payload[:-1])
        binary_control('trailing_binary_events',payload+b'\x00')
        header=(str(len(events))+' '+str(original['leaves'])+'\n').encode()
        binary_control('invalid_binary_split',header+b'\x06'+events[1:])
        binary_control('invalid_binary_scalar',header+b'\xf2'+events[1:])

    report={'result':'PASS','controls':controls,
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'controls_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'wrapper_sha256':hashlib.sha256((HERE/'run_low_side_upper_order_exact_replay.py').read_bytes()).hexdigest(),
            **build_metadata}
    (HERE/'low_side_upper_order_rejection_controls.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Targeted malformed-input controls for the independent Fraction checker."""
from copy import deepcopy
from pathlib import Path
import hashlib,json
from verify_low_side_with_lower_central import verify

HERE=Path(__file__).resolve().parent


def main():
    certificate=HERE/'low_side_with_lower_central_cover.json'
    raw=certificate.read_bytes();original=json.loads(raw)
    controls=[]

    def control(name,mutate):
        data=deepcopy(original);mutate(data)
        try:
            verify(data)
        except (AssertionError,KeyError,TypeError,ValueError):
            controls.append({'name':name,'result':'REJECTED'})
        else:
            raise AssertionError(('malformed certificate accepted',name))

    control('changed_root',lambda d:d['root'][0].__setitem__(1,'2'))
    control('missing_root',lambda d:d['roots'].pop())
    control('duplicate_chirality',lambda d:d['roots'][1].update(signs=d['roots'][0]['signs']))
    control('missing_last_node',lambda d:d['nodes'].pop())
    control('nonempty_frontier',lambda d:d.update(remaining=1,pending=[0]))

    def whole_roots(d,rule=0):
        d['nodes']=[{'rule':rule,'upper':'-1'}for _ in range(4)]
        for j,root in enumerate(d['roots']):root['index']=j
        d.update(leaves=4,counts=[4]+[0]*11,maximum_depth=0)
    control('false_whole_root_leaf',whole_roots)
    control('illegal_leaf_rule',lambda d:whole_roots(d,12))
    control('illegal_split_axis',lambda d:d['nodes'][d['roots'][0]['index']].update(axis=5))
    control('boolean_leaf_rule',lambda d:whole_roots(d,True))

    report={'result':'PASS','controls':controls,
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'checker_sha256':hashlib.sha256((HERE/'verify_low_side_with_lower_central.py').read_bytes()).hexdigest(),
            'controls_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'low_side_with_lower_central_rejection_controls.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()

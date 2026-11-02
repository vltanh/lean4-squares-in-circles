#!/usr/bin/env python3
"""Malformed-proof and false-leaf controls for the standalone exact replay."""
from pathlib import Path
import gzip,hashlib,json
import verify_two_shoulder_mainheight_exact as verifier

HERE=Path(__file__).resolve().parent
REPORT=HERE/'two_shoulder_mainheight_cover_independent_exact_replay.json'


def main():
    accepted=json.loads(REPORT.read_text())
    cover=HERE/accepted['certificate_file'];raw=cover.read_bytes()
    json_bytes=gzip.decompress(raw)if cover.name.endswith('.gz')else raw
    data=json.loads(json_bytes)
    assert accepted['proof_status']=='independent_exact_replay_passed'and accepted['complete']is True
    assert accepted['certificate_sha256']==hashlib.sha256(raw).hexdigest()
    assert accepted['decompressed_json_sha256']==hashlib.sha256(json_bytes).hexdigest()
    assert accepted['checker_cpp_sha256']==hashlib.sha256(verifier.CPP.read_bytes()).hexdigest()
    assert accepted['checker_wrapper_sha256']==hashlib.sha256(Path(verifier.__file__).read_bytes()).hexdigest()
    assert accepted['checker_executable_sha256']==hashlib.sha256(verifier.EXE.read_bytes()).hexdigest()
    records=[]

    def reject(name,change):
        bad=dict(data);change(bad)
        try:
            passed,result=verifier.run(bad)
        except (AssertionError,KeyError,TypeError,ValueError,IndexError)as error:
            records.append({'name':name,'rejected':True,'exception':type(error).__name__})
        else:
            assert not passed,('damaged proof accepted',name)
            records.append({'name':name,'rejected':True,'engine_return_code':result['return_code'],
                            'failed_event':result.get('failed_event'),'failed_root':result.get('root')})

    reject('wrong_schema',lambda d:d.update(schema='unrelated_cover'))
    reject('unfinished_status',lambda d:d.update(proof_status='incomplete_discovery'))
    reject('wrong_Q',lambda d:d.update(Q='1106/256'))
    reject('wrong_main_threshold',lambda d:d.update(main_height='-3/10'))
    reject('wrong_floor_threshold',lambda d:d.update(floor='1/9'))
    reject('missing_sign_root',lambda d:d.update(root_count=15))
    reject('nonempty_frontier',lambda d:d.update(frontier_count=1))
    reject('nonempty_python_frontier',lambda d:d.update(frontier=[{'node':0}]))
    reject('wrong_node_count',lambda d:d.update(nodes=d['nodes']-1))
    reject('wrong_leaf_count',lambda d:d.update(leaves=d['leaves']+1))
    reject('unreplayable_depth',lambda d:d.update(max_depth=71))
    reject('wrong_root_count_sum',lambda d:d.update(leaves_per_root=[0]*16))
    reject('wrong_channel_count_sum',lambda d:d.update(counts=[0]*21))

    old=data['events'][0]
    for name,value in [('invalid_split',7),('invalid_scalar',-22),('noninteger_tag',0.0),('boolean_tag',True)]:
        try:
            data['events'][0]=value;reject(name,lambda d:None)
        finally:data['events'][0]=old

    def false_whole_roots(d):
        d.update(events=[-1]*16,nodes=16,leaves=16,max_depth=0,
                 counts=[16]+[0]*20,leaves_per_root=[1]*16)
    reject('false_whole_root_strict_leaves',false_whole_roots)

    answer={'result':'PASS','controls_rejected':len(records),'controls':records,
        'certificate_sha256':accepted['certificate_sha256'],
        'checker_cpp_sha256':accepted['checker_cpp_sha256'],
        'checker_wrapper_sha256':accepted['checker_wrapper_sha256'],
        'scope':'metadata, complete fixed roots, preorder tags, counts, and false exact scalar leaf rejection'}
    target=HERE/'two_shoulder_mainheight_rejection_controls.json'
    target.write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps(answer),flush=True)


if __name__=='__main__':main()

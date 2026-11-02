#!/usr/bin/env python3
"""Short rejected controls for the complete exact middle-main verifier."""
import argparse,hashlib,json,tempfile
from pathlib import Path
from verify_middle_main_side_triple import verify

def main():
    base=Path(__file__).resolve().parent
    p=argparse.ArgumentParser();p.add_argument('--certificate',type=Path,default=base/'middle_main_low_floor_candidate.json');p.add_argument('--report',type=Path,default=base/'middle_main_side_triple_negative_controls.json');a=p.parse_args()
    original=a.certificate.read_bytes();source=json.loads(original)
    controls=[('unknown_split',[7]),('unproved_root_leaf',[-6]),('incomplete_root_split',[0]),('noninteger_split',[False])]
    results=[]
    with tempfile.TemporaryDirectory() as tmp:
        for name,events in controls:
            data={'status':'COMPLETE_UNTRUSTED_DISCOVERY','kind':'low_floor','nodes':len(events),'leaves':sum(type(x) is int and x<0 for x in events),'max_depth':0,'events':events}
            path=Path(tmp)/(name+'.json');path.write_text(json.dumps(data)+'\n')
            try:verify(path)
            except AssertionError as exc:results.append({'control':name,'result':'REJECTED','reason':str(exc)[:1000]})
            else:raise AssertionError(('invalid control accepted',name))
    report={'status':'ALL_FOUR_DAMAGED_CONTROLS_REJECTED','accepted_candidate_kind':source['kind'],'certificate_sha256':hashlib.sha256(original).hexdigest(),'checker_sha256':hashlib.sha256((base/'verify_middle_main_side_triple.py').read_bytes()).hexdigest(),'controls':results}
    a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()

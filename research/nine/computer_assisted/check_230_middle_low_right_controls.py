#!/usr/bin/env python3
"""Damaged-certificate controls for the independent central-right replay."""
from pathlib import Path
import copy,gzip,hashlib,json,tempfile
import verify_230_middle_low_right as verifier

HERE=Path(__file__).resolve().parent
cert_path=HERE/'230_middle_low_right_complete_cover.json.gz'
raw=cert_path.read_bytes();original=json.loads(gzip.decompress(raw))
results=[]
with tempfile.TemporaryDirectory(prefix='central_right_controls_') as temporary:
    for name in ('changed_root_boundary','missing_child','unknown_rule','false_whole_root_exclusion'):
        damaged=copy.deepcopy(original)
        if name=='changed_root_boundary':damaged['root'][4][0]='-1/3'
        elif name=='missing_child':damaged['tree'][0]['children']=damaged['tree'][0]['children'][:1]
        elif name=='unknown_rule':damaged['tree']=[{'tag':'unsupported'}];damaged['closed']=1
        else:damaged['tree']=[{'tag':'direct'}];damaged['closed']=1
        path=Path(temporary)/(name+'.json.gz')
        path.write_bytes(gzip.compress(json.dumps(damaged).encode()))
        try:verifier.verify(path)
        except (AssertionError,ValueError,IndexError,ZeroDivisionError) as error:
            results.append({'control':name,'rejected':True,'reason':str(error)[:400]})
        else:raise AssertionError('A damaged certificate was accepted: '+name)
report={'result':'PASS','certificate_sha256':hashlib.sha256(raw).hexdigest(),'controls':results,'rejected_count':len(results)}
(HERE/'230_middle_low_right_negative_controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

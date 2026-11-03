#!/usr/bin/env python3
"""Reject incomplete or damaged deep-boundary rational certificates."""
from pathlib import Path
import copy
import hashlib
import json
from weak_outer_deep_boundary_verify import verify

HERE=Path(__file__).resolve().parent
CERT=HERE/'weak_outer_deep_boundary_angle_certificate.json'

def missing_case(d):d['cases'].pop()
def missing_angle(d):d['cases'][0]['proofs'].pop()
def repeated_target(d):d['cases'][0]['proofs'][1]=copy.deepcopy(d['cases'][0]['proofs'][0])
def negative_weight(d):d['cases'][0]['proofs'][0]['weights'][0][1]='-1'
def false_identity(d):d['cases'][0]['proofs'][0]['weights']=[]
def false_error_cost(d):d['cases'][0]['proofs'][0]['error_weight']='1000'

def main():
    data=json.loads(CERT.read_text());reports=[]
    for name,damage in [('missing_sign_separator_case',missing_case),
      ('missing_signed_angle',missing_angle),('repeated_angle_target',repeated_target),
      ('negative_multiplier',negative_weight),('false_exact_identity',false_identity),
      ('false_nonlinear_error_cost',false_error_cost)]:
        broken=copy.deepcopy(data);damage(broken)
        try:verify(broken)
        except (AssertionError,ValueError,KeyError,TypeError) as exc:
            reports.append({'control':name,'status':'REJECTED','reason':str(exc)[:300]})
        else:raise AssertionError('Damaged certificate accepted: '+name)
    out={'status':'PASS','controls':reports,
      'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),
      'verifier_sha256':hashlib.sha256((HERE/'weak_outer_deep_boundary_verify.py').read_bytes()).hexdigest()}
    (HERE/'weak_outer_deep_boundary_rejection_controls.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()

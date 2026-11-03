#!/usr/bin/env python3
"""Numerical dual discovery, followed by exact reconstruction and replay.

The delivered certificate is independently replayable without NumPy/SciPy.
This optional producer searches nonnegative row identities; no optimizer
status or floating residual is accepted as a proof.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import numpy as np
from scipy.optimize import linprog
from weak_outer_deep_boundary_verify import CASES,CENTERS,RADIUS,physical_rows,verify

def discover():
    result={'schema':'weak-outer-deep-boundary-angle-contraction-v1',
      'radius':str(RADIUS),'centers':[[str(z) for z in p] for p in CENTERS],
      'unboxed_original_center':'F','cases':[]}
    maximum=F(0)
    for sc,sd,direction in CASES:
        rows=physical_rows(sc,sd,direction)
        mat=np.array([r[1] for r in rows],dtype=float).T
        costs=np.array([float(r[2]) for r in rows])
        case={'sign_C':sc,'sign_D':sd,'separator':direction,'proofs':[]}
        largest=F(0)
        for angle in range(9):
            for sign in (-1,1):
                target=[F(0)]*36;target[18+angle]=F(sign)
                lp=linprog(costs,A_eq=mat,b_eq=np.array(target,dtype=float),
                  bounds=[(0,None)]*len(rows),method='highs',options={'threads':1})
                assert lp.success,(sc,sd,direction,angle,sign,lp.message)
                weights=[F(float(v)).limit_denominator(10**8) for v in lp.x]
                assert all(v>=0 for v in weights)
                exact=[sum(weights[k]*rows[k][1][j] for k in range(len(rows))) for j in range(36)]
                assert exact==target,'Rational reconstruction did not give an exact identity.'
                cost=sum(weights[k]*rows[k][2] for k in range(len(rows)))
                assert cost<1/RADIUS
                case['proofs'].append({'angle':angle,'upper_sign':sign,
                  'weights':[[k,str(v)] for k,v in enumerate(weights) if v],
                  'error_weight':str(cost)})
                largest=max(largest,cost)
        case['K']=str(largest);maximum=max(maximum,largest);result['cases'].append(case)
    result['maximum_K']=str(maximum)
    verify(result)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();data=discover()
    args.out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'status':'EXACT_RECONSTRUCTION_PASS','cases':len(data['cases']),
      'identities':sum(len(c['proofs']) for c in data['cases']),'maximum_K':data['maximum_K']}))

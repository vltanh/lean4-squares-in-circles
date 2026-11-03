#!/usr/bin/env python3
"""Floating diagnostic only: insert an exact closed-weak boundary control.

The independent Fraction control checker supplies the geometric proof.
This script deliberately imports the current numerical producer to expose
its closed-relaxation boundary; its output is not a strict-mask certificate.
"""
import hashlib,json
from pathlib import Path
import numpy as np
import weak_outer_numeric_bulk_pose_lp as pose
from weak_outer_numeric_relaxed_boundary_control import CENTERS,verify

verify();centers=np.array(CENTERS,dtype=float)
box=tuple([(-1.,1.)]*3+[(0.,1.)]+[(-1.,1.)]*5)
pos=tuple([(-pose.rho,pose.rho)]*18);choices=[]
for i,j in pose.base.PAIRS:
    d=centers[j]-centers[i]
    if (i,j)==(2,3):owner,axis,sign=3,0,1
    elif (i,j)==(3,6):owner,axis,sign=6,1,1
    else:
        axis=0 if abs(d[0])>=1 else 1
        sign=1 if d[axis]>=0 else -1;owner=i
    choices.append(((i,j),'sat',(owner,axis,sign)))
A,B,names,cb,hs,gs=pose.matrix(box,pos,tuple(choices))
x=np.zeros(A.shape[1]);x[:18]=centers.ravel();x[18:27]=1;x[45:54]=.5;cursor=54
for (i,j),kind,(owner,axis,sign) in choices:
    d=centers[j]-centers[i]
    n=np.array([sign,0.]) if axis==0 else np.array([0.,sign])
    x[cursor:cursor+6]=[n[0]*d[0],n[1]*d[1],1,0,0,0];cursor+=6
res=A@x-B
corner_slack=[-res[k] for k,name in enumerate(names) if name.startswith('dense_original_corner')]
out={'diagnostic_only':True,'matrix_rows':len(B),'variables':len(x),
     'originals':9,'physical_pair_branches':len(choices),
     'maximum_float_row_violation':float(max(res)),
     'minimum_dense_corner_slack':float(min(corner_slack)),
     'strict_weak_defect':0,'strict_001_predicate_satisfied':False,
     'producer_sha256':hashlib.sha256(Path(pose.__file__).read_bytes()).hexdigest()}
print(json.dumps(out,indent=2))

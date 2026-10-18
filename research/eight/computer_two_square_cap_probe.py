#!/usr/bin/env python3
"""Exploratory two-square mixed-center, same-sign cap optimization.

NOT A PROOF. Uses nonconvex scipy SLSQP with multiple starts. Failed
solver status / tiny negative residuals mean the numerical output must
NOT be presented as a rigorous optimum or impossibility certificate.

It DOES model true square vertices, eight signed separating-axis
candidates, whole-square cap membership, and inner/outer center norms.
The exact hand results in HUMAN_CAP_ENVELOPE_37_100.md and
HUMAN_MIXED_HIGH_CAP_37_100.md do not depend on this optimization.

Usage:
  python -m pip install numpy scipy
  OPENBLAS_NUM_THREADS=1 python research/eight/computer_two_square_cap_probe.py --starts 5
"""
import argparse
import json
from math import pi
import numpy as np
from scipy.optimize import minimize

def geom(v):
    px,py,pt,qx,qy,qt,R2=v
    p=np.array([px,py]); q=np.array([qx,qy])
    e=np.array([np.cos(pt),np.sin(pt)])
    f=np.array([-np.sin(pt),np.cos(pt)])
    a=np.array([np.cos(qt),np.sin(qt)])
    b=np.array([-np.sin(qt),np.cos(qt)])
    vp=np.array([p+(i*e+j*f)/2 for i in (-1,1) for j in (-1,1)])
    vq=np.array([q+(i*a+j*b)/2 for i in (-1,1) for j in (-1,1)])
    return p,q,e,f,a,b,vp,vq

def residuals(v,h,axis_id):
    p,q,e,f,a,b,vp,vq=geom(v)
    n=(e,-e,f,-f,a,-a,b,-b)[axis_id]
    sat=np.dot(n,q-p)-(abs(n@e)+abs(n@f)+abs(n@a)+abs(n@b))/2
    return np.r_[1-p@p,q@q-1,vp[:,1].min()-h,vq[:,1].min()-h,
                 sat,v[6]-np.einsum('ij,ij->i',vp,vp),
                 v[6]-np.einsum('ij,ij->i',vq,vq)]

def run(h,starts,seed):
    rng=np.random.default_rng(seed)
    bounds=[(0,1),(h+.5,1),(-pi/4,pi/4),
            (0,1.6),(h+.5,1.6),(-pi/4,pi/4),(3.2,5)]
    axis_q=(h+1)**2+9/4
    best=None
    for axis_id in range(8):
        for k in range(starts):
            if k==0:
                x=np.array([0,.95,0,1,h+.5,0,axis_q])
            else:
                x=np.array([rng.uniform(0,.2),
                            rng.uniform(h+.5,.99),
                            rng.uniform(-.6,.6),
                            rng.uniform(.75,1.25),
                            rng.uniform(h+.5,1.1),
                            rng.uniform(-.6,.6),
                            rng.uniform(max(3.5,axis_q-.2),
                                        min(4.9,axis_q+.5))])
            r=minimize(lambda v:v[6],x,method="SLSQP",bounds=bounds,
                constraints={"type":"ineq",
                             "fun":lambda v,j=axis_id:residuals(v,h,j)},
                options={"maxiter":300,"ftol":2e-11})
            minimum=float(residuals(r.x,h,axis_id).min())
            # A tolerance is necessary for exploratory float arithmetic.
            # Negative residuals / success=False are explicitly reported.
            if minimum>=-3e-8 and (best is None or
                r.x[6]<best["radius_squared"]):
                best={"axis":axis_id,
                      "radius_squared":float(r.x[6]),
                      "variables":r.x.tolist(),
                      "minimum_constraint_residual":minimum,
                      "success":bool(r.success)}
    return {"offset":h,
            "axis_aligned_ansatz_radius_squared":axis_q,
            "best_local_candidate":best,
            "comparison_ceiling_radius_squared":9789/2500,
            "warning":"LOCAL NONCERTIFYING SEARCH; read solver success/residual"}

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--offsets",nargs="+",type=float,
                    default=[7/24,1/3,37/100])
    ap.add_argument("--starts",type=int,default=6)
    ap.add_argument("--seed",type=int,default=20261012)
    args=ap.parse_args()
    for idx,h in enumerate(args.offsets):
        print(json.dumps(run(h,args.starts,args.seed+idx)),flush=True)

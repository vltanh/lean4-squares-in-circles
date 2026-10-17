#!/usr/bin/env python3
"""NONCERTIFYING convex center-fiber oracle for the seven directed n8 separators.

After fixing the seven true square frame angles and the tilted
separator direction t, the remaining 14 center coordinates and
squared radius q form a convex quadratic epigraph program:
  28 true disk-vertex inequalities (quadratic)
  7 directed full-square support inequalities (affine).
This program uses a numerical SLSQP implementation with analytic
constraint Jacobians. Numeric output, even success=True, is a
DISCOVERY DIAGNOSTIC, NEVER an exact proof or an exhaustive certificate.

Use:
  OPENBLAS_NUM_THREADS=1 python computer_seven_angle_fiber_oracle.py --random 200
  OPENBLAS_NUM_THREADS=1 python computer_seven_angle_fiber_oracle.py --random 0
Requires NumPy and SciPy.

The exact geometric proof and full-eight-square owner-fiber reduction
are in GLOBAL_SAT_ANGLE_FIBER_DUALITY.md. An independent exact rational
boundary-fiber certificate is in HUMAN_SEVEN_PARALLEL_EXACT_DUAL.md.
"""
import argparse
from math import atan2, pi
import numpy as np
from scipy.optimize import minimize

QSTAR_APPROX = 3.9155341375174753
# Near-sharp *rational* base construction (no global optimality assumption).
r=1.753659; U=331179/200000; u=11/12
v=.547767; w=95073/50000
c=255/257; s=32/257
h1=c*r-s*u-2-c
h2=s*w-c*v-1-s
P5=np.array([h1*c-h2*s,h1*s+h2*c])
e=np.array([c,s]); f=np.array([-s,c])
BASE=np.array([
    [r-.5,.5-u], [U-.5,1.5-u],
    [U-1.5,1.35], [U-2.5,1.5-v],
    [.5-w,.5-v], P5+(e+f)/2, P5+(e+f)/2+e
])
T0=atan2(s,c)
PAIRS=[(0,1,"b"),(2,1,"a"),(3,2,"a"),
       (4,3,"b"),(6,0,"e"),(5,6,"e"),(5,4,"f")]
NAMES=("A","B","T","D","E","H","G")

class CenterFiber:
    """One convex center/radius fiber of prescribed true orientations."""
    def __init__(self,angles,t):
        angles=np.asarray(angles,dtype=float)
        assert angles.shape==(7,)
        self.e=np.column_stack((np.cos(angles),np.sin(angles)))
        self.f=np.column_stack((-np.sin(angles),np.cos(angles)))
        self.offsets=np.array([
            (i*self.e+j*self.f)/2 for i in (-1,1)
            for j in (-1,1)
        ]).transpose(1,0,2)
        axis={
            "a":np.array([1.,0.]),
            "b":np.array([0.,1.]),
            "e":np.array([np.cos(t),np.sin(t)]),
            "f":np.array([-np.sin(t),np.cos(t)])
        }
        self.A=np.zeros((7,15))
        self.b=np.zeros(7)
        for k,(i,j,d) in enumerate(PAIRS):
            n=axis[d]
            self.A[k,2*j:2*j+2]=n
            self.A[k,2*i:2*i+2]=-n
            self.b[k]=(
                abs(self.e[i]@n)+abs(self.f[i]@n)
                +abs(self.e[j]@n)+abs(self.f[j]@n)
            )/2

    def constraints(self,x):
        vertex=x[:14].reshape(7,2)[:,None,:]+self.offsets
        disk=(x[-1]-(vertex*vertex).sum(axis=2)).ravel()
        directed=self.A@x-self.b
        return np.r_[directed,disk]

    def jacobian(self,x):
        vertex=x[:14].reshape(7,2)[:,None,:]+self.offsets
        J=np.zeros((35,15))
        J[:7]=self.A
        for i in range(7):
            J[7+4*i:7+4*i+4,2*i:2*i+2]=-2*vertex[i]
            J[7+4*i:7+4*i+4,-1]=1
        return J

    def solve(self,maxiter=140):
        x0=np.r_[BASE.ravel(),4.1]
        result=minimize(
            lambda x:x[-1],x0,
            method="SLSQP",
            jac=lambda x:np.r_[np.zeros(14),1.],
            bounds=[(-2.5,2.5)]*14+[(2.5,6.0)],
            constraints=[{
                "type":"ineq","fun":self.constraints,
                "jac":self.jacobian
            }],
            options={"maxiter":maxiter,"ftol":1e-10}
        )
        return result,float(np.min(self.constraints(result.x)))

def run():
    ap=argparse.ArgumentParser()
    ap.add_argument("--random",type=int,default=0)
    ap.add_argument("--seed",type=int,default=20261013)
    ap.add_argument("--maxiter",type=int,default=140)
    args=ap.parse_args()
    rng=np.random.default_rng(args.seed)
    record=(float("inf"),None)
    settings=[(np.r_[np.zeros(5),t,t],t) for t in
              (0.,T0,.2,.4)]
    for j in range(args.random):
        scale=(.02,.08,.25)[j%3]
        tilt=float(np.clip(T0+rng.normal(0,scale/2),0,pi/4))
        frames=np.r_[np.zeros(5),T0,T0]+rng.normal(0,scale,7)
        frames=np.clip(frames,-pi/4,pi/4)
        settings.append((frames,tilt))
    for idx,(frames,tilt) in enumerate(settings):
        f=CenterFiber(frames,tilt)
        result,residual=f.solve(maxiter=args.maxiter)
        if result.success and residual>=-1e-7 and result.fun<record[0]:
            record=(float(result.fun),(frames.copy(),tilt))
        if idx<4 or (idx+1)%100==0:
            print("sample",idx,"q_numerical",round(float(result.fun),10),
                  "min_residual",round(residual,9),
                  "solver_success",bool(result.success),
                  "delta_from_candidate",round(
                      float(result.fun)-QSTAR_APPROX,10))
    print("best_DIAGNOSTIC",record[0])
    print("REMINDER: not a certificate; all other true square pairs,")
    print("the eighth square, and all global SAT owner classes")
    print("remain outside this seven-directed-separator oracle.")

if __name__=="__main__":
    run()

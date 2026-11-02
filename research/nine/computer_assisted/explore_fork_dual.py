"""Exploratory dual bound for E/R/P fork; floating results are not proofs."""
import math,itertools
import numpy as np
from scipy.optimize import minimize_scalar
r=math.sqrt(1105)/16;a=46.;b=13.5;T=52.75
amax=math.asin(16/(15*math.sqrt(2)))-math.pi/4
def support(v,theta):
    c,s=math.cos(theta),math.sin(theta);x,y=v
    return (abs(x*c+y*s)+abs(-x*s+y*c))/2
def min_support(vectors,interval=(-math.pi/4,math.pi/4)):
    lo,hi=interval;cand=[lo,hi]
    for x,y in vectors:
      p=math.atan2(y,x)
      for j in range(-3,4):
        t=p+j*math.pi/2
        if lo<=t<=hi:cand.append(t)
    return min(sum(support(v,t) for v in vectors) for t in cand)
def dual(w,z,k,ownerE='R',ownerP='P',floor=.1):
    n=np.array([-w,1.]);m=np.array([1.,z]);ex=np.array([1.,0.]);vE=a*ex-k*n;vR=b*m+k*n
    evec=[a*ex,vE,k*n];rvec=[vR,b*m,k*n];pvec=[b*(1+z)*ex,b*m]
    pe=sum(support(v,math.atan(w)) for v in evec) if ownerE=='E' else min_support(evec,(-amax,amax))
    pr=sum(support(v,math.atan(w)) for v in rvec) if ownerE=='R' else (sum(support(v,math.atan(z)) for v in rvec) if ownerP=='R' else min_support(rvec))
    pp=sum(support(v,math.atan(z)) for v in pvec) if ownerP=='P' else min_support(pvec)
    return b+r*(np.linalg.norm(vE)+np.linalg.norm(vR))-pe-pr-pp-b*z*floor
def main():
 for eo,po in [('R','R'),('R','P'),('E','R'),('E','P')]:
  vals=[]
  ws=np.linspace(0,1,31) if eo=='R' else np.linspace(-math.tan(amax),math.tan(amax),11)
  for w in ws:
   zs=[w] if eo=='R' and po=='R' else np.linspace(0,2,41)
   for z in zs:
    opt=minimize_scalar(lambda k:dual(w,z,k,eo,po),bounds=(0,40),method='bounded')
    vals.append((opt.fun-T,w,z,opt.x))
  print(eo,po,'maxgap',max(vals),'positive count',sum(v[0]>1e-6 for v in vals),'count',len(vals),flush=True)
if __name__=='__main__':main()

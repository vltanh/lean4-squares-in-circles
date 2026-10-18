#!/usr/bin/env python3
"""Exact Fraction verifier for selected genuine SAT center-fiber duals.

Usage: python verify_exact_angle_fiber_dual.py certificate.json
A PASS proves: EVERY configuration with the specified EXACT rational
square frames and all listed ACTUAL directed owner-axis separators
needs squared radius >= certificate["target_q"].

It does NOT prove the result over an interval of angles, all owner
words, or unrestricted eight-square packings.
"""
import json,sys
from fractions import Fraction as F

def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(k,a):return (k*a[0],k*a[1])
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def val(q):return F(str(q))

def check(cert):
    z=[val(t) for t in cert["frame_half_tangents"]]
    n=len(z);e=[];f=[];corners=[]
    for t in z:
        c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
        e.append((c,s));f.append((-s,c))
        assert dot(e[-1],e[-1])==dot(f[-1],f[-1])==1
        assert dot(e[-1],f[-1])==0
        corners.append([
            mul(F(1,2),add(mul(i,e[-1]),mul(j,f[-1])))
            for i in (-1,1) for j in (-1,1)
        ])
    mu=[F(0) for _ in range(n)]
    a=[(F(0),F(0)) for _ in range(n)]
    cvec=[(F(0),F(0)) for _ in range(n)]
    total=F(0)
    for i,k,mstr in cert["corner_weights"]:
        m=val(mstr)
        assert 0<=i<n and 0<=k<4 and m>=0
        mu[i]+=m
        a[i]=add(a[i],mul(m,corners[i][k]))
        total+=m
    assert total==1,"circle weights not normalized"
    edge_term=F(0)
    for i,j,axis_name,sgn,lamstr in cert["edges"]:
        assert 0<=i<j<n and sgn in (-1,1)
        lam=val(lamstr)
        assert lam>=0
        ai,ax=axis_name.split(".")
        assert ai in ("i","j") and ax in ("e","f")
        ii=i if ai=="i" else j
        axis=e[ii] if ax=="e" else f[ii]
        axis=mul(sgn,axis)
        support=(
            abs(dot(axis,e[i]))+abs(dot(axis,f[i]))+
            abs(dot(axis,e[j]))+abs(dot(axis,f[j]))
        )/2
        edge_term+=lam*support
        cvec[i]=add(cvec[i],mul(lam,axis))
        cvec[j]=sub(cvec[j],mul(lam,axis))
    dual=F(1,2)+edge_term
    for i in range(n):
        v=add(mul(2,a[i]),cvec[i])
        if mu[i]==0:
            assert v==(0,0),"unanchored square has unbalanced force"
        else:
            dual-=dot(v,v)/(4*mu[i])
    target=val(cert["target_q"])
    assert dual>=target,(dual,target)
    print("PASS: exact fixed-frame genuine support dual")
    print("n =",n,"edges =",len(cert["edges"]),
          "corner terms =",len(cert["corner_weights"]))
    print("certified q >=",dual,"=",float(dual))
    print("target_q =",target,"margin =",dual-target)
    print("SCOPE: exact frame angles and listed directed true SAT owners only")

if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))

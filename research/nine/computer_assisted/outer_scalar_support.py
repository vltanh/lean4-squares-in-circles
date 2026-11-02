"""Producer helpers for the shoulder-owned outer scalar envelope tables.

Floating routines propose rational multipliers. The independent replay
does not import this file, the proposal routines, or producer arithmetic.
"""
from fractions import Fraction as F
import math
import numpy as np
from joint_five_interval import (
    D,V,S,rad,rho,norm,minimum,free_sum,fixed_sum,scale,center_with_faces,
)
from joint_center_support import face_certificate,center_support
from explore_fork_dual import min_support,support

A=F(46)
B=F(27,2)
K=F(207,16)
T=F(211,4)
EPS=F(1,80)
DEN=4096
EBOX=(F(89,60),F(91,60),F(-1,8),F(1,8))
SBOX=(F(23,30),F(13,12),F(25,32),F(21,16))


def expression(box,cert,sign):
    """Historical scalar form; the caller substitutes its exact target."""
    w=D(V(box[0],box[1]),[1,0,0,0])
    t=D(V(box[2],box[3]),[0,1,0,0])
    z=-t if sign=='negative' else t
    den=cert['den']
    k=F(cert['k'],den)
    n=[-w,D(1)]
    m=[D(1),z]
    axis=[D(1),w]
    ve=[A+k*w,D(-k)]
    vs=[B-k*w,k+B*z]
    ecost=[[D(A),D(0)],scale(k,n)]
    cost=free_sum(ecost,True)
    xl,xh,yl,yh=EBOX
    box_support=((xl+xh)*ve[0]+(yl+yh)*ve[1]
                 +(xh-xl)*ve[0].abs()+(yh-yl)*ve[1].abs())/2
    ep=minimum([rad*norm(ve)-free_sum([ve,*ecost],True),
                rho*norm(ve)-cost,box_support-cost])
    sp=(center_with_faces(vs,axis,SBOX,cert['faces'],den)
        -fixed_sum([scale(B,m),scale(k,n)],axis))
    ans=ep+sp-T
    return ans+B*t if sign=='negative' else ans-B*t-B*(norm([D(1),t])-1)


def certificate(w,t,k,sign):
    kn=max(0,round(float(k)*DEN))
    kk=kn/DEN
    z=-t if sign=='negative' else t
    vs=np.array([float(B)-kk*w,kk+float(B)*z])
    faces=face_certificate(vs,math.atan(w),tuple(map(float,SBOX)),DEN)['lambda']
    return {'den':DEN,'k':kn,'faces':faces}


R_FLOAT=math.sqrt(1105)/16
RHO_FLOAT=math.sqrt(1105/256-.25)-.5
ENDPOINT_FRAME=(-math.atan(.07),math.atan(.07))


def scalar(w,z,k=None):
    """Floating support bound for discovery only."""
    a,b=46.,13.5
    if k is None:
        k=float(K)/(1+max(w,0))
    n,m=np.array([-w,1.]),np.array([1.,z])
    ve=np.array([a+k*w,-k])
    vs=np.array([b-k*w,k+b*z])
    ecosts=[np.array([a,0.]),k*n]
    emin=min_support(ecosts,ENDPOINT_FRAME)
    xl,xh,yl,yh=map(float,EBOX)
    ep=min(R_FLOAT*np.linalg.norm(ve)-min_support([ve,*ecosts],ENDPOINT_FRAME),
           RHO_FLOAT*np.linalg.norm(ve)-emin,
           max(xl*ve[0],xh*ve[0])+max(yl*ve[1],yh*ve[1])-emin)
    theta=math.atan(w)
    sh=(center_support(vs,theta,tuple(map(float,SBOX)))
        -support(b*m,theta)-support(k*n,theta))
    return ep+sh

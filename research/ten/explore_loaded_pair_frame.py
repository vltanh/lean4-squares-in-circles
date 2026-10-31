#!/usr/bin/env python3
"""Exploratory floating-point loaded-frame scan; not certified minima or a proof.

This preserves the probe behind LOADED_RUN_STRONGER_ANGLE_HANDOFF.md.
The grid and bisection do not establish exhaustive global bounds.
"""
import numpy as np
from math import pi
f=np.linspace(-pi/4,pi/4,40001)
w=np.cos(f)+np.abs(np.sin(f)); r1=(np.sqrt(w*w+16)-w)/2

def vmax(a,d):
 r0=(np.sqrt((np.cos(a)+abs(np.sin(a)))**2+16)-(np.cos(a)+abs(np.sin(a))))/2
 D=d+f-a
 H=(1+np.abs(np.cos(D))+np.abs(np.sin(D)))/2
 vals=np.array([np.abs(r1*np.cos(d-a)-r0*np.cos(a))-H,
 np.abs(r1*np.sin(d-a)+r0*np.sin(a))-H,
 np.abs(r1*np.cos(f)-r0*np.cos(d+f))-H,
 np.abs(-r1*np.sin(f)+r0*np.sin(d+f))-H])
 k,j=np.unravel_index(np.argmax(vals),vals.shape)
 return vals[k,j],k,f[j]
def opt(a):
 lo,hi=pi/6,pi/3
 for _ in range(38):
  mid=(lo+hi)/2
  if vmax(a,mid)[0]>=0:hi=mid
  else:lo=mid
 return hi*180/pi,vmax(a,hi)[1:]
for aa in np.arange(0,45.01,2.5):
 g=opt(aa*pi/180);b=opt(-aa*pi/180)
 print(round(aa,3),g,b,'sum',g[0]+b[0])

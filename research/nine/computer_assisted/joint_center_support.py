"""Floating support of a known square's exact center region and a box.

Exploration only. Every candidate is independently checked against all
circle and box inequalities before its support value is used.
"""
import math
from functools import lru_cache
import numpy as np
Q=1105/256
r=math.sqrt(Q)

@lru_cache(maxsize=2048)
def region(theta,box):
    c,s=math.cos(theta),math.sin(theta)
    u=np.array([c,s]);v=np.array([-s,c])
    verts=np.array([(i*u+j*v)/2 for i in [-1,1] for j in [-1,1]])
    centers=-verts
    xl,xh,yl,yh=box
    cand=[np.array([x,y]) for x in [xl,xh] for y in [yl,yh]]
    for p in centers:
        for xx in [xl,xh]:
            disc=Q-(xx-p[0])**2
            if disc>=0:
                for sign in [-1,1]:cand.append(np.array([xx,p[1]+sign*math.sqrt(disc)]))
        for yy in [yl,yh]:
            disc=Q-(yy-p[1])**2
            if disc>=0:
                for sign in [-1,1]:cand.append(np.array([p[0]+sign*math.sqrt(disc),yy]))
    for i,p in enumerate(centers):
        for q in centers[:i]:
            d=q-p;le=np.linalg.norm(d);mid=(p+q)/2
            perp=np.array([-d[1],d[0]])/le
            hh=math.sqrt(Q-le*le/4)
            cand.extend([mid+hh*perp,mid-hh*perp])
    def mask(ar):
        return ((ar[:,0]>=xl-1e-10)&(ar[:,0]<=xh+1e-10)&(ar[:,1]>=yl-1e-10)&(ar[:,1]<=yh+1e-10)&
          (np.max(np.sum((ar[:,None,:]+verts[None,:,:])**2,axis=2),axis=1)<=Q+1e-10))
    ar=np.array(cand);ar=ar[mask(ar)]
    return centers,ar,mask

def center_support(vec,theta,box):
    centers,static,mask=region(float(theta),tuple(map(float,box)))
    le=np.linalg.norm(vec)
    if le<1e-15:return 0.
    dynamic=centers+r*vec/le
    dynamic=dynamic[mask(dynamic)]
    vals=[float(np.max(ar@vec)) for ar in [static,dynamic] if len(ar)]
    return max(vals) if vals else -1e12

def support_point(vec,theta,box):
    centers,static,mask=region(float(theta),tuple(map(float,box)))
    le=np.linalg.norm(vec)
    if le<1e-15:
        return static[0] if len(static) else None
    dynamic=centers+r*vec/le
    dynamic=dynamic[mask(dynamic)]
    ar=np.concatenate([static,dynamic])
    return ar[int(np.argmax(ar@vec))] if len(ar) else None

def plain_support(vec,theta):
    c,s=math.cos(theta),math.sin(theta)
    aa,bb=sorted([abs(vec[0]*c+vec[1]*s),abs(-vec[0]*s+vec[1]*c)],reverse=True)
    le=math.hypot(aa,bb);rho=math.sqrt(Q-.25)-.5
    return rho*aa if 2*r*bb<=le else r*le-(aa+bb)/2

def face_certificate(vec,theta,box,den=4096):
    """Return nonnegative box-face multipliers, independently usable bounds.

    Face order: lower x, upper x, lower y, upper y. The final inequality is
    H_K(vec-sum lambda_i normal_i)+sum lambda_i bound_i, for the exact
    unboxed center region K. This expression is valid for every choice of
    the returned nonnegative multipliers; finding the point is discovery.
    """
    p=support_point(vec,theta,box)
    if p is None:raise ValueError('empty known-frame center box')
    xl,xh,yl,yh=box
    sn=np.array([[-1.,0.],[1.,0.],[0.,-1.],[0.,1.]])
    sb=np.array([-xl,xh,-yl,yh])
    centers,_,_=region(float(theta),tuple(map(float,box)))
    normals=[]
    for vertex in -centers:
        q=p+vertex
        if abs(q@q-Q)<1e-7:normals.append((q,None))
    for j,(s,bb) in enumerate(zip(sn,sb)):
        if abs(s@p-bb)<1e-7:normals.append((s,j))
    candidates=[np.zeros(4)]
    for i,(n,label) in enumerate(normals):
        if abs(n[0]*vec[1]-n[1]*vec[0])<=1e-7*(1+np.linalg.norm(vec)):
            coeff=float(n@vec/(n@n))
            if coeff>=-1e-8:
                lam=np.zeros(4)
                if label is not None:lam[label]=max(0,coeff)
                candidates.append(lam)
        for m,l2 in normals[:i]:
            mat=np.column_stack([n,m])
            if abs(np.linalg.det(mat))<1e-10:continue
            al,be=np.linalg.solve(mat,vec)
            if min(al,be)<-1e-7:continue
            lam=np.zeros(4)
            if label is not None:lam[label]+=max(0,al)
            if l2 is not None:lam[l2]+=max(0,be)
            candidates.append(lam)
    def value(lam):return plain_support(vec-lam@sn,theta)+lam@sb
    best=min(candidates,key=value)
    nums=np.maximum(0,np.round(best*den)).astype(int)
    rounded=nums/den
    return {'den':den,'lambda':nums.tolist(),'value':value(rounded),'support':float(vec@p),'loss':value(rounded)-float(vec@p)}

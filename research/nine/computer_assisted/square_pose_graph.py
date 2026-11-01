#!/usr/bin/env python3
"""Exact square-orientation relaxation on the fixed nineteen-cell cover.

The graph is a NECESSARY relaxation, never a test proving physical feasibility.
No floating arithmetic is used. See SQUARE_POSE_CERTIFICATES.md for the proof.
This producer uses the original fan triangulation and endpoint arithmetic;
its separate verifier uses a horizontal mesh and midpoint/radius arithmetic.
"""
from fractions import Fraction as F
import numpy as np
from itertools import product
import make_hex_cover as hc
D=1<<20
M=6
K=12

def fl(x):return x.numerator//x.denominator

def ce(x):return -fl(-x)

def mul_int(al,au,bl,bu):
    v=[al*bl,al*bu,au*bl,au*bu]
    return min(v),max(v)

def abs_min(l,h):return max(0,l,-h)

def build(m=M,k=K):
    if m not in (6,8) or k not in (12,24):
        raise ValueError("supported meshes are m=6 or 8, k=12 or 24")
    ts=[]
    for c,(q,r) in enumerate(hc.CELLS):
        cx,cy=3*q*m,(q+2*r)*m
        for n in range(6):
            a,b=hc.HEX[n],hc.HEX[(n+1)%6]
            def p(i,j):return cx+i*a[0]+j*b[0],cy+i*a[1]+j*b[1]
            for i in range(m):
                for j in range(m-i):
                    ts.append((c,tuple(sorted((p(i,j),p(i+1,j),p(i,j+1))))))
                    if i+j<=m-2:ts.append((c,tuple(sorted((p(i+1,j),p(i+1,j+1),p(i,j+1))))))
    ts=sorted(set(ts))
    ts=[t for t in ts if F(49,100)**2*hc.minimum_norm(t[1])<=4*m*m*F(91,60)**2]
    sqrtL,sqrtU=F(1732050807,10**9),F(1732050808,10**9)
    if not sqrtL*sqrtL < 3 < sqrtU*sqrtU:
        raise ValueError("invalid square-root enclosure")
    box=[]; norm=[]
    for c,t in ts:
        xx=[F(49*x,200*m) for x,y in t]
        yy=[v for x,y in t for v in (F(49*y,200*m)*sqrtL,F(49*y,200*m)*sqrtU)]
        box.append((fl(min(xx)*D),ce(max(xx)*D),fl(min(yy)*D),ce(max(yy)*D)))
        norm.append(fl(F(49,100)**2*hc.minimum_norm(t)/(4*m*m)*D*D))
    def axis(t):return (1-t*t)/(1+t*t),2*t/(1+t*t)
    endpoints=[axis(F(i,k)) for i in range(k+1)]
    ax=[(fl(endpoints[i+1][0]*D),ce(endpoints[i][0]*D),fl(endpoints[i][1]*D),ce(endpoints[i+1][1]*D)) for i in range(k)]
    lower=np.zeros((k,k),dtype=np.int64)
    for i in range(k):
        for j in range(k):
            values=[a*A+b*B+abs(a*B-b*A) for a,b in endpoints[i:i+2] for A,B in endpoints[j:j+2]]
            if max(i,j)<=min(i+1,j+1):values.append(F(1))
            lower[i,j]=fl((1+min(values))*D*D)
    states=[]
    for i,(c,t) in enumerate(ts):
        xl,xu,yl,yu=box[i]
        for o,(al,au,bl,bu) in enumerate(ax):
            valid=True
            for s,v in product((-1,1),repeat=2):
                sa=(s*al,s*au);tb=(v*bl,v*bu);sb=(s*bl,s*bu);ta=(v*al,v*au)
                xlo,xhi=2*xl+min(sa)-max(tb),2*xu+max(sa)-min(tb)
                ylo,yhi=2*yl+min(sb)+min(ta),2*yu+max(sb)+max(ta)
                if 64*(abs_min(xlo,xhi)**2+abs_min(ylo,yhi)**2)>1105*D*D:
                    valid=False;break
            if not valid:continue
            a,b=mul_int(al,au,xl,xu),mul_int(bl,bu,yl,yu)
            pu=abs_min(a[0]+b[0],a[1]+b[1])
            a,b=mul_int(-bu,-bl,xl,xu),mul_int(al,au,yl,yu)
            pv=abs_min(a[0]+b[0],a[1]+b[1])
            if 256*(norm[i]+pu+pv)+128*D*D>1105*D*D:continue
            states.append((c,i,o))
    # Every retained state contains one position triangle and a CLOSED angle arc.
    # Triangle, rather than rectangular, projection extrema. Each a/b
    # interval has four corners; use their u and v axes, with both signs.
    vertex=[]
    for c,t in ts:
        vv=[]
        for x,y in t:
            xx=F(49*x,200*m)*D
            ys=[F(49*y,200*m)*v*D for v in (sqrtL,sqrtU)]
            vv.append((fl(xx),ce(xx),fl(min(ys)),ce(max(ys))))
        vertex.append(vv)
    verts=np.array(vertex,dtype=np.int64)
    if int(np.max(np.abs(verts))) > 3*D:
        raise ValueError("integer arithmetic bound exceeded")
    limits=[]
    for al,au,bl,bu in ax:
        os=[]
        for a,b in product((al,au),(bl,bu)):
            for A,B in ((a,b),(-b,a)):
                xlo=A*verts[:,:,0 if A>=0 else 1];xhi=A*verts[:,:,1 if A>=0 else 0]
                ylo=B*verts[:,:,2 if B>=0 else 3];yhi=B*verts[:,:,3 if B>=0 else 2]
                os.append((np.min(xlo+ylo,axis=1),np.max(xhi+yhi,axis=1)))
        limits.append(os)
    limits=np.array(limits)
    lo,hi=limits[:,:,0,:],limits[:,:,1,:]
    # Keep exact previous center-separation condition.
    xy=np.array([t for c,t in ts],dtype=np.int64)
    normmax=np.zeros((len(ts),len(ts)),dtype=np.int64)
    for i,j in product(range(3),repeat=2):
        delta=xy[:,None,i,:]-xy[None,:,j,:]
        normmax=np.maximum(normmax,delta[:,:,0]**2+3*delta[:,:,1]**2)
    centerok=2401*normmax>=40000*m*m
    states=np.array(states,dtype=np.int64)
    cell,pos,ori=states.T
    n=len(states); adj=[0]*n
    for pi in range(len(ts)):
        projection=np.maximum(np.max(hi-lo[:,:,pi,None],axis=1),np.max(hi[:,:,pi,None]-lo,axis=1))
        for v in np.flatnonzero(pos==pi):
            a=2*np.maximum(projection[ori[v],pos],projection[ori,pos])>=lower[ori[v],ori]
            a &= centerok[pi,pos]
            a &= cell!=cell[v]
            adj[v]=int.from_bytes(np.packbits(a,bitorder='little').tobytes(),'little')
    groups=[sum(1<<int(i) for i in np.flatnonzero(cell==c)) for c in range(19)]
    result=dict(m=m,k=k,denominator=D,triangles=ts,box=box,norm=norm,axes=ax,lower=lower.tolist(),states=states.tolist(),adjacency=adj,groups=groups)
    return result

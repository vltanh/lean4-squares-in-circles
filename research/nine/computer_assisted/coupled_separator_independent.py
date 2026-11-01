"""Separate reconstruction of coupled-angle separator compatibility.

Obtains arc-triangle vertices by solving the two tangent-line equations.
Uses midpoint/radius projection enclosures and evaluates both owners directly,
without the producer's closed-form tangent vertex or packed transposition.
"""
from fractions import Fraction as F
from math import lcm
from itertools import product
import numpy as np
D=2**20


def require(ok,msg):
    if not ok:raise ValueError(msg)


def refine_independent(g, block=24):
    k=g['k'];require(k in (12,24) and g['denominator']==D,'geometry parameters')
    meta=g['contraction'];polys=meta['polygons'];lookup=np.asarray(meta['mapping'],dtype=np.int64)
    n=len(lookup);pmax=max(map(len,polys))
    arr=np.asarray([list(p)+[p[-1]]*(pmax-len(p)) for p in polys],dtype=np.int64)
    require(np.max(np.abs(arr))<=3*D,'position bound')
    xm=arr[:,:,0]+arr[:,:,1];xr=arr[:,:,1]-arr[:,:,0]
    ym=arr[:,:,2]+arr[:,:,3];yr=arr[:,:,3]-arr[:,:,2]
    endpoints=[(F(k*k-t*t,k*k+t*t),F(2*k*t,k*k+t*t)) for t in range(k+1)]
    lo=[];hi=[];thresholds=[];arc_data=[]
    for i in range(k):
        u,v=endpoints[i:i+2];det=u[0]*v[1]-u[1]*v[0]
        require(det>0,'positive arc')
        tangent=((v[1]-u[1])/det,(u[0]-v[0])/det)
        pts=(u,tangent,v);lower=[];upper=[];th=[];saved=[]
        for p in pts:
            denominator=lcm(p[0].denominator,p[1].denominator)
            A=int(p[0]*denominator);B=int(p[1]*denominator)
            require(max(abs(A),abs(B))<=denominator<=2*k*k,'coefficient arithmetic bound')
            H=[]
            for j in range(k):
                if i==j:z=F(2)
                else:
                    values=[]
                    for w in endpoints[j:j+2]:
                        dot=p[0]*w[0]+p[1]*w[1]
                        det=p[0]*w[1]-p[1]*w[0]
                        values.append(1+dot+(det if i<j else -det))
                    z=min(values)
                z*=D*D;H.append(z.numerator//z.denominator)
            for X,Y in ((A,B),(-B,A)):
                mid=X*xm+Y*ym;radius=abs(X)*xr+abs(Y)*yr
                require(not np.any((mid-radius)%2) and not np.any((mid+radius)%2),'midpoint parity')
                left=np.min((mid-radius)//2,axis=1)*D
                right=np.max((mid+radius)//2,axis=1)*D
                lower.append(left//denominator)
                upper.append(-((-right)//denominator))
                th.append(H)
            saved.append((A,B,denominator))
        lo.append(lower);hi.append(upper);thresholds.append(th);arc_data.append(saved)
    L=np.asarray(lo);U=np.asarray(hi);H=np.asarray(thresholds,dtype=np.int64)
    del arr,xm,xr,ym,yr
    angles=np.asarray([s[2] for s in g['states']],dtype=np.int64)
    valid=lookup>=0;p=np.maximum(lookup,0);rows=[]
    # Compute both endpoint owners in the same test. This avoids the producer's
    # directed graph plus blockwise transpose mechanism.
    for start in range(0,n,block):
        end=min(n,start+block);i=angles[start:end];q=p[start:end]
        yes=np.zeros((end-start,n),dtype=np.bool_)
        for a in range(6):
            span1=np.maximum(U[i[:,None],a,p[None,:]]-L[i,a,q][:,None],
                             U[i,a,q][:,None]-L[i[:,None],a,p[None,:]])
            yes |= 2*span1>=H[i[:,None],a,angles[None,:]]
            span2=np.maximum(U[angles,a,p][None,:]-L[angles[None,:],a,q[:,None]],
                             U[angles[None,:],a,q[:,None]]-L[angles,a,p][None,:])
            yes |= 2*span2>=H[angles[None,:],a,i[:,None]]
        yes &= valid[None,:]&valid[start:end,None]
        packed=np.packbits(yes,axis=1,bitorder='little')
        for off,row in enumerate(packed):rows.append(int.from_bytes(row.tobytes(),'little') & g['adjacency'][start+off])
    return {**g,'adjacency':rows,'coupled_separator':{'scheme':'coupled-endpoint-tangent-v1','scale':D,
                                                    'arc_vertices':arc_data,'thresholds':thresholds}}

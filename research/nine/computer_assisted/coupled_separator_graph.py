"""Coupled continuous-angle necessary separator test.

For different frame arcs, minimize cos(delta)+abs(sin(delta)) at the
partner's endpoints BEFORE maximizing over the owning axis. Enclose the
owning unit-circle arc by its endpoint/tangent triangle, not a component box.
All comparisons are integer/rational, including coefficient correlations.
"""
from fractions import Fraction as F
from itertools import product
import numpy as np
D=2**20


def arc_vertices(k, i):
    # Three rational pairs (A/q,B/q): start, intersecting tangents, end.
    return [(k*k-i*i,2*k*i,k*k+i*i),
            (k*k-i*(i+1),k*(2*i+1),k*k+i*(i+1)),
            (k*k-(i+1)**2,2*k*(i+1),k*k+(i+1)**2)]


def refine(g, block=32):
    k=g['k'];scale=g['denominator'];n=len(g['states'])
    if k not in (12,24) or scale!=D:raise ValueError('unsupported scale/arcs')
    md=g['contraction'];polygons=md['polygons'];mapping=np.array(md['mapping'],dtype=np.int64)
    maxv=max(map(len,polygons))
    verts=np.array([list(p)+[p[-1]]*(maxv-len(p)) for p in polygons],dtype=np.int64)
    if np.max(np.abs(verts))>3*D:raise ValueError('vertex bound')
    lows=[];highs=[];bounds=[]
    ends=[(F(k*k-j*j,k*k+j*j),F(2*k*j,k*k+j*j)) for j in range(k+1)]
    coefficients=[]
    for i in range(k):
        ls=[];hs=[];bs=[];cs=[]
        for A,B,q in arc_vertices(k,i):
            if max(abs(A),abs(B))>q or q>2*k*k:raise ValueError('coefficient bound')
            threshold=[]
            for j in range(k):
                if j==i:
                    threshold.append(2*D*D);continue
                eps=1 if j>i else -1
                z=min(1+F(A,q)*(a+eps*b)+F(B,q)*(b-eps*a) for a,b in ends[j:j+2])
                threshold.append((z*D*D).numerator//(z*D*D).denominator)
            for X,Y in ((A,B),(-B,A)):
                lo=X*verts[:,:,0 if X>=0 else 1]+Y*verts[:,:,2 if Y>=0 else 3]
                hi=X*verts[:,:,1 if X>=0 else 0]+Y*verts[:,:,3 if Y>=0 else 2]
                # |num|<=6qD; num*D<=6(2k^2)D^2<2^63 for k<=24.
                ls.append(np.min(lo,axis=1)*D//q)
                hs.append(-((-np.max(hi,axis=1)*D)//q))
                bs.append(threshold);cs.append((X,Y,q))
        lows.append(ls);highs.append(hs);bounds.append(bs);coefficients.append(cs)
    low=np.asarray(lows);high=np.asarray(highs);threshold=np.asarray(bounds,dtype=np.int64)
    del verts
    angles=np.array([s[2] for s in g['states']],dtype=np.int64)
    safe=np.maximum(mapping,0);live=mapping>=0
    width=(n+7)//8
    directed=np.zeros((n,width),dtype=np.uint8)
    for i in range(k):
        selected=np.flatnonzero(live & (angles==i))
        L=low[i][:,safe];U=high[i][:,safe];H=threshold[i][:,angles]
        for begin in range(0,len(selected),block):
            ids=selected[begin:begin+block];p=safe[ids]
            possible=np.zeros((len(ids),n),dtype=np.bool_)
            for h in range(6):
                projection=np.maximum(U[h][None,:]-low[i,h,p,None],high[i,h,p,None]-L[h][None,:])
                possible |= 2*projection>=H[h][None,:]
            possible &= live[None,:]
            directed[ids]=np.packbits(possible,axis=1,bitorder='little')
    # Symmetrize the directed owner condition exactly, in byte-aligned blocks.
    # Either square can own the physical separating axis.
    size=512
    for a in range(0,n,size):
        ae=min(a+size,n)
        for b in range(a,n,size):
            be=min(b+size,n)
            ab=np.unpackbits(directed[a:ae,b//8:(be+7)//8],axis=1,bitorder='little')[:,:be-b]
            ba=np.unpackbits(directed[b:be,a//8:(ae+7)//8],axis=1,bitorder='little')[:,:ae-a]
            both=ab | ba.T
            directed[a:ae,b//8:(be+7)//8]=np.packbits(both,axis=1,bitorder='little')
            if a!=b:directed[b:be,a//8:(ae+7)//8]=np.packbits(both.T,axis=1,bitorder='little')
    rows=[int.from_bytes(directed[v].tobytes(),'little') & g['adjacency'][v] for v in range(n)]
    metadata={'scheme':'coupled-endpoint-tangent-v1','scale':D,'arc_vertices':[arc_vertices(k,i) for i in range(k)],
              'thresholds':bounds,'coefficients':coefficients}
    return {**g,'adjacency':rows,'coupled_separator':metadata}

#!/usr/bin/env python3
"""Second implementation of exact pose-cover geometry, independent of producer.

No producer import. The hex mesh uses horizontal elementary lattice triangles;
all scalar arithmetic is Python int/Fraction. NumPy only evaluates bounded
integer support tables and builds bitsets, with explicit overflow bounds.
"""
from fractions import Fraction
from itertools import product
import hashlib,json,time
from pathlib import Path
import numpy as np

SCALE=2**20
CELLS=tuple(sorted((q,r) for q,r in product(range(-3,4),repeat=2) if q*q+q*r+r*r<=4))
LOW3=Fraction(1732050807,10**9)
HIGH3=Fraction(1732050808,10**9)

def require(condition,message):
    if not condition:raise ValueError(message)

def floor(q):return q.numerator//q.denominator

def ceil(q):return -floor(-q)

def metric(p):return p[0]*p[0]+3*p[1]*p[1]

def minimum(t):
    cc=[t[i][0]*t[(i+1)%3][1]-t[i][1]*t[(i+1)%3][0] for i in range(3)]
    if min(cc)>=0 or max(cc)<=0:return Fraction(0)
    result=min(Fraction(metric(p)) for p in t)
    for i in range(3):
        x,y=t[i];X,Y=t[(i+1)%3];a,b=X-x,Y-y
        length=a*a+3*b*b;dot=x*a+3*y*b
        if -length<dot<0:result=min(result,Fraction(metric((x,y)))-Fraction(dot*dot,length))
    return result

def product_bounds(a,b):
    aa,bb=a;cc,dd=b
    return min(aa*cc,aa*dd,bb*cc,bb*dd),max(aa*cc,aa*dd,bb*cc,bb*dd)

def add_ranges(a,b):return a[0]+b[0],a[1]+b[1]

def neg_range(a):return -a[1],-a[0]

def amin(a):return max(0,a[0],-a[1])

def reconstruct(m=6,k=12):
    require(m in (6,8) and k==12,'unsupported certificate mesh')
    require(LOW3**2<3<HIGH3**2,'sqrt(3) enclosure')
    d=SCALE;ts=[];low_norm=[];verts=[]
    for c,(q,r) in enumerate(CELLS):
        local=set()
        def inside(x,y):return abs(y)<=m and abs(x+y)<=2*m and abs(x-y)<=2*m
        for y in range(-m,m+1):
            for x in range(-2*m,2*m+1):
                if (x-y)%2:continue
                for z in (-1,1):
                    tri=((x,y),(x+2,y),(x+1,y+z))
                    if all(inside(a,b) for a,b in tri):
                        local.add(tuple(sorted((a+3*q*m,b+(q+2*r)*m) for a,b in tri)))
        require(len(local)==6*m*m,'triangle mesh')
        for tri in sorted(local):
            norm=Fraction(2401,40000*m*m)*minimum(tri)
            if norm>Fraction(8281,3600):continue
            ts.append((c,tri));low_norm.append(floor(norm*d*d))
            vertices=[]
            for X,Y in tri:
                x=Fraction(49*X*d,200*m)
                a=Fraction(49*Y*d,200*m)*LOW3;b=Fraction(49*Y*d,200*m)*HIGH3
                vertices.append((floor(x),ceil(x),floor(min(a,b)),ceil(max(a,b))))
            verts.append(vertices)
    e=[(Fraction(k*k-i*i,k*k+i*i),Fraction(2*k*i,k*k+i*i)) for i in range(k+1)]
    ranges=[((floor(e[i+1][0]*d),ceil(e[i][0]*d)),(floor(e[i][1]*d),ceil(e[i+1][1]*d))) for i in range(k)]
    thresholds=[]
    for i in range(k):
        row=[]
        for j in range(k):
            a,b=e[i];A,B=e[i+1];c,f=e[j];C,F=e[j+1]
            values=[a*C+b*F+abs(a*F-b*C),A*c+B*f+abs(A*f-B*c)]
            if i<=j+1 and j<=i+1:values.append(Fraction(1))
            row.append(floor((1+min(values))*d*d))
        thresholds.append(row)
    states=[];boxes=[]
    for t,(cell,tri) in enumerate(ts):
        xx=(min(v[0] for v in verts[t]),max(v[1] for v in verts[t]))
        yy=(min(v[2] for v in verts[t]),max(v[3] for v in verts[t]))
        boxes.append((*xx,*yy))
        for o,(a,b) in enumerate(ranges):
            corners=[]
            for ss,tt in product((-1,1),repeat=2):
                aa=a if ss==1 else neg_range(a)
                bb=b if tt==1 else neg_range(b)
                X=add_ranges((2*xx[0],2*xx[1]),add_ranges(aa,neg_range(bb)))
                aa=a if tt==1 else neg_range(a)
                bb=b if ss==1 else neg_range(b)
                Y=add_ranges((2*yy[0],2*yy[1]),add_ranges(aa,bb))
                corners.append(64*(amin(X)**2+amin(Y)**2)<=1105*d*d)
            if not all(corners):continue
            U=add_ranges(product_bounds(a,xx),product_bounds(b,yy))
            V=add_ranges(product_bounds(neg_range(b),xx),product_bounds(a,yy))
            if 256*(low_norm[t]+amin(U)+amin(V))+128*d*d>1105*d*d:continue
            states.append((cell,t,o))
    vertex=np.asarray(verts,dtype=np.int64)
    require(int(np.max(np.abs(vertex)))<=3*d,'coordinate int64 bound')
    low=[];high=[]
    # Independently use interval midpoints and radii for each directed projection.
    # 2*d.x = coefficient*(low+high) +/- |coefficient|*(high-low).
    xm=vertex[:,:,0]+vertex[:,:,1];xr=vertex[:,:,1]-vertex[:,:,0]
    ym=vertex[:,:,2]+vertex[:,:,3];yr=vertex[:,:,3]-vertex[:,:,2]
    for a,b in ranges:
        lowers=[];uppers=[]
        for A,B in product(a,b):
            for X,Y in ((A,B),(-B,A)):
                mid=X*xm+Y*ym;rad=abs(X)*xr+abs(Y)*yr
                require(not np.any((mid-rad)%2) and not np.any((mid+rad)%2),'projection parity')
                lowers.append(np.min((mid-rad)//2,axis=1));uppers.append(np.max((mid+rad)//2,axis=1))
        low.append(lowers);high.append(uppers)
    low=np.asarray(low);high=np.asarray(high)
    centers=np.asarray([v for c,v in ts],dtype=np.int64)
    n=len(ts);far=np.zeros((n,n),dtype=np.int64)
    for a in range(3):
        for b in range(3):
            dx=centers[:,a,0,None]-centers[None,:,b,0]
            dy=centers[:,a,1,None]-centers[None,:,b,1]
            far=np.maximum(far,dx*dx+3*dy*dy)
    possible=far*2401>=40000*m*m
    states_array=np.asarray(states,dtype=np.int64);cells,pos,angles=states_array.T
    width=(len(states)+7)//8
    threshold=np.asarray(thresholds,dtype=np.int64)
    rows=[0]*len(states)
    groups=[0]*19
    for v,(c,t,o) in enumerate(states):groups[c]|=1<<v
    # Sweep positions in reverse order; row predicate formed as an OR of
    # the two owners' necessary separator conditions.
    by_position=[[] for _ in ts]
    for v,(c,t,o) in enumerate(states):by_position[t].append(v)
    for t in range(n-1,-1,-1):
        first=np.max(high-low[:,:,t,None],axis=1)
        second=np.max(high[:,:,t,None]-low,axis=1)
        for v in by_position[t]:
            o=angles[v];b=threshold[o,angles]
            owner1=(2*first[o,pos]>=b)|(2*second[o,pos]>=b)
            owner2=(2*first[angles,pos]>=b)|(2*second[angles,pos]>=b)
            compatible=possible[t,pos]&(cells!=cells[v])&(owner1|owner2)
            rows[v]=int.from_bytes(np.packbits(compatible,bitorder='little').tobytes(),'little')
    return dict(m=m,k=k,denominator=d,triangles=ts,box=boxes,norm=low_norm,
                axes=[(*a,*b) for a,b in ranges],lower=thresholds,states=states,groups=groups,adjacency=rows)

def graph_hash(rows):
    size=(len(rows)+7)//8;h=hashlib.sha256()
    for row in rows:h.update(row.to_bytes(size,'little'))
    return h.hexdigest()


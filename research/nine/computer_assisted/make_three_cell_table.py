#!/usr/bin/env python3
"""Produce a small rational/dual table proving the three-cell obstruction.

No fine position mesh, graph, solver, NumPy or floating arithmetic is used.
Every possible square orientation is covered by one of ten closed rational arcs.
The separate verifier reconstructs polygons by line intersections instead of clipping.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import gcd,isqrt,lcm
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
K=10;D=1000
NORMALS=((-2,-1),(-1,-2),(-1,0),(1,-3))
CELLS={0:(-2,0),3:(-1,-1),7:(0,-2)}
HEX=((2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1))
DIRECTIONS=((-1,0),(-1,1),(-1,1),(-1,1),(-5,4),(-3,2),(-2,1),(-2,1),(-2,1),(-1,0))


def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
def ceilroot(x):
    n=isqrt(x.numerator//x.denominator);return n+int(F(n*n)<x)
def endpoint(i):return F(K*K-i*i,K*K+i*i),F(2*K*i,K*K+i*i)
def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(pts):
    pts=sorted(set(pts))
    if len(pts)<2:return pts
    lo=[];hi=[]
    for p in pts:
        while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0:lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0:hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]
def clip(poly,n,b):
    if not poly:return []
    a,c=n;out=[];p=poly[-1];dp=b-a*p[0]-c*p[1]
    for q in poly:
        dq=b-a*q[0]-c*q[1]
        if (dp>=0)!=(dq>=0):
            t=F(dp,dp-dq);out.append((p[0]+t*(q[0]-p[0]),p[1]+t*(q[1]-p[1])))
        if dq>=0:out.append(q)
        p,dp=q,dq
    return list(dict.fromkeys(out))
def primitive(a,b,c):
    g=gcd(abs(a),abs(b));return a//g,b//g,F(c,g)


def support_table():
    out=[]
    for i in range(K):
        row=[]
        for x,y in NORMALS:
            ell=x*x+y*y;candidates=[]
            for a,b in (endpoint(i),endpoint(i+1)):
                A,B=abs(x*a+y*b),abs(-x*b+y*a);A,B=max(A,B),min(A,B)
                if 1105*B*B<=64*ell:
                    z=ceilroot(F(1041,256)*A*A*D*D)-floor(A*D/2)
                else:z=ceilroot(F(1105,256)*ell*D*D)-floor((A+B)*D/2)
                candidates.append(z)
            X,Y=x,y
            while X<0 or Y<0:X,Y=-Y,X
            a,b=endpoint(i);A,B=endpoint(i+1)
            if a*Y-b*X>=0 and X*B-Y*A>=0:
                candidates.append(ceilroot(F(1041,256)*ell*D*D)-isqrt(ell*D*D//4))
            row.append(max(candidates))
        out.append(row)
    return out


def cell_domain(c,i,rhs):
    q,r=CELLS[c];pts=[]
    for x,y in HEX:
        X=F(49*(3*q+x)*D,200)
        yy=[F(49*(q+2*r+y)*D,200)*z for z in (F(433,250),F(1733,1000))]
        pts.extend(product((floor(X),ceil(X)),(floor(min(yy)),ceil(max(yy)))))
    poly=hull(pts);lines=[]
    for p,z in zip(poly,poly[1:]+poly[:1]):
        a,b=z[1]-p[1],p[0]-z[0]
        lines.append(primitive(a,b,a*p[0]+b*p[1]))
    lines.extend((a,b,F(v)) for (a,b),v in zip(NORMALS,rhs[i]))
    lines=sorted(set(lines))
    for a,b,v in lines:poly=clip(poly,(a,b),v)
    return poly,lines


def arc(i):
    return ((K*K-i*i,2*K*i,K*K+i*i),
            (K*K-i*(i+1),K*(2*i+1),K*K+i*(i+1)),
            (K*K-(i+1)**2,2*K*(i+1),K*K+(i+1)**2))
def lower_width(i,j,a,b,q):
    if i==j:return F(2)
    eps=1 if i<j else -1
    return min(1+F(a,q)*(x+eps*y)+F(b,q)*(y-eps*x) for x,y in (endpoint(j),endpoint(j+1)))


def alternatives(i,neighbor,domains):
    grouped={}
    for j in range(K):
        P=domains[neighbor,j][0]
        if not P:raise ValueError('unexpected empty neighbor domain; requires explicit proof')
        for own,other in ((i,j),(j,i)):
            for a,b,q in arc(own):
                h=lower_width(own,other,a,b,q)
                for x,y in ((a,b),(-b,a)):
                    for sign in (-1,1):
                        X,Y=sign*x,sign*y
                        v=q*D*h/2+min(X*p+Y*t for p,t in P)
                        X,Y,v=primitive(X,Y,v)
                        grouped[X,Y]=min(v,grouped.get((X,Y),v))
    return [(x,y,v) for (x,y),v in sorted(grouped.items())]


def dual(lines,objective,target,strict=False):
    ex,ey=objective
    candidates=[]
    for i,(a,b,c) in enumerate(lines):
        den=a if a else b;num=ex if a else ey
        lam=F(num,den)
        if lam>=0 and lam*a==ex and lam*b==ey:
            candidates.append((lam*c,[[i,str(lam)]]))
    for (i,(a,b,c)),(j,(u,v,w)) in combinations(enumerate(lines),2):
        det=a*v-b*u
        if not det:continue
        L=F(ex*v-ey*u,det);M=F(a*ey-b*ex,det)
        if L>=0 and M>=0:candidates.append((L*c+M*w,[[i,str(L)],[j,str(M)]]))
    feasible=[z for z in candidates if (z[0]<target if strict else z[0]<=target)]
    if not feasible:raise ValueError('no two-line rational dual found')
    val,weights=min(feasible,key=lambda z:(z[0],len(z[1]),z[1]))
    return {'terms':weights,'weighted_bound':str(val)}


def generate(directory=HERE):
    rhs=support_table();domains={(c,i):cell_domain(c,i,rhs) for c in CELLS for i in range(K)}
    rows=[]
    for i,e in enumerate(DIRECTIONS):
        C,lines=domains[3,i];parts={};extremes={}
        for neighbor in (0,7):
            aa=alternatives(i,neighbor,domains)
            reachable=[]
            for x,y,b in aa:
                P=clip(C,(-x,-y),-b)
                if P:reachable.extend(P)
            if not reachable:raise ValueError('empty disjunction needs its own source proof')
            extremes[neighbor]=max(e[0]*x+e[1]*y for x,y in reachable) if neighbor==0 else min(e[0]*x+e[1]*y for x,y in reachable)
            parts[neighbor]=aa
        U,L=ceil(extremes[0]),floor(extremes[7])
        if not U<L:raise ValueError('rounded ten-row contradiction failed')
        record={'arc':i,'direction':list(e),'upper_left':U,'lower_right':L,
                'exact_upper_left':str(extremes[0]),'exact_lower_right':str(extremes[7]),'branches':{}}
        for neighbor in (0,7):
            proof=[]
            for x,y,b in parts[neighbor]:
                if max(x*X+y*Y for X,Y in C)<b:
                    row={'normal':[x,y],'rhs':str(b),'kind':'impossible',
                         'dual':dual(lines,(x,y),b,True)}
                else:
                    obj=e if neighbor==0 else (-e[0],-e[1]);target=U if neighbor==0 else -L
                    row={'normal':[x,y],'rhs':str(b),'kind':'bound',
                         'dual':dual(lines+[(-x,-y,-b)],obj,F(target))}
                proof.append(row)
            record['branches'][str(neighbor)]=proof
        rows.append(record)
    def serialized_lines(lines):return [[a,b,str(c)] for a,b,c in lines]
    cert={'schema':'n9_three_cell_rational_table_v1','target_q':'1105/256','scope':'q<=Q',
          'cells':[0,3,7],'scale':D,'angle_intervals':K,'normals':[list(n) for n in NORMALS],
          'sqrt3_enclosure':['433/250','1733/1000'],'support_bounds':rhs,
          'domains':[{'cell':c,'arc':i,'lines':serialized_lines(domains[c,i][1]),
                      'vertices':[[str(x),str(y)] for x,y in sorted(domains[c,i][0])]} for c in CELLS for i in range(K)],
          'rows':rows,'global_lower_bound_proved':False}
    raw=(json.dumps(cert,sort_keys=True,separators=(',',':'))+'\n').encode()
    (Path(directory)/'three_cell_rational_table.json').write_bytes(raw)
    summary={'result':'GENERATED_REQUIRES_INDEPENDENT_CHECK','certificate_sha256':hashlib.sha256(raw).hexdigest(),
             'rows':[{key:r[key] for key in ('arc','direction','upper_left','lower_right')} for r in rows],
             'dual_rows':sum(len(z) for r in rows for z in r['branches'].values()),
             'global_lower_bound_proved':False}
    print(json.dumps(summary,indent=2));return summary

if __name__=='__main__':generate()

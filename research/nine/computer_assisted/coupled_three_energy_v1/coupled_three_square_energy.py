"""Exact coupled-difference upper planes for the accepted 7/2 energy theorem.

For i<j<k, u=c_j-c_i, v=c_k-c_j, and u+v=c_k-c_i.
Each scalar coordinate lies in a closed polygon defined by the three
independently certified difference intervals. The convex polynomial
u²+v²+(u+v)² is bounded above by any affine plane that dominates its values
at every polygon vertex. No new geometric assumption or case split is used.
"""
from fractions import Fraction as F
from itertools import combinations,product
from functools import lru_cache

def energy(u,v):return u*u+v*v+(u+v)*(u+v)

@lru_cache(maxsize=20000)
def polygon_vertices(U,V,W):
    """Intersect all pairs of the six rational boundary lines."""
    a,b=U;c,d=V;e,f=W
    assert a<=b and c<=d and e<=f
    lines=((F(1),F(0),a),(F(1),F(0),b),(F(0),F(1),c),
           (F(0),F(1),d),(F(1),F(1),e),(F(1),F(1),f))
    vertices=set()
    for (p,q,r),(s,t,w)in combinations(lines,2):
        determinant=p*t-q*s
        if not determinant:continue
        u=(r*t-q*w)/determinant;v=(p*w-r*s)/determinant
        if a<=u<=b and c<=v<=d and e<=u+v<=f:vertices.add((u,v))
    return tuple(sorted(vertices))

def plane_on_three(p,q,r):
    x,y=p;u,v=q;a,b=r
    determinant=(u-x)*(b-y)-(a-x)*(v-y)
    if not determinant:return None
    p0,q0,r0=energy(*p),energy(*q),energy(*r)
    A=((q0-p0)*(b-y)-(r0-p0)*(v-y))/determinant
    B=((u-x)*(r0-p0)-(a-x)*(q0-p0))/determinant
    return A,B,p0-A*x-B*y

@lru_cache(maxsize=20000)
def upper_planes(U,V,W):
    vertices=polygon_vertices(U,V,W)
    if not vertices:return (),vertices
    planes=set()
    for p,q,r in combinations(vertices,3):
        plane=plane_on_three(p,q,r)
        if plane is None:continue
        A,B,C=plane
        if all(A*u+B*v+C>=energy(u,v)for u,v in vertices):planes.add(plane)
    if not planes:
        # A degenerate polygon is a point or segment. A scalar secant along
        # any nonconstant coordinate, lifted constantly in the other, suffices.
        assert all((q[0]-p[0])*(r[1]-p[1])==(r[0]-p[0])*(q[1]-p[1])
                   for p,q,r in combinations(vertices,3)), 'Missing upper hull plane on a two-dimensional polygon.'
        if len(vertices)==1:
            planes.add((F(0),F(0),energy(*vertices[0])))
        else:
            p,q=vertices[0],vertices[-1]
            if p[0]!=q[0]:
                A=(energy(*q)-energy(*p))/(q[0]-p[0]);plane=A,F(0),energy(*p)-A*p[0]
            else:
                B=(energy(*q)-energy(*p))/(q[1]-p[1]);plane=F(0),B,energy(*p)-B*p[1]
            assert all(plane[0]*u+plane[1]*v+plane[2]>=energy(u,v)for u,v in vertices)
            planes.add(plane)
    return tuple(sorted(planes)),vertices

def projected_interval(ds,direction,diagonal=None):
    p,q=direction
    xs=[p*x+q*y for x,y in product(*ds)]
    lo,hi=min(xs),max(xs)
    if diagonal is not None:
        values=[(p+q)*u/2+(p-q)*v/2 for u,v in product(*diagonal)]
        lo=max(lo,min(values));hi=min(hi,max(values))
    return lo,hi

def rows(differences,diagonal=None,directions=((F(1),F(0)),(F(1),F(1)))):
    diagonal=diagonal or{}
    result=[];guards=[]
    for dn,e in enumerate(directions):
        e=tuple(map(F,e));f=(-e[1],e[0]);norm=e[0]*e[0]+e[1]*e[1]
        assert norm>0
        for i,j,k in combinations(range(9),3):
            pairs=((i,j),(j,k),(i,k));data=[]
            for axis,direction in enumerate((e,f)):
                intervals=tuple(projected_interval(differences[p],direction,diagonal.get(p))for p in pairs)
                if any(a>b for a,b in intervals):
                    result.append(((),F(-1),f'coupled_three_empty_projection_{i}_{j}_{k}_{dn}_{axis}'))
                    data.append(((),(),intervals));continue
                planes,vertices=upper_planes(*intervals)
                if not vertices:
                    result.append(((),F(-1),f'coupled_three_empty_{i}_{j}_{k}_{dn}_{axis}'))
                data.append((planes,vertices,intervals))
            for ai,pa in enumerate(data[0][0]):
                for bi,pb in enumerate(data[1][0]):
                    co={};constant=pa[2]+pb[2]
                    for plane,direction in ((pa,e),(pb,f)):
                        a,b,c=plane
                        for original,mul in((i,a),(j,b-a),(k,-b)):
                            for ax,v in enumerate(direction):
                                key=2*original+ax;co[key]=co.get(key,F(0))+mul*v
                    name=f'coupled_three_energy_{i}_{j}_{k}_{dn}_{ai}_{bi}'
                    result.append((tuple((v,c)for v,c in sorted(co.items())if c),constant-F(7,2)*norm,name))
            guards.append(dict(triple=[i,j,k],direction=list(map(str,e)),norm_squared=str(norm),
                planes=[[[str(v)for v in p]for p in item[0]]for item in data],
                vertices=[[[str(v)for v in p]for p in item[1]]for item in data],
                intervals=[[[str(v)for v in p]for p in item[2]]for item in data]))
    return result,guards

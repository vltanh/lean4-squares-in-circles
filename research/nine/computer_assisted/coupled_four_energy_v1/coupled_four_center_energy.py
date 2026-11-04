"""Exact coupled-difference upper planes for four planar original centers.

Retains all six independently proved difference intervals.  Convexity
extends an affine majorant checked at EVERY exact polytope vertex to the
whole closed polytope.  Floating hulls propose planes only; they never
supply proof coefficients or establish validity.  The accepted universal
four-center energy lower bound is 8 for pairwise unit-separated centers.
"""
import os
for _k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_k]='1'
from fractions import Fraction as F
from itertools import combinations,product
from functools import lru_cache

PAIRS=((0,1),(0,2),(0,3),(1,2),(1,3),(2,3))
NORMALS=((1,0,0),(0,1,0),(0,0,1),(-1,1,0),(-1,0,1),(0,-1,1))

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def energy(u):return sum(dot(n,u)**2 for n in NORMALS)
def det3(a,b,c):
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def inverse3(a,b,c):
    d=det3(a,b,c)
    if not d:return None
    # The difference-constraint matrices are totally unimodular; assert it.
    assert abs(d)==1
    return (( (b[1]*c[2]-b[2]*c[1])//d,(a[2]*c[1]-a[1]*c[2])//d,(a[1]*b[2]-a[2]*b[1])//d),
            ( (b[2]*c[0]-b[0]*c[2])//d,(a[0]*c[2]-a[2]*c[0])//d,(a[2]*b[0]-a[0]*b[2])//d),
            ( (b[0]*c[1]-b[1]*c[0])//d,(a[1]*c[0]-a[0]*c[1])//d,(a[0]*b[1]-a[1]*b[0])//d))

# Twelve boundary planes, including both faces of zero-width intervals.
LINE_NORMALS=tuple(n for n in NORMALS for _ in range(2))
BASIS_TRIPLES=tuple((ids,inv) for ids in combinations(range(12),3)
    if (inv:=inverse3(*(LINE_NORMALS[i]for i in ids))) is not None)

@lru_cache(maxsize=20000)
def polytope_vertices(intervals):
    intervals=tuple(tuple(map(F,x))for x in intervals)
    assert len(intervals)==6 and all(a<=b for a,b in intervals)
    rhs=tuple(x for ab in intervals for x in ab)
    vertices=set()
    for ids,inv in BASIS_TRIPLES:
        r=tuple(rhs[i]for i in ids)
        u=tuple(dot(row,r)for row in inv)
        if all(a<=dot(n,u)<=b for n,(a,b)in zip(NORMALS,intervals)):vertices.add(u)
    return tuple(sorted(vertices))

def rank_pivots(rows):
    """Exact rational row reduction; return spatial pivot coordinates."""
    rows=[list(map(F,row))for row in rows];pivots=[];k=0
    for j in range(3):
        p=next((i for i in range(k,len(rows))if rows[i][j]),None)
        if p is None:continue
        rows[k],rows[p]=rows[p],rows[k];d=rows[k][j]
        rows[k]=[v/d for v in rows[k]]
        for i in range(len(rows)):
            if i!=k and rows[i][j]:
                d=rows[i][j];rows[i]=[v-d*w for v,w in zip(rows[i],rows[k])]
        pivots.append(j);k+=1
        if k==len(rows):break
    return tuple(pivots)

def solve_square(matrix,rhs):
    n=len(matrix);a=[list(map(F,row))+[F(v)]for row,v in zip(matrix,rhs)]
    for j in range(n):
        p=next((i for i in range(j,n)if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];d=a[j][j];a[j]=[v/d for v in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                d=a[i][j];a[i]=[v-d*w for v,w in zip(a[i],a[j])]
    return tuple(row[-1]for row in a)

def secant_plane(intervals):
    co=[F(0)]*3;constant=F(0)
    for n,(a,b)in zip(NORMALS,intervals):
        for j in range(3):co[j]+=(a+b)*n[j]
        constant-=a*b
    return tuple(co+[constant])

def plane_at(indices,vertices,pivots):
    p=solve_square([tuple(vertices[i][j]for j in pivots)+(F(1),)for i in indices],
                   [energy(vertices[i])for i in indices])
    if p is None:return None
    co=[F(0)]*3
    for j,v in zip(pivots,p[:-1]):co[j]=v
    return tuple(co+[p[-1]])

def dominates(plane,vertices):
    return all(dot(plane[:3],u)+plane[3]>=energy(u)for u in vertices)

@lru_cache(maxsize=20000)
def upper_planes(intervals):
    intervals=tuple(tuple(map(F,x))for x in intervals)
    vertices=polytope_vertices(intervals)
    if not vertices:return (),vertices
    # These fallback planes are certified identically and need no floating hull.
    planes={secant_plane(intervals),(F(0),F(0),F(0),max(map(energy,vertices)))}
    origin=vertices[0];pivots=rank_pivots([tuple(a-b for a,b in zip(v,origin))for v in vertices[1:]])
    dim=len(pivots)
    if dim==0:return ((F(0),F(0),F(0),energy(origin)),),vertices
    candidates=set()
    if len(vertices)==dim+1:candidates.add(tuple(range(len(vertices))))
    else:
        # Normalize spatial coordinates and subtract the quadratic's tangent.
        # Qhull only nominates facet vertex indices. Exact arithmetic follows.
        try:
            import numpy as np
            from scipy.spatial import ConvexHull
            center=tuple(sum(v[j]for v in vertices)/len(vertices)for j in range(3))
            spatial=[[float(v[j]-center[j])for j in pivots]for v in vertices]
            heights=[float(energy(tuple(v[j]-center[j]for j in range(3))))for v in vertices]
            points=np.c_[np.asarray(spatial),np.asarray(heights)]
            scale=np.max(np.abs(points),axis=0);scale[scale==0]=1
            hull=ConvexHull(points/scale)
            for face,equation in zip(hull.simplices,hull.equations):
                if equation[-2]>0:candidates.add(tuple(sorted(map(int,face))))
        except Exception:
            # Lower-dimensional lifted sets can still have a unique majorant.
            # Exact enumeration is small for simplex / segment degeneracies.
            if len(vertices)<=12:candidates.update(combinations(range(len(vertices)),dim+1))
    for ids in sorted(candidates):
        plane=plane_at(ids,vertices,pivots)
        if plane is not None and dominates(plane,vertices):planes.add(plane)
    assert all(dominates(p,vertices)for p in planes)
    return tuple(sorted(planes)),vertices

def projected_interval(ds,direction):
    p,q=direction;values=[p*x+q*y for x,y in product(*ds)]
    return min(values),max(values)

def correlated_projected_interval(ds,direction,pair,diagonal=None):
    lo,hi=projected_interval(ds,direction)
    if diagonal and pair in diagonal:
        p,q=direction
        idx=0 if p==q else (1 if p==-q else None)
        if idx is not None and p:
            a,b=diagonal[pair][idx]
            a,b=(p*a,p*b)if p>0 else(p*b,p*a)
            lo,hi=max(lo,a),min(hi,b)
    return lo,hi

def rows(differences,directions=((F(1),F(0)),),original_count=9,quads=None,diagonal=None):
    result=[];guards=[]
    if quads is not None:quads=tuple(map(tuple,quads))
    for dn,e in enumerate(directions):
        e=tuple(map(F,e));f=(-e[1],e[0]);norm=dot(e,e)
        assert norm>0
        for originals in (combinations(range(original_count),4)if quads is None else quads):
            originals=tuple(originals);a,b,c,d=originals
            assert originals==tuple(sorted(set(originals)))
            pairs=tuple((originals[i],originals[j])for i,j in PAIRS);data=[]
            for axis,direction in enumerate((e,f)):
                intervals=tuple(correlated_projected_interval(differences[p],direction,p,diagonal)for p in pairs)
                planes,vertices=upper_planes(intervals)
                if not vertices:
                    result.append(((),F(-1),f'coupled_four_empty_{a}_{b}_{c}_{d}_{dn}_{axis}'))
                data.append((planes,vertices,intervals))
            for ai,pa in enumerate(data[0][0]):
                for bi,pb in enumerate(data[1][0]):
                    co={};constant=pa[3]+pb[3]
                    for plane,direction in ((pa,e),(pb,f)):
                        weights=(sum(plane[:3]),-plane[0],-plane[1],-plane[2])
                        for original,mul in zip(originals,weights):
                            for ax,v in enumerate(direction):
                                key=2*original+ax;co[key]=co.get(key,F(0))+mul*v
                    name=f'coupled_four_energy_{a}_{b}_{c}_{d}_{dn}_{ai}_{bi}'
                    result.append((tuple((v,c)for v,c in sorted(co.items())if c),constant-8*norm,name))
            guards.append(dict(quad=list(originals),direction=list(map(str,e)),norm_squared=str(norm),
                planes=[[[str(v)for v in p]for p in item[0]]for item in data],
                vertices=[[[str(v)for v in p]for p in item[1]]for item in data],
                intervals=[[[str(v)for v in p]for p in item[2]]for item in data]))
    return result,guards

def lifted_rows(differences,first_aux,directions=((F(1),F(0)),),original_count=9,quads=None,diagonal=None):
    """Equivalent compact extension: one exact projected-energy auxiliary.

    Return (rows, absolute_auxiliary_bounds, guards).  Physical meaning of
    z for each quad is sum_{i<j}(e dot (c_j-c_i))**2.  All z bounds and
    both families are consequences, with no split and no chosen plane.
    """
    result=[];absolute=[];guards=[]
    if quads is not None:quads=tuple(map(tuple,quads))
    for dn,e in enumerate(directions):
        e=tuple(map(F,e));f=(-e[1],e[0]);norm=dot(e,e)
        assert norm>0
        for originals in (combinations(range(original_count),4)if quads is None else quads):
            originals=tuple(originals);a,b,c,d=originals
            assert originals==tuple(sorted(set(originals)))
            pairs=tuple((originals[i],originals[j])for i,j in PAIRS);data=[]
            for axis,direction in enumerate((e,f)):
                intervals=tuple(correlated_projected_interval(differences[p],direction,p,diagonal)for p in pairs)
                planes,vertices=upper_planes(intervals)
                if not vertices:result.append(((),F(-1),f'coupled_four_empty_{a}_{b}_{c}_{d}_{dn}_{axis}'))
                data.append((planes,vertices,intervals))
            aux=first_aux+len(absolute)
            maximum=max(map(energy,data[0][1]),default=F(0));absolute.append(maximum)
            result.append((((aux,F(-1)),),F(0),f'coupled_four_aux_nonnegative_{a}_{b}_{c}_{d}_{dn}'))
            result.append((((aux,F(1)),),maximum,f'coupled_four_aux_upper_{a}_{b}_{c}_{d}_{dn}'))
            for axis,(item,direction)in enumerate(zip(data,(e,f))):
                for pi,plane in enumerate(item[0]):
                    co={aux:F(1)if axis==0 else F(-1)}
                    weights=(sum(plane[:3]),-plane[0],-plane[1],-plane[2])
                    for original,mul in zip(originals,weights):
                        for ax,v in enumerate(direction):
                            key=2*original+ax;co[key]=co.get(key,F(0))+mul*v
                    rhs=plane[3]-(8*norm if axis else 0)
                    name=f'coupled_four_lifted_{a}_{b}_{c}_{d}_{dn}_{axis}_{pi}'
                    result.append((tuple((v,c)for v,c in sorted(co.items())if c),rhs,name))
            guards.append(dict(quad=list(originals),direction=list(map(str,e)),norm_squared=str(norm),
                auxiliary=aux,auxiliary_maximum=str(maximum),
                planes=[[[str(v)for v in p]for p in item[0]]for item in data],
                vertices=[[[str(v)for v in p]for p in item[1]]for item in data],
                intervals=[[[str(v)for v in p]for p in item[2]]for item in data]))
    return result,absolute,guards

if __name__=='__main__':
    import json
    # A strict gain over independent secants on a correlated domain.
    intervals=tuple((F(a),F(b))for a,b in ((0,1),(0,1),(0,1),(0,1),(0,1),(0,1)))
    planes,vertices=upper_planes(intervals)
    print(json.dumps({'vertices':[[str(x)for x in v]for v in vertices],
        'planes':[[str(x)for x in p]for p in planes]},indent=2))

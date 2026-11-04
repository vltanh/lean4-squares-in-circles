"""Independent checker for coupled-difference energy row definitions.

The producer uses all boundary-line intersections. This checker clips a
closed rectangle by the two sum halfplanes, then solves 3x3 systems with
rational Gaussian elimination. It imports no producer and no optimizer.
"""
from fractions import Fraction as Q
from itertools import combinations,product
from functools import lru_cache

DEFAULT_DIRECTIONS=((Q(1),Q(0)),(Q(1),Q(1)))

def quadratic(p):
    x,y=p
    return 2*x*x+2*x*y+2*y*y

def clip(vertices,a,b,c):
    if not vertices:return ()
    result=[]
    for p,q in zip(vertices,vertices[1:]+vertices[:1]):
        fp=a*p[0]+b*p[1]-c;fq=a*q[0]+b*q[1]-c
        if fp<=0:result.append(p)
        if fp*fq<0:
            t=fp/(fp-fq)
            result.append((p[0]+t*(q[0]-p[0]),p[1]+t*(q[1]-p[1])))
    # Repeated corners arise naturally for closed segment/point rectangles.
    out=[]
    for p in result:
        if p not in out:out.append(p)
    return tuple(out)

@lru_cache(maxsize=20000)
def vertices(U,V,W):
    l,u=U;a,b=V;c,d=W
    assert l<=u and a<=b and c<=d
    polygon=tuple(dict.fromkeys(((l,a),(u,a),(u,b),(l,b))))
    polygon=clip(polygon,Q(1),Q(1),d)
    polygon=clip(polygon,Q(-1),Q(-1),-c)
    assert all(l<=x<=u and a<=y<=b and c<=x+y<=d for x,y in polygon)
    return tuple(sorted(polygon))

def solve_plane(points):
    matrix=[[Q(x),Q(y),Q(1),quadratic((x,y))]for x,y in points]
    for col in range(3):
        pivot=next((i for i in range(col,3)if matrix[i][col]),None)
        if pivot is None:return None
        matrix[col],matrix[pivot]=matrix[pivot],matrix[col]
        d=matrix[col][col];matrix[col]=[x/d for x in matrix[col]]
        for i in range(3):
            if i==col:continue
            d=matrix[i][col];matrix[i]=[x-d*y for x,y in zip(matrix[i],matrix[col])]
    return tuple(matrix[i][3]for i in range(3))

@lru_cache(maxsize=20000)
def planes(U,V,W):
    polygon=vertices(U,V,W)
    if not polygon:return ()
    answer=set()
    for points in combinations(polygon,3):
        p=solve_plane(points)
        if p is not None and all(p[0]*x+p[1]*y+p[2]>=quadratic((x,y))for x,y in polygon):answer.add(p)
    if not answer:
        assert all((q[0]-p[0])*(r[1]-p[1])==(r[0]-p[0])*(q[1]-p[1])
                   for p,q,r in combinations(polygon,3))
        if len(polygon)==1:answer.add((Q(0),Q(0),quadratic(polygon[0])))
        else:
            first,last=polygon[0],polygon[-1]
            if first[0]!=last[0]:
                a=(quadratic(last)-quadratic(first))/(last[0]-first[0]);p=a,Q(0),quadratic(first)-a*first[0]
            else:
                b=(quadratic(last)-quadratic(first))/(last[1]-first[1]);p=Q(0),b,quadratic(first)-b*first[1]
            assert all(p[0]*x+p[1]*y+p[2]>=quadratic((x,y))for x,y in polygon)
            answer.add(p)
    return tuple(sorted(answer))

def project(ds,direction,diagonal=None):
    def scale(v,b):
        vals=[v*x for x in b]
        return min(vals),max(vals)
    p,q=map(Q,direction);x,y=scale(p,ds[0]),scale(q,ds[1])
    lo,hi=x[0]+y[0],x[1]+y[1]
    if diagonal is not None:
        a,b=scale((p+q)/2,diagonal[0]),scale((p-q)/2,diagonal[1])
        lo,hi=max(lo,a[0]+b[0]),min(hi,a[1]+b[1])
    return lo,hi

def rebuild(name,differences,diagonal=None,directions=DEFAULT_DIRECTIONS):
    diagonal=diagonal or{}
    parts=name.split('_')
    assert parts[:2]==['coupled','three']
    mode=parts[2]
    if mode=='empty'and parts[3]=='projection':
        i,j,k,dn,axis=map(int,parts[4:]);assert 0<=i<j<k<9 and axis in(0,1)
        e=tuple(map(Q,directions[dn]));direction=e if axis==0 else(-e[1],e[0])
        ab=[project(differences[p],direction,diagonal.get(p))for p in((i,j),(j,k),(i,k))]
        assert any(a>b for a,b in ab)
        return (),Q(-1),name
    if mode=='empty':
        i,j,k,dn,axis=map(int,parts[3:]);assert 0<=i<j<k<9 and axis in(0,1)
        e=tuple(map(Q,directions[dn]));direction=e if axis==0 else(-e[1],e[0])
        ab=[project(differences[p],direction,diagonal.get(p))for p in((i,j),(j,k),(i,k))]
        assert not vertices(*ab)
        return (),Q(-1),name
    assert mode=='energy'and len(parts)==9
    i,j,k,dn,ai,bi=map(int,parts[3:]);assert 0<=i<j<k<9
    e=tuple(map(Q,directions[dn]));f=(-e[1],e[0]);n=e[0]*e[0]+e[1]*e[1];assert n>0
    coeff={};constant=Q(0)
    for direction,index in((e,ai),(f,bi)):
        ab=tuple(project(differences[p],direction,diagonal.get(p))for p in((i,j),(j,k),(i,k)))
        A,B,C=planes(*ab)[index];constant+=C
        # Affine energy upper bound is A*(c_j-c_i)+B*(c_k-c_j)+C.
        for axis,weight in enumerate(direction):
            for original,value in((i,A),(j,B-A),(k,-B)):
                column=2*original+axis;coeff[column]=coeff.get(column,Q(0))+weight*value
    return tuple((k,v)for k,v in sorted(coeff.items())if v),constant-Q(7,2)*n,name

def verify_literal(row,differences,diagonal=None,directions=DEFAULT_DIRECTIONS):
    """Verify any literal upper-plane row without trusting facet indices.

    Coefficients recover each projected plane's slopes. Its necessary
    intercept is recomputed as a maximum over independently clipped vertices.
    The requested rhs may be weaker but never stronger than those maxima.
    """
    diagonal=diagonal or{}
    terms,rhs,name=row;rhs=Q(rhs);parts=name.split('_')
    assert parts[:2]==['coupled','three']
    coefficients={}
    for column,value in terms:
        assert type(column)is int and 0<=column<18
        coefficients[column]=coefficients.get(column,Q(0))+Q(value)
    coefficients={k:v for k,v in coefficients.items()if v}
    if parts[2]=='empty':
        assert not coefficients and rhs<0
        offset=4 if parts[3]=='projection'else 3
        i,j,k,dn,axis=map(int,parts[offset:]);assert 0<=i<j<k<9 and axis in(0,1)
        e=tuple(map(Q,directions[dn]));direction=e if axis==0 else(-e[1],e[0])
        U,V,W=[project(differences[p],direction,diagonal.get(p))for p in((i,j),(j,k),(i,k))]
        if offset==4:assert any(a>b for a,b in(U,V,W))
        else:
            assert all(a<=b for a,b in(U,V,W))
            assert max(U[0]+V[0],W[0])>min(U[1]+V[1],W[1])
        return dict(status='PASS',kind='empty_exact_difference_domain')
    assert parts[2]=='energy'and len(parts)==9
    i,j,k,dn,unused_a,unused_b=map(int,parts[3:]);assert 0<=i<j<k<9
    assert set(coefficients)<=set(2*o+axis for o in(i,j,k)for axis in(0,1))
    ci=tuple(coefficients.get(2*i+axis,Q(0))for axis in(0,1))
    cj=tuple(coefficients.get(2*j+axis,Q(0))for axis in(0,1))
    ck=tuple(coefficients.get(2*k+axis,Q(0))for axis in(0,1))
    assert all(ci[axis]+cj[axis]+ck[axis]==0 for axis in(0,1))
    e=tuple(map(Q,directions[dn]));f=(-e[1],e[0]);n=e[0]*e[0]+e[1]*e[1];assert n>0
    intercepts=[]
    for d in(e,f):
        A=sum(ci[axis]*d[axis]for axis in(0,1))/n
        B=-sum(ck[axis]*d[axis]for axis in(0,1))/n
        ab=[project(differences[p],d,diagonal.get(p))for p in((i,j),(j,k),(i,k))]
        polygon=vertices(*ab)
        assert polygon,'Use an explicit empty-domain row for this case.'
        C=max(quadratic((u,v))-A*u-B*v for u,v in polygon)
        intercepts.append(C)
    required=sum(intercepts)-Q(7,2)*n
    assert rhs>=required,('unproved coupled-energy rhs',name,str(rhs),str(required))
    return dict(status='PASS',kind='coupled_energy_literal',minimum_rhs=str(required),
        intercepts=list(map(str,intercepts)),rhs_slack=str(rhs-required),facet_indices_trusted=False)

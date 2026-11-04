"""Independent exact rational verification of coupled four-center guards.

No imports from the discovery generator; no scipy or numerical hull is used.
The exhaustive vertices are rebuilt using generic Gaussian elimination,
not the generator's integer inverse matrices.
"""
from fractions import Fraction
from itertools import combinations
import json,sys,hashlib
F=Fraction
EDGE_NORMALS=((1,0,0),(0,1,0),(0,0,1),(-1,1,0),(-1,0,1),(0,-1,1))
def quadratic(v):
    q=(F(0),)+tuple(v)
    return sum((q[j]-q[i])**2 for i,j in combinations(range(4),2))
def intersection(equations):
    m=[[F(v)for v in row]for row in equations]
    for col in range(3):
        chosen=next((i for i in range(col,3)if m[i][col]),None)
        if chosen is None:return None
        m[col],m[chosen]=m[chosen],m[col]
        leading=m[col][col]
        for j in range(col,4):m[col][j]/=leading
        for i in range(3):
            if i==col:continue
            mult=m[i][col]
            for j in range(col,4):m[i][j]-=mult*m[col][j]
    return tuple(m[i][3]for i in range(3))
def vertices_from_intervals(intervals):
    assert len(intervals)==6
    assert all(a<=b for a,b in intervals)
    equations=tuple(tuple(n)+(bound,)for n,iv in zip(EDGE_NORMALS,intervals)for bound in iv)
    result=set()
    for triple in combinations(equations,3):
        v=intersection(triple)
        if v is None:continue
        if all(a<=sum(n[j]*v[j]for j in range(3))<=b for n,(a,b)in zip(EDGE_NORMALS,intervals)):result.add(v)
    return tuple(sorted(result))
def verify(guards):
    comparisons=0;vertices=0;plane_count=0;rows=0;empty=0
    for guard in guards:
        quad=guard['quad'];assert len(quad)==4 and quad==sorted(set(quad))
        e=tuple(map(F,guard['direction']));assert len(e)==2
        norm=sum(t*t for t in e);assert norm>0 and str(norm)==guard['norm_squared']
        counts=[]
        for axis in range(2):
            intervals=tuple(tuple(map(F,p))for p in guard['intervals'][axis])
            actual=vertices_from_intervals(intervals)
            recorded=tuple(tuple(map(F,v))for v in guard['vertices'][axis])
            assert actual==recorded,('vertex mismatch',quad,axis)
            planes=tuple(tuple(map(F,p))for p in guard['planes'][axis])
            vertices+=len(actual);plane_count+=len(planes);counts.append(len(planes))
            if not actual:
                assert not planes;empty+=1;continue
            assert planes
            for p in planes:
                assert len(p)==4
                for v in actual:
                    assert sum(p[j]*v[j]for j in range(3))+p[3]>=quadratic(v),('non-majorant',quad,axis,p,v)
                    comparisons+=1
        if 'auxiliary' in guard:
            assert isinstance(guard['auxiliary'],int) and guard['auxiliary']>=2*(max(quad)+1)
            expected=max((quadratic(tuple(map(F,v)))for v in guard['vertices'][0]),default=F(0))
            assert F(guard['auxiliary_maximum'])==expected
        rows+=counts[0]*counts[1]
    return dict(status='PASS',guard_count=len(guards),exact_vertices=vertices,exact_planes=plane_count,
                exact_majorant_comparisons=comparisons,converted_rows=rows,empty_polytopes=empty)
def reconstructed_rows(guards,lifted=False):
    """Reconstruct the exact original-coordinate rows from certified guards."""
    result=[];auxiliary_bounds=[]
    for guard in guards:
        quad=tuple(guard['quad']);a,b,c,d=quad
        e=tuple(map(F,guard['direction']));f=(-e[1],e[0]);n=sum(t*t for t in e)
        # Direction number is part of naming only; preserve first occurrence order.
        if 'direction_names' not in locals():direction_names={}
        if e not in direction_names:direction_names[e]=len(direction_names)
        dn=direction_names[e]
        for ax in range(2):
            if not guard['vertices'][ax]:result.append(((),F(-1),f'coupled_four_empty_{a}_{b}_{c}_{d}_{dn}_{ax}'))
        px=[tuple(map(F,p))for p in guard['planes'][0]]
        py=[tuple(map(F,p))for p in guard['planes'][1]]
        def original_coefficients(plane,axis):
            co={}
            for i in range(1,4):
                for k in range(2):
                    v=plane[i-1]*axis[k]
                    co[2*quad[0]+k]=co.get(2*quad[0]+k,F(0))+v
                    co[2*quad[i]+k]=co.get(2*quad[i]+k,F(0))-v
            return co
        def clean(co):return tuple((k,v)for k,v in sorted(co.items())if v)
        if not lifted:
            for i,p in enumerate(px):
                for j,q in enumerate(py):
                    co=original_coefficients(p,e)
                    for k,v in original_coefficients(q,f).items():co[k]=co.get(k,F(0))+v
                    result.append((clean(co),p[3]+q[3]-8*n,f'coupled_four_energy_{a}_{b}_{c}_{d}_{dn}_{i}_{j}'))
        else:
            aux=guard['auxiliary'];maximum=F(guard['auxiliary_maximum']);auxiliary_bounds.append(maximum)
            if len(auxiliary_bounds)>1:assert aux==guards[0]['auxiliary']+len(auxiliary_bounds)-1
            result.append((((aux,F(-1)),),F(0),f'coupled_four_aux_nonnegative_{a}_{b}_{c}_{d}_{dn}'))
            result.append((((aux,F(1)),),maximum,f'coupled_four_aux_upper_{a}_{b}_{c}_{d}_{dn}'))
            for ax,(planes,direction)in enumerate(((px,e),(py,f))):
                for pi,p in enumerate(planes):
                    co=original_coefficients(p,direction);co[aux]=F(1)if ax==0 else F(-1)
                    result.append((clean(co),p[3]-(8*n if ax else 0),f'coupled_four_lifted_{a}_{b}_{c}_{d}_{dn}_{ax}_{pi}'))
    return result,auxiliary_bounds

if __name__=='__main__':
    path=sys.argv[1];packet=json.load(open(path));guards=packet['guards']if isinstance(packet,dict)else packet
    result=verify(guards);result['input_sha256']=hashlib.sha256(open(path,'rb').read()).hexdigest()
    print(json.dumps(result,indent=2))

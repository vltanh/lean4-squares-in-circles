#!/usr/bin/env python3
"""Exact regressions for Gate 2 and Gate 3A; not a global proof certificate."""
from fractions import Fraction as Q
from itertools import combinations, product
from verify_ordered_rational_gate import (
    dot, add, sub, scale, frame, support, vertices, quarter_turn,
)

U = ((12,5),(5,12),(-5,12),(-12,5),(-12,-5),(-5,-12),(5,-12),(12,-5))


def octants(n):
    x,y=n
    tests=(x>=y>=0, y>=x>=0, y>=-x>=0, -x>=y>=0,
           -x>=-y>=0, -y>=-x>=0, -y>=x>=0, x>=-y>=0)
    result=[k for k,t in enumerate(tests) if t]
    assert result
    return result


def dual_data(frames, mu, edges):
    m=[sum(row,Q(0)) for row in mu]
    a=[]
    c=[(Q(0),Q(0)) for _ in frames]
    edge_sum=Q(0)
    for (ei,fi),row in zip(frames,mu):
        offs=vertices((Q(0),Q(0)),ei,fi)
        a.append(tuple(sum((weight*v[k] for weight,v in zip(row,offs)),Q(0))
                       for k in range(2)))
    for i,j,n,lam in edges:
        c[i]=add(c[i],scale(lam,n))
        c[j]=sub(c[j],scale(lam,n))
        edge_sum+=lam*(support(*frames[i],n)+support(*frames[j],n))
    psi=[]
    for mi,ai,ci in zip(m,a,c):
        B=add(scale(2,ai),ci)
        if mi==0:
            if B!=(0,0):
                raise ValueError('Unbalanced zero-anchor square')
            psi.append(Q(0))
        else:
            psi.append(dot(B,B)/(4*mi))
    return Q(1,2)+edge_sum-sum(psi,Q(0)),m,psi


def check_regularization():
    frames=[frame(Q(i,20))[3:] for i in range(8)]
    mu=[[Q(0) for _ in range(4)] for _ in range(8)]
    for i in range(4):
        mu[i][i]=Q(1,4)
    edges=[(i,j,frames[i][(i+j)%2],Q(i+j+1,31))
           for i,j in combinations(range(4),2)]
    D,m,psi=dual_data(frames,mu,edges)
    for eps in (Q(1,10000),Q(1,100),Q(1,2),Q(9,10)):
        mur=[[(1-eps)*v+eps/32 for v in row] for row in mu]
        er=[(i,j,n,(1-eps)*lam) for i,j,n,lam in edges]
        Dr,mr,_=dual_data(frames,mur,er)
        assert sum(map(sum,mur),Q(0))==1 and min(mr)>=eps/8
        reserve=sum(((1-eps)*eps*psi[i]/(8*mr[i])
                     for i in range(8) if m[i]>0),Q(0))
        assert Dr-((1-eps)*D+eps/2)==reserve>=0
    try:
        dual_data(frames,mu,edges+[(0,7,frames[0][0],Q(1))])
    except ValueError:
        pass
    else:
        raise AssertionError('Invalid zero-anchor dual was accepted')
    # Balanced directed triangle: an exact empty-owner-fiber certificate.
    frames=[frame(Q(0))[3:] for _ in range(8)]
    uniform=[[Q(1,32)]*4 for _ in range(8)]
    e=frames[0][0]
    cycle=[(0,1,e,Q(2)),(1,2,e,Q(2)),(2,0,e,Q(2))]
    assert dual_data(frames,uniform,cycle)[0]==Q(13,2)
    print('Gate 2: regularization identities, zero-anchor guard, force cycle: PASS')


def construction(generic=False):
    u=Q(11,12); r=Q(1753659,1000000); bigU=Q(331179,200000)
    v=Q(547767,1000000); w=Q(95073,50000)
    e=(Q(255,257),Q(32,257)); f=quarter_turn(e)
    h1=e[0]*r-e[1]*u-2-e[0]
    h2=e[1]*w-e[0]*v-1-e[1]
    P5=add(scale(h1,e),scale(h2,f))
    H=add(P5,scale(Q(1,2),add(e,f)))
    G=add(H,e)
    centers=[(r-Q(1,2),Q(1,2)-u),
             (bigU-Q(1,2),Q(3,2)-u),
             (bigU-Q(3,2),Q(7,20)),
             (bigU-Q(5,2),Q(3,2)-v),
             (Q(1,2)-w,Q(1,2)-v),
             (bigU-Q(3,2),Q(27,20)),H,G]
    frames=[frame(Q(0))[3:] for _ in range(6)]+[(e,f),(e,f)]
    if generic:
        centers=[scale(1+Q(1,10**8),p) for p in centers]
        new=[]
        for j,(ei,fi) in enumerate(frames,1):
            _,_,_,rot,_=frame(Q(j,10**12))
            en=add(scale(rot[0],ei),scale(rot[1],fi))
            new.append((en,quarter_turn(en)))
        frames=new
        for (ei,_),(ej,_) in combinations(frames,2):
            assert dot(ei,ej)!=0 and ei[0]*ej[1]-ei[1]*ej[0]!=0
    return centers,frames


def longest_path(edges):
    adj=[[] for _ in range(8)]
    for i,j in edges:
        adj[i].append(j)
    state=[0]*8; dist=[0]*8
    def visit(i):
        if state[i]==1:
            raise AssertionError('Cycle in actual canonical projection graph')
        if state[i]==2:
            return dist[i]
        state[i]=1
        dist[i]=max((1+visit(j) for j in adj[i]),default=0)
        state[i]=2
        return dist[i]
    return max(visit(i) for i in range(8))


def check_packing(generic):
    ps,fs=construction(generic)
    q=Q(9789,2500)
    slacks=[q-dot(v,v) for p,(e,f) in zip(ps,fs) for v in vertices(p,e,f)]
    assert len(slacks)==32 and min(slacks)>0
    graphs=[[] for _ in range(4)]
    margins=[]
    for i,j in combinations(range(8),2):
        delta=sub(ps[j],ps[i])
        normals=[scale(sign,axis) for axis in (*fs[i],*fs[j]) for sign in (-1,1)]
        widths=[support(*fs[i],n)+support(*fs[j],n) for n in normals]
        assert min(widths)==max(widths)
        w=widths[0]
        maximum=max(dot(n,delta) for n in normals)
        assert maximum>=w
        if generic:
            assert maximum>w
        choices=[n for n in normals if dot(n,delta)==maximum]
        for n in choices:
            assert abs(dot(quarter_turn(n),delta))<=maximum
            for k in octants(n):
                assert dot(U[k],delta)>=7*maximum>=7*w>=7
        n=choices[0]; k=octants(n)[0]
        graphs[k%4].append((i,j) if k<4 else (j,i))
        margins.append(dot(U[k],delta)-7)
    for p in ps:
        assert all(abs(dot(r,p))<=Q(39,2) for r in U)
    heights=[longest_path(g) for g in graphs]
    assert max(heights)<=5 and len(margins)==28
    kind='generic eight-distinct-frame' if generic else 'rational reference'
    print(f'Gate 3A: {kind}: 32 vertices, 28 pairs, all maximizing-axis ties: PASS')
    print(f'  Four canonical projection longest-path lengths: {heights}')


def check_cones():
    count=0
    vectors=[(Q(a,3),Q(b,3)) for a,b in product(range(-6,7),repeat=2) if (a,b)!=(0,0)]
    for ai in range(9):
        for aj in range(ai,9):
            ei,fi=frame(Q(ai,8))[3:]
            ej,fj=frame(Q(aj,8))[3:]
            normals=[scale(s,n) for n in (ei,fi,ej,fj) for s in (-1,1)]
            for delta in vectors:
                maximum=max(dot(n,delta) for n in normals)
                for n in normals:
                    if dot(n,delta)!=maximum:
                        continue
                    for k in octants(n):
                        assert dot(U[k],delta)>=7*maximum
                        count+=1
    # Essential negative control: a valid NONmaximizing owner need not pass.
    delta=(Q(1),Q(-11,5)); n=(Q(1),Q(0))
    assert dot(n,delta)==1  # valid horizontal SAT for two axis-parallel squares
    assert dot(U[0],delta)<7
    # Centers +/-delta/2 both fit their squares in q=89/25<the ceiling.
    assert Q(89,25)<Q(9789,2500)
    print(f'Gate 3A: {count} exact cone identities and noncanonical negative control: PASS')


def main():
    check_regularization()
    check_cones()
    check_packing(False)
    check_packing(True)
    print('No exhaustive owner-family enumeration or unrestricted radius proof is claimed.')

if __name__=='__main__':
    main()

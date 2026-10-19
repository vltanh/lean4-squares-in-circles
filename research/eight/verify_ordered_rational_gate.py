#!/usr/bin/env python3
"""Exact arithmetic regression for Gate 1, not a continuous proof oracle.

No external packages, floating-point trigonometry, Lean, or network access.
The domain coverage and SAT equivalence are proved in the companion note.
"""
from fractions import Fraction as Q
from itertools import product


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def scale(s, a):
    return tuple(s*x for x in a)


def frame(z):
    d = 1+z*z
    E = (1-z*z, 2*z)
    F = (-2*z, 1-z*z)
    return d, E, F, scale(1/d, E), scale(1/d, F)


def support(e, f, n):
    return (abs(dot(e, n))+abs(dot(f, n)))/2


def vertices(p, e, f):
    return [add(p, scale(Q(1,2), add(scale(s,e), scale(t,f))))
            for s,t in product((-1,1), repeat=2)]


def disjoint(p, ei, fi, r, ej, fj):
    delta = sub(r,p)
    return any(dot(n,delta) >= support(ei,fi,n)+support(ej,fj,n)
               for axis in (ei,fi,ej,fj) for s in (-1,1)
               for n in (scale(s,axis),))


def rotate_to_frame(v, e, f):
    return dot(e,v), dot(f,v)


def quarter_turn(v):
    return -v[1], v[0]


def representative(v):
    # Four side-normal representatives describe precisely the same square.
    for _ in range(4):
        if v[0] > 0 and v[1] >= 0:
            return v
        v = quarter_turn(v)
    raise AssertionError('No first-quadrant side representative')


def main():
    grid = [Q(k,16) for k in range(17)]
    centers = [(Q(-7,6),Q(2,5)), (Q(0),Q(0)),
               (Q(3,8),Q(-11,7)), (Q(5,4),Q(9,10))]
    checked = 0
    for a in grid:
        di,Ei,Fi,ei,fi = frame(a)
        assert dot(ei,ei)==dot(fi,fi)==1 and dot(ei,fi)==0
        for b in grid:
            if b < a:
                continue
            dj,Ej,Fj,ej,fj = frame(b)
            delta = b-a
            P = (1+a*b)*(1+a*b+delta)
            assert P-di*dj == delta*(1+a*b-delta) >= 0
            w=P/(di*dj)
            for own_d,other_d,E,F,e,f in (
                (di,dj,Ei,Fi,ei,fi), (dj,di,Ej,Fj,ej,fj)):
                for U,u in ((E,e),(F,f)):
                    for sign in (-1,1):
                        n=scale(sign,u)
                        assert support(ei,fi,n)+support(ej,fj,n)==w
                        for p,r in zip(centers,centers[1:]):
                            v=sub(r,p)
                            polynomial=sign*other_d*dot(U,v)-P
                            actual=dot(n,v)-w
                            assert polynomial==di*dj*actual
                            checked+=1
        q=Q(9789,2500)
        for p in centers:
            for s,t in product((-1,1),repeat=2):
                V=add(scale(2*di,p),add(scale(s,Ei),scale(t,Fi)))
                v=add(p,scale(Q(1,2),add(scale(s,ei),scale(t,fi))))
                assert 4*di*di*q-dot(V,V)==4*di*di*(q-dot(v,v))

    # Weak equality is essential: edge and corner tangency are allowed.
    _,_,_,e,f=frame(Q(0))
    origin=(Q(0),Q(0))
    assert disjoint(origin,e,f,(Q(1),Q(0)),e,f)
    assert disjoint(origin,e,f,(Q(1),Q(1)),e,f)
    assert not disjoint(origin,e,f,(Q(999,1000),Q(0)),e,f)
    assert not disjoint(origin,e,f,origin,e,f)
    # z=1 is only a different side normal for the z=0 square.
    _,_,_,e1,f1=frame(Q(1))
    assert set(vertices(origin,e,f))==set(vertices(origin,e1,f1))

    # Exact common-rotation normalization on eight arbitrary rational frames.
    zs=[Q(-4,5),Q(2,7),Q(0),Q(1),Q(-1),Q(1,3),Q(1,3),Q(3,4)]
    poses=[]
    for i,z in enumerate(zs):
        _,_,_,ei,fi=frame(z)
        poses.append(((Q(4*(i%4)),Q(4*(i//4))),ei,fi))
    base_e,base_f=poses[0][1:]
    normalized=[]
    for p,ei,fi in poses:
        pnew=rotate_to_frame(p,base_e,base_f)
        raw_e=rotate_to_frame(ei,base_e,base_f)
        enew=representative(raw_e)
        fnew=quarter_turn(enew)
        znew=enew[1]/(1+enew[0])
        assert Q(0)<=znew<=Q(1)
        assert frame(znew)[3:]==(enew,fnew)
        old_vertices=vertices(p,ei,fi)
        new_vertices=vertices(pnew,enew,fnew)
        assert {rotate_to_frame(v,base_e,base_f) for v in old_vertices}==set(new_vertices)
        normalized.append((znew,pnew,enew,fnew))
    normalized.sort(key=lambda x:x[0])
    assert normalized[0][0]==0
    for i in range(8):
        for j in range(i+1,8):
            _,p,ei,fi=normalized[i]
            _,r,ej,fj=normalized[j]
            assert disjoint(p,ei,fi,r,ej,fj)
    print(f'Exact SAT polynomial/residual identities checked: {checked}')
    print('Vertex identities, endpoint duplication, tangency, and 8-frame normalization: PASS')
    print('The finite checks audit formulas; the continuous theorem is the written proof.')

if __name__=='__main__':
    main()

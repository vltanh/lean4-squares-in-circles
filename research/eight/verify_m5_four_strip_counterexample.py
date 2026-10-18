#!/usr/bin/env python3
"""Exact M5 witnesses and curvature-chain arithmetic, not a global search.
All final acceptance uses Fraction arithmetic; no optimizer or trig library.
"""
from fractions import Fraction as F
from itertools import combinations, product

Z_NUMERATORS = [0,1000000,414211219229,414212390801,414212976588,
                414214148160,414215319735,999997000004]
Z_DENOMINATOR = 10**12
CENTER_NUMERATORS = [(-55267,9560),(-500000,1222109),(-1025488,-895564),
    (1051313,-921389),(-1264568,279570),(0,-1284290),
    (1264568,279570),(500000,1222109)]
STRIP_ONLY_CENTERS = [(-61276,144607),(-500001,1144607),(-973545,-913494),
    (973543,-913495),(-1268382,205881),(-1,-1354166),
    (1268382,205880),(500001,1144607)]
DILATION = F(10001,10000)
STRIP_RADIUS = F(989,500)
DISK_Q = F(397,100)
U = ((12,5),(5,12),(-5,12),(-12,5))
SEPARATORS = (('+f1','-e2','-f3','-e0','-f0','+e0','+e7'),
    ('-f1','-f3','-e4','-f1','-f6','+e1'),
    ('+e2','+f2','-f5','+e2','+e2'),
    ('+f4','-e3','+e6','+e7'),('-f4','-f6','+e4'),
    ('+e6','+e7'),('+f6',))
NORM_LOWER_DISK = (5679,39661,38044,39415,39661,39661,39661,39661)
NORM_LOWER_STRIP = (7305,37052,36595,36595,39454,42494,39454,37052)


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),F(0))


def J(a):
    return -a[1],a[0]


def scale(t,a):
    return tuple(t*x for x in a)


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def frame(z):
    d=1+z*z
    e=((1-z*z)/d,2*z/d)
    return e,J(e)


def support(fr,n):
    return (abs(dot(fr[0],n))+abs(dot(fr[1],n)))/2


def quarter_rep(x,y):
    for _ in range(4):
        if x>0 and y>=0:
            return x,y
        x,y=-y,x
    raise ValueError('Zero direction')


def relative(a,b):
    return quarter_rep(dot(a,b),a[0]*b[1]-a[1]*b[0])


def witness(strip_only=False):
    nums=STRIP_ONLY_CENTERS if strip_only else CENTER_NUMERATORS
    return ([scale(DILATION,tuple(F(a,10**6) for a in v)) for v in nums],
            [frame(F(z,Z_DENOMINATOR)) for z in Z_NUMERATORS])


def check_chain(ps,fs):
    # A=1, B=7, H=4, L=2, D=5, R=3, E=6, using zero-based labels.
    eps=F(1,200)
    for i in (1,7,2,3,4,5,6):
        v=(1,0) if i in (1,7) else (1,1)
        assert any(dot(n,v)>0
                   and abs(n[0]*v[1]-n[1]*v[0])<=eps*dot(n,v)
                   for axis in fs[i] for s in (-1,1)
                   for n in [scale(s,axis)])
    edges=((1,7,(1,0)),(4,1,(1,1)),(6,7,(-1,1)),
           (4,2,(1,-1)),(2,5,(1,-1)),
           (6,3,(-1,-1)),(3,5,(-1,-1)))
    for i,j,v in edges:
        d=sub(ps[j],ps[i])
        axes=[scale(s,n) for fr in (fs[i],fs[j])
              for n in fr for s in (-1,1)]
        maximum=max(dot(n,d) for n in axes)
        assert any(dot(n,d)==maximum and dot(n,v)>0
                   and abs(n[0]*v[1]-n[1]*v[0])<=eps*dot(n,v)
                   for n in axes)


def main():
    eps=F(1,200)
    a=(1-eps-eps*eps/2)*(1-2*eps*eps)
    assert a==F(1591900401,1600000000)
    sharp_simple=(F(1693,1000)**2+F(2252,1000)**2)/2
    assert sharp_simple-F(99,25)==F(17753,2000000)>0
    assert F(99,25)*a*a-F(9789,2500)==F(
        282141783692119299,64000000000000000000)>0
    print('Hand-proof curvature constants and independent-angle reserve: PASS')
    for strip_only in (False,True):
        ps,fs=witness(strip_only)
        counts=[]
        for e,f in fs:
            counts.append(sum(x>=y for x,y in
                              (relative(e,g) for g,h in fs)))
        assert counts==[5,5,5,5,4,4,4,4]
        entries=[]
        for i,(e,f) in enumerate(fs):
            x,y=e
            ch='L' if x>=y else 'H'
            if ch=='H':
                x,y=x+y,y-x
            entries.append((y/x,ch,i))
        entries.sort()
        assert len({x for x,c,i in entries})==8
        assert ''.join(c for x,c,i in entries)=='LHLHLHLL'
        sat=[]
        for i,j in combinations(range(8),2):
            d=sub(ps[j],ps[i])
            axes=(*fs[i],*fs[j])
            slacks=[abs(dot(n,d))-support(fs[i],n)-support(fs[j],n)
                    for n in axes]
            sat.append(max(slacks))
        assert min(sat)>F(1,20000)
        # Also check every displayed hand-table axis, not only a maximizer.
        for i,row in enumerate(SEPARATORS):
            for j,symbol in enumerate(row,i+1):
                k=int(symbol[2:])
                n=scale(1 if symbol[0]=='+' else -1,
                        fs[k][0 if symbol[1]=='e' else 1])
                assert dot(n,sub(ps[j],ps[i]))-support(fs[i],n)-support(fs[j],n)>F(1,20000)
        radius=F(191,100) if strip_only else STRIP_RADIUS
        strips=[13*radius-abs(dot(u,p))-support(fr,u)
                for p,fr in zip(ps,fs) for u in U]
        assert min(strips)>(F(9,100) if strip_only else F(1,500))
        norms=[]
        for i,(p,(e,f)) in enumerate(zip(ps,fs)):
            lower=(NORM_LOWER_STRIP if strip_only else NORM_LOWER_DISK)[i]
            farthest=(abs(dot(p,e))+F(1,2))**2+(abs(dot(p,f))+F(1,2))**2
            assert F(lower,10000)<farthest<F(lower+1,10000)
            assert dot(e,e)==dot(f,f)==1 and dot(e,f)==0
            for s,t in product((-1,1),repeat=2):
                v=add(p,scale(F(1,2),add(scale(s,e),scale(t,f))))
                norms.append(dot(v,v))
        assert len(norms)==32
        if strip_only:
            assert radius<F(79,40)
            assert F(21,5)<max(norms)<F(17,4)
        else:
            assert max(norms)<DISK_Q<4
            assert max(norms)>F(99,25)>F(9789,2500)
        check_chain(ps,fs)
        print(('Four-strip no-go' if strip_only else 'Disk-radius-two no-go')+':')
        print('  M5 counts',counts,'and generic folded type I: PASS')
        print('  28 actual SAT gaps > 1/20000; all 32 full-square strips: PASS')
        print('  All true vertices checked; seven canonical chain hypotheses: PASS')
    print('The strip witness fits radius-191/100 support strips, not that disk.')
    print('Neither witness is a subcandidate disk packing or an optimality counterexample.')


if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Exact constants for a physical-SAT neighborhood with independent angles.

Proof of the analytic Taylor bounds is in UNRESTRICTED_NEIGHBORHOOD.md.
No previously reviewed certificate is modified.
"""
from contextlib import redirect_stdout
from io import StringIO
from fractions import Fraction as F
from contact_family import family
from isolate_contact_root import I,certificate
from check_fixed_orientation_stress import solve_intervals
from check_local_angular_stress import angular_certificate
from check_angle_neighborhood import active_matrix,EDGES,DISKS,abs_upper

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')

def unrestricted_neighborhood_certificate():
    # Re-run the exact physical owner and angular-flow certificate, keeping
    # this top-level output concise. A failed assertion still aborts.
    with redirect_stdout(StringIO()):
        angular_certificate()
        box=certificate()
    matrix=active_matrix(box) # J_half_angle transpose
    weights=solve_intervals(matrix,[0]*23+[1])
    assert all(w.lo>F(1,100) for w in weights)
    assert sum(w.hi for w in weights)<20
    inverse_bound=F(0)
    for i in range(24):
        rhs=[0]*24;rhs[i]=1
        column=solve_intervals(matrix,rhs)
        # J_angle = J_half_angle * diag(1,...,(1+ta^2)/2,
        # (1+tb^2)/2,1). The two inverse row factors are strictly below2.
        row_bound=sum(abs_upper(x) for x in column)*(2 if i in [21,22] else 1)
        inverse_bound=max(inverse_bound,row_bound)
    assert inverse_bound<40
    _,p,angles,extra=family(box[0],box[1],lambda x:x.sqrt())
    (ca,sa),(cb,sb)=angles;r,_,_,_=extra
    a,b=p[0];ka=(1+ca+sa)/2
    H=(ka+1-r-sa*(b-1))/ca
    p[1]=(I(H.lo-F(1,10000),a.hi+F(1,10000)),b-1)
    ex,ey=(I(1),I(0)),(I(0),I(1))
    frames=[(ex,ey)]*7+[((ca,sa),(-sa,ca))]*2+[((cb,sb),(-sb,cb))]*2
    dot=lambda x,y:sum(a*b for a,b in zip(x,y))
    norm2=lambda x:dot(x,x)
    for i,e,f in DISKS:
        vertex=tuple(p[i][k]+(e*frames[i][0][k]+f*frames[i][1][k])/2 for k in range(2))
        assert norm2(vertex).hi<F(25,4)
    parallel={0,1,3,4,5,6,8,10,13}
    for index,(i,j,owner,axis,sign) in enumerate(EDGES):
        delta=tuple(p[j][k]-p[i][k] for k in range(2))
        assert norm2(delta).hi<9
        n=tuple(sign*x for x in frames[owner][axis]);jn=(-n[1],n[0])
        if index in parallel:
            assert dot(jn,delta).abs_upper()<F(999,1000)
        else:
            cosine=dot(frames[i][0],frames[j][0]);sine=dot(frames[i][1],frames[j][0])
            assert cosine.lo>F(1,100) and sine.lo>F(1,100)
    radius=F(1,10**7)
    # Pair slack changes by <=8N, preserving the >=1/1000 parallel-axis
    # margin and >=1/100 nonparallel-axis margin. Selected projection signs
    # and the smooth nonparallel support quadrant also persist.
    assert 8*radius<F(1,1000) and 2*radius<F(1,100)
    # W<20 and each constraint's error <=10N² give C=200.
    # T<=20000N²; every grouped linear row <=120010N².
    contraction=(40*120010+20000)*radius
    assert contraction<1
    print('PASS: all24 stress weights >1/100 and their total <20.')
    print('PASS: ordinary-angle grouped Jacobian inverse infinity norm <40.')
    print('PASS: boundary vertex norms <5/2 and active center gaps <3.')
    print('PASS: owner persistence and smooth oblique support hold for N<=1/10^7.')
    print('PASS: N <=4820400 N² contradicts 0<N<=1/10^7.')
    print('Conclusion: every physical packing in this explicit neighborhood has q>=qc; equality is the exact slider family.')
    return inverse_bound,radius

if __name__=='__main__':unrestricted_neighborhood_certificate()

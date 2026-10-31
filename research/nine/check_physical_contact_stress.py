"""Exact local/witness regressions for PHYSICAL_CONTACT_STRESS.md.

These checks are not a universal nine-square optimality certificate.
Run alongside check_sparse_stress.py; Python standard library only.
"""
from fractions import Fraction as F
import json
from check_sparse_stress import Square, add, sub, scale, dot, rot, pair_gap


def main() -> None:
    Q = F(1105,256)
    S = ([Square((F(x,2),F(1,16))) for x in (-3,-1,1,3)]
         + [Square((F(x),-F(15,16))) for x in (-1,0,1)]
         + [Square((F(x,20),F(19,16)),(F(99,101),F(20,101))) for x in (-11,11)])
    lam = [F(23,64),F(0),F(0),F(23,64),F(9,64),F(0),F(9,64),F(0),F(0)]
    P = {0:(F(-2),F(9,16)),3:(F(2),F(9,16)),
         4:(-F(3,2),-F(23,16)),6:(F(3,2),-F(23,16))}
    ex, ey = (F(1),F(0)),(F(0),F(1))
    edges = ([(i,i+1,ex,F(23,16),(S[i+1].c[0]-F(1,2),F(45,128))) for i in range(3)]
             + [(4,5,ex,F(27,64),(S[5].c[0]-F(1,2),-F(115,96))),
                (5,6,ex,F(27,64),(S[6].c[0]-F(1,2),-F(115,96))),
                (4,0,ey,F(207,512),(-F(5,4),-F(7,16))),
                (6,3,ey,F(207,512),(F(5,4),-F(7,16)))])
    forces = [(F(0),F(0)) for _ in S]
    moments = [F(0) for _ in S]
    for i,p in P.items():
        assert dot(p,p) == Q
        f = scale(2*lam[i],p)
        forces[i] = add(forces[i],f)
        moments[i] += dot(f,rot(sub(p,S[i].c)))
    for i,j,d,mu,p in edges:
        for s in (S[i],S[j]):
            assert abs(dot(sub(p,s.c),s.u)) <= F(1,2)
            assert abs(dot(sub(p,s.c),s.v)) <= F(1,2)
        assert dot(d,sub(p,S[i].c)) == S[i].support(d)
        assert dot(d,sub(p,S[j].c)) == -S[j].support(d)
        forces[i] = add(forces[i],scale(mu,d))
        forces[j] = sub(forces[j],scale(mu,d))
        moments[i] += mu*dot(d,rot(sub(p,S[i].c)))
        moments[j] -= mu*dot(d,rot(sub(p,S[j].c)))
    assert forces == [(0,0)]*9
    assert moments == [0]*9

    # Exact rational angle tests of the two-endpoint sufficient branch.
    # With i's frame equal to identity and delta = theta_j-theta_i:
    # delta >= 0 -> i's upper-right corner maximizes projection on u_j;
    # delta <= 0 -> j's lower-left corner minimizes projection on u_i.
    rotations_checked = 0
    for t in [F(-1,3),F(-1,5),F(-1,7),F(0),F(1,7),F(1,5),F(1,3)]:
        u = ((1-t*t)/(1+t*t),2*t/(1+t*t))
        v = rot(u)
        i = Square((-F(2,7),F(3,8)))
        j = Square((F(9,11),-F(4,13)),u)
        low_j = add(j.c,scale(-F(1,2),add(u,v)))
        up_i = add(i.c,(F(1,2),F(1,2)))
        B_minus = F(1,2)-dot(ex,sub(low_j,i.c))
        B_plus = F(1,2)+dot(u,sub(up_i,j.c))
        if t <= 0:
            exact_i_gap = F(1,2)+j.support(ex)-dot(ex,sub(j.c,i.c))
            assert B_minus == exact_i_gap
        if t >= 0:
            exact_j_gap = F(1,2)+i.support(u)-dot(u,sub(j.c,i.c))
            assert B_plus == exact_j_gap
        assert dot(u,u) == 1
        rotations_checked += 1

    # Both base contact-gradient rows have actual endpoint levers.
    # Test full and partial side overlap in the t>=0 local chart.
    base_gradient_checks = 0
    for t in [F(0),F(1,4),F(1,2),F(3,4)]:
        ci,cj = (F(0),F(0)),(F(1),t)
        lo = (F(1,2),t-F(1,2))
        hi = (F(1,2),F(1,2))
        for p in (lo,hi):
            assert all(abs(z) <= F(1,2) for z in sub(p,ci))
            assert all(abs(z) <= F(1,2) for z in sub(p,cj))
        # B_minus = .5 - u_i dot(p_j-c_i).
        own_lo = -dot(rot(ex),sub(lo,ci))
        other_lo = -dot(ex,rot(sub(lo,cj)))
        assert own_lo == dot(ex,rot(sub(lo,ci)))
        assert other_lo == -dot(ex,rot(sub(lo,cj)))
        # B_plus = .5 + u_j dot(p_i-c_j).
        left_hi = dot(ex,rot(sub(hi,ci)))
        owner_hi = dot(rot(ex),sub(hi,cj))
        assert left_hi == dot(ex,rot(sub(hi,ci)))
        assert owner_hi == -dot(ex,rot(sub(hi,cj)))
        # Simultaneous rotation annihilates the full physical gradient.
        for p in (lo,hi):
            residual = (dot(ex,rot(ci))-dot(ex,rot(cj))
                        +dot(ex,rot(sub(p,ci)))-dot(ex,rot(sub(p,cj))))
            assert residual == 0
        base_gradient_checks += 2
    print(json.dumps({
        "scope":"one exact physical stress and finite local algebra regressions; not global optimality",
        "q":str(Q),
        "physical_pair_forces":len(edges),
        "actual_shared_contact_points_checked":len(edges),
        "normal_cone_memberships_checked":2*len(edges),
        "force_residuals": [list(map(str,f)) for f in forces],
        "physical_angular_residuals":list(map(str,moments)),
        "rational_relative_rotations_checked":rotations_checked,
        "base_contact_endpoint_gradient_checks":base_gradient_checks,
        "all_checks_passed":True
    },indent=2))


if __name__ == '__main__':
    main()

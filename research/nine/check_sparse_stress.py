"""Exact regression checks for the n=9 sparse-stress reduction.

Uses Fraction arithmetic only.  This file checks the concrete record-radius
witness and its fixed-orientation stress; it is not an optimality certificate
for arbitrary configurations and does not establish the compactness/KKT proofs.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
import json

Vec = tuple[F, F]


def add(x: Vec, y: Vec) -> Vec:
    return (x[0] + y[0], x[1] + y[1])


def scale(a: F, x: Vec) -> Vec:
    return (a*x[0], a*x[1])


def sub(x: Vec, y: Vec) -> Vec:
    return add(x, scale(F(-1), y))


def dot(x: Vec, y: Vec) -> F:
    return x[0]*y[0] + x[1]*y[1]


def rot(x: Vec) -> Vec:
    return (-x[1], x[0])


@dataclass(frozen=True)
class Square:
    c: Vec
    u: Vec = (F(1), F(0))

    @property
    def v(self) -> Vec:
        return rot(self.u)

    def support(self, d: Vec) -> F:
        return (abs(dot(d, self.u)) + abs(dot(d, self.v)))/2

    def corners(self) -> tuple[Vec, ...]:
        return tuple(add(self.c, add(scale(F(a,2), self.u), scale(F(b,2), self.v)))
                     for a, b in product((-1,1), repeat=2))

    def radius_sq(self) -> F:
        return max(dot(p, p) for p in self.corners())


def pair_gap(s: Square, t: Square) -> F:
    """Maximum of the four undirected separating-axis gaps."""
    return max(abs(dot(sub(t.c,s.c),d)) - s.support(d) - t.support(d)
               for d in (s.u,s.v,t.u,t.v))


def pos(x: F) -> F:
    return max(x, F(0))


def main() -> None:
    Q = F(1105,256)
    S = ([Square((F(x,2), F(1,16))) for x in (-3,-1,1,3)]
         + [Square((F(x), -F(15,16))) for x in (-1,0,1)]
         + [Square((F(x,20), F(19,16)), (F(99,101),F(20,101))) for x in (-11,11)])
    assert len(S) == 9
    assert all(dot(s.u,s.u) == 1 for s in S)
    slacks = [Q-s.radius_sq() for s in S]
    assert min(slacks) == 0
    assert slacks[7:] == [F(42573,80800), F(22173,80800)]
    gaps = {(i,j): pair_gap(S[i], S[j]) for i,j in combinations(range(9),2)}
    assert all(g >= 0 for g in gaps.values())
    # The upper pair's actual own-axis separation is strict although both
    # common coordinate projection intervals overlap.
    assert gaps[(7,8)] == F(79,1010)
    for d in ((F(1),F(0)), (F(0),F(1))):
        assert abs(dot(sub(S[8].c,S[7].c),d)) < S[7].support(d)+S[8].support(d)

    lam = [F(23,64), F(0), F(0), F(23,64), F(9,64), F(0), F(9,64), F(0), F(0)]
    P = {0:(F(-2),F(9,16)), 3:(F(2),F(9,16)),
         4:(-F(3,2),-F(23,16)), 6:(F(3,2),-F(23,16))}
    ex, ey = (F(1),F(0)), (F(0),F(1))
    edges = ([(i,i+1,ex,F(23,16)) for i in range(3)]
             + [(4,5,ex,F(27,64)), (5,6,ex,F(27,64)),
                (4,0,ey,F(207,512)), (6,3,ey,F(207,512))])
    force = [(F(0),F(0)) for _ in S]
    edge_work = F(0)
    for i,j,d,mu in edges:
        w = S[i].support(d)+S[j].support(d)
        assert dot(d,sub(S[j].c,S[i].c)) == w
        assert pair_gap(S[i],S[j]) == 0
        force[i] = add(force[i],scale(mu,d))
        force[j] = sub(force[j],scale(mu,d))
        edge_work += mu*w
    assert sum(lam) == 1
    barycenter = (F(0),F(0))
    for i,s in enumerate(S):
        if lam[i]:
            assert P[i] in s.corners()
            assert dot(P[i],P[i]) == Q
            assert add(scale(2*lam[i],P[i]),force[i]) == (0,0)
            barycenter = add(barycenter,scale(lam[i],P[i]))
        else:
            assert force[i] == (0,0)
    assert barycenter == (0,0)
    dual = edge_work
    for i,s in enumerate(S):
        a = lam[i]
        if not a:
            assert force[i] == (0,0)
            continue
        dual += a/2 - (pos(abs(dot(force[i],s.u))-a)**2
                       +pos(abs(dot(force[i],s.v))-a)**2)/(4*a)
    assert dual == Q
    assert edge_work + F(1,2) - sum(lam[i]*dot(s.c,s.c) for i,s in enumerate(S)) == Q

    # A separate full angular-stationarity certificate on the same witness.
    # Every selected directed separator normal belongs to its tail square.
    # At parallel edge contacts, split its weight among the two active
    # support vertices of the head square, choosing a true common contact point.
    torque = [F(0) for _ in S]
    for i,p in P.items():
        torque[i] += 2*lam[i]*dot(p, rot(sub(p,S[i].c)))
    angular_atoms = []
    for i,j,d,mu in edges:
        if d == ex:
            y = F(45,128) if i < 3 else -F(115,96)
            contact = (S[j].c[0]-F(1,2), y)
            vb = sub(S[j].c,contact)
            assert vb[0] == F(1,2) and abs(vb[1]) <= F(1,2)
            atoms = [((F(1,2),F(1,2)), mu*(F(1,2)+vb[1])),
                     ((F(1,2),-F(1,2)), mu*(F(1,2)-vb[1]))]
        else:
            contact = ((-F(5,4) if j == 0 else F(5,4)), -F(7,16))
            vb = sub(S[j].c,contact)
            assert vb[1] == F(1,2) and abs(vb[0]) <= F(1,2)
            atoms = [((F(1,2),F(1,2)), mu*(F(1,2)+vb[0])),
                     ((-F(1,2),F(1,2)), mu*(F(1,2)-vb[0]))]
        assert all(abs(z) <= F(1,2) for z in sub(contact,S[i].c))
        assert all(abs(z) <= F(1,2) for z in sub(contact,S[j].c))
        assert sum(a for _,a in atoms) == mu
        for v,a in atoms:
            assert a > 0
            # g = 1/2 + d dot v_j - d dot(c_j-c_i).
            assert F(1,2)+dot(d,v)-dot(d,sub(S[j].c,S[i].c)) == 0
            torque[i] += a*dot(rot(d),sub(v,sub(S[j].c,S[i].c)))
            torque[j] += a*dot(d,rot(v))
            angular_atoms.append((i,j,d,v,a))
    assert torque == [0]*9
    assert len(angular_atoms) == 14

    # Exact uncrossing identity used in PLANAR_STRESS_CORE.md.
    # Quadrants are SW=0, SE=1, NW=2, NE=3; all arrows left-to-right.
    A,B = F(7,11),F(5,13)
    delta = min(A,B)
    def corner_forces(es):
        ff = [F(0)]*4
        for i,j,w in es:
            ff[i] += w
            ff[j] -= w
        return ff
    before = [(0,3,A),(2,1,B)]
    after = [(0,3,A-delta),(2,1,B-delta),(0,1,delta),(2,3,delta)]
    assert corner_forces(before) == corner_forces(after)
    assert sum(w for _,_,w in before) == sum(w for _,_,w in after)
    assert (A-delta)*(B-delta) == 0

    report = {
        "scope": "one exact packing and its fixed-orientation stress; not unrestricted optimality",
        "q": str(Q),
        "unit_frames_checked": len(S),
        "pairwise_SAT_checks": len(gaps),
        "corner_checks": 4*len(S),
        "free_square_circle_slacks": list(map(str,slacks[7:])),
        "upper_pair_oblique_gap": str(gaps[(7,8)]),
        "positive_circle_atoms": sum(a>0 for a in lam),
        "positive_contact_edges": len(edges),
        "total_positive_fixed_frame_atoms": sum(a>0 for a in lam)+len(edges),
        "lambda_sum": str(sum(lam)),
        "force_balance_at_all_nine_nodes": True,
        "boundary_barycenter": list(map(str,barycenter)),
        "dual_value": str(dual),
        "angular_separator_vertex_atoms": len(angular_atoms),
        "angular_plus_circle_atoms": len(angular_atoms)+sum(a>0 for a in lam),
        "angular_stationarity_at_all_nine_nodes": all(t == 0 for t in torque),
        "four_corner_uncrossing_identity": True,
        "all_checks_passed": True,
    }
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()

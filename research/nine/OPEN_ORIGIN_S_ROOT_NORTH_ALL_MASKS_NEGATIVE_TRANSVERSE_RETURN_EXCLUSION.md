# Every negative transverse AB return in the North roof interface is impossible

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed all-mask feature theorem, awaiting separate
full review and root adoption. The remaining zero-transverse AB side
and the original roof ABC.S family are not declared closed.**

The proof covers both complete original H3 rows, every physical B
circle mask, every C-to-B support, all original means and individual
zero coefficients. The only normal-selection input is the already
compatible fixed-point unique-circle-tip theorem, at a literal B2
with two distinct physical singleton applications. A physical shared
BC is handled geometrically and never put into that selector.

## 1. Exact retained chart and force conventions

Use the complete North chart and physical reductions in
OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md
and BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md.
Write

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=1+epsilon, 0<epsilon<1/60,
    F=1-a in (59/60,1), F^2+b^2=d^2,
    sqrt(2 epsilon)<b<31/120,
    k=F t/b in (1/2,1),
    Q=(k,1-b),
    j=(-C_A,S_A), w=(S_A,C_A),
    A=Q+[0,1]j+[0,1]w,
    C_A,S_A>0, C_A^2+S_A^2=1,
    Z_A=Q+w is A's unique physical circle corner,
    D C_A=alpha+a+k,
    D S_A=beta-1+b-t,
    0<D<1.                                         (1)

The actual original HA axis is w. Put

    J=-Q.j=k C_A-(1-b)S_A,
    W=Q.w=k S_A+(1-b)C_A,
    1/2<J<k<1,
    R^2=J^2+(W+1)^2.                               (2)

The complete previous AB cover gives G.j>0 and G.w<=0. We exclude
the whole strict-negative case G.w<0. Its actual AB application is

    V=Q+j=(1-J)j+W w.                              (3)

The physical radial C has both original circle corners and weights:

    C=[d,d+1]n+[-1/2,1/2]e,
    n=(-C_n,-S_n), e=(-S_n,C_n), C_n,S_n>0.

Its actual C-to-B unit normal g and actual application satisfy

    g.e>0, g.n<=0;
    g.n<0: P_CB=d n+(1/2)e;
    g.n=0: g=e, P_CB=r n+(1/2)e, d<=r<d+1.          (4)

All real pair magnitudes are positive. At the actual B2 the exact
force equation is F_B=G+delta_B g, where F_B retains its full
physical circle mask. Both A and C are actual boundary neighbors.

The physical-two-circle B / G.w<0 case is completely excluded in
TWO_RADIAL_BOUNDARY_UNITS_EXACT_CONTACT_AND_TRANSVERSE_RETURN_BARRIER.md.
We therefore retain a unique physical B circle corner for the rest
of this proof. Its full circle resultant is a positive multiple of
that one actual corner. Its true two-force concurrence is proper,
lies in B, and is a positive multiple of the actual circle corner.

## 2. A uniform relative-angle bound for the whole North residual

This section does not assume the B mask, either CB normal feature,
or the strict-negative AB feature. It uses the entire retained
North chart (1)--(2).

Since D>k and beta<1,

    0<S_A<(b-t)/k=b/k-b/F<b,
    W<k S_A+1-b<1-t<1.                            (5)

The original hub strip also gives, simultaneously in both H3 rows,

    S_n<5b/4.                                      (6)

For a complete derivation, let a_H=a beta+t alpha and
c_H=t beta-a alpha. In the HC-side row put zeta=0; in the
opposite row keep its original zeta. The exact radial support and
original weak moment give

    d^2>=(1+a_H)^2(1+zeta^2),
    a_H>=t alpha,
    0<=zeta<t.

For the side row the first inequality is equality. For the opposite
row use c_H>=(1+a_H)zeta and
d=(1+a_H+c_H zeta)/sqrt(1+zeta^2). Using d^2=(1-a)^2+b^2 gives

    zeta^2+2t alpha<b^2.

Hence

    alpha+zeta
       <b^2/(2t)+t/2-(t-zeta)^2/(2t)
       <=b^2/(2t)+t/2
       <b[F+1/(4F)]<5b/4.

Here b/(2F)<t<b, the preceding function decreases for t<b, and
F+1/(4F)-5/4=(F-1)(F-1/4)/F<0. The actual S_n is alpha in
the side row and (alpha+zeta beta)/sqrt(1+zeta^2) in the opposite
row, proving (6).

Resolve the same original C frame in the A frame:

    n=p j-q w, e=q j+p w,
    p=j.n>0,
    q=S_n C_A+C_n S_A>0,
    p^2+q^2=1.                                     (7)

Put Delta_0=1-W>0. By (5), Delta_0>t=kb/F>kb. The exact world
height of Q also gives

    b=Delta_0+W(1-C_A)+J S_A.

Thus, using J<k,

    b<Delta_0/J,
    S_A<(b-Delta_0)/J,
    q<S_n+S_A
       <Delta_0[1/(4J)+1/J^2].                     (8)

The actual circle equation in (2) and R^2>17/4 give

    Delta_0<2-sqrt(17/4-J^2).

Rationalizing, (8) yields on the entire 1/2<J<1 interval

    q < [(1+J/4)(1-1/(4J^2))]
              /[2+sqrt(17/4-J^2)]
       < 15/[8(4+sqrt(13))] < 1/4.                (9)

The middle strict comparison follows because both positive numerator
factors increase with J, while the positive denominator decreases;
evaluate their limiting quotient at J=1. The last comparison is
equivalent to sqrt(13)>7/2 and has squared reserve 3/4.

In particular p>sqrt(15)/4>29/30. Also (2) gives
W>sqrt(13)/2-1>4/5. For the actual V in (3), therefore,

    V.n=p(1-J)-q W<1/2,
    1/2<V.e=q(1-J)+p W<9/8.                       (10)

The lower estimate follows from p W>(29/30)(4/5)=58/75>1/2.
These are whole-domain bounds, independent of the actual B frame.

## 3. A complete scalar obstruction when B owns both perpendicular inputs

Suppose B owns the two original incoming normals G and g, and they
are perpendicular. With gamma=|G|>0, write in the real A frame

    G/gamma=c_v j-s_v w,
    g=s_v j+c_v w,
    c_v=cos(v), s_v=sin(v),
    0<=v<=arcsin(q).                                (11)

For G.w<0 one has v>0. The weak endpoint is retained for the
calculation. The sign of the perpendicular g is forced by g.e>0,
and the upper bound follows from g.n<=0. In the strict g.n<0 case
the actual CB point is P=d n+(1/2)e. Put its A coordinates

    X=d p+q/2,
    Y=p/2-d q,
    h=1-J.

The actual near B supports and the other coordinates of the two
applications are

    H=V.(G/gamma)=h c_v-W s_v,
    K=P.g=X s_v+Y c_v,
    V.g=h s_v+W c_v,
    P.(G/gamma)=X c_v-Y s_v.                        (12)

The full B2 force has positive coefficients on its two orthogonal
inward own axes. Since B has one physical circle corner, that corner
must be its positive-positive far corner in these axes. Thus

    H>-1/2, K>-1/2,
    Z_B=(H+1)(G/gamma)+(K+1)g,
    R^2=(H+1)^2+(K+1)^2.                            (13)

Indeed a negative own center coordinate would make the unique far
corner negative in that axis, contradicting the strictly positive
corresponding component of F_B. A zero center coordinate would
give two physical circle corners, already outside this case.

By H<=h and K=P.g<=1/2, equation (13) shows J<3/5. Otherwise

    R^2<=(2-J)^2+(3/2)^2
        <=49/25+9/4=421/100<17/4,

a contradiction. Consequently

    1/2<J<3/5,
    W>35/36,
    0<Delta_0<1/36,
    q<(9/2)Delta_0<1/8.                            (14)

For the W bound, R^2-J^2>389/100>(71/36)^2, the last
squared reserve being 44/129600. The q bound follows directly
from (8), because J>1/2.

The true B2 concurrence is the intersection of the original normal
lines. In its actual orthogonal frame it is

    q_B=[P.(G/gamma)](G/gamma)+(V.g)g.

Its radial proportionality to the true Z_B in (13) requires

    E(v):=[P.(G/gamma)](1+K)-(V.g)(1+H)=0.          (15)

We prove E(v)>0 continuously on the whole interval (11).

### 3.1. The closed endpoint v=0 is already strictly positive

At zero,

    E(0)=X(1+Y)-W(2-J).

Since p>1-q^2 and d in(1,61/60),

    X>1+q/2-q^2,
    1+Y>3/2-(61/60)q-q^2/2.

Both right sides are positive for 0<q<1/8. Their product minus
(3/2-(3/5)q) equals

    q/3-(301/120)q^2+(23/30)q^3+q^4/2>0,

because 1/3-(301/120)q>19/960>0. Hence

    X(1+Y)>3/2-(3/5)q.

Using q<(9/2)Delta_0 and W=1-Delta_0 gives

    E(0)>J-1/2-Delta_0(J+7/10)>0.                 (16)

For completeness, the actual circle equation gives

    J^2>1/4+4Delta_0-Delta_0^2,
    J-1/2>Delta_0(4-Delta_0)/(J+1/2)>3Delta_0,

where (14) bounds the last ratio below by 715/198>3.
Thus (16) even has the strict lower bound (17/10)Delta_0.

### 3.2. One uniform derivative bound covers the entire angle interval

Expand (15), using (12):

    E(v)=(X-W)cos(v)-(Y+h)sin(v)
       +(XY-hW)cos(2v)
       +(X^2-Y^2-h^2+W^2)sin(2v)/2.

Throughout (14) and 0<=v<=arcsin(q),

    99/100<X<259/240,
    Y<1/2,
    2/5<h<1/2,
    W>35/36,
    0<=sin(v)<1/8,
    0<=sin(2v)<1/4,
    cos(2v)>31/32.

Also Y>1/3 from p>99/100 and d q<61/480. These bounds give

    X-W<1/9,
    Y+h<1,
    XY-hW<217/1440<1/6,
    X^2-Y^2-h^2+W^2>7/5.

The last inequality follows directly from
(99/100)^2+(35/36)^2-1/2>7/5. Differentiating the exact
expanded expression, retaining the signs of the nonnegative sine
factors, therefore gives over the entire closed interval

    E'(v)
       > (7/5)(31/32)-1/72-1-1/12
        =373/1440>0.                               (17)

If X-W or XY-hW is negative, its corresponding term only improves
this lower bound. Thus E(v)>=E(0)>0, contradicting (15).

This excludes the entire perpendicular-owned-input alternative.
It also includes the endpoint g=e, G/gamma=n with an actual
CB mean P=r n+(1/2)e, r>=d: there K=1/2 is unchanged while
P.(G/gamma)=r>=d. The actual E is at least the strictly positive
expression computed at r=d. No original mean is replaced in an
equation; a lower bound is applied to its actual value.

## 4. The complete strict C-vertex return has both B-owned axes

Suppose g.n<0. Both actual pair applications at B are fixed physical
singleton points: AB strictly exposes the A vertex V because
G.j>0>G.w, and CB strictly exposes C's inner upper vertex P.
They are distinct, since V.n<1/2 and P.n=d>1.

B has one physical circle corner and is a true degree-two body.
The existing compatible fixed-tip normal selector therefore forbids
a free vertex/vertex normal on either of its incident edges. Neither
original normal is owned by the other endpoint: G is strictly
between A's two vertex axes, and g is strictly between the two C
vertex axes. Thus B owns both original directions. Their original
force lines are nonparallel by the true B2 properness theorem with
its actual boundary neighbors. Two distinct nonparallel B axes are
perpendicular. Section 3 applies and excludes this whole row.

The selector was prelisted before multipliers, at these fixed actual
points. No physical circle weight, selected normal or application is
altered after extraction.

## 5. The complete C-owned e return

It remains g=e with the entire actual point range in (4).

### 5.1. B parallel to C, including all physical shared BC means

If B is parallel to C, its actual e interval is [1/2,3/2]. Equation
(10) puts V strictly between those levels. Since V belongs to B's
boundary, it lies on a side with normal n. Its n coordinate is
less than 1/2, while B also contains P_CB with n coordinate at
least d>1. Thus V is on B's minimum-n side, and the unchanged
normal G is a positive multiple of n. The two B inputs are its
perpendicular axes n,e, so the complete endpoint of Section 3
excludes this row, with the whole actual CB mean range retained.

### 5.2. B nonparallel to C: the only additional owner conclusion

If B is not parallel to C, the actual P_CB is B's unique lowest
e vertex. Both physical pair applications are singleton points and
are distinct by (10). The same fixed-tip selector applies at the
true unique-circle B2. G is not an A axis, so it must be B-owned.
The direction e is already C-owned; no B ownership of e is claimed.

Write r=P_CB.n>=d>1 and, in the real (n,e) coordinates, let the
two actual inward unit axes of B at P=P_CB=(r,1/2) be

    f=(c,s), z=(-s,c),
    c,s>0, c^2+s^2=1,
    B=P+[0,1]f+[0,1]z.                             (18)

These cover every nonparallel B frame at its unique minimum-e
vertex. The original inward B side axis G/|G| is one of
f,z,-f,-z. We retain every actual side parameter rho in [0,1].

**Axis f.** From G.w<=0 one has p s<=q c, so s<=q<1/4.
Its actual minimum-f side is V=P+rho z. Hence
V.n=r-rho s>=d-s>3/4, contradicting V.n<1/2.

**Axis z.** Its w projection is q s+p c>0, contradicting G.w<0.

**Axis -f.** Its actual support is V=P+f+rho z. Then V.n<1/2
implies rho s>r+c-1/2>c+1/2, hence s>c+1/2. This forces
s>3/4: otherwise c>=sqrt(7)/4>1/2. But then
V.e=1/2+s+rho c>5/4, contradicting V.e<9/8.

**Axis -z.** Here V=P+z+rho f, so

    V.e=1/2+c+rho s<9/8,
    c<5/8,
    s>sqrt(39)/8>3/4.                              (19)

Use the full genuine B2 proper concurrence. The original incoming
e line through P and incoming -z line through V meet at

    q_B=(r,1/2+rho/s),
    q_B.f=P.f+rho.                                 (20)

Since P.f=r c+s/2>0, B's unique circle corner is either P+f
or P+f+z. In the second alternative its n coordinate is
r+c-s, which is positive and less than r by (19). Radial
properness would make q_B=tau(P+f+z) with tau>1. Taking the f
coordinate contradicts (20), because

    q_B.f<=P.f+1<tau(P.f+1).

Thus the only possible circle corner is P+f. The exact radial
proportionality in (20) now gives

    rho=s(r s-c/2)/(r+c),
    V.e=1/2+c+s^2(r s-c/2)/(r+c).                   (21)

The last expression is increasing in r: its derivative is
s^2 c(s+1/2)/(r+c)^2>0. At r=1, use s^2=1-c^2 and s>3/4:

    V.e>1/2+c+(1-c)(s-c/2)
        >5/4-c/4+c^2/2
        >=39/32>9/8.                              (22)

The quadratic minimum is attained at c=1/4; the final reserve is
3/32. This again contradicts (10). These four axes exhaust the
original B-owned G direction and every actual supporting mean.

Consequently the whole g=e row is excluded too, including the
separate physical shared and nonparallel singleton alternatives.

## 6. Exact all-mask conclusion and remaining obligation

The physical two-circle B mask is excluded in the preceding radial
pair theorem. Sections 3--5 exclude every unique-circle B in the
strict-negative AB feature, with the full CB support cover (4).
Thus the entire original North-domain feature G.w<0 is impossible.

Together with the separately proved G.w>0 exclusion, every surviving
North-domain certificate must have exactly

    G=gamma j, gamma>0,
    P_AB=Q+j+y w, 0<=y<=1,
    H-to-A normal w,
    A's unique circle corner Z_A=Q+w,
    C=[d,d+1]n+[-1/2,1/2]e,
    0<q=-n.w<1/4.                                 (23)

The whole original y interval and both physical B masks remain in
(23); no shared mean is changed to a convenient endpoint. In
particular this theorem does not close the zero-transverse AB side,
the whole North interface, or the original roof ABC.S family.

All nine actual units, true degrees, full original forces and
torques, selected normals, actual applications, both C physical
corners and every zero individual coefficient remain. The proof
uses only continuous analytic inequalities, exact positive rational
reserves, physical rectangle support covers and the existing
compatible fixed-tip selection. No geometry sampling, finite
exclusion packet, Lean compilation, CI, metadata edit or remote
mutation is used.

## 7. Exact operative inputs

| Source | SHA256 | Literal use |
| --- | --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 | Whole retained North chart, actual HA and AB supports, unique physical A corner and complete C return cover |
| BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md | 40b4d692d48b172bca4320a9da98a34239007a61ebcff1fa7811291548086974 | Complete positive-w AB exclusion and original full mean preservation |
| TWO_RADIAL_BOUNDARY_UNITS_EXACT_CONTACT_AND_TRANSVERSE_RETURN_BARRIER.md | a0a4f1f25dd4ae6658be21bddcca75b21a851c7fc6696672f8c8ac8426478aac | Complete physical-two-circle B / negative-w AB feature exclusion |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Original compatible unique-circle true-B2 selector only at two distinct physical singleton points |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | True B2 nonparallel proper concurrence, positive radial factor and unique-mask interior conclusion |

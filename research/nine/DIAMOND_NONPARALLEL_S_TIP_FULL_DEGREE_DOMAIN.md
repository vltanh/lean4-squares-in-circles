# Exact full-degree domain of the hub/tip diamond with a nonparallel S tip

Date: October 27, 2026.

**Status: complete new hand necessary-domain theorem; independent review
requested.** This is an exhaustive reduction, not a whole hub/tip exclusion.
It is derived from readable local physical lemmas and the actual B3
equation. In particular no zero-external-moment assumption is assigned
to either actual H4 or K3 triangle aggregate.

Keep the original nine-unit packing and compatible selected certificate,
with actual positive edges

    HK, HB, HC, KB, KC, HL, BM,
    H4,K3,B3,C2,L1,M1.

L and M are genuine S leaves at H and B. K,C have positive total
circle loads. All original forces, normals, owners, means, physical
circle masks and individual zero weights remain. Work in

    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=1105/256,

and assume B's actual two nonleaf forces are nonparallel. The high
parallel alternative has a separate complete proof in
DIAMOND_PARALLEL_S_TIP_COMPLETE_GEOMETRIC_EXCLUSION.md. The whole
low/critical domain is separately excluded by the readable
ADJACENT_LEAF_ROOT_TRIANGLE_LOW_CRITICAL_EXCLUSION.md.

## 1. Original near points and nonparallel genuine leaf directions

Each real root contains its actual inward-segment point epsilon*e_L
or epsilon*e_M. Consequently both meet the closed epsilon disk.
For any actual separating normal N directed B to H,

    epsilon*(N.e_M)<=h_B(N)<=epsilon*(N.e_L),
    -epsilon<=h_B(N)<=epsilon.                         (1)

These are support-line inequalities. They do not bound the tangential
location of an arbitrary original shared-side mean.

If either root is tilted relative to its genuine leaf, its real leaf
frame may be written

    [U-1,U] times [V-1,V], U>=V>0, U^2+V^2=d^2.

The other actual near point cannot lie in its open interior. If
U<1-epsilon, then U>epsilon, V<1-epsilon, and V<=epsilon would
give U^2>=d^2-epsilon^2>1, a contradiction. Thus all four origin
margins would exceed epsilon. That would put the other near point
in the open interior. Therefore, for each such actual tilted root,

    U>=1-epsilon, |U-1|<=epsilon,
    0<V<=2sqrt(epsilon)<13/50.                         (2)

The actual genuine directions e_L,e_M are nonparallel. Equal
directions would identify the two physical S leaves. For opposite
directions, the complete global force equation is

    alpha*e_L+beta*e_M+F_K+F_C=0.                      (3)

The real boundary pair K,C has acute physical corner pairs and
positive total loads. Hence F_K+F_C is nonzero. It would point
along one of the real radial leaves. This is excluded by the
degree-free boundary-pair cone theorem in Section1 of
ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md:
the minor center interval of a touching boundary pair contains no
third boundary center, all corner/resultant directions lie within
15 degrees of their own centers, and distinct boundary centers are
more than40 degrees apart. That theorem has no graph degree premise.
Only its complete physical statement is imported. Equation(3) is
the sum of the FULL present equations; the actual HK force cancels
internally and has not been deleted from either body equation.

## 2. The aligned genuine-tip row

First suppose the real M direction is an own B axis. Rotate it east:

    M=S(East), B=[epsilon,d] times[h-1,h], 0<=h<=1.

No actual nonleaf B normal is a side axis in the present nonparallel
row. A vertical owned normal and the physical B-H-K triangle
side-normal lemma would give both nonleaf terms the same weak
vertical sign, contradicting the horizontal leaf force. An East
owned normal gives a strictly positive East scalar product in the
full force equation. A West owned normal makes the other normal
horizontal by the full vertical balance and hence parallel.

Thus both applications are strict B vertices. The physical triangle
excludes opposite vertices. Coincident vertices and two adjacent
top or bottom vertices have either an impossible common vertical
sign or an impossible full torque. The two right vertices would
give three positive horizontal force terms. Therefore, after a
vertical reflection putting H above K, the exact full row is

    P_BH=(epsilon,h), P_BK=(epsilon,h-1), 0<h<1,
    n_BH=(-cos(phi),sin(phi)),
    n_BK=(-cos(psi),-sin(psi)),
    0<phi,psi<pi/2,
    mu_H*sin(phi)=mu_K*sin(psi),
    mu_H*h*cos(phi)=mu_K*(1-h)*cos(psi),
    h/(1-h)=tan(phi)/tan(psi).                        (4)

The two zero-height endpoints would leave exactly one nonzero
origin moment and are impossible. Since the actual K port belongs
to a physical boundary unit, its norm is at least R-sqrt(2).
The exact high-radius bound (R-sqrt(2))^2>419/1000 gives

    0<h<9/25, h-1<-16/25,
    -epsilon*cos(phi)+h*sin(phi)<=epsilon.            (5)

Both nonleaf contacts in(4) have a real neighbor-side owner: H owns
the reverse HB axis and K owns the reverse KB axis. Here is the
precise compatible selection scope. The two original applications
are distinct fixed B vertices and each is noncollinear with B's
radial leaf direction. The full true-S3 singleton determinant
prelist in Section4 of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md has no degree or load
premise at those two neighbors. For each free point normal it
excludes only finitely many directions before extraction. The two
distinct physical junction parameters remain independent, including
the matched-junction convention. Its full identity therefore rules
out a free HB or KB contact. The strict point convention excludes
a merely axis-endpoint vertex/vertex contact; the required actual
side owner is consequently at the corresponding neighbor. No mean
has been selected or altered, and H4/K3 remain their true degrees.

## 3. The tilted genuine-tip row: full root feature cover

Now suppose B is tilted relative to its real M leaf. Choose its own
axes e_1,e_2, reflecting if necessary, so its actual rectangle is

    B=[-U,1-U] times[-V,1-V],
    U=d*a, V=d*b, a>b>0, a^2+b^2=1,                 (6)

with the genuine leaf at(-U,-V), in direction(-a,-b). The strict
ordering follows from(2): U>59/60 and V<13/50. Temporarily use
coordinates in[0,1]^2 with that actual leaf vertex as origin.
The full B3 equations are

    mu*n+nu*m=alpha*(a,b),
    mu*det(P,n)+nu*det(Q,m)=0,                       (7)

where P,Q are the unchanged original applications in those own
coordinates. The physical B-H-K triangle provides two facts:
an owned side normal is nonobtuse to the other actual normal,
and two strict exposed vertices cannot be opposite. These are
pure physical conclusions, without triangle external-moment data.

An owned West or South normal is impossible by taking its scalar
product with the full force sum in(7): both nonleaf terms would
have the wrong coordinate sign. Thus only owned East or North
can occur. With owned East, the other nonparallel support must
be owned North or the strict Northeast vertex W=(1,1): Southwest
and Northwest fail the triangle dot-product test, while Southeast
has the wrong vertical force sign.

With owned North, a strict Southeast normal fails that same dot
test and a strict Northwest normal has the wrong horizontal force
sign. A strict Northeast normal is also impossible. If the North
mean is(X,1), its contribution and the W contribution give

    total moment=alpha*(b-a)-mu_N*(1-X)<0,

contrary to(7). The full original X in[0,1] remains.

If neither normal is B-owned, both strictly expose vertices.
Coincident Southwest, Southeast or Northwest vertices have an
impossible coordinate sign in(7); coincident W gives moment
alpha*(b-a)<0. Opposite vertices are physically forbidden. The
bottom and left adjacent pairs again have the wrong force sign.
For the top pair, let the W force be mu*n and the upper-left
force be nu*m. The full torque gives mu*n_y=alpha*a, whereas
the full vertical sum is alpha*b=mu*n_y+nu*m_y>alpha*a,
contradicting a>b. Thus only the right adjacent pair remains:

    P=(1,0), W=(1,1),
    n_P has positive x and negative y,
    n_W has both components positive.               (8)

This exhausts all actual normal features, including whole owned
side means and their endpoints.

## 4. Signed radial concurrence and the exact three interfaces

The two actual nonparallel support lines meet at a point q. The
full moment equation implies that q lies on B's real radial line.
Write its own coordinates from the leaf vertex as

    q=sigma*(a,b).

The pure physical proper-port lemma in Section1 of
RADIAL_TRIANGLE_CONCURRENCE.md gives
P=q+ell*n, Q=q+ell'*m with ell,ell'>=0. Only that local physical
lemma is used; the global positive-radial theorem in that file
is NOT applied to the present higher-degree triangle.

For the strict pair(8), q has height strictly between0 and1 and
x<1, so0<sigma<1/a. For East plus strict W, q_y is the actual
East-side mean in[0,1], and properness at W gives q_x<=1.
Equality q_x=1 would force q=W and a=b, so0<=sigma<1/a.
For owned East and North, their exact mean coordinates are
(1,sigma*b) and(sigma*a,1); the full torque in(7) gives this
relation and0<=sigma<=1/a. Thus throughout the complete row,

    0<=sigma<=1/a,
    t=d-sigma in[(U-1)/a,d],
    q in original coordinates=(-t*a,-t*b).           (9)

In particular t need not be positive. No positive radial
concurrence has been silently assigned to B.

The strict P port, and every owned East port, have squared norm
at most epsilon^2+V^2<241/3600<(R-sqrt(2))^2. For the East
port this uses |t|<=d, which follows from U>1/2 and(9).
Therefore the boundary neighbor K cannot use such a port. H
necessarily uses it, and the complete literal interfaces are

| Interface | Actual B-to-H support | Actual B-to-K support |
|---|---|---|
| P/W | strict P=(1-U,-V) | strict W=(1-U,1-V) |
| East/W | East at(1-U,-t*b) | strict W=(1-U,1-V) |
| East/North | East at(1-U,-t*b) | North at(-t*a,1-V) |

In the last row the full force equation gives mu_H:mu_K=a:b.
All three rows retain the proper lengths and actual mean endpoints.

In P/W, the two applications are fixed distinct vertices with
det(e_M,P)=b and det(e_M,W)=b-a both nonzero. The same complete
true-S3 singleton preselection used in Section2 therefore forces
HB to be H-owned and BK to be K-owned. In East/W, no such
conclusion is asserted for BK: its other application is a whole
actual B-owned side mean. In East/North, no neighbor ownership
is imposed merely from B owning both normals.

## 5. Exact scope retained for the whole fine family

Sections2 and3--4 are the exhaustive aligned/tilted alternatives
for a nonparallel genuine B tip. The original H4/K3/C2 forces,
both genuine leaves, every physical circle mask and all three
completion units remain. The original leaf-direction and near-point
facts of Section1 apply to every row. The domain does not assert
that one of these necessary rows is physically realizable, nor
does it count one as a closed fine family.

This fresh proof uses no absent older domain source, no numerical
pose or interval certificate, no shortened hub equation, no selected
replacement mean, and no post-extraction change to a normal. No
metadata, remote action, compilation or CI is part of the proof.

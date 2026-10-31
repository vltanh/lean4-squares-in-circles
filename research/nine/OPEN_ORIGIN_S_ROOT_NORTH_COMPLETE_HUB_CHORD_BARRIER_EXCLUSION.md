# The entire North roof return is excluded by the actual hub's corner barrier

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed exclusion of the original open-origin,
root-owned-singleton HX, North XA interface, awaiting independent full
review and root adoption. This is not a claim that the whole roof ABC.S
family or a coarse gate is closed.**

The proof keeps the same nine actual contained, interior-disjoint unit
squares, their original circle, the true X3/H3/A3/B2/C2 equations,
every original normal and actual application or shared mean, every
physical circle corner, and each individual zero circle coefficient.
It uses the physical disjointness of the actual hub H and actual B,
which is independent of whether HB is a selected graph edge.

Two force-free geometric lemmas cover all B frames at once. The first
excludes every inner-corner C return without any B mask or B force
assumption. The second handles the original C-side mean when its two
actual B support vertices are adjacent. The parallel-frame endpoints
are covered separately by their actual supporting faces.

## 1. A unit chord cannot clear a nearby square corner

Let an actual unit square have coordinates

    H=[A-1,A] x [Y-1,Y].                              (1)

Let P,V be points of another actual unit square B, with

    P_x>=A,       Y-1<P_y<Y,
    V_x<A-1/2,    V_y>Y-1.                           (2)

Suppose the open interiors of H and B are disjoint. The segment PV
belongs to B, so it cannot enter int H: every point of the actual
square B is a limit of its interior points. If P_x=A, a sufficiently
short initial subsegment from P toward V would enter int H, a
contradiction. Thus P_x>A. At its intersection with x=A the segment
must have height at least Y: its height is strictly above Y-1, and
a height less than Y would give an open subsegment in int H. Hence

    V_y>P_y,
    (V_y-P_y)/(P_x-V_x) >= (Y-P_y)/(P_x-A).         (3)

This gives two useful, complete geometric exclusions.

### 1.1. A narrow horizontal gap excludes any two points in a unit

If

    P_x-A < (Y-P_y)/3,                              (4)

then (3) gives V_y-P_y>3(P_x-V_x)>3/2. But two points of a
unit square have distance at most sqrt(2), and 3/2>sqrt(2).
This is impossible. This lemma imposes no condition on the frame,
load, physical circle mask, or contact owners of B.

### 1.2. The larger gap is still impossible for a unit-length chord

Instead suppose

    Y-P_y>6/25,
    |P-V|<=1.                                      (5)

Put ell=|P-V| and write the direction from P to V as (-c,s),
where c,s>0 and c^2+s^2=1. Condition (3) is equivalent to

    ell >= (A-V_x)/c+(Y-P_y)/s
         > (1/2)/c+(6/25)/s.                       (6)

The ordinary Cauchy inequality and c+s<=sqrt(2) give

    (1/2)/c+(6/25)/s
      >= (sqrt(1/2)+sqrt(6/25))^2/(c+s)
      >= [37/50+2 sqrt(3)/5]/sqrt(2)
       > 71/[50 sqrt(2)] >1.                      (7)

Here sqrt(3)>17/10, and 71^2-2*50^2=41>0. This contradicts
ell<=1. The proof includes equality at the square corner in the
clearance condition (3), and all possible segment directions.

## 2. The entire accepted North chart in the actual H frame

Use the unchanged North interface of
OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md.
In its notation,

    H=P+[0,1]u+[0,1]v,
    u=(-alpha,beta), v=(-beta,-alpha),
    P=(-a,-t), alpha,beta>0,
    a_H=a beta+t alpha in (0,epsilon],
    c_H=t beta-a alpha,
    0<=c_H<t<b<31/120,
    d=1+epsilon, 0<epsilon<1/60.                    (8)

Use the actual orthonormal coordinates (v,u), and abbreviate

    A_0=1+a_H, c_0=c_H.

Thus the whole actual hub is exactly

    H=[a_H,A_0] v+[-c_0,1-c_0] u.                  (9)

Both complete original H3 rows have the following uniform physical
description. In the HC-side row set zeta=0. In the opposite-vertex
row retain its actual zeta. Then

    0<=zeta<=c_0/A_0<4/15,
    L=sqrt(1+zeta^2),
    n=(v-zeta u)/L, e=(u+zeta v)/L,
    d=(A_0+c_0 zeta)/L.                            (10)

For the side row the final equality is d=A_0, because its original
radial C conclusion gives a_H=epsilon. No actual HC mean is
altered in making the auxiliary definition zeta=0. For the opposite
row (10) is exactly the accepted original radial support relation.

The actual C and its complete original CB support cover remain

    C=[d,d+1]n+[-1/2,1/2]e,
    g.e>0, g.n<=0;
    g.n<0: P_CB=d n+(1/2)e;
    g.n=0: g=e, P_CB=r n+(1/2)e, d<=r<d+1.        (11)

Both physical C circle corners and their independent nonnegative
weights are retained. In the second line the actual r is the full
original supporting mean; it is not moved to an endpoint.

The same accepted reduction gives

    A=Q+[0,1]j+[0,1]w,
    j=(-C_A,S_A), w=(S_A,C_A), C_A,S_A>0,
    J=-Q.j in (1/2,1), W=Q.w>0,
    V=P_AB=(1-J)j+(W+y)w, 0<=y<=1.                (12)

This is the complete original AB support, before assuming a sign of
its transverse force. Write h=1-J and K=W+y; thus 0<h<1/2 and
K>0. One has

    j.u=alpha C_A+beta S_A=:q_H>0,
    w.v=-q_H,
    j.v=w.u=:p_H>0.                                (13)

For the last positivity, the prior reduction gives j.n>0, and
j.e=C_A S_n+S_A C_n>0 in its actual C frame. Since
v=(n+zeta e)/L, this proves j.v>0. Consequently every actual
AB point, including both endpoints and every shared mean, obeys

    V.v=h p_H-K q_H<h<1/2,
    V.u=h q_H+K p_H>0.                             (14)

No equation has been imposed at a fictitious neighbor. The actual
pair of points used below always belongs to the same actual B.

## 3. Every strict C-vertex return crosses the actual hub

Suppose g.n<0, so its actual point is P_0=d n+e/2. Define

    rho=1/2+(c_0-A_0 zeta)/L>=1/2.                 (15)

Exact substitution of (10) gives

    P_0.v=A_0+zeta rho/L,
    P_0.u=-c_0+rho/L.                              (16)

The horizontal distance past H's outer side is therefore
zeta rho/L, and its height below H's top is 1-rho/L.
We prove uniformly that the former is less than one third of the
latter. Since c_0<4/15, A_0>=1 and L<=1+zeta^2/2,

    L^2-(L/2+c_0-A_0 zeta)(1+3zeta)
      > 1+zeta^2-(23/30-zeta+zeta^2/4)(1+3zeta)
       = 7/30-(13/10)zeta+(15/4)zeta^2-(3/4)zeta^3
      >=7/30-(13/10)zeta+(71/20)zeta^2
      >= 7/30-169/1420
       = 487/4260>0.                              (17)

The second comparison uses zeta<4/15 and includes zeta=0. The
first comparison is strict throughout. The last inequality is the minimum of the displayed
quadratic, or follows by completing its square.

Because L rho=L/2+c_0-A_0 zeta, (17) proves

    3 zeta rho<L-rho.                              (18)

In particular P_0.u lies strictly between -c_0 and 1-c_0.
For zeta>0, (18) is exactly

    P_0.v-A_0 < [(1-c_0)-P_0.u]/3.                 (19)

If zeta=0, P_0 is directly on H's outer side and strictly inside
its height interval. In either case, apply Section 1.1 to the actual
H in (9), the actual P_0 in B, and the actual V in B satisfying
(14). It contradicts interior disjointness of H and B.

This excludes the whole g.n<0 alternative, for every physical B
circle mask, every original g within that strict return cone, and
every original AB mean. No B force equation or B degree assumption
is needed in this section. The original C2 was used only in the
accepted prior derivation of the full support cover (11).

## 4. The original zero-transverse AB side leaves only the C-side return

The all-mask theorem
OPEN_ORIGIN_S_ROOT_NORTH_ALL_MASKS_NEGATIVE_TRANSVERSE_RETURN_EXCLUSION.md,
together with its preceding positive-transverse exclusion, gives
the unchanged original vector

    G=gamma j, gamma>0.                             (20)

It also supplies the whole-domain bounds

    n=p j-q w, e=q j+p w,
    0<q<1/4, p>29/30,
    W>4/5.                                        (21)

No restriction on the original y in (12) is needed here. Section 3
has excluded the strict C-vertex feature, so the complete remaining
actual CB feature is

    g=e,
    P=P_CB=r n+(1/2)e, d<=r<d+1.                  (22)

As a point of B, V is a minimum-j supporting point by (20). As a
point of B, P is a minimum-e supporting point by (22). These are
properties of the original forces and their unchanged applications.

The whole range (22) has a useful force-free description in H's
frame. From (16),

    P.v=P_0.v+(r-d)/L>=A_0,
    P.u=P_0.u-zeta(r-d)/L<=1/2,
    P.u+c_0=[rho-zeta(r-d)]/L
             >[1/2-zeta]/L>0.                     (23)

The upper bound P.u<=1/2 also follows immediately from
P.u=(1/2-zeta r)/L. Therefore

    -c_0<P.u<1-c_0,
    (1-c_0)-P.u >=1/2-c_0
                  >29/120>6/25.                   (24)

The last rational reserve is 29/120-6/25=1/600. Equations
(14), (23), and (24) give exactly the coordinate hypotheses of
Section 1.2 for the entire original C-side mean range.

## 5. All actual B frames in the remaining side feature

There are precisely three frame alternatives. Each retains the
same actual P,V and every physical circle mask.

### 5.1. B parallel to A, including any shared AB mean

Since G is a positive multiple of j, B's actual j interval is
[h,h+1], where h=1-J<1/2. The vector e=q j+p w has strictly
positive components in that common frame. Hence its minimum on B
is attained only at B's minimum-j, minimum-w corner. The actual
CB point must therefore satisfy P.j=h<1/2.

But (22)--(21) give

    P.j=r p+q/2>=d p+q/2>29/30>1/2,

a contradiction. This includes every actual AB mean on a physical
shared side, and does not impose a new supporting point on that side.

### 5.2. B parallel to C, including any shared CB mean

The actual minimum-e side of B is e=1/2. In this common frame,
j=p n+q e has strictly positive components. Its minimum on B
is the unique minimum-n, minimum-e corner. Thus the actual AB
point must have V.e=1/2.

On the other hand its actual coordinates (12) and (21) give

    V.e=q h+p K>=p W>(29/30)(4/5)=58/75>1/2,

again a contradiction. The whole actual r interval in (22),
including every physical shared-side mean, is retained.

### 5.3. B parallel to neither frame

Neither j nor e is an axis of B. Their minimum supporting points
on B are therefore unique actual vertices. Thus the unchanged V
and P are vertices of B. They are distinct: V.v<1/2, whereas
P.v>=A_0>1.

They cannot be opposite vertices. Indeed, in any orthonormal frame
of B, two nonaxis inward normals whose minima are at opposite
vertices have opposite signs in both components. Their dot product
is then strictly negative. Here j.e=q>0 by (21), so this is
impossible. The two distinct vertices are consequently adjacent,
and their physical distance is exactly

    |P-V|=1.                                      (25)

Apply the full unit-chord exclusion in Section 1.2 using
(14), (23), (24), and (25). It gives a contradiction to the
physical interior disjointness of the actual B and H.

These three alternatives exhaust every B frame. No normal selector
is used in Section 5, and neither the physical B circle mask nor
an individual circle coefficient affects this geometric cover.

## 6. Complete original North conclusion and scope

Every original strict C-vertex return is excluded by Section 3.
After the accepted full transverse AB exclusions, Sections 4--5
exclude the entire original C-side return, including both physical
shared-side possibilities, all nonparallel frames, and every actual
mean endpoint. These are the complete C return alternatives (11).

Therefore the whole original open-origin root-owned-singleton HX,
North XA interface in roof ABC.S is impossible. Both complete H3
rows, all physical A/B/C circle masks present in the retained
domain, both independent C weights, and every original contact
owner or mean have been covered. All nine actual units remain;
the contradiction uses two actual points of B and the actual H.

This closes the North interface only. Any other original root
domain or direction, the whole roof ABC.S family, and every
original family ledger remain unchanged unless separately joined
by the root with their exact existing whole-domain proofs.

The proof is hand-written continuous geometry with strict rational
reserves. It uses no numerical pose search, finite exclusion packet,
replacement mean, altered normal, deleted force, false two-force
equation, Lean compilation, CI, metadata edit, or remote mutation.

## 7. Exact operative inputs

| Source | SHA256 | Literal use |
| --- | --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 | Entire original North chart and both H rows; actual unique A corner and j=1 AB support; physical radial C and complete original CB support cover |
| OPEN_ORIGIN_S_ROOT_NORTH_ALL_MASKS_NEGATIVE_TRANSVERSE_RETURN_EXCLUSION.md | e97a96393322d9a680677314069017a9eb3d6a6204187f13c1cc7d8b20f61fdf | Complete original zero-transverse AB conclusion after both transverse signs; whole-domain q<1/4, p>29/30 and W>4/5 |

The second source pins its complete positive-transverse and radial
pair prerequisites. No additional multiplier convention, compatible
normal selection, or interpretation of a shared mean is introduced
by this final geometric proof.

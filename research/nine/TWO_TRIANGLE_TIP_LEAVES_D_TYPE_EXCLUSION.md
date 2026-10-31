# Two triangles with leaves at separate tips: every D-leaf alternative is excluded

Date: October 27, 2026.

**Status: accepted complete hand proof after two separate independent
full-source reviews in
REVIEW_TWO_TRIANGLE_TIP_LEAVES_D_TYPE_HEXAGON_2026_10_27.md and
REVIEW_TWO_TRIANGLE_TIP_LEAVES_D_TYPE_ROOTED_BLOCKS_2026_10_27.md.**
This excludes the entire S/D and D/S type domain in the sole remaining
attachment of C2.33.b2. The S/S type remains an original obligation;
no whole coarse-cell closure is claimed.

Keep the original nine physical unit squares, compatible selected
certificate, and radius window

    79/40 <= R <= sqrt(1105)/16.

The actual positive graph is

    HA,AB,BH, HC,CD,DH, AL,CM.

Thus H has true positive degree four; A,C have degree three; B,D
degree two; and L,M are genuine leaves. Every physical circle mask,
original zero weight, contact normal and mean, and both other physical
squares remain. Assume at least one of L,M is a genuine D leaf.

## 1. A general triangle consequence of the forbidden resultant ray

Let K,U,V be an actual positive unit-square triangle with all original
force and torque equations. At each vertex aggregate all forces outside
this triangle, with zero total origin moment. Let n_1,n_2 be K's actual
outward normals, P_1,P_2 its ports, and mu_1,mu_2 their positive
magnitudes. Set

    N=mu_1 n_1+mu_2 n_2.

The actual external resultant at K is -N. Suppose

    K intersect {-t N:t>=0} is empty.                   (1)

**Triangle ray lemma.** Both K normals equal an actual side axis n
of K. Their ports are distinct; their common support height h=h_K(n)
is strictly positive; and h n belongs to K.

All three actual units are contained in the original circle. No degree
or boundary-load assumption is imposed at U,V.

RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md gives nonzero,
noncollinear full external resultants. Parallel normals at a triangle
body have the same outward sign. At most one triangle body can have
a parallel pair. The complete physical proper-port lemma in
RADIAL_TRIANGLE_CONCURRENCE.md, Section 1, applies at every nonparallel
pair with the original nonnegative proper lengths.

First the common directed cycle moment cannot be zero. If it were
zero and K were nonparallel, at least one of U,V would also be
nonparallel. Their concurrences would both be O, since their two
nonparallel force lines have zero origin moment. At their shared
edge the two proper-port identities then force both nonnegative
lengths to vanish. The actual contact would be O in K, contrary
to (1).

If instead K were parallel, both normals would be the same n.
Either other body, say U, has nonparallel concurrence O. At its
K contact the proper-port identity gives P_1=-a n, a>=0.
Since N is a positive multiple of n, this is again a point of K
on the forbidden ray (1). Thus the common cycle moment is nonzero.

If K were nonparallel, RADIAL_TRIANGLE_CONCURRENCE.md would give

    q_K=tau(-N)=-tau N,       tau>0,

with both actual proper ports P_i=q_K+a_i n_i, a_i>=0.
These are exactly the hypotheses of
ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md, with this same
N and the entire forbidden ray (1). Its complete two-neighbor
center contradiction excludes the case.

Therefore n_1=n_2=n. The nonzero common cycle moment gives nonzero,
opposite-signed port moments in K's actual moment equation, so the
ports are distinct. Two distinct support points of a square in one
direction belong to a side, making n an actual K side axis.
The zero external origin moment gives

    det(mu_1 P_1+mu_2 P_2,n)=0.

Their weighted mean belongs to K and has n coordinate h=h_K(n).
It is exactly h n. Condition (1) implies h>0. This proves the
triangle ray lemma with every original mean and aggregate retained.

## 2. The D root has a shallow horizontal side

Exchange the triangles so L at A is D. Then O belongs to int A.
M cannot also be D, since its distinct root C would contain O
openly. Therefore M is S. Put

    r=R-sqrt(2), s=1-r, d=sqrt(R^2-1/4)-1,
    epsilon=d-1.

An S-leaf root contains O when d<=1, which would make C meet
int A. Hence d>1 and R^2>17/4. The D-chart bounds give

    0<epsilon<1/60,  1/2<r<2/3,  s>1/3,
    r^2-s^2>1/16.                                      (2)

See D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Section 2; its R>2
premise follows here from d>1. Every point of a physical boundary
unit has norm at least r.

Orient L east. The exact actual chart is

    A=[-s,r] times [a-1,a], 0<a<1,
    p_AL=(r,0), n_AL=e_x.

C contains its genuine inward radial-segment point epsilon v,
where v is M's unit direction. That point is outside int A.
The horizontal side heights r,s exceed epsilon, so a vertical
side height is at most epsilon. Reflect vertically to obtain

    0<a<=epsilon.                                      (3)

## 3. The actual AH port is too central for H to touch the circle

B and D are loaded: each has true positive degree two with its
two neighbors physically touching, which excludes unloaded
transmission. A,C are physically circle-clear by their genuine
leaf-root geometry. Keep H's possible circle load until its
following physical exclusion.

The purely local A-star cover in
TIP_LEAF_BOWTIE_D_NONPARALLEL_EXCLUSION.md, Section 1, explicitly
prelists arbitrary degrees and loads on the two triangle neighbors.
Here is its full argument at the original A3 star.

A vertical triangle normal is impossible: the other triangle
normal has opposite vertical sign by A's full force equation,
and the strict support-span lemma would prevent the two
neighbors from touching. If one normal is horizontal, both are;
the triangle same-sign fact and the east leaf make both west.

Otherwise both normals are nonaxis, at fixed A vertices with
distinct heights a and a-1. There is no shared-side mean in this
alternative. At a free contact the necessary determinant

    (n_1)_y det(P_2,n_2)-(n_2)_y det(P_1,n_1)=0

has nonzero coefficient (n_2)_y(P_1)_y in the first normal's
horizontal component. The two nonzero heights belong to distinct
physical junctions. The already established finite compatible
preselection removes each free normal. Each remaining contact
is genuinely side-owned by its neighbor. Opposite A vertices
cannot be used in a physical unit triangle, by the complete
proper-port/support-span lemma. The two vertices consequently
lie on one vertical A side. They cannot both be on the right,
where both triangle horizontal forces and the leaf force would
be positive. They are the two left vertices.

These are the stated local calculations and selections of the
cited source, made before extraction. They use no H clearance,
H degree-two equation, or intact opposite petal. Every original
shared-side mean is retained in the parallel alternative.

The upper-left point satisfies

    s^2+a^2 <= s^2+epsilon^2 < r^2                     (4)

by (2). In the nonparallel case it cannot be B's boundary point,
so it is the actual AH point P. In the parallel case B's port
(-s,y_B) has norm at least r and y_B<=a<=epsilon, so y_B<0.
The unchanged A moment equation mu_B y_B+mu_H y_H=0 then gives
0<y_H<=a for H's actual port. Thus in both entire alternatives,

    |P|^2 <= s^2+epsilon^2 < r^2.                       (5)

Every point of a physical boundary unit has norm at least r.
Since P belongs to H, H is physically circle-clear. Its circle
load is therefore zero for this proved reason; no physical
zero-weight corner or load alternative was discarded earlier.

## 4. The same full resultant enters both triangles

Let N=F_D+F_M, using D's original full circle resultant and M's
genuine leaf resultant. Sum the actual C,D,M force equations.
Their internal forces cancel and C is physically clear, so N
is exactly the positive sum of the H-to-C and H-to-D pair
forces. Their actual root moments also sum to zero.

The full external systems of triangle A,H,B are F_L,F_B,N.
This uses the H clearance just proved. Each has zero origin
moment. Since O lies in int A,
ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md gives, for
H's unchanged outward normal n_A toward A,

    h_H(n_A)<0,       n_A.N<0,
    H intersect {-t N:t>=0} is empty.                   (6)

For triangle H,C,D the root pair sum is this same N. Its full
external at H is F_B+F_L=-N by whole-component balance; the
other externals are the genuine F_M at C and actual F_D at D.
All external origin moments vanish. The triangle ray lemma
therefore makes both H normals to C,D equal an actual H side
axis m, with N a positive multiple of m. Equation (6) yields

    n_A.m<0.                                            (7)

No artificial force is substituted for a physical square.

## 5. One actual side has incompatible support heights

P is an actual maximizer of n_A on H. Since m is an actual
H side axis and (7) is strict, P has the minimum m coordinate
on H: in H's m,Jm frame the coefficient of m in n_A is negative.
The true unit width gives

    h_H(m)=P.m+1 >= 1-|P| >1-r>1/3.                    (8)

This includes every original AH shared-side mean.

But C lies in the outward half-plane m.x>=h_H(m), and contains
its actual point epsilon v. Consequently

    h_H(m)<=epsilon(m.v)<=epsilon<1/60,                 (9)

contradicting (8). This is a core contradiction with both
arbitrary completion squares still present.

D/D was excluded in Section 2; this proves the complete S/D
and D/S alternatives as well. The S/S family remains open:
the D-root proof of physical H clearance and the small actual
AH point is not asserted for two S roots.

All original positive forces, physical circle masks, individual
zero weights, true degrees, normals and means remain. No new
scalar certificate, numerical pose, Lean compilation, CI,
workflow dispatch or merge was used. No original checklist ID
or coarse-cell tick is changed by this manuscript.


# A nonzero-moment triangle excludes every distinct closed-origin unit

Date: October 27, 2026.

**Status: complete proposed uniform theorem, pending full root and
separate independent review.** No original graph label, coarse cell or
shared ledger is changed.

Keep the unchanged actual nine-square packing and its compatible
selected physical force certificate in

    79/40 <= R <= sqrt(1105)/16.

Every positive force, actual common application, chosen normal,
physical circle mask and zero corner-weight endpoint remains. At each
triangle body, its external system is the entire original system
outside that triangle, including any original circle load.

## 1. Exact theorem and inherited physical radial data

Let T_1,T_2,T_3 be three actual unit squares with all three positive
pair edges. Suppose the complete external force system at each T_i
has zero origin moment and the common directed triangle cycle moment
is nonzero. Let E be any other actual unit, distinct from all three,
with

    O in E,                                           (1)

where E is the closed square. No origin-interiority assumption is
made on E or on any triangle body.

**Theorem.** These hypotheses are impossible.

The complete physical radial-external theorem
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md` gives nonzero,
noncollinear full external resultants F_i with

    F_1+F_2+F_3=0.                                    (2)

At any nonparallel triangle pair, the nonzero-moment theorem
`RADIAL_TRIANGLE_CONCURRENCE.md` gives the genuine concurrence

    q_i=t_i F_i, t_i>0,                               (3)

and the unchanged common application toward T_j satisfies

    p_ij=q_i+a_ij n_ij, a_ij>=0.                      (4)

Here n_ij points outward from T_i to T_j. The positive-ray lemma in
`GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md`, Section 1,
gives an actual closed-body point

    D_i=s_i F_i in T_i, s_i>0.                        (5)

Its statement includes arbitrary complete external systems, every
parallel pair, coincident port and zero proper length. In particular
it does not require two decorated petals in its later graph caller.
At most one of the three triangle pairs is parallel.

We will use (3)--(5) to extend the entire homotopy argument of
`ROOTED_NONZERO_MOMENT_TRIANGLE_ORIGIN_UNIT_EXCLUSION.md` to (1).
The added local observation below is essential: a concurrence need
not be inside its actual square, and E need not contain a ball at O.

## 2. A radial concurrence does not enlarge a square locally at O

First, O cannot lie in the open interior of any T_i. Otherwise
interior points of the full-dimensional E approach O and enter that
open interior, contradicting physical interior disjointness.

For a nonparallel T_i, put

    K_i=conv(T_i union {q_i}).                         (6)

We claim that some radius rho_i>0 has the following property:

    K_i intersect B_{rho_i}(O) subset T_i.             (7)

If O does not belong to T_i, strict separation gives a linear
functional v with v.x>=c>0 on T_i. Equation (5) implies v.F_i>0,
and (3) implies v.q_i>0. Hence the compact convex K_i has positive
distance from O. Choose rho_i below that distance; then the left
side of (7) is empty.

Suppose instead O is on the boundary of T_i. Write its four actual
own-side half-planes as

    u_j.x <= b_j, j=1,2,3,4, |u_j|=1, b_j>=0.         (8)

There is at least one active face b_j=0. Since D_i=s_i F_i belongs
to T_i and q_i=(t_i/s_i)D_i is a positive scalar multiple of D_i,
we have u_j.q_i<=0 at every active face. Thus the whole K_i satisfies
all active half-planes of (8).

Every inactive face has b_j>0. Choose rho_i smaller than all those
positive b_j. Every point in B_{rho_i}(O) automatically satisfies
all inactive half-planes. A point in the left side of (7) therefore
satisfies all four own-side inequalities and belongs to T_i.
This proves (7), including an origin-side or origin-vertex position,
and including a D_i lying on an active face.

At a parallel triangle pair we use the actual point D_i, and all
chord replacements are inside T_i itself. For that body (7) is
available trivially with K_i=T_i and any positive rho_i.

The complete open interior of E avoids every closed T_i. Indeed an
interior point of E in a closed T_i would have nearby interior points
of T_i still inside E. Consequently (7) implies

    int E intersect B_{rho_i}(O) intersect K_i is empty. (9)

No claim is made that K_i avoids all of E far from O. Only the
finite local statement (9) is needed.

## 3. Three nonparallel pairs: use a nearby interior point of E

Let

    P=p_12,p_23,p_31,p_12                             (10)

be the unchanged actual three-port loop. Its three sides lie in the
three closed actual units. Within K_i, replace the actual chord at
T_i by the two segments through q_i. The endpoint-fixed linear
homotopy stays in K_i, including every coincident-port degeneration.

The two proper relations at an edge give

    p_ij=q_i+a_ij n_ij=q_j-a_ji n_ij,
    q_j-q_i=(a_ij+a_ji)n_ij.                          (11)

The coefficient is positive: if both lengths vanished, q_i=q_j
would be a common nonzero point on two distinct external rays,
impossible by (2)--(3). Thus p_ij lies on [q_i,q_j]. Removing these
collinear subdivisions leaves the force-concurrence triangle

    q_1,q_2,q_3,q_1.                                 (12)

Equation (2), with (3), gives strictly positive barycentric
coordinates of O in the nondegenerate triangle (12). There is
therefore a radius rho_0>0 whose open ball lies in its interior.

Choose rho>0 below rho_0 and all three radii from Section 2.
Because E is full-dimensional and O belongs to its closed square,
there exists

    z in int E intersect B_rho(O).                    (13)

All three chord replacements avoid z by (9). Their winding about z
is unchanged, while (12) has winding +1 or -1 about z. Hence the
unchanged actual contact loop P has nonzero winding about z.
This argument does not attempt to define winding at O if an actual
contact lies there; the point z is in the open interior of the
distinct actual E and avoids every actual triangle chord.

## 4. The full parallel-pair alternative

Let K be the unique parallel-pair body and I,J the other two.
Rotate so the complete external resultant F_K points east. The
two actual outward triangle normals at K are both -e_x, and their
ports have the form

    p_I=(h,y_I), p_J=(h,y_J).

Its actual moment equation makes a positive weighted mean of the
heights zero. The nonzero common cycle moment makes both heights
nonzero, so after relabeling

    y_I<0<y_J.                                        (14)

The two other pairs are nonparallel. Their genuine concurrences and
proper relations give

    q_I=p_I-a_I e_x,
    q_J=p_J-a_J e_x, a_I,a_J>=0.                      (15)

The original IJ port lies on [q_I,q_J]. Choose the actual positive-
ray point D=s_K F_K in K from (5); it has positive x coordinate and
zero height. Replacing the three square chords inside K_K=T_K,
K_I,K_J, then removing the IJ subdivision, gives the loop

    D,p_I,q_I,q_J,p_J,D.                              (16)

Both correction triangles

    conv{D,p_I,q_I}, conv{D,p_J,q_J}                   (17)

are compact and avoid O. In the first, every convex combination
using p_I or q_I with positive weight has strictly negative height;
the only possible zero-height point is D, whose x coordinate is
positive. The second uses strictly positive height. This remains
true at either zero proper length, when the corresponding triangle
degenerates. Both sets therefore have positive distance from O.

Replacing the two broken segments using (17) leaves

    D,q_I,q_J,D.                                      (18)

All three vertices are positive multiples of their respective full
external F vectors. By (2), O lies strictly inside this nondegenerate
triangle. Choose rho>0 smaller than the three local radii in Section
2, the two distances of (17) from O, and an interior-ball radius of
(18). Choose z as in (13). Every original chord homotopy and both
correction homotopies avoid z, while (18) surrounds z. Thus P again
has nonzero winding about z.

This covers both original parallel means and every proper-length
endpoint. No fictitious concurrence is assigned to K; no shared-side
mean is moved to its midpoint.

## 5. The actual unit E cannot fit inside its contact triangle

The boundary of P lies in the three actual closed T_i and therefore
avoids int E. Winding about points of the connected int E is constant.
It is nonzero at z by Section 3 or 4, hence nonzero throughout int E.

If the original ports coincide or are collinear, their triangular
loop has winding zero away from its image, an immediate contradiction.
Otherwise the entire int E lies in the bounded interior of the
actual contact triangle.

Each triangle side is a chord of an actual unit square, so its length
is at most sqrt(2). If ell is the longest side, its altitude is at
most sqrt(3) ell/2, since each of the other two sides has length at
most ell. Consequently

    area(P)<=sqrt(3) ell^2/4<=sqrt(3)/2<1=area(int E).  (19)

This contradicts the obtained inclusion and proves the theorem.
The proof uses actual contact chords throughout its final enclosure;
no perturbed drawing area, numerical pose or auxiliary physical
stress is substituted.

## 6. Uniform consequence for several triangular blocks

Suppose the selected positive graph has at least two distinct
triangular blocks. Their complete external moments vanish separately
by summing each entire attached block-cut branch, retaining every
circle force and actual common application.

`GLOBAL_CLOSURE_RADIAL_TRIANGLE_BLOCK_ORIGIN_ROUTING.md` gives at least
one actual unit containing O. For any triangle block with nonzero
cycle moment, the theorem above says that every such actual unit
must belong to that block.

A zero-moment triangular block contains O in at least two of its
closed units, by the two nonparallel concurrences and their mutual
proper port at O. Two distinct graph blocks share at most one body.
Therefore a zero-moment block cannot coexist with a nonzero-moment
block: one of its two origin-containing bodies would be a distinct
outside E for the nonzero-moment block.

Hence precisely the following two alternatives remain:

* every triangular block has zero common cycle moment; or
* every triangular block has nonzero common cycle moment, and every
  actual origin-containing unit belongs to every triangular block.

In the second alternative, two vertex-disjoint triangular blocks
are impossible. If two distinct blocks share H, their intersection
is exactly {H}; then H is the unique actual closed unit containing
O, and every other triangular block must also contain that same H.
This last statement is only closed-origin containment. It does not
silently strengthen H to origin-interior, nor discard any forest
force at H.

The zero-moment alternative remains explicit. In particular, this
source alone does not exclude several actual units meeting at O
or declare any whole bridge family closed.

No minimum-support change, new normal choice, physical motion,
Lean compilation, CI, remote action or shared-ledger edit is used.

# A nonzero-moment radial-external triangle excludes every outside origin-interior unit

Date: October 26, 2026.

**Status: accepted complete hand theorem or reduction after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `d41154aa32350cd212b33ec7dda2c18ea3237eb8cf1187db9d4dd47b84d45532`. Root review: REVIEW_C3_334_B1_TRIANGLE_AND_DIAMOND_ROOT_2026_10_27.md. Separate review: REVIEW_NONZERO_MOMENT_TRIANGLE_ORIGIN_UNIT_GLOBAL_2026_10_26.md. No
original fine label, coarse row or shared ledger is changed here.

Keep all actual interior-disjoint unit squares and the compatible
selected physical force certificate in

    79/40 <= R <= sqrt(1105)/16.

All original positive forces, selected normals, common application
means, circle masks and individual zero corner weights remain. The
external systems below are entire actual systems, not redistributed
fractions of an articulation's load.

## 1. Exact local statement and its radial-ray inputs

Let T_1,T_2,T_3 be three actual unit squares with all three positive
physical pair edges. At each T_i retain the sum F_i of every force
external to that triangle, and assume the complete external system
has zero origin moment. Its full force and moment equations hold.
Assume that the common directed triangle cycle moment is nonzero.

Let E be another actual unit, distinct from all three T_i, with

    O in int E.                                       (1)

**Theorem.** These conditions are impossible.

The theorem does not require a loaded tip, a genuine leaf, an intact
petal or a degree bound at any T_i. It uses those hypotheses only
in a later caller which supplies the nonzero cycle moment. Every
original external circle or pair force is retained at its actual
vertex. The two/three positive-edge systems are never substituted
for the full body's equation.

The full actual-external-resultant theorem
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md` gives

    F_1+F_2+F_3=0,
    each F_i nonzero, and the three directions noncollinear. (2)

At every nonparallel cycle pair, the full nonzero-moment theorem
`RADIAL_TRIANGLE_CONCURRENCE.md` gives the genuine concurrence

    q_i=t_i F_i, t_i>0,                                (3)

and its purely physical proper-port statement retains the actual
applications:

    p_ij=q_i+a_ij n_ij, a_ij>=0.                      (4)

Here n_ij points from T_i to T_j. At most one triangle pair is
parallel. A parallel pair has the same outward sign and is not
assigned a fictitious concurrence.

The complete positive-ray lemma in
`GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md`,
Section 1, applies at this arbitrary-external-system scope. It gives

    D_i=s_i F_i in the actual closed T_i, s_i>0.         (5)

It includes parallel pairs, zero proper lengths and all original
shared-side means. No D_i is assumed to be interior. That source's
later two-decorated-triangle graph is not a premise of its ray lemma.

## 2. Replacing a square chord by its radial concurrence avoids O

Because E contains O openly, O belongs to none of the other closed
actual units. Indeed a point of a closed full-dimensional square
inside another square's open interior gives overlap of their open
interiors in every sufficiently small neighborhood.

For any one of the compact convex T_i there is therefore a vector
v_i and number c_i>0 with

    v_i.x>=c_i>0 for all x in T_i.                     (6)

For example take v_i in the direction of its unique nearest point
to O. If the pair at T_i is nonparallel, (5) gives
v_i.F_i>0; then (3) gives v_i.q_i>0 as well. Consequently

    conv(T_i union {q_i}) lies in {x:v_i.x>0}.          (7)

In particular this whole convex hull avoids O, even if q_i lies
outside the actual square. Equation (7) is the reason a concurrence
outside a two-corner or higher-degree body is safe here; no assertion
of concurrence-interiority is made.

The straight actual chord between T_i's two original ports can
therefore be replaced by the two segments through q_i without
changing winding about O. Both paths have the same endpoints and
lie in the convex O-free set (7), so an endpoint-fixed linear
homotopy is sufficient. Coincident original ports and zero proper
lengths remain covered.

At a parallel body we may instead use the actual point D_i from
(5). The corresponding two-segment replacement lies in that body
itself and likewise avoids O.

Only winding about O is tracked during these replacements. The
convex hulls need not avoid the whole E; that stronger assertion
is neither needed nor made. Section 5 separately uses the actual
contact polygon's disjointness from E.

## 3. All three cycle pairs nonparallel

Let p_12,p_23,p_31 be the unchanged actual common applications.
The actual contact polygon is

    P = p_12, p_23, p_31, p_12.                        (8)

Its three segments belong to T_2,T_3,T_1 respectively. Apply the
three replacements in Section 2. The resulting loop, written
starting at q_1, is

    q_1, p_12, q_2, p_23, q_3, p_31, q_1.             (9)

At each common edge, the two proper relations give

    p_ij=q_i+a_ij n_ij=q_j-a_ji n_ij,
    q_j-q_i=(a_ij+a_ji)n_ij.

The coefficient is strictly positive. If it were zero, (3) would
make q_i=q_j a common nonzero point of two distinct external rays.
Those external vectors are independent by (2), so this is impossible.
Thus p_ij lies on the actual closed segment [q_i,q_j], including
its allowed endpoints. Removing these collinear subdivisions
changes (9) to the ordinary force-concurrence triangle

    q_1,q_2,q_3,q_1.                                  (10)

By (2)--(3),

    (1/t_1)q_1+(1/t_2)q_2+(1/t_3)q_3=0.

All three coefficients are positive. After normalization they
give strictly positive barycentric coordinates of O in that
nondegenerate triangle. Thus its winding about O is +1 or -1,
according to the chosen orientation. In particular it is nonzero.

Sections 2--3 prove that the actual contact polygon (8) also has
nonzero winding about O. No ordinary Jordan position of the
original contact means was assumed in obtaining that conclusion.

## 4. The entire parallel-pair alternative

There is at most one parallel triangle pair. Name its body K and
the other two I,J. Rotate so F_K points in direction e_x. Its
actual two outward normals have the same sign and are both -e_x.
Their unchanged ports lie on one support line:

    p_I=(h,y_I), p_J=(h,y_J).

The original K moment equation is

    mu_I y_I+mu_J y_J=0, mu_I,mu_J>0.

The nonzero common directed cycle moment makes both heights
nonzero. Relabel the two sides if needed so

    y_I<0<y_J.                                        (11)

Both other pairs are nonparallel. Their genuine concurrences are
q_I=t_I F_I, q_J=t_J F_J, with t_I,t_J>0. Properness toward K,
whose outward direction from either other body is +e_x, gives

    q_I=p_I-a_I e_x,
    q_J=p_J-a_J e_x, a_I,a_J>=0.                      (12)

In particular q_I and p_I have the same strictly negative height;
q_J and p_J have the same strictly positive height. At IJ the
actual common application is on the segment [q_I,q_J], again
by the two physical proper relations. The segment is nondegenerate
because the two heights differ.

Choose the actual positive-ray point D=s_K F_K in K from (5).
It has coordinates (x_D,0) with x_D>0. Use D for the K chord
replacement and q_I,q_J for the other two replacements in
Section 2. Removing the collinear IJ port gives the loop

    D, p_I, q_I, q_J, p_J, D.                         (13)

The triangle with vertices D,p_I,q_I avoids O: every convex
combination with positive weight on p_I or q_I has strictly
negative height. Its only possible point on the x-axis is D
itself, which has positive x coordinate. The same statement with positive
height holds for the triangle D,p_J,q_J. It remains valid if
p_I=q_I or p_J=q_J, when that triangle degenerates.

Consequently the first broken segment D,p_I,q_I can be replaced
by D,q_I, and the last q_J,p_J,D by q_J,D, without changing
winding about O. Loop (13) has the winding of

    D,q_I,q_J,D.                                      (14)

Now D is a positive multiple of F_K, and q_I,q_J are positive
multiples of F_I,F_J. The exact sum in (2) gives strictly positive
barycentric coordinates of O in the nondegenerate triangle (14),
just as in Section 3. Its winding, and hence that of the actual
contact polygon, is nonzero.

This covers arbitrary original parallel-pair means and both
zero proper lengths at I,J. It uses no invented concurrence at K,
no radial midpoint replacement and no boundary-neighbor premise.

## 5. The actual outside unit cannot fit in the contact triangle

The boundary of the actual polygon P in (8) lies in the three
closed physical triangle units. The open interior of E avoids
all three closed units and therefore avoids that boundary.
It is connected and contains O. The winding of the actual P is
therefore constant throughout int E, and Sections 3--4 make it
nonzero there.

If any of the three actual application points coincide, or if
they are collinear, their triangular loop has winding zero off
its image, already a contradiction. Otherwise P is an ordinary
nondegenerate triangle, possibly with the reverse orientation.
Nonzero winding means its entire bounded triangular interior
contains int E.

Each side of P is a chord of one actual unit square and has
length at most sqrt(2). A triangle of longest side ell has area
at most sqrt(3) ell^2/4: the other two sides are at most ell,
so its altitude to that longest side is at most sqrt(3) ell/2.
Thus

    area(P)<=sqrt(3)/2<1=area(int E).                 (15)

This contradicts the inclusion just established. It proves the
theorem, including every original port coincidence, endpoint
mean and multiple-junction degeneracy. No limiting plane routing
can create extra area: the contradiction already uses the actual
three contact chords and the unchanged open E itself.

## 6. A genuine leaf triangle cannot be disjoint from an origin-interior unit

Suppose a positive triangle A-X-Y-A has exactly one genuine leaf
at X, with true X degree three and true loaded Y degree two.
Allow arbitrary complete other forces and any original circle
load at A, provided its full external system relative to the
triangle has zero origin moment.

The complete moment lemma in
`GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md`,
Section 2, gives a nonzero common triangle moment. Its proof
includes all S/D leaves, all loaded-tip masks, both parallel
tip geometries and the critical d=1 case. The present theorem
therefore excludes every distinct actual unit E outside A,X,Y
with O in int E.

This corollary does not need to prove A physically clear first.
Its possible circle force remains in the complete external
aggregate throughout. Nor does it require an intact petal or
any particular graph outside that triangle.

## 7. Whole original C3.334.b1 middle-four-block application

Consider the entire original family (R2) in
`ROOTED_C3_334_ONE_BRIDGE_STRUCTURAL_REDUCTION.md`. Its four-body
block Q is the middle block of the core, with distinct triangle
attachment roots A and B. The triangle at B is intact. The
triangle at A is A-X-Y-A, and X has the unique genuine leaf L.
All nine actual bodies remain in this connected component.

The intact triangle has its two true degree-two loaded tips, so
`ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md` gives

    O in int B.

B is distinct from all A,X,Y because the two triangles attach
to Q at different actual roots. The true untouched Y is loaded
by the touching-neighbor transmitter obstruction; X has precisely
its two triangle contacts and its genuine leaf. Every original
positive force and circle atom at A is retained.

The complete external origin moment at A is zero. Indeed, remove
A from the actual block-cut tree and sum every unchanged moment
equation in the entire Q-plus-other-triangle branch. All its
internal pair moments cancel at their original common applications,
and all remaining circle moments are radial and zero. The surviving
moment at A is exactly that complete branch moment. A's own circle
force is radial and also has zero origin moment. X's leaf force
and Y's actual circle force have the same zero-moment property.

Section 6 now excludes the whole configuration using E=B.
The argument is independent of Q's internal graph, private load
mask, ordered attachment orbit and root degrees. In particular
it covers every C4 mask, both hub/tip attachment roles of either
root in a diamond, and K4, without applying a true degree-two
equation to a Q articulation or deleting an original Q force.

Thus the entire original (R2) domain is excluded. The proof also
covers its S/D and critical-radius alternatives before any earlier
reduction to d>1; no radius slice or circle mask is discarded.

This source leaves the separate (R3) leaf-decorated private-Q
family untouched. No standalone claim that the entire coarse
C3.334.b1 row is closed is made here.

No numerical pose, altered stress, normal reselection, reset mean,
physical motion, Lean compilation, CI, remote mutation or shared-
ledger edit is used.

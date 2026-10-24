# The three external ports orient the nonzero triangle moment

**Status: complete hand implication; root and independent full hand audits passed.**
Work in the entire remaining distinct-articulation domain of
`TRIANGLE_DISTINCT_LEAVES_DOMAIN.md`:

\[
 \frac{\sqrt{17}}2<R\le\frac{\sqrt{1105}}{16},\qquad H\ne0.
\tag{1}
\]

The positive triangle is A,B,C, with radial leaves at A and B.
A,B are physically circle-clear, C is loaded, and the leaf types are
S/S or D/S. Every actual shared-side mean and every physical circle
mask is retained.

Orient the plane so the three external circle-port groups occur in
the order A-leaf, B-leaf, C. Then the common directed triangle moment
for A to B to C to A is strictly positive. At either articulation
whose two cycle force lines are nonparallel, their intersection is
a strictly positive multiple of its leaf direction. Articulations
with parallel cycle forces are not excluded by this implication.

## 1. The external port groups and local order

Write the two radial leaf directions as e_A,e_B, and the nonzero
circle-load vector at C as m_C. Global force balance is

\[
                 \alpha e_A+\beta e_B+m_C=0,
                         \qquad\alpha,\beta>0.
\tag{2}
\]

Their directions are distinct and noncollinear by the domain theorem
and the distinct circle-resultant direction theorem. Their successive
angular gaps in the circular order are strictly less than pi.

For each of the three loaded bodies take every positive circle-corner
port. Each such body's circle corners occupy a single angular
interval, and the three intervals are disjoint in their circle order:
circle corners are less than 20 degrees from their center direction,
while distinct boundary centers are more than 40 degrees apart.
These are the exact strict estimates in
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Section 2, and
`CENTERED_INNER_ARC.md`. Each resultant direction lies inside its
own corner interval. Thus the groups' order agrees with the order
of the three directions in (2).

Attach all circle spokes simultaneously using the planar physical
embedding. Delete one triangle edge at a time. The remaining tree
has three exterior port groups, so the order of its branches at the
other triangle vertex agrees with their boundary-circle order. This
is the same crosscut order used in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md` and
`UNIQUE_POSITIVE_COMPONENT.md`. It applies to actual side means and
to the untangled physical junctions; no straight-line drawing of a
triangle through an occupied body is assumed.

## 2. No articulation port coincidences remain

Put d=sqrt(R^2-1/4)-1 and r=R-sqrt(2). Thus
\(1<d<61/60\), \(1/2<r<7/10\).

First suppose the two cycle applications at A coincide at p.
Their sum is a negative multiple of e_A, so p supports A in the
direction -e_A. Origin torque makes p collinear with e_A. For an
S articulation its coordinate is d-width_A(e_A), hence

\[
             |p|\le\max(\sqrt2-1,d-1)<r.
\tag{3}
\]

For D its coordinate is r-1, and |p|=1-r<r. But p belongs to
the circle-touching C, all of whose points have norm at least r.
Both alternatives are impossible. The argument at B is identical.

A cycle contact at a D leaf's application is also impossible. The
articulation has a side interior there, occupying a half-plane; the
radial D leaf occupies a right-angle sector symmetric about the
outward side normal. The two remaining sectors each have angle
45 degrees, too small for another unit square's tangent cone.

For an S leaf, a C contact at its inner application is excluded by
the shallow-inner-face boundary-neighbor theorem in
`C7_FORCE_POLYGON.md`, Lemma 2.1. If instead AB meets an S leaf's
application p=(d,0), the S leaf occupies the right half-plane there.
A and B must both have vertex tangent cones and fill the two left
quadrants. After labeling, they are exactly

\[
           [d-1,d]\times[0,1],\qquad
           [d-1,d]\times[-1,0].
\tag{4}
\]

The other articulation in (4) cannot support any different radial
leaf when d>1. Its side normals would require radial support values
d, d-1, 0, or 1. Only the east value d can be an S application,
and that repeats the original physical S leaf. No value can be the
D radius r, with the proper radial sign. Of its vertices, (d,-1)
has norm greater than d; (d-1,0) and (d-1,-1) have positive first
coordinate but belong to left outward normal cones, so neither is
a radial outward support. The remaining vertex (d,0) again repeats
the original leaf. The reflected upper half-square is identical.
Thus (4) cannot occur in this two-distinct-leaf layout.

Consequently at each articulation the leaf application and both
cycle applications are distinct. Their outward supporting normals
have the same weak cyclic order as their boundary applications.

## 3. Circle forces preserve the local order at C

At C, the positive circle normals are the radial vectors of its
positive circle corners. They are genuine outward supporting normals
of C. If there are two, they occur in the outward-normal order at
the two ends of the outer radial S face. No contact with a unit
neighbor can lie on that outer face, whose support exceeds R-1,
and a containing-circle vertex cannot be shared. Thus the two pair
normals are outside this consecutive circle-normal interval.
Replacing the circle vectors by their positive sum m_C preserves
their order relative to both pair normals. This includes one-positive-
corner masks on a body with two physical circle corners.

If the two C applications coincide at a vertex, their common-normal
intervals still have the order of the two neighboring tangent sectors.
Here is the elementary endpoint check. A neighbor sector with angular
interval [a,a+u], u>=pi/2, permits inward normal directions only in
[a+u-pi/2,a+pi/2]. If the next disjoint neighbor sector starts at b
with b>=a+u and has width v>=pi/2, its first allowable normal is
b+v-pi/2>=a+pi/2. The two intervals are therefore ordered, including
their common endpoint if present. Intersecting with C's outward
normal cone preserves this order. The strict point-normal convention
and any fixed side axes are compatible with it.

Hence the local group order at C is

\[
                         m_C,\ n_{CA},\ n_{CB},
\tag{5}
\]

where the pair normals point outward from C. The corresponding
orders at A and B are e_A,n_AB,n_AC and e_B,n_BC,n_BA.

## 4. The moment sign from C, including parallel pair forces

Suppose first that the C pair force lines are nonparallel. Their
concurrence q_C is a positive multiple of m_C. This uses precisely
the general-neighbor normal-line part of the degree-two concurrence
calculation cited in the domain theorem; it does not require A or B
to touch the circle.

Three noncollinear vectors with positive coefficients summing to zero
have every successive angular gap strictly less than pi. Apply this
to C's two pair forces and m_C, in the order (5). It gives

\[
                     \det(m_C,n_{CA})>0.
\]

The contact point p_CA differs from q_C along n_CA. Therefore

\[
               H=\mu_{CA}\det(p_{CA},n_{CA})
                 =\mu_{CA}\det(q_C,n_{CA})>0.
\tag{6}
\]

If C's pair forces are parallel, the same-sign alternative is radial
S or D; opposite signs would require an impossible outer contact.
Radial D has both contacts at its inner vertex with radial normal,
giving H=0, already excluded. Thus C is radial S. Rotate its radial
direction east. Both pair forces point inward, with normal -e_x,
and their actual means are (d,y_A),(d,y_B). The order C,A,B puts
y_A>y_B along the inner face. These means are distinct because
equality and torque would give H=0. Origin torque says

\[
                       \mu_{CA}y_A+\mu_{CB}y_B=0.
\]

Thus y_A>0>y_B and
\(H=\mu_{CA}y_A>0\). The entire variable-mean parallel chart
is retained in this sign argument.

## 5. Positive radial concurrence at a nonparallel articulation

Suppose the two cycle force lines at A are nonparallel. Their
intersection q_A lies on the radial leaf force line by torque about
that intersection. Write q_A=t_A e_A. Positive three-force balance,
with the order e_A,n_AB,n_AC, gives

\[
                         \det(e_A,n_{AB})>0.
\]

Using (6) and the common triangle moment,

\[
 0<H=\mu_{AB}\det(p_{AB},n_{AB})
      =\mu_{AB}t_A\det(e_A,n_{AB}),
\]

so t_A>0. The argument at B is identical. Reflection changes both
moment and determinant signs, so positivity of these radial scalars
is invariant under a later coordinate reflection.

This proves the stated complete implication. It does not assert that
q_A or q_B lies inside its articulation, and it does not discard the
parallel-force charts at either articulation. Those physical cases
must still be included in any full closure.

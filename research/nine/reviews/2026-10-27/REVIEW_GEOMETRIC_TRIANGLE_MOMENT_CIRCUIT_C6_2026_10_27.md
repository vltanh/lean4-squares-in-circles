# Full independent review: geometric triangle moment circuit

Date: October 27, 2026.

Reviewer: `c6_side`, separate from the source author.

**Decision: ACCEPT the complete geometric theorem.**

Reviewed source:

`ROOTED_GEOMETRIC_TRIANGLE_MOMENT_CIRCUIT_EXCLUSION.md`

Frozen SHA-256:

`fc55c0a5395b4cca051299416c99a7532df4f9ae440daee9ab9badc4d29ffbc3`

I read all 299 lines and independently reconstructed each algebraic,
physical and winding step. I also read the complete physical
proper-port theorem, its side-normal/support-span prerequisite, the
positive-ray proof from which the argument is transferred, and the
older nonpositive-ray cap proof. I checked the full stated scope of
the geometric theorem and the nonradial face-sign invocation in the
new private-diamond caller. No correction is required.

## 1. Auxiliary coefficients do not assert a new physical stress

The theorem starts with three actual pairwise touching squares,
specified actual common points and common separating normals, and
three directed line moments of one nonzero sign. Positive original
edges retain their original selections. A physical zero-stress edge
is permitted only with a specified real contact and normal; the
theorem does not assign it a positive physical force.

Multiplying the three geometric normals by the inverse absolute
line moments makes the three directed moments equal to H=+1 or -1.
The auxiliary F_i are exact differences of those three vectors and
sum to zero. Each local pair has zero total origin moment. These
are elementary geometric identities; neither the proof nor the
caller requires a modified physical equilibrium or an allocation
of a higher-degree body's circle load. All following arguments use
only those identities, positive coefficients and unchanged geometry.

## 2. Noncollinearity and positive concurrences

The proper-port theorem is applicable at this scope. I checked its
whole owner cover: an actual side axis uses the nonobtuse-normal
lemma; strict vertex supports are either equal or adjacent, while
opposite vertices are excluded by the strict support-span bound.
All side means and zero proper lengths are included. This proof has
no degree, load, selected-stress or containing-radius premise.

An auxiliary F_i cannot vanish, because that would make the two
outward normals opposite, separating the other two touching units.
If the F_i were collinear, a parallel pair would make all three
edge vectors collinear, requiring impossible alternating outward
signs around the odd cycle. Otherwise all three actual concurrences
lie on the same line through O. Properness gives nonnegative
increments along the actual edge vectors. Distinct concurrences
would again force all edge vectors to be collinear. If they all
coincide, all proper lengths vanish, and the three physical squares
have the same contact vertex. A positive sum of two nonparallel
vertex normals lies strictly inside that vertex normal cone. Two
of the three same-line F_i have the same sign, so their closed
right-angle tangent cones would both lie strictly within one open
semicircle. Their interiors cannot then be disjoint. This completes
the noncollinearity proof without an external-force theorem.

For three nonparallel pairs, equal directed moments imply
q_i=t_i F_i. None of these coefficients is zero because H is
nonzero. Properness and pairwise independence make all three edge
increments strictly positive. I independently solved the cyclic
linear equations and obtained exactly the three positive products
over Lambda displayed in the source.

For the single parallel pair, the two unchanged port heights are
strictly opposite by their positive weighted zero moment. The
other two concurrences have those same heights. Their mutual
proper increment has positive vertical component, and the exact
auxiliary difference equations give matching signs for their F_i
components. Both concurrence coefficients are therefore positive.
No fictitious concurrence is assigned to the parallel square.

## 3. Positive-ray geometry, including the weak side endpoint

I verified the entire positive-ray argument afresh. Under avoidance
of the open positive F ray, the weighted actual port combination
P_bar=q+M/W lies on the positive M ray. The coefficient cannot
vanish: at a boundary mean, every incident own outward side normal
has strictly positive dot product with M, since both actual ports
lie on that side and their normals are nonparallel. Thus -M enters
the square strictly, including at a vertex. This justifies the
boundary-origin endpoint not covered by a strict separation alone.

Choosing an own coordinate interval [a,a+1] with a>=0, the same
face fact gives M_x>0. Both actual normal x components are positive
and both ports lie on the far side A=a+1>=1. Properness and the
opposite ray points place zero between their transverse heights.
The exact zero-moment equation makes M_y/M_x a positive weighted
mean of those heights divided by A. Substituting the proper-port
slopes gives

    P_i.n_i >= A/(n_i)_x >= 1/(n_i)_x

for both normals, including one horizontal normal and every actual
side mean. The upper port has nonnegative slope bounded by its
own height ratio; the lower port has the reflected inequalities.
No strict transverse sign is assumed at an endpoint.

The containing-disk support bound is geometric and yields
(n_i)_x>60/61. Each actual neighbor center has normal coordinate
at least 3/2 and norm less than 91/60. The stated common cap
rectangle then has squared diameter 52124381/53582400<1,
contradicting the incircle center-distance lower bound for two
distinct actual neighbors. The case A=1 remains strict because
the radius bound d<61/60 is strict.

At a parallel square, the two distinct opposite-height ports force
an own support side. A support height at least one would put its
two actual neighbors in the smaller cap of squared diameter less
than 29/144. Therefore its support height is below one, and an
actual negative-normal-axis point lies in its open interior. This
is the required positive auxiliary-ray point, with its original
means retained.

## 4. Winding and the full outside-unit contradiction

Because O lies in the open interior of the outside actual unit E,
it lies in none of the closed triangle squares. Each square has a
strict separating half-plane from O. Its actual positive F-ray
point and its positive concurrence lie in that same half-plane.
The contact chord can therefore be replaced through the concurrence
by an endpoint-fixed homotopy avoiding O, whether the concurrence
is inside or outside its square. The homotopy need not avoid E;
the source explicitly uses only the avoidance of O here.

For three nonparallel pairs, the actual edge means are on the
segments joining the corresponding concurrences. The resulting
triangle has O strictly inside by the positive barycentric identity
q_1/t_1+q_2/t_2+q_3/t_3=0. Noncollinearity excludes a degenerate
auxiliary triangle.

For one parallel pair, use its actual positive-ray point D_K.
The lower and upper correction triangles each have only D_K on
the zero-height axis, at positive x. They avoid O even in their
degenerate limits. Removing those corrections leaves a triangle
of three positive auxiliary-ray points, with the same strictly
positive barycentric argument. Thus the original actual contact
loop has nonzero winding in every case.

Every original loop side is in an actual triangle square, so the
loop avoids the entire open interior of E. Its winding is constant
on that connected interior and nonzero at O. A degenerate original
contact loop is impossible; otherwise the actual contact triangle
contains the entire open unit E. Each side is a chord of a unit
square and has length at most sqrt(2), giving maximal area
sqrt(3)/2<1. This contradicts containment of an open unit of area
one. The reasoning is independent of the actual degrees of the
three triangle bodies.

## 5. Arithmetic and the exact caller scope

Nine independent exact rational checks passed, covering the strict
radius/center margin, the transverse estimate, both exact cap
diameters, and the normal-angle and area reserves. These only
confirm the displayed constants; the proof is a whole-domain
geometric argument with no numerical sampling.

In `ROOTED_C3_334_ONE_BRIDGE_PRIVATE_DIAMOND_EXCLUSION.md`, the
nonradial caller derives the unchanged moment flow c=b-a from the
full original zero external moments. If (a,b) is nonzero and a!=b,
the two face triples (a,a,a-b) and (b-a,b,b) include one with a
strict common sign: select the one whose path moment has larger
absolute value, retaining the equal-absolute/opposite-sign endpoint.
Positive original magnitudes preserve these geometric moment signs.
The outside origin-interior unit A is distinct from all diamond
units. This is a valid invocation of the reviewed theorem, with
all actual contact points, normals and higher-degree forces kept.

The separate radial alternatives and the caller's entire diamond
assembly require their own reviews. This source itself correctly
claims no standalone original graph closure and no C4 or coarse
cell closure.

**Final decision: full independent ACCEPT at the pinned version.**

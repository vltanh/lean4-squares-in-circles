# n=9: physical contact-point stresses, joint planar incidence, and discrete transmitters

**Status: hand necessary-condition theorem for every unrestricted global
minimizer.** This strengthens the earlier angular certificate by placing
each contact force at a point in the **actual common square intersection**.
Its contact-point incidence network is planar and satisfies both force
and angular balance. No common perpendicular separating frame is assumed.

This is a **different graph** from the body-to-body support in
PLANAR_STRESS_CORE.md: here true multi-square contact points are retained
as junction vertices. We do not claim the body-pair graph is planar or
that its force-and-torque-balanced stress has only 19 atoms. The bound
here is **27 physical contact/circle atoms before aggregation** for nine
squares. The unrestricted sharp bound `q>=1105/256` remains OPEN.

## 1. Goal: local feasible constraints with physical contact gradients

At a global minimizing packing translate the circle center to zero and
use local orientation angles. For square `i`, write `c_i` for its center,
`u_i,v_i` for its orthonormal side axes, and `a_{i,k}` for its four
half-side corner offsets. Circle constraints are

\[
 C_{i,k}=\|c_i+a_{i,k}\|^2-q\le0. \tag{1}
\]

We construct a finite, smooth, local feasible branch through the
minimizer such that every active pair constraint has the following
center and angular derivatives at the base point:

\[
 \begin{array}{c|cccc}
 &c_i&c_j&\theta_i&\theta_j\\ \hline
 \nabla B_e&d_e&-d_e&d_e\cdot J(p_e-c_i)&-d_e\cdot J(p_e-c_j).
 \end{array}                                                \tag{2}
\]

Here `p_e` is a **genuine common point** of the two squares and `d_e`
is a common unit supporting normal pointing from square `i` toward
square `j`. The tangent line through `p_e` separates the two squares.
The force coefficient in (2) is one; the eventual nonnegative
multiplier supplies its magnitude.

Noncontacting pairs need no active inequality: because their closed
squares have positive distance, a sufficiently small open neighborhood
preserves their nonoverlap. There are finitely many such pairs, so choose
one neighborhood working for all. We treat every touching pair below.

## 2. Complete contact-type construction

Two convex squares with disjoint open interiors intersect in either
an empty set, a single point, or a nondegenerate segment. Their
intersection cannot contain area. A point contact is a vertex of
at least one square: two relative side-interior points would instead
give a nondegenerate shared side segment. The following cases exhaust
all contacts, including angle ties.

### 2.1 Vertex against relative interior of an edge

Let `i` supply the supporting edge and let its normal `d_i(theta_i)`
point toward `j`. The unique contacting corner of `j` is
`c_j+a_j(theta_j)`, and define

\[
 B=\tfrac12-d_i(\theta_i)\cdot(c_j+a_j(\theta_j)-c_i)\le0. \tag{3}
\]

That corner uniquely minimizes the projection of `j` on `d_i` at
the base point. Otherwise a whole side of `j` would lie on the
supporting line through the relative interior of `i`'s edge and
would share a positive-length segment with `i`, contrary to this
case. Uniqueness persists in a small angle neighborhood. There
(3) is an actual separating-axis inequality, so it ensures physical
nonoverlap. It is active at the common point `p`.

Differentiating (3), using `d_i'=Jd_i`, gives (2). In particular,
`-Jd_i dot(p-c_i) = d_i dot J(p-c_i)` is the owner's angular term.
The supporting normal rotates with its owner; it has not been frozen
incorrectly.

### 2.2 A single point that is a vertex of both squares

There is a unit supporting normal `d` that exposes this vertex
**uniquely in both squares**, as the maximum on `i` and the minimum
on `j`. To see this, their two closed right-angle tangent sectors
cannot share a nonzero boundary ray: a shared ray would give a
positive-length common side segment. The two sectors are disjoint
except at zero, so a line can strictly separate their directions.
Its normal lies in the interiors of the two appropriate normal cones.

Fix one such `d`, and retain the two corresponding corner labels.
In a small angle neighborhood they remain the unique extreme corners.
Use the smooth inequality

\[
 B=d\cdot(c_i+a_i(\theta_i)-c_j-a_j(\theta_j))\le0. \tag{4}
\]

It is a true separating condition throughout this neighborhood.
At the base point both displayed corners equal the actual common
point `p`, and differentiation gives exactly (2). The fixed direction
need not be one of the square side axes; any actual supporting normal
is legitimate. We are not asserting an owner-axis classification here.

### 2.3 A positive-length common side segment

The frames agree modulo quarter turns because the shared side lines
are parallel. Choose local coordinates and corner labels so at the
base point `c_i=(0,0)`, `c_j=(1,t)`, both frames are axis-aligned,
and `0<=t<1`. The case `t<0` is its reflected version. This local
translation is only a description of pair geometry, not a change of
the global disk center in the optimization.

The two endpoints of the actual intersection segment are

\[
 p_-=(1/2,t-1/2)=c_j+(-u_j-v_j)/2,
 \qquad p_+=(1/2,1/2)=c_i+(u_i+v_i)/2.                     \tag{5}
\]

For perturbed poses use **two**, not all support vertices, in the
smooth constraints

\[
\begin{aligned}
 B_-&=\tfrac12-u_i\cdot(c_j+(-u_j-v_j)/2-c_i)\le0,\\
 B_+&=\tfrac12+u_j\cdot(c_i+(u_i+v_i)/2-c_j)\le0.
\end{aligned}                                             \tag{6}
\]

**Lemma 2.1 (two-endpoint sufficient branch).** The conjunction (6)
ensures physical nonoverlap in a neighborhood of the base pose.
Both base gradients are physical contact gradients (2), at `p_-`
and `p_+` respectively.

*Proof.* Put `delta=theta_j-theta_i` in a chart with `|delta|<pi/2`.
If `delta<=0`, the corner `(-u_j-v_j)/2` is a minimum of the
projection of square `j` on `u_i`. Then `B_-<=0` alone is a full
separating-axis inequality owned by `i`.
If `delta>=0`, the corner `(u_i+v_i)/2` is a maximum of the
projection of square `i` on `u_j`. Then `B_+<=0` alone is a full
separating-axis inequality owned by `j`. At `delta=0` both statements
hold, including ties. Thus requiring both inequalities is sufficient
for either sign of the relative angle; no differentiability of an
absolute-value support maximum is needed.

At the base pose `u_i=u_j=d=(1,0)`. In `B_-`, the contact corner
is the actual common point `p_-`; differentiating the owner's normal
and the other corner gives (2). For `B_+`, the roles of the two
owners are reversed, but the gradient with respect to the left center
is again `+d`, that with respect to the right center `-d`, and their
angular terms are exactly those in (2) at `p_+`.

If `t=0`, both endpoints in (5) are still actual common points and
the same proof works. If `-1<t<0`, reflect the construction and use
the upper contacting corner of `j` and the lower contacting corner
of `i`. Contacts of length zero belong to case 2.2. QED.

**Scope of this construction:** (6) is a smooth **sufficient local
feasible branch**, not a claim that every nearby feasible packing
must satisfy both inequalities. Global minimality on all packings
implies minimality on this branch, which is exactly what is needed.

## 3. Regularity and the physical equilibrium theorem

Use these pair inequalities for all contacts and (1) for all corners.
Shrink the open neighborhood so every point satisfying them is a
physical packing, including the originally noncontacting pairs.
The minimizing pose is a local minimum of `q` in this smooth branch.

The velocity `dot c_i=c_i`, `dot theta_i=0`, `dot q=K` with large
enough `K` strictly decreases all active circle constraints. At any
active physical contact row its derivative is

\[
 d_e\cdot(c_i-c_j)=-(h_i(d_e)+h_j(d_e))\le-1.              \tag{7}
\]

Thus the strict active-direction hypothesis of
SPARSE_MINIMIZER_STRESS.md, Lemma 3.1, holds. Its elementary conic
argument produces normalized nonnegative circle multipliers
`lambda_{i,k}` and physical contact-row multipliers `mu_e`.

Let `p_{i,k}=c_i+a_{i,k}`. Write `s_{i,e}=+1` if `e` is oriented
from `i` and `-1` if it points into `i`. Then

\[
\begin{aligned}
 \sum_{i,k}\lambda_{i,k}&=1,\\
 2\sum_k\lambda_{i,k}p_{i,k}
      +\sum_{e\ni i}s_{i,e}\mu_e d_e&=0,\\
 2\sum_k\lambda_{i,k}p_{i,k}\cdot J(p_{i,k}-c_i)
      +\sum_{e\ni i}s_{i,e}\mu_e d_e\cdot J(p_e-c_i)&=0.
\end{aligned}                                             \tag{8}
\]

Every positive circle atom is at a vertex on the containing circle,
and every positive contact atom acts at a point
`p_e in S_i intersection S_j` with an actual common support normal.
These are **simultaneous force and angular balances**.

The gradient of each active row is orthogonal to the infinitesimal
simultaneous rotation

\[
 T=(Jc_1,\ldots,Jc_n,1,\ldots,1,0).
\]

For contact rows this follows directly from (2): the two center
and two angular terms cancel. It holds even for the fixed-normal
vertex/vertex row (4), although its entire local branch need not be
rotation-invariant away from the contact. For a circle row the
sum is `2 p dot Jp=0`.

Consequently conic thinning in the `3n`-dimensional subspace gives

\[
 \#\{\text{positive circle atoms}\}
   +\#\{\text{positive physical contact atoms}\}\le3n.       \tag{9}
\]

**Theorem 3.1 (physical minimizer stress).** Every unrestricted
minimizer of nine unit squares admits a nonnegative normalized
physical contact-point stress satisfying (8), with at most **27
positive scalar atoms** before aggregation. It exactly attains the
center-eliminating dual, now allowing any selected true common support
normals, not only the own-axis normals of the older encoding.

*Proof of exact dual attainment.* For fixed frames each true contact
normal yields the valid linear center constraint
`d dot(c_j-c_i)>=h_i(d)+h_j(d)`, tight at the base packing. The
center equations in (8), positive circle-corner complementarity and
the scalar completed-square identity are exactly the proof in
SPARSE_MINIMIZER_STRESS.md, Section 5. QED.

For a side/side contact with two positive endpoint atoms, their
normals agree at the base pose. Combine their weights and replace
the two application points by their weighted average. The average
lies in the true shared segment and preserves both force and moment.
There is now one positive physical force/application point per
positive body pair, without increasing the atom count.

## 4. A planar incidence network retaining all angular balances

Create one node for each stressed square center and one junction node
for every **distinct actual application point** after aggregation.
For each positive pair force at `p`, join both incident square centers
to the junction `p`. Merge duplicate body-to-junction incidences.
Each incidence carries the sum of its signed force vectors; the
force at a square points in its outward normal cone at that contact.

These sums cannot vanish accidentally: a square's outward normal
cone at a side point is a ray and at a corner is a pointed right-angle
cone. A nonempty sum of positive forces in that cone is nonzero.
At every contact junction the incident vectors sum to zero, by
pairwise cancellation of action/reaction terms. At every body node
(8) remains unchanged. All force applications remain at the same
geometric points, so **all angular balances are preserved**.

**Lemma 4.1 (straight-line contact incidence).** This incidence
network is planar. A contact junction has degree between two and
four. All circle-loaded square nodes are incident to the exterior
face.

*Proof.* Join a square center to each of its application points by
a straight segment. Except for its contact endpoint, this segment
lies in the open square. Distinct square interiors are disjoint,
so two such segments cannot cross outside their common contact node.
Within one square, different boundary points determine different
rays from its center, so the segments meet only at that body node.
This is a straight-line planar incidence drawing; no four-body
junction needs to be replaced by crossing pair edges.

At most four interior-disjoint squares can contain one point, since
each contributes an interior angle of at least pi/2. A nonempty
balanced contact junction has at least two incident squares. A
circle-contact vertex belongs to only one square, by the strict
inward-sector argument in PLANAR_STRESS_CORE.md. The segment to
that vertex and its outward continuation expose its square-center
node to the exterior face without crossing the incidence drawing.
QED.

A connected positive body-pair component can be retained and
renormalized before making the incidence drawing. It has at least
two distinct circle-loaded squares, by the boundary-barycenter
argument in SPARSE_MINIMIZER_STRESS.md. Unstressed squares remain
physical obstacles and count toward the total of nine; they must
not disappear from the eventual completion-capacity proof.

**What is newly joint:** this <=27-atom certificate has physical
force points, angular equilibrium, and a planar **contact-incidence**
network simultaneously. It does NOT prove that the corresponding
simple body-to-body graph is planar, nor that the <=19-term simple
planar certificate can be chosen torque-balanced.

## 5. An unloaded two-force square has a discrete orientation

After aggregating each positive body pair to a single physical
contact point, consider a square `S` with zero circle weight and
exactly two positive incident body-pair forces. Let their physical
application points be `p_-,p_+`.

**Lemma 5.1 (edge-normal or diagonal transmission).** Its two
normal directions are opposite, the force magnitudes agree, and
relative to the force direction `d` the square has precisely one
of two orientation types:

1. `d` is a side normal; the two application points are on opposite
   parallel sides at matching transverse coordinates, with
   `p_+-p_-=d` and projection width **1**.
2. `d` is a square diagonal direction; the two application points
   are opposite vertices, with `p_+-p_-=sqrt(2)*d` and projection
   width **sqrt(2)**.

*Proof.* Force balance gives the equal opposite forces `+mu*d`
and `-mu*d`. Angular balance gives

\[
                  d\cdot J(p_+-p_-)=0.                    \tag{10}
\]

The two actual contact normals support the square in opposite
directions. Thus `p_+` and `p_-` are its maximum and minimum support
points in `d`, and (10) makes their difference parallel to `d`.
They cannot coincide because the projected width is positive.

If `d` is a side normal, the width is one and collinearity gives
case 1. Otherwise both support points are unique opposite vertices;
writing the side axes as `u,v`, their difference is `+/-u +/-v`.
Its length is sqrt(2), and it is parallel to `d` only if
`|d dot u|=|d dot v|=1/sqrt(2)`. This is exactly a diagonal direction,
which gives case 2. These cases exhaust all support directions of
a square. QED.

This is a whole-angle result: no approximate tilt interval and no
numerical minimization appears. Pure translational equilibrium alone
would not force this discrete orientation.

## 6. Exact square-ended transmission-path labels at q<=Q

Follow a path in the positive **body-pair graph**, with retained
endpoint squares `A,B`, whose internal squares all have zero circle
weight and degree two in that graph. Their force magnitudes agree
and their normals have a consistent common direction `d`. Consecutive
squares touch at the actual application point on that path. The gap
identity is

\[
 d\cdot(c_B-c_A)=h_A(d)+h_B(d)+\sum_{i\text{ internal}} w_i(d),
       \qquad w_i(d)\in\{1,\sqrt2\}.                       \tag{11}
\]

No such path closes to its own starting square: every directed
contact gap is positive. If `q<=Q`, all square centers have norm
strictly below `61/40`, so the left side is less than `61/20`.
Both endpoint halfwidths are at least 1/2. Therefore:

- three internal squares are impossible, since they require a gap
  at least `1+3=4`;
- two internal squares can occur only if **both are side-normal**,
  since one diagonal would require `1+1+sqrt(2)>61/20`;
- one internal square may be side-normal or diagonal;
- no internal square is also possible.

Thus the internal reserve has exactly the four allowed labels

\[
                         \boxed{0,\;1,\;\sqrt2,\;2}.       \tag{12}
\]

The endpoints in (11) are **squares**, not arbitrary contact-junction
nodes. Do not apply the center-diameter proof to a path whose endpoints
are junction points on the boundary of several squares. Similarly,
contracting these paths in the body-pair graph is not asserted to
preserve a simple planar drawing when different pairs share a junction;
retain the incidence network if planarity is used.

## 7. Gate effect and verification boundary

**CLOSED:** the missing physical-lever bridge for a simultaneous
force/angle certificate. Every unrestricted minimizing configuration
has a <=27-atom **physical** stress and a planar contact-point incidence
network, with circle-loaded bodies on the exterior face. Its unloaded
degree-two body transmitters have only side-normal or diagonal frame
types, yielding the discrete square-ended path labels (12).

**STILL OPEN:** a sharp exhaustive inequality for all physically
realizable nine-square networks/completions. The network and its
unstressed remaining squares still carry continuous coordinates and
angles at retained branching/loaded squares. Neither 27 atoms nor
four path labels makes that inequality automatic.

The rational checks in `check_physical_contact_stress.py` verify the
actual force application points and all physical angular balances on
the committed oblique record witness, and the two endpoint/support
identities used in Lemma 2.1 for exact rational rotations. They are
regression checks, not universal optimality or a substitute for the
case-complete hand arguments above. No Lean, CI or independent full
manuscript audit is claimed.

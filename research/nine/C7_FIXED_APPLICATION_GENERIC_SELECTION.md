# Generic normals remove free vertex contacts at fixed-application C7 bodies

**Status: complete simultaneous-selection implication; independent hand audit passed.**
Work with a physical packing in

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\]

At every point-only vertex/vertex contact whose common-normal cone has
nonempty relative interior on the unit circle, call a normal in that
open interval a **free normal**. The normals can be chosen simultaneously,
before a physical stress is selected, so that the following body cannot
occur in an all-boundary positive C7 component:

* it has a unique physical circle corner;
* its two positive incident contacts have fixed actual application points;
* at least one of those contacts has a free normal.

A fixed application point means a point contact, including a genuine
vertex/side contact. A positive-length common side is not fixed: its
aggregate application can vary along the common segment, and is
explicitly outside the assertion. Bodies with two physical circle
corners are also outside the assertion. Zero circle multipliers are
retained throughout.

This is a generic-selection reduction. It does not assert that every
physical stress on every initially chosen set of vertex normals already
has the stated property. The normals must be selected first, followed by
the existing stress extraction and positive-component selection.

## 1. Geometric inputs and notation

Fix one prospective degree-two circle-touching body S. Its two incident
circle-touching neighbors meet it at fixed points p and q. The points
are distinct: no point belongs to three circle-touching squares in this
radius window. Write n and m for the unit outward common normals from S
at p and q, respectively. Suppose n is a free vertex/vertex normal.

The following previously proved physical facts are used:

1. A contact between two circle-touching squares is nonradial:
   \(\det(q,m)\ne0\), for every actual common normal m. See
   `CIRCLE_CONTACT_ANGULAR_ORDER.md`, Section 6.
2. A containing-circle point cannot belong to two squares. Thus neither
   p nor q is a circle corner shared by the two bodies.
3. Every unit square has width at least one in every unit direction.

Because S has a unique physical circle corner, choose its orthogonal
side frame so that

\[
 S=[a-1,a]\times[b-1,b],\qquad z=(a,b),
 \qquad a,b>\frac12,\qquad a^2+b^2=R^2.
 \tag{1}
\]

The unique circle-load resultant is a nonnegative scalar multiple of z.
The free contact p is a vertex of S other than z. No common frame with
another square is assumed.

## 2. One determinant is necessary for force and torque balance

Let the positive contact magnitudes be \(\mu,\nu>0\), and let
\(\lambda\ge0\) be the circle multiplier. Translation and origin-torque
balance have the form

\[
 \mu n+\nu m+2\lambda z=0,
 \qquad
 \mu\det(p,n)+\nu\det(q,m)=0.
 \tag{2}
\]

Consequently the three columns

\[
 \begin{pmatrix}n_x\\n_y\\\det(p,n)\end{pmatrix},
 \quad
 \begin{pmatrix}m_x\\m_y\\\det(q,m)\end{pmatrix},
 \quad
 \begin{pmatrix}z_x\\z_y\\0\end{pmatrix}
\]

are linearly dependent. Their determinant is

\[
\begin{aligned}
 D(n,m)
 &=\det(z,n)\det(q,m)-\det(z,m)\det(p,n)\\
 &=\det\bigl(W(m),n\bigr),
 \qquad
 W(m):=\det(q,m)z-\det(z,m)p.
\end{aligned}
 \tag{3}
\]

Thus (2) requires \(D(n,m)=0\). This conclusion uses no positivity of
the circle load; it remains necessary when \(\lambda=0\).

We prove next that \(W(m)\ne0\) for every genuine common normal m at
the other fixed contact.

## 3. The coefficient vector cannot vanish

Suppose \(W(m)=0\). Nonradiality gives \(\det(q,m)\ne0\).
Equation (3) then forces p to be collinear with z.

The non-circle vertices in (1) are

\[
 (a-1,b),\qquad(a,b-1),\qquad(a-1,b-1).
\]

Their determinants with z are, respectively, \(-b\), a, and \(a-b\).
The first two are nonzero. Therefore the only remaining possibility is

\[
 a=b=:s=R/\sqrt2,\qquad
 p=(s-1,s-1)=\tau z,
 \qquad \tau=1-1/s>0.
 \tag{4}
\]

Thus S is the radial diagonal square, and p is its opposite inner
corner. Substituting (4) into \(W(m)=0\) yields

\[
                        \det(q-p,m)=0.
 \tag{5}
\]

In other words, the other actual normal line passes through p. Both
possible types of fixed contact q are impossible.

### 3.1. The other fixed contact is a vertex

It is distinct from p and cannot be z. It is therefore either
\((s-1,s)\) or \((s,s-1)\). Equation (5) makes its normal line vertical
or horizontal, respectively. The genuine outward-normal cone at that
vertex selects the outward normal \(e_y\) or \(e_x\). In either case
its supporting value is s.

The neighbor lies beyond that support line and has width at least one.
It therefore has a point whose corresponding unit-direction coordinate
is at least \(s+1\). But

\[
 s=\frac R{\sqrt2}>R-1,
\]

since \(R<2+\sqrt2\). This point would have coordinate greater than
R, contradicting containment in \(D_R\).

### 3.2. The other fixed contact is in a side interior

The actual normal line is perpendicular to that side. A horizontal or
vertical line through the corner \((s-1,s-1)\) meets each side of the
axis-parallel square either at an endpoint or not at all, except that
it may be the supporting line of an incident side. That latter line
is parallel, not perpendicular, to the side in question. It cannot be
the perpendicular normal line through a distinct side-interior point.
Thus (5) is impossible here as well.

These cases exhaust the fixed application q. We have proved

\[
                         \boxed{W(m)\ne0.}
 \tag{6}
\]

The two genuine degeneracies have been excluded explicitly: a free
application radially collinear with the circle corner forces (4), and
a second normal line through that inner corner is physically
impossible. There is no generic-concurrence assumption hidden in (6).

## 4. Simultaneous generic selection

For any fixed choice of the other actual normal m, equations (3) and
(6) show that \(D(n,m)=0\) restricts n to one unoriented line. A free
common-normal interval therefore contains normals with
\(D(n,m)\ne0\).

If the other contact also has a free normal, the same statement holds
for every fixed value of that second parameter. Hence the determinant
zero set has empty interior in the product of the two open normal
intervals. It is closed relative to that product, because D is
continuous. If m is fixed, the corresponding one-parameter zero set
has the same properties.

There are only finitely many square bodies and contact pairs. Before
selecting the stress component, list every prospective degree-two
body satisfying the hypotheses, with either incident free edge chosen
as n. In the product of all free normal intervals, each body's bad
set is a closed set with empty interior: vary that body's n parameter
while keeping every other parameter fixed and use (6). The complement
of the finite union of these bad sets is nonempty, indeed open and
dense. Choose the free normals in that complement.

Any matched opposite-pair requirement at a four-square contact
junction uses only the one local normal parameter for that junction.
It cannot identify the two parameters belonging to p and q, since
p and q are distinct. Moreover a junction contains at most two
circle-touching bodies, so it cannot couple two different C7 edges.
The boundary-pair normal may be chosen in the required open interval,
with its matched opposite pair then chosen as prescribed by the
planar-selection rule. The same finite avoidance argument applies to
these independent local parameters.

After this simultaneous choice, no listed body can satisfy (2) with
positive contact forces, since its determinant is nonzero. Therefore
none can occur in the selected all-boundary positive C7 component.

These finite exclusions can be imposed simultaneously with the earlier
D-body and other generic choices: restrict to their existing nonempty
open parameter domains and avoid the finite union of all bad sets at
once. The later physical uncrossing operation adds only
positive-length shared-side pairs and does not change the normal of a
surviving point contact. Subsequent thinning deletes atom types rather
than creating new ones. Consequently any final degree-two body whose
two applications are fixed uses an already prelisted pair of original
point contacts with their chosen normals. No newly created
fixed-application star escapes the determinant exclusions. A newly
added shared-side contact falls under the explicit variable-application
exception instead.

## 5. Exact scope of the reduction

For a surviving all-boundary positive C7 after this choice, every
incident free vertex/vertex edge at a unique-circle-corner degree-two
body forces at least one of its two positive contacts to have a
positive-length shared-side application interval.

Equivalently, if both applications are fixed and at least one edge
retains a free vertex normal, the body must have two physical circle
corners. These remaining alternatives are genuine cases to analyze;
this manuscript does not remove them or replace their variable
applications by endpoints.

Nor does the theorem remove an isolated common-normal ray: such an
edge has no open free parameter to select. The result supplies a whole
subfamily reduction for the C7 proof, while the general two-square
completion obstruction remains open. \(\square\)

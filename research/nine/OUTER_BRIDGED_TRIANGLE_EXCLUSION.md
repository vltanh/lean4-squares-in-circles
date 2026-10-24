# An outer bridged end triangle cannot lie beyond the radial support threshold

**Status: complete hand theorem and whole-fork corollary; root and
separate independent full hand audits passed.** Work in the common
selected physical certificate, with
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 T=\sqrt{R^2-\tfrac14},\qquad d=T-1.
\tag{1}
\]
Every other physical square remains present.

**Theorem.** Suppose A,B,C form a positive triangle. B,C have exact
positive degree two, and A has exact positive degree three, its
third edge being a bridge. Direct that bridge from its other
component toward A. In coordinates with this direction \(e_x\),
write its actual radial application as
\[
                  p_0=\rho e_x,\qquad A\subset\{x\ge\rho\}.
\tag{2}
\]
If
\[
                         \rho\ge\max(d-1,0),
\tag{3}
\]
the positive component is impossible.

No degree, load, or tree hypothesis is imposed on the component
on the other side of the bridge. All physical circle masks,
contact owners and actual shared-side means are retained. In
particular, the theorem is not obtained by applying an exact
smaller-component exclusion after deleting other forces.

## 1. The full loads and the sharp supporting-half-plane bound

An unloaded degree-two body cannot have physically touching
neighbors: its two opposite support planes separate those
neighbors by a positive width. Thus B,C are loaded. A is
physically circle-clear, since three mutually touching boundary
units would form a forbidden boundary triangle.

Use the sign convention that the circle-resultant vector of a
loaded body is the positive weighted sum of its circle corners.
Write these nonzero vectors as \(F_B,F_C\). Summing the genuine
equations over B,C and then A gives
\[
                         F_B+F_C=\mu e_x,\qquad\mu>0.
\tag{4}
\]
The force exerted through the third edge at A is the opposite
of the triangle aggregate. Equation (4) uses the bridge cut
equation, not a replacement radial-leaf model at A.

The center of every unit square in the containing disk satisfies
\[
                            |c|\le T-\tfrac12.
\tag{5}
\]
For clarity, if its center has norm \(r_c\), the farthest-corner
identity gives
\(R^2\ge r_c^2+r_c+1/2\): in its own axes,
the sum of the absolute center coordinates is at least \(r_c\).
Solving this quadratic gives (5).

Consequently any unit square lying in the half-plane
\(n\cdot x\ge h\), where n is a unit vector, satisfies
\[
                              h\le d.
\tag{6}
\]
Indeed its center has \(n\cdot c\ge h+1/2\). If \(h=d\), all
inequalities are equalities: its center is
\((d+1/2)n\), its half-width in direction n is \(1/2\), and
its frame contains n as a side axis. Hence there is exactly
one such physical unit square, namely the radial S square with
inner face at \(n\cdot x=d\).

## 2. The true end-triangle moment has a strict sign

Every positive circle corner of B or C has positive first
coordinate. To see this, take any such corner z. Its scalar
product with each positive circle corner of either body is
strictly positive: two corners of one physical boundary square
are adjacent, and corners across physically touching B,C obey
the strict acute-contact theorem. Taking its scalar product
with (4) gives \(z_x>0\).

The directions of \(F_B,F_C\) are distinct. This is the
strict disjoint corner-interval/resultant-direction theorem for
distinct boundary units, proved using the inner-circle arcs.
Equation (4) therefore makes their vertical components opposite
and nonzero. Label them so that
\[
       (F_B)_y>0>(F_C)_y,\qquad (F_B)_x,(F_C)_x>0.
\tag{7}
\]

Both B,C have the proper radial concurrence of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1. Its hypotheses
are exact here: each tip has exactly two positive pair forces,
and its other tip neighbor touches the circle. Thus its
two force lines are nonparallel, meet at a positive multiple
\(q_i\) of \(F_i\), and every actual contact p with outward
normal n obeys
\[
                             p-q_i=\ell_i n,\qquad\ell_i\ge0.
\tag{8}
\]
No assertion that a two-corner concurrence lies inside its
body is needed.

Let \(g\) be the BC normal directed from B toward C, and p
its actual application. Equation (8) gives
\[
 q_C-q_B=\ell g,\qquad \ell>0,\qquad
 \det(p,g)=\frac{\det(q_B,q_C)}{\ell}<0.
\tag{9}
\]
Here \(\ell>0\) follows from the opposite vertical signs in
(7), and the determinant is negative because both concurrence
points have positive first coordinate.

Orient the triangle A to B to C to A. The true torque
equations at B,C, and the zero origin moment of the radial
bridge at A, make its three directed contact moments equal.
Call the common value \(\mathcal H\). By (9),
\[
                              \mathcal H<0.
\tag{10}
\]
In particular, for the outward A-to-B normal \(n_B\), actual
application \(p_B\), and positive magnitude \(\mu_B\),
\[
                  \mu_B\det(p_B,n_B)=\mathcal H<0.
\tag{11}
\]

## 3. The actual three ports put A's concurrence on the opposite ray

First, the two triangle applications on A are distinct.
If both were p, their positive normal sum (4) would support
A in direction \(e_x\). The zero total moment would give
\(p_y=0\), while
\[
                 p_x=\max_A x\ge\rho+1>0.
\]
At B, (8) says \(q_B=p+\ell_B n_B\).
Its strictly positive height forces
\(\ell_B>0\) and \((n_B)_y>0\). This makes
\(\det(p,n_B)>0\), contrary to (11).

Neither triangle application equals the bridge application
\(p_0=(\rho,0)\). For B, the same proper-concurrence equation
would again give \((n_B)_y>0\), so
\(\det(p_0,n_B)\ge0\), contradicting (11).
For C, use the oppositely directed AC moment and its strictly
negative concurrence height. This also covers \(\rho=0\)
and an endpoint value of an actual shared-side mean.

For now suppose \(n_B,n_C\) are nonparallel. Their two lines
meet at a point \(q_A=(q,0)\). This is the elementary three-force
concurrence at an unloaded degree-three A: their positive sum
is horizontal, their summed origin moment is zero, and their
third force is the actual radial bridge force. It is not a
degree-two concurrence assertion.

The component beyond the bridge has total circle resultant
\(-\mu e_x\), by its exact cut balance. Therefore it contains
a positive circle corner z with \(z_x<0\). Choose a simple
positive path from A through that bridge to the body of z,
and retain its circle spoke. Also retain the A-to-B and
A-to-C paths and choose respectively a positive upper circle
corner of B and a positive lower circle corner of C.
Delete BC and all other edges of these retained branches.
They form an embedded three-port tree. The physical planar
embedding and circle-spoke construction apply also when the
discarded external graph had cycles or when additional physical
contacts have zero weight.

The three exterior ports have circular order B, z, C:
the chosen B and C corners lie respectively in the first
and fourth quadrants, while \(z_x<0\). At A all three actual
applications were just proved distinct. The crosscut order
for the three branches consequently gives the same cyclic
order for their outward support normals
\[
                              n_B,\ -e_x,\ n_C.
\]
Supporting normals of a convex square have the weak order of
their support applications, including side means and endpoints.
The positive, noncollinear three-force equilibrium makes every
successive angular gap strictly below \(\pi\), so
\[
                         (n_B)_y>0>(n_C)_y.
\tag{12}
\]
This is the same actual-port order argument used in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Section 3; no
straight drawing through a body interior is imposed.

Since the AB line passes through \(q_A\), equations (11)--(12)
give
\[
                               q<0.
\tag{13}
\]
Furthermore \(q_B-q_A\) is parallel to \(n_B\). Its vertical
coordinate and (12) show that its scalar coefficient is positive.
Its first coordinate is positive by (7) and (13). Hence
\[
                         (n_B)_x>0,\qquad(n_C)_x>0.
\tag{14}
\]
The same argument for C uses two negative vertical components
and again gives a positive coefficient.

## 4. Every articulation frame is excluded

### 4.1. A frame tilted relative to the bridge

Then the left support \(p_0\) of A is its unique leftmost
vertex. Choose its inward orthonormal side axes \(u,v\);
both have positive first coordinate, and
\[
                         A=p_0+[0,1]u+[0,1]v.
\tag{15}
\]
The point \(q_A\) has both own coordinates strictly negative
relative to \(p_0\), by (13) and \(\rho\ge0\).

At any triangle contact p, the vector \(p-q_A\) therefore
has both own coordinates strictly positive. It is parallel to
the contact normal. By (14) the normal cannot have both own
coordinates negative, since both u,v have positive first
coordinate. It thus has both own coordinates strictly positive.
Its unique support point on A is the far vertex \(p_0+u+v\).

Both triangle applications would be this same vertex. Section 3
already excluded that possibility. Thus no tilted A remains.

### 4.2. A frame parallel to the bridge

Write
\[
                   A=[\rho,\rho+1]\times[l,l+1],
                          \qquad l\le0\le l+1.
\tag{16}
\]
From (12)--(14), the AB normal has both components positive
and its contact is the upper-right vertex
\(p_B=(\rho+1,y)\), where \(y=l+1\).
Because its line passes through \(q_A=(q,0)\), \(q<0\),
we have \(y>0\). Put \(a=\rho+1>0\) and \(b=-q>0\). Then
\[
       n_B=\frac{(a+b,y)}{\sqrt{(a+b)^2+y^2}},\qquad
       p_B\cdot n_B>a.
\tag{17}
\]
The strict inequality follows by squaring: the numerator square
minus \(a^2((a+b)^2+y^2)\) is
\[
                        y^2\bigl(a(a+2b)+y^2\bigr)>0.
\]
But B lies beyond this supporting line, and (3) gives
\(a=\rho+1\ge d\). Equation (17) contradicts (6).
Thus no parallel frame remains in the nonparallel-force case.

### 4.3. Parallel triangle forces, with all actual means

If \(n_B,n_C\) are parallel, (4) makes their common axis horizontal.
They cannot point in opposite directions: then B,C would lie
beyond A's opposite vertical supports and could not physically
touch. They cannot both point west by (4). Hence
\[
                               n_B=n_C=e_x.
\tag{18}
\]
Both units lie in
\[
                     x\ge\max_A x\ge\rho+1\ge d.
\]
Equation (6) excludes a strict inequality. In equality, its
rigidity says B,C are the same radial S square, again impossible.
This includes every shared-face mean, all endpoint means,
and the critical value \(d=1,\rho=0\).

Sections 4.1--4.3 prove the theorem.

## 5. Entire six-body fork attachment

Consider the exact positive graph with triangle A,B,C and
three bridges
\[
                              A-U,\qquad U-L_1,\qquad U-L_2.
\tag{19}
\]
There are three arbitrary other physical squares, which remain
in place.

The leaves \(L_1,L_2\) are genuine radial S/D leaves. U has
exact positive degree three and every incident edge is a bridge.
It is unloaded: the local all-bridge loaded-body lemma in
TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md, Section 1,
makes any such loaded body radial D of degree one or radial S
of degree at most two. This local argument does not suppose
that the entire component is a tree.

Apply the two-leaf central-disk lemma in
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1,
to U and its two actual leaves. It proves
\[
       D_{\max(d-1,0)}\subset U;
\]
the containment is strict in U's interior except possibly when
\(d=1\). At that value the only boundary case is an origin-vertex
U with two S leaves in its two side directions.

Direct the remaining bridge from U toward A and rotate this
direction to \(e_x\). Its actual mean lies on the radial line,
so \(p_0=\rho e_x\). It is U's right support and A's left support.
The displayed disk containment yields
\[
                             \rho\ge\max(d-1,0).
\]
All hypotheses of the uniform theorem hold: B,C have exact
degree two and A exact degree three. It excludes (19), including
the complete exceptional-radius U geometry. No edge has been
discarded from an equilibrium equation, and no assumption about
the three extra squares was used.

Thus the entire fork-at-U attachment of C1.3.b3 is closed.


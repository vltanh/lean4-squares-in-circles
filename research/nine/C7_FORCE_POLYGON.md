# An all-boundary positive seven-cycle has an embedded convex force polygon

**Status: complete structural implication, independently audited.**
Let a positive physical stress component consist entirely of
circle-touching unit squares in the radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

By `CIRCLE_CONTACT_ANGULAR_ORDER.md`, this component is a seven-cycle
and contains every circle-touching square. The theorem here gives an
additional geometric property of its positive stress: each loaded
body's two aggregate contact-force lines concur **inside that body**.
For a zero-load body one can choose a point on its straight
transmission chord. These seven points form a convex polygon containing
the origin, with every polygon edge running along the actual contact
force and through an actual contact point.

This conclusion retains zero circle multipliers, two active circle
corners, vertex contacts, and aggregated side contacts. It does not
yet prove that the remaining region cannot contain two more unit
squares. In particular, it is not a claim that every positive
seven-cycle is regular.

## 1. Conventions and geometric inputs

Number the squares \(S_0,\ldots,S_6\) in positive circular order of
their centers. Indices below are taken modulo seven. Orient edge
\(i\) from \(S_i\) to \(S_{i+1}\). Its aggregate positive force is

\[
 f_i=\mu_i n_i,\qquad \mu_i>0,
 \tag{2}
\]

where \(n_i\) is a unit common supporting normal, directed outward
from \(S_i\), and its application point \(p_i\) belongs to the
actual intersection \(S_i\cap S_{i+1}\).

This aggregation preserves force and torque. At a side contact all
atoms have the same normal, so their weighted mean application point
is still in the actual common segment. At a point contact all
application points coincide; any positive sum of the common normals
is a nonzero common normal, and can be normalized as in (2).

Write

\[
 m_i=\sum_k\lambda_{i,k}z_{i,k},\qquad \lambda_{i,k}\ge0,
 \tag{3}
\]

for the weighted sum of the circle corners of \(S_i\). Its body
equations are

\[
 f_i-f_{i-1}+2m_i=0,
 \qquad
 \det(p_i,f_i)=\det(p_{i-1},f_{i-1}).
 \tag{4}
\]

The second equation is torque balance about the origin: each circle
force is radial and contributes zero origin moment. Consequently

\[
                  \det(p_i,f_i)=H
 \tag{5}
\]

is independent of \(i\).

We use these already proved geometric facts:

* No point belongs to three circle-touching squares
  (`CYCLIC_GLOBAL_CONTINUATION.md`, Section 7).
* The direction of every nonzero \(m_i\) pierces the open interior
  of its square on the circle of radius \(5/4\). In particular the
  nonzero \(m_i\)'s have distinct directions
  (`CYCLIC_GLOBAL_CONTINUATION.md`, Section 8).
* Each circle-touching square has angular shadow shorter than
  \(\pi/3\). A contact joins consecutive center directions along a
  positive gap shorter than \(2\pi/5\)
  (`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Sections 3--5).
* A contact between two circle-touching squares cannot be radial:
  \(\det(p_i,n_i)\ne0\)
  (`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Section 6). Thus
  \(H\ne0\) in (5).

Also, a containing-circle point cannot belong to two squares. Indeed,
if \(z\) is a circle corner and \(w_1,w_2\) are the two orthogonal
unit side directions pointing into its square, containment of
\(z+w_j\) gives

\[
 z\cdot w_j\le-\frac12.
\]

Thus \(-z\) lies strictly inside the inward tangent quadrant, and
\(z-\varepsilon z\) is in the open square for sufficiently small
\(\varepsilon>0\). Two squares sharing \(z\) would therefore have
overlapping interiors.

Every square in question avoids the origin: a circle corner is at
distance \(R\), while the square diameter is \(\sqrt2<R\).

## 2. A shallow inner contact cannot reach another circle-touching body

The following metric lemma will control the case with two circle
corners.

**Lemma 2.1.** Put

\[
 S=[d,d+1]\times[-1/2,1/2],
 \qquad R^2=(d+1)^2+\frac14,
 \tag{6}
\]

in the window (1). Let a unit square \(T\subset D_R\) be supported
on the other side of a common contact at \(p=(d,1/2)\), with common
normal outward from \(S\)

\[
 n=(-\cos\eta,\sin\eta),\qquad
 0\le\eta\le\arctan(1/2).
 \tag{7}
\]

Then every corner of \(T\) has norm strictly less than \(R\).
The same conclusion holds at \((d,-1/2)\) after reflection. It also
holds for any \(p=(d,h)\), \(|h|\le1/2\), with normal \((-1,0)\).

*Proof.* The lower radius bound gives

\[
 d=\sqrt{R^2-1/4}-1>\frac9{10}
 >\frac{1+\sqrt5}{4}.
 \tag{8}
\]

First suppose \(p\) is a vertex of \(T\). Its two inward unit side
directions can be labeled

\[
 w_1=(\sin\theta,\cos\theta),\qquad
 w_2=(-\cos\theta,\sin\theta).
\]

The supporting normal condition is exactly

\[
 \eta-\frac\pi2\le\theta\le\eta.
 \tag{9}
\]

For \(\theta\le0\), (9) puts \(\theta\) in
\([-\pi/2,0]\). All corner first coordinates lie in
\([d-\sqrt2,d]\subset[-d,d]\), and all second coordinates lie in
\([-1/2,3/2]\). Hence every corner has squared norm at most

\[
 d^2+\frac94
 <d^2+2d+\frac54=R^2.
 \tag{10}
\]

For \(0\le\theta\le\arctan(1/2)\), put
\(t=\sin\theta\), \(u=\cos\theta\). The corners \(p\) and
\(p+w_2\) satisfy the same bound (10). The other two have squared
norms

\[
 \begin{aligned}
 |p+w_1|^2&=d^2+\frac54+2dt+u,\\
 |p+w_1+w_2|^2
   &=d^2+\frac94+(2d+1)t+(1-2d)u.
 \end{aligned}
 \tag{11}
\]

Both expressions increase with \(\theta\) on this interval. At its
right endpoint, \((t,u)=(1,2)/\sqrt5\), their differences below
\(R^2\) are respectively at least

\[
 2d-\frac{2d+2}{\sqrt5}>0,
 \qquad
 (2d-1)+\frac{2d-3}{\sqrt5}>0.
 \tag{12}
\]

Both strict inequalities follow from (8).

If \(p\) lies in the relative interior of a side of \(T\), vary
its position along that side while keeping \(p\) and the orientation
fixed. Each corner position is affine in this position parameter.
The two endpoint placements have \(p\) as a vertex, and have just
been bounded strictly inside the disk. Convexity of the squared norm
therefore gives the same strict bound for every intermediate placement.

For the final horizontal-normal assertion, use the same endpoint
reduction at \(p=(d,h)\). Now \(\theta\in[-\pi/2,0]\); all
corner first coordinates again lie in \([-d,d]\), and all second
coordinates lie in \([h-1,h+1]\subset[-3/2,3/2]\). Equation (10)
applies unchanged. Reflection proves the lower-corner case.
\(\square\)

## 3. The contact lines of a loaded body are not parallel

A circle-touching unit square in the window has either one or two
circle corners. To see the exhaustive alternatives, place a circle
corner at \((a,b)\) in its orthogonal side frame:

\[
 S=[a-1,a]\times[b-1,b],\qquad
 a\ge b\ge\frac12,\qquad a^2+b^2=R^2.
 \tag{13}
\]

The bounds \(a,b\ge1/2\) follow from the two adjacent corners.
Equality for another corner is possible exactly when one coordinate
equals \(1/2\). Both cannot equal \(1/2\) in (1). Thus the
two-corner case is, after reflection and relabeling, precisely (6).

Let a loaded body have two positive outward contact forces. Suppose
their normals are parallel. Force balance implies that their common
axis is the axis of the nonzero circle resultant.

In the unique-corner case, the circle resultant is a positive multiple
of \(z=(a,b)\). If the contact normals have opposite signs, one
points in direction \(z\), and its contact is the outer circle
corner; this is impossible by Section 1. If they have the same sign,
both point in direction \(-z\), and both contacts are the inner
corner. This gives a point in three circle-touching squares, also
impossible.

In the two-corner case set \(a=d+1\). The normalized circle
resultant has the form

\[
                    \bar z=(a,b),\qquad |b|\le1/2.
 \tag{14}
\]

For \(b\ne0\), the same argument applies: the \(+\bar z\)
direction supports at an outer circle corner and the \(-\bar z\)
direction at a single inner corner. For \(b=0\), a contact with
normal \((1,0)\) would force the neighbor to have a point with first
coordinate at least \(a+1>R\), since a unit square has width at
least one in every direction. A contact with normal \((-1,0)\)
is excluded by Lemma 2.1 because its neighbor is circle-touching.

The two contact lines of every loaded body are therefore nonparallel.
Let \(q\) be their intersection. Taking torque about \(q\), or
combining force and origin torque, gives

\[
                         \det(q,m)=0.
 \tag{15}
\]

It remains to prove that this concurrency point belongs to the body.

## 4. Concurrence lies inside a body with one circle corner

Use (13), with the unique circle corner \(z=(a,b)\). Equation
(15) says

\[
                             q=\tau(a,b).
 \tag{16}
\]

If \(1-1/a\le\tau\le1\), then \(q\in S\): the first
coordinate lies in \([a-1,a]\), and
\(b\tau\ge b-b/a\ge b-1\). We exclude both remaining ranges.

The normal-line checks below use only the elementary normal cones of
a rectangle. At a relative side-interior contact the line is
perpendicular to that side. At a vertex, an outward normal has the
corresponding two coordinate signs. The line through \(q\) and the
vertex must have one of the two signs of such an outward normal.

If \(\tau>1\), then \(q\) is strictly above and to the right of
the rectangle. Among its vertices only the outer circle corner and
the opposite inner corner can have an outward normal line through
\(q\); no side-interior normal line can. The circle corner cannot
be shared, and two contacts at the inner corner violate the
three-square incidence prohibition.

Now suppose \(\tau<1-1/a\), so \(q_x<a-1\). If
\(q_y<b-1\), the same normal-cone check leaves only the inner
corner and outer circle corner. At equality \(q_y=b-1\), there
is also the right lower corner with horizontal outward normal
\((1,0)\); its support value \(a>R-1\) makes a unit neighbor
impossible by width.

It remains to consider

\[
               q_x<a-1,\qquad b-1<q_y<b.
 \tag{17}
\]

The only possible non-circle contacts are the left-side point
\((a-1,q_y)\), a right-side point with outward normal \((1,0)\),
and the lower right corner \(p=(a,b-1)\). The right-side point is
excluded by the same width bound. Since the two contacts must be
distinct, the lower right corner must be one of them. Its outward
normal has the form

\[
 n=(\cos\eta,-\sin\eta),\qquad
 0\le\tan\eta
 =\frac{b\tau-(b-1)}{a(1-\tau)}
 <\frac{a-b}{a}.
 \tag{18}
\]

We show that this contact also has support too large for a unit
neighbor:

\[
       p\cdot n=a\cos\eta-(b-1)\sin\eta
                       \ge\frac{R}{\sqrt2}>R-1.
 \tag{19}
\]

The displayed trigonometric expression is positive and concave on
the closed interval \(0\le\tan\eta\le(a-b)/a\), so its minimum
is at an endpoint. At zero it equals \(a\ge R/\sqrt2\). At the
other endpoint put \(e=a-b\ge0\) and

\[
 N=a^2+e(1-b),\qquad D^2=a^2+e^2.
\]

The endpoint value is \(N/D\), and direct expansion gives

\[
\begin{aligned}
 2N^2-R^2D^2
 =e\bigl[&2b^2(2-b)
       +e(2+4b-3b^2)\\
       &+e^2(4-2b)\bigr]\ge0.
\end{aligned}
 \tag{20}
\]

All coefficients in the brackets are positive for
\(1/2\le b<3/2\); this upper bound follows from
\(b\le R/\sqrt2<3/2\). Also \(N>0\). Thus the first inequality
in (19) follows. The second uses \(R<2+\sqrt2\), which is much
weaker than (1).

The neighboring square lies on the outward side of the support line
and has width at least one along \(n\), so (19) would give a point
with \(n\)-coordinate greater than \(R\). This contradicts disk
containment. Every case outside the rectangle has been excluded;
therefore \(q\in S\).

## 5. Concurrence lies inside a body with two circle corners

Use (6), write \(a=d+1\), and normalize its positive circle
resultant as in (14). Equation (15) gives

\[
                          q=\tau(a,b).
 \tag{21}
\]

For \(d/a\le\tau\le1\), clearly \(q\in S\).

If \(\tau<d/a\), then \(q\) lies strictly to the left of the
rectangle. When \(|q_y|<1/2\), the rectangle normal-cone check
leaves one inner-face point, the two outer circle corners, and an
outer-face horizontal contact. The outer-face contact is impossible
by its support \(a>R-1\), and the circle corners cannot be shared.
There is only one non-circle contact. When \(|q_y|>1/2\), there
is again only one non-circle vertex with an outward normal line
through \(q\). At \(|q_y|=1/2\), the possible extra horizontal
outer-face contact is excluded by width. Thus two distinct contacts
are impossible throughout this range.

Suppose instead that \(\tau>1\), so \(q_x>a\). If
\(|q_y|>1/2\), only one non-circle corner can have an outward
normal line through \(q\). At \(|q_y|=1/2\), there is at most
one further non-circle contact, with horizontal normal \((-1,0)\)
on the inner face, excluded by Lemma 2.1. It remains to handle
\(|q_y|<1/2\).

In this last range, first exclude the outer-face horizontal contact
by the same support bound \(a>R-1\). The remaining possible
non-circle contacts are a horizontal inner-face contact and the two
inner corners. Lemma 2.1 excludes the
horizontal contact. Therefore both inner corners must be used. Put
\(\ell=q_x-d>1\). Their outward normals are proportional to

\[
 (-\ell,1/2-q_y),\qquad
 (-\ell,-1/2-q_y).
 \tag{22}
\]

The smaller of their absolute slopes is

\[
              \frac{1/2-|q_y|}{\ell}<\frac12.
\]

That contact is forbidden by the upper or lower version of Lemma
2.1: its neighbor would be circle-clear. The range \(\tau>1\)
is impossible as well. Hence \(q\in S\).

Together, Sections 3--5 prove the promised local assertion:

**Theorem 5.1 (physical concurrence).** At every loaded body of an
all-circle-touching positive cycle, the two aggregate contact-force
lines are nonparallel and meet at a point \(q_i\in S_i\). Moreover

\[
                         m_i=\kappa_i q_i,
                    \qquad \kappa_i>0.
 \tag{23}
\]

The positive proportionality follows from (16) or (21), because the
rectangle lies in the positive first-coordinate half-plane.

## 6. The concurrence points form a convex polygon around the origin

For every loaded body choose the point \(q_i\) of Theorem 5.1. If
body \(i\) is unloaded, (4) gives \(f_i=f_{i-1}\). Its two
application points lie on the same force line by torque balance and
on the two opposite supporting faces. Thus

\[
                 p_i-p_{i-1}=w_i n_i,
                 \qquad w_i\ge1.
\]

Choose their midpoint as \(q_i\). It belongs to \(S_i\), is
distinct from both contact points, and lies on both contact-force
lines. No body has \(q_i=0\), since the squares avoid the origin.

For every edge \(i\), both \(q_i\) and \(q_{i+1}\) lie on the
line \(p_i+\mathbb R n_i\). They lie on the two corresponding
supporting half-lines, because they belong to their respective
squares. Hence \(p_i\) lies between them and

\[
                  q_{i+1}-q_i=\ell_i n_i,
                  \qquad \ell_i\ge0.
 \tag{24}
\]

In fact \(\ell_i>0\). Otherwise both endpoints equal \(p_i\).
Neither could be an unloaded midpoint. If both were loaded, (23)
would give identical directions for their nonzero circle resultants,
contrary to Section 1. Thus every polygon edge is nondegenerate.

The loop made of the edges in (24) has winding number one about the
origin. Here is a direct proof that does not presume an embedding.
Insert \(p_i\) into every edge and move each \(q_i\) linearly to
the center \(C_i\) inside \(S_i\), keeping the \(p_i\)'s fixed.
All resulting segments stay in their respective squares, so this is
a homotopy avoiding the origin. The final loop is

\[
 C_0\longrightarrow p_0\longrightarrow C_1
 \longrightarrow p_1\longrightarrow\cdots
 \longrightarrow C_6\longrightarrow p_6\longrightarrow C_0.
\]

For each link \(C_i\to p_i\to C_{i+1}\), the two square shadows
overlap and their union is a connected interval shorter than
\(2\pi/3<\pi\). The link therefore changes its polar angle by
exactly the positive consecutive center gap, not by that gap plus a
full turn. Those gaps sum to \(2\pi\), proving the winding claim.

On the other hand, (5) and (24) give

\[
 \det(q_i,q_{i+1})
   =\frac{\ell_i}{\mu_i}\det(q_i,f_i)
   =\frac{\ell_i}{\mu_i}H.
 \tag{25}
\]

Since \(H\ne0\), the polar-angle change along every edge is
nonzero, shorter than \(\pi\), and has the sign of \(H\). The
winding number one forces \(H>0\). The seven positive polar-angle
changes then partition one full turn. Each edge meets each radial
ray in its own angle interval exactly once. Consequently the polygon
is simple and contains the origin in its interior.

At a loaded vertex, (4) and (23) give

\[
 f_i-f_{i-1}=-2\kappa_i q_i,
 \qquad
 \det(f_{i-1},f_i)=2\kappa_i H>0.
 \tag{26}
\]

At an unloaded vertex the force directions agree. Since its edge
directions are positive multiples of the \(f_i\)'s, the simple
polygon has a strict left turn at every loaded vertex and is straight
at every unloaded vertex. A simple polygon with these turns is
convex. This proves the structural theorem.

**Theorem 6.1 (embedded convex force polygon).** Every all-boundary
positive seven-cycle in (1) admits points \(q_i\in S_i\) such that:

1. The polygon \(q_0q_1\cdots q_6\) is convex and contains the
   origin in its interior.
2. Its edge \([q_i,q_{i+1}]\) contains the actual contact point
   \(p_i\), and points in the direction of the positive contact
   force \(f_i\).
3. A vertex is a strict convex vertex exactly when its body is loaded;
   an unloaded body gives a straight transmission vertex.
4. At every loaded body the radial vector \(q_i\) is a positive
   multiple of its circle-load resultant.

All polygon vertices and edges lie in \(D_R\), since the vertices
belong to the contained squares and the disk is convex.

## 7. What remains for completion

The theorem is a necessary condition on an entire positive
seven-cycle, with no regularity or common-frame hypothesis. It may
be used together with the actual square side lengths and circle
corners when analyzing its central complementary region. Convexity
of this force polygon alone has not yet been converted into a
two-square completion obstruction. The unrestricted nine-square
lower bound is therefore not claimed here.

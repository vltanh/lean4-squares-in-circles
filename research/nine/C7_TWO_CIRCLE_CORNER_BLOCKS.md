# Two-circle-corner contacts form radial blocks with no three-body run

**Status: complete vertex-shell and simultaneous-selection implication;
independent hand audit passed.** In the radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\]

any vertex/vertex contact from a two-circle-corner unit square to another
circle-touching unit square forces that neighbor also to have two circle
corners. Every contact between two such radial bodies has the same
center-angle gap, and its common-normal cone has a nonempty open
interval. Those normal intervals can be restricted, before stress
extraction, so that no selected positive C7 contains three consecutive
two-circle-corner bodies. Zero circle multipliers are retained.

The restrictions are open. They are therefore compatible with the
finite open-dense selections in
`C7_FIXED_APPLICATION_GENERIC_SELECTION.md` and the earlier generic
contact-selection lemmas. They do not impose common orientations on
other bodies or replace a variable shared-side application by a point.

## 1. The two-circle-corner square and its inner vertex radius

Put

\[
 a_0=\sqrt{R^2-\frac14},\qquad d=a_0-1,
 \qquad r_0=a_0-\frac12.
 \tag{1}
\]

A unit square with two circle corners is, up to rotation, precisely

\[
                S=[d,d+1]\times[-1/2,1/2].
 \tag{2}
\]

Its center is \((r_0,0)\), its two circle corners are
\((a_0,\pm1/2)\), and its two non-circle vertices have common squared
norm

\[
       L_0^2=d^2+\frac14=R^2-2a_0+1.
 \tag{3}
\]

Here \(d>1/2\), and in fact \(d>9/10\), throughout the declared
window. Containment of the adjacent vertices proves the classification
(2), as in `C7_FORCE_POLYGON.md`, Section 3.

## 2. A unique-circle-corner square has no vertex on this inner shell

Take any circle-touching square with exactly one circle corner. In its
side frame write

\[
 T=[a-1,a]\times[b-1,b],\qquad
 a\ge b>\frac12,\qquad a^2+b^2=R^2.
 \tag{4}
\]

Since \(b>1/2\), we have \(a<a_0\). Its two vertices adjacent to the
circle corner have squared norms

\[
 R^2-2a+1>L_0^2,
 \qquad R^2-2b+1\ge R^2-2a+1>L_0^2.
 \tag{5}
\]

Its opposite inner vertex has squared norm

\[
                    R^2-2(a+b)+2<L_0^2.
 \tag{6}
\]

For the strict inequality, the function
\(b\mapsto\sqrt{R^2-b^2}+b\) increases strictly from
\(b=1/2\) to \(b=R/\sqrt2\), except that its derivative vanishes
at the final endpoint. Thus
\(a+b>a_0+1/2\), which gives (6).

The circle corner itself has norm R, also greater than \(L_0\).
Therefore no vertex of T lies on the circle of radius \(L_0\).

A vertex/vertex contact with S cannot use one of S's circle corners,
because two squares cannot share a containing-circle point. It must
therefore lie at one of the two inner vertices in (3). Equations
(5)--(6) exclude a unique-circle-corner neighbor. We have proved:

**Vertex-shell lemma.** Every circle-touching neighbor meeting a
radial two-circle-corner body at a vertex/vertex contact is itself a
radial two-circle-corner body.

This assertion uses only geometry and retains every genuine common
normal at the contact.

## 3. Every radial-pair contact is a fixed inner-vertex contact

The frame of a radial body (2) is determined, up to square symmetries,
by its center direction. Two radial bodies can have parallel frames
only if their center directions differ by a multiple of \(\pi/2\).
They cannot touch at any nonzero such difference: at a right angle
their axis-parallel coordinate intervals have a strict gap
\(r_0-1>0\), and at a half turn their center distance exceeds
\(\sqrt2\). Equal center directions would give identical bodies.

Thus two touching radial bodies have nonparallel frames. Their contact
has a vertex application on at least one body. It cannot be a circle
vertex, so this application has norm \(L_0\). On the other body's
boundary, the only points of norm \(L_0\) are its two inner vertices:

* on the inner face, squared norm is \(d^2+y^2\), with equality to
  \(L_0^2\) only at its endpoints;
* on either transverse side, squared norm increases strictly from
  \(L_0^2\) at the inner endpoint toward \(R^2\) at the outer one;
* on the outer face, squared norm is at least \(a_0^2>L_0^2\).

Every radial-pair contact is consequently a single common inner
vertex.

Let

\[
             \eta=\arctan\frac1{2d},\qquad \gamma=2\eta.
 \tag{7}
\]

The two inner vertices have polar angles \(\pm\eta\) relative to the
center direction. Distinct radial bodies sharing such a vertex must
use opposite signs, so their positive consecutive center gap is
exactly \(\gamma\in(0,\pi/2)\). The angular-order theorem also places
it in \((\pi/5,2\pi/5)\).

Orient each radial-pair edge by increasing circular center order. In
the predecessor's radial frame, the contact is \((d,1/2)\). Its common
normal directions, pointing toward the successor, form the closed
interval

\[
                  \frac\pi2\le\arg n\le\frac\pi2+\gamma.
 \tag{8}
\]

Indeed the predecessor's outward vertex cone is
\([\pi/2,\pi]\), and the successor's inward vertex cone, expressed
in this frame, is \([\gamma,\gamma+\pi/2]\). Their intersection is
(8). Its strict interior is a genuine free normal interval.

## 4. A three-body radial run fails at the tangential limiting normals

Consider three consecutive radial bodies, and use the middle body's
radial frame. Its applications are

\[
                   p_-=(d,-1/2),\qquad p_+=(d,1/2).
\]

On each of the two edges, choose the limiting normal equal to the
predecessor's positive tangential side direction. The incoming edge
normal and outgoing edge normal in the middle frame are therefore

\[
              n_-=(\sin\gamma,\cos\gamma),
 \qquad       n_+=e_y.
 \tag{9}
\]

Let their positive magnitudes be \(\mu_-\) and \(\mu_+\).
Origin-torque balance requires

\[
 \mu_+d
 =\mu_-\left(d\cos\gamma+\frac12\sin\gamma\right).
 \tag{10}
\]

Since \(\tan(\gamma/2)=1/(2d)\),

\[
                 d(1-\cos\gamma)=\frac12\sin\gamma.
 \tag{11}
\]

The parenthesis in (10) equals d. Thus the magnitudes are equal.
Translation balance then forces the circle-load resultant m to obey

\[
 2m=\mu_-n_--\mu_+n_+
   =\mu_-\bigl(\sin\gamma,\cos\gamma-1\bigr).
 \tag{12}
\]

Every admissible nonnegative combination of the middle body's two
circle corners \((a_0,\pm1/2)\) satisfies

\[
                       m_x+2a_0m_y\ge0.
 \tag{13}
\]

But (11), (12), and \(a_0=d+1\) give

\[
 2(m_x+2a_0m_y)
 =\mu_-\bigl[\sin\gamma+2a_0(\cos\gamma-1)\bigr]
 =-2\mu_-(1-\cos\gamma)<0.
 \tag{14}
\]

This is a strict contradiction. In particular the required resultant
is nonzero, so zero circle multipliers do not provide an exception.

## 5. Open restrictions and simultaneous selection

The limiting normals in (9) lie on the endpoints of the common-normal
intervals (8). We now replace them by strict normals in small open
intervals just beyond those endpoints.

Normalize \(\mu_-=1\). For normals sufficiently close to (9), the
outgoing origin moment remains positive. Torque therefore fixes
\(\mu_+\) as the ratio of two positive origin moments. This ratio and
the required resultant

\[
                 2m=n_--\mu_+n_+
\]

are continuous functions of the two normal parameters. The strict
negative value in (14) persists in a product neighborhood of the two
limiting parameters. Within that neighborhood, no positive body
stress with any nonnegative circle multipliers exists.

There are finitely many prospective radial three-body runs in the
physical packing. Orient every radial-pair edge as in Section 3 and
restrict its normal to a sufficiently small strict open interval
immediately beyond its predecessor's tangential side axis. Because
all the exclusions in (14) are strict, the intervals can be chosen
simultaneously so that every prospective middle body is excluded.
Their product is nonempty and open.

These radial-pair edges cannot be subject to a matched four-square
junction choice. Four interior-disjoint squares meeting at one point
must fill four right-angle sectors, so all four frames are parallel;
see `PLANAR_STRESS_CORE.md`, Lemma 1.1. But a touching radial pair has
relative frame angle \(\gamma\in(0,\pi/2)\), strictly between the
parallel-frame possibilities. Hence its contact point is not a
four-square junction, and the radial normal intervals are independent
of those matched choices.

Restricting to this open product leaves the later finite open-dense
normal selections available. In particular the exclusions from
`C7_FIXED_APPLICATION_GENERIC_SELECTION.md` and the prior generic
lemmas can be imposed inside these intervals. Uncrossing does not
change a surviving point-contact normal and only adds shared-side
pairs; thinning only deletes atom types. Every final radial-pair edge
is the original fixed inner-vertex contact, so the chosen restriction
continues to apply to every final radial three-body run.

We conclude:

**Radial-block selection theorem.** The physical normals may be chosen
before stress extraction so that every radial block in the selected
all-boundary positive C7 has length at most two. A free vertex/vertex
contact incident to a radial body always joins it to another radial
body; after this selection, the two such radial bodies cannot extend
to a three-body radial run.

The remaining two-body radial blocks, isolated radial bodies,
variable shared-side applications, and contacts at unique-circle-corner
bodies are not excluded by this theorem. Their completion by two
arbitrary squares remains part of the general positive C7 obligation.
\(\square\)

## 6. Counting and a parallel-frame obstruction

The no-three-run conclusion implies that a selected positive C7 has
at most four radial bodies and at least three bodies with unique
physical circle corners. If there are r radial bodies and u nonradial
bodies, each nonradial body can separate at most one radial run, and
every run has length at most two. Thus \(r\le2u\) and \(r+u=7\),
which gives \(r\le4\).

There is also a useful restriction requiring no stress selection:
**two radial bodies with parallel frames cannot occur among seven
interior-disjoint circle-touching unit squares in this window.**

On the circle of radius \(5/4\), the open interior of the radial body
(2) cuts out precisely the arc about its center direction of half-angle

\[
                         \delta=\arcsin(2/5)>\pi/8.
 \tag{15}
\]

Indeed its transverse sides impose \(|y|<1/2\), its outer face is
beyond that inner circle, and its inner face does not cut the arc:
\(d<41/40<\sqrt{21}/4\). The last lower endpoint is the x-coordinate
of the inner-circle point with \(|y|=1/2\). The strict inequality in
(15) follows from \(\sin(\pi/8)<2/5\), equivalently
\((2-\sqrt2)/4<4/25\).

By `CYCLIC_GLOBAL_CONTINUATION.md`, Theorem A and its explicit interval
description, each other circle-touching square occupies one connected
open inner-circle arc of length greater than \(\pi/4\). Those five
arcs are pairwise disjoint and avoid the two radial arcs.

If the two radial center directions differ by \(\pi/2\), the two
remaining gaps have lengths

\[
             \pi/2-2\delta<\pi/4,
 \qquad       3\pi/2-2\delta<5\pi/4.
\]

The smaller gap cannot contain any of the five other arcs. The larger
cannot contain all five, since each has length greater than \(\pi/4\).
A difference of \(3\pi/2\) is the same case. If the two radial center
directions are antipodal, both remaining gaps have length

\[
                            \pi-2\delta<3\pi/4.
\]

Each can hold at most two of the other arcs, again fewer than five.
Equal center directions would give overlapping identical radial
bodies. These are every possibility for parallel radial frames.

Consequently every parallel shared-side block in a physical boundary
C7 contains at most one radial body. This geometric fact is
independent of the chosen loads and common normals.

## 7. The predecessor of each radial pair has a shared-side neighbor

The open choices can be narrowed further so that, for every surviving
radial/radial edge oriented in positive circular order, its predecessor
belongs to a nonsingleton shared-side block. More precisely, that
predecessor's other positive contact is a positive-length shared side
on its backward tangential face.

Use the predecessor's radial frame

\[
 S=[d,d+1]\times[-1/2,1/2],\qquad a_0=d+1.
\]

Its forward radial-pair contact is \(p_+=(d,1/2)\), and its chosen
normal is in the small strict interval just beyond \(e_y\). We show
that every alternative in which its other application is fixed fails
at the limiting normal \(e_y\), with a strict margin.

The outer radial face cannot have a unit neighbor by width. The inner
radial face cannot meet another circle-touching neighbor by the
shallow-contact lemma. Circle corners cannot be shared. Any other
point on the forward tangential face, including its inner vertex,
has strictly positive origin moment for every genuine outward normal;
it cannot balance the positive moment at \(p_+\). Thus the only
possible fixed other applications lie on the backward tangential face
or at its inner vertex.

First let that application be \((x,-1/2)\) in the relative interior
of the backward face, so \(d<x<a_0\). Its incoming directed force
normal is \(e_y\). Normalize its magnitude to one. Torque at the
limiting forward normal forces the outgoing magnitude to be x/d.
Translation would then require

\[
                      2m=(0,1-x/d).
\]

This violates the admissible circle-resultant inequality
\(m_x+2a_0m_y\ge0\), strictly because x>d.

Next let the other fixed application be the backward inner vertex
\((d,-1/2)\). A vertex/vertex neighbor would be radial by the
vertex-shell lemma, producing a prohibited three-radial run in the
selected C7. Hence the remaining fixed-point alternative is a genuine
vertex/side contact. Its incoming normal has the form

\[
                       n_-=(s,t),\qquad s>0,\quad t\ge0.
\]

The strict inequality s>0 is necessary: if s=0, the neighbor's side
would be parallel to S's tangential side through the vertex. Since
that vertex is in the neighbor's side interior, their intersection
would contain a positive-length segment, contrary to the fixed-point
case.

Normalize the incoming magnitude to one. At the limiting forward
normal, torque forces

\[
                          \mu_+=t+\frac{s}{2d}.
\]

Translation consequently requires

\[
                2m=(s,-s/(2d)),
 \qquad 2(m_x+2a_0m_y)=-s/d<0.
\]

This again lies strictly outside the cone of nonnegative combinations
of \((a_0,\pm1/2)\). Zero circle weights are included in the exclusion.

There are finitely many actual fixed-point alternatives. Their other
normal is fixed in the genuine vertex/side or side/vertex case. The
outgoing magnitude, after the above normalization, is a continuous
ratio of positive origin moments near the limiting forward normal.
The strict violations therefore persist on a sufficiently small open
interval immediately beyond \(e_y\). Intersect these restrictions
with the previously selected radial-pair intervals. They remain
nonempty open intervals. The already excluded three-radial runs stay
excluded, and all later finite open-dense choices remain available.

No point-only alternative survives. The other positive contact must
therefore be a shared-side segment. The outer and inner radial faces
are already impossible, and the forward tangential face has the wrong
moment sign, so the segment is on the backward tangential face.
Uncrossing and thinning preserve the forward point normal, while all
possible fixed-point alternatives were listed beforehand. This proves
the strengthened predecessor assertion for the final selected C7.

## 8. A symmetric choice removes singleton endpoints of every radial pair

One can strengthen Section 7 to both endpoints by making the choice
separately on each maximal physical radial run. This replaces the
uniform directional choice on runs of length two; it retains all the
conclusions already proved for the final selected C7.

If the physical circle-contact graph is not a C7, it cannot underlie
an all-boundary positive C7, and no further choice is needed for this
branch. Otherwise its maximal radial runs are fixed by the physical
packing and do not share radial/radial edges.

For a run of length at least three, keep the uniform forward near-axis
choices from Sections 4--5. Such a run cannot appear in the selected
positive C7. For a maximal run of exactly two, its two outside
neighbors are nonradial. If either outside contact is point-only,
apply the proof of Section 7 at that endpoint. If it is the forward
endpoint, reflect the circular order and use the other endpoint of
the same common-normal interval. This is precisely the reflected
fixed-point calculation, with the corresponding strict cone failure.

The outside point-contact normal is fixed: a vertex/vertex outside
neighbor would be radial by the shell lemma and would extend the
run, while a genuine vertex/side contact has its unique side normal.
Thus the continuity restriction used in Section 7 supplies a genuine
nonempty open interval on this radial/radial edge. If both outside
contacts are point-only, choose either one to exclude the run.

If both outside contacts are positive-length shared sides, retain
the original forward interval. No exclusion of this run is claimed.
Since distinct maximal runs use distinct radial/radial edges, all
these choices are simultaneous. They are open restrictions and remain
compatible with the finite generic exclusions and the pinned-profile
choices. Surviving point normals are preserved by uncrossing and
thinning, as before.

The final selected C7 therefore has the following stronger property:

**Two-sided radial-pair reduction.** Every surviving radial/radial
edge joins the radial endpoints of two nonsingleton shared-side
blocks. Each radial body has its other positive contact on its
outward-in-the-run tangential shared side. In particular no radial
singleton is incident to a free vertex edge.

The no-three-run and at-most-four-radial conclusions still hold:
long physical runs were excluded by the original choice, and a
surviving two-body run has no radial continuation. The predecessor
statement of Section 7 is also retained, now as part of the two-sided
conclusion.

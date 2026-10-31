# Circle-touching contacts follow angular order

**Status: complete global geometric reduction in the declared radius
window.** Among the physical squares that touch the containing circle,
every contact joins consecutive center directions, along an empty
minor angular arc of length strictly less than \(2\pi/5\). Each such
square also has total angular shadow strictly less than \(\pi/3\).
Consequently the graph induced by all circle-touching squares has
maximum degree two and no cycle of length at most six.

For a positive physical stress component in which every body is
circle-touching, the conclusion is stronger: it is exactly a seven-cycle,
contains every physical square touching the circle, and all remaining
physical squares lie strictly inside the circle. Some circle-touching
bodies may have zero circle multiplier. This eliminates every such
five- or six-body component, without assuming a planar body graph.
It does not yet settle the completion capacity of the general
seven-cycle.

Throughout,

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad Q=\frac{1105}{256}.
 \tag{1}
\]

Squares have side length one and disjoint open interiors. A square is
*circle-touching* if it has a point on the containing circle; such a
point must be a corner. A square is *loaded* if it carries a positive
circle multiplier in the physical stress certificate. Every loaded
square is circle-touching, but the geometric conclusions apply to all
circle-touching squares, whether their multipliers vanish or not.

## 1. A narrow annulus contains all circle-touching centers

Let \(C\) be the center of a circle-touching square, with orthonormal
side axes \(u,v\), and put \(r=|C|\). Its maximum squared corner norm is

\[
 r^2+\tfrac12+|C\cdot u|+|C\cdot v|=R^2.
 \tag{2}
\]

Since \(|C\cdot u|+|C\cdot v|\ge r\), this gives

\[
 r\le\sqrt{R^2-\tfrac14}-\tfrac12.
\]

The distance from the center to a corner is \(1/\sqrt2\), so the circle
corner also gives \(r\ge R-1/\sqrt2\). Consequently

\[
 R-\frac1{\sqrt2}\le r
 \le\sqrt{R^2-\tfrac14}-\tfrac12.
 \tag{3}
\]

In the entire window (1), the following convenient uniform strict
bounds hold:

\[
                  \boxed{\frac54<r<\frac{61}{40}.}
 \tag{4}
\]

For the lower bound, \(1/\sqrt2<29/40\) follows by squaring, so
\(79/40-1/\sqrt2>5/4\). For the upper bound,

\[
 \sqrt{R^2-\tfrac14}-\tfrac12
 \le\frac{\sqrt{1041}}{16}-\tfrac12
 <\frac{61}{40},
\]

where the last inequality is equivalent to
\(1041<(162/5)^2\). In particular all these centers are nonzero, and
their angular directions are defined.

Two elementary center-distance facts will also be used:

1. Distinct squares have center distance at least one, because their
   open inscribed disks of radius \(1/2\) are disjoint.
2. If two closed squares touch, their center distance is at most
   \(\sqrt2\), by applying the triangle inequality through a common
   point and using each square's circumradius \(1/\sqrt2\).

## 2. Every two circle-touching center directions are more than 36 degrees apart

For two circle-touching centers, let \(\gamma\in[0,\pi]\) be their
minor angular separation and \(r,s\) their lengths.

**Lemma 2.1.**

\[
                        \gamma>\frac{\pi}{5}.
 \tag{5}
\]

Suppose instead that \(\gamma\le\pi/5\). The identity

\[
 \cos(\pi/5)=\frac{1+\sqrt5}{4}>\frac45
\]

uses only \(\sqrt5>11/5\). Therefore

\[
 |C-D|^2=r^2+s^2-2rs\cos\gamma
 <r^2+s^2-\frac85rs.
 \tag{6}
\]

The expression on the right is convex in each variable separately.
Its maximum on the rectangle \([5/4,61/40]^2\) is thus at one of the
four corners. The three distinct corner values are

\[
 \frac58,\qquad \frac{1341}{1600},\qquad
 \frac{3721}{4000}.
\]

Each is strictly less than one. Equation (6) contradicts the
center-distance lower bound, proving (5).

## 3. A circle-touching contact spans less than 72 degrees

**Lemma 3.1.** If the two circle-touching squares physically touch, then

\[
                        \gamma<\frac{2\pi}{5}.
 \tag{7}
\]

Indeed, if \(\gamma\ge2\pi/5\), then by (4)

\[
 \begin{aligned}
 |C-D|^2
 &=(r-s)^2+4rs\sin^2(\gamma/2)\\
 &>\frac{25}{4}\sin^2(\pi/5)\\
 &=\frac{25}{32}(5-\sqrt5)\\
 &>\frac{275}{128}>2.
 \end{aligned}
\]

Here \(\sin^2(\pi/5)=(5-\sqrt5)/8\), and
\(\sqrt5<9/4\). This contradicts the contact center-distance upper
bound \(|C-D|\le\sqrt2\).

**Theorem 3.2 (angular-neighbor contact rule).** The minor angular arc
between the centers of two touching circle-touching squares contains
no center direction of another circle-touching square.

If an intermediate direction existed, the two positive angular gaps
from it to the endpoint directions would sum to \(\gamma<2\pi/5\).
Each is itself a minor angular separation, since the whole arc is
shorter than \(\pi\), and each exceeds \(\pi/5\) by Lemma 2.1.
Their sum would therefore exceed \(2\pi/5\), a contradiction.

Thus all physical contacts among circle-touching squares occur along
consecutive directions in their circular order, using a gap shorter
than \(2\pi/5\). These conclusions do not use force balance, torque,
normal selection, graph planarity, or positivity of circle loads.

## 4. Every circle-touching square casts an angular shadow shorter than 60 degrees

The angular shadow of a square is the set of directions of its points
as viewed from the origin. It is a closed interval of directions,
because the square is convex and does not contain the origin.

**Lemma 4.1.** Every circle-touching square in the window (1) has
angular shadow of length strictly less than \(\pi/3\).

Choose inward side coordinates at one circle corner, and reflect or
exchange the axes if necessary, so the square is

\[
 [a-1,a]\times[b-1,b],\qquad
 a\ge b\ge\tfrac12,\qquad a^2+b^2=q=R^2.
 \tag{8}
\]

The bounds \(a,b\ge1/2\) follow from containment of the two adjacent
corners. Since \(a\ge R/\sqrt2>1\), the square lies strictly in the
right half-plane of this frame and its angular shadow has an ordinary
interval representative.

First suppose \(b\le1\). Put \(h=a-1>0\). The shadow endpoints are
the directions of \((h,b-1)\) and \((h,b)\). Their determinant is
\(h\), and their dot product is

\[
 h^2+b^2-b=q-2a-b+1.
\]

We claim that

\[
 q-2a-b+1>\frac{a-1}{\sqrt3}>0.
 \tag{9}
\]

By Cauchy--Schwarz, it suffices to prove

\[
 q+1+\frac1{\sqrt3}
 >
 \sqrt q\,\sqrt{\left(2+\frac1{\sqrt3}\right)^2+1}.
 \tag{10}
\]

The difference of the squares of these two positive expressions is

\[
 G(q)=q^2-\left(\frac{10}{3}+\frac2{\sqrt3}\right)q
                  +\frac43+\frac2{\sqrt3}.
\]

Since \(q>39/10>1\) and \(2/\sqrt3<7/6\),

\[
 G(q)>q^2-\frac92q+\frac52
       \ge\left(\frac{39}{10}\right)^2
           -\frac92\frac{39}{10}+\frac52
       =\frac4{25}>0.
\]

The displayed quadratic is increasing for \(q\ge39/10\). This proves
(10) and (9). The shadow angle is therefore acute and has tangent
strictly less than \(\sqrt3\), so is less than \(\pi/3\).

Now suppose \(b\ge1\). The shadow endpoints are the directions of
\((a,b-1)\) and \((a-1,b)\), whose determinant and dot product are

\[
 a+b-1,\qquad q-a-b.
\]

The second is positive since \(a+b\le\sqrt{2q}<q\). With \(q\)
fixed, the ratio

\[
 \frac{a+b-1}{q-a-b}
\]

is increasing in \(a+b\), because \(q>1\). It is therefore at most
its value for \(a=b=\sqrt{q/2}\). At that diagonal position the
shadow angle is

\[
                2\arctan\frac1{\sqrt{2q}-1}.
\]

The existing window satisfies \(q>2+\sqrt3\), so
\(\sqrt{2q}-1>\sqrt3\). This angle is strictly less than \(\pi/3\)
as well. Both cases prove the lemma.

## 5. The complete circle-touching graph has only path components, or one seven-cycle

Let \(t\) be the number of physical circle-touching squares. The inner
arc theorem in CYCLIC_GLOBAL_CONTINUATION.md gives \(t\le7\).

When \(t\ge3\), Theorem 3.2 makes their physical touching graph a
subgraph of the cyclic graph on those \(t\) vertices in angular order.
An allowed edge must moreover use its consecutive angular gap of
length less than \(2\pi/5\). Consequently every vertex has degree
at most two.

Any cycle in this graph must traverse the entire circular order:
a proper subgraph of a cyclic graph has no cycle. Its consecutive
angular gaps sum to \(2\pi\), and each gap is strictly less than
\(2\pi/5\). The cycle therefore has at least six vertices. Combining
this with \(t\le7\), it initially has six or seven vertices and contains
all circle-touching squares.

Six vertices are also impossible by Lemma 4.1. To justify using angular
shadows here, the shadows of physically touching squares intersect at
the direction of a shared point. This point is nonzero by (4) and the
square circumradius bound. Each shadow has length less than \(\pi/3\),
so the union of the two intersecting shadows is one arc of length less
than \(2\pi/3<\pi\). It contains both center directions, hence contains
the minor angular arc between those directions. In the cycle this
minor arc is exactly the corresponding consecutive angular gap.
The shadows of the cycle's squares therefore cover every direction.
But six shadows of length strictly less than \(\pi/3\) have total
length strictly less than \(2\pi\), a contradiction.

Thus any cycle is a seven-cycle containing all circle-touching squares.

For \(t\le2\), no cycle is possible. Thus, in every case, the
circle-touching graph is a disjoint union of paths (isolated vertices
included), unless it is one complete seven-cycle.

In particular three circle-touching squares never form a physical
triangle. This is a restriction on the actual touching graph, including
contacts whose stress multiplier is zero.

## 6. A physical contact between circle-touching squares cannot be radial

This auxiliary fact only needs \(R>3/2\).

**Lemma 6.1.** Let \(A,B\subset D_R\) be circle-touching unit squares
with disjoint interiors. Let \(p\in A\cap B\), and let \(n\) be a unit
common supporting normal directed from \(A\) to \(B\). Then

\[
                         \det(p,n)\ne0.
 \tag{11}
\]

Rotate coordinates so that \(n=(1,0)\), and write the supporting line
as \(x=d\), with \(A\) to its left and \(B\) to its right. The width
of a unit square in every direction is at least one. Containment in
the disk therefore gives

\[
                         1-R\le d\le R-1.
 \tag{12}
\]

If \(\det(p,n)=0\), then \(p=(d,0)\).
For \(d\ge0\), take a circle corner \(z\) of \(A\), so \(z_x\le d\).
Then

\[
 |z-p|^2=R^2-2dz_x+d^2
 \ge R^2-d^2
 \ge R^2-(R-1)^2
 =2R-1>2.
\]

Both \(z\) and \(p\) belong to the same unit square, whose diameter
is \(\sqrt2\), a contradiction. If \(d\le0\), take a circle corner
of \(B\) and use \(z_x\ge d\); the same inequality follows.
This proves (11), including the case \(d=0\).

## 7. Every all-circle-touching positive component is exactly a seven-cycle

Use the physical contact stress of PHYSICAL_CONTACT_STRESS.md,
aggregating parallel endpoint atoms at a side contact in the usual
way. Each positive pair edge then has a force \(\mu n\), with
\(\mu>0\), applied at a genuine common point \(p\).

Consider a connected positive stress component with at least one
positive circle multiplier, as in the existing component reduction,
and suppose every one of its bodies is circle-touching. Individual
bodies may have zero circle multiplier. An isolated vertex would have
to carry positive circle load and is impossible because its nonzero
circle resultant could not balance. The nonzero-resultant statement
also follows from CYCLIC_GLOBAL_CONTINUATION.md, Theorem D.

There is no degree-one vertex either. If its circle multiplier is zero,
its one nonzero contact force cannot balance. Otherwise all its circle
forces have zero torque about the origin, and its only contact force
has torque \(\pm\mu\det(p,n)\). Angular equilibrium would force
\(\det(p,n)=0\), contradicting Lemma 6.1, since its neighbor is
circle-touching as well.

On the other hand, every vertex has degree at most two by Theorem 3.2.
The connected finite positive graph is therefore a cycle. Section 5
now shows that it is a seven-cycle and contains every
physical circle-touching square.

It follows in particular that:

- Every positive component on at most six bodies, all of which touch
  the circle, is impossible.
- An all-circle-touching positive component cannot have a chord,
  branch, or bridge, and cannot coexist with another circle-touching
  square outside the component.
- In a nine-square packing with such a component, exactly two remaining
  physical squares are circle-clear; their positions and orientations
  remain unrestricted.

The exact regular seven-cycle in
SEVEN_LOADED_RING_COUNTEREXAMPLE.md shows that the seven-cycle
alternative is realizable below \(Q\). That one explicit ring has
completion capacity one, proved there. A general seven-cycle completion
theorem is still required; no such theorem is asserted here.

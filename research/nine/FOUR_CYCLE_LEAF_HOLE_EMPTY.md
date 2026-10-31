# The entire four-cycle-with-leaf branch has no inner completion square

**Status: complete exact hand region theorem; root and separate independent hand audits passed.**
In the selected physical stress certificate, let the component graph be
a four-cycle with one pendant edge, in the radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

Then no additional unit square can lie on the bounded side of the
four-cycle. This covers the whole C4 graph branch of C1.4.b1, every
load allocation, every contact orientation, and all shared-junction
degeneracies. All four completion squares must be in exterior regions.

The exterior completion bound remains open. This theorem does not close
C1.4.b1 or the unrestricted nine-square lower bound.

## 1. The cycle and the selected physical embedding

Write the positive cycle as

\[
                        A-B-C-D-A,
\]

and let the pendant body L be joined to A. Every positive edge has an
actual shared application point and a genuine common supporting normal.
The normal at a point-only vertex/vertex contact is strictly exposing
for both squares. These conventions are retained by
PHYSICAL_BODY_GRAPH_UNCROSSING.md.

The leaf L is loaded, since an unloaded degree-one body cannot balance
its one nonzero contact force. The radial bridge's central endpoint
theorem makes A physically circle-clear; in particular its circle
weight is zero. The other three cycle vertices B,C,D have positive
graph degree two. Each either has positive circle weight or is a clear
degree-two transmitter. Here “clear” in the latter phrase means zero
circle weight; the transmission argument also applies if a physical
circle contact happens to have zero weight.

Choose one actual aggregate application point for each of the four
cycle edges. Number these points cyclically as p_0,p_1,p_2,p_3, so that
the segment [p_{i-1},p_i] is a chord of one ring square. Put

\[
                    \ell_i=|p_i-p_{i-1}|\le\sqrt2.
 \tag{2}
\]

When the center/contact loop is Jordan, its bounded side is the usual
physical cycle hole, as in CONTACT_RING_HOLE_AREA.md. At a shared
junction use the arbitrarily small physical plane embeddings supplied
by PHYSICAL_BODY_GRAPH_UNCROSSING.md and explicitly formulated in
NO_POSITIVE_K4_SUBGRAPH.md. Each graph edge can be homotoped to its
center/contact broken segment within an arbitrarily small neighborhood
of its two endpoint squares.

There is no extra capacity hidden in the small routing disks. More
precisely, suppose a unit square T has its center on the bounded side
of the embedded cycle. Its center, and every concentric square obtained
by moving its four sides a positive distance inward, have positive
distance from all four closed ring squares. For sufficiently small
routing neighborhoods the edge homotopies avoid that smaller square.
The winding number of the contact polygon

\[
                         P=p_0p_1p_2p_3p_0
 \tag{3}
\]

therefore equals one throughout the open interior of T, after choosing
the positive orientation. One first applies the edge homotopy to its
center. The winding is then constant throughout the connected open
interior of T, which is disjoint from every closed ring square and hence
from every later homotopy. In particular this remains true when each
center is moved to the midpoint of its two contact points.

If two opposite contact vertices in (3) coincide, the contact polygon
is two retraced segments and has zero winding off its edges. If two
consecutive contact vertices coincide, it is a triangle, possibly
degenerate, whose three side lengths are at most sqrt(2). Its area is
at most sqrt(3)/2<1. This elementary maximum-area triangle estimate is
also used in NO_POSITIVE_K4_SUBGRAPH.md. Neither case can contain the
full unit area of T with nonzero winding. Further coincidences only
degenerate these cases. Thus the hypothetical inner square forces all
four contact vertices to be distinct.

With distinct contact vertices the physical center/contact loop is
Jordan: each open center-to-contact segment is in its own square's
open interior, and the two different boundary endpoints of one square
give different rays from its center. Different squares' open strands
cannot intersect. The edge homotopies show that T lies on the bounded
side of this Jordan loop. We can therefore apply
CONTACT_RING_HOLE_AREA.md directly, including its proof that the
limiting contact polygon has winding only zero or one. If H denotes
its winding-one region with the ring squares removed, then

\[
 \operatorname{area}(H)
 \le A(P)-\frac12\sum_{i=0}^3
                         \sqrt{\max(\ell_i^2-1,0)}
 \le\sum_{i=0}^3
       \left(\frac{\ell_i^2}{4}
             -\frac12\sqrt{\max(\ell_i^2-1,0)}\right)
 \le1.
 \tag{4}
\]

The hypothetical T contributes its full unit area to H. All
inequalities in (4) must therefore be equalities.

## 2. Equality forces the aligned four-neighbor cross

For 0\le x\le1, the corresponding summand in (4) is x/4 and
equals 1/4 only at x=1. For 1<x\le2, put u=\sqrt{x-1};
then 0<u\le1 and

\[
 \frac{x}{4}-\frac12\sqrt{x-1}
  =\frac14+\frac14u(u-2)<\frac14.
 \tag{5}
\]

Equality in (4) therefore gives

\[
                         \ell_0=\ell_1=\ell_2=\ell_3=1,
                         \qquad A(P)=1.
 \tag{6}
\]

The four-vertex polygon inequality in CONTACT_RING_HOLE_AREA.md is
the finite Fourier estimate

\[
                       A(P)\le\frac14\sum_i\ell_i^2.

\]

Its equality case is immediate from that proof: only the first positive
Fourier mode can be nonzero. All other modes have strictly smaller
area-to-edge-energy ratio. Thus P is a positively oriented regular
quadrilateral. By (6), it is a unit square.

Also, its interior contains zero area of the ring squares. If an open
chord [p_{i-1},p_i] entered the interior of its ring square, a small
open piece on its inward side would belong both to that square and to
the interior of P. This would have positive area, a contradiction.
Consequently each chord lies on a boundary side of its ring square.
Its length is one, so it is that entire side. The ring square must lie
on the exterior side of P; placement on the interior side would occupy
P itself.

It follows that the four ring squares are exactly the four exterior
unit squares sharing the four sides of the central unit square P.
They have one common frame. Adjacent ring squares meet at precisely
one common vertex, the corresponding vertex of P. In particular all
four cycle contacts are physical point-only vertex/vertex contacts.

This also resolves every potential contact coincidence in the limiting
argument: equality has forced four distinct contact vertices and the
ordinary aligned cross. Any genuinely coincident-contact limit has
strictly less available area and cannot contain T.

## 3. A clear degree-two cycle vertex rules out the cross

Suppose at least one of B,C,D has zero circle weight. Its two positive
contact forces balance, so they are equal and opposite. Torque balance
makes the displacement between their actual application points parallel
to their common force direction. This is the exact degree-two
transmission statement in PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md.

In the cross from Section 2, those two application points are the two
endpoints of the same full inward side of this square. Their difference
is a side vector of length one. Hence both contact-force normals are
parallel to a square side axis.

But both neighboring ring squares have the same frame, and each contact
is a point-only vertex/vertex contact. A side-axis normal is on the
boundary of the vertex normal cone; it is not strictly exposing at
either vertex. This contradicts the selected strict-normal convention.

Thus a hypothetical inner square would force all of B,C,D to be
loaded. No two-load completion theorem is needed in this step; it
also covers every smaller loaded subset of the ring directly.

## 4. Three loaded outer squares force radius squared 5/2

It remains to consider all three of B,C,D loaded. Use the common
frame of the cross and write (x,y) for the center of its central unit
square P. Relabel its sides so that A is the right square, B the top
square, C the left square, and D the bottom square. Their centers are

\[
 (x+1,y),\quad(x,y+1),\quad(x-1,y),\quad(x,y-1).
 \tag{7}
\]

For an aligned unit square centered at (u,v), the largest squared norm
of a corner is

\[
                         (|u|+\tfrac12)^2
                         +( |v|+\tfrac12)^2.
 \tag{8}
\]

A loaded square physically touches the containing circle, so this
maximum equals R^2. Equality of (8) for B and D gives

\[
                       |y+1|=|y-1|,
                       \qquad y=0.
 \tag{9}
\]

Equality for B and C now becomes

\[
 (|x-1|+\tfrac12)^2-(|x|+\tfrac12)^2=2.
 \tag{10}
\]

For x\le0 the left side is 2-2x, so (10) gives x=0.
For 0\le x\le1 it is 2-4x, again giving x=0. For x\ge1
it is -2x and cannot equal2. Therefore

\[
                            x=y=0,
                            \qquad R^2=\frac52.
 \tag{11}
\]

This contradicts (1), since (79/40)^2>5/2. The three-loaded
alternative is impossible as well.

## 5. Complete region conclusion and the remaining exterior task

**Theorem 5.1.** Every selected positive component consisting of a
four-cycle with one pendant edge, in (1), has inner unit-square
capacity zero. The theorem includes every load allocation, physical
zero-weight circle contact, side-contact mean, and multiple-junction
embedding allowed by the selected certificate.

Hence in C1.4.b1.C4 all four additional physical squares lie in
exterior complementary regions of the cycle/leaf core. The K4 block
branch is separately excluded by NO_POSITIVE_K4_SUBGRAPH.md, and the
two diamond block branches have empty triangular holes by
CONTACT_RING_HOLE_AREA.md. Thus the entire remaining C1.4.b1
completion problem is exterior; its sharp joint exterior capacity is
not proved here.

No whole-cell closure, equality classification for nine squares, Lean
compilation, or CI result is claimed.

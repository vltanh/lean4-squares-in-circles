# A four-square contact ring with three boundary squares has no central unit

**Status: complete uniform hand region theorem; root and separate
independent full hand audits passed.**

Let H,A,B,C be four actual, contained, interior-disjoint unit squares,
with physical ring H--A--B--C--H and the physical plane embedding of
the common selected certificate. Assume at least three ring squares
physically touch the containing circle and
\[
                               R^2\ne5/2.
\tag{1}
\]
The declared radius window \(79/40\le R\le\sqrt{1105}/16\) satisfies (1).
Every other physical square remains, with every ring contact point,
original mean and weak shared junction retained.

**Theorem.** The bounded side of this ring has unit-square capacity zero.
No degree, positive circle weight, root equation, pendant leaf,
secondary minimizer or restriction on forces outside the ring is needed.

The full area and equality proof is reproduced below to make the
leaf-independent and weight-independent scope explicit. It is exactly
the geometric argument of FOUR_CYCLE_LEAF_HOLE_EMPTY.md, Sections1--2
and4. Its transmitter argument in Section3 is not used.

## 1. The actual contact polygon and all weak junctions

Choose the four unchanged actual ring applications p_0,p_1,p_2,p_3
in cyclic order. Each segment from p_(i-1) to p_i is a chord of its
actual unit square. Its length satisfies
\[
                             \ell_i\le\sqrt2.
\tag{2}
\]
The selected physical embedding is supplied by
PHYSICAL_BODY_GRAPH_UNCROSSING.md: each embedded graph edge can be
homotoped to its center/contact broken segment within arbitrarily
small neighborhoods of the two actual endpoint squares. At a shared
junction retain the arbitrarily small routing disks of that theorem;
do not prescribe a new force mean.

Suppose another contained unit T has its center on the bounded side
of this embedded ring. Every point of the open interior of T is
disjoint from all four closed ring squares. Every smaller concentric
closed square inside T has positive distance from them. For sufficiently
small routing neighborhoods, the contact-polygon homotopy avoids that
smaller square. Thus, with positive orientation, the polygon
\[
                             P=p_0p_1p_2p_3p_0
\tag{3}
\]
has winding one throughout the open interior of T. One first carries
the winding at T's center through the edge homotopy, then uses its
constancy on the connected open interior disjoint from every ring
chord. This remains valid when each ring center is moved to the
midpoint of its two actual applications.

All coincidences are retained. If opposite p_i coincide, P consists
of two retraced segments and has winding zero off its edges. If
consecutive p_i coincide, P is a possibly degenerate triangle with
side lengths at most sqrt(2), hence area at most sqrt(3)/2<1.
Further coincidences only degenerate these cases. None can contain
the full unit area of T with winding one. A hypothetical T therefore
forces four distinct contact vertices.

With these vertices distinct, the center/contact loop is Jordan:
each open center-to-contact segment lies in its own square's open
interior, and the two different boundary points of one square give
different rays from its center. Strands in different square interiors
cannot meet. The limiting polygon has winding only zero or one, as
proved in CONTACT_RING_HOLE_AREA.md. Its winding-one region with the
ring squares removed has area \(\mathcal A\) satisfying
\[
 \begin{split}
 \mathcal A
 &\le A(P)-\frac12\sum_{i=0}^3
                     \sqrt{\max(\ell_i^2-1,0)}\\
 &\le\sum_{i=0}^3\left(
          \frac{\ell_i^2}{4}
             -\frac12\sqrt{\max(\ell_i^2-1,0)}\right)
 \le1.
 \end{split}
\tag{4}
\]
These are the complete chord-cut area and four-vertex polygon
inequalities of that source. They involve only the physical ring
squares. Any square T in its bounded complementary region contributes
its entire unit area to \(\mathcal A\). Thus equality is necessary at
every step of (4).

## 2. Equality forces the entire aligned cross

For \(0\le x\le1\), the summand in (4) equals x/4 and reaches1/4
only at x=1. For \(1<x\le2\), set \(u=\sqrt{x-1}\), so \(0<u\le1\).
Then
\[
 \frac{x}{4}-\frac12\sqrt{x-1}
       =\frac14+\frac14u(u-2)<\frac14.
\tag{5}
\]
Equality in (4) therefore forces
\[
                \ell_0=\ell_1=\ell_2=\ell_3=1,\qquad A(P)=1.
\tag{6}
\]
The polygon inequality \(A(P)\le\frac14\sum_i\ell_i^2\) has equality
only for a positively oriented regular quadrilateral. For completeness,
its finite Fourier proof has only the first positive mode at the
maximal area-to-edge-energy ratio; every other nonconstant mode has
strictly smaller ratio. Equality leaves only that mode and an arbitrary
translation. Equation (6) makes P a unit square.

Its interior has zero area occupied by the ring squares. If the
relative interior of any chord [p_(i-1),p_i] entered its own ring
square's interior, a small open piece on the chord's inward side
would lie both in that square and in P, with positive area. Hence each
chord lies on a side of its actual ring square. Its length is one,
so it is the entire side. The ring square occupies the exterior
side of P, since occupying its interior side would occupy P itself.

Consequently the four ring squares are exactly the four exterior
neighbors sharing the four sides of the central unit square P.
All five have one common frame. Adjacent ring squares meet at one
vertex of P. This equality description also resolves every weak
junction: the only possible unit-capacity limit has four distinct
contact vertices and the ordinary aligned cross.

## 3. Three physical boundary squares force the forbidden radius

At least three of the four exterior cross squares physically touch
the circle. Label the possibly unprescribed one as the right square.
If all four touch, choose any one as that square. Write (x,y) for the
center of P in the common orthonormal frame about the unchanged
circle origin. The three prescribed boundary-square centers are
\[
                    (x,y+1),\qquad (x-1,y),\qquad (x,y-1).
\tag{7}
\]
An aligned unit centered at (u,v) has maximum corner norm squared
\[
                      (|u|+1/2)^2+(|v|+1/2)^2.
\tag{8}
\]
Containment and physical circle contact say that this maximum is
exactly R^2. No positive circle multiplier is needed.

Equality of (8) for the top and bottom squares gives
\[
                       |y+1|=|y-1|,\qquad y=0.
\tag{9}
\]
Equality for the top and left squares then gives
\[
           (|x-1|+1/2)^2-(|x|+1/2)^2=2.
\tag{10}
\]
For x<=0 its left side is 2-2x. For 0<=x<=1 it is 2-4x.
For x>=1 it is -2x. The only solution is x=0. Thus
\[
                                x=y=0,\qquad R^2=5/2,
\tag{11}
\]
contradicting (1). The whole bounded free region therefore has
capacity zero.

## 4. Actual use for the triangle-attached three-load C4

For the actual component H--A--B--C--H with intact H--X--Y--H,
the ABC load orbit makes A,B,C physical boundary squares. The
theorem applies to the C4 without changing H's true degree four,
any force, any physical mask, any original shared mean, or any of
the three completion squares. It also applies to the C4 inside
larger graphs whenever its stated physical boundary premise holds.

The adjacent HXY triangular hole is independently empty by
CONTACT_RING_HOLE_AREA.md. The actual boundary-pair exterior
pockets at AB,BC,XY are independently empty by
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md. These facts do not by
themselves prove a joint capacity bound for the two remaining
articulation pockets. Their complete orientation and attachment
domains, possible weak junctions, and all three extra units remain
a separate obligation. No single-pocket capacity is inferred here.

The theorem is purely geometric once the actual plane contact ring
is specified. It has no canonical-minimizer or force-selection
conclusion, changes no original equality configuration, and uses
no sampled poses, Lean compilation or CI.

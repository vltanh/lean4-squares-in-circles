# The whole five-body two-load family reduces to P.ALL

**Status: the whole-family reduction is CLOSED by a hand proof.** Every
five-body parallel-layer core supplied by the two-load rigidity theorem
either contains an actual four-square member of family P or admits at
most three further physically nonoverlapping unit squares. Consequently
the five-body family creates no completion obligation beyond P.ALL.

This is a reduction, not a proof of P.ALL. The unrestricted nine-square
theorem remains conditional on that and the other outstanding families.
The added squares may have arbitrary independent orientations. No Lean
compilation or CI has been run.

## 1. The complete five-body geometry and its singleton height

Let
\[
D=\{(x,y):x^2+y^2\le17/4\},\qquad
E=[1,2]\times[-1/2,1/2],\qquad W=-E.
\]

The parallelism and layer theorem in
[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md),
Sections 6--7, puts every five-body positive component with exactly
two circle-loaded bodies into the following form, after exchanging
left and right if necessary:

- the loaded terminals are \(E,W\);
- one aligned internal square has center \((-1/2,t)\);
- two aligned internal squares have centers \((1/2,l)\) and
  \((1/2,u)\), where
  \[
  -1<l<0<u<1,\qquad u-l\ge1.                              \tag{1}
  \]

The strict height interval \((-1,1)\) follows from the strictly
exposing-normal choice at point-only vertex/vertex contacts, as stated
in the cited theorem. The height gap follows from physical nonoverlap
within one column. Ordering the two heights then gives their strict
opposite signs in (1).

The singleton satisfies the sharper bound
\[
                              |t|\le1/2.                  \tag{2}
\]
Here is its force-and-torque derivation; it does not impose that bound
on either member of the doubled column. The terminal \(W\) has only
the singleton as a positive contact neighbor. Every such contact force
is horizontal, has the same sign, and is applied at a common point
\((-1,p_y)\) of those two squares. Take torque balance for \(W\)
about the disk origin. Each circle force is radial at its application
point and has zero torque about that origin. Since the contact-force
magnitudes \(\mu_j\) are positive and all signs agree, the remaining
equation is
\[
                              \sum_j\mu_j p_{y,j}=0.
\]
Thus the weighted mean of the contact heights is zero. Every contact
point belongs to the singleton, so every such height lies in
\([t-1/2,t+1/2]\). Its weighted mean does too, proving (2).
Torque about the origin is equivalent to the usual torque about the
body center because total force is zero.

For the physical completion theorem below, it is enough to assume
the displayed five core squares lie in \(D\), have disjoint open
interiors, and satisfy (1)--(2). No stress equations for the additional
squares will be used.

## 2. The branch that already contains family P

If either \(l\) or \(u\) lies in \([-1/2,1/2]\), choose that height
as \(v\). The four core squares with centers
\[
(-3/2,0),\quad(-1/2,t),\quad(1/2,v),\quad(3/2,0)
\]
are exactly a member of family P, with both slider parameters in the
full allowed closed interval. In a nine-square packing, the other core
member together with four further squares would give the five-square
completion prohibited by P.ALL. This entire branch is therefore an
actual geometric reduction to that existing gate, including its
boundary slider values.

It remains to handle the full complementary parameter domain
\[
                              l<-1/2,\qquad u>1/2.         \tag{3}
\]
We will prove directly that this branch admits at most three further
squares, so its total capacity is at most eight.

## 3. Every extra center has a strictly negative horizontal coordinate

Let \((x,y)\) be the center of any additional square \(T\).
[DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md) gives
\[
                         |(x,y)|\le3/2,\qquad -1<x<1.     \tag{4}
\]
The open disk of radius \(1/2\) about this center lies in
\(\operatorname{int}T\), so its distance to every closed core square
is at least \(1/2\).

If \(x\ge0\), then \(x\in[0,1)\) lies in the horizontal span of
both right-column core squares. Their center-height forbidden
intervals are \((l-1,l+1)\) and \((u-1,u+1)\). They overlap because
\(u-l<2\), and therefore avoidance forces
\[
                         y\le l-1\quad\text{or}\quad y\ge u+1.
\]
By (3), these alternatives give \(y<-3/2\) or \(y>3/2\), both
contrary to (4). Hence every additional square has
\[
                                  -1<x<0.                 \tag{5}
\]

Its horizontal center coordinate is consequently in the left
singleton's span \([-1,0]\). The same disk-distance calculation gives
\[
                         y\le t-1\quad\text{or}\quad y\ge t+1.
                                                                    \tag{6}
\]
Reflecting the whole configuration in the horizontal axis, and
relabeling the doubled heights, preserves (1) and (3). We may thus
assume from now on
\[
                                  0\le t\le1/2.            \tag{7}
\]
Call the two alternatives in (6) lower and upper, respectively.

## 4. There is at most one upper extra

The core covers the full segment
\[
                              [-2,2]\times\{1/2\}.         \tag{8}
\]
Its middle left part belongs to the singleton by (7); its middle right
part belongs to the upper right square since \(1/2<u<1\); its end
parts belong to terminal edges.

An upper extra has center height \(y\ge t+1\ge1\). Every point of
that extra has \(-2<x<2\), by the radial-terminal outer-face screen
in [RADIAL_SECTOR_POCKET_CAPACITY.md](RADIAL_SECTOR_POCKET_CAPACITY.md).
If any point of it had height below \(1/2\), the segment from that
point to its interior center would cross (8) at an interior point of
the extra. Every open neighborhood of a point on (8) meets the
interior of a core square, including at seams and terminal edges.
That would be physical overlap. Thus every upper extra lies wholly in
\(D\cap\{y\ge1/2\}\).

By [HALF_CAP_CENTER_SEPARATION.md](HALF_CAP_CENTER_SEPARATION.md),
two different squares in this cap must have centers of strictly
opposite horizontal signs. All additional centers have negative
horizontal coordinate by (5). Consequently there is at most one
upper extra.

## 5. A vertex obstruction routes every lower extra below the axis

The core need not cover the positive horizontal axis: under (3), the
right column has an open gap around height zero. We retain that gap
and prove the required whole-square routing directly.

The core does cover
\[
                              [-2,0]\times\{0\},          \tag{9}
\]
using \(W\) and the singleton. A lower extra satisfies, by (6)--(7),
\[
                                  y\le t-1\le-1/2.        \tag{10}
\]
Suppose nevertheless that this square has some point of positive
height. Its top vertex has positive height. That vertex must have
strictly positive horizontal coordinate: otherwise the segment from
the interior center \((x,y)\), with \(-1<x<0\), to the top vertex
crosses (9) at an interior point of the extra, giving physical overlap
as before. The outer-face screen ensures that the crossing lies in
the covered segment.

Choose frame parameters
\[
a\ge b\ge0,\quad a^2+b^2=1,\qquad
h=(a+b)/2,\quad k=(a-b)/2.
\]
For negative tilt, with axes \((a,-b),(b,a)\), the top vertex is
\((x-k,y+h)\). Its horizontal coordinate is negative by (5), so this
tilt is impossible. The axis-aligned case also cannot have a positive
top height, by (10). We are left with positive tilt, with axes
\((a,b),(-b,a)\), whose top vertex is
\[
                                  (x+k,y+h).
\]
The preceding argument gives
\[
                                  x+k>0,\qquad y+h>0.      \tag{11}
\]
Its rightmost vertex is \((x+h,y-k)\). From (5), (10), and (11),
\[
             0<x+h<h<1,\qquad -1\le-a<y-k\le-1/2.          \tag{12}
\]
For the vertical lower bound, \(y>-h\) in (11) gives
\(y-k>-h-k=-a\ge-1\). The doubled lower height obeys
\(-1<l<-1/2\), so
\[
                                  l-1/2<-1,\qquad l+1/2>-1/2.
\]
Thus (12) puts the rightmost vertex strictly inside the lower-right
core square \([0,1]\times[l-1/2,l+1/2]\). A vertex of one closed
square lying strictly inside another forces their open interiors to
intersect, a contradiction.

This proves that every lower extra lies wholly in \(y\le0\), without
filling or discarding the right-column gap.

## 6. At most two lower extras; conclusion for the whole family

Every lower extra is now a whole square in the lower half-disk, and
all its center horizontal coordinates lie in \((-1,0)\). If three
such squares existed, two consecutive horizontal center coordinates
would differ by less than \(1/2\). The reflected pair rigidity theorem
in [HALF_DISK_CLOSE_CENTER_RIGIDITY.md](HALF_DISK_CLOSE_CENTER_RIGIDITY.md)
would then force a square centered at \((0,-3/2)\). That contradicts
the strict center-sign bound (5). There are at most two lower extras.

There is at most one upper extra and at most two lower extras. By (6)
these exhaust every additional square. Therefore the residual branch
(3) has at most three additional squares and at most eight squares in
total. Together with Section 2, this proves:

**Theorem.** Every nine-square packing in \(D\) containing a five-body
two-load parallel-layer core contains an actual four-square member of
family P, with both slider parameters in \([-1/2,1/2]\). Equivalently,
P.ALL implies the full five-body two-load completion exclusion.
\(\square\)

## 7. Consequence for the entire two-load class

The two-load rigidity theorem allows only four-, five-, or six-body
positive components in the declared working radius window, and forces
\(R^2=17/4\). Its four-body family is exactly P. The whole six-body
family is excluded from nine-square packings by
[SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md).
The present theorem reduces every five-body case to P as well.

Consequently every hypothetical nine-square packing in that window
having a selected positive component with exactly two circle-loaded
bodies must contain an actual family-P skeleton. This closes the
whole two-load reduction to P.ALL; it does not prove that remaining
completion gate, and it makes no assertion about components with three
or more loaded bodies.

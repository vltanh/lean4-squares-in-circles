# n=9 G2: inner-pair shadow domination, valid with OBLIQUE separators

**Status (2026-10-22): complete orientation-independent hand lemma.**
This is an unrestricted implication **conditional only on the existence
of four squares with disjoint projections along one direction**;
it does NOT assume all remaining square pairs have common x/y
separating axes. In particular it remains valid when some of the five
remaining squares can only be separated by oblique own-frame axes.

**Theorem.** Suppose nine independently oriented unit squares with
disjoint open interiors fit in a disk of squared radius
\(q\le1105/256\). Suppose four squares \(M_1,M_2,M_3,M_4\)
have pairwise disjoint interior projections onto some fixed
direction e, ordered from left to right. Then *each of the
other five squares has an open e-projection intersecting
the open e-projection of at least one of the two middle
squares \(M_2,M_3\)*.

Thus, however oblique its actual geometric separator,
no other square can lie exclusively in the shadow
of the leftmost or rightmost member of the four-chain.

## Proof

Rotate the whole plane so e is horizontal, and
translate the containing circle's center to the origin.
For any unit square S with center c and orthogonal
unit side vectors u,v, its farthest corner obeys
\[
 q\ge |c|^2+\tfrac12+|c\cdot u|+|c\cdot v|
       \ge |c|^2+\tfrac12+|c|.
\]
Exactly as in FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md,
\[
             |c|<\rho:=61/40. \tag{1}
\]

For every square, its horizontal projection halfwidth
\(h_S=(|u\cdot e|+|v\cdot e|)/2\)
is at least 1/2. For a disjoint projection chain of
four squares the horizontal centers satisfy
\(x_{i+1}-x_i\ge1\), whence
\[
 -61/40<x_1<-59/40,\qquad
 -21/40<x_2<-19/40,
\]
and their reflected analogues for \(x_3,x_4\).
In particular, from (1) and \(|x_1|>59/40\),
\[
 |y_1|^2<\rho^2-(59/40)^2=3/20<(2/5)^2,
 \quad\text{so }|y_1|<2/5. \tag{2}
\]

By the full-projection shadow barrier
FOUR_CHAIN_SHADOW_BARRIER.md (Theorem 2.1),
any other square T has an open horizontal
projection meeting at least one chain square's
open projection.

Suppose T's projection met neither middle
projection. By connectedness of projection
intervals, it must meet **only** the leftmost
projection or **only** the rightmost one;
it cannot jump over either middle interval.

Consider the leftmost case. Let
\[
 I_i=[x_i-h_i,x_i+h_i],\qquad
 J=[x_T-h_T,x_T+h_T].
\]
Since J meets the interior of I_1 but not of I_2,
and I_1 lies left of I_2, necessarily
\[
 \sup J\le\inf I_2=x_2-h_2.
\]
Therefore
\[
 x_T+h_T\le x_2-h_2,\qquad
 x_T\le x_2-h_2-h_T\le x_2-1<-59/40.
 \tag{3}
\]
Using the center radius bound \(x_T>-\rho\),
(3) gives
\[
          -61/40<x_T<-59/40.
\]
As in (2), \(|y_T|<2/5\).
Both T and M_1 consequently have
\[
 |x_T-x_1|<2/40=1/20,\qquad
 |y_T-y_1|<4/5.
\]
Their squared center distance is strictly less than
\[
                     (1/20)^2+(4/5)^2
                       =257/400<1. \tag{4}
\]

But **any two independently oriented unit squares
with disjoint open interiors have center distance
at least 1**: each square contains an open Euclidean
disk of radius 1/2 about its center, and those
disks must be disjoint. This contradicts (4).

The exclusive-rightmost case is identical after
reflecting the horizontal direction. Thus T must
meet the open projection of M_2 or M_3.
\(\square\)

## Scope and structural consequences

This proves the *unconditional-on-frames inner-pair incidence*
once the four-chain exists. No global coordinate-separability
hypothesis or same-orientation assumption is used.

Combining this with FOUR_CHAIN_SHADOW_BARRIER.md,
each of the five extra squares has a consecutive
projection-incidence block containing index 2 or 3.
The original nine possible nonempty blocks thereby
reduce to the following **seven** blocks:
\[
 \{2\},\{3\},\{1,2\},\{2,3\},\{3,4\},
 \{1,2,3\},\{2,3,4\}.
\]
This is a structural reduction, not a completed
enumeration of the five remaining squares.

**Important:** the three-block types {1,2,3} and {2,3,4}
must NOT be discarded without proof. A sufficiently
rotated free square can have horizontal projection
meeting three consecutive aligned anchor squares,
while being physically separated from all of them
by the vertical direction. In particular, the
conclusion is exactly 'one of the inner two shadows',
not 'one of five special types' or a forced
two-by-four grid.

The main OPEN gates remain:

- Existence of a four-chain (or another terminal
  sharp stress) from unrestricted nine-square Packing;
- A complete global obstruction for other-square
  interactions with the inner pair, allowing real
  oblique separating axes;
- The coherent-side branch in the common-coordinate
  separable subclass.

No Lean compilation/CI/kernel claim is made.

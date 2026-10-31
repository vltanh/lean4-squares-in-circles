# Every all-shared short seven-cycle forces an exact radius below two

Date: October 30, 2026. Author: joint-pockets continuation.
Input mathematical tree: `3132896f3c306faecfdd69daafb0b577bf7d70a1`
(the mathematical sources are unchanged from the preceding checkpoint).

**Status: complete proposed whole-family hand exclusion, awaiting separate
independent review.** In the closed project window, an entire positive
seven-cycle whose unloaded vertices are isolated and whose seven positive
contacts are genuinely shared sides cannot occur in a nine-square packing.
The proof retains every actual shared mean, every physical circle mask,
every individual zero circle coefficient, every additional zero-weight
physical contact, and both other actual squares.

It derives exactly four loaded bodies and the exact radius

\[
                         R^2=\frac{2257}{576}<4.             \tag{0.1}
\]

The contradiction is with the independent same-nine theorem `R>2`.
This is not a claim that the seven-body core alone is impossible, and
it is not a motion of a shared block. In particular no requirement
that the loaded bodies have unique physical circle corners, or only
two actual physical neighbors, is imposed. The proof derives the
loaded masks at the end, using their full original circle loads.

The precise geometric hypothesis used is slightly wider than genuine
sharing: all seven body frames are parallel to one common orthonormal
frame, and all seven positive aggregate normals are common frame axes.
The argument applies whenever these two facts have been independently
established. Common body frames alone do not automatically assert the
second fact at a strict vertex/vertex contact.

## 1. Full original cycle and the common-axis consequence of sharing

Work in

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                                  \tag{1.1}
\]

Retain an actual compatible selected physical force-and-torque
certificate for all original squares. Let an entire positive component
be a simple cycle on seven bodies. Assume no two unloaded cycle
vertices are adjacent. Every cycle body therefore has full positive
pair degree exactly two. An unloaded body may still physically touch
the circle with zero selected coefficients.

Assume each of its seven positive intersections is a positive-length
shared side. Two unit squares sharing such a segment have the same
pair of side axes, up to interchanging and reversing them. Connectivity
of the cycle gives one common orthonormal frame for all seven actual
squares. Each shared-side normal is a signed common axis. Aggregation
may put its actual application anywhere in its full physical shared
segment, including an endpoint; no choice of a mean is made below.

More generally, the rest of the proof needs only these resulting
common-frame and common-axis-normal facts. It does not inspect the
length of an individual positive intersection again.

Let k be the number of loaded cycle vertices. Isolation of the
unloaded vertices on a seven-cycle gives `k>=4`. Thus the complete
theorem in `SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md` applies. It retains
every physical mask and gives a strictly convex contracted polygon
of the k loaded concurrences, with one strictly left turn at each
loaded vertex and total turn `2pi`.

Every side direction of that polygon is a common frame axis. A
strict turn between such directed axes, being strictly between zero
and pi, is exactly `pi/2`. Hence

\[
                                  k=4.                     \tag{1.2}
\]

All three unloaded bodies are side-normal transmitters: their original
normal is a common own-side axis, so their exact support width is one.
Their isolation puts them on three different contracted edges. The
four physical reserves in cyclic order are therefore three ones and
one zero. This includes all initial five- and six-load alternatives:
they were already excluded by the turn count, not assigned four loads.

## 2. The four exact center projection gaps

Rotate and, if necessary, reflect the common axes and cyclic labels
so that the zero-reserve edge is on the eastern side of the strictly
convex force rectangle. Denote its four loaded bodies in their
rectangle order by E+, W+, W-, E-. These names initially describe
positions in the force rectangle, not assumed signs of their centers.

The three nonempty channels are the northern, western and southern
ones. The eastern edge is a direct loaded-to-loaded contact. Write
the actual centers as `c_(E+),c_(W+),c_(W-),c_(E-)`.

On a horizontal channel from a left loaded body to a right loaded
body, the actual endpoint applications have x coordinates equal to
their respective center coordinates plus `1/2` and minus `1/2`.
The application difference along the actual channel is its reserve.
Consequently the horizontal center gap is `1+reserve`. The identical
statement holds vertically. It retains every transverse application
mean and needs no equality of transverse center coordinates.

The exact four equations are therefore

\[
\begin{aligned}
 (c_{E+})_x-(c_{W+})_x&=2,\\
 (c_{W+})_y-(c_{W-})_y&=2,\\
 (c_{E-})_x-(c_{W-})_x&=2,\\
 (c_{E+})_y-(c_{E-})_y&=1.                                \tag{2.1}
\end{aligned}
\]

The exact normal-channel telescope supplying these equations follows
from the original unloaded two-force and torque equations. No internal
square is physically replaced by a segment, and no positive contact
or branch is removed to obtain degree two.

Let the positive force magnitudes on these contracted edges be
`mu_N,mu_W,mu_S,mu_E`. They are the original magnitudes, preserved
across each unloaded transmitter by its full force balance. The
loaded circle resultant `m_i` retains all its actual corners:

\[
                  m_i=\sum_a\lambda_{ia}z_{ia},\qquad
                  \lambda_{ia}\ge0,\quad
                  \Lambda_i:=\sum_a\lambda_{ia}>0.          \tag{2.2}
\]

Each actual active corner has norm R. The four unchanged force
equations, in the common frame, are

\[
\begin{aligned}
 2m_{E+}&=(\mu_N,\mu_E),&
 2m_{W+}&=(-\mu_N,\mu_W),\\
 2m_{W-}&=(-\mu_S,-\mu_W),&
 2m_{E-}&=(\mu_S,-\mu_E).                                  \tag{2.3}
\end{aligned}
\]

These are equations at the four original loaded stars. They make no
assumption about their individual corner-weight splits or about the
forces and physical contacts of either additional square.

## 3. A positive-load comparison rigidity lemma

We record explicitly the small convexity argument used here. Suppose
another choice of centers `c_i'=c_i+d_i` for these four common-frame
squares has the following two properties:

1. Each translated whole square individually remains in the same disk
   `D_R`. Mutual nonoverlap of this comparison collection is not needed.
2. It satisfies the same four exact projected gap equations (2.1).

The difference of those gap equations, dotted with the original forces
in (2.3), gives

\[
\begin{split}
 2\sum_i m_i\cdot d_i
  ={}&\mu_N((d_{E+})_x-(d_{W+})_x)
       +\mu_W((d_{W+})_y-(d_{W-})_y)\\
     &+\mu_S((d_{E-})_x-(d_{W-})_x)
       +\mu_E((d_{E+})_y-(d_{E-})_y)=0.                    \tag{3.1}
\end{split}
\]

For every original circle atom at i, its translated point `z_ia+d_i`
is a vertex of the comparison square, and therefore has norm at most R.
Since `|z_ia|=R`, the exact squared-norm expansion gives

\[
                  2z_{ia}\cdot d_i+|d_i|^2\le0.
\]

Multiply by its original nonnegative coefficient and sum all original
atoms and bodies. Using (2.2)--(3.1),

\[
                    0+\sum_i\Lambda_i|d_i|^2\le0.
\]

Every total load `Lambda_i` is strictly positive, so every `d_i=0`.
Thus the original four loaded centers are the only individually
contained common-frame centers satisfying the same projected gaps.

This is a comparison of the original equations with exact circle
inequalities. It is not a claim that the comparison collection is a
new feasible packing, and it uses neither a canonical Phi minimum
nor an attempted rigid motion of a shared block. Two physical circle
corners, a zero coefficient at either corner, and arbitrary genuine
shared-side means all remain literal throughout.

## 4. Reflection forces the complete center symmetry

Let `F(x,y)=(x,-y)`. Form comparison centers by reflecting and
interchanging the upper and lower labels:

\[
\begin{aligned}
 c'_{E+}=F(c_{E-}),\quad&c'_{E-}=F(c_{E+}),\\
 c'_{W+}=F(c_{W-}),\quad&c'_{W-}=F(c_{W+}).                 \tag{4.1}
\end{aligned}
\]

Every comparison square is contained in `D_R`: because all square
frames are the same common axes, translating the original label's
square to its new center gives exactly the reflected partner square
as a set. The disk is invariant under F. This statement includes
every translated vertex of the original label, whether or not it
was one of that label's positive circle atoms.

The northern gap of the comparison collection is the original
southern gap, and conversely; both are two. Its western vertical
gap is the original western gap, still two. Its eastern vertical
gap is the original eastern gap, still one. Thus all four equations
(2.1) are preserved exactly.

The comparison rigidity lemma gives `c_i'=c_i` at all four labels.
Together with (2.1), this forces real numbers u,v with

\[
\begin{gathered}
 c_{E+}=(u,1/2),\quad c_{E-}=(u,-1/2),\\
 c_{W+}=(v,1),\quad c_{W-}=(v,-1),\qquad u-v=2.            \tag{4.2}
\end{gathered}
\]

No geometric or force symmetry was assumed before this deduction.
The original shared means and all transmitter transverse positions
have not been fixed or averaged.

## 5. The physical masks and radius are now exact

Containment and `R<5/2` force

\[
                              u>0>v.                       \tag{5.1}
\]

Indeed, if `u<=0`, then `v=u-2<=-2`, and the western square has
a vertex with x coordinate at most `-5/2`. If `v>=0`, the eastern
square has a vertex with x coordinate at least `5/2`. Both contradict
the project upper radius. This proves (5.1) without making a prior
claim about the direction of a two-corner resultant.

Every coordinate of every center in (4.2) is now nonzero. Hence each
aligned loaded square has a unique farthest corner. Since its actual
total circle load is positive, that corner lies on the same containing
circle. The two-corner physical alternative has been excluded as a
consequence, not erased because of a zero individual weight.

Put

\[
                        a=u+\frac12,\qquad c=\frac12-v.
\]

Their exact actual farthest-corner equations are

\[
                     a+c=3,\qquad
                     R^2=a^2+1=c^2+\frac94.                \tag{5.2}
\]

Subtracting the two squared equalities gives
`(a-c)(a+c)=5/4`. Thus

\[
        a=\frac{41}{24},\qquad c=\frac{31}{24},\qquad
        u=\frac{29}{24},\qquad v=-\frac{19}{24},
\]

and therefore

\[
                \boxed{R^2=\frac{41^2+24^2}{24^2}
                                  =\frac{2257}{576}}.
                                                                  \tag{5.3}
\]

The strict gap below four is the exact positive rational number

\[
                         4-\frac{2257}{576}=\frac{47}{576}.
                                                                  \tag{5.4}
\]

**Theorem 5.1 (whole aligned-axis short-C7 rigidity).** An actual
compatible positive simple seven-cycle in (1.1), with isolated unloaded
vertices, all frames common, and all positive normals common axes,
has exactly four loaded bodies and the exact loaded geometry
(4.2),(5.3). In particular its radius is strictly less than two.
The same conclusion applies whenever all seven positive intersections
are genuinely shared sides, since those physical facts supply both
common-frame hypotheses.

## 6. Complete nine-square exclusion and exact remaining scope

The independent theorem in
`LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md` applies to the original
nine squares, with all their actual frames and contacts unchanged,
and gives `R>2`. Equations (5.3)--(5.4) give `R<2`, a contradiction.
Neither additional square was dropped to invoke that theorem.

**Corollary 6.1 (entire all-shared short-C7 family excluded).** No
original nine-square packing in the closed project window has an
entire positive seven-cycle with isolated unloaded vertices and seven
genuinely shared positive contacts. All five- and six-load candidates
are eliminated by the common-axis turn count; the remaining four-load
candidate is eliminated by its exact radius. Every original circle
mask, shared mean, unloaded transverse position and zero-weight
physical contact is retained.

This applies independently of canonical motion hypotheses and permits
additional actual physical neighbors of every core body. It covers
the whole specified family, not a small mean or angle interval.

The proof does not assert a common body frame for a partially shared
cycle. Nor does it assert that a common-frame cycle has only axis
normals at its possible free vertex/vertex contacts. A separate
selected-certificate argument would be needed to remove that latter
obstruction. Non-isolated unloaded runs, including the long-channel
record equality configurations, do not satisfy the short-run premise
and are not contradicted by (5.3).

The old `C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md` and its pinned-block
callers concern the all-physical-boundary C7 domain. Their virtual
block translations are not treated as feasible motions of a mixed
cycle here. None of their boundary-only exports is imported into this
proof.

## 7. Direct mathematical inputs and verification boundary

The direct source statements below were read in full at the displayed
identities. The reflection, complete circle-mask work, center-gap
algebra and exact radius calculation are proved above.

| Source | SHA-256 | Consumed scope |
| --- | --- | --- |
| `SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md` | `5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635` | Whole-component convex contracted polygon and actual positive turns, for at least three loads and the compatible physical certificate. |
| `PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md` | `ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab` | Exact original normal-channel equations and preservation of force magnitude; no fictitious degree assignment. |
| `LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md` | `3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90` | The unchanged nine-square conclusion `R>2`, with its existing printed analytic dependencies retained. |

The last source is used as its already established same-nine theorem,
not as a new reproof of its six analytic measure dependencies. No
computational checker is run or made a new premise of this argument.

No original fine or coarse ledger flag is changed by this proposed
source. The unrestricted mixed C7 family, partial shared blocks and
all original parent gates keep their remaining obligations. No numerical
search, mesh, certificate computation, Lean/Lake invocation, CI dispatch,
metadata mutation or remote edit was used.

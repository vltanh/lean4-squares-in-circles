# Independent review: the 93/100 inner arc and full diagonal-channel cap

Date: October 26, 2026.

**Result: PASS after full independent source, physical-scope, analytic and
exact-arithmetic review.** Reviewer: block_attachments, separate from the
author. This review concerns the current sources below, after the two
wording corrections recorded in Section 6. No historical review is reused.

| Current source | SHA-256 at review |
| --- | --- |
| ANNULAR_CENTER_ARC_AT_93_100.md | 7dcc481854502c70dbb0f4ca5d05bec654e91a9c4ae77f9239deecd6b689930d |
| DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md | 5745b99e022946910fd4fcba3685c605a45675272ce5348aa87a1bab96dc5de0 |

Status or review-citation-only header updates do not change the reviewed
mathematical content. Any substantive later change needs its own audit.

## 1. Original-domain and dependency audit

I read both new sources in full and the complete accepted
ANNULAR_CENTER_ARC_AT_23_25.md. For the physical application I read
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md,
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md and
SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md. The proper-concurrence
dependency was checked against FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md,
Lemma 1.1.

The channel theorem expressly assumes the entire positive component is
a simple cycle with at least three positive circle loads. Its two
endpoints are therefore true degree-two loaded bodies. The proof does
not apply a degree-two equation at an endpoint of a larger positive
graph. The compatible diagonal convention already belongs to the
original certificate: the transmitter's two diagonal vertices meet
strict interiors of actual endpoint sides. Thus both endpoint frames
have the channel as a side axis, with the actual displacement
\(\sqrt2\), and both original transverse means remain unchanged.

The physical cap theorem supplies the positive actual height \(h\),
the opposite horizontal center signs, nonnegative endpoint center
heights, and the actual exterior crosscut. These give exactly
\[
 X=[-a,1-a]\times[b-1,b],\qquad
 Y=[c-1,c]\times[d-1,d],
\]
\[
 a+c=2+\sqrt2,\qquad
 a^2+b^2=c^2+d^2=R^2,\qquad b,d\ge1/2.
\]
The weak height endpoint is important: either endpoint may initially
have the physical two-circle-corner mask, with every individual
nonnegative weight retained.

The new general radius premise is \(2\le R\le\sqrt{1105}/16\).
It is not asserted over the whole earlier lower-radius window. In
the original nine-square FIVE application the already accepted
same-nine lower bound \(R>2\) supplies it without changing the
configuration.

## 2. The complete 93/100 arc strengthening

The accepted 23/25 theorem supplies the connected open arc, its
radial-center point, and the full clipping/endpoint domain. The new
threshold is larger, so all those conclusions transfer directly.

I independently reconstructed the only sharpened derivative numerator.
With \(x^2+y^2=k^2\), it is exactly
\[
 (x-y)\{(x+y)(k^2-21/16)+k^2+xy\}.
\]
On the complete fixed-radius outer-face domain the bracket exceeds
\(1/32\). The diagonal is in the same connected allowed interval,
so the outer-outer arc is minimized there; continuity includes
an outer face tangent to the inner circle. No finite set of
orientations is being substituted.

At \(k=93/100\), the exact diagonal arcsine argument is
\((100+93\sqrt2)/250\). Its squared comparison with
\(\cos(\pi/8)\), multiplied by the positive denominator, reduces
to \(11900\sqrt2-15808>852>0\). This proves length strictly
greater than \(\pi/4\).

The other three outer-face differences, and both inner-face
alternatives, were read in the accepted source and each already
exceeds \(\pi/4\) on the larger domain. Thus the new conclusion
covers every independent square frame, not only the diagonal
minimizer. Different actual open squares produce disjoint open
arcs. The lower center bound alone does not route those arcs; that
separate obligation is proved in the channel source.

## 3. Original height bound and all endpoint masks

I rederived the endpoint bounds
\[
11/8<a,c<81/40
\]
and then relabelled only the whole left/right channel so that
\(a\le c\). The smaller-horizontal endpoint satisfies
\[
b^2\ge 4-(2+\sqrt2)^2/4=5/2-\sqrt2>1.
\]
Together with \(a>1/2\), this proves that this actual endpoint is
physically unique. The other endpoint remains unrestricted. It is
therefore legitimate, at this endpoint only, to put its original
proper concurrence inside its actual square and derive
\[
h\ge b(1-1/a).
\]
No interior bound is imposed on a radial concurrence.

I independently differentiated the two complete scalar lower bounds:
\[
G'(a)=\frac{2(a-1)}{a^3}
 \{A^2+1/4-Aa(a+1)\},\qquad A=2+\sqrt2,
\]
\[
F'(a)=\frac{2(a-1)}{a^3}(4-a^3).
\]
Each derivative can change sign only from positive to negative.
Thus the entire two intervals have endpoint minima. All four
endpoint comparisons are positive, including the small reserve
\(41/8910000\) at \(a=3/2\) in the first bound. This establishes
the strict original height \(h>43/100\), even at \(R=2\).

The whole-square cap inclusion then gives
\[
(c_E)_y\ge h+1/2>93/100
\]
for every actual pocket extra. It uses the projection halfwidth
of an arbitrary unit; no extra frame is imposed.

## 4. All four endpoint-face comparisons

The gap-facing endpoint formulas were reconstructed directly on the
upper inner semicircle from the two actual aligned rectangles.
The outer vertical faces lie beyond that circle; only the inner
vertical or top face can determine a gap-facing endpoint.
Lower faces cut the opposite ends of the endpoint intervals.
Clipping a top face above the inner circle is included.

With \(x=a-1,\ y=c-1,\ x+y=\sqrt2\), I checked separately:

1. \(x^2+y^2<r^2\), which gives the vertical/vertical angle sum
   greater than \(\pi/2\).
2. \(b^2+d^2>r^2\), from convexity at the two ends of
   \(a+c=A,\ a,c\le\sqrt{R^2-1/4}\), including a clipped
   horizontal angle.
3. \(d>x\), by the full convex polynomial
   \(x^2+(1+\sqrt2-x)^2<4\) on the stated interval.
4. The reflected inequality \(b>y\).

The mixed-polynomial upper bounds hold on the whole interval,
not merely at the physical configurations. Both positive quantities
are squared only where their signs are known. These four
comparisons prove the single actual free endpoint interval has
length strictly less than \(\pi/2\).

## 5. Actual exterior routing and original FIVE join

The occupied crosscut is the original
\(z_X-P_X-P_Y-z_Y\), with its actual upper circle arc.
Its endpoint portions are contained in the actual endpoint
squares, and its middle segment is occupied by the unchanged
diagonal transmitter. The original physical cyclic-order theorem
identifies its bounded upper side as the actual exterior pocket.

The full endpoint inner-circle arcs contain their radial center
points in their interiors. Their upper-semicircle restrictions
contain those directions, allowing direction zero or pi when a
physical radial endpoint has center height zero. Every intersection
of the middle segment with the upper inner semicircle lies between
the two center directions, because those two radial points lie
strictly beyond the segment's respective horizontal endpoints.

For an extra arc point on the wrong side of either center
direction, the prescribed inner-circle path to angle zero or pi
avoids both actual endpoint intervals and the middle segment.
The horizontal ray then escapes below the positive height \(h\),
avoiding the outer upper arc as well. This contradicts membership
in the bounded actual pocket. Thus every extra arc lies in the
same free interval used in Section 4. Additional physical contacts
may subdivide that region but do not permit crossing its occupied
boundary. Compact-interior limits cover all stated weak-junction
conditions.

Two pocket extras would now supply disjoint open arcs whose total
length is greater than \(\pi/2\) inside one interval shorter than
\(\pi/2\). This gives capacity at most one for the entire stated
diagonal-channel domain.

For the original five-load bare C6, the accepted actual center
diameter and winding argument gives central capacity one, with
all other extras in this sole cap. The new cap capacity therefore
allows at most two extras, contradicting the three original
physical extras. All five original circle loads, all other
endpoint masks, zero individual radial weights and actual
applications remain. This is a complete diagonal-width family
exit, not closure of the entire FIVE gate: its width-one,
unique/unique endpoint row still remains.

## 6. Independent exact reconstruction and corrections

A fresh two-variable sparse Fraction calculation reproduced the
two height derivative factorizations and the arc derivative
numerator. Separate exact arithmetic in \(\mathbb Q(\sqrt2)\)
reproduced \(G(11/8)\), \(F(A/2)\), and the mixed-face quadratic
endpoint. The following displayed rational reserves were checked
independently:
\[
\begin{gathered}
1271/1210000,\quad41/8910000,\quad859/90000,\quad57/70000,\\
2/9801,\quad1/4900,\quad11/112,\quad1/16,\quad1/32,\quad852.
\end{gathered}
\]
The auxiliary endpoint and universal center bounds gave respectively
\(219/6400\) and \(31/57600\). All eighteen independent algebraic
and rational checks passed. These checks reconstruct the displayed
hand inequalities; no numerical sample or parameter grid enters
the proof.

Two harmless wording corrections were requested and applied before
this review:

- The arc title now says longer than45 degrees; its theorem always
  stated the correct angle \(\pi/4\).
- The routing distinguishes the full endpoint arc's interior from
  mere containment in its upper-semicircle restriction, explicitly
  permitting center angle zero or pi.

No remaining mathematical, endpoint, force-scope or actual-routing
gap was found. The two current sources and the stated original
diagonal FIVE family exit pass this independent review.

# Root review of the uniform diagonal-channel capacity and sharper annular arc

Date: October 26, 2026.

Reviewer: root, separate from the author and the independent block reviewer.

**Verdict: PASS for both complete stated theorems and the entire five-load
diagonal-width application.** This review does not close the original
five-load C6 parent or either four-load completion parent.

## 1. Exact current sources

I read both sources in full, including the original-domain qualifications,
all scalar intervals, the actual occupied crosscut, and the final
same-nine counting argument.

| Source | SHA256 at this review |
| --- | --- |
| ANNULAR_CENTER_ARC_AT_93_100.md | 7dcc481854502c70dbb0f4ca5d05bec654e91a9c4ae77f9239deecd6b689930d |
| DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md | 5745b99e022946910fd4fcba3685c605a45675272ce5348aa87a1bab96dc5de0 |

Subsequent acceptance-header and review-citation edits do not change the
reviewed mathematics. Substantive changes require a new review.

I checked the imported connected-arc and clipping conclusions against
ANNULAR_CENTER_ARC_AT_23_25.md, and the physical channel hypotheses against
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md,
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md,
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md and the proper-concurrence statement
in FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma 1.1. The latter distinguishes
physical uniqueness from a radial body whose concurrence may lie outside.
The new proof respects that distinction.

## 2. Whole-orientation annular strengthening

The threshold \(93/100\) is larger than the accepted \(23/25\) threshold,
so the connected open arc and inclusion of its radial center direction
remain valid. In the \(a>5/4\) part of the own-frame domain, the accepted
inner-face and opposite-face-strip estimates already exceed \(\pi/4\).
For \(a\le5/4\), three of the four possible endpoint differences also
already exceed \(\pi/4\). Only the outer-outer difference is sharpened.

I rederived its derivative at fixed \(x^2+y^2=k^2\), with \(x\ge y\).
After multiplying and squaring positive quantities, its sign is the sign
of
\[
(x-y)\{(x+y)(k^2-21/16)+k^2+xy\}.
\]
The whole-domain bounds \(k^2>4/5\), \(k^2\le9/8\) and \(x+y\le3/2\)
give a bracket strictly greater than \(1/32\). The fixed-radius allowed
interval is connected and contains the diagonal. Thus its minimum is
at the diagonal, with continuity at an outer-face tangent.

The diagonal value increases with \(k\). At \(k=93/100\), the arcsine
argument is \((100+93\sqrt2)/250\). Its comparison with
\(\cos(\pi/8)\) reduces, with positive denominators, to
\[
11900\sqrt2-15808>852>0.
\]
Consequently the complete actual open arc has length greater than
\(\pi/4\), for every orientation and every stated center radius.
No circle contact or force premise is imported into this analytic theorem.

## 3. Proper use of the original diagonal channel

The entire selected component is a simple cycle with at least three
positive circle loads. Its loaded endpoints have their true degree two,
nonparallel forces and proper concurrences. Compatible diagonal avoidance
places the actual transmitter vertices in the relative interiors of the
endpoint sides. Hence the channel direction is a genuine side axis of
both endpoint frames, not a replacement support choice.

The actual endpoint-height and cap theorems give
\[
a+c=2+\sqrt2,\quad a^2+b^2=c^2+d^2=R^2,\quad b,d\ge1/2,
\]
and the unchanged positive height \(h\), with
\(b-1<h<b,\ d-1<h<d\). A physical radial endpoint is retained at the
weak center-height boundary.

After relabelling so \(a\le c\), the inequality
\[
b^2\ge5/2-\sqrt2>1
\]
forces this particular endpoint to be physically unique. Only there
does the proof put its proper concurrence inside its actual body.
The unchanged right support then gives \(h\ge b(1-1/a)\).

I differentiated both scalar lower bounds. Their derivatives are
\[
G'(a)=\frac{2(a-1)}{a^3}
 \{A^2+1/4-Aa(a+1)\},\qquad
F'(a)=\frac{2(a-1)}{a^3}(4-a^3).
\]
On each complete stated interval, the derivative can change only
from positive to negative, so an endpoint attains the minimum.
All four endpoint comparisons exceed \((43/100)^2\).
Thus the original height is strictly greater than \(43/100\);
no parameter sample or restricted endpoint mask is being used.

The actual whole-cap inclusion and the halfwidth of an arbitrary
unit give \((c_E)_y\ge h+1/2>93/100\) for every pocket extra.
This supplies the new arc theorem for every extra, without prescribing
its frame or assuming any center-sector localization.

## 4. All four free-gap comparisons and actual routing

I reconstructed the gap-facing endpoints on the upper inner semicircle
from the two actual rectangles. The outside vertical faces lie beyond
the inner circle. The inner vertical face or top face determines each
gap-facing endpoint; the lower face cuts the opposite end. The clipped
arcsine includes a top face above the inner circle.

The four angle sums are justified separately:

1. \(x^2+y^2<25/16\) gives the vertical/vertical comparison.
2. Convexity of \(a^2+c^2\) on the full interval
   \(a+c=A,\ a,c\le\sqrt{R^2-1/4}\) gives
   \(b^2+d^2>25/16\), including clipped top-face angles.
3. The full convex quadratic
   \(x^2+(1+\sqrt2-x)^2<4\) gives \(d>x\).
4. Reflection gives \(b>y\).

Thus the one gap between the two endpoint intervals is strictly
shorter than \(\pi/2\).

Routing is a separate proved step. The crosscut
\(z_X-P_X-P_Y-z_Y\) is occupied by the actual endpoints and transmitter;
its outward upper circle arc is the correct exterior arc by the
physical loaded-body order. The endpoint inner-circle intervals contain
their radial center points in their interiors. The upper restrictions
may have a center direction at zero or pi, which the proof explicitly
allows. Every intersection of the middle crosscut with the inner
semicircle lies between those directions because the two radial points
are strictly inside the respective endpoint rectangles.

An extra arc point outside the center-direction interval has the
specified path along the inner semicircle to zero or pi, then along
the horizontal ray below \(h\). This avoids the occupied crosscut and
outer arc, contradicting the bounded exterior-pocket label. Inside
the direction interval, avoiding the two connected closed endpoint
arcs confines every extra arc to the same gap. The disjoint endpoint
interiors rule out interleaving their arc intervals. Additional
physical contacts only subdivide the bounded region, and the original
compact-interior convention covers weak junctions.

Two extra units would therefore provide two disjoint open arcs, each
longer than \(\pi/4\), inside one interval shorter than \(\pi/2\).
The whole diagonal cap has capacity at most one.

## 5. Exact arithmetic and the original five-load consequence

A fresh Fraction calculation from the displayed definitions reproduced
the four height reserves
\[
1271/1210000,\quad41/8910000,\quad859/90000,\quad57/70000,
\]
the endpoint bound reserve \(219/6400\), the vertical-gap reserve
\(11/112\), the annular derivative reserve \(1/32\), and the
strict diagonal comparison \(852\). I also rechecked the universal
center reserve \(31/57600\). These exact checks corroborate the
continuous arguments; they are not a finite parameter cover.

For the original nine-square five-load bare C6, the already reviewed
central theorem bounds the whole central union by one extra. The
same-nine radius theorem gives \(R>2\), so the new channel theorem's
radius premise is supplied on the unchanged configuration. There is
only one exterior channel region. A diagonal transmitter therefore
allows at most two extras in total, contrary to the original three.
All five positive circle loads, all physical masks, individual zero
weights, actual support owners and means remain.

This closes the whole diagonal-width subfamily. Together with the
accepted radial side-channel exit, the sole five-load family remaining
is the width-one channel with two physically unique endpoints. No
original whole FIVE gate or four-load parent is closed by this review.
No Lean compilation, CI, or new computational certificate was used.

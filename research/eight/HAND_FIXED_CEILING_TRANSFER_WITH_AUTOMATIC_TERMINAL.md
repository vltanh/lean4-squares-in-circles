# Transfer from the fixed hand ceiling to the exact sharp radius

## 1. The transfer needed by the current terminal

Set

\[
q_-:=\frac{7831}{2000}=3.9155,
\qquad Q_1:=\frac{1957767069}{500000000}=3.915534138.
\tag{1}
\]

The existing sharp-root hand bounds give

\[
                         q_-<q_*<Q_1<4.
\tag{2}
\]

The coarse lower bound in (2) is in
`HUMAN_BROAD_TERMINAL_ARITHMETIC.md`; the sharp ceiling bracket supplies
the upper bound. Only (2), not the width of its interval, is used here.

Suppose the completed fixed-ceiling hand capture has the following
universal conclusion: every admissible seven-square boundary neighbor
cycle at squared radius \(Q_1\) obtains the candidate roles, the
appropriate coarse signed-tangent bounds, and \(S\le1/1000\).
Then `HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md` supplies every
required canonical owner and \(1/10<t<4/25\).

**Transfer theorem.** Under that fixed-ceiling capture input, no actual
eight-square packing has squared containing radius below \(q_*\).
For an actual packing at \(q_*\), the same input supplies the frame
and witness hypotheses of
`EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`, hence the existing complete
equality classification.

This theorem removes the former need for a reserve in a local
center-error tolerance. The automatic-slider terminal applies after
contracting the boundary representative back to its own radius.
No monotonicity of a sampled pair-gap function is assumed.

## 2. Uniform outer-radius monotonicity

Fix a center ray and the square's true frame. Its relative angle
\(\alpha\in[-\pi/4,\pi/4]\) is fixed. An outer-boundary center has
radius \(r(q,\alpha)\) defined by

\[
r^2+B r+\frac12=q,
\qquad B=\cos\alpha+|\sin\alpha|\in[1,\sqrt2].
\tag{3}
\]

For \(5/2\le q\le4\),

\[
\frac45<r<\frac32,
\qquad \frac14\le r_q
=\frac1{\sqrt{B^2+4q-2}}\le\frac13.
\tag{4}
\]

Indeed, at \(r=4/5\), the left side of (3) is less than
\(16/25+6/5+1/2=117/50<5/2\). At \(r=3/2\), it is at least
\(9/4+3/2+1/2=17/4>4\). The left side increases with \(r\).
The squared denominator of the derivative lies between 9 and 16.

A core-boundary center, which remains fixed when \(q\) changes, has
radius at most \(\sqrt2/2+1/12<4/5\). This follows either from its
rounded-square parametrization, or by writing it as a point of the
centered unit square plus a vector of length \(1/12\).

Choose any actual signed SAT axis of a pair. Its unit normal and its
required width sum \(w\ge1\) remain fixed. For an outer–outer pair,
write its signed center projection as

\[
                       P=u r_A+v r_B,\qquad |u|,|v|\le1.
\]

If both coefficients are nonnegative and \(P\ge w\), then
\(u+v>2/3\), so \(P'>(1/6)\) by (4). They cannot both be
nonpositive. In the remaining case relabel the two terms and write
\(P=u r_A-s r_B\) with \(u,s\ge0\). From \(P\ge1\) and
(4),

\[
u>\frac23+\frac8{15}s,
\qquad s<\frac58.
\]

The second bound follows from
\(s r_B\le u r_A-1<1/2\). Consequently,

\[
P'\ge\frac u4-\frac s3
>\frac16-\frac s5>\frac1{24}.
\tag{5}
\]

For a core–outer pair write \(P=u r_O+v r_C\). Because
\(r_C<4/5\), feasibility gives \(u r_O>1/5\), hence
\(u>2/15\) and

\[
                              P'>\frac1{30}.
\tag{6}
\]

A core–core pair remains unchanged. The axis width never changes.
Equations (5)–(6), applied whenever \(P\ge w\), and continuity
therefore show that an initially feasible signed axis cannot become
infeasible as \(q\) increases. A first downward crossing of its
feasibility threshold would contradict the positive derivative there.

Thus expanding every outer-boundary radius from any
\(q_a\in[5/2,4]\) to \(q_b\in[q_a,4]\), while keeping core
centers fixed, preserves **every initially feasible signed axis**, not
merely one chosen witness. It also preserves every center ray, cyclic
center gap, true frame, relative tangent, and C/O assignment. Each
moved center travels at most \((q_b-q_a)/3\), although the transfer
below does not use this distance estimate.

## 3. Boundary reduction at the hypothetical subsharp radius

Suppose an actual eight-square packing lies in a disk of squared radius
\(q<q_*\). Enlarge only the containing disk, if necessary, to

\[
                            \bar q=\max(q,q_-).
\tag{7}
\]

The square centers and frames do not move in this enlargement. By (2),
\(5/2<q_-\le\bar q<q_*<Q_1\). The hand central-core theorem,
which applies below the coarse ceiling \(9789/2500\), selects the
central square; the other seven avoid the open radius-\(1/12\) disk.

Apply `CYCLIC_RADIAL_BOUNDARY_REDUCTION.md` at the containing radius
\(\bar q\). Its proof is uniform below the coarse ceiling: the
same strict angular separation bounds hold, and the bounded outer
center body is simply formed using the actual radius \(\bar q\).
Move each center using its two fixed neighboring SAT halfplanes until
it first touches its outer or core boundary. The result is a seven-square
neighbor cycle at \(\bar q\), preserving cyclic order and true frames.
Nonneighbor overlap is permitted in this relaxation.

If desired, retain one initially chosen signed SAT witness on every
edge throughout all these moves. At each step the two such incident
halfplanes still contain the current center, and their common recession
direction preserves both inequalities. This strengthened choice is
needed for the original-center equality statement in Section 5.

Expand the outer centers of this boundary cycle to \(Q_1\) using
Section 2. It remains an admissible boundary neighbor cycle, with all
its previous feasible signed separators retained. The universal
fixed-ceiling capture input therefore applies to it.

## 4. Contract without any loss in the terminal hypotheses

Choose the captured candidate labeling and frame normalization on the
expanded cycle. It has the declared signed-tangent cuts,
\(S\le1/1000\), \(1/10<t<4/25\), and only the canonical
owner sets

\[
\{1,3\},\{1\},\{1,3\},\{3,4\},\{1,3\},\{3,4\},\{2\}.
\tag{8}
\]

Now return its outer centers to their positions at radius \(\bar q\).
This is not an assertion that arbitrary separators survive inward
motion. The cycle being recovered is the one already constructed at
\(\bar q\), so its chosen original witnesses were feasible there
before the expansion.

Every such originally feasible witness survived expansion by Section 2.
The preceding universal axis-elimination theorem puts every feasible
signed witness of the expanded cycle among the four retained forward
axes. The all-axis conclusions of the owner theorems at \(Q_1\)
therefore force each of those witnesses to belong to (8). This is precisely why
the owner theorems exclude a forbidden feasible axis even when another
axis also separates. No reverse monotonicity inference is made.

Center rays and true frames were fixed during expansion. Thus the
captured canonical labeling, quarter offsets, relative tangents,
\(S\), and \(t\) are identical on the recovered
\(\bar q\)-boundary cycle. Its containment and core avoidance hold
by its construction in Section 3. All hypotheses of the automatic-slider
terminal are therefore valid at \(\bar q\), without estimating the
distance traveled by any center. The terminal gives

\[
                             \bar q\ge q_*,
\]

contradicting (7). This proves the sharp lower bound from the universal
fixed-ceiling capture input.

## 5. Equality and the original centers

For an actual packing at \(q_*\), carry out the same construction
with \(\bar q=q_*\), retaining an initially selected signed witness
on every edge. Expand to \(Q_1\), apply the capture, and recover
the boundary cycle at \(q_*\) as in Section 4.

The automatic terminal has a strictly positive coefficient of \(S\),
a strictly positive coefficient of \((t-t_*)^2\), and five positive
completed center squares. Equality therefore forces

\[
                            S=0,\qquad t=t_*.
\]

The true frames are the original true frames, since neither the boundary
deformation nor the expansion changed them. The initially selected
witnesses are still the original feasible signed axes, and (8) shows
they have the stationary allowed directions. Consequently the fixed
stationary dual may be reapplied directly to the original centers,
exactly as in `EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`. Its two
slider forces vanish at zero frame error; no original slider projection
or canonical center proximity is required for that identity.

It forces the five original anchors and all seven original contact
gaps. The necessary and sufficient remaining parameter domain is the
one in `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md`. In particular the
transfer does not introduce an extra equality branch or remove the
real slider and central-square freedoms already classified there.

## 6. Exact scope

The elementary monotonicity and transfer argument is complete. Its
external hypothesis is the universal fixed-ceiling hand capture at
\(Q_1\), including the final bound \(S\le1/1000\). The capture
package proves the owners and tilt conditionally on that bound; a
completed global cyclic contraction must still supply the bound before
the unrestricted sharp theorem follows.

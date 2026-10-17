# Independent review of the final capture and radius transfer

**Result: PASS.** The logical chain in
`HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md` and
`HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md` is valid on
their stated conditional scope. The remaining global mismatch premise
is explicit; neither note claims it as a conclusion of the transfer.

## 1. Owner, tilt and automatic-terminal interface

The capture steps occur in a valid order. The zero-quarter exclusions
apply at \(S\le.4\); the enlarged quarter-owner table applies at
\(S\le.015\); the mixed-owner and signed-error tilt tables apply at
\(S\le.001\). The latter two have the owners supplied by the preceding
step as premises. Their radii also match: \(Q_1<Q_0\), and the tilt
table uses exactly \(Q_1=3.915534138\).

The canonical quarter offsets \((-1,-1,0,0,1,1,2)\), including the
closing turn, yield exactly \(0101011\). The same five real frame
differences define \(S\) in the capture and terminal statements.
The final owner sets have exactly 32 assignments, precisely those of
the completed-square terminal. The strict captured tilt interval lies
within its closed \([1/10,4/25]\) interval.

The terminal's primary-coordinate bounds require core avoidance and
containment, not a radial-boundary equality. They give the enlarged
slider rectangle automatically. Its remaining angular coefficient is
exactly

\[
\frac{56793}{5000000}-\frac{93}{10}\frac1{1000}
=\frac{10293}{5000000}>0.
\]

Thus the wrapper introduces no hidden center-proximity or slider premise.
The 3,513 quartics and their complete owner/angle covers are supplied
by the independently reviewed capture package, manifest SHA-256

```
dd0146dd4262476704293ad8928921d15e5184212490d7eb8c9406e7b7bf8bf6
```

## 2. Outer-radius monotonicity

I rederived the extended range \(5/2\le q\le4\). For
\(r^2+Br+1/2=q\), \(1\le B\le\sqrt2\), it gives
\(4/5<r<3/2\) and \(1/4\le r_q\le1/3\).
The entire forbidden core-center body has radius at most
\(\sqrt2/2+1/12<4/5\); hence expanding an outer state also preserves
core avoidance. Core-boundary centers stay fixed and remain contained
as the circle grows.

For a feasible signed outer–outer projection with coefficients of
opposite signs, write \(P=ur_A-sr_B\), \(u,s\ge0\).
The bounds imply
\(u>2/3+8s/15\) and \(s<5/8\), so
\(P'>1/6-s/5>1/24\). The same-positive case has a still larger
positive derivative. For a core–outer pair feasibility gives
\(u>2/15\), and therefore \(P'>1/30\). Core–core projections do
not change. The required width is constant because both true frames
are fixed.

These derivative estimates hold whenever a signed axis is feasible.
A first downward crossing is therefore impossible. The result preserves
every initially feasible signed axis, including ties, together with
the center rays, canonical tangents, real frames, cyclic center gaps
and radial kinds.

## 3. Recover the original boundary cycle

For a hypothetical packing below \(q_*\), the choice
\(\bar q=\max(q,3.9155)\) is below \(q_*\) and above \(5/2\),
using the cited sharp-root bounds. The central-core theorem and physical
holonomy radial reduction apply at this radius. Keeping one initially
chosen witness per cyclic edge is valid: each center's two fixed
incident halfplanes have a nonzero common recession direction, and
the first hit of an outer or core boundary stops that center.
Nonneighbor overlaps are allowed in this adjacent-pair relaxation.

Expanding only the outer centers to \(Q_1\) preserves all those
witnesses. The universal fixed-ceiling capture therefore places every
one of them in the intended owner sets. In particular, this implication
uses the all-axis owner conclusions; merely finding one good separator
would not have been sufficient.

The inward step recovers the boundary cycle already constructed at
\(\bar q\). It does not infer inward monotonicity for arbitrary new
separators. Its retained initial witnesses were feasible before the
expansion, while its rays and frames give exactly the captured
tangents, tilt and mismatch. The automatic terminal therefore applies
at \(\bar q\), contradicting \(\bar q<q_*\). No traveled-distance
estimate or local tube reserve is needed.

## 4. Equality pullback

At \(q=q_*\), the same construction retains the initially chosen
original witnesses. Equality in the terminal forces \(S=0\) and
\(t=t_*\). The original true frames have never moved. Each retained
original separator is now known to have one of the stationary allowed
directions. The cited stationary dual can consequently be reapplied
directly to the original centers: at zero error the two slider forces
vanish, so no original slider-position or tangent-cut assumption is
needed for that identity.

The existing equality pullback then forces the five original anchors
and seven contact gaps; the complete parameter-domain theorem supplies
the remaining necessary and sufficient slider and central-square
freedom. The transfer creates no additional equality branch and does
not assert uniqueness of one rigid pose where the classified freedoms
remain.

## 5. Reproduction and scope

`audit_candidate_fixed_ceiling_transfer_independently.py` checks all new
strict rational comparisons, derivative constants, quarter offsets,
owner counts and source hashes. Its results are in
`candidate_fixed_ceiling_transfer_independent_audit.json`. Both source
layouts are supported, including flattened `research/eight` files.

The review accepts the already independently proved radial reduction,
sharp-root bracket, core theorem, finite capture package, completed
square terminal and equality-domain theorem as explicit imports. The
remaining external obligation is the universal fixed-ceiling capture
of \(S\le1/1000\); the transfer itself is complete.

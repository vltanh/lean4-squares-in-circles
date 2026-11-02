# Independent review of the wide-main bracketed-side triple reduction

November 2, 2026. Agent physical and mathematical-evaluator review.
No Lean or CI. This review validates the reduction for both complementary
roots; a consequence is accepted only after its complete exact replay.

Reviewed frozen sources under `agent_low_floor/weak_middle_11/`:

- `WEAK_MIDDLE_BRACKETED_MAIN_SIDE_TRIPLE_HAND_TABLE.md`, SHA-256
  `30c8a568ad570dfaebdefe2d4f5933ec7456968c873eb6f7bc907d4b6bf12b73`.
- `verify_weak_middle_side_eight.py`, SHA-256
  `c1fad9ffb92596f67ff1b306230da124b61ad6151e419fc47832685455ea714c`.

**Physical reduction and exact Python evaluator: PASS.** I found no
missing chirality, physical owner, main-height order, cone boundary, or
shared-original-frame condition. The low-right and low-floor conclusions
use separate complementary roots; neither conclusion is assumed by the
other. This is an eight-original conditional input, not a complete
010/11 occupancy assembly.

## 1. Scope and the retained lower original

The four main originals retain their cone order, two actual outer links,
and weak middle pair. The original selected L,P,R retain both cone and
weak-link predicates, with L,R in their closed side columns. Their common
upward routing is supplied by the accepted wide-main routing theorem.
The original additional left-side S lies below B and supplies exactly
the independently accepted bound yB>f(hB). No constraint on the ninth
original is used to strengthen this subsystem.

The function

`f(h)=-2h/3+max(0,min((h-1/2)/6,(27/50-h)/3))+1/400`

is decreasing on the entire h root. Its three nonconstant pieces have
slopes -1/2, -1, and -2/3. Thus the exact evaluator's use of the upper
hB endpoint gives a safe lower height. It does not assume that either
wide main lies in the old narrow actual-four center band.

## 2. Endpoint resources and main boxes

The three orientation-toll bounds for V, the lower bounds for A0,A3,
and c0,c3>=c*+(32/9)V agree with the accepted outer-actual-link
resources. Their algebraic coefficients 27/92 and 157/184 are correct.

The sum constant K=80669/93000 follows independently from

`gA+gD >= 1/(1+U)`

and the endpoint height budget. The resulting expression

`1/(1+U)-1/8+(37/50)U`

decreases on 0<=U<=1/30; its endpoint value is precisely K. This proves
the retained sum bound with the added (32/9)V term.

For live c0, c0<=gA bounds hA by H0. Since h+k decreases with h,
J0 is a lower bound for the original endpoint's hA+kA. Also hA+gA>=1.
The outward-corner inequality therefore gives the displayed A0 upper
bound. Using it in xB>=hB-A0 gives the strengthened b- endpoint.

The two radical inversions for c3 are valid. The two-endpoint arc bound
uses U<=1/30 in the chord loss 73U/1000. The single-endpoint arc uses
the accepted lower A3 and hD+kD>=29927/30000. Both square-root lower
requirements are positive on this root. A negative upper radicand is
an impossible branch; clipping only the negative lower endpoint of an
otherwise nonnegative radical interval is a safe enclosure of its
physically real part.

The four main x endpoints and both main lower-height formulas follow
from the same original outer cone comparisons. In particular

`yB>=c0-121/60-b+`, `yC>=c3+c--121/60`

use |yE|<=gE-cE<=1/2-cE. The opposite-sign outer-cone bounds supply
the upper main heights used later. Dropping further available upper
bounds is a relaxation, not a hidden hypothesis.

## 3. All signed original main/outsider owners are present

For a folded signed frame (a,sb),(-sb,a), the upward owned normals are

`(s*a,b)` and `(-s*b,a)`.

The evaluator uses both of these for the main and both for the outsider.
Its signed support expression is the original pair's support sum on
every owned axis, with a safe interval lower bound and the independent
lower bound one. The B and C chiralities are held fixed across every
use involving that same original main.

A P/main horizontal gap is at most 7/5-hM<=9/10. A same-side
selected endpoint/main gap is smaller still. Thus an actual separating
normal with nonpositive vertical component is impossible: its projection
is at most the horizontal gap, below the support sum one. Zero vertical
owned normals are impossible for the same reason. No necessary axis is
lost by restricting to the four upward choices.

For the additional main-inset bound, throughout all four uses,

`D-gM<=2/5`.

For P this follows from hM+gM=1+etaM and D<=7/5-hM. For a
same-side selected endpoint use D<=11/10-gM-eta_other and
gM>5/13, or the even smaller opposite horizontal order. Consequently
the horizontal inset separator is impossible, wrong vertical signs
are impossible, and both finite owned-axis numerators in the inset
formula are positive: they are at least 1/2-2/5=1/10.

The center-distance bound follows from an actual unit separating normal
with projection at least the same support sum. The maximum of this
bound, the inset bound, and the signed-owner bound remains a necessary
clearance for the original pair. None replaces the original unit's
frame or creates an actual vertical projection comparison.

## 4. Endpoint reach and the zero-slope boundary

The fixed endpoint rectangles and their improved inward edges are
contained in the original endpoint insets. The improved edge rho-c
is an upper bound for xE-gE, since xE<rho and gE>=c. The selected
unit lies left of the rectangle's far boundary throughout the root.

The signed r+ and r- formulas give exactly the two possible upper/lower
routes around the inward edge. If interval data do not guarantee
horizontal overlap, the evaluator keeps its earlier lower bound and
does not use the reach improvement. If overlap is guaranteed, the
negative-height alternative is removed only when the earlier lower
height plus the corresponding reflected reach is strictly positive.
Otherwise both alternatives remain admitted by the preceding bound.

One arithmetic detail is useful for the C++ port as well. Under the
guaranteed overlap, delta>-h. Therefore

`(1/2+delta*b)/a > k>=0`,

while, for b>0,

`(1/2+delta*a)/b > -k>=-1/2`.

The second numerator can be negative. Any finite negative sentinel used
for an interval quotient touching b=0 must be justified by this lower
bound, not by claiming both endpoint numerators positive. At b=0 the
unavailable second axis is omitted; the remaining formula is the aligned
limit. The frozen Python evaluator's -1000 sentinel is safely below
the physical reach bound. No change to its arithmetic is needed.

All four original corners are used for each selected unit's upper
height. The reflected left frame has sign -sL, consistently in both its
corner cap and its endpoint reach. The low-right root adds only yR<=3/5;
the low-floor root adds only yP<=hP+1/10.

## 5. Shared P height and the original B/C union

For a horizontal cone pair, a separating owned normal can be chosen
with nonnegative horizontal component. Quarter-turning an unfavorable
normal preserves both unit-square supports and does not decrease its
projection on a horizontal cone displacement. When a horizontal
component is zero, a vertical comparison can likewise be replaced by
the horizontal quarter-turn if necessary. Thus the four listed normals
remain exhaustive at zero slopes.

For each original LP or PR owner, `pair_ranges` encloses its allowed
signed vertical difference after intersection with the cone interval.
Positive vertical coefficients give lower bounds and negative ones
give upper bounds. The horizontal zero-slope alternative is rejected
only when its numerator is strictly positive throughout the interval.

LP adds its difference interval to the original L height interval;
PR subtracts its interval from the original R height interval. The
intersection with the one original P interval is performed separately
for all sixteen owner pairs. P's center and signed frame are shared
throughout. Neither a height nor a chirality is minimized independently
on the two links.

The resulting upper main heights are valid consequences of the P and
shoulder upper heights and the original clearances. Together with the
lower main heights they give the complete interval for yC-yB. The
original middle cone contributes |yC-yB|<=dM, while the original weak
bit gives dxBC<=hB+hC. The lower inset span is retained independently.

For the final B/C physical check, the horizontal owner components are
nonnegative, so replacing the actual horizontal gap by dM is a valid
upper bound on its projection. The signed vertical component is
maximized over the full retained height-difference interval. All four
owners use the same original B,C signed frames as their earlier
clearance applications. If every upper bound is below the support
lower bound, that one chirality/owner-pair alternative is impossible.
Taking the union over all five signs and all sixteen short-owner pairs
is therefore exhaustive.

## 6. Exact evaluator and tree interface

The 80-bit Python evaluator reproduces these necessary inequalities with
outward bounds. Its shape endpoint directions, eta monotonicity,
piecewise main-height floor, effective-width upper bound, resource
inversions, all signed products, and original corner bounds have the
correct interval directions. The linear effective-width maximum keeps
its interior peak t=19/27; the curved branch is increasing and uses its
upper endpoint.

Each early return is a strictly negative upper bound for a necessary
margin. Empty height intervals or owner lists remove only their own
physical alternatives. The maximum over chiralities and owner pairs is
an upper bound for the complete union, including their shared original
P and main parameters. A true physical point would keep at least one
alternative's every margin nonnegative, so a negative returned margin
excludes the complete box.

The verifier reconstructs the nine-dimensional rational root itself.
Tags 0 through 8 split at exact rational midpoints and tag 9 is the only
terminal. Every leaf is recomputed; producer reserves are ignored.
Empty-stack and final-frontier checks reject trailing events and missing
children. The computed counts are reported independently of discovery
metadata. Its two allowed `kind` values use exactly the two separate
complementary hypotheses stated in the manuscript.

This review validates the reduction and both evaluator modes. The
complete low-right certificate is SHA-256
`89033c7e5fd8caaca5b4c7fcee5309be0e2791f718e8cc99ecadaddf50d78303`.
Its completed replay record must accompany acceptance. The low-floor
mode requires its own complete replay before that consequence is used.

## 7. Final manuscript acceptance-record amendment

The final manuscript was reread after its acceptance paragraphs were
updated. Its SHA-256 is
`9ddd2c7e0248d3c3d6b1ea46f3ebcd34fe21e173239c22d208238d21baa8cba4`.
The physical hypotheses, parameter root, formulas, owner lists,
shared-P intersections, and B/C union agree with the reviewed reduction
above. The updates record the now-complete independent low-right C++
replay and the completed agent reviews, while continuing to leave the
separate low-floor consequence unaccepted. The Python evaluator remains
at its frozen SHA-256 stated at the start of this review.

The final source therefore has the same **PASS** mathematical review.
Its accepted low-right theorem is supported by the separate complete
297,270-leaf exact replay and the final C++ code review in
`WEAK_MIDDLE_BRACKETED_SIDE_CPP_INDEPENDENT_REVIEW.md`. No extra geometric
premise or low-floor conclusion was added by the acceptance update.

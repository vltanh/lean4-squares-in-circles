# Full review: occupied inner arcs, actual gaps, and the seven-body compatible-cycle bound

**Date:** October 30, 2026 UTC. **Reviewer:** block-ears agent.
**Result:** PASS. No repair requested.

## Frozen source and review scope

I read the entire current source
`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`
and independently reconstructed its complete geometric proof, order join,
continuous metric inequality, and physical stress callers. The reviewed
source has 18,761 bytes and SHA256
`369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403`.

I had already read the complete occupied-arc proof in
`CYCLIC_GLOBAL_CONTINUATION.md` before this source was frozen. This review
checks the new self-contained reconstruction and assembly, including its
stronger metric statement. I authored the earlier marked-cycle angular
source; that fact is recorded because its topology is related. The new
arc reconstruction, actual-gap accounting, and all-load count conclusion
were independently checked here, rather than accepted by analogy with
that earlier result.

## 1. Full actual inner-circle intersection

For an actual outer circle corner, the own axes used in the new source
must be outward. In those axes the square is exactly
`[a-1,a] x [b-1,b]`, with `a>=b>=1/2` and `a^2+b^2=R^2`.
The new source correctly states that convention and does not translate
the disk origin.

With `rho=5/4`, `A=a-1`, and `B=b-1`, all bounds used to identify the
intersection have strict rational margins. In particular:

* `(25/12)^2-Q=55/2304`;
* `6241/3200-121/64=191/3200`;
* `(81/40)^2-589/144=149/14400`;
* `9/4-(25/12)^2/2=23/288`;
* `rho^2-2081/1600=419/1600`.

Thus the full intersection with the inner circle is in the own positive
x-halfplane. Its exact parameter interval is
`[max(-alpha,beta),min(alpha,gamma)]`. The strict bound
`A^2+B^2<rho^2` proves `beta>-alpha`, including the negative-B case.
Consequently the full intersection is one proper closed arc
`[beta,min(alpha,gamma)]`. Its relative interior is inside the actual
open square; its limiting endpoints are only claimed to belong to the
closed square. This endpoint distinction is needed and is retained.

For the two-inner-face width, the expression
`E=A^2+B^2+sqrt(2) A B` is convex in `a+b` at fixed `q`.
The allowed interval really has endpoints `b=1/2` and `a=b`:
`sqrt(q-b^2)+b` is nondecreasing for `b<=a`. The first endpoint gives
`E<933/1600`, below `25/32` by `317/1600`. The second endpoint
comparison reduces to `401<287 sqrt(2)`, with positive-square margin
`3937`. The sign `sqrt(2) A+B>0` is strict, so the square-root step is
valid. Since `beta+pi/4` lies strictly between zero and `pi/2`, cosine
monotonicity gives `alpha-beta>pi/4` on the required branch.

For the other side constraint, the arcsine difference is nondecreasing
on `b in [1/2,rho)` because `b>=|b-1|`. Its value at `1/2` is
`2 asin(2/5)>pi/4`; the endpoint `b=rho` is obtained by continuity.
For `b>=rho`, the asserted width follows immediately from
`gamma=pi/2` and `beta<pi/4`. Taking the minimum of the two upper
endpoints therefore leaves a complete actual arc of length greater
than `pi/4` for every boundary square.

## 2. Choice of trimmed arcs and their true order

For every actual outer circle corner z, the radial inner-circle point
`(rho/R) z` is strictly inside the original square. Both own-coordinate
inward moves are positive and smaller than `R-rho<5/6<1`.
This establishes the direction claim for every physical circle corner,
not only a selected load atom.

The center direction also lies in the same arc: the center radius is
strictly between `rho` and `M=91/60`, so its radial inner-circle point
is within `M-rho=4/15<1/2` of the center. The farthest-corner bound at
M has exact excess `31/57600` over Q. The boundary lower radius uses
`R-1/sqrt(2)>5/4`, valid throughout the stated radius window.

Because the full intersection is a single arc and both specified
directions are strictly inside it, one can trim both ends by small
positive amounts while preserving length greater than `pi/4` and
keeping both directions in its relative interior. All points on the
trimmed closed arc are in the actual open square.

Distinct trimmed arcs are disjoint compact subsets of the inner
circle. Their order is consequently the order of their selected corner
directions and of their center directions. Another outer corner of the
same square stays in the relative interior of that square's full arc;
it cannot pass another square's nonempty trimmed arc. Hence changing
which actual outer corner is selected does not change the cyclic
order. This argument requires no estimate of the angular offset of a
corner from the center.

## 3. The force-free metric inequality

Writing the selected arc lengths as `lambda_i>pi/4` and their directed
intervening angular gaps as `delta_i>0` gives
`sum(lambda_i+delta_i)=2 pi`. The two endpoints of an intervening
gap belong to their respective actual squares. Thus the actual set
distance `D_i` is at most their chord length and hence at most
`rho delta_i`.

This inequality is valid even if a directed gap exceeds pi; no
substitution of a minor angle is needed. Nor must the angular gap be
empty of all other physical squares. It is a gap only in the selected
list of compact arcs. Summation gives exactly

    sum_i D_i < (5*pi/16)*(8-t).

The strictness comes from the real occupied arcs. The proof does not
charge a notional arc to any circle-clear square. The elementary
integral for `pi<22/7` was checked by polynomial division; together
with `16/5-22/7=2/35`, it proves `tau=5*pi/16<1`.

## 4. Compatible embedding and support-width join

The source gives the complete compatibility premise, rather than
abstract graph planarity. Every chosen center-to-circle-corner spoke
lies in its own actual square except its terminal point. A circle point
cannot belong to two packing squares: the radial inward displacement
lies in the open interior of every putative owner. Hence a circle
corner is not a body-contact point. Distinct center-to-contact rays
cannot meet a spoke away from their common center.

The finitely many contact-resolution neighborhoods can be chosen to
avoid the marked spokes. Near each marked center, the spoke occupies
an angular sector distinct from all contact rays. The compatible
embedding therefore retains all spokes, including for marked vertices
with extra chords or attachments. A spoke from a Jordan cycle to the
outer circle, meeting the cycle only at its starting vertex, lies on
the cycle's exterior side. Pairwise disjoint spokes preserve order in
the annulus between the cycle and the outer circle. Cutting along one
spoke gives the standard disk separation proof; two marks cause no
exception. No assumption that the origin lies inside the cycle is
inserted.

For a run with one signed actual support normal, all tight support
equalities telescope. The endpoint-set separation is at least the
sum `W_i` of the actual widths of its internal squares, and
`W_i>=j_i`. This works for every finite run length without classifying
its orientations or invoking torque. Every actual contact mean and
actual endpoint support is retained.

The metric inequality now gives
`sum W_i < tau*(8-t)`. Nonnegativity first implies `t<8`.
Only then is `tau<1` applied to the positive factor `8-t`.
Therefore `m-t=sum j_i<=sum W_i<8-t`, so `m<=7`.
The continuous inequality remains a strictly stronger statement when
some widths exceed one.

## 5. Full-force caller and remaining branch scope

A genuinely unloaded body of true positive degree two in the entire
same graph has two equal and opposite forces. Propagation supplies the
run normal used above. Degree two only in the displayed cycle would
not suffice; the source explicitly excludes that substitution. The
marked bodies may have arbitrary true degree and may have zero circle
weight if they physically touch the circle.

For an entire simple positive component, the summed center-dotted
force equations force at least one positive circle load. The plain
force sum forbids all circle atoms from lying on a single boundary
body: every such corner has positive dot product with its center.
Thus there are at least two marks and the theorem applies. For a
chorded displayed cycle whose circle-clear vertices all have full
degree two, zero or one physical boundary marks are independently
excluded by strict support telescoping around the whole cycle or a
self-return run. These joins do not require an independently selected
torque stress or a convex force polygon.

The theorem closes every compatible eight- or nine-body simple
positive cycle, and the broader marked-cycle domain stated in the
source. It does not close a large block having a circle-clear branching
vertex on its displayed cycle. Every original square remains present;
there is no asserted placement, stress, or load for additional bodies.
The seven-body record with internal counts `(2,0,1,0)` is preserved.
No original ledger credit or automated formal verification follows
from this mathematical review.

## Decision

The frozen source is complete and sound at its stated scope. Its
self-contained occupied-arc proof and actual endpoint-set gap budget
support the seven-body compatible-cycle theorem uniformly over all
load counts and run placements. No repair or source mutation is
requested.


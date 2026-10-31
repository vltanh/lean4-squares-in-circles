# Root review: two intact petals, adjacent faces and no unloaded neighbor

Date: October 26, 2026.
Sources: INTACT_PETAL_OPPOSITE_FACES_EXCLUSION.md and
TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md.
Reviewer: root proof worker.

**Verdict: both implications accepted at their full stated original
scope.** Separate independent reviews by the hexagon and rooted-block
workers respectively are saved alongside the sources.

For the adjacent-face theorem I checked the complete strict estimates.
After the inherited same-nine exclusion of R<=2, every actual root port
on a physical boundary tip has norm at least R-sqrt(2)>2-sqrt(2).
The intact-petal theorem supplies opposite transverse port signs on
one actual side of H. At least one port has transverse magnitude at
most1/2, so that side has height P with

    P^2 > (2-sqrt(2))^2-1/4
        =23/4-4sqrt(2)>9/100.

The rational comparison sqrt(2)<283/200 makes the final inequality
strict. For two opposite petal faces both normal margins are thus
greater than3/10. On the smaller-height face P<=1/2, both straddling
ports have transverse magnitude greater than3/10, giving the other
two margins. This proves the closed D_(3/10) is inside int H.
All eight other original closed units avoid that disk. Convex
nearest-point separation gives the exact hypothesis of the accepted
force-free radius-5/4 arc theorem; eight disjoint arcs each longer than
pi/4 are impossible. The earlier one-petal-per-side result then gives
at most two petals, with their sides adjacent if there are two.
No H force equation has been modified or specialized.

For the uniform D_(1/40) theorem, suppose a side has height
sigma<=1/40. That side and its opposite cannot carry a petal,
using the earlier strict common-side interval (1/5,39/40).
Two distinct petals must use the perpendicular opposite sides.
On either, strict port straddling supplies the port toward the
shallow side, with transverse magnitude at most1/40. The actual
boundary norm lower bound yields

    P^2>(67/120)^2-(1/40)^2=14/45>1/4.

Both perpendicular heights would exceed1/2. This includes the
endpoint sigma=1/40 and proves the whole closed disk lies in int H.

If a true unloaded degree-two neighbor U remains, its unchanged two
forces give the real normal channel from H to its other neighbor V,
with reserve w>=1. The true support of H exceeds1/40, so the far
neighbor support h+w exceeds41/40. The accepted sharp contained-unit
support bound requires h+w<=sqrt(R^2-1/4)-1<61/60, a contradiction.
This uses the actual degree-two equation only at U; H and V retain
arbitrary additional forces. It works whether U is cyclic or a bridge
body, without calling a cyclic edge a bridge.

The common-root C3.335.b0 application correctly forces its two actual
pentagon neighbors to be loaded, since they retain true degree two.
The two remaining pentagon vertices and all their original load
assignments remain. Neither source closes the whole C3.335.b0 row,
and neither introduces a new checklist ID. The unrestricted inequality
and equality classification remain open.

No Lean compilation, CI, numerical pose, workflow dispatch or merge
was used in this review. The earlier same-nine arithmetic dependency
is retained where invoked.


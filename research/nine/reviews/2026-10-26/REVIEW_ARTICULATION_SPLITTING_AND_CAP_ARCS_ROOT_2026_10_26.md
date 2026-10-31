# Full-source root review: articulation splitting and whole-range cap arcs

Date: October 26, 2026.

This review covers the complete current arguments in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md and
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md. Their authors are separate agents.
It accepts the stated reusable theorems; it does not close a whole coarse
cell, the unrestricted sharp inequality, equality classification, or the
older full prerequisite-chain audit. No Lean compilation or CI was run.

## 1. Exact articulation splitting

The actual branch moment vanishes separately: summing the origin moments
over one component of G minus its articulation cancels every internal
pair at the same actual application and leaves no circle moment. The
CY.LOAD.1 center-dotted identity in CYCLIC_BLOCK_INVENTORY.md proves that
each such branch has positive circle mass. These are different facts;
neither is substituted for the other.

The bounded circle-weight criterion is sufficient exactly as stated.
Keeping all pair forces on one side and splitting only the articulation's
original circle weights gives both force equations by subtraction and both
moment equations by the preceding branch identity. Each side can be
normalized because its private branch mass is positive. Shared-side means
are inherited, including their endpoints. No old higher-degree equation
is reused after a force has been removed: the new equations are proved.

For the all-bridge application I checked the radial cut law, the tiny-disk
clearance argument and radial S/D leaf calculation in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Sections 2, 3 and 6, together with
the local all-bridge scope in
TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md, Section 1. A loaded
all-bridge articulation can only be the degree-two radial S alternative;
its two original equal circle weights split in the positive ratio of the
two retained pair-force magnitudes. The degree-one D alternative is not
an articulation.

The small-core consequence retains its explicit inherited hypothesis:
the complete at-most-five-body exclusions at the common canonical pose.
The original size identity is m1+m2=m+1<=10, so one complete new stress
uses at most five bodies. Its other physical squares remain among the
same nine. The established five-body source joins are recorded in
DEEP_GATED_ROADMAP.md, G3.M5.ALL, and CYCLIC_CELL_LEDGER.md's completed
five-body frontier; the canonical-minimizer scope is not enlarged.

The support-minimal theorem is also valid independently of that small-core
join. Its vectors (branch force, branch circle mass) and (circle force,
circle mass) lie in R^3, and sum to (0,0,1). With more than three vectors,
a dependence has both signs because their last coordinates are positive.
The proposed coefficient change is nonnegative, keeps normalization and
force balance, and kills at least one formerly positive scalar atom.
Whole-branch scaling preserves every internal equation and every actual
shared mean. All branch moments at the root remain zero. This supplies
the full physical stress required for the minimal-support contradiction.

In particular k+ell<=3 concerns the number of components after removing
the articulation and its number of positive circle atoms. It is not a
degree bound. A physical two-corner body with one zero circle weight
still has two physical circle corners and ell=1.

**Verdict:** accept the exact splitting theorem and the support-minimal
selection. Accept the small-core consequence with its named inherited
canonical-pose prerequisites. No original coarse cell is closed here.

## 2. Whole-range cap-arc theorem

I checked both complete own-frame domains. For a>5/4, the fixed-q
quadratic in a+b is convex and the two enlarged endpoints give bounds
933/1600 and 15463/20000, respectively, both strictly below 25/32.
The corrected weak intermediate comparison at the diagonal endpoint
retains v=1; the final comparison remains strict. The exact inner-circle
interval is nonempty, connected and has the two asserted possible lengths.
The strip derivative and clipping at b=5/4 preserve every endpoint.

For a<=5/4, the actual cap forces both inner coordinates positive and
k^2>1/16. Squaring the positive derivative terms gives exactly
(A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)]. Thus the diagonal is the minimum
on each connected fixed-k arc. The displayed fixed radical comparison
is strict. The remaining three differences have the stated strip and
inner-face bounds, proving one open arc longer than pi/4. The center
lies between radii 3/4 and 91/60, so its radial point on radius 5/4 is
strictly inside the actual incircle.

The width-one height theorem uses both actual positively loaded endpoint
bodies, as explicitly required in the revised statement. The support
bounds give -61/60<l<1/60, hence one unchanged application has horizontal
coordinate of absolute value at most 1/2. Its distance from the origin
is at least R-sqrt(2). Consequently h^2>=23/4-4sqrt(2)>9/100 and h>3/10.
The rational comparison sqrt(2)<283/200 has the stated positive squared
reserve. No endpoint mask, side mean or transmitter slider changes.

The original physical channel-cap theorem supplies whole-square inclusion;
the new result does not infer it from a center. Every exterior extra then
has the proved connected open arc. A separate upper bound on the actual
free interval is still needed to exclude two extras.

**Verdict:** accept the complete cap-arc and actual channel-height
theorems. They introduce no scalar certificate and alone close no
original five-load or four-load C6 gate.

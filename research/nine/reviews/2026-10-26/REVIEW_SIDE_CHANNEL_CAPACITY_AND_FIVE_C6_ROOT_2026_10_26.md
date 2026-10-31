# Root full-source acceptance: side-channel capacity one and the whole FIVE orbit

Date: October 26, 2026.

Reviewed complete source: GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md.
Separate independent review: REVIEW_GENERAL_SIDE_CHANNEL_CAPACITY_GLOBAL_2026_10_26.md.

**Verdict: accept the entire actual width-one cap theorem and the original
five-load bare-C6 exclusion.** Exactly the existing M6.B6.C6.FIVE.CAP and
M6.B6.C6.FIVE labels close. Neither a four-load parent, C6.ALL nor coarse
C1.6.b0 is closed by this result.

## 1. Physical endpoint domain

I reconstructed the application-straddling argument before using positive
a,b. The owned-side, opposite-corner and adjacent-corner cases each force
R^2>=(b+1)^2+h^2 when b>=1. The unchanged opposite application then has
norm below 23/40, contradicting its physical circle corner at R>=2.
This covers both endpoints by reflection and establishes a,b>0, a+b=1.

For each oblique endpoint, its center's closed upper-left location makes
the v-coordinate positive. The actual physical far corner is therefore
exactly one of p-u+v and p+v. The unique-corner proper concurrence in the
square forces cos(t)>=sin(t) only in the opposite-corner case where it
is used. The full adjacent-corner case keeps t unrestricted. Both cases
prove the actual application is inside radius 5/4 and the opposite v-face
lies beyond that circle. Thus the calculated intersection on p+[0,1]v
is the actual gap-facing endpoint, not a convenient substitute point.

The four owned-side cases use the original application h throughout.
The virtual values B-1 and B give only monotone lower bounds for the
same expression. No contact mean is reset. Face joins, h endpoints and
both signs of cos(phi)-sin(phi) are included.

## 2. Exact scalar inequalities

The identity
f(k,j)=((j-k)sqrt(r^2-k^2)+k^2+jk)/r
equals the actual endpoint expression in the source, with the displayed
rotation signs. I checked it by substituting a=-k cos(t)+j sin(t) and
h=k sin(t)+j cos(t).

For -1/2<=k<=1/2, both polynomial identities expand exactly. The
quadratic lower bound for the square root has nonnegative squared reserve,
and J-k>=79/200. The lower estimates for P(k), including its completed
square with reserve 719/96000, are strict on the full intervals.
For -7/8<=k<=-1/2, the coefficient of j remains positive, so all three
continuous radical comparisons may use the true lower bound for j.
Their final bounds 1433/2000, 467/625 and 101/120 exceed 71/100.
The adjacent-corner interval 1/2<=k<=1 is likewise complete: the two
signs of j-k are both retained and each polynomial is monotone on its
stated interval. Its final bound exceeds 41/50.

The fixed comparisons 71/100>1/sqrt(2), 177/250>1/sqrt(2) and
320sqrt(2)>449 all have strictly positive squared reserves. These are
explicit hand inequalities, not sampled sign or coefficient packets.

## 3. Free interval and actual routing

Each endpoint gives its strict lower bound F>1/sqrt(2). If the actual
two endpoint angles had total at least pi/2, the sine-sum identity in
Section 5 and a+b=1 would force their sum F_X+F_Y<=sqrt(2). This
contradicts the two strict inequalities and proves the entire free
interval is shorter than pi/2. The high-channel case h>=r/sqrt(2)
already has an interval of length at most pi/2 from the actual cap.

The routing uses the original occupied crosscut, actual endpoint arcs
and their radial-center points. On the upper semicircle the middle
segment has no intersections outside the two center directions; paths
toward zero or pi then exclude a pocket-extra arc outside the stated
gap. The endpoint arcs are connected by the cited whole-orientation
boundary theorem. The compact-interior convention preserves weak
junctions and genuine mean endpoints. Every whole extra has an open
arc longer than pi/4 by GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md. Hence
two physically disjoint extras cannot occupy the same actual pocket.

Physical radial endpoint masks use the existing full
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md theorem, whose whole-window
statement retains both original weights, including either zero. Together
the physical unique/unique and nonempty-radial cases exhaust the width-one
channel domain.

## 4. Exact original FIVE join

I read SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md in full. Its preliminary
central-area argument first forces an occupied cap; the transmitter-center
bound then gives every actual center pair below three, and the general
contact-ring theorem gives central capacity one. It does not depend on
the new cap theorem, so the join is noncircular.

The same nine unchanged squares satisfy R>2 by the accepted global
radius-two theorem. A true diagonal transmitter has cap capacity one by
DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md. A true side transmitter has
cap capacity one by the complete new theorem. These widths exhaust the
original unloaded degree-two transmitter. All five positive circle loads,
their physical masks and individual zero weights, every normal and mean,
and the same three completion squares remain. The entire allocation
equation is n_in+n_cap=3, while both capacities are at most one.
This excludes the whole original FIVE family and both existing labels.

The two remaining four-load C6 families still require their own joint
occupancy arguments. The unrestricted sharp bound, original equality
classification and older complete prerequisite audit remain open.
No Lean compilation, CI, workflow dispatch or merge was run.

# Independent agent review of the middle-main side-triple refinements

November 2, 2026. Reviewer: the independent `root_certificates` agent.
This is an analytic and implementation review, not a human review,
proof-kernel verification, or CI result. The complete low-floor cover and
its exact replay remain separate acceptance requirements.

The reviewed source is
`MIDDLE_MAIN_SIDE_CONE_TRIPLE_HAND_TABLE.md`, together with
`verify_middle_main_side_triple.py` in the `agent_low_floor` workspace.
This record covers the formulas and implementation decisions listed below.
The producer's numerical results are not used as proof evidence.

## 1. Universal pair caps and endpoint resources

The universal physical pair cap applies independently to the two original
pairs (M0,L) and (M3,R). Since A0+A3 >= 2+2e and each Ai < 61/60,
each individual cap and their sum give the displayed upper bounds on e.
The constants 451/810, 27/184, 157/184 and 27/92 agree with the exact
algebra. The opposite shoulder remains the same physical unit in the
adaptive lower bound for the other endpoint load.

The synthetic outward endpoint corner gives

    Q >= (Ai+JE)^2+(1-ci)^2.

The live left inset height implies g0 >= c0 and h0 <= 1/(4c0).
The function h+sqrt(1/2-h^2) decreases for h >= 1/2. Thus the proposed
JL(c0), evaluated at min(8/15,1/(4c0)), is a lower bound for the same
original endpoint's h0+k0. In an interval box, using the lower endpoint
of c0 and rounding JL downward preserves this implication.

The resulting upper bound

    A0max = min(61/60, sqrt(Q-(1-c0)^2)-JL(c0))

is valid. The actual main-chain gaps then imply

    -A0max+h1 <= x1 <= -l-e.

Consequently P's horizontal main gap is at most
xP+A0max-1/2-eNeed. The two corresponding endpoints for the absolute
L/main gap give the implemented maximum. These are bounds on the same
original main center, not independently chosen replacement positions.

The strengthened endpoint rectangle with inner edge
min(A,rho-c) is contained in the original endpoint: gE >= c and the
center norm bound give xE-gE <= rho-c. The fixed farther edge remains
valid. All signed endpoint separator alternatives therefore retain their
original physical interpretation.

## 2. Correlated main tilt and exact center-distance support

The physical bad-floor and main-clearance inequalities imply

    g1 <= hP+9/20-rP = T,
    e >= max(0,1/(4T)-1/2).

The evaluator uses an outward upper bound for T, and hence obtains a
lower bound eNeed. The derived nonnegative gain

    q(eNeed)=2 eNeed^2/(1+2 eNeed)

can be added to the two correlated main-inset margins because
h1+g1-1=q(e) and q is increasing for e >= 0. This is a one-way
refinement of a previously proved lower bound; no fixed-point assumption
or circular bound is introduced.

Writing H=1/2+eUpper and K=sqrt(1/2-H^2), the physical main/outsider
pair support is at least

    max(1,1/2+bF H+aF K).

The expression decreases in H, since its derivative is
bF-aF H/K <= 0. It increases in the outsider's folded slope t, since
that derivative is (H-Kt)/(1+t^2)^(3/2) >= 0. Evaluation at eUpper
and the lower endpoint of the outsider slope interval therefore gives
a valid lower support bound. The updated implementation follows these
directions, with outward integer arithmetic.

## 3. Feeding the proved high right shoulder into the same main

The low-right theorem is used before the low-floor theorem. If horizontal
overlap with R's original endpoint rectangle holds, yR > 3/5 excludes
every downward original side normal. The displayed algebra also includes
the zero-component limit; the strict horizontal overlap supplies the
needed strictness there. The upward reach and the original corner ceiling
then bound the same actual c3 from above.

Combining that upper bound with the shared endpoint resource gives the
displayed eUpper, and therefore g1 >= 1/(2+4eUpper). The Python evaluator
fixes the original P and R chiralities before maximizing over L, applies
the same strengthened main inset to both P and L, and retains
eNeed <= eUpper. It does not mix incompatible R signs or main tilts.

The implementation's small-negative eUpper clamp is harmless: the
unclamped value remains in the necessary margin eUpper-eNeed, so an
impossible negative bound cannot become an accepted physical branch.

## 4. The shared P-height owner matrix

For a left owner (a,b) and right owner (c,d), the chosen L and R height
endpoints lower the respective right sides in

    b yP >= AL,   -d yP >= AR.

For equal vertical signs, multiplication by |d| and |b| cancels the one
original P height, giving |d|AL+|b|AR <= 0. This remains necessary
when a vertical component vanishes. Opposite vertical signs retain the
two independent necessary projection tests.

`shared_height_owner_upper` implements these endpoint choices correctly
for both signs. It encloses signed products by ordinary interval
arithmetic and maximizes over all 16 pairs of the four physical owner
normals. The support sum is the same for either owner of a unit-square
pair, so using its outward lower bound in AL and AR is valid. No normal,
chirality, or vertical-order branch is omitted.

## 5. Additional hand cut available to the low-floor root

Section 2 of
`ACTUAL_FOUR_131_BOTH_SIDE_UPPER_CLOSED_HAND_PROOF.md` proves a separate
two-unit statement: a high central unit with whole floor at most 1/10
and a high left-side unit has center x > -1/5. Its reflected version uses
a high right-side unit. The proof uses only contained disks and two
convex circular-profile endpoint bounds; it has no occupancy or joint-cap
dependency. The `whole_mask` agent independently reviewed that argument
and its exact Fraction reserves.

In the middle-main branch, L is high because y1 >= -7/20 and its
own-side clearance exceeds 97/100. If xP <= 0, P is high because its
central own-half clearance exceeds 59/60, giving yP > 19/30.
Thus every bad-floor P in this branch satisfies xP > -1/5. The excluded
complement of a root narrowed to [-1/5,23/60] is covered by this hand
argument. Once high R has been proved, xP >= 1/5 also forces yP < 3/5.

## 6. Final cancellation, contraction, and root-collar refinements

The final mathematical evaluator additionally uses the following reviewed
necessary inequalities. The main-height base is -17/50 in the low-floor
calculation, with the separately proved low-right gate retaining -7/20.

The bad floor rules out vertical separation from the actual main inset.
After the previously excluded horizontal and inward alternatives, its one
outward P-owned tilted axis is necessary. Cancelling hP gives

    tP(kP-deltaP) >= g1-11/25               (negative chirality),
    -kP-deltaP >= tP(g1-11/25)             (positive chirality).

These formulas use the original P frame, and justify the exact tilt
upper-bound cancellation and the branch-specific lower xP bounds. The
zero-tilt collar tP <= 1/27 is excluded by the displayed hand argument
even with the older 9/20 constant. The reserves 1/1860 and 261/3650
are correct. Thus the advertised root tP in [1/27,1] has no omitted
orientation complement.

For equal vertical signs, expanding the weighted owner inequality retains
the common xP exactly. When both owners are the same original P axis,
adding the two physical separators cancels both coordinates of P and
gives the displayed necessary outer-span inequality, including a zero
vertical component. The owner-index identity used in the Python source
selects precisely those coinciding original P axes.

For every owner pair, including opposite vertical signs, multiplying the
left and right separators by the other's nonnegative horizontal component
cancels xP. The resulting coefficients

    ac(Z+X)+(cb-ad)yP-cb*yL+ad*yR-c*sigmaLP-a*sigmaPR

have the signs stated in the manuscript and code. The chosen L/R height
endpoints maximize this necessary left side; the full one P-height
interval is used against its possibly signed coefficient.

The cap-derived effective width psi is the exact algebraic consequence of
the separately accepted linear and curved shoulder tolls. Its linear
branch has its sole maximum at t=19/27, while its curved branch is
increasing. The implemented minimum of the two outward upper bounds is
therefore a valid upper bound for the pointwise minimum psi.

Each of the three linear-intersection sweeps uses an already proved
necessary inequality, with outward shape/resource endpoints. No physical
point can leave its box under those intersections. Inside each original
chirality chart, the two physical owner unions similarly supply necessary
lower bounds on the two horizontal gaps, hence an interval containing the
one original xP. Charts whose upper necessary margin is negative are
impossible. The hull of all remaining chart intervals therefore contains
every physical xP in the original box. Repeating the complete calculation
on that hull three times preserves this statement by induction; no
convergence or fixed-point premise is used. The original split tree, not
the contracted intervals, supplies root coverage.

## Acceptance boundary

No analytic or code-direction gap was found in the refinements above.
This record does not certify a discovery frontier, a partial tree, the
entire middle-main caller, or the full 000/11 family. Those claims require
the completed advertised covers, standalone exact replay, and the final
caller/coverage assembly.

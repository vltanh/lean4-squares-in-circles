# Complete strict-radius closure of the original-nine 000/11 domain

November 2, 2026. Computer-assisted discovery, complete independent exact
replay, and a physical hand/table assembly. No Lean, Lake, or CI.

**Theorem.** The full predicate `D_000/11^lt` in
`A2_COVERAGE_AND_CLOSURE_CONTRACT.md` is empty. All nine original unit
squares, their independent frames, all 36 original corner constraints,
all 36 physical pair constraints, and the five marked cone comparisons
are retained. This is a strict-radius closure, classified **C**, with
no assertion that the closed-Q predicate is empty.

Put

\[
 Q=1105/256,\qquad l=29/60,\qquad u=13/12.
\]

## 1. Normalize while preserving the exact fixed mask

Suppose a configuration and witness satisfy `D_000/11^lt`. Label the
actual horizontal main four-chain M0,M1,M2,M3 and the designated
outsider cone three-chain L,P,R. Both short links are strictly weak;
the two other original squares remain unrestricted physical outsiders.

Apply `SMALL_CENTER_EXPANSION_PRESERVES_FIXED_MASKS.md`. Choose one
common multiplier lambda>1 sufficiently close to one, and multiply all
nine centers by lambda, leaving every original frame unchanged. The
finite strict corner margins permit this expansion while every corner
still has squared norm below Q. Each original physical separating
normal becomes strict, so the expanded closed squares are pairwise
disjoint. Cone comparisons remain homogeneous. Choosing lambda below
each of the two strict weak-gap ratios preserves both weak short bits.
The actual main links remain actual. The same lemma can preserve the
outsider columns, although the proof may simply classify them after
expansion.

For the original and expanded adjusted main spans,

\[
 D_0=x_3-x_0-h_0-h_3\ge2h_1+2h_2\ge2,
\]

\[
 D_\lambda=\lambda D_0+(\lambda-1)(h_0+h_3)>2.
\tag{1}
\]

Henceforth use the expanded configuration and write D for D_lambda.
No attainment of the outer circle is needed. Every caller below assumes
only closed-Q containment, the stated original comparisons and physical
disjointness, and the strict span (1). The side-marker theorem's
closed-square hypothesis is supplied by the same expansion.

This normalization makes no claim about preservation of a particular
historical positional root. It is used only for the fixed full mask.

## 2. The common terminal uses five distinct original squares

The accepted `WIDENED_JOINT_FIVE_SQUARE_CAP.md` gives D<=2 if there
are three distinct original outsiders A,F,B satisfying

\[
 x_A\le0\le x_B,\qquad |x_F|\le l,\qquad
 y_A,y_B\ge3/5,\qquad y_F-h_F\ge1/10.
\tag{2}
\]

The other two squares in this cap are the original main endpoints M0,M3.
Its actual endpoint-band and endpoint-frame hypotheses follow from the
actual four-chain bounds. Every outsider satisfies |x|<u. Thus (2)
supplies the wider cap's full shoulder and central domains. A shoulder
may itself be a central original; the three choices must remain distinct.

The cap retains independent original frames and physical pair
separators, including all real central slopes. Its previously accepted
four outer covers and analytic slope complements are unchanged. Each
caller below derives (2) and therefore contradicts (1).

## 3. Exact finite count and height coverage

Assign every outsider to exactly one of

\[
 L_c:\ x\le-l,\qquad C:\ |x|<l,\qquad R_c:\ x\ge l.
\]

The boundary lines belong to the side columns. The complete side-capacity
and marker theorem gives at most two outsiders on each side. Five
outsiders therefore have, up to horizontal reflection, exactly these
six counts:

\[
 (2,1,2),\ (2,2,1),\ (2,3,0),\ (1,3,1),\ (1,4,0),\ (0,5,0).
\tag{3}
\]

These represent all nine ordered triples; no other occupancy is possible.

`ACTUAL_FOUR_CONE_THREE_COMMON_ROUTING.md` puts the selected P in the
central strip and gives |xP|<23/60, xL<-19/60, and xR>19/60. A single
vertical reflection makes P above both inner mains, every selected side
endpoint above its own main, and every selected central endpoint above
both mains. Every central outsider is either above both inner mains or
below both. Physical clearance excludes equality and mixed routing.

Each cone gap is at least the sum of two inset halfwidths, so the selected
triple has horizontal span at least sqrt(2)>2l. It cannot be wholly
central. If R is central, L is a far-left side outsider with yL>27/40,
P is negative central, and R is positive central. Horizontal reflection
gives the counterpart. These are consequences of the original three
units, without an actual short-edge assumption.

## 4. Complete caller for each count

The table lists complete source arguments, not additional assumptions.
All its reflection operations act on the original configuration and
chain labels together. Each source retains every unselected original
square; omitting an unnecessary constraint from a contradiction subsystem
does not replace a square or add a hypothesis.

| Count up to reflection | Exhaustive internal alternatives | Complete source |
|---|---|---|
| (2,1,2) | Both full-side marker orders, including their vertical reflections; incompatible opposite extremes are excluded by the main cone | `ACTUAL_FOUR_FULL_SIDE_OCCUPANCY_CLOSED_HAND_PROOF.md` |
| (2,2,1) | Full-side main bottom, middle, or top | Bottom/top: `ACTUAL_FOUR_221_FULL_SIDE_BOTTOM_CLOSED_HAND_PROOF.md`; middle: `ACTUAL_FOUR_221_FULL_SIDE_MIDDLE_ASSEMBLY.md` |
| (2,3,0) | Selected P,R central and upper; remaining central upper or lower; full-side main bottom or middle | `ACTUAL_FOUR_230_WHOLE_OCCUPANCY_CLOSED_HAND_PROOF.md` |
| (1,3,1) | One, two, or three upper central originals | One/three: `ACTUAL_FOUR_MANY_CENTRAL_EASY_CALLERS.md`; two: Section 5 below |
| (1,4,0) | Two, three, or four upper central originals | Two/four: `ACTUAL_FOUR_MANY_CENTRAL_EASY_CALLERS.md`; three: `ACTUAL_FOUR_140_THREE_UPPER_ONE_LOWER_CLOSED_HAND_PROOF.md` |
| (0,5,0) | All outsiders central | Contradicts the selected cone span directly |

For (2,3,0) and (1,4,0), common routing already places two selected
central originals above both mains. There are no zero-upper or one-upper
complements. The selected L is above the left main, excluding the top
full-side marker in (2,3,0). The bottom/top (2,2,1) proof does not depend
on retaining an upward selected short-chain direction and hence its
vertical reflection covers the top marker without an extra premise.

## 5. The complete two-upper (1,3,1) split

There are two upper central originals and one lower. At least one side
outsider is a selected cone endpoint, so at least one lies above its own
main. Both cannot lie below. Physical same-side clearance excludes equal
main/outsider heights. Exactly two side-order families remain.

If both side outsiders are above their own mains, use
`ACTUAL_FOUR_131_BOTH_SIDE_UPPER_CLOSED_HAND_PROOF.md`. Two low side
outsiders would make the entire outsider x-span less than 49/40,
contradicting the selected cone span. When both are high, the lower
central original gives both main heights above -9/10 through a complete
25-row table. Original disk inequalities then force at least one upper
central whole floor above 1/10. When exactly one side is low, the complete
very-low/moderate helper split forces every upper central whole floor
above 1/10; its moderate branch uses a complete 112-leaf original-unit
versus raised-inset table. Every branch extracts three distinct original
cap witnesses.

Otherwise, reflect horizontally so the left side outsider is above its
main and the right side outsider below. The latter cannot be selected.
Thus selected R is central and selected L is the actual left outsider.
`ACTUAL_FOUR_131_OPPOSITE_SIDES_CLOSURE.md` applies. Its two selected cone
budgets retain the same original P frame. A complete 9,035-leaf cover
proves the remaining P-height bound; the far-left/high-P disk lemma and
coupled inset-loss bound give precisely the original L,P,R witnesses
for (2). There is no missing third side-order family.

## 6. The complete middle-main (2,2,1) input

For clarity, the largest table is consumed only after all its physical
premises have been supplied. The full left side contains an original
lower outsider and an original upper outsider around M1. The separate
74-row physical-pair theorem gives y1>-17/50; the upper outsider is
therefore a high left shoulder.

If a selected endpoint is central, the two selected central originals
are ordered with opposite signs. The coupled cone-loss theorem gives
the negative one's high floor. The original sole right-side outsider's
three exhaustive possibilities are: high above its main, low above its
main, or below its main. Respectively it supplies the high right shoulder,
forces the positive selected central's high floor, or supplies the
reflected lower-side height bound making that central high. These cases
all use three distinct originals.

If both selected endpoints are side outsiders, the complete first table
proves yR>3/5 using y1>=-7/20. Its 19,387 leaves have passed independent
80-bit exact replay. The complete second table uses this established
high-R consequence and y1>=-17/50 to prove yP-hP>1/10. Its 2,821,264
leaves have passed a separate exact C++ replay, complete source and
coverage audits, and a fresh root replay. Its least exact reserve is

\[
                         360606/2^{48}>0.
\]

The seven-variable physical reduction includes every original chirality
and separator owner, retains the same P frame and center across both
links, and explicitly justifies every finite interval contraction.
The tP<=1/27 complement is excluded by a printed hand inequality.
The original lower left-side unit remains the eighth physical premise;
the other central outsider needs no additional restriction. The exact
case assembly is `ACTUAL_FOUR_221_FULL_SIDE_MIDDLE_ASSEMBLY.md`.

## 7. Acyclic dependencies and conclusion

The dependencies can be ordered as follows:

1. Original-square support/inset facts, actual-four bounds and side
   capacity, the universal physical two-square cap, and normalization.
2. The independently proved widened five-square cap, common routing,
   original-pair clearance tables, and the two universal orientation
   tolls with their complete one-variable covers.
3. Central floor/height extraction results, low-side and lower-central
   exclusions, and the completed small occupancy inputs.
4. The middle-case low-right exclusion, followed by its low-floor
   exclusion; every other complete occupancy caller.
5. The exhaustive count and side-order assembly in Sections 3--6.

The widened cap assumes no occupancy conclusion. The universal
orientation tolls assume no shoulder height or central floor and are
independent of that cap. The same-side high-central disk lemma used by
the middle proof is the two-unit lemma in Section 2 of the both-upper
(1,3,1) source; it does not depend on that source's occupancy conclusion.
The two middle tables are used in their explicit low-right-before-floor
order. Thus the dependency graph has no circular call.

Every alternative of (3) contradicts D>2, either directly or through
the cap D<=2. This proves the theorem for every radius strictly below
sqrt(Q), including those arbitrarily close to it. No fixed distance
below Q, tilt gap, contact pattern, or additional positional restriction
has been assumed.

Combining this result with the earlier 000/00, 000/01, and 000/10
proofs gives the useful corollary: nine original squares with an actual
cone four-chain and a disjoint cone three-chain cannot fit strictly below
sqrt(Q), regardless of the two selected short bits.

The fixed frontier changes only at `000/11`: seven masks are now closed
for strict radius and 25 remain open. This proof leaves the closed-Q
status of `000/11` unclassified. It does not close A.2 globally, classify
unrestricted equality, or alter any of the 7,915 positional-root IDs.
The same 15 roadmap gates remain.

# The original nine-square minimum lies in the required radius window

Date: October 29, 2026 UTC. Author: current root continuation.

**Status: complete proposed hand join for original G4.2.b, submitted for
separate independent review.** This proves the entire lower/upper radius
entry for an actual global minimum of the unchanged nine-square Packing
predicate. It uses the already accepted stronger same-nine lower bound
instead of the optional eight-square deletion route. It does not supply
the missing sharp lower bound, choose a stress certificate or classify
equality packings. Every one of the nine actual squares is retained.

Put Q=1105/256 and R0=sqrt(1105)/16, so R0>0 and R0^2=Q.

## 1. Exact original upper witness

Use the original axisSquare frame, independently allowed by UnitSquare:
cosine=1, sine=0. Take the following nine distinct centers about O=0.

| Group | All horizontal center coordinates | Vertical center coordinate |
| --- | --- | --- |
| T, two units | -1/2, 1/2 | 17/16 |
| M, four units | -3/2, -1/2, 1/2, 3/2 | 1/16 |
| B, three units | -1, 0, 1 | -15/16 |

These are nine original labels, with an ordinary unit square at each.
Within each row distinct horizontal centers differ by at least one.
Thus their open horizontal projection intervals are disjoint. Between
two rows the vertical center gap is one or two, so their open vertical
projection intervals are disjoint. Every pair of different open square
interiors is therefore disjoint, including adjacent rows whose closed
sides touch. No physical contact is excluded by the original predicate.

For every point of the closed axis square at (x,y),

    normSq(p) <= (|x|+1/2)^2+(|y|+1/2)^2.

Each bound is attained at an actual outer corner. The largest values
over the complete rows are exactly

    T: 1+(25/16)^2 = 881/256 < Q,
    M: 4+(9/16)^2 = 1105/256 = Q,
    B: 9/4+(23/16)^2 = 1105/256 = Q.

Consequently every point of every closed square lies in the original
closed disk of radius R0. Together with nonnegative R0 and the pairwise
open-interior check, this is exactly Packing S0 0 R0. This finite direct
construction is a witness, not a sampled impossibility certificate.

The same construction appears in HAND_PROOF.md Section 1, but its full
verification is given here. No horizontal-layer hypothesis is imposed
on an arbitrary competing packing; a particular upper witness is allowed
to have a common frame.

## 2. Attain an original global minimum, with all nine units

Apply ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md
to this feasible nine-unit witness. Its compactness theorem is about the
unchanged original Packing predicate and all independent frame circles.
It supplies an actual origin-centered packing of nine units at the global
least nonnegative radius Rmin, with

    0 <= Rmin <= R0.

The bound is global over every original containing-circle center and
every independent square frame. It does not restrict the minimum to the
explicit witness's rows, orientation, graph or physical contact pattern.
If later arguments require it, the same source supplies an attained
minimum of Phi=sum |center_i|^2 within the full minimum-radius fiber.
This refinement changes neither the value of Rmin nor the nine-unit
Packing predicate. No stress selection follows from compactness alone.

## 3. The complete same-nine lower entry

The accepted LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md proves

    R > 2

for every original nine-unit packing, at arbitrary nonnegative R and
with arbitrary independent frames and physical contacts. Its hypotheses
are exactly whole closed-square containment and disjoint open interiors;
it has no stress, minimizer, initial radius window or eight-square premise.
Apply it to the actual nine units attained in Section 2. Thus

    79/40 < 2 < Rmin <= sqrt(1105)/16.                  (1)

The first strict inequality is the exact identity 2-79/40=1/40>0.
In particular the complete declared closed certificate window

    79/40 <= Rmin <= sqrt(1105)/16

holds. No zero-stress square has been removed, and no theorem for an
isolated six-body or smaller positive component is being substituted.

This invokes the accepted analytic lower-window assembly with its
existing complete independent reviews and active hand-proof dependencies.
It does not claim a new recursive proof audit of that entire measure
argument. Its old generated charge tables and numerical evaluators are
not new premises of this join.

## 4. Subcritical entry and the weak upper endpoint

If a hypothetical original nine-unit packing has R^2<Q, its original
nonnegative radius gives R<R0. Global minimality gives
0<=Rmin<=R<R0. Combining with the same-nine lower theorem yields

    79/40 < 2 < Rmin < sqrt(1105)/16.                   (2)

Alternatively that original packing itself may provide the compactness
ceiling; the recovered compactness theorem gives the same conclusion.
There is no logical dependence on the unknown sharp lower bound.

For the attained global minimum without a subcritical assumption, only
the weak upper endpoint in (1) is asserted. Equality at Rmin=R0 is
allowed. Once a sharp lower bound is eventually proved, (1) will identify
the minimum value; it currently supplies only the necessary window.

An arbitrary original equality packing need not minimize Phi. Nothing
in (1)--(2) permits replacing it by a Phi minimizer for classification.
The original equality obligations remain separate and open.

## 5. Original gate and exact dependency scope

The original G4.2.b asks to use the upper construction and a valid lower
entry to place the actual minimum in the declared window. Its historical
description names the eight-square deletion/import route. The roadmap's
already accepted W.3 and its G4.3.c explicitly permit replacing that lower
import by the independent same-nine theorem. Equation (1) proves the
whole required radius assertion using that documented stronger route.
The existing ID and its mathematical target are preserved; no theorem
is assumed from a smaller positive subcomponent.

After separate independent review, exactly G4.2.b is eligible to change
from open to checked in addition to the separately reviewed G4.2.a.
G4.2.c (common certificate selection), G4.2.d (complete exclusions),
G4.2.e (the sharp minimum bound), the parent G4.2, equality and global
integration remain open. The conditional transfer in Section 4 does
not assert that the subcritical minimizer has been excluded.

| Operative complete source | SHA256 | Consumed scope |
| --- | --- | --- |
| SquaresInCircles/Geometry.lean | 64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94 | Original UnitSquare, closed/open membership, nonnegative disk radius and Packing definitions |
| ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md | be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06 | Complete original finite Packing compact minimum and optional continuous refinement |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Entire already accepted same-nine theorem R>2, without an assumed radius window |

The upper witness is proved self-contained in Section 1. The definitions
are unchanged. No numerical pose search, new packing certificate, Lean
compilation, CI/workflow dispatch, remote mutation or merge is part of
this proof. No original status flag is edited before review and adoption.

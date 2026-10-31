# Independent review of the original nine-square minimum-radius window

Date: October 29, 2026 UTC. Reviewer: block_forests continuation, separate
from the author of the proposed join.

**Verdict: PASS at the complete stated original G4.2.b scope.** The exact
nine-square upper witness and the accepted same-nine lower theorem put an
attained original global minimum in the required closed radius window.
The manuscript does not assume the missing sharp lower bound or a chosen
stress certificate. No correction is required.

## 1. Frozen target and complete direct inputs

The target was read in full. Both mathematical inputs below were also read
in full, and the actual Geometry definitions were checked directly. The
three dependency hashes printed in the target match their current bytes.

| File | SHA256 | Review use |
| --- | --- | --- |
| ORIGINAL_NINE_MINIMUM_RADIUS_WINDOW_WITHOUT_EIGHT_SQUARE_IMPORT_2026_10_29.md | 299638eb3cdfcb4666bb9538bbd3a8f82de1bd9e69e2f748eb885faccc0609d2 | Entire proposed join |
| SquaresInCircles/Geometry.lean | 64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94 | Actual Point, normSq, UnitSquare, localX/localY, closedSquare, openSquare, inDisk, Packing and axisSquare definitions |
| ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md | be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06 | Complete original finite-packing compactness, global attainment, optional Phi refinement and conditional transfer |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Entire accepted same-nine theorem R>2 with no assumed window |

The relevant existing roadmap entries W.3, G4.2.a--f and G4.3.c were read
directly to check the proposed bookkeeping implication. This review checks
the new join and the literal interfaces of the accepted mathematical
inputs. It does not claim a new recursive independent audit of every
analytic-measure source cited by the lower-window assembly.

## 2. The explicit witness satisfies the original predicate

For cosine=1 and sine=0, the source's square at center (x,y) is exactly the
original axisSquare. Its closed set is
[x-1/2,x+1/2] times [y-1/2,y+1/2], and its open set has both inequalities
strict. The nine table entries are distinct and provide nine original
labels; no frame restriction is imposed on other packings.

In each row horizontal center gaps are at least one. Between the top,
middle and bottom rows the vertical center gaps are respectively one,
one and two. Thus a pair in one row has disjoint open horizontal
projections, and a pair in different rows has disjoint open vertical
projections. This proves the actual pairwise open-interior condition even
at shared-side endpoints. The argument does not require disjoint closed
squares.

The coordinatewise upper bound for the squared norm on a whole closed
square is exact at an outer corner. The three row maxima independently
check as

    top:    1 + 625/256 = 881/256,
    middle: 4 +  81/256 = 1105/256,
    bottom: 9/4 + 529/256 = 1105/256.

The farthest vertical magnitudes used here are 25/16, 9/16 and 23/16;
the farthest horizontal magnitudes are 1, 2 and 3/2. Consequently every
point of every closed unit is in the original disk of squared radius
1105/256. Since R0=sqrt(1105)/16 is positive and R0 squared is 1105/256,
all three conjuncts of the unchanged original Packing predicate hold.

This verification is a direct exact construction. It does not call a
numerical evaluator, pose sample or exclusion certificate.

## 3. Compact attainment applies to all original frames and centers

The compactness input removes an arbitrary circle center by translating
all original square centers together. Its compact coordinate space retains
each independent frame circle. Whole-square containment is equivalent to
the four continuous vertex inequalities, and a hypothetical point in two
limit open interiors persists under sufficiently small coordinate changes.
Those are exactly the closed feasibility conditions required here.

The attained radius on the witness sublevel is global: any original
competitor above R0 already has radius at least the attained value, and a
competitor at or below R0 translates into that same compact feasible set.
All nine original units remain. The resulting inequality

    0 <= Rmin <= R0

therefore has no added row, common-frame, contact-graph, stress or load
premise. Minimizing continuous Phi on the minimum-radius fiber is available
but unnecessary for the window assertion. Neither compactness nor this
optional refinement supplies a simultaneous stress selection.

## 4. The lower-window interface and noncircular subcritical entry

The accepted lower input states R>2 for arbitrary nine independently
oriented actual closed unit squares in a disk of nonnegative radius, with
disjoint open interiors. It explicitly includes all contacts and allows
the circle origin on square boundaries. Its contradiction places a
hypothetical R<=2 packing inside the radius-two disk without moving,
scaling or deleting any unit, and applies the same nonnegative measure to
all nine open interiors. No radius window or positive-component premise
appears in this theorem.

It therefore applies literally to the nine-unit minimizer above. The exact
positive difference 2-79/40=1/40 yields

    79/40 < 2 < Rmin <= sqrt(1105)/16.

This implies the entire required closed window. No sharp lower bound
Rmin squared >=1105/256 was used.

For a hypothetical original R squared <1105/256, original nonnegativity
gives R<R0. Global minimality then gives Rmin<=R<R0, while the same-nine
lower theorem gives Rmin>2. This proves the stated strict-upper-window
conditional entry. Without that hypothesis only Rmin<=R0 is asserted,
so the sharp upper endpoint is correctly retained.

## 5. Exact gate consequence and remaining obligations

W.3 is already checked in the existing roadmap as an independent same-nine
replacement for the eight-square import. G4.3.c explicitly records whether
that replacement has been made. The new join proves the entire radius
assertion requested by existing G4.2.b through that documented replacement;
the historical mention of deletion does not introduce an additional
mathematical need to delete a unit after W.3 supplies a stronger result.

After root adoption this source supports checking exactly G4.2.b. Original
G4.2.a is supplied and reviewed separately by the compactness package; the
new join is not an additional proof of the missing G4.2.c--e assertions.
It closes no cyclic coarse cell, proves no unrestricted sharp lower bound,
and does not check the parent G4.2 or the equality/integration gates.

The explicit warning about equality is correct: a particular original
packing at the proposed sharp radius need not minimize Phi. Replacing it
by a Phi minimizer cannot establish its individual classification. The
conditional radius transfer has no such classification consequence.

All conclusions retain the unchanged original nine-square predicate and
every actual square. This review changed no authoritative ledger, roadmap,
Lean implementation or remote state and ran no Lean compilation, CI,
numerical pose search or new packing certificate.

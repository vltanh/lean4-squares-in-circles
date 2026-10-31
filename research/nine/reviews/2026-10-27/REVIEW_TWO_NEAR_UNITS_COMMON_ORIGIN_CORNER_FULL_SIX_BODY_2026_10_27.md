# Independent full review: two near units at one corner of an origin-containing square

Date: October 27, 2026.
Reviewer: six_body_core, independently of the author and root reviewer.

**Verdict: PASS for the complete physical theorem and its stated conditional owner reduction.** The entire source was read and checked. It does not exclude either retained owner interface, close an original graph domain, or create fine or coarse ledger credit.

## 1. Exact source and boundary

The reviewed full source is

    GENERAL_TWO_NEAR_UNITS_AT_ONE_ORIGIN_CORNER.md
    SHA256 682b48f2f82b6ae35bfc7ef1a5efa900942fc115f2485048385c5b3403de151d.

Sections 1–3 are a self-contained physical proof. No force balance, torque, degree, circle system, selected-normal owner rule, or origin avoidance of the two near units is used there. Section 4 imports exactly the physical noncontact conclusion of

    GENERAL_SMALL_ORIGIN_CORNER_CONTACT_KERNELS.md
    SHA256 b977be65217728c0363e8bab030bdb3d11b1b8ef75cc32d295a8337c4ea01477,

whose operative rectangle source is

    ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md
    SHA256 6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467.

Both of those complete physical sources were previously read in full and independently audited in

    REVIEW_SMALL_ORIGIN_CORNER_KERNELS_FULL_SIX_BODY_2026_10_27.md
    SHA256 f6111940d64c5d5e48a50e6f5dedf1e3160c87919bcd7a81c7bfcad928cdec39.

Their unchanged exact pins are the inherited boundary for Section 4. The current review checks that the new application meets their actual hypotheses; it does not claim that some stronger contact conclusion has been proved at an origin-free H or a different near-disk radius.

## 2. The full common-vertex physical theorem

The actual H vertex P and its inward own axes give O−P=ai+bj with 0≤a,b≤1 because O belongs to closed H. The proof allows any ε≥0. If a>ε, every selected actual disk point q of either near unit has strictly positive i displacement from P. In particular q≠P, including the closed-disk endpoint and ε=0 cases.

The preliminary disjointness fact is correct: an interior point of one square cannot belong to another closed square, because the latter's interior is dense in its closure and would enter a sufficiently small open neighborhood of the former. It follows that P is a boundary point of each of X,Y. It also follows that neither actual tangent sector can contain a nonzero direction with both coordinates positive; sufficiently small displacement along that direction would be a point of the closed near unit in int H.

Convexity puts q−P in the actual tangent sector. Its positive i component and nonpositive j component place its angle in (−π/2,0]. The complete sector at P has angle π/2 or π, according as P is a vertex or relative-side-interior point. Its angular lift can be taken inside the closed complement [−3π/2,0] of H's open first quadrant. If its endpoints are α,β, then β>−π/2, β≤0 and α≤β−π/2≤−π/2.

Thus both actual open tangent sectors contain the nonempty interval (−π/2,min(β_X,β_Y)). A single direction in that interval enters both actual open units for sufficiently small positive displacement from the same unchanged P. This contradicts interior disjointness. The conclusion a≤ε follows, and exchanging the two own axes proves b≤ε. Orthogonality gives |P−O|≤√2ε.

The proof correctly includes a disk point on an H side, where its direction angle can equal zero; a disk point on its own unit boundary; a point on the boundary of the closed disk; and a common P in the relative interior of either near unit's side. No disk point is perturbed into the open disk and no actual contact is substituted for another point.

Closed-origin containment is the full stated scope. The proof does not require O in int H, but does require O in closed H to make the two inward margins nonnegative. It gives no corresponding conclusion for an origin-free H.

## 3. Two non-owned small applications

A separating normal which is not an own axis of H strictly exposes one actual H vertex. Its application is necessarily that vertex, whether the contact is owned by the other unit or is free. The two applications have mutual distance less than 3/4, whereas distinct H vertices are at least one apart. They therefore equal the same actual P.

Both distinct actual near units really contain P, so Section 1 applies without a new physical contact or normal choice. For 0≤ε<1/60 the bound √2ε<1/40 is strict. The original applications and non-owned normals remain unchanged. This argument includes original aggregate means because a strictly exposed support face is a singleton.

## 4. Every shallow-support owner alternative is retained correctly

For Section 3 the additional open-origin premise supplies positive own support heights. If both normals are H-owned and opposite, their heights sum to the true unit width one, contradicting the bound 2ε<1. If they are adjacent, their actual own support lines meet in a genuine H corner with both inward margins at most ε, giving the same strict small-corner bound. If they coincide, the source correctly retains the entire same-side interface with its two original applications and means.

For the mixed owner case, the non-owned contact is an actual H vertex P of norm below 3/8. The opposite side of the actual shallow H face has distance 1−h>59/60, so P cannot lie there and must lie on the shallow face itself. This proves only the stated incidence.

In particular this argument does not show that the H-owned contact application equals P, that its other actual unit contains P, or that the non-owned-contact unit lies entirely beyond the shallow face. The manuscript explicitly avoids those unsupported inferences. An H vertex in the relative interior of a private unit's owned side remains a legitimate mixed interface. This is essential to the completeness of the retained owner cover.

## 5. The conditional boundary-neighbor consequence

At the stated critical/high radius, two distinct physical boundary neighbors K,T of the actual closed-origin H which touch each other cannot coexist with an actual H vertex of norm below 1/40, by the fully reviewed b977 physical kernel. The present small-corner conclusions meet precisely those hypotheses. No positive circle multiplier or degree equation is needed at K or T, and no original physical circle endpoint is lost.

Consequently the new source correctly removes the non-owned/non-owned and adjacent-owned/owned possibilities only under that extra physical boundary-neighbor premise. The full remaining alternatives are exactly both normals owned by one H side, or one H-owned normal with the other actual H-vertex application on that same side. Neither alternative is excluded by this manuscript.

An actual graph caller must still establish the original near-point, small-application and shallow-support hypotheses at its true body degrees. The local theorem does not produce them by shortening a higher-degree star. The stated conditional scope and its explicit lack of graph-cell credit are correct.

No Lean compilation, CI, pose sampling, equilibrium modification, remote mutation or original-ledger edit was performed for this review.

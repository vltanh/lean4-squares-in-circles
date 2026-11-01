# Common-point direct triangle: exact sector and exit-direction reduction

Date: 2026-11-01. PR #11 hand-only continuation.

**Evidence:** H — new elementary hand derivation, NOT independently reviewed. This is a necessary-condition lemma, not a complete exclusion of the common-point direct triangle, a new original case closure, or a global packing bound. No Lean, CI or mathematical scripts.

## Original physical setting

Take the same nine actual closed unit squares with pairwise disjoint open interiors inside the disk of radius R, with R^2 <= 1105/256. Retain one complete physical positive force-and-torque certificate, all actual original contacts, orientations, application points and shared-side means, and all zero and nonzero circle coefficients.

Let K={A,B,C} be an entirely selected-circle-unloaded original positive triangle. Each body has original full positive degree exactly three: the two displayed internal edges and exactly one positive edge to an actual square outside K. The three outside squares need not be distinct. Suppose a point P belongs to A intersect B intersect C. Do NOT infer that the selected applications on positive AB, BC and CA all equal P; a physical shared-side contact may carry an application at another point of that side.

## Lemma 1. A nonparallel three-square junction uses three genuine vertices

If three distinct interior-disjoint unit squares all contain P, then P is a boundary point of each. At most one of them has P in the relative interior of a side. If one does, all three square frames are parallel modulo quarter turns. Therefore, if the three frames are not all parallel, P is a genuine vertex of each square.

**Proof.** At P, a square contributes an inward tangent sector of angular size pi/2 at a vertex and pi at a relative side-interior point. Distinct square interiors force the interiors of these tangent sectors to be pairwise disjoint. Three angles must sum to at most 2pi. If one sector is a halfplane, the other two sectors must each be vertex quadrants, and their total is precisely 2pi. They tile the complementary halfplane. The two quadrant sides then consist of its two bounding directions and the single perpendicular mid-direction; each frame is parallel to the halfplane square's frame. Two halfplane sectors would make the sum exceed 2pi. Hence nonparallel frames force three genuine vertices. This uses only actual whole-square geometry. QED.

**Four-unit corollary.** If a fourth distinct actual unit also contains P, then all four contribute vertex quadrants whose angles total 2pi. They tile the full turn, so all four square frames are parallel modulo quarter turns. Hence a nonparallel three-square common junction cannot host a fourth actual unit.

## Lemma 2. If all three internal force applications really equal P, the exits lie on discrete rays

Assume, in addition to Lemma 1's nonparallel case, that the ORIGINAL positive AB, BC and CA forces have exactly the SAME actual application P (a stronger premise than mere physical common-point incidence). Then for each i in {A,B,C}, let q_i be the unchanged application of its one positive outside exit, let n_i point from i into its outside neighbor, and let u_i,v_i be the two unit inward side directions from P into i.

The complete original torque equation at square i gives

    det(q_i-P,n_i)=0.                               (1)

Furthermore q_i != P. Its only possible exit features are EXACTLY

    (q_i,n_i)=(P+u_i,u_i),
                 (P+v_i,v_i),
                 (P+u_i+v_i,(u_i+v_i)/sqrt(2)).      (2)

Its actual outside neighbor therefore contains, respectively, one of the following points of the SAME original disk:

    P+2u_i,  P+2v_i,  P+(1+1/sqrt(2))(u_i+v_i).      (3)

The three positive exit forces and their applications remain in the original certificate. This is a necessary classification, not a claim that every displayed feature is physically realizable.

**Proof.** The two internal original forces at i are applied at P. Its total circle load is zero, so their moments about P vanish and the remaining sole positive exit must have zero moment about P. This proves (1), without using or changing the other squares' equations.

If q_i=P, the outside neighbor also contains P, making four distinct actual units there. The four-unit corollary contradicts the nonparallel premise. Hence q_i != P.

Write i=P+[0,1]u_i+[0,1]v_i, and q_i-P=s u_i+t v_i, where 0<=s,t<=1 and s+t>0. Equation (1) says q_i-P=lambda n_i with lambda>0: the sign is positive because q_i is a maximum-n_i support point of i, whereas P belongs to i, so n_i dot(q_i-P)>=0; collinearity and q_i != P make it strictly positive. Thus the two components of n_i in the inward frame are nonnegative.

If both components are positive, the unique maximum support of i in direction n_i is P+u_i+v_i. Collinearity then makes s=t=1 and n_i=(u_i+v_i)/sqrt(2). If exactly one component is positive, say along u_i, maximum support has u_i-coordinate 1 and collinearity forces v_i-coordinate 0, so q_i=P+u_i and n_i=u_i. The v_i case is symmetric. This proves (2), including all support means: none is replaced by a convenient endpoint; it is forced to the stated point.

The exit application's q_i is a minimum-n_i support point of the unchanged outside neighbor. Any unit square containing a minimum-n support point q contains q+n: in each own-side coordinate adding the corresponding component of n moves inward from its minimum support face by at most one. Thus the outside neighbor contains q_i+n_i. Substitute (2) to obtain (3). All three points belong to the same original disk. QED.

## Scope fence / live geometric obligation

The common-point branch is **not closed** by these lemmas. When a positive internal pair shares a physical side, its ORIGINAL application can be a different point on that shared segment; the additional premise in Lemma 2 then fails. A full common-point exclusion must separately cover those unchanged application means, all coincident junctions and all actual external-unit placements. The earlier exploratory claim of a complete common-point exclusion has not been reconstructed as a full hand manuscript or independently verified, and is NOT adopted here.

Likewise the exploratory "all three internal applications are vertices of both touching squares -> R>9/4" claim has no recovered complete contact-geometry and outside-force derivation. It is OPEN pending proof; no equilateral contact arrangement is assumed or promoted by this source.

## Exact next proof test

For each genuine common-point sector pattern, classify whether each internal positive contact is point-only (application forced to P) or an original shared side (application a free point of its actual segment). Keep the original three full unloaded force-and-torque stars. For the all-point case, use the explicitly present disk points (3) to prove an impossible disk diameter or three-point circumradius at R^2<=1105/256; an orientation or point-distance calculation must cover all three rays and all repeated outside-terminal identities. For shared-side patterns, use their true separate applications and obtain an equally complete width/moment inequality without setting any mean to P.

The original coarse register remains 41/58, the original fine flags 2,373/2,513, and the nested exterior table 18/38.

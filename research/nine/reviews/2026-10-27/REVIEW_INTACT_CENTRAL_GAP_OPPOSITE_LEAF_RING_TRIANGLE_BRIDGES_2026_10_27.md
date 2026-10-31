# Independent full review: intact central-gap theta and opposite-leaf four-rings

Date: October 27, 2026.
Reviewer: triangle_bridges, independent of the mixed_blocks author.

**Verdict: PASS for the complete gap lemma, both original C3.334.b1
domains, and both stated original C2.34.b2 domains.**

Reviewed full source:

    INTACT_MIDDLE_TRIANGLE_OPPOSITE_LEAF_FOUR_RING_EXCLUSION.md
    SHA256 ad860b7e65232da5b7e5d0afb2f55cb3459779528faeaf9c354cc4d4058e78b1

No correction is requested. All actual degree, endpoint, completion-unit,
and whole-load joins were checked. This review changes no cover, original
ID, checkbox, coarse status, or shared ledger.

## 1. The exact new geometric hypothesis is sufficient

The six actual bodies A,H,K,B,J,U are distinct. The original edges
HA,HB,BK,KJ,JH,AU remain, while AK is absent from the positive graph.
B,J,U are physically boundary, A,K physically clear, O is in int A,
and the actual radial segment [O,k] meets no body other than A,K.
Every actual positive application at A or K is outside that segment.
The proof never assigns a force or a new normal to the auxiliary AK
curve, and H/K may keep the positive chord and arbitrary other forces.

Convexity gives a last A point alpha*k and a first K point beta*k,
with 0<alpha<=beta<=1. A point before alpha*k is interior to A:
it lies strictly between the interior point O and a point of the
convex closed A. Therefore no closed K point can precede it, by
interior disjointness. The resulting open gap is outside every body.
Equality alpha=beta is a genuine two-body physical contact and is
explicitly included. The K intersection may run along a side; the
proof never assumes k or beta*k is interior to K.

The path from c_A to alpha*k, through the gap, and from beta*k to
c_K is simple. Its two open endpoint segments lie in the corresponding
actual square interiors; its open middle segment meets no unit. Those
facts also prove disjointness from every other closed unit. In the
zero-gap case only A,K contain the junction.

## 2. The new curve admits one simultaneous full compatible embedding

The new ports are different from all original positive applications
at A,K. Distinct boundary points of a convex square have distinct
rays from its interior center, so the new half-edges fit into the
actual center stars with their geometric cyclic order. They cannot
cross any of the original straight center-to-application strands.

All original weak contact junctions retain the common certificate's
compatible local routing. A new zero-gap AK junction has only two
physical units and no old positive application there, so it creates
no interlacing multiway matching. The finite original routing disks
and strand tubes can be chosen sufficiently small away from the new
curve. Thus the proof constructs an embedding of the complete original
positive graph plus one auxiliary edge, not independently incompatible
embeddings of different subgraphs.

PHYSICAL_BODY_GRAPH_UNCROSSING.md, Sections 5--6, was reread in full.
Its exact center/contact construction, four-body junction order,
parallel strand tubes and exterior-boundary spokes agree with every
use here. No uncrossing, normal reselection, force thinning or change
of an original application is needed for the newly added curve.

## 3. All physical boundary vertices keep exterior access

The source's circle-corner uniqueness argument is valid. One can
also use the direct identity from the reread uncrossing proof:
containment gives z dot w_i<=-1/2 for both inward own side directions
at a circle corner, so a short inward radial segment belongs to the
open square. Two units sharing z would overlap on that segment.

For each named boundary unit B,J,U, its center-to-circle-corner spoke
meets the original center/contact drawing only at its own center.
No actual positive application can equal its unique circle corner.
The new auxiliary curve is disjoint from all these closed boundary
units, hence has positive clearance from their compact spokes.
The full compatible routing can therefore preserve the spokes and
their outward continuation to infinity simultaneously.

This verifies that B,J,U remain incident to the unbounded face of
the augmented graph. Physical circle contact is enough; no positive
circle multiplier is silently imposed for this topological step.
The auxiliary curve stays within the containing disk and introduces
no external crossing of a protected spoke.

## 4. The three theta placements are exhaustive

The three internally disjoint H-to-K paths have pages A,B,J. In a
plane embedding of this K2,3 one pair of paths bounds its unbounded
face and the remaining page is strictly inside that simple four-cycle.
The weak physical contacts have already been resolved in the single
compatible embedding; the five actual graph vertices remain distinct.

If the inner page is B or J, its preserved access to infinity is
impossible. Removing other graph edges cannot destroy that access.

If the inner page is A, the bounding ring is the actual original
positive H-B-K-J-H. The original AU edge has both endpoints distinct
from ring vertices and cannot cross that ring. Since A is strictly
inside, U must be inside as well. That contradicts the original
physical boundary U's protected exterior access. The positive HK
chord may be restored throughout: it is omitted only when restricting
the complete embedding to the theta for its face argument, and no
equation or degree is changed.

These three alternatives exhaust all placements, including positive,
zero-length and side-tangent central gaps.

## 5. The full original mixed chains supply every premise

The intact A-U-V gives O in int A and the two true boundary tips.
The genuine K leaf cannot be D, nor S at d<=1, since each would put
O in the closed K. Thus it is S at d>1 and its unchanged inward
radial segment supplies k=epsilon*e in the actual K. The genuine
leaf-root theorem, or the boundary-point floor, gives K clearance.

For the precise nine-body mixed chain, the true boundary C is the
degree-two tip of A-H-C. The complete near-unit/common-boundary
theorem rules out any point of H in D_epsilon, using the actual
contacts A-C and H-C and the intact A. The other six named units
U,V,C,B,J,L are physical boundary, with every point of norm greater
than R-sqrt(2)>67/120>epsilon. These are all nine original units,
so only A,K can meet the entire closed central disk. All positive
applications at A,K lie on a different actual neighboring body
and therefore outside that disk. The graph has no AK edge.

The stronger alternative in Section 2.1 is also exact. I reread the
complete INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md.
Its two near units have no load, leaf, force, or graph-degree premise.
Once K supplies one actual near unit, every other physical square
different from A,K is disjoint from closed D_epsilon. This includes
an arbitrary ninth completion square. The full separating-axis and
quarter-square proof includes all disk tangencies. It therefore gives
the required free segment without a middle triangle or any assumption
about the force degree of H.

## 6. All four whole-domain joins retain the exact private loads

The complete accepted source
INTACT_PETAL_OPPOSITE_LEAF_C4_PRIVATE_LOAD_REDUCTION.md was reread.
Its hypotheses are true B2/J2, genuine K3 with its leaf, arbitrary
H, and an outside intact root. The one-transmitter cases use the
real near-K channel and the actual boundary detour. Its two-transmitter
case uses the full K leaf force and torque, the unchanged means, and
the genuine aligned rectangle winding; H is never assigned a smaller
equation. Thus it really forces both pages loaded in both C4 joins.

The exact original consequences checked are:

| Domain | Original higher degrees | Page-load justification |
| --- | --- | --- |
| C3.334.b1 opposite-leaf C4 | A4,H4,K3 | Entire accepted B2/J2 load reduction |
| C3.334.b1 other-hub-leaf diamond | A4,H5,K4 | Each true degree-two page has physically touching hub neighbors |
| C2.34.b2 direct bridge plus opposite C4 leaf | A3,H3,K3 | Same arbitrary-H/outside-intact load reduction |
| C2.34.b2 direct bridge plus other-hub diamond leaf | A3,H4,K4 | Same actual touching-hub obstruction at both true degree-two pages |

The mixed rows retain all nine stressed units. The two direct-bridge
rows retain their eight actual stressed units and the entire arbitrary
ninth square, which cannot block the free disk by the complete
two-near theorem. Both diamond chords remain in the graph and the
force equations. K4 here denotes true degree four, never a reduced
degree-three hub or a four-clique.

These are whole attachment exits, including every original page load
mask through the full load reduction, all physical corner masks,
every individual zero weight, and every original contact mean.
The three remaining mixed graph domains and all other b2 attachments
are correctly left outside the consequence.

The new argument is purely topological after its accepted actual
geometry and full-load inputs. No numerical pose, new certificate,
Lean compilation, CI, remote write, or shared-ledger change was used.

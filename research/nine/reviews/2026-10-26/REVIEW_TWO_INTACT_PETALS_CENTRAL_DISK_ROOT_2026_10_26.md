# Root review: two intact petals, the actual central disk, and the whole block tree

Date: October 26, 2026.

Reviewed the complete mathematical source
GLOBAL_CLOSURE_TWO_INTACT_PETALS_CENTRAL_DISK.md, including its original
scope and every conclusion. Direct dependencies inspected in full or at
the complete invoked sections: ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md;
GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md,
Sections 1--4; GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md;
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md; and the original
coarse rows in CYCLIC_CELL_LEDGER.md.

## 1. New local conclusion

The old common-root source supplied the common-side heights
1/5<P<39/40, genuine strict port straddling, one petal per side,
and the boundary-contact norm lower bound. Its small-port contradiction
did not use the existence of a bridge after identifying a side of
height at most epsilon. The new source correctly applies that same
geometric argument to any side whose distance from O is at most
epsilon, with no bridge premise.

O is already in the open interior of H. If the closed D_epsilon is
not contained in int H, a side height sigma<=epsilon exists, including
the equality endpoint. The side and its opposite are excluded as petal
sides by the strict 1/5 and 39/40 bounds. Both petals must therefore
occupy the two perpendicular sides, since the one-petal-per-side theorem
is stated at arbitrary full root degree. Their actual ports with
positive transverse coordinate have magnitude at most epsilon. Each
side height P consequently satisfies

    P^2>(67/120)^2-(1/60)^2=299/960>1/4.

The two opposite heights cannot both exceed 1/2. The argument proves
closed-disk containment in the OPEN interior, which is the strictness
required in the later overlap arguments. For epsilon=0 it uses the
already accepted origin-interior theorem directly.

## 2. Every other actual root and every bridge-only internal body

The genuine S/D leaf geometry supplies a point in D_epsilon at each
leaf root. Such a point in int H is impossible for any other actual
unit, even if it is only a boundary point of that other unit. This
is the correct interior-overlap argument; mere disjointness of closed
squares is not assumed.

The loaded all-bridge articulation split and the off-origin transmitter
theorem apply at the retained common minimal-support selection. An
internal bridge-only body is either a loaded articulation, already
excluded, or truly unloaded. O in int H makes a different such body
off-origin. Its original positive inward application has norm at most
epsilon, contradicting the new disk conclusion. No force is deleted
to obtain its degree-two equation.

## 3. Complete incidence-tree argument

The source concerns an entire component whose cyclic blocks are all
triangles, with arbitrary bridge blocks. Root its block-cut tree at H.
A terminal triangle has two private vertices of true positive degree
two, hence is an intact petal with an origin-containing root. That
root must be H. A terminal bridge has a genuine leaf endpoint and its
other endpoint must likewise be H. An incidence-tree branch extending
beyond an articulation different from H has a terminal block descendant
whose root differs from H; this is impossible. Thus every block is
incident to H. A finite chain or a decorated tip has not been omitted.

The final H equation is the complete equation of all its petals and
direct leaves. H is physically circle-clear because it contains O and
R>sqrt(2). Every retained branch has strictly positive scalar product
with the actual c_H, by the accepted petal pressure or exact S/D leaf
support. The sum cannot be zero. No effective leaf replaces a triangle.

## 4. Acceptance and precise accounting

Accept the complete local disk theorem and the exclusion of every
all-triangle/bridge component containing two intact petals. Distinct
intact roots were already impossible by origin-interior overlap; the
new conclusion handles a common root with arbitrary other decorations.

The source correctly leaves every whole C2.33.b2/b3/b4 and
C3.333.b1/b2 coarse cell open until its exactly-one-intact and no-intact
families also have complete exits. No original fine label is added or
changed by this review. The common canonical/minimum-support scope,
all nine squares, actual degrees, physical masks, individual zero
weights and original contact means are retained. This review does not
claim the older full prerequisite-chain audit or Lean integration is
complete. No numerical certificate, Lean compilation or CI was used.

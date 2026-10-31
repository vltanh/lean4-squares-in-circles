# Full root review: D leaf, boundary path and short hub faces

Date: October 26, 2026.
Source: D_LEAF_BOUNDARY_PATH_SHORT_FACES_EXCLUSION.md.
Reviewer: root proof worker.

**Verdict: accepted at the complete stated original scope.** The independent
hexagon review is separately recorded in
REVIEW_D_LEAF_BOUNDARY_PATH_SHORT_FACES_HEXAGON_2026_10_26.md.

The original component has a physical boundary path, endpoint hub spokes,
any retained internal spokes whose consecutive indices differ by at most
two, and genuine direct leaves including a D leaf. Every original force
and every physical unit is retained. The direct eight-boundary exit
reduces the geometric argument to at most six path bodies. Thus the
physical seven-cycle exception does not enter the boundary-path order.

The D leaf gives O in int H, r>1/2, s>1/3 and r^2-s^2>1/16.
The unchanged endpoint torque equations give the first strictly positive
and last strictly negative origin moments. These signs require neither
positive endpoint circle weight nor a concurrence construction. Internal
path vertices keep their genuine degree two or three. Their missing
spokes are not inserted and their actual spokes are not deleted.

I checked the complete shallow-side cover. At a<=1/4 every other genuine
leaf points strictly downward. If no spoke pointed upward, the full
root force equation would leave only horizontal spokes and the original
east D leaf. The first-normal lifts 0, pi and 2pi are all excluded by
the two actual endpoint moments or the full east force. The first
application is consequently on the northeast or positive-x top part,
with x>1/3. Normal order and the first-positive/last-negative moment
signs prohibit the last application there. The whole complementary
arc through the genuine D-leaf point then stays strictly outside
D_(1/4). Reflection covers the other shallow side. If neither side
is shallow, the original H directly contains a larger quarter disk.

The coincident-application cases are covered. At a vertex containing O
on its inner side, d/dtheta det(p,n(theta))=p.n(theta)>0 throughout
the outward normal cone. This prevents first-positive/last-negative
moments at one ordered vertex even when k=2. The genuine leaf point
cannot belong to another square because the two remaining tangent
sectors have angle pi/4. Gap-facing intersection extremes therefore
retain a nontrivial arc through that point.

The occupied closing barrier uses those actual contact extremes,
endpoint interiors and the circle arc. It has the strict quarter-disk
margin, while O in int H fixes its winding as zero about O. No auxiliary
force triangle replaces the physical barrier. Triangular faces are
empty, and each possible four-face contains three actual boundary
bodies and is empty by the accepted exact four-ring equality theorem.
All boundary-pair pockets are empty as well. The complete weak-contact
face allocation therefore puts every remaining physical unit in the
closing pocket. Exactly eight actual nonhub units receive disjoint
open radius-5/4 arcs of length greater than pi/4.

The house caller uses H=A, the actual path T,D,C,B and spokes at
indices 1,2,4. Its original inner faces are ATD and ADCB. The genuine
degree-three D keeps all its forces; no AC spoke is introduced.
The D leaf and three arbitrary completion squares stay present.
Thus the exact original gate M6.B5L.HOUSE.HUB.LTDCB.D closes. Its S
alternative, other load families and parent remain open. Same-root
C4 SD/DD consequences repeat already closed gates and are not counted.

The proof retains the accepted same-nine R<=2 arithmetic dependency.
It introduces no new numerical certificate. No Lean compilation, CI,
workflow dispatch or merge was performed.


# Five unrestricted core and ring cases for eleven squares

Let eleven independently oriented unit squares have disjoint open interiors
and lie in a disk centered at zero with squared radius `q<=U=49013/10000<5`.
Set

    r1 = (sqrt(7)+1-sqrt(2))/2,
    rho = sqrt(2),
    gamma = 2 asin(1/(2 sqrt(2))).

Call a square a core square when its center has norm strictly less than `r1`,
and a ring square otherwise. This is a classification by center position,
not by containment of the origin or of the whole square in an inner disk.

**Theorem.** Exactly one of the five cardinality pairs below applies:

| Core squares | Ring squares |
| ---: | ---: |
| 3 | 8 |
| 4 | 7 |
| 5 | 6 |
| 6 | 5 |
| 7 | 4 |

Every core square is strictly inside the containing disk and has no circle
contact. Every ring square meets the auxiliary circle of radius `rho` in a
connected arc of angular length at least `gamma`; its center ray lies in the
interior of that arc. Consequently the ring centers have a genuine cyclic
order inherited from pairwise interior-disjoint arcs. All eleven physical
squares and all 55 nonoverlap pairs remain in each case.

The five cases are exhaustive necessary geometric classes. Their sharp
terminal inequalities remain open; the theorem does not assert that every
listed cardinality pair is realizable below the candidate radius.

## 1. At least three core centers

The refined arc lemma in
[ARC_CORE_RADIUS_REFINEMENT.md](boundary/ARC_CORE_RADIUS_REFINEMENT.md), using
[ANNULAR_ARC_THREE_INNER.md](boundary/ANNULAR_ARC_THREE_INNER.md), proves that
every square with center norm at least `r1` contributes at least `gamma` to
the angular measure occupied on the radius-`rho` circle. Square boundaries
intersect the circle in finitely many points. The open square intersections
are disjoint and have total measure at most `2pi`.

Since `9gamma>63/10>44/7>2pi`, there are at most eight ring squares. There
are therefore at least three core squares, including all weak threshold
cases on the ring side.

## 2. At most seven core centers

We prove an elementary point-packing fact: a set of points of pairwise
Euclidean distance at least one in a disk of radius `9/8` has at most seven
points. Unit-square centers have this distance property because their open
radius-`1/2` inscribed disks are disjoint.

At most one point has norm strictly less than `1/2`. For the others, let
`r,s` be their norms, so `1/2<=r,s<=9/8`, and let `delta` be their smaller
angular separation. The cosine rule gives

    cos(delta) <= (r^2+s^2-1)/(2rs).

For fixed `s`, the derivative in `r` changes sign at most once, from negative
to positive, so this expression has no strict interior maximum. Applying the
same argument in `s`, its maximum on the rectangle is at a corner. The three
corner values are

    -1,       11/24,       49/81.

Hence `delta>=2 asin(4/9)`. Moreover

    asin(4/9) >= 4/9 + (4/9)^3/6 = 1004/2187 > 9/20,

so every such angular separation exceeds `9/10`. The arcsine estimate follows
by integrating `(1-t^2)^(-1/2)>=1+t^2/2` for `0<=t<1`; squaring positive
quantities proves the integrand inequality directly. If there were seven
annular points, their cyclic consecutive gaps would each exceed `9/10`,
including a directed gap larger than `pi` if present. Their sum would exceed
`63/10>2pi`, a contradiction. There are at most six annular points and one
inner point, proving the seven-point bound.

Finally `sqrt(7)<53/20` and `sqrt(2)>7/5` give `r1<9/8`. Therefore at most
seven unit-square centers can lie in the core disk. Combining with Section 1
gives precisely the five cardinality alternatives above.

## 3. Every core square is circle-unloaded

Area gives `11<=pi*q`, because eleven unit square interiors are disjoint
inside the disk. The strict bound `pi<22/7` implies

    q >= 11/pi > 7/2.

For any core square with center `p`, every one of its points has norm at most
`||p||+sqrt(2)/2`. Thus every point has norm strictly less than

    r1+sqrt(2)/2 = (sqrt(7)+1)/2.

The square of this last radius is

    2+sqrt(7)/2 < 7/2 < q.

Every core square is therefore strictly contained in the disk, including all
four vertices. In a nonnegative stress formed from active circle constraints,
all circle weights on core squares must be zero. This is a geometric
conclusion, independent of the existence or choice of a stress.

The area argument concerns the original eleven-square packing, not a reduced
contact subsystem from which squares have been removed.

## 4. A genuine cyclic ring and retained angular data

The unconditional center bound is

    ||p|| <= C(5) = (sqrt(19)-1)/2.

Every ring center satisfies `r1<=||p||<=C(5)`. Since `r1>1` and
`rho-1/2<1`, while `C(5)<rho+1/2`, it follows that

    | ||p||-rho | < 1/2.

Consequently the point `rho*p/||p||` on the center ray belongs to the square's
open inscribed radius-`1/2` disk, and hence to its open interior. It is in the
interior of the connected auxiliary-circle arc supplied by the refined lemma.

The arcs from different ring squares have disjoint relative interiors. Their
center-ray points are therefore distinct, and sorting their center arguments
produces a cyclic order agreeing with the order of the arcs. This is a
geometric ordering theorem; it does not come from a drawing of the candidate.

Write the lifted center arguments as `beta_i`, and the corresponding arc as

    [beta_i-l_i, beta_i+r_i],       l_i>0, r_i>0,
    l_i+r_i>=gamma.

Use consistent real lifts on each arc and lift cyclic indices by `2pi`.
Pairwise disjoint arc interiors give the necessary neighbor inequalities

    beta_(i+1)-beta_i >= r_i+l_(i+1),
    sum_i (beta_(i+1)-beta_i) = 2pi.

The endpoints and lengths have explicit side/corner formulas in the two arc
notes. Boundary equalities are retained. No step moves a center, changes a
frame, or drops the nonneighbor ring pairs or the core-to-ring pairs.

## 5. Finite signatures and remaining obligations

Each physical packing determines one of the five count rows, a set of core
labels, the cyclic order of its ring labels, and actual own-axis separator
data for all 55 pairs. A relabeling can assign the ring labels first in cyclic
order and the core labels afterward. Its inverse must be retained for a final
equality statement; reflections reverse the cyclic order and are distinct
unless separately identified by an allowed congruence.

The center threshold gives a disjoint bookkeeping partition (`<r1` versus
`>=r1`). For compact minimizer arguments one may instead use overlapping
closed core conditions `<=r1` and ring conditions `>=r1`. The same upper and
lower count bounds hold for that closed cover, the core noncontact conclusion
remains strict by the area margin, and the auxiliary-circle formulas include
threshold equalities. This avoids losing limits at the threshold.

For each row the unresolved terminal problem retains the complete core
positions and frames, the complete ring arcs and frames, all pair separators,
and every possible physical contact completion. Cardinality and cyclic order
alone do not imply global nonoverlap or a sharp radius bound. A circle-loaded
stress core can use only the ring bodies for its circle contacts, but may
transmit forces through core bodies with zero circle weights or leave some
core bodies entirely unstressed. These alternatives must remain explicit.

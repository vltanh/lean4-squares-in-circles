# Independent review of the five core and ring cases

Reviewed on 2026-10-23 at 13:25 UTC. The three notes below establish an
unrestricted necessary classification into five core/ring cardinality cases.
They do not supply sharp terminal bounds or capture the candidate family.

| Source | SHA-256 at review |
| --- | --- |
| `boundary/ANNULAR_ARC_THREE_INNER.md` | `7faa1838ba0be7433ce24e281ad2af1a2dbb00e283c75bb7620f49a0ff9f48d3` |
| `boundary/ARC_CORE_RADIUS_REFINEMENT.md` | `3b70a4505367d934f1a0837b75cb60b585f1c3f178bc74dd60afcb9cb78f542d` |
| `CORE_RING_FIVE_CASES.md` | `f7b112d5c668fd1b598796c8869bd4068754e7cd9e467241d931466111ec48e9` |

Two independent mathematical passes checked the following operations.

- The initial own-frame arc calculation includes negative secondary
  coordinates, both upper-endpoint branches, side tangencies, and the
  strictly internal near-corner bound `6-sqrt(19)<2`.
- Increasing the primary coordinate to the far-corner boundary preserves
  the domain required by the comparison. The exact derivative factorization
  is `(x-y)*((x+y)^2+1)`. The strict comparison with the target arc reduces
  to the integer inequality `4480<4489`.
- In the refined threshold's extra far-primary-side branch, the secondary
  near coordinate is positive. The intersection is one interval whose
  length is the minimum of all four endpoint differences. The derivative
  factorization for the new far/far difference is
  `(a-b)*[(7/4-r^2)*(a+b)-((a+b)^2+r^2)/2]`. Its sign and the diagonal
  endpoint give the claimed arc lower bound without sampling.
- Boundary-circle intersections are finite, so replacing closed squares
  by open interiors preserves angular measure. Nine qualifying arcs exceed
  `2pi`, proving at least three core centers with every weak threshold case
  accounted for.
- The independent point-packing bound maximizes the cosine-rule expression
  over `[1/2,9/8]^2`. Its corner values are `-1`, `11/24`, and `49/81`.
  The exact arcsine comparison `1004/2187>9/20` excludes seven annular
  centers, and at most one further center lies strictly inside radius
  `1/2`. Since the refined radius is less than `9/8`, there are at most
  seven core centers.
- The area bound `q>7/2` and core vertex bound
  `2+sqrt(7)/2<7/2` prove that every core square is circle-unloaded.
- Every ring center's radial point on the auxiliary circle is within
  distance strictly less than `1/2` of its center. It is therefore in the
  square's open interior. This supplies the claimed cyclic order and
  neighbor arc-gap inequalities, including touching endpoints.
- Overlapping closed threshold classes retain all five count bounds and
  the strict circle-unloaded conclusion, so compactness limits are not
  silently lost.

No gap was found. The resulting rows are exactly `(core,ring)=(3,8),(4,7),
(5,6),(6,5),(7,4)` as necessary alternatives, with all eleven squares and all
55 pair constraints retained. No row is claimed physically realizable or
excluded at the candidate radius. No center deformation, common frame,
origin-containing square, omitted completion, or Lean verification enters
this review.

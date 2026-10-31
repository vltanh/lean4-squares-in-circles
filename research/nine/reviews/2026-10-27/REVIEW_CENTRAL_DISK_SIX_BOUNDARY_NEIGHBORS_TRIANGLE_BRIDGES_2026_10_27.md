# Independent full review: central disk and six boundary neighbors

Date: October 27, 2026.

Reviewer: triangle_bridges, independently of the source author and root.

**Verdict: PASS for both complete geometric theorems and all three stated
original C3.335 bouquet consequences.** No mathematical or scope correction
is required. This review does not close the other ten graph domains or the
whole C3.335.b0 cell.

Reviewed source:

`NINE_SQUARE_CENTRAL_DISK_AND_SIX_BOUNDARY_NEIGHBORS_EXCLUSION.md`

SHA-256:

`b270c64641ae3299e8b471084b807fc44f2ef2a5e6ff1a8621826ddbd2f1d4e5`.

## 1. Full source and direct scope audit

I read the entire new source, independently checked its analytic cover and
each geometric join, and read the complete direct sources
`CENTERED_INNER_ARC.md`, `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`,
`TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md`,
`NO_UNLOADED_DIAMOND_HUB.md`, and
`MIXED_C3_335_COMPLETE_ATTACHMENT_REMAINDER.md`.

The first two new theorems are physical statements for the same nine units
and assume 2<=R<=sqrt(1105)/16. They do not use a selected stress, a positive
circle multiplier, a contact graph, or a complete classification of the
other eight units. The original-window application correctly retains the
accepted same-nine R>2 theorem and its current five-charge certificate.
It does not relabel that inherited certificate as table-free or discharge
the separate global prerequisite audit.

## 2. Complete angular-measure bound

The own-frame normalization a>=b>=1/2 and a^2+b^2<=R^2 covers all
orientations and positions of every actual contained square. The nearest
point is (max(a-1,0),max(b-1,0)); hence the closed distance premise is
retained exactly.

For a>r, I checked the bound A<=d<R-53/50, the inner-corner reserve, and
the fixed-q convex expression for E_0. Its full parameter interval has
the two stated endpoints b=1/2 and a=b. Enlarging to either endpoint is
legitimate even if that endpoint is outside the original distance region.
The original a>r inequality still gives the lower bound on q needed in
both endpoint estimates. Both v<=1 and v>=1 branches have strict reserves.

The resulting E_0<r^2/2 is exactly equivalent to
(sqrt(2)A+B)^2<r^2-B^2. The subsequent unsquared comparison remains valid
when sqrt(2)A+B is negative. Since |beta|<pi/4, the cosine comparison uses
its correct monotone interval. The actual closed intersection is the
displayed single interval, and both candidate upper endpoints give an
angle greater than pi/4. The b>r cap and b=r endpoint are included.

For a<=r, B<=0 forces A=h and a=r. The entire positive-x strip is inside
the inner x bound; deleting the possible isolated point (r,0) from the
open square has zero angular measure. This is why the source properly
states a measure conclusion rather than unnecessary connectedness.

For B>0, I independently expanded the fixed-k derivative comparison.
After multiplying the positive denominators, its sign is exactly the
sign of

    (A-B)[(A+B-h)^2+(k^2-h^2)(A+B+1)].

The comparison path from A=B=k/sqrt(2) to the actual pair remains in
0<B<=A<=h, with the same k>=h. Its sign is nonnegative throughout.
Continuity includes A=h and its infinite arcsine derivative. The four
upper-minus-lower endpoint differences in the circle intersection are
exhaustive; the outer-outer comparison retains k=h and has the stated
strict final reserve (16-9sqrt(2))/100>0. Thus every equality and face
tangency allowed by dist(O,S)>=h is covered.

## 3. Central disk and six-neighbor consequences

If one actual unit contains closed D_h, every other closed unit has
distance at least h, because any point of smaller norm can be approached
by its interior points inside the first unit. The eight pairwise disjoint
open-interior circle sets then each have measure greater than pi/4.
Additivity on one circle gives the contradiction without any assumption
about their connectedness or their boundaries.

The center consequence |c|>1/2-h includes equality: if |c| were at most
that value, both own-coordinate offsets would be small enough that all
four side distances from O were at least h.

For every physical boundary neighbor B, the common actual contact gives
|b-c|<=sqrt(2), while an actual radius-R corner gives
|b|>=R-1/sqrt(2)>R-71/100. The positive-variable monotonicity used with
F(R) is valid because t>13/50. I checked the complete derivative and
strictness chain leading to cos(angle)>-1/6. The triple-angle proof of
arccos(-1/6)<100 degrees is valid and does not introduce an approximate
trigonometric assumption.

I read the full centered-inner-arc proof, including its own-frame cubic
reserve. Its strict minor separation greater than 40 degrees applies to
all physical boundary bodies, regardless of their circle weights. Six
neighbor directions in the displayed open arc shorter than 200 degrees
have five consecutive differences greater than 40 degrees. This remains
valid if the enclosing interval is longer than a semicircle: every raw
consecutive difference is at least its minor separation. The resulting
strict span contradiction is complete.

## 4. All original graph and load joins

The two intact petals provide four distinct true degree-two loaded tips,
without changing the full equation at H. In the C5 bouquet both immediate
cycle neighbors remain true degree two and the complete two-petal channel
theorem forces their loads. In the house-hub bouquet the roof is a true
triangle tip and the lower neighbor is a true degree-two neighbor of the
two-petal root. In the fan-inner bouquet the endpoint is a true triangle
tip, while the next inner vertex retains exactly three positive neighbors
with two actual physical edges among those neighbors. The full unchanged-
degree diamond-hub theorem therefore forces its load; no degree-three
statement is applied to the higher-degree root.

All six boundary neighbors in each row are different actual units. Their
physical contacts with H and the containing circle suffice for the new
theorem. Every remaining private load mask, all positive chords, original
normals, side means, and the ninth physical square are retained.

The accepted thirteen-domain finite graph cover consequently loses exactly
C5, house-hub, and fan-inner bouquets. The previously excluded fan-hub
bouquet is not counted again. The three other bouquets and seven chains
remain, as the source states.

## 5. Independent exact arithmetic

A separate Python standard-library Fraction calculation checked these
displayed exact quantities directly:

| Comparison | Exact result |
| --- | --- |
| Inner-corner reserve at R=2 | 109/2000 |
| Quadratic endpoint at D=61/60 | 2059/3600 |
| Angular quadratic reserve | 3979/180000 |
| Lower radical squared reserve | 231/1000000 |
| Upper radical squared reserve | 179/218750 |
| Linear radical reserve at R=25/12 | 3/1000 |
| F(2) | 17/2000 |
| F'(2) | 7/15 |
| F'' | 182/25 |

The monotonicity arguments and strict upper radius bound turn these endpoint
computations into the whole stated interval estimates. These calculations
check displayed identities; they are not a pose enumeration or a new
parameter certificate. No Lean compilation, CI, remote mutation, source
edit, central status edit, or original gate-count change was performed.

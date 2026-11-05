# Root review of universal physical rows and exact assembly reuse

This review accepts the physical implications and independent literal decoders
in three published row families. It also accepts an optimization that assembles
the same exact area-moment rows under the stated discovery API contract. The
source snapshot is commit `600818c19a54f124aedbb67db7cc5044ba68ee0b`; all 36
input files, including the saved weighted examples, are bound by size and
SHA-256 in `SOURCE_BINDING.json`. The review adds no original or mask closure.

## Incircle separation

Two distinct original unit squares with disjoint open interiors have disjoint
open inscribed disks of radius 1/2. Consequently the distance between their
original centers is at least 1, independent of their frames, mask or containing
circle. Write the same-pair signed coordinate as `d >= 0`, and its transverse
coordinate as `t` in the certified closed interval `[L,U]` within `[-1,1]`.

For rational nonnegative endpoint heights `a,b` satisfying
`a²+L² <= 1` and `b²+U² <= 1`, the linearly interpolated height `ell(t)`
satisfies `ell(t)²+t² <= 1`. The exact expansion in the source hand proof
retains both endpoints and subtracts the nonnegative squared difference of
the two endpoint vectors. Thus `d² >= ell(t)²`, and nonnegativity gives
`d >= ell(t)`. The decoder checks the original pair, axis and sign, both
endpoint inequalities, the enclosing transverse interval and every printed
coefficient. In the accepted difference convention the pair interval is for
`center[j] - center[i]`; the printed signs agree with that convention.

The fresh unchanged control program passes 440 exact unit-distance cases and
rejects 96 damaged literals or unproved state guards. This is a universal row
family review. It does not reconstruct a complete original's state ancestry.

## Supports from all four original corners

Let `S,T` be the absolute center coordinates in an original orthonormal square
frame. The maximum of its four squared corner norms gives
`S²+T²+S+T <= 977/256` at squared circle radius `1105/256`.
Completing two squares, for any rational `r >= s >= 0`, gives

`(2r+1)S + (2s+1)T <= 977/256 + r²+s²`.

For a fixed world direction, the decoder verifies that one signed frame
projection is strictly positive and that the other projection's absolute
value is at most `(2s+1)/(2r+1)` times it. After division by the original
positive `alpha`, these are affine inequalities in the certified slope.
Their checks at both closed endpoints prove them throughout the interval.
Multiplying the completed-square inequality by that positive projection
then gives the printed affine inequality in original `x,y,alpha,beta`.
The other major axis and both signs follow by the same explicit formulas.
No selected SAT direction, marked edge or replacement square is introduced.

The narrow family is the exact specialization `r=91/60, s=0`. Its fresh
packet replay checks 328 literals and 15 rejection controls. The general
family checks 5,220 literals, 17 literal/guard rejections and three weighted
arithmetic rejections. Both freshly replay a saved actual weighted excerpt,
including rational residual correction and outward rounding. Each excerpt
has one positively weighted new cone row.

Those excerpts are conditional on their other printed rows and supplied
absolute bounds. Their complete older-row provenance and original ancestry
are explicitly outside this packet. Integration requires a separately frozen
runtime adapter, independently propagated same-owner angles and same-pair
intervals, a fresh complete arithmetic replay, and the full parent/path/cover
checks. Existing numerical processes are unchanged by this review.

## Exact area-moment assembly

The optimized discovery generator precomputes each pair/matrix contribution
and sums those exact rational contributions over the same original subsets.
The lower bound, row name, coefficients and enumeration order are unchanged.
All 6,144 rows across the two supplied interval inputs matched literally in
a fresh comparison. The recorded generator times were about 4.1–4.8 seconds
for the reference and 0.51–0.54 seconds for the optimized version. These are
generator measurements, not a claimed speedup for the entire proof search.

The accepted API contract supplies all 36 exact immutable pair intervals,
finite stable sequences of subset sizes and matrices, and frozen `lower_bound`,
`name` and `axes_matrices` functions after installation. A one-shot matrix
iterator or later mutation of those functions is outside this comparison.
The cache key includes the full interval state, ordered matrices and subset
sizes; its internal pair cache is not exposed to callers. The independent
certificate checker continues to reconstruct the original rows unchanged.

## Scope and execution

All four fresh commands were observed to exit zero using Python `-B -S`.
No Lean, Lake or CI was run. The current register remains 222/231 original
cells CLOSED, nine OPEN, and eight of 32 masks CLOSED, 24 OPEN. The nine
originals, their 36 corners and 36 physical pairs, the five original cones
and every exact mask bit remain in force.

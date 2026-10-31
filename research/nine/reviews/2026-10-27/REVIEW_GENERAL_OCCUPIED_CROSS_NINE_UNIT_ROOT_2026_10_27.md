# Root full review: every occupied cross has total capacity at most eight

Date: October 27, 2026.

**Verdict: ACCEPT both complete uniform geometric sources below.**
I read both sources in full, reconstructed every continuous-orientation
polynomial and all sixty displayed rational Bernstein coefficients, and
checked the original physical-ring and restricted K2,3 embedding joins.
This accepts their entire stated domains, not a boundary-loaded special
case. The frozen mathematical pins precede acceptance-only header edits.

| Source | Reviewed mathematical SHA-256 |
| --- | --- |
| GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md | `c3e0979e5baacda8a117572ad9e337b0ec4e21a56bbcf9bb25f7af33481e92a5` |
| CHORDED_HEXAGON_OCCUPIED_CROSS_OPPOSITE_QUADRANT_EMPTY.md | `c824dd96ba8b9505de653248b9bd99bbf429eb706f84f5288d58657db6f9abf7` |

The main source has the separate full independent ACCEPT in
REVIEW_GENERAL_OCCUPIED_CROSS_NINE_UNIT_GLOBAL_2026_10_27.md. Its
opposite-quadrant dependency has the separate full independent ACCEPT in
REVIEW_OCCUPIED_CROSS_OPPOSITE_QUADRANT_ROOTED_BLOCKS_2026_10_27.md.

## 1. Entire physical and orientation domain

The theorem assumes only the five actual aligned cross units, actual
interior nonoverlap, and containment in one actual disk with
R^2<=Q=1105/256. The disk center is allowed to move relative to the
cross; no boundary contact, positive load, force, normal, degree or
equilibrium equation is assumed. Every extra unit has its own arbitrary
frame. The argument counts the actual full packing.

The exact farthest-cross-vertex expression gives both disk-center
coordinates strictly below 31/60 in absolute value. The universal
farthest-corner formula bounds every actual unit center's distance from
that disk center by M=91/60. Both strict reserves are 31/57600.
These are orientation-independent bounds.

For an actual cross vertex and two actual corners of an extra unit, the
three nonnegative weights in Section 1 sum to one. Their weighted
variance is at most R^2 because all three points are in the same actual
disk. Expansion gives (4); taking the larger of the two signed choices
gives (5). This is a geometric point identity, and changes no physical
force or circle weight. Its separate coordinate derivatives remain
positive throughout X,Y>=1, including the absolute-value junction by
continuity. The signed expression used for the vertical-separation
case is likewise monotone.

I checked the full separating-axis cover for both solid cross rectangles.
Every mixed-sign own separator implies an ordinary cross-axis separator
by the displayed exact nonnegative difference. The remaining own normal
has both coordinates positive. Aligned endpoints are already included
in the cross-axis cases. The chosen own axes therefore represent every
actual orientation; no favorable frame has been selected.

## 2. One unit in each entire corner region

A corner center has both coordinates above 1/2 after actual whole-plane
reflections. A coordinate at least two gives a point-to-square farthest
corner distance greater than the diameter of the original disk. This
argument also supplies the weak endpoint evaluations used later.

For the upper bound x<169/100, horizontal separation from the long
horizontal rectangle is impossible. Ordinary vertical separation gives
the three displayed full-interval polynomials after the rational circle
parameterization. In the own-axis case, reducing coordinatewise to
the support line is a lower-bound evaluation, not a movement of a
physical square. On that line the minimum occurs at the feasible W of
smallest absolute value. The three ranges a<=7/8, 7/8<=a<=99/100,
and a>=99/100 cover all remaining orientations. I checked the strict
monotonicity of a(3a+b+1/2) in the first, the concavity lower bound for
3a+b+1 in the middle, and the negative W endpoint in the last. The
last evaluation again has a coordinate at least two and is excluded
by the already proved point-to-square bound.

For the lower bound x>59/60, both ordinary separators from the vertical
rectangle are excluded. On the remaining support line, the entire
relaxed X interval is [1,89/60]. For a<=1/4 the closest W endpoint
again yields the diameter contradiction. For 1/4<=a<=5/12 concavity
gives the strict 33/8 bound and its exact equality threshold. For
a>=5/12, the full second-derivative calculation makes a(a+3b+1/2)
concave, with endpoint values at least 3/2>89/60. Thus W is negative
throughout the actual domain, and its smallest absolute value occurs
at the stated endpoint. The last polynomial is strictly positive on
the two full closed intervals. Interchanging coordinates gives both
bounds on y.

Consequently every corner center is in the strict rectangle
(59/60,169/100)^2 in its reflected coordinates. Its squared diameter
is 5618/5625<1. The actual open half-unit incircles show that centers
of two distinct interior-disjoint units are at least one apart. Hence
each entire corner region has capacity at most one.

## 3. Independent exact polynomial verification

Using rational polynomial arithmetic, I rederived the numerator
polynomials directly from the point-variance expressions (10), (15)
and (21), rather than checking only the printed coefficient lists.
I then substituted each stated closed interval and independently
computed every Bernstein coefficient using (28). All sixty equal
the displayed rational values exactly and are strictly positive.

| Appendix interval | Number of coefficients | Smallest exact coefficient |
| --- | --- | --- |
| A.1 | 5 | 988312739619/1600000000 |
| A.2 | 5 | 796616506019/1600000000 |
| A.3 | 5 | 1331980044/390625 |
| A.4 | 9 | 511875/256 |
| A.5 | 9 | 191590420929/2560000000 |
| A.6 | 9 | 1950420590659/25600000000 |
| A.7 | 9 | 178559059/390625 |
| A.8 | 9 | 64 |

The nonnegative Bernstein basis sums to one, so these exact identities
prove strict positivity at every parameter in each interval, including
the joins. They are not sampled orientations. The rational denominators
are positive on their actual domains; the harmless z=1 polynomial
endpoint is never substituted into a zero denominator.

Additional exact checks give 347/20-4Q=27/320,
1731/400-Q=71/6400, (33/8)^2+1/4-4Q=0,
2(29/60)^2+4(29/60)+5/2-Q=33647/57600,
M^2-(89/60)^2=1/10, and 533/225-M^2=247/3600.
These checks confirm the stated strict thresholds; they do not replace
the interval and geometric arguments.

## 4. Opposite quadrant and every possible axial extra

I checked the dependency's complete opposite-quadrant proof separately.
Reflection makes the extra center nonnegative and the actual circle
center nonpositive. The incircle and center bounds first force both
extra-center coordinates into [1,3/2), so every extra-square point is
positive and also lies in the disk of radius sqrt(Q) about the cross
center. The full SAT cover reduces to an ordinary upper separation
and either a right separation or one northeast own separator. Two
ordinary separators require radius squared at least 9/2. In the
remaining own case, s<1/2, the true own coordinates U,W are positive,
and the complete quadratic lower bound is increasing from U0 onward.
Its endpoint again requires at least 9/2>Q. This includes all weak
contacts, tilt signs, aligned endpoints and circle-center axis cases.
Thus at least one entire corner quadrant is empty.

If any extra center lies in an axial region, say north with y>=2,
the actual circle center has v>29/60. South is immediately impossible,
and another axial direction violates the exact cross-radius formula.
All north centers lie in one rectangle of squared diameter 401/900<1,
so that whole region holds at most one. Both southern corner regions
violate the center bound by the strict 247/3600 reserve. At most one
unit remains in each northern corner. If no axial region is occupied,
the empty-quadrant lemma and the corner bounds give the same total
of at most three extras. This exhausts all actual extra centers.

Therefore an actual occupied five-unit cross has total unit capacity
at most eight, with no physical boundary-arm assumption.

## 5. Exact four-ring and K2,3 consequences

I reread Sections 1--2 of FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md.
Their actual contact-polygon area inequality and full equality case
are independent of the boundary premise used only afterward. A whole
actual unit in a physical four-ring forces four distinct contact
vertices, four full inward side chords and the actual aligned cross.
The new theorem excludes that cross in a nine-unit packing. All weak
junctions are included by the already fixed physical routing, with
homotopies avoiding smaller concentric squares of the enclosed unit.

I also checked Section 1 of
GLOBAL_CLOSURE_SPANNING_K23_BOUNDARY_AND_TERMINAL_EXCLUSIONS.md.
Restricting the existing compatible physical plane embedding to the
six actual K2,3 edges leaves a biconnected graph whose outer face is
a four-cycle and whose fifth actual center is inside. This is a proof
restriction of one existing embedding; no physical force or square is
removed and no abstract replacement drawing is used. The same
four-ring equality gives the actual cross. Thus every such actual
positive K2,3 subgraph is impossible at arbitrary original degrees,
with every additional chord and force retained.

The precise consequence is empty whole-unit capacity in every actual
four-ring region and exclusion of actual K2,3 in the selected physical
embedding. Five-sided regions and arbitrary exterior completions still
need their own proofs. No original gate is closed merely by this
review. The unrestricted sharp bound and every original equality
packing remain separate open obligations. No Lean compilation, CI,
workflow or numerical pose search was run.

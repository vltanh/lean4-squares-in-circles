# Independent root review: pair-dependent capacity and large-block diagnostics

Date: October 30, 2026 UTC (October 29, America/Chicago).

**Verdict: PASS for the complete three sources at the exact scopes below.**
No source proves unrestricted n=9 optimality or closes an original coarse
cell. This review distinguishes a physical capacity theorem from exact
obstructions to proposed proof methods.

## Frozen sources

| Source | SHA256 |
| --- | --- |
| NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md | `33168fb5ab4605739746348d1425b47da33c6f2a64803357f1f0608515a160b8` |
| ALL_RADII_NINE_PROFILE_OBSTRUCTION_AND_PAIR_DEPENDENCE_2026_10_30.md | `001070964ef60f1ff93852fbee25ea45439f48757ed7a8d390a2968c5d557a3c` |
| LARGE_BLOCK_LONG_EAR_OBSTRUCTION_AND_SUBCRITICAL_SEVEN_CORE_2026_10_30.md | `c2206265e00022a2b3fab3523ea5dd9ed5e258d80c49baece4e6f10d4e352b16` |
| ADDITIVE_MEASURE_OBSTRUCTION.md (direct input to the radial diagnostic) | `29e07f1f8bd3ecfaaafc0db9ee5664e53c6624bfd4442fd2ff239c2a3308ebd8` |

## 1. Complete central-pair capacity theorem

I checked the whole theorem, including the actual rectangle premise and all
weak contact endpoints. The union of the two given units is the occupied
rectangle [s-1,s+1] times [h-1/2,h+1/2], with |s|,|h|<=1/12 and the original
disk origin unchanged. An extra unit's open interior avoids this rectangle;
the central seam cannot conceal an open intersection.

The rectangle contains the disk of radius delta=1/2-|h|. For an extra square
whose two absolute own-center coordinates are at most 1/2+delta, an own-axis
separator can only attain the rectangle's minimum support delta. Equality
forces a vertical normal. A horizontal rectangle separator would instead
force |c_x|>=17/12>sqrt(2), contradicting the own-coordinate cap. The exact
last squared reserve is 1/144. Thus every such extra is wholly above or below
the occupied rectangle, with clearance at least delta from the origin.

In the extra's actual own-frame chart the condition a>5/4 follows from that
clearance; otherwise its nearest-point norm would be at most sqrt(2)/4,
strictly below delta>=5/12. This makes the stated inner-circle intersection
one genuine connected arc. I checked both possible upper endpoints and the
strip-width lower bound 2 asin(2/5).

The remaining arc bound uses a convex quadratic in a+b at fixed a^2+b^2.
The enlarged endpoint b=1/2 is bounded strictly by 933/1600, and the diagonal
endpoint is bounded by the exact Q-dependent expression. The positive gap
between the latter lower comparison and 933/1600 is 843/8000. The two radical
comparisons for v have reserves 713/12800 and 223/12800. The conversion back
to the arc angle stays on the decreasing cosine branch, even when the
unsquared linear expression has either sign.

Finally I checked the complete delta interval [5/12,1/2], split only at the
exact value sqrt(Q/2)-1. Each of the two candidate arc lower bounds, after
tripling, strictly exceeds the available half-plane cap. The triple-angle
comparison has exact squared reserve 316/140625. Thus three qualifying
extras cannot occupy either side, and the total qualifying capacity is four.

All independently tilted completing squares satisfying the own-coordinate
condition are included. The theorem does not restrict the orientations of
the other extras, and it does not assert that the central pair can be
extracted from any particular positive graph.

## 2. Complete all-radii relaxation diagnostic

I checked the existing additive-measure source as well as the new corollary.
At q0=17/4, the individual square profiles A, S and B have the exact corner
radii stated. The old pointwise inequality with coefficients 2,2,101/20
immediately implies the new inequality with integral multiplicities 2,2,5,
because the B angular occupation is nonnegative at every radius.

This really does hold simultaneously at all concentric radii. It persists
under every nonnegative weighted integration of those inequalities. It also
has the required two near profiles and seven far, circle-touching profiles
at the circle of radius sqrt(q0). No simultaneous disjoint placement is
claimed. The distinction is essential: the two actual A units, if jointly
realized disjointly, have antipodal centers by the center-distance bound and
therefore create the occupied central rectangle. The first theorem then
rules out the five B units. This is a valid pair-dependent contradiction,
not a contradiction to the pointwise radial calculations.

## 3. Long ears and the exact seven-body core

The radius-free inequality k+1<=l sqrt(2) follows by summing all actual tight
projection gaps along the true unloaded-degree-two path and comparing with
any physical contact walk. The contact-walk bound uses actual common points
and the two square circumradii. It applies to zero-weight physical contacts
as well as selected positive ones. In particular k=2 forbids a return of at
most two physical edges, with strict squared reserve 9-8=1.

I reconstructed the seven aligned units and every listed stress row. All
pair interiors are disjoint, the four specified corners have squared norm
13/4, the circle weights sum to one, and every shared-side application is in
the relative interior of its true shared segment. At A and B the displayed
force and moment sums cancel exactly; reflection supplies C and D. Each
remaining body has two equal opposite forces on a common horizontal line.
The six-cycle plus the A--M--D ear is biconnected, and no two unloaded
degree-two vertices are consecutive.

The separate completion obstruction is valid for every possible orientation
of an eighth square. Its center would have norm between 1 and 91/60. In the
first quadrant the two stated x ranges force distance less than one from
U or D respectively, with exact reserves 307/1800 and 139/3600. Reflections
cover the other quadrants. Thus the fixed seven-square core cannot accept
even one extra in the target disk.

This counterexample is correctly limited: its stressed radius sqrt(13)/2
lies below 79/40. It disproves extraction from the bare graph, positivity
and equilibrium data; it does not disprove a theorem that also uses the
research lower window or an actual nine-square completion.

## 4. Verification and scope

The displayed rational identities were recomputed independently. No sampled
pose, optimizer, generated exclusion table, Lean build or CI result is a
premise. These accepted sources provide one conditional physical capacity
theorem and two precise route diagnostics. The arbitrary-stagger central-pair
extension and any later source need their own current-source reviews.

# Nine exact radial profiles pass every concentric-circle occupation budget below Q

Date: October 30, 2026 UTC.

**Status: exact consequence of the existing additive-measure obstruction,
submitted for independent review. This is a relaxation witness, not a
physical packing of nine disjoint squares. No original gate is closed.**

The purpose is to distinguish the missing angular coupling from the
number of auxiliary radii. Even the occupation budgets at **all radii
simultaneously**, with nine integral square profiles and the existing
two-near-unit count, do not imply the target bound.

## 1. The exact nine profiles

Put

    q0 = 17/4 < Q = 1105/256,
    a = sqrt(17/8), b = a-1,
    A = [0,1] x [-1/2,1/2],
    S = [1,2] x [-1/2,1/2],
    B = [b,a] x [b,a].

Every displayed object is an actual individual unit square contained in
the disk of squared radius q0. Their farthest squared corner norms are,
respectively, 5/4, 17/4 and 17/4. The nine-profile multiset is

    two copies of A, two copies of S, five copies of B.             (1)

A copy may be rotated arbitrarily about O without changing its radial
profile. No simultaneous choice of those rotations is supplied here.

Let ell_T(r) be the angular measure, in radians, of
`int(T) intersect {|x|=r}` for r>0, and set ell_T(0)=0. The value zero
at r=0 agrees with the origin's nonmembership in all three interiors.
The existing exact pointwise theorem in ADDITIVE_MEASURE_OBSTRUCTION.md
proves

    2 ell_A(r) + 2 ell_S(r) + (101/20) ell_B(r) <= 2*pi
    for every r>=0.                                               (2)

That source's complete hand proof uses the three exact angular
profiles, one increasing/decreasing split at sqrt(a^2+b^2), and two
explicit trigonometric comparisons; no angular mesh is a premise.
Since ell_B(r)>=0, (2) immediately gives

    2 ell_A(r) + 2 ell_S(r) + 5 ell_B(r) <= 2*pi
    for every r>=0.                                               (3)

Thus (1) passes every finite choice of concentric-circle occupation
tests and the entire continuous family of them. Every nonnegative
weighted combination or integral of these tests also holds, whenever
the integral exists, by integrating (3). The weights can depend on
radius; there is no restriction to one or two circles.

## 2. The central counts do not remove this witness

The three center norms and square clearances are exactly

| Profile | Center norm | Distance from O to the square |
| --- | --- | --- |
| A | 1/2 | 0 |
| S | 3/2 | 1 |
| B | sqrt(2)*(a-1/2) | sqrt(2)*(a-1) |

Since a>29/20, B has clearance greater than
`(7/5)*(9/20)=63/100>1/2`, and its center norm exceeds one.
Consequently the nine profiles have exactly two units at distance
less than any prescribed h in (0,1/2), exactly two centers of norm
less than one, and exactly seven profiles physically touching the
circle of radius sqrt(q0). Relative to the larger target disk D_sqrt(Q),
all nine individual profiles are physically circle-clear.
No profile contains a positive-radius disk about O. These counts
already satisfy the known two-near-unit and seven-far-unit necessary
conditions. They do not supply angular order or actual contacts.

## 3. What a successful annular argument must retain

This proves a specific insufficiency, not that annular geometry is
unusable. Any contradiction must introduce information absent from
(1)--(3), such as a common relative angular placement, actual
separators from the two near units, a pair-dependent occupation bound,
or a justified joint force/contact constraint. More radii alone do not
remove the witness.

For example the two A profiles, **if actually realized disjointly**,
have center distance at least one and both center norms 1/2. Equality
in the triangle inequality forces opposite centers. Their own radial
side axes therefore agree, and their physical union is, after one
common rotation, the rectangle [-1,1] x [-1/2,1/2]. This is genuine
pair geometry which the independent profiles discard. The companion
NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md
uses that information and allows a small displacement and arbitrary
orientations of every completing square.

Frozen direct source:

    ADDITIVE_MEASURE_OBSTRUCTION.md
    SHA256 29e07f1f8bd3ecfaaafc0db9ee5664e53c6624bfd4442fd2ff239c2a3308ebd8

No physical nine-square counterexample, radius theorem, original
coarse closure, Lean compilation, CI or publication is asserted.

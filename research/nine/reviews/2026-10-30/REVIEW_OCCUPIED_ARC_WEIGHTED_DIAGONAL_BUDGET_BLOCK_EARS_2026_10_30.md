# Occupied-arc weighted diagonal budget: complete independent review

Date: October 30, 2026 UTC.

**Verdict: PASS at the full stated scope. No repair requested.**

Reviewed frozen source:
`OCCUPIED_ARC_CHORD_BUDGET_ALLOWS_AT_MOST_ONE_DIAGONAL_IN_EVERY_SEVEN_CYCLE_2026_10_30.md`.

Length: 9,449 bytes. SHA256:
`dd6b92bf76b58869a93fa5ad5ab79142ffb74b4640dd5ee22d275ef170b08970`.

I read the entire source and reconstructed the directed-gap geometry,
the exact radical estimates, the complete physical-stress caller and
the simultaneous cycle consequences. I previously reconstructed the
full occupied-arc input, including connectedness of each actual inner
arc, compact interior trimming, marked-order compatibility and the
whole-component load caller. That independent review is recorded in
`REVIEW_OCCUPIED_INNER_ARCS_AND_SEVEN_BODY_CYCLE_BOUND_BLOCK_EARS_2026_10_30.md`.
The new weighted proof is reviewed here as a complete extension.

## 1. Actual arcs and directed gaps

The source explicitly uses the existing radius range
79/40<=R<=sqrt(1105/256). For each of t>=2 physical boundary units,
the frozen input supplies a compact actual radius-5/4 arc in the
unit's open interior, of length lambda_i>pi/4, retaining its center
and selected outer-corner directions. Distinct units' compact arcs
are disjoint because their open square interiors are disjoint.

The compatible actual cycle/spoke routing supplies their order when
the caller is a marked cycle. Extra positive edges at marked vertices
do not change the premise: the simultaneous physical routing remains
explicitly required. Abstract graph planarity is not substituted for
that geometric compatibility.

The directed intervening gaps delta_i and actual arc lengths partition
the same full circle, so their sum is 2pi. Each gap's endpoints are
actual points of its two neighboring squares. A set-distance lower
bound W_i thus gives a lower bound on their chord, namely
2rho sin(delta_i/2)>=W_i.

For 0<=delta_i<=2pi, the half-angle lies in [0,pi]. Consequently
sin(delta_i/2)>=u, for 0<=u<=1, implies
delta_i/2>=asin(u), including the branch above pi/2. The directed
gap is not identified with a minor angle; a gap exceeding pi is
handled by exactly the same inequality. If W_i>2rho the actual
chord condition is impossible before any inverse sine is used.

## 2. Exact strict chord costs

At rho=5/4, W=1 gives ratio 2/5. The comparison
sin(pi/8)^2=(2-sqrt(2))/4<4/25 follows from
sqrt(2)>7/5>34/25. Thus the gap is strictly greater than pi/4.

At W=sqrt(2), the ratio is 2sqrt(2)/5 and its square is 8/25.
The half-angle identity gives

    sin(3pi/16)^2=(2-sqrt(2-sqrt(2)))/4.

Positive squaring proves sqrt(2)<71/50. Therefore
2-sqrt(2)>29/50>(18/25)^2, with the last exact difference
77/1250. Taking positive square roots yields
sqrt(2-sqrt(2))>18/25, and hence the displayed sine square
is strictly less than 8/25. The actual directed gap is therefore
strictly greater than 3pi/8.

At W=2 the ratio is 4/5, whose square 16/25 is strictly greater
than sin(pi/4)^2=1/2. Thus the gap is strictly greater than pi/2.

All three comparisons are between positive quantities and use the
monotone inverse sine on [0,1]. No sampled or approximate angle
value enters any strict inequality. The estimates stay strict at
R=sqrt(Q), at actual circle-contact endpoints and at all shared-side
or point-contact cases.

## 3. Weighted count and its strictness

For t boundary marks, s side singleton runs, d diagonal singleton
runs and l two-side runs, the actual body count is
m=t+s+d+2l. These are vertices of the original simple cycle, so
they are counted once. Support telescoping supplies actual endpoint
set-gap reserves 1, sqrt(2), and 2, respectively.

Summing occupied arcs and their directed intervening gaps gives

    2pi > t*pi/4+s*pi/4+d*3pi/8+l*pi/2
         = (pi/8)(2m+d).

The strict sign already follows from each mark's arc length being
strictly greater than pi/4; the three nonempty gap inequalities are
also strict. Direct-contact gaps need only their nonnegative angular
length and are not assigned a fictitious transmitter reserve.

It follows that 2m+d<16. Since m and d are integers, the asserted
uniform conclusion 2m+d<=15 is exact. In particular m=7 forces
d<=1. The proof makes no distinction between cyclic placements or
between the physical orientations of marked endpoints.

## 4. The full original force-and-moment caller

Every unmarked body must be truly unloaded and have full positive
degree two in the same original certificate. Its force equation
therefore gives equal opposite original unit normals and equal
magnitudes. Its full moment equation makes the difference of its
two actual contact means parallel to the normal. This statement
continues to hold for all original means on a shared side.

The square-width classification is complete. If one own-frame normal
component is zero, the two exposed features are opposite sides and
the width is one. If both components are nonzero, the exposed means
are the unique opposite vertices. Their difference is parallel to
the normal only if the absolute normal components are equal; this
gives width sqrt(2). A merely translationally selected certificate
would not justify this classification, and the source correctly
requires angular balance here.

All actual centers have norm less than M=91/60. An internal run
of width sum W has endpoint center projection at least W+1, since
the two endpoint halfwidths are each at least one half. Thus
W+1<2M=91/30. Three internal squares would give W+1>=4, an
impossibility. Two internals including a diagonal would give
W+1>=2+sqrt(2)>91/30, also impossible. Consequently the four
listed run types exhaust the genuine caller; there is no omitted
longer or mixed two-body channel.

Marked vertices may have arbitrary additional positive edges. They
need only be physically circle-touching; no particular individual
circle atom is assumed positive. A circle-touching zero-total-load
unmarked body is still eligible if and only if its full degree is
two, and its physical contact is not deleted. Every square outside
the cycle remains in the physical packing.

For an entire simple positive component, the imported full force
argument supplies at least two positively loaded vertices. Marking
them gives the exact unmarked degree and zero-load domain required
here. That caller does not need every physical circle contact to
carry a positive weight.

## 5. Scope of simultaneous consequences

For four marked vertices and singleton pattern (1,1,1,0), two or
three diagonal transmitters are both ruled out, in all placements.
For five marks with two singleton runs, the both-diagonal case is
ruled out for both adjacent and separated placements. These are
direct integer consequences of the same inequality, not separate
finite contact audits.

For m>=8 the inequality is impossible already with d=0. The source
correctly preserves the stronger applicability of the preceding
force-only occupied-arc theorem for that conclusion: the new
discrete weighted caller adds moment assumptions only to distinguish
diagonal reserves.

The theorem does not by itself rule out one diagonal in a seven-cycle
with a long run; that separate exclusion is explicitly attributed to
the already reviewed sharp long/diagonal angle theorem. It does not
declare all seven-cycle load families or larger branching parents
closed. Original coarse obligations, full means and compatible
selection requirements remain unchanged.

Both frozen source pins were checked against the workspace bytes.
No numerical pose search, sampled trigonometry, Lean/Lake build, CI
run, certificate reselection or original ledger edit is part of this
review.

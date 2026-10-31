# Independent review of the uniform four-square axial near-diameter theorem

**Date:** October 30, 2026 UTC. **Reviewer role:** axial-chain research agent,
separate from the author of the input near-diameter manuscript. Reviewed the
complete current source
[UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_2026_10_30.md](UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_2026_10_30.md),
all five conclusions and its precise stress-path corollary. This is a review
of that stated theorem, not a review or adoption of the separate new
expanded-square-cover theorem.

## Result

**Accepted at its exact stated scope.** The center-radius quadratic, whole
width-excess budget, angle conversion and endpoint transverse bound are
valid, retaining equality in the radius hypothesis. No global row, common
center height, same-angle assumption, or whole-original-cell closure is
inferred.

## Reconstruction

1. The exact farthest-corner identity gives
   `|c|²+|c|+1/2 <= Q`. Its positive root is
   `rho = sqrt(1041)/16 - 1/2`. Thus every projected center lies in
   `[-rho,rho]`. The strict slack comparison uses
   `225*1041=234225<234256=484²`, establishing
   `Delta=2rho-3<1/30` without rounding.
2. Each consecutive projected gap is `(m_j+m_(j+1))/2>=1`.
   Summing forward and backward gives exactly
   `j-rho <= x_j <= j+rho-3`, centered at `j-3/2` with halfwidth
   `Delta/2`. All four indices, including both endpoints, obey this.
3. The telescoping width expression is
   `m_0/2+m_1+m_2+m_3/2`.
   Subtracting three leaves exactly the manuscript's four nonnegative
   excess terms. Consequently the interior widths are below `31/30`
   and the endpoint widths below `16/15`.
4. On the reduced square-angle range `[0,pi/4]`,
   `m²=1+sin(2theta)` and sine is increasing. The exact two squared
   width excesses are `61/900` and `31/225`. The stated arcsine bounds
   follow; their decimal degree values are explanatory only.
5. The endpoint longitudinal magnitudes are at least `3-rho`.
   Therefore their transverse squared magnitudes are at most
   `rho²-(3-rho)²=6rho-9=3Delta<1/10`.
6. Four consecutive gaps of at least one in a five-square path require
   projected span at least four, whereas `2rho=3+Delta<4`.

The signed-normal stress-path corollary is also correct: at each actual
unloaded true-positive-degree-two internal unit, its two nonzero pair
forces cancel, giving equal magnitudes and the same signed normal after
orienting the path. The actual tight projection equalities then supply
the geometric premise. No full torque equation is needed for this
corollary; loaded or branching internal bodies are correctly excluded.

## Caller and equality limits

The proof actually tolerates nonnegative extra projection gaps when
deriving the displayed inequalities, although the source only claims
tight links. This observation does not extract a chain from an arbitrary
packing. The endpoint degrees and physical circle masks do not enter the
estimate. The known aligned four-unit row is retained at `q=Q`; internal
transverse center coordinates remain unrestricted beyond the other actual
packing constraints. The manuscript correctly avoids treating a staggered
projection chain as a solid row.

No numerical pose search, Lean build, CI, original inventory change or
end-to-end audit of the sharp n=9 theorem was performed in this review.

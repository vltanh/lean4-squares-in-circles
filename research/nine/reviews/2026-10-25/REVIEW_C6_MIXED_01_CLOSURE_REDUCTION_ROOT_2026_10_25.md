# Root review: mixed 0/1 C6 closure and the uniform force ratio

Date: October 25, 2026 (America/Chicago).

Reviewed source: `SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md`.

**Verdict: accepted as a complete necessary reduction, with no claimed
whole-orbit exclusion.** I read the full saved source and checked its
original physical domain, both closure projections, the strict angular
consequence and the entire analytic force-ratio proof. No numerical
sample, Lean compilation or CI is a premise of this review.

Directly expanding `f_2+J(f_1-f_2)` gives exactly the two coordinates
printed for the actual nonshared unit 2. Its two summands have the
claimed angles, and their positive sum lies between them. This gives
both component inequalities in (6) with their correct directions.
Substituting the actual shared chords gives precisely (7)--(9),
including the retained nonnegative `c_1 t_1/p` term. The strict
positivity of the original chord at unit 0 supplies `q t_0<1`, hence
the strict inequality (10). The excluded upper-turn endpoint is
contradicted directly by closure, without dropping its genuine mean.

Under the contrary `p<=1+1/sqrt(2)`, the first projection implies
`c_0<=kappa-kappa^2 c_1`. I checked the exact reciprocal identities
and the endpoint map from `[0,1/sqrt(2)]` to
`[1-1/sqrt(2),sqrt(2)-1]`. The displayed function `L` is decreasing
and concave on the whole interval, so its two strict endpoint lower
bounds imply the claimed affine lower line throughout. The final
Cauchy inequality places `h_1` strictly below that line. This is
incompatible with the original strict angular consequence and proves
the full force-ratio bound `p>1+1/sqrt(2)`.

Using an independent `Fraction` calculation, I reproduced the four
rational reserves (15), (16), (18), (20), and the positive coefficient
in (17). They agree exactly with the saved fractions. The two squared
comparisons have positive sides, so no extraneous root is accepted.

All genuine shared endpoints, actual forces and means, true transmitter
degrees, unique physical masks, both radius endpoints and all three
extra units remain. The virial inequality for the whole mixed 0/1
orbit still requires a separate full proof; no original roadmap gate
is checked by this necessary force-ratio reduction alone.

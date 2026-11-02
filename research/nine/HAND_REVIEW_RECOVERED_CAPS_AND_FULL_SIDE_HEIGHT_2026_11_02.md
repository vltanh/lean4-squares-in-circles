# Hand review: recovered physical caps and the new full-side height bound

November 2, 2026. This is an agent hand-reconstruction record, not a human
review or kernel verification. No proof script, Lean, Lake, or CI was used.

## Recovered sources

The following sources were recovered from the previous session's local
workspace and re-read in full. Their restored status supersedes only the
latest handoff's statement that these particular complete texts had not
been found; it does not retroactively close A.2.

- `TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`: complete ordered 9/20
  whole-floor cap, with its exact 7/16 negative control.
- `TWO_SQUARE_SIDE_STRIP_CENTER_CAP_HAND_PROOF.md`: complete 9/16
  high-center side cap, including both horizontal normal signs.
- `UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md`.
- Sections 7--9 restored to
  `UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md`:
  physical section/center order and the stated center-height consequences.
- Sections 1--6 of
  `UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`:
  the 3/8 preliminary and stronger 7/20 main-height bounds. Its later
  adjacent-proxy and strip-routing sections were not restored as part of
  this minimal dependency recovery.

For the central cap, the complete square expansion was independently
reconstructed. The coefficients before multiplying by 16 and subtracting
248625 s^2(1+s^2)^2 are
\[
 1,174,11410,24174,30258,-1494,22330,-3894,3481.
\]
They give all nine source coefficients. The cubic values
4259563/10^6, -134979/10^4, 64973/25, and 418473/2500 were recomputed
by ordinary hand arithmetic. The positive-normal reduction, chosen test
vector, and the fact that only the lower square needs the whole floor
were checked. The strict 7/16 counterexample remains in scope.

For the side cap, the convexity numerator
1/2+(5/2)a^2-(9/5)a and the two anchor values 1279/624 and 77/4320
were reconstructed. Both signed horizontal coefficients are necessary;
neither horizontal center ordering was dropped. The final squared reserve
47/1224 is correct.

For inner clearance, the disk-to-box distance, the two strict horizontal
excess bounds 1/10 and 1/60, and the final 97/100 and 59/60 constants
were checked. These are center clearances, not projection separators.

The side-marker order transports nondegenerate vertical sections from
their center-midpoint line to the marker line. The marker line is inside
both horizontal projection intervals; continuity and closed disjointness
preserve the order. The 29/30 main-to-side gap has exact radical reserve
2960/864900. The subsequent full-side and equal-marker deductions keep
their hypotheses, including the full-side premise in the zero-marker case.

For the recovered 7/20 height bound, the near-aligned main's two
chirality cases give center distance greater than h_F+12/25. The
horizontal majorant X-9/20 is strict on the whole side band. The first
corner expression increases in X; the second is concave in X. The
three ranges [1/2,13/25], [13/25,13/20], and [13/20,1/sqrt(2)]
are exhaustive. The endpoint reserves 30091/1440000, 1759/57600, and
77527/1440000 were checked. No physical y-separator is introduced.

## New sources

`ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md` proves
the low-center band and the negative-horizontal-normal cap.

The low-band radical comparison has the exact reserve
1819/5760000. The oriented cap retains its essential signed-normal
hypothesis. Its complete-interval curvature estimate is
1/10+83/162000, and its endpoint comparison gives F>52/25.
An initial wording error in the derivative estimate's interval was fixed:
the actual range is sqrt(21)/5<=b<=1, which implies L^2>=1;
9/10 is used only as a looser numerator and derivative bound.

`FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md` proves that a
main above two same-side outsiders has y>3/5, with all three reflections.

The near-main estimate keeps the outsider's orientation:
V>=g+h_F-1/128. The quadratic loss bound is
t(1/8-t/2)<=1/128. After the low-band restriction, this supplies the
needed whole floor -1/8, with strict rational reserve 21/19840.

The positive-normal terminal uses the test vector (1/2,b). Its two
normal ranges use different strip endpoints according to the sign of
1/2-a. In the first range, the reconstructed derivative numerator is
\[
 b^3/2+(b^2-a^2)/(8b)+a/(32b)-a/120+a^3/2.
\]
Its lower bound and the final product derivative give monotonicity.
The second range has the two exact polynomial endpoint values
991/9600 and 1049/7680. The integrating root agent independently
reconstructed this positive-normal argument, the near-main floor, and
the final signed-case join and reported PASS.

An earlier proposed isolated asymmetric side-pair cap was rejected:
its positive-normal branch used an invalid strip endpoint when a test
vector's horizontal component exceeded that of the separator. It is
not among the accepted sources. The final main-height proof resolves
the missing branch by retaining the inner main and deriving a stronger
whole-square floor; it does not reuse the rejected assertion.

## Method and accounting

This agent made twelve exploratory scalar-evaluation calls to test candidate
constants and support directions. They were finite floating-point scans
of conjectured analytic bounds, not physical root enumeration or proof
verification; one family included a discarded invalid proposed bound.
No output from those scans is proof evidence. All accepted identities,
sign choices, whole-interval bounds, and rational reserves above were
derived and checked by hand. Text copying and editing processed source
bytes only.

The separately restored adjacent-proxy barrier and horizontal-strip
pair-gap sources were also hand-checked for the new bounded-inner caller.
The barrier retains both activity cases and both square chiralities.
For the strip's 4/5 estimate, the half-angle polynomial is exactly
875w^4-792w^3+88w+5; its anchors 16/125, 635/4096, 1839/128 and final
reserve 1190079/29491200 were reconstructed. The new source
`BOUNDED_INNER_HEIGHT_ROUTED_TRIPLE_HAND_PROOF.md` retains all five
outsiders, derives their exact three-plus-two split, and gives the central
whole floor 109/930 using the stronger central proxy gap. Its matched
shoulder-to-endpoint comparisons remain explicit: the subsequent terminal
uses either actual vertical comparison or an upward nearvertical
separator owned by the outer main, with the choices made independently
at the two ends. The separate integration review records that join.

These recovered and new statements do not yet exclude every actual-four
occupancy or completed-chain mask. A.2 and the canonical root ledger
remain unchanged unless a separate complete-domain caller is supplied.

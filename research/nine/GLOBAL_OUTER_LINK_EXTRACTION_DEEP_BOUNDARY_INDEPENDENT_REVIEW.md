# Independent review of the deep-boundary nonlinear cylinder terminal

November 3, 2026. The nonlinear physical reduction, original separator
coverage, independently reconstructed rational checker, and fresh full
exact replay are accepted. No Lean, Lake, or CI was used.

The reviewed hand source is
`WEAK_OUTER_LARGE_GAP_DEEP_BOUNDARY_NONLINEAR_LIFT.md`. Its base is the
aligned nine-original configuration with B,C in the bottom row and H,I
in the central row. The terminal applies at closed `Q=1105/256` when
the eight centers other than F and all nine signed canonical angles
are within `1/64` of their stated base values. **Both coordinates of
the original F center are free.** The original strict C/D weak bit and
the original marked comparisons are retained.

## 1. The error scale is sufficient for a nonlinear conclusion

Let eta bound the specified coordinate shifts and all angle magnitudes,
and let `Z=max_i|theta_i|`. The accepted row bounds are multiples of
`eta*Z`, with no independent squared-center error. This distinction is
necessary because some center motions survive the tangent equations.

For a physical pair, the exact owned support sum is
`(1+cos(Delta)+|sin(Delta)|)/2`. Its deficit from
`1+|Delta|/2` is bounded by

    Delta^2/4+|Delta|^3/12 <= (1+2eta/3)*eta*Z.

The largest owned-projection error is the diagonal C/D error
`(2+eta/6)*eta*Z`. Their sum is at most
`149eta*Z/48 < 25eta*Z/8` for eta<=1/8. The actual-link width error is
at most `25eta*Z/48`. These estimates use the actual angle magnitudes
and retain zero-angle and opposite-chirality faces.

For an active circle corner p and its rotating offset w, the exact
containment identity is

    2p·e + 2p·Jw theta + 2p·E + |e+theta Jw+E|^2 <= 0.

The complete final square is nonnegative and can be dropped. The
rotation remainder has norm at most `theta^2/(2sqrt(2))`, so the
linear circle row is at most `sqrt(Q/2)*theta^2 < (3/2)eta*Z`.
There is consequently no center-only error to absorb. Absolute-value
rows, the two sign choices, the marked cones, and the closed weak row
have exactly zero error. In particular

    d<h_C+h_D<=1+(|theta_C|+|theta_D|)/2

supplies the weak tangent row directly, without a Taylor relaxation.

## 2. Local owned separators and their linear rows are exhaustive

For central-row contacts near `(1,0)`, every steep projection is below
one; negative shallow signs cannot separate. The coordinate-swapped
argument covers lower-to-middle contacts near `(0,1)`. For the four
boxed upper contacts near `(±1/2,1)`, shallow projections are at most
29/32 and negative vertical signs cannot separate. The diagonal C/D
pair retains its positive shallow and positive upward-steep alternatives
as separate exhaustive cases. Either physical original may own each
surviving axis.

At upper contacts, minimizing the owned angle expression yields
`max(theta_i,theta_j)/2` for horizontal offset +1/2 and
`-min(theta_i,theta_j)/2` for offset -1/2. Each minimum bounds both
printed linear angle rows in the required direction. Thus imposing
both rows does not assume simultaneous separation by both owners.
The diagonal owner minima are respectively
`-(theta_C+theta_D)/2` and `+(theta_C+theta_D)/2`, matching the two
physical alternatives in the exact source.

## 3. The unboxed F-center cylinder is valid

Original actual EF and FG imply `|x_F|<=eta`. The original FG cone
gives `y_F>=-1/16-3eta`. If F were no higher than H or I, their center
distance squared would be bounded by

    (1/2+2eta)^2+(4eta)^2 <= 13/16 < 1,

contradicting the original contained radius-1/2 disks. Thus F is above
both central extras. Containment also gives `y_F<rho`, and the two
full vertical gaps lie strictly between zero and two.

This excludes every shallow separator for these two contacts: its
projection is strictly less than `1/2+4eta<=1`. A negative vertical
normal has projection at most `eta*(1/2+2eta)<1`. The surviving upward
projection has its full positive vertical gap multiplied by cosine;
discarding that cosine loss is favorable. Its error therefore depends
only on the bounded horizontal increment and angle, exactly as in the
boxed upper-contact estimate. No bound on F's vertical displacement
from the base is used.

The only other rows involving F are its actual horizontal comparisons,
which use x_F and its angle. No active circle row uses F. Hence the
same nonlinear bounds and exact identities hold with both F-center
coordinates unboxed. This covers the continuous upward F motion in
the aligned equality family without invoking the separate F/C order
theorem.

## 4. Exact checker and complete fresh replay

The independently reviewed exact source reconstructs all 65 homogeneous
rows in each of eight cases: 56 physical, sign, and weak-comparison
rows, followed by nine explicit exact rows `-z_i<=0`. It uses only
`Fraction` arithmetic and standard-library routines. The appended rows
correctly account for the magnitude lower-bound multipliers from
discovery. No numerical bound on a center or signed-angle variable
is retained.

The checker requires all eight C-sign, D-sign, and C/D-direction cases,
and all 18 signed-angle targets in each case. Every positive rational
combination must equal its single signed-angle target in **all 36
columns**, including both free F-center columns. Repeated cases,
targets, or row indices, wrong identities, and insufficient contraction
costs are rejected.

A fresh complete exact replay passed all 144 identities. The report is
`computer_assisted/weak_outer_deep_boundary_global_independent_replay.json`.
Both frozen hashes were checked before and after execution and remained
unchanged:

    certificate
    0a64c08f0e7845a4bf6aa5d5ce43bcb80167a847101b36f903d10554e53a290c

    exact verifier
    08d913b7e9adc174e66e2225fe0a05e732cd6fa6fbacb794f39b23f61c6e2aef

The maximum exact weighted error cost is `K=4234/69`. At the accepted
closed radius `eta<=1/64`, the contraction reserve is

    1-K/64 = 91/2208 > 0.

Choose the original and sign attaining Z and apply its exact dual.
Then `Z<=K*eta*Z`, so Z=0. Every physical original is aligned. In
particular C,D are aligned, and their nonoverlap requires `d>=1` or
`|v|>=1`. Their unchanged cone has `d>=|v|`, whereas their strict weak
bit requires `d<1`. This is a contradiction, with no further equality
classification or center-rigidity assumption.

## 5. Acceptance boundary

The result is a complete nonlinear cylinder exclusion for the original
strict caller, even at closed Q. It is stronger than a tangent-space
diagnostic. It does not exclude the actual-link equality configuration
after deleting the strict weak premise, and it does not establish that
every remaining original-nine configuration lies in this cylinder.
That global placement complement, and the whole fixed mask, remain
open until separately covered.

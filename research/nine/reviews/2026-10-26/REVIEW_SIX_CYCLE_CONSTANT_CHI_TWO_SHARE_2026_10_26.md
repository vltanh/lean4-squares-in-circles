# Independent review: full constant-corner two-share C6 exclusion

Date: October 26, 2026.

**Verdict: PASS.** The saved manuscript
`SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md` proves the entire
constant-corner two-share orbit, subject to its explicitly cited and
unchanged physical normal-form inputs. Its force and angle domains are
whole domains; the only finite positivity work is the six displayed
rational matrices. This review does not label that finite calculation
table-free and does not extend the conclusion to either mixed orbit.

## 1. Physical equations and orbit cover

I checked the original local support formulas against
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md` and the three-orbit cover in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`. For constant
corner bits, cyclic relabeling places the two genuine outgoing shares
at 0 and 1, and reflection plus reversal takes the constant-zero
pattern to the constant-one pattern while carrying the actual means.
This is the complete constant-corner orbit, not an assumption that the
two mixed placements are equivalent.

The shared chords in (4) are the actual torque-determined chords,
including chord one at a genuine endpoint mean. The nonshared vector
is exactly \(g_2=f_1+JF_2\), so its norm is
\(\sqrt{2\mu_1^2+\mu_2^2+2h_2\mu_1\mu_2}\). In particular
the asymmetric coefficient 2 is on \(\mu_1^2\). The numerator and
closure in (6) follow without moving a transmitter, centering a force
triangle, or changing an application mean.

All actual force magnitudes are positive. The two normalizations in
Sections 2 and 4 are explicitly separate homogeneous rescalings. The
final gap is restored with its correct factor \(\sum_i\mu_i\).
The three completion squares are arbitrary because the contradiction
already follows from necessary equations of the six actual component
squares. No step uses nonoverlap of a replacement or aggregate body.

## 2. Closure projection and the single angle triangle

Independent expansion gives
\(g_2=p(-(c+d),d-c)+q(-b,a)\). Both summands lie in the
stated second-quadrant cone, and \(\beta_2\le\pi/4\) gives
\(\pi/4-\beta_1\le\beta_0\). Consequently the normalized
first coordinate satisfies \(m\ge b\). Substitution of the actual
\(\ell_1\), rather than a unit chord, yields (11), hence (12)
and the angular consequence (13).

The optional force bound (14) also checks. Expanding (15) and using
\(c^2+d^2=1\) proves the exact displayed factorization. Since
\(A=0\) contradicts (12) and \(\beta_0>0\), every denominator
used there is strictly positive.

For Section 3, the derivative formula (17) is correct and strictly
positive on the full interval. The sine polynomial is an upper bound
on \([0,1]\) with the correct alternating remainder sign, and it is
increasing there. Independent exact rational arithmetic reproduces
the stated reserve
\(1733430901/704936673280\) in (19).
The comparison \(41/140<1-1/\sqrt2\) is precisely
\(\sqrt2<99/70\). Convexity of \(T\) and its two endpoint
values give the claimed global implication, including the enlarged
closed endpoints. The three vertices in (20) are exactly those of
the resulting single triangle.

## 3. Whole-force quadratic and Taylor bounds

The square-root chord inequality (22) has the correct direction by
concavity. Since each adjacent normalized force sum is at most one,
replacing its reciprocal by one preserves the lower bound (23).
The sole remaining numerator norm has the exact squared difference
shown before (24). The square-root tangent upper bound and
\(\sqrt2p+q\le\sqrt2\) give the stated coupling coefficient
\(1-h_2/\sqrt2\), with the correct subtraction sign.

I expanded the homogeneous quadratic independently. Its diagonal
coefficients are exactly \(2K-C_i\); its off-diagonal coefficients
are exactly (27), including the extra coupling only at the pair
\((1,2)\). Thus (26) covers every positive force ratio without
optimization or subdivision.

Both second-derivative estimates in (28) hold globally on the full
closed angle interval. They are Taylor remainder bounds valid on
both sides of \(2\pi/3\), rather than one-sided series truncations.
The signs in the matrix formula imply the stated entrywise lower
bound. The proof correctly applies that bound only to nonnegative
force coordinates, not to arbitrary signed vectors.

## 4. Independent exact reconstruction of all six controls

I reconstructed (30)--(32) from their formulas, with a fresh rational
interval implementation using only `fractions.Fraction`. The linear
polarization and quadratic polarization in (31) give exactly the six
degree-two triangular controls, so (33) is an identity and its six
weights are nonnegative with sum one. There is no omitted mixed
coefficient or recursively subdivided angle region.

The fresh calculation reproduces every rational reserve in (35),
both Machin reserves following (36), all six minimum entrywise
reserves in Section 6.2, and all six matrix-vector products in
Section 6.3. In particular the six minimum entrywise reserves are:

| Control | Independently reconstructed reserve |
| --- | --- |
| \(AA\) | \(1188713761/2880000000000\) |
| \(BB\) | \(1188713761/2880000000000\) |
| \(CC\) | \(45726851003/368640000000000\) |
| \(AB\) | \(897083982283/3686400000000000\) |
| \(AC\) | \(20646394735267/98304000000000000\) |
| \(BC\) | \(18560102883341/294912000000000000\) |

Each exceeds \(1/20000\). The matrix-vector products are,
respectively, \((410,720,324)\), \((394,569,618)\),
\((251,260,63)\), \((34,208,249)\), \((121,205,109)\),
and \((170,355,315)\), exactly as displayed.

Expanding the weighted-row identity (38) recovers the quadratic
form coefficient by coefficient. The nonpositive off-diagonal signs
make every squared-difference term nonnegative. Its uniform smallest
row ratio is exactly \(21/5000\), coming from the final coordinate
of the \(CC\) control. This proves (39) for all real vectors; the
entrywise comparisons around it are used only for the actual positive
force vector, as required.

The rational reconstruction is an independent audit of the displayed
small calculation, not an additional proof dependency. The manuscript
itself gives the formulas, rational intervals, lower matrices, and
positive row identities needed to reproduce the proof by exact
arithmetic. No numerical eigenvalue or sampled sign is used.

## 5. Joined contradiction and limits

The convex control decomposition, the entrywise comparisons, and
\(\sum_i\mu_i^2\ge1/3\) give exactly the normalized reserve
\(7/5000\). Restoring scale yields (41). Substitution of the
original virial identity gives \(R<79/40\), contradicting the
whole retained radius window, including both endpoints.

I accept the complete constant-corner two-share orbit as excluded by
this manuscript. It uses six explicit small matrix positivity
calculations, with no separate coefficient packet or force-ratio
certificate. It does not yet close the entire two-share gate, because
the two mixed-corner orbits require their own proofs. The one-share
and strictly obtuse one-radial families, equality classification, and
the earlier prerequisite-chain audit remain outside this result.
No Lean compilation, CI, or workflow dispatch was performed.

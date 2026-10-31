# Exhaustive assembly of the three two-share alternating-C6 contact orbits

Date: October 26, 2026.

**Status: complete whole-family exclusion, accepted after independent
saved-source and physical-scope review.** All three original contact
orbits have complete independently reviewed exclusions. The last
mixed placement 01 is assembled in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md`; its boundary proof is
independently reviewed in
`REVIEW_C6_MIXED_01_BOUNDARY_MONOTONICITY_C6_2026_10_26.md`.
The resulting exhaustive three-orbit join passed root independent
review in `REVIEW_C6_MIXED_01_COMPLETE_JOIN_ROOT_2026_10_26.md`.
No conditional proof dependency remains. This source does not
by itself close the remaining one-share completion gate or an original
coarse roadmap gate.

This assembly retains all nine original physical squares, the common
selected certificate, every actual positive force, each genuine shared
interface and actual application mean, all physical unique-circle
masks, the true unloaded side-normal transmitter equations, all three
extra squares and all actual transmitter positions, and

\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

## 1. The finite cover is of original contact types

The strict-turn normal form gives at most one genuine share at each
loaded unit. The accepted double-shared-channel exclusion gives at
most one genuine share at each transmitter. With exactly two shares,
the original six-cycle therefore contains a matching of two genuine
shared interfaces. A mean at a side endpoint does not change that
interface's contact type.

The full mean-preserving symmetry proof in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md` uses only
cyclic relabeling and a reflection followed by cycle reversal. The
latter sends the corner bits to their complements and carries every
physical unit, actual mean and positive force along. It reduces all
constant patterns to `111`, and all mixed patterns to `110`.

For `111`, all possible shares are outgoing, so cyclic relabeling
places the two shared loaded units at 0 and 1. For `110`, a
share at 0 is outgoing to transmitter 0, a share at 1 is outgoing to
transmitter 1, and a share at 2 is incoming from transmitter 1. The
placement `{1,2}` would share that one transmitter twice and is
already excluded. The other two mixed placements must both be covered.

The exact exhaustive list and its proofs are:

| Corner word | Shared loaded units | Original shared interfaces | Whole-orbit proof |
| --- | --- | --- | --- |
| `111` | `0,1` | `S_0W_0`, `S_1W_1` | `SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md` |
| `110` | `0,1` | `S_0W_0`, `S_1W_1` | `SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md` |
| `110` | `0,2` | `S_0W_0`, `W_1S_2` | Both mixed-02 branch sources joined below |

No angular or force-ratio mesh is part of this enumeration. It is an
exhaustive symmetry cover of actual original contact types.

## 2. Reviewed constant-corner and mixed-02 exits

The constant-corner source proves the whole-angle, all-positive-force
gap

\[
 \frac{79}{40}\sum_i|F_i|-N
                  >\frac7{5000}\sum_i\mu_i>0.
\tag{2}
\]

Its exact shared means enter the closure projection before the angular
enlargement is made. All endpoint means remain included. The finite
positivity work consists of six explicitly displayed rational
three-by-three matrices with positive weighted-row identities; this
assembly does not describe that proof as table-free. Its complete
independent review is
`REVIEW_SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_2026_10_26.md`.

For mixed placement 02, normalize the original positive force scale to
`(1,p,q)`. The orderings `q>=p` and `q<p` are exhaustive;
the equality case belongs to the first. Their proofs are respectively

- `SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md`;
- `SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md`.

The first gives a whole-domain virial contradiction. The second uses
the actual unique-corner force bound `p<27/10` and the exact
closure equations to obtain a contradiction over the complementary
force ordering. Their physical corner word, genuine interfaces,
original means, force normalization and full radius window agree.
Their independent exhaustive join is saved in
`REVIEW_C6_MIXED_02_LARGE_FORCE_AND_JOIN_2026_10_26.md`.
Neither branch uses a coefficient packet or numerical sign premise.

## 3. The mixed-01 exit and the complete-family consequence

The separate mixed-01 assembly retains all original shared means long
enough to obtain exact closure projections and the strict force bound
`p>1+1/sqrt(2)`. Cauchy's inequality then gives a necessary gap
over the full remaining positive-force interval. Its two fixed endpoint
values have complete rational square-bound proofs. The independent
analytic boundary monotonicity gives the complete force-range join,
with the original homogeneous gap

\[
 \frac{79}{40}\sum_i|F_i|-N>\frac{\mu_0}{40}>0.
\tag{3}
\]

Every row in Section 1 therefore has a full contradiction.
Consequently **no all-unique, all-side-transmitter alternating C6 can
have exactly two genuine shared interfaces** in the radius interval
(1). The proof is independent of the locations of all three extra
squares, which remain arbitrary physical units throughout.

Combined with the already accepted zero-share and three-share
exclusions, this complete result leaves exactly one genuine share
in any remaining all-unique all-side alternating C6. The surviving
one-share contact types require their own original three-extra
completion arguments; no valid feasible core is contradicted merely
by this two-share theorem. The strictly obtuse one-radial family also
remains a separate original obligation.

This contact-family exclusion does not by itself prove the unrestricted sharp radius bound,
classify all equality packings, or discharge the earlier prerequisite
audit. No original coarse roadmap gate or accepted checklist count is
changed by this source alone. No Lean compilation, CI, workflow
dispatch, or physical-force deletion is used.

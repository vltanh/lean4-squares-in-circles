# Independent audit: complete common quarter table

Date: 2026-10-17 UTC.

**Result: PASS.** The complete three-row common marker table has hand
proofs for every signed core/outer boundary pair and every retained SAT
axis. The resulting four word exclusions are conditional on the explicit
upstream frame bound \(D<7/10\). That global hand gate remains open.

## Reviewed proof units

| Proof unit | Review result |
|---|---|
| Whole core/core four-type estimate | Independent geometry, marker, incircle, and rational audit passed |
| Complete zero-quarter row, \(\gamma_0=391/400\) | Independent continuous geometry/sign audit passed; 40 displayed strict rational comparisons passed |
| Complete unit-quarter row, \(\gamma_1=157/200\) | Two independent continuous audits passed; 80 strict rational comparisons passed |
| Complete double-quarter row, \(\gamma_2=163/200\) | Independent continuous geometry/sign audit passed; its fixed rational replay passed |
| Four words with a double increment | Exact common-marker telescoping gives \(2\pi>1259/200>44/7\), a contradiction |

The unit-quarter reviews checked the full 32-cell source-axis table and
the physical reflection/reversal covering the retained target axes. In
particular, both reviews separately checked:

- The three constant-multiplier circle envelopes and their concavity on
  both sides of zero.
- The negative-source reduction to the straight core side on the
  secondary axis.
- The mixed core/outer primary-axis bounds, including the positive-core
  corner barrier and the sloping outer-circle support.
- The two core-side subintervals with forced target coordinates
  \(B<.415\) and \(B<.04\).
- The negative-target compensation \(h(z)+gB(1-\cos z)\).
- The separate outer/outer negative-primary corollary. It uses its own
  endpoint argument and is not inferred by swapping source axes.
- The core/core reuse at \(K=7.3\), including the change of marker
  coefficient from \(1.077372\) to \(1.164\).

One review reran the arithmetic in temporary copies and reproduced the
JSON outputs byte for byte. The arithmetic checks are fixed rational
calculations; no optimizer or interval subdivision is used as a premise.

## Remaining dependency boundary

COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md records the exact
logical assembly. Its premises include the hand central-core and radial
reductions, the common-point gap and backward-axis exclusions, and the
separate frame-concentration conclusion. The first group has hand proofs;
the whole-domain frame-concentration hand replacement is still active.

After that frame conclusion, precisely three quarter words remain:
\(0010111\), \(0011011\), and the candidate \(0101011\). Their global
hand inequalities/capture are not supplied by this audit. In particular,
this audit does not relabel the completed computer-assisted unrestricted
theorem as an unrestricted hand proof.

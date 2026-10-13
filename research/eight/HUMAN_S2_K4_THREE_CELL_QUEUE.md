# Exact three-cell continuous queue for the surviving exclusive S2/k=4 branch

Research continuation, 2026-10-12. This is an
**exhaustive combination of established necessary
hand theorems**, not a claim that any listed
continuous cell is geometrically realizable.
Its purpose is to prevent previously excluded
inner/outer and near-axis states being revisited,
without silently inferring whole-square membership
from a center sign.

## Assumptions

Let eight pairwise interior-disjoint unit squares
lie in the disk \(R^2\le9789/2500\), with unique
open origin-containing central square C.
Suppose all seven exterior labels have **exactly
one** available central-owned whole-square
side separator of exclusive type
S2=(3+0,2+2), and precisely \(k=4\)
exterior centers have norm \(\ge1\).

After central-frame symmetries write
\[
R:3,\quad L:0,\quad U:2,\quad D:2,
\]
with U the nearer two-square cap.
Let \(h_R,h_U,h_D\) be the outward signed
central side offsets, so \(h_U+h_D=1\).
Write \(t\) for the central square's signed
coordinate on the 2+2 axis:
\[
h_U=1/2-|t|,\qquad h_D=1/2+|t|.
\]

## Forced labels, center classes and offsets

All seven statuses are single-side, so
the three R labels, two U labels, and
two D labels are **mutually distinct**.

The two far D-center norms are outer
because \(h_D\ge1/2\).
The preceding complete S2 near-inner
exclusion shows that at least one U-center
is outer. The triple-inner cap lemma says
at least one R-center is outer. Because
exactly \(k=4\), there is therefore
**exactly one outer and one inner U-center**,
**exactly one outer and two inner R-centers**,
and **exactly two outer D-centers**.

The two inner R centers have opposite strict
signed y coordinates, by the all-frame
two-inner whole-cap theorem. The far two
D centers have opposite strict transverse
x coordinates, by the previously established
two-cap center sign theorem at offset
\(h_D\ge1/2\).

The sharp triple-cap two-outer result
[HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md](HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md)
rules out \(h_R\ge13/100\), since that would
force at least two outer R labels in addition
to the other three outer labels.
The opposite 2+2 cap theorem gives
\(|t|<5/24\), and the high two-outer-cap
theorem [HUMAN_TWO_OUTER_HIGH_CAP.md](HUMAN_TWO_OUTER_HIGH_CAP.md)
rules out \(|t|\le3/200\) when k=4.
Thus the remaining exact necessary offset
intervals are
\[
\boxed{0<h_R<13/100,\qquad
3/200<|t|<5/24,}
\]
or, equivalently,
\[
\boxed{7/24<h_U<97/200,\qquad
1/2<h_D<17/24.}                                 \tag{1}
\]

## A complete three-cell sign/offset split

Denote the actual nearer-U center coordinates
by \(p=(p_x,p_y)\) for the inner label,
and \(q=(q_x,q_y)\) for the outer label.
The exact
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
proves
\[
\boxed{|\arg(p)-\arg(q)|>3/4}
\]
for **every** such configuration and moreover
that \(q_x\ne0\).

Every S2/k=4 configuration satisfying (1)
must lie in **exactly one** of the following
three disjoint continuous cases:

| Cell | Offset / transverse sign | Additional necessary constraints |
| --- | --- | --- |
| **A — high near cap** | \(2/5\le h_U<97/200\) | The two U center x-signs are strictly opposite: \(p_xq_x<0\), by HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md |
| **B — low near cap, opposite signs** | \(7/24<h_U<2/5\), \(p_xq_x<0\) | Preserve the mixed \(>3/4\) polar gap and all far-D / R-center constraints |
| **C — low near cap, weak same signs** | \(7/24<h_U<2/5\), \(p_xq_x\ge0\) | \(|p_x|<1/4,\ |q_x|>7/10\). **At least one U frame deviates \(>1/2600\) radian** from the central axes, by HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md |

The no-zero-outer-x lemma proves that
the weak-same-sign cell C includes the
possible inner \(p_x=0\) boundary but
never \(q_x=0\). Hence no lost zero-coordinate
cases hide between B and C.

These are **necessary** geometric cells, not
three certified feasible packings and not an
independent status-word count. A proof excluding
A, B and C would finish exclusive S2/k=4,
but would **not** finish S2/k=5,6 or the
other S1/S3/S4/D1/D2 branches.

## Next exact proof obligations

* **A:** combine both U and D pairs'
  strict opposite transverse signs with the
  two R-inner radial/cross-diameter positions,
  and force an actual pairwise separating-axis
  contradiction or sharp disk-vertex bound.
* **B:** use the mixed inner/outer center gap
  together with all four outer R/U/D center
  angles; center norm and cap membership alone
  are not sufficient to assign arbitrary
  full-square separators.
* **C:** retain the forced \(>1/2600\) frame
  defect and the extreme U inner/outer center
  magnitudes. A near-axis argument cannot
  simply be extended to all orientations.

All three still contain continuous center
and frame variables. No formal Lean proof or
complete global \(R_8\ge\widehat R\)
derivation follows. The legitimate sharp
S4/k=7 equality packing is unaffected.


## Additional actual-square slice geometry shared by A, B, and C

[HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md](HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md)
proves that at the common horizontal midpoint
\(Y=(R+h_U)/2\), **each of the two actual nearer-U
whole squares** has an open horizontal chord
of length \(\ge1\). The two chord intervals are
disjoint and therefore have a true left-to-right
order. Any tilted square has *strictly longer*
chord than one. The proof is analytic over
all frames: on a sloping chord the bound is
\[
\ell\ge2(\sqrt2-(R-h_U)/2)>667/600>1.
\]
Only plateau or axis-parallel chords can
approach length one, with equality requiring
an axis-parallel square.

This supplies an **additional common-slice ordering
in every remaining A/B/C cell**; unlike whole
projection separation it is an actually justified
statement for arbitrarily rotated squares. It
does not prove any full cell impossible without
coupling the chord order to true disk
vertices and the remaining five exterior squares.

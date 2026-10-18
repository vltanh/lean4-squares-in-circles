# Exact three-cell continuous queue for the surviving exclusive S2/k=4 branch


## AUTHORITATIVE current A/B/C partition after exact Bernstein search

**The current strict mixed-cap same-sign cutoff is
\(h_U\ge79/250\), NOT the historical 37/100, 1/3
or 8/25 values preserved further below.**

[HUMAN_CAP_ENVELOPE_79_250.md](HUMAN_CAP_ENVELOPE_79_250.md)
proves the sharp arbitrary-frame one-square cap envelope
at h>=79/250 under the actual disk ceiling,
with a **noncircular** height argument and
**63 exact Bernstein coefficient** checks.
[HUMAN_MIXED_HIGH_CAP_79_250.md](HUMAN_MIXED_HIGH_CAP_79_250.md)
then proves that any one-inner/one-outer two-square
whole cap at that offset has strictly **opposite**
transverse center signs: same signs would yield a
coupled radial squared-center distance
\(<999361/1000000<1\).

Therefore the **exact presently necessary S2/k4**
mixed-center near-U cells are

| Cell | h_U | Signs and additional frame/whole-square constraints |
| --- | --- | --- |
| **A** | \(79/250\le h_U<97/200\) | Strictly opposite transverse center x signs |
| **B** | \(7/24<h_U<79/250\) | Strictly opposite signs; retain full outer angular and true SAT constraints |
| **C** | \(7/24<h_U<79/250\) | Weak same signs, inner \(|x|<1/4\), outer \(|x|>7/10\), outer whole NE/NW quadrant owner, at least one actual frame tilt \(>1/2600\) |

The C interval is now only **\(73/3000\) wide**,
and all former high-offset same-sign portions
are **fully excluded**. The two squares on the
near-U side still have common true horizontal
chords on \(y=(R+h_U)/2\) of length >=1.
**No A/B/C cell is globally closed yet.**

A fully rational *single rotated square* at
\(h=3/10\) violates the one-square sharp envelope
even under \(R^2\le q_+\);
[RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md](RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md).
This is **not** a mixed two-square counterexample,
but blocks any unjustified extension of the
one-square proof directly to the lower
cap endpoint 7/24. The
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md)
identifies the next **SAT-based two-square hand
inequality** and six-/eight-square global branches.



## CURRENT case split after computer-to-hand envelope extension

**This section supersedes the earlier A/B/C offset table
farther below; older thresholds are retained as historical
intermediate restrictions.**

The proved [HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md)
extends the sharp single-square arbitrary-frame cap
envelope to \(h\ge37/100\) at \(q\le9789/2500\).
The resulting exact mixed-inner/outer
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md)
excludes **all same-weak-sign** near-U center pairs
for \(h_U\ge37/100\), with strict center-distance
upper bound \(1989/2000<1\).

Thus the *current* exhaustive necessary S2/k4
three-cell partition is:

| Cell | Exact near-U offset | Inner/outer U transverse center signs |
| --- | --- | --- |
| **A** | \(37/100\le h_U<97/200\) | Strictly opposite |
| **B** | \(7/24<h_U<37/100\) | Strictly opposite |
| **C** | \(7/24<h_U<37/100\) | Nonnegative sign product; inner \(|x|<1/4\), outer \(|x|>7/10\); a genuine whole-quadrant outer U member; at least one frame tilt \(>1/2600\) |

This is *strictly smaller* than the previous
same-sign interval up to \(2/5\).
**None of A/B/C is proved impossible as a whole.**
The local numerical experiment and exact
proof conversion are recorded in
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md).


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


## Exact local guardrail: the same-sign two-square cap itself is feasible

[RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
provides a completely **rational actual two-square packing**
of independently rotated unit squares with both
center x coordinates **strictly positive**, with
both whole squares contained in the same cap at
\[
h=881/3000=7/24+1/500>7/24,
\]
and both contained in a disk of squared radius
\[
R^2=7040861/1800000<9789/2500.
\]
Its actual square-pair separating-axis gap equals
\(31/48120>0\), while its disk vertex margin
on the radius-determining square is
\(7219/1800000>0\).
[verify_same_sign_cap_pair.py](verify_same_sign_cap_pair.py)
checks all eight actual vertices and the SAT gap
using **exact fractions**.

**Logical implication:** one cannot close cell C by
claiming that any two whole squares in
\(y\ge h>7/24\) with same-sign centers are
impossible for arbitrary frames. Such a blanket
two-square lemma is **false**.

The pair in the witness has two **outer** centers,
so it is **not itself an S2/k4 cell C realization**,
which requires **one inner and one outer** near-U
center plus five more packed squares. The conditional
near-axis theorem and the mixed inner/outer
polarization theorem are **not** refuted. A genuine
cell C exclusion must exploit the mixed radial
classification, the other five squares, or
additional geometric relations.


## Two local geometry developments affecting cell C

**Exact nonempty standalone same-sign cap pairs.**
[RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
provides two genuine whole unit squares
with both center x coordinates *strictly
positive*, independent frames and positive
SAT separation, at shared cap offset
\(h=881/3000>7/24\) under the n=8
radius ceiling. Both centers in that
example are **outer**, so it is **not**
a complete S2/k4 cell C packing with one
inner and one outer nearer-U center.
It does disprove any universal all-frame
same-sign **two-square** cap exclusion.

**Actual whole-quadrant ownership.**
[HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md](HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md)
proves the stronger *mixed radial class*
result: if the near-U inner and outer
centers in cell C have nonnegative
transverse sign product, the **outer U
square itself** lies wholly in either
NE or NW, with signed x clearance
strictly **greater than \(1/50\)**.
The independent whole-quadrant capacity
theorem forbids any additional entire
unit square in that same quadrant.
This does **not** force every R square
to be wholly in an origin quadrant,
and it does not eliminate cell C.

These notes refine cell C's true-square
status without changing the exhaustive
A/B/C classification or claiming
\(R_8\ge\widehat R\).

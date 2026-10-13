# The exact four side-count branches when all seven exterior squares have single-side separators

## Theorem

Consider any eight-unit-square packing at squared radius
q<=9789/2500, with unique central square C in its
own horizontal/vertical side frame. Suppose every
noncentral square has **exactly one available
central-owned signed-side separator**: no two-adjacent-side
square and no corner-only own-axis exception.

Then all seven exterior squares are assigned
exclusively to sides R,L,U,D. Up to axis exchange
and independent reflections, their two opposite-side
population pairs must form exactly **one of four types**:

| Canonical type | One opposite pair | Other opposite pair |
|---|---|---|
| S1 | 3+0 | 3+1 |
| S2 | 3+0 | 2+2 |
| S3 | 2+1 | 3+1 |
| S4 | 2+1 | 2+2 |

No other all-single-side population type can
occur under the proved cap exclusions.

**Equality guard.** The exactly optimized Cantrell
five-corner construction of SHARP_CANDIDATE_SIDE_STATUS.md
is type **S4**: in its central frame the populations
R=2,L=2,U=1,D=2. Thus S4 must be kept as a genuine
sharp-radius equality branch. The other three types
have not been proved impossible.

## Hand proof

In this branch all seven exterior squares are
single-side, so their total whole-square central
side membership is exactly

    N_R+N_L+N_U+N_D=7.                             (1)

The orientation-free semicircle theorem gives
each population <=3. The 3+2 opposite
cap theorem eliminates pair totals 5 and 6,
so both opposite-pair totals lie between 0
and 4 inclusive.

Because the sum of the two opposite-pair
totals is seven, the **only possible**
unordered pair of pair-totals is {3,4}.
A total of three on one axis is, up to
reflection, either 3+0 or 2+1.
A total of four on the other axis is,
up to reflection, either 3+1 or 2+2.
Taking the Cartesian product gives
exactly S1--S4. QED.

This proof does not assign any specific
frame to the seven exterior squares:
the status 'single side' is a **whole-square
separator direction**, not parallelism
of its own edges to the central frame.

## Exact labeled assignment counts

Each canonical type has a finite number of
signed side-count vectors, and each such
vector has a multinomial number of assignments
to the seven labeled exterior squares.

| Type | Signed vectors | Labelings per vector | Total labeled assignments |
|---|---:|---:|---:|
| S1 (3+0,3+1) | 8 | 140 | 1,120 |
| S2 (3+0,2+2) | 4 | 210 | 840 |
| S3 (2+1,3+1) | 8 | 420 | 3,360 |
| S4 (2+1,2+2) | 4 | 630 | 2,520 |
| **Total** | **24** | | **7,840** |

The row count is checked using
`7!/(N_R! N_L! N_U! N_D!)` and the
axis/reflection symmetries noted above.
Thus the whole D0/S=7 branch consists
of only four **coarse** types rather than
many independent center/angle patterns.

Each row still contains continuous choices
of the seven square orientations, positions,
interior contacts, circle contacts, and
their mutual separating axes.

## Signed central-center domains for the four types

The uniformly proved side-population offset
bounds in HUMAN_ALL_SIDE_OFFSET_INTERVALS.md
give the following **necessary** signed
intervals for the two central-center coordinates
after the same normalization:

    3+0 => t in (-1/2,-5/24),
    2+1 => t in (-83/200,5/24),
    3+1 => t in (-83/200,-5/24),
    2+2 => t in (-5/24,5/24).

For S4, the sharp candidate's actual central
center values satisfy these strict ranges,
as verified by SHARP_CANDIDATE_SIDE_STATUS.md.

These intervals are not by themselves
global geometry certificates. The precise
remaining sharp statement is to rule out
R<Rhat in S1--S4 while allowing equality
in S4, or to derive a single sharp
obstruction valid for the whole D0/S=7
class without this further split.


## 5. New genuine continuous rejection inside S1

The independent whole-orientation slice theorem
HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md proves:

> Three squares wholly beyond a line x=h with
> h>=11/50 in a disk R<=99/50 necessarily
> include **one entire square in y>0 and
> another entire square in y<0**.

Its hand proof takes the midpoint of the cap's
available x strip, proves each of the three
vertical square chords has length >=1 and
that the full square protrudes beyond its
chord by less than 7/20, while the
containing disk's chord half-height is
less than 33/20. Thus the topmost and
bottommost squares lie wholly above and
below the origin's horizontal diameter.

Consequently, two *perpendicular* triples
with both cap offsets >=11/50 force a
**shared double-side member**, since each
triple supplies a whole square in the
common origin quadrant and that quadrant
holds at most one entire square.
The completely single-side Type S1 has
two perpendicular triples and **no**
shared double status. Therefore, after
normalizing them to R and U with central
center (a,b),

    S1 => min(a,b)<-7/25.

Thus the previous S1 location rectangle
`-83/200<a,b<-5/24` (on any axis with
3+1; and `-1/2<t<-5/24` on its 3+0 axis)
has a concrete forbidden near-central
subrectangle:

    **S1 impossible if a>=-7/25 and b>=-7/25.**

This does **not** eliminate all S1:
one triple offset may still be smaller
than 11/50. If the small-offset triple
also has the single opposite-side
member from the 3+1 axis, the opposite
square's transverse center coordinate
is additionally forced into
`(-3/8,3/8)` by the one-square cap
envelope (see the last section of the
triple-cap note).

The three other single-side types S2,S3,S4
are unaffected by this specific
*two perpendicular triples* rejection;
S4 contains candidate equality and
must remain.


## 6. Sharper full-orientation S1 exclusion and the remaining k-subcases

Two new independent hand proofs greatly strengthen
the S1 geometry without assuming a common frame:

* HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md:
  **three whole square members** of a positive cap
  at offset h>=7/50 and radius R<=99/50
  have two distinct centers of norm >1.
  The proof uses three long vertical chords,
  the bound `ell>987/1000`, and the actual
  center inequality
  `p_top.x+p_top.y>1421/1000>sqrt(2)`.
* HUMAN_PERPENDICULAR_TRIPLES_SHARP_LANE.md:
  if two **perpendicular** central sides
  both serve three whole squares and their
  offsets are >=7/50, the two appropriately
  selected outer centers lie in the same
  angular interval of width
  `pi/2-2 atan(9/20)<pi/4-1/100`.
  The proved outer-center angular gap is
  >pi/4-1/500, so they **must be the same
  square**, possessing a shared double-side
  separator status.

S1 has exactly two perpendicular triples
and **no double-side members**. Hence, for
every possible number k of outer centers,

    S1 => min(h_triple1,h_triple2)<7/50.

Normalize the triples to R and U and write
the central center as (a,b). Then

    S1 => min(a,b)<-9/25.

This is a **genuine continuous exclusion**
of the entire complementary central-center
rectangle for S1, substantially stronger
than the previous threshold 11/50 or 13/60.
It does **not** prove S1 impossible when one
triple offset is below 7/50.

Further center-count exclusions, retaining
all frames independently, follow from the
two-outer-center triple result:

* **S2=(3+0,2+2):** if the triple offset
  is >=7/50, then k>=4. If also the central
  signed coordinate on the 2+2 axis is
  within 1/10 of zero, then k>=5.
  Even without the triple offset condition,
  |t|<=1/10 forces k>=4, improving the
  previous |t|<=1/14 band.
* **S3=(3+1,2+1):** if its triple offset
  is >=7/50, then k>=4. The branch k=3
  now requires both triple offset <7/50
  **and** the two-square side on the
  2+1 axis to have offset <2/5.
* **S4=(2+1,2+2):** retains the exact
  candidate equality; this triple theorem
  has no direct consequence for S4.

If S1's triple side of type 3+1 has the
exceptionally small offset <7/50,
its sole opposite far-side square has
transverse center coordinate strictly
smaller than 9/50 in magnitude, by the
orientation-free cap center-height bound.

All these conclusions prune **regions in
the continuous central-center/outer-count
parameter space**, not just symbolic
combinatorial assignments. The exact
unrestricted target R8>=Rhat remains OPEN.


## 7. Complete k=7 rejection in S1 **and** S2

The latest exact angular-cap theorems eliminate **two
entire outer-center macro-branches** without presuming
any square angles or actual contacts:

* HUMAN_S1_NO_SEVEN_OUTER_CENTERS.md proves
  **S1/k=7 impossible**, for every central
  offset, by a two-case far-singleton/angular
  saturation inequality. When the 3+1 triple
  offset h>=7/50, the U cap center rays
  begin beyond atan(9/20), while the distant
  D singleton stays within atan(12/29)
  of the negative y axis. When h<7/50,
  its tighter |transverse|<9/50 lane
  moves the D singleton even closer
  to that axis. In either case all seven
  hypothetical outer rays lie in an arc
  shorter than 6*(pi/4-1/500), contradicting
  the outer-center pair separation theorem.
* HUMAN_S2_NO_SEVEN_OUTER_CENTERS.md proves
  **S2/k=7 impossible for EVERY |t|<5/24**,
  improving the earlier partial |t|>=1/8
  conclusion. Split the 2+2 central offset
  at |t|=1/10. For small displacement,
  the sharp one-square cap envelope gives
  polar elevations >atan(5/4) and >pi/4
  on the farther/nearer opposite caps.
  For larger displacement, use
  >atan(33/20) and >atan(2/3).
  Their sums exceed pi/2+3/250 by
  exact arctangent identities and one
  integer square comparison. Therefore
  all seven outer rays would lie in
  an arc shorter than 6*(pi/4-1/500),
  again impossible.

The updated coarse classification of the
**all-seven-single-side** statuses is:

    S1=(3+0,3+1): k=3,4,5,6 retained;
    S2=(3+0,2+2): k=4,5,6 retained;
    S3=(2+1,3+1): k=4,5,6,7 retained;
    S4=(2+1,2+2): k=4,5,6,7 retained,
                    including exact k=7
                    candidate equality.

Additional central-offset restrictions for
k=3,4 in S1--S3 appear in section 6 and
HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md.

This does not imply any complete all-orientation
eight-square lower bound: outer **paths with
noncentral inner-center attachments** remain,
as do D1/D2 and the equality-bearing S4.


## 8. New full macro-cell exclusions: S2/k=3 and S4/k=3

[HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md)
establishes a new **entire k-cell exclusion** that supersedes
the earlier conditional k=3 offset-pruning rows for S2 and S4.
It uses the existing strict outer-center angular gap and
a new mixed inner/outer angular exclusion to prove that six
distinct squares cannot simultaneously supply:

* two **inner** centers in one positive whole central-side cap;
* two **inner** centers in a perpendicular positive cap
  of offset \(h>7/24\);
* two **outer** centers in its opposite cap of offset \(1-h\).

This forbidden six-square configuration eliminates the whole
exclusive S2/k=3 cell, and the whole exclusive S4/k=3 cell,
**without any central-coordinate exception**. In each case the
two outer far-side members and the remaining total \(k=3\)
force exactly the requisite four inner centers on perpendicular
sides; S4's opposite 2+1 singleton is the third outer center.

The latest allowable k values therefore are:

| All-single-side type | k still not globally excluded |
| --- | --- |
| S1=(3+0,3+1) | **3,4,5,6** |
| S2=(3+0,2+2) | **4,5,6** |
| S3=(3+1,2+1) | **4,5,6,7** |
| S4=(2+1,2+2) | **4,5,6,7** |

The actual S4/k=7 sharp equality branch is deliberately
preserved. These are outer-count/status **necessary conditions**,
not a classification of realizable packings or a proof of
the unrestricted sharp lower bound.


## 9. New five-square fan obstruction: the S3/k=3 upper-offset strip is eliminated

The arbitrary-frame
[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
theorem excludes five **distinct** whole-side-cap squares
consisting of two R-inner, two perpendicular U-inner,
and one additional R-outer whenever
\[
h_R>17/200,\quad h_U\ge21/100.
\]

Because any exclusive S3=(3+1,2+1) configuration
with exactly k=3 exterior outer centers has
**exactly** those five R/U center statuses,
the entire S3/k=3 region with \(h_U\ge21/100\)
is **impossible** (no frame, contact graph or
central coordinate exception). The remaining S3/k=3
offsets satisfy
\[
17/200<h_R<13/100,\qquad 17/200<h_U<21/100.
\]

[HUMAN_S3_K3_REMAINING_TWO_LANES.md](HUMAN_S3_K3_REMAINING_TWO_LANES.md)
gives the exact further two-ray classification:
the outer R member's center-ray angle is
in \((-5\pi/36,-2\pi/45)\) **or**
\((7\pi/36,13\pi/45)\), and the two distant
L,D singletons obey
\(|p_L.y|<3/20\), \(|p_D.x|<11/32\).
These are genuine continuous center-position
constraints, not a proof that the two surviving
sectors are geometrically feasible.

For S1/k=3, if the U triple has an opposite
D singleton and its offset \(h_U\ge21/100\),
the perpendicular R triple must have
\(h_R\le17/200\), or the same five-square
obstruction applies. The remaining S1/k=3
branch is **not** fully eliminated.

The outer-center count table in section 8
remains **unchanged**: S1 k=3..6,
S2 k=4..6, S3 k=3..7 and S4 k=4..7.
This theorem removes an entire **continuous
subregion** within S3/k=3, not an entire k-cell,
and does not alter the 3,995,040 purely
symbolic separator-status assignment total.
The S4/k=7 equality realization is untouched.


## 10. Latest stronger continuous-domain restrictions (October 12)

The following **supersede** the earlier weaker offset and
angular interval bounds while preserving every original
status/outer-count hypothesis.

**Exclusive S2=(3+0,2+2), nearer 2+2 pair both inner.**
[HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md](HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md)
reduces its right triple offset from
\(h_R<1/10\) to the stronger **strict**
\(0<h_R<1/20\). The previously proved center-count
conclusion is **k=4 exactly**. Also
[HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md](HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md)
gives the four signed x-center placements
\[
x_{U_-}<-9/25,\quad x_{U_+}>9/25,\qquad
x_{D_-}<-29/100,\quad x_{D_+}>29/100.
\]
The far D polar-elevation theorem works
for a whole cap of offset \(h_D\ge5/8\) at
the stated n=8 disk ceiling. It provides a
strict \(>60^\circ\) center elevation for
all square frames, without assuming any
actual edge contact.

**Exclusive S3=(3+1,2+1), k=3.**
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
improves the old \(h_U<21/100\) bound to
the stronger \(h_U<1/5\). The remaining
offset rectangle is
\[
17/200<h_R<13/100,\qquad17/200<h_U<1/5.
\]
The far D singleton satisfies \(|p_D.x|<13/40\);
the L singleton still satisfies \(|p_L.y|<3/20\).
[HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md)
further sharpens the sole R outer-center ray to
the **two** strict alternatives
\[
-\pi/9<\psi<-2041/10500
\quad\text{or}\quad
311/500<\psi<8959/10500.
\]

All these are **genuine continuous necessary conditions**,
not reductions of the independently counted 12-status words
or a claim that the remaining positions realize a packing.
In particular **S2/k4** and **S3/k3** are still open.
The complete S2/k3 and S4/k3 exclusions established
earlier remain valid, and the S4/k7 exact candidate
equality case is untouched.

The unrestricted optimality inequality
\(R_8\ge\widehat R\) and the Lean handoff remain OPEN.


## 11. Latest S3/k=3 correction: only the positive R-outer ray survives

**Supersedes section 10's two-sector alternative for S3/k=3.**

[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md)
proves the **entire negative outer-R center sector**
is impossible, via an iterated exact mixed
inner/outer center-distance angular bound and
the R-minus inner center's mandatory whole-side
normal projection.

Consequently the only **currently unexcluded**
S3/k=3 outer-R ray is
\[
\boxed{311/500<\psi<8959/10500.}
\]
In particular its actual *center* has positive x
and y coordinates. This does **not** mean the
whole rotated R square lies in an open origin quadrant.

[HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md](HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md)
uses the surviving positive sector to force
the far D singleton's actual *center* strictly
to the left of the vertical origin diameter:
\[
\boxed{-13/40<x_D<0,\qquad y_D<0.}
\]
The full S3/k3 branch remains unresolved in
\[
17/200<h_R<13/100,\qquad
17/200<h_U<1/5,
\]
with the above angular/center-sign restrictions.

This removes a **whole continuous angular sector**
without decreasing the purely symbolic 12-status
assignment count or eliminating S3/k3 altogether.
S4/k7 exact equality remains valid, and
the unrestricted \(R_8\ge\widehat R\)
is still OPEN.


## 12. Complete elimination of the S3/k=3 parent macro-cell

**This supersedes every earlier 'still-open S3/k=3' rectangle,
ray sector and far-singleton note in sections 7–11.**

[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md)
proves that the **entire exclusive S3=(3+1,2+1), k=3 case
is impossible**, with no angular or central-offset exception.
It combines the earlier rigorous single **positive** outer-R
ray restriction with a new hand proof of the positive-y
inner R square's center reserve:
\[
y_{R_+}>49/500.
\]

Since the sole outer R square is **R-only**,
it cannot be wholly beyond the central U side.
Its vertical center is therefore below
\(h_U+\sqrt2/2<227/250\), while its positive
ray \(311/500<\psi<8959/10500\) and outer radius
\(<283/200\) imply \(1/2<q_x<230079/200000\)
and \(q_y>1/2\). The inner R+ center has
\(117/200<p_x<1,\ 49/500<p_y<1\). Hence
\[
|q-p_{R_+}|^2
<1-\frac{969139759}{40000000000}<1,
\]
contradicting their mandatory center distance
at least one. All exact rational endpoint
comparisons are audited in
[verify_s3_k3_global_exclusion.py](verify_s3_k3_global_exclusion.py).

The **new current exclusive D0/S=7 outer-center queue** is:
\[
\begin{array}{ll}
{\rm S1}:&k=3,4,5,6,\\
{\rm S2}:&k=4,5,6,\\
{\rm S3}:&k=4,5,6,7,\\
{\rm S4}:&k=4,5,6,7.
\end{array}
\]
The S4/k=7 sharp seven-outer equality construction
is retained; no whole status class has been
proved impossible, and the unrestricted radius
inequality \(R_8\ge\widehat R\) remains OPEN.


## 13. S2 nearer-U pair cannot both have inner centers (complete closure)

**This supersedes all earlier statements treating S2's
'near-U both inner, k=4, h_R<1/20' as a still-open
geometry subcase.**

[HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
proves an exact arbitrary-frame **contradiction**
from two inner centers in the nearer U cap
of an exclusive S2=(3+0,2+2) arrangement.
The prior outer-center angular order and
inner R center placement force the positive
outer R center ray into
\(43/100<\psi_2<31/50\).
The positive-x inner U center is constrained
to \(9/25<x<31/50,\ 79/100<y<47/50\).
A short four-rational-endpoint convexity
comparison forces their squared center distance
strictly below \(4923651/5000000<1\).
The two labels are distinct packed unit squares,
so their centers must be at least one apart.
Hence **the entire near-U both-inner case
is impossible** for every offset and every k.

This leaves, for exclusive S2:
* k=4 with **exactly one** outer U-center and
  exactly one outer R-center (plus the two
  far-D outer centers);
* k=5,6 with **at least one** outer U-center,
  and admissible additional outer R-center
  allocations.

These allocations are necessary, not
realizability statements; S2 itself is not
proved impossible.

The earlier complete S3/k=3 exclusion
in section 12 remains valid. The current
exclusive D0/S=7 k queue is unchanged
(S1 3..6; S2 4..6; S3 4..7;
S4 4..7), but the genuine *continuous
inner/outer subcases* have shrunk.
The real S4/k=7 sharp equality remains
untouched and unrestricted
\(R_8\ge\widehat R\) is still OPEN.


## 14. High 2+2-cap center norms prune both S2/k4 and S4/k4 near the center

[HUMAN_TWO_OUTER_HIGH_CAP.md](HUMAN_TWO_OUTER_HIGH_CAP.md)
supplies another new arbitrary-frame cap fact:
two distinct whole squares in an outward cap
of offset \(h\ge97/200\), within
\(R^2\le9789/2500\), **must both have
outer centers**. It is proved analytically
from the sharp one-square cap envelope and
a center-distance contradiction with exact
margin \(543/200000>0\).

For either exclusive side-status class
**S2=(3+0,2+2)** or
**S4=(2+1,2+2)**, let t denote C's
signed center coordinate along the 2+2 axis.
If \(|t|\le3/200\), *both* opposite 2+2
caps have offset at least 97/200, hence
all four members of that axis have outer
centers. The perpendicular axis contributes
at least one **distinct** outer label.
Thus \(k\ge5\), and the complete
closed strip \(|t|\le3/200\) is excluded
from **both S2/k=4 and S4/k=4**:
\[
\boxed{\text{S2/k4 or S4/k4}\ \Longrightarrow\
|t_{2+2}|>3/200.}
\]

This improves the signed continuous center
domain but does **not** exclude the full
k=4 macro-cells or alter the candidate-bearing
S4/k7 equality case. The current completed
parent exclusions are S2/k3, S3/k3,
S4/k3, and S2 with *both nearer-U*
centers inner. All other listed cells
still need additional global geometry.


## 15. An additional S1/k3 closed offset subregion

The *five-square* local theorem
[HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md](HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md)
requires only a R triple with two inner
and one **R-only** outer center, two **distinct**
U inner squares, and both whole-cap offsets
strictly greater than \(17/200\).
It does not require S3-specific far
singletons or contact assumptions; its
geometric proof is independently valid.

Applied to **exclusive S1/k3**, normalize
the 3+1 triple to R and its far singleton
to L, and normalize the 3+0 triple to U.
The L singleton and one outer label from
each triple exhaust k=3, forcing **two
inner centers per triple**. The existing
opposite far-singleton cap envelope
gives \(h_{31}>17/200\); the local
five-square theorem therefore excludes
\[
\boxed{h_{30}>17/200.}
\]
The surviving 3+0 side offset is
\(0<h_{30}\le17/200\). When the
3+1 triple offset also satisfies
\(h_{31}\le1/10\), the older
perpendicular-triple low-offset rectangle
forces the stronger \(h_{30}<1/16\).

This new **continuous region exclusion**
does not globally reject S1/k3, S1,
or any legitimate S4/k7 equality packing.


## 16. Stronger S1/k3 exclusion: the 3+0 triple offset is strictly below 1/16

**This supersedes section 15's weaker bound
\(h_{30}\le17/200\), and the earlier *conditional*
\(h_{30}<1/16\) subcase restricted to
\(h_{31}\le1/10\).**

[HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md](HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md)
strengthens the local five-square all-frame
R-only obstruction: a cap of three actual
square labels at \(h_R>17/200\), with **two
inner, one R-only outer**, cannot coexist
with two other distinct inner-center whole
squares in a perpendicular upper cap at
\[
\boxed{h_U\ge1/16}.
\]
The proof lowers the older \(17/200\)
perpendicular threshold using three
exact mixed-center angular gaps, including
a new \(>59/100\)-radian gap at inner
radius \(>9/16\) and a sharper
\(>779/1000\)-radian gap when the
R-minus inner center's radius is forced
above \(9/10\). Both polar alternatives
for the outer R center lead to strict
unit-center-distance contradictions.

Apply the theorem to **exclusive S1/k=3**,
with the 3+1 triple normalized to R and
its opposite far singleton L; the
perpendicular 3+0 triple is U. The far
L singleton is outer, and both triples
have exactly two inner and one outer
members. The 3+1 R offset is
\(h_{31}>17/200\). All five selected
R and U inner labels are distinct,
and the outer R is genuinely R-only.

Therefore
\[
\boxed{\text{exclusive S1/k=3 requires }
0<h_{30}<1/16.}
\]
This is uniform over the entire allowed
3+1 offset range: **there is no longer
an \(h_{31}>1/10\) exception** to
the \(1/16\) restriction.

The remaining very-small-offset
S1/k3 continuum is still open.
This does not rule out S1 with higher
outer counts, the known S4/k7 sharp
equality construction, or prove the
unrestricted \(R_8\ge\widehat R\).


## 17. Additional S1/k3 signed far-singleton side exclusion

[HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md](HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md)
proves the entire **far singleton transverse
center-sign** subcase incompatible with the
perpendicular 3+0 triple's outward direction
is impossible.

Normalize exclusive S1/k3 as
R=3,L=1,U=3,D=0; the far L singleton
has center \(p_L=(x_L,y_L)\).
Then necessarily
\[
\boxed{y_L<0.}
\]
This strict sign is *relative to the
positive U triple direction*: the
far singleton center lies on the
opposite side of the horizontal origin
diameter. The proof uses the existing
four-inner-center fan and the strict
pairwise mixed inner/outer angular
separation. If \(y_L\ge0\), the
northwest U-inner ray must be below
\(7\pi/9\). Three successive
inner-ray gaps \(>\pi/3\) then force
the northeast and right-inner rays into
strict smaller sectors. The outer R
ray has neither a permitted negative
placement nor a permitted positive
placement without violating the
R-only cap and center separation
conditions.

This supplements the **uniform**
strict 3+0 offset restriction
\[
\boxed{0<h_{30}<1/16}
\]
from [HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md](HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md).
The *remaining* S1/k3 case with both
conditions is still OPEN; no actual
eight-square packing has been constructed
there. The real equality-bearing
S4/k7 branch is unaffected, and
\(R_8\ge\widehat R\) remains unproved.


## 18. Quantitative far-singleton S1/k3 transverse clearance

The completed signed-center theorem is sharpened by
[HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md](HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md).
Normalize S1/k3 to R=3,L=1,U=3,D=0.
The far L singleton's actual center
\(p_L=(x_L,y_L)\) now obeys the exact
**strict transverse interval**
\[
\boxed{-3/20<y_L<-1/75.}
\]
The upper magnitude bound comes from
the sharp one-square far-left cap envelope,
while the **new negative clearance**
rules out \(-1/75\le y_L<0\).
Its proof revisits the four-inner
angular fan with a strictly positive
\(1/100\)-radian far-L polar slack,
then excludes both possible R-outer
ray placements by the same exact mixed
center-distance obstructions. The new
arithmetic margins are independently
checked in
[verify_s1_k3_far_singleton_clearance.py](verify_s1_k3_far_singleton_clearance.py).

Together with the stronger uniform
3+0 offset restriction from section 16,
the currently necessary S1/k3 region has
\[
17/200<h_{31}<13/100,\qquad
0<h_{30}<1/16,\qquad
-3/20<y_L<-1/75.
\]

These are **actual whole-cap/center
necessary inequalities**, not a proof
the remaining S1/k3 continuum is feasible
or impossible. S1 with larger k, other
S2/S3/S4 classes, D1/D2, and the
unrestricted sharp lower bound
\(R_8\ge\widehat R\) remain open.


## NEW computer-to-hand 37/100 mixed cap exclusion (2026-10-12)

The numerical exploratory cap-pair optimizer in
[computer_two_square_cap_probe.py](computer_two_square_cap_probe.py)
was used only to select an analytic target. Its local
minimum values are **not** global proof or feasibility
certificates. The reproducible details and proof
roadmap are in
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md).

The new **rigorous** exact
[HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md)
extends the previous one-square arbitrary-frame
sharp cap center envelope from \(h\ge2/5\)
to \(h\ge37/100\) at the justified
search ceiling \(R^2\le9789/2500\).
Its written proof is a negative-frame
concavity reduction plus an affine positive-frame
polynomial check on **four rational parameter
vertices** (tangent minimum \(553/78125>0\)).

Therefore
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md)
**eliminates every same-weak-sign center
mixed inner/outer whole-cap pair** at
\(h\ge37/100\), for arbitrary square
orientations, by a strict center-distance
contradiction
\[
|p-q|^2<1989/2000<1.
\]

For the exclusive S2=(3+0,2+2) **k=4**
branch, the current necessary geometric
three-cell queue is:
A: \(37/100\le h_U<97/200\), opposite signs;
B: \(7/24<h_U<37/100\), opposite signs;
C: \(7/24<h_U<37/100\), weak same signs
(with one whole-quadrant owner and a
compulsory nontrivial frame defect).
The entire old C offset strip
\([37/100,2/5)\) is now impossible.

**Important limitations:** S2/k4 cells
A, B and C are each still OPEN in
their residual intervals. The numerical
conjecture \(R^2\ge(h+1)^2+9/4\)
for all mixed same-sign pairs at
\(h\ge7/24\) remains unproved.
The equality-bearing S4/k7 packing,
D0 corner-only, D1/D2 and all
unrestricted \(R_8\ge\widehat R\) tasks
are unchanged and remain appropriately
open.

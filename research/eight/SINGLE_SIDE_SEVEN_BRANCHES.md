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
    S3=(2+1,3+1): k=3,4,5,6,7 retained;
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
| S3=(3+1,2+1) | **3,4,5,6,7** |
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

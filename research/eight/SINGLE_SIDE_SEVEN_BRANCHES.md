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

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

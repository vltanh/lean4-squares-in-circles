# The three surviving double-side macro-branches

**Purpose.** After the hand-proved sector and sharp
corner-cap rejections, the 12-status classification
of seven exterior unit squares reduces to **three
exhaustive double-side macro-branches**. Each still
contains continuous square centers, orientations
and mutual pair separators. This is a finite
proof roadmap, not a claim of R8>=Rhat.

Work in C's own horizontal/vertical frame,
where the unique central square C has center
(a,b), |a|,|b|<1/2, and the disk has

    R^2 <=q_plus=9789/2500<2257/576<98/25.

An exterior square is counted as RU, RD, LU
or LD precisely when **its whole square**
lies beyond both corresponding adjacent
central side supporting lines. Other
statuses are four single-side and four
corner-only types (one per corner).

## Macro-branch D0: no double-side square

All seven exterior squares are assigned
to either one central-owned side separator
or to one corner-only own-axis separator.
At most four are corner-only, so **at least
three distinct** exterior squares have
a single central-owned side separator.

This branch is forced whenever

    |a|<=1/10 and |b|<=1/10,

by the sharp one-square corner-cap inequality:
a whole square beyond two central sides
would need squared radius at least
2*(7/5)^2=98/25>q_plus.

The branch can also occur for other central
positions; being near the origin is a
sufficient condition, not a characterization.
All four individual side counts remain
bounded by three, and opposite 3+2
populations remain forbidden.

## Macro-branch D1: exactly one double-side square

After reflection call its status RU.
The sharp corner-cap theorem forces

    R^2>=(3/2+a)^2+(3/2+b)^2,
    a+b<-487/2500.

It also forces each signed coordinate
a,b<5/24, because if either were
>=5/24 the corresponding corner-cap
term would be >=(41/24)^2 while
the other term would exceed one.
The other six exterior squares have
only four single-side types or
four corner-only types (the latter
at most one per corner). At least
two of those six must be side-separated:
seven total distinct exterior units
and at most four corner-only.

When any central side serves three
whole squares, its opposite side
can have at most one, and that
singleton must have a **single-side**
status with transverse center
coordinate in (-1/2,1/2).

## Macro-branch D2: two adjacent double-side squares

Opposite double statuses RU+LD and RD+LU
are impossible. Thus up to reflection
the only two-double arrangement is RU+RD,
sharing the right central side.

The sharp corner-cap bound and the
opposite-cap 2+2 bound force

    -1/2<a<-5/24,         |b|<5/24,               (1)
    N_R>=2,               N_L<=1.               (2)

The strict central-coordinate inequalities
follow from HUMAN_SHARP_DOUBLE_CORNER_CAP.md,
Theorem 7; they are not numerical estimates.
There can be **no third** double-side status.

At least one of the other five exterior squares
is side-separated, since four corner-only
squares are the maximum. If N_R=3, its opposite
left side has offset >17/24; every left-cap
singleton crosses the horizontal diameter
and has no adjacent double status.
All remaining units require actual pair
separations, and corner-only exceptions
may appear at distinct central corners.

The rotated/reflected versions of D2 share
the same geometry: **exactly one central
coordinate has magnitude >5/24** along
the common side's direction, and the
other has magnitude <5/24.

## How to combine with the outer-center graph

Independently classify k, the number of
noncentral center norms >=1.
The existing bound gives 3<=k<=7.

* For k=3,4,5,6 the outer-induced actual
  contact graph is paths and isolates,
  with near-center inner attachments
  retained in the full graph.
* For k=7 the outer-induced graph is
  paths/isolates or the full seven-cycle.
  The seven-cycle is realized by the
  exact sharp five-corner candidate,
  so **it cannot be rejected by existence**.

Do not multiply the 3 macro-branches by
5 k-categories and declare 15 independent
complete theorems: each cell still has
specific corner types, side populations,
side-frame orientations, nonadjacent pair
constraints and physical stress weights.
The classification is **exhaustive
combinatorially**, not a list of a
finite number of isolated configurations.

## Next proof gates

**D2** is the most tightly positioned:
its two diagonal cap squares, central
offset (1), and at most one opposite
side square should be tested against
the central square and the remaining
four/five exterior units first.

**D1** retains only one corner-cap member;
a sharp bound will require preserving
its two genuine side separators rather
than promoting every near-corner center
to a whole-cap assignment.

**D0** includes the fully centered central
square and candidate-like paths/rings
with only single-side and corner-only
separator assignments. It needs either
a global five-corner projected chain
or an equally sharp alternative bound.

The goal is to rule out every **radius
strictly below Rhat** in D0,D1,D2,
while allowing the candidate's
valid equality realizations. None of
the current discrete restrictions
establishes that final inequality.

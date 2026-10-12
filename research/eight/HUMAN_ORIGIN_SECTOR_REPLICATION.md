# Replication capacity of entire unit squares in rational-angle disk sectors

## Theorem (all orientations; exact rejection of adjacent double-side membership)

Fix the disk radius so that R^2 <= 98/25, and assume
any number m of interior-disjoint unit squares are
contained entirely in the intersection of D_R with
one **closed sector** whose vertex is the disk origin
and whose angular opening is at most 2*pi/k, where
k is an integer >=2.

Then necessarily

    k*m <= 7,         equivalently m<=floor(7/k).       (1)

In particular:

| Sector opening | k | Maximum number of entire unit squares |
| --- | ---: | ---: |
| 180 degrees | 2 | 3 |
| 120 degrees | 3 | 2 |
| 90 degrees | 4 | 1 |
| 72 degrees | 5 | 1 |
| 60 degrees | 6 | 1 |
| 360/7 degrees | 7 | 1 |
| 45 degrees or less | >=8 | **0** |

No square-frame assumption, common orientation, central contact,
circle contact, chosen separator, center membership or numerical
continuum certificate is involved.

**Central-square consequence.** Fix the unique origin-containing
unit square C of an eight-square packing with R^2<=9789/2500.
In C's side frame any other whole square served simultaneously by
two adjacent outward **central-owned side separators**, for example
R and U, lies in

    {x>=h_R>0, y>=h_U>0} intersect D_R

and hence lies entirely inside the 90-degree quadrant
{x>=0,y>=0}. The sector theorem therefore gives:

> For each of the four adjacent central-side pairs RU,RD,LU,LD,
> at most **ONE** exterior square can be served by both sides.

Thus in the twelve-status central-separator taxonomy, each of
the four double-side statuses has capacity **at most one**,
just as each of the four corner-only statuses does. This is a
new global combinatorial constraint independent of the original
cap h bounds; two different whole squares can never share one
adjacent double-side status at the search ceiling.

It is not claimed that a square served by just one central side
is entirely in a quadrant, or that corner-only squares lie
entirely in the quadrant of their centers. Therefore the
theorem must not be used to exclude two arbitrary square
**centers** from a quadrant.

## Hand proof

Rotate coordinates so the containing closed sector has angular
range [0,alpha], where alpha<=2*pi/k. Let
S_1,...,S_m be the packed unit squares entirely inside
that sector and D_R. Rotate every S_j about zero through
angles 2*pi*l/k, l=0,...,k-1.

The k rotated **closed sectors** have pairwise disjoint
open interiors: their angular intervals do not overlap,
and even if alpha<2*pi/k they leave empty gaps.
For each l, the m rotated squares have disjoint open
interiors because rigid rotation preserves nonoverlap.
For different l, their open interiors lie in disjoint
open angular sectors; any common boundary rays can
contain closed-square contacts but not an open overlap.

Rigid rotations around the origin preserve D_R exactly.
Therefore the construction yields k*m labeled unit
squares with pairwise disjoint open interiors, all
inside D_R. (Even coincident copies are impossible:
each square has nonempty open interior lying in its
own rotated sector.)

Every square lies inside a closed sector with opening
at most pi, hence its open interior cannot contain
the origin: any sufficiently small disk centered at
the origin extends outside that sector. Therefore
none of the k*m squares contains zero in its open
interior.

If k*m>=8, select any eight of these squares.
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md proves, entirely
analytically, that **every** packing of eight unit
squares in a disk with R^2<=98/25 contains a
unique square whose *open* interior contains the
origin. The selected eight contradict that theorem.

Hence k*m<=7, proving (1) and every table row.
The central square application follows because
the two adjacent outward central sides are at
strictly positive distances h_R,h_U from zero.
Membership beyond **both** makes the entire
square a subset of the corresponding origin
quadrant. Two such squares would contradict
the k=4 result. QED.

## What this actually eliminates

Unlike the already established semicircle result
(four whole squares forbidden), this theorem
removes **multiplicity** of an adjacent-side
central separator status: RU,RD,LU,LD can each
appear at most once. It also proves every packed
unit square omitting the origin has angular
shadow strictly wider than pi/4; if the shadow
had width at most pi/4, that square would be
entirely contained in a 45-degree origin sector,
contradicting k=8.

These are *whole-square* statements. An outer
center in a 45-degree sector may belong to a
square whose angular shadow extends outside it.
No existing seven-outer actual-contact ring or
near-center corner-owned exception is thereby
excluded. The unrestricted sharp inequality
R8>=Rhat remains open.

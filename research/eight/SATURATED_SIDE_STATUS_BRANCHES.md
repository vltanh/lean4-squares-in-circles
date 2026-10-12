# Saturated central-side populations force almost every separator status

**Status:** exact combinatorial-geometric theorem for
eight freely oriented unit squares in the established
sharp-radius search range q<=9789/2500.
It uses only the already proved semicircle, corner-only
capacity, opposite cap and double-corner restrictions.
It removes **no** surviving radius branch outright;
instead it proves exact status structure in the
highest-population branches, with at most one corner-only
exception. No numerical geometry optimization is used.

## 1. The occupancy identity and a universal saturation bound

Fix the unique central square C and its signed
side frame R,L,U,D. Each of the seven other squares
has exactly one of the 12 mutually exclusive
statuses of FINITE_PATTERN_TAXONOMY.md:

* single side: four types, contributing one
  central-owned *whole-square* side membership;
* double adjacent sides: four types,
  contributing exactly two memberships;
* corner-only: four types, contributing zero.

Let n_1,n_2,n_0 be the numbers of squares in
these three groups, so

    n_0+n_1+n_2=7.                                  (1)

Let N_R,N_L,N_U,N_D be the side populations,
counting a double member in both its sides,
and put

    S=N_R+N_L+N_U+N_D=n_1+2*n_2.

Subtracting (1) gives the exact integer identity

    **n_0=n_2+7-S.**                               (2)

The cap bounds forbid a 3+2 population on
opposite sides, and each side has count <=3.
Therefore both opposite pairs have total
population at most four:

    N_R+N_L<=4,      N_U+N_D<=4.

Consequently

    **S<=8.**                                      (3)

The double-corner cap theorem says at most
two double statuses are populated and each
at most once, so n_2<=2.
The one-corner theorem gives n_0<=4.
Thus the number of corner-only exceptions
at fixed S is sharply bounded above by

    n_0<=min(4,9-S) for S>=7,

and the exact identity (2) is more useful
than the crude inequality in individual cases.

In particular:

    S=8 => n_2=1 or 2, n_0=0 or 1;
    S=7 => n_0=n_2<=2;
    S=6 => n_0=n_2+1<=3.                             (4)

These are **necessary status classifications**;
we do not assert that all counts are realized
by actual eight-square packings.

## 2. The only three coarse shapes at S=8

At S=8, both opposite side pairs must have
their *maximum* total count four.
The cap theorem permits only two such
unordered pairs:

    3+1,       2+2.

After exchanging the central axes and
reflecting signs, there are exactly three
coarse possibilities:

    Type A: (3+1,3+1),
    Type B: (3+1,2+2),
    Type C: (2+2,2+2).                            (5)

The rest of the proof identifies their
fine separator statuses.

### Type A: two perpendicular triple sides, no corner-only members

Reflect so N_R=N_U=3 and N_L=N_D=1.
The triple-side vs opposite double rule
of HUMAN_SHARP_DOUBLE_CORNER_CAP.md, Theorem 5,
gives:

    triple R forbids LU,LD;
    triple U forbids RD,LD.

Thus the **only** permissible double type
is RU. Since S=8 but there are only seven
exterior squares, identity (2) forces
n_2>=1. Hence **exactly one RU square**,
no corner-only squares, and every
other exterior square has a single-side
central-owned separator.

The seven statuses are thereby *fully forced*:

    1 RU, 2 R, 1 L, 2 U, 1 D.                  (6)

This is up to the same central frame symmetries
as in (5). It is a necessary exact
classification of the entire Type A branch,
not a proof that Type A can actually fit.

### Type C: both axes 2+2, no corner-only members

Suppose N_R=N_L=N_U=N_D=2.
Two double statuses cannot be opposite by
the sharp double-corner theorem. If they
were adjacent, they would share some
central side; its *opposite* side here
has two whole squares, contradicting
Theorem 3 of that note. Hence n_2<=1.

Again S=8 forces n_2>=1, so n_2=1
and n_0=0. All seven exterior squares
have central-owned separators, and
exactly one is double.

Up to central frame symmetries put
the single double status at RU.
The seven statuses are then

    1 RU, 1 R, 2 L, 1 U, 2 D.                  (7)

No corner-only exception survives Type C.
This is an exact fine-status reduction;
the implied seven-square configuration
could still have arbitrary orientations
and additional separations between its members.

### Type B: either no corner-only or exactly one

Reflect so the first opposite pair is
R=3, L=1 and the second is U=D=2.
Triple R forbids LU,LD. Thus any occupied
double statuses are among RU,RD, and
their two types share side R.

Identity (2) leaves exactly two
possibilities:

* n_2=1,n_0=0: **one** of RU,RD is
  occupied, all six other exterior
  squares have single-side statuses.
* n_2=2,n_0=1: **both** RU and RD are
  occupied, and exactly one exterior
  square is corner-only, assigned
  to one of the four corners.

There are no other Type B fine-status
branches. The other seven side counts
determine the multiplicities of each
single-side status by subtraction.

If the two doubles RU,RD occur,
their common right side has positive
offset h_R<7/24 and the offset
dichotomy of TRIPLE_DOUBLE_STATUS_PRUNING.md
applies:

    h_R<1/4  or  |b|<1/29,                        (8)

where b is the perpendicular central-center
coordinate. The triple R additionally
forces a<-5/24, and the opposite L single
forces a> -83/200 by
HUMAN_ALL_SIDE_OFFSET_INTERVALS.md.

These are precise real-variable domains
for the **sole** S=8 branch retaining
a corner-only exception.

## 3. Exact symbolic counts in the saturated case

Among the 3,995,040 labeled separator-status
assignments surviving the current finite
filters (TRIPLE_DOUBLE_STATUS_PRUNING.md),
the S=8 branch consists of exactly

    20,160 with n_2=1 and n_0=0,
    80,640 with n_2=2 and n_0=1,
    --------------------------------
    100,800 total labeled status assignments.

Each figure is a finite multinomial sum
`sum_m 7!/(product m_status!)` over the
status vectors satisfying equations
(1)--(5) and the forbidden double/triple
combinations. Nothing is inferred about
their continuous geometric realizability.

For comparison the exact labeled counts
stratified by total side memberships are

| S | Surviving symbolic assignments |
| ---: | ---: |
| 3 | 53,760 |
| 4 | 372,960 |
| 5 | 1,118,880 |
| 6 | 1,534,400 |
| 7 | 814,240 |
| 8 | 100,800 |
| **Total** | **3,995,040** |

The table follows directly from the
same 12-variable factorial sum;
its entries add to 3,995,040.
It is a count of **words**, not proof
that these are independent packing
patterns or that they all survive
the continuous separator constraints.

## 4. Practical implication

The most saturated side-count branch
S=8 is no longer a high-dimensional
corner-exception combinatorial problem.

* In Type A, two perpendicular triples
  force exactly one shared-corner double
  and **no corner-only exceptions**.
* In Type C, two opposite 2+2 pairs
  force exactly one double and
  **no corner-only exceptions**.
* Type B is the **only** S=8 shape
  with a corner-only exception at all:
  it then has exactly one, and two
  adjacent double types are forced.

This does not prove R>=Rhat in those
branches. It tells a sharp geometric
proof exactly which remaining seven
square separator roles must be
considered, rather than allowing
arbitrary choices among 12 statuses.

# Every two-double-corner branch has an own-axis corner exception

## Exact theorem at the n=8 search ceiling

Fix the unique central square C of an eight-square packing in
the disk q=R^2<=9789/2500. Use C's own horizontal/vertical frame.
For the seven exterior squares, each has exactly one of the
twelve central separator statuses described in
FINITE_PATTERN_TAXONOMY.md: one central side; two adjacent
central sides; or an own-axis corner-only separator.

Write D for the number of squares occupying a two-adjacent-side
status, E for the number of corner-only exceptions, and
S=N_R+N_L+N_U+N_D for total whole-square central side memberships.
Since there are seven exterior squares, the identity is

    E=D+7-S.                                           (1)

The existing corner-cap theorem gives D<=2; if D=2, the two
double statuses are adjacent and share a central side.

**New forced-corner conclusion.** Whenever D=2,

    E>=1.                                              (2)

Moreover, if the common side serves only those two
double-status squares (population exactly two), then

    E>=2.                                              (3)

Consequently **no D2 branch is wholly central-side
separated**: at least one of its seven exterior
squares must use an own-axis corner-only separator,
and when the common side is not a triple there must
be at least two such exceptions.

These are actual whole-square separator statements,
not assertions about the signs of the square centers
or whether any square touches C.

## Hand proof

By symmetry suppose the two occupied double types
are RU and RD, sharing the right side. Theorem 5 of
HUMAN_SHARP_DOUBLE_CORNER_CAP.md rules out:

* population N_U=3, because a triple upper side
  forbids the double type RD;
* population N_D=3, because a triple lower side
  forbids the double type RU.

Thus N_U,N_D<=2. Theorem 3 of that note gives
N_L<=1, since RU+RD is occupied. The universal
semicircle-cap theorem gives N_R<=3.
Therefore

    S=N_R+N_L+N_U+N_D <=3+1+2+2=8.              (4)

Inserting D=2 and S<=8 into (1) yields

    E=9-S>=1,

proving (2). If N_R=2, the strengthened
bound S<=2+1+2+2=7 gives

    E=9-S>=2,

proving (3). Reflections and quarter turns handle
each other pair of adjacent double types. QED.

## Exact status-count bookkeeping (not realizable packing counts)

After imposing all previously proved Boolean restrictions
listed in TRIPLE_DOUBLE_STATUS_PRUNING.md, there remain
exactly 3,995,040 **labeled status assignments**.
They are grouped as follows. D=0,1,2 is the number of
occupied double-side statuses, and the compulsory
corner-only count E in each cell is supplied by (1).

| Total side memberships S | D=0 | D=1 | D=2 |
|---:|---:|---:|---:|
| 3 | 53,760 | 0 | 0 |
| 4 | 211,680 | 161,280 | 0 |
| 5 | 231,840 | 806,400 | 80,640 |
| 6 | 82,880 | 967,680 | 483,840 |
| 7 | 7,840 | 322,560 | 483,840 |
| 8 | 0 | 20,160 | 80,640 |
| **Total** | **588,000** | **2,278,080** | **1,128,960** |

For reproducibility, write the twelve counts
m_R,m_L,m_U,m_D,m_RU,m_RD,m_LU,m_LD,
m_NE,m_NW,m_SE,m_SW, summing to seven. The
contribution of a multiplicity vector is exactly

    7!/(m_R! m_L! ... m_SW!).

Sum it over the finite vectors satisfying:
each corner-only and double type has multiplicity
at most one; all side populations <=3; no opposite
3+2 counts; no opposite double pair RU+LD or RD+LU;
no adjacent double pair when its common side's
opposite population >=2; and no triple side with
a double status on its opposite side. Group by
D=m_RU+m_RD+m_LU+m_LD and
S=m_R+m_L+m_U+m_D+2D.
This is an exact integer definition of every
displayed count, not a claim of a continuum
packing certificate.

## Priorities and real equality branch

In branch D0 (no double-side exterior square),
S=7 implies E=0: **all seven exterior squares
have exactly one central-owned side separator**.
The exact sharp five-corner candidate's standard
slider realization has this status (see
SHARP_CANDIDATE_SIDE_STATUS.md). Therefore this
no-double/no-corner branch **cannot be discarded**.

D1 has E=8-S: at maximal S=8 there are no
corner-only exceptions and precisely one
double-status square.

D2 has E=9-S>=1, and E>=2 unless the common
side has a triple population. Thus the
remaining D2 work is **intrinsically a
corner-only-separator problem**. A proof which
assumes every exterior square has a central
side separator cannot cover any D2 packing.

None of the combinatorial restrictions proves
R8>=Rhat. The true remaining task is to
derive the sharp geometric obstruction for
these continuous branches, preserving
candidate equality when present.

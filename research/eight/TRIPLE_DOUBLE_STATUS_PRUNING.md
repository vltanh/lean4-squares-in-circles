# Further exact pruning: triple sides, double corners, and center offsets

**Status.** Hand proofs and exact finite assignment arithmetic.
Valid for eight freely oriented unit squares with disjoint open
interiors in D_R, at squared radius q<=9789/2500.
The central square C contains zero in its open interior.
Work in its own side frame; write its center (a,b),
with |a|,|b|<1/2.

This note does not claim R8>=Rhat. It prunes status assignments
and continuous central-center regions. An 'R','U',etc side
membership always means **whole-square** central-owned
separator containment, not merely center sign.

## 1. A strict one-fifth signed-diagonal displacement from any double corner

For a square served by both central right and upper sides (RU),
the sharp arbitrary-frame corner-cap inequality from
HUMAN_SHARP_DOUBLE_CORNER_CAP.md is

    q >= (3/2+a)^2+(3/2+b)^2.                       (1)

Write s=a+b. The identity

    (3/2+a)^2+(3/2+b)^2
      = (3+s)^2/2+(a-b)^2/2
      >= (3+s)^2/2                                (2)

is exact. Because |a|,|b|<1/2 we have 3+s>2>0.
And q<=9789/2500<98/25 gives

    3+s <=sqrt(2*q)<sqrt(196/25)=14/5.

Hence

    **RU => a+b < -1/5.**                         (3)

Reflecting coordinate axes gives the **four exact tests**

    RU:  a+b < -1/5,
    RD:  a-b < -1/5,
    LU: -a+b < -1/5,
    LD: -a-b < -1/5.                             (4)

They improve the earlier linear bound -487/2500,
since -1/5=-500/2500 is strictly smaller.
They imply in particular that a double-side status requires
max(|a|,|b|)>1/10. They are strict at the whole
closed q_plus ceiling; no angle sampling is involved.

## 2. A narrow remaining strip for two adjacent double statuses

Suppose RU and RD are occupied by *distinct* squares.
They share the positive right central side.
Put its signed distance from the origin

    h=1/2+a>0.

The same sharp one-square corner-cap bound for both
squares gives

    q >= (1+h)^2+(3/2+b)^2,
    q >= (1+h)^2+(3/2-b)^2.

Taking the larger gives the exact necessary restriction

    (1+h)^2+(3/2+|b|)^2<=q_plus.                  (5)

In particular h<sqrt(q_plus-9/4)-1<7/24,
so a< -5/24. This repeats the global pair
bound in HUMAN_SHARP_DOUBLE_CORNER_CAP.md.

Equation (5) also gives a useful **dichotomy**:

    RU and RD => either h<1/4,
                 or |b|<1/29.                  (6)

To prove it, suppose h>=1/4 and |b|>=1/29.
Then the left side of (5) is at least

    (5/4)^2+(3/2+1/29)^2
       =52709/13456
       =9789/2500+12929/8410000
       >q_plus,

a contradiction. Thus h>=1/4 forces |b|<1/29.
Reflections and quarter-turns give the identical
dichotomy for LU+LD, RU+LU and RD+LD,
using their own shared side and the perpendicular
central-center coordinate.

This does not exclude the two-double branch:
it either places the shared central side at offset
<1/4 or confines the center to a narrow
perpendicular strip of half-width 1/29. The
sign and offset are now exact one-variable
conditions for later sharp inequalities.

## 3. Triple-side incompatibilities eliminate 571,760 further assignments

Theorem 5 of HUMAN_SHARP_DOUBLE_CORNER_CAP.md proves
the following *whole-square* implication, stronger
than the 3+2 opposite-side count exclusion:

    triple R => no LU,LD double status,
    triple L => no RU,RD double status,
    triple U => no RD,LD double status,
    triple D => no RU,LU double status.           (7)

A short proof: three squares on a side of positive
offset h require q>=(1+h)^2+9/4. Since q<2257/576,
that offset must satisfy h<7/24. The opposite side
lies beyond offset 1-h>17/24. A square served by
that opposite side **and** either perpendicular side
would, by the sharp quadrant-cap bound, require

    q>(1+17/24)^2+1=2257/576>q_plus,

contradiction. This covers all four cases in (7),
without assuming that different corner types
correspond to different positive-stress edges.

**Exact count.** There are seven *labeled* exterior
squares, assigned one of the twelve mutually
exclusive statuses R,L,U,D; RU,RD,LU,LD; NE,NW,SE,SW.
For a count vector m=(m_1,...,m_12) with
sum m_i=7, its number of labeled realizations
as a purely symbolic status assignment is

    7! / (m_1! ... m_12!).                           (8)

Set side populations

    N_R=m_R+m_RU+m_RD,
    N_L=m_L+m_LU+m_LD,
    N_U=m_U+m_RU+m_LU,
    N_D=m_D+m_RD+m_LD.                              (9)

Apply the following filters to the integer vector m:
* every corner-only multiplicity <=1;
* each N is <=3, with no 3+2 opposite population;
* each double-side multiplicity <=1;
* no opposite double pair RU+LD or RD+LU;
* no adjacent double pair on a shared side
  whose opposite side population is >=2;
* the triple-side restrictions (7).

All are **necessary**, though they omit further
continuous geometry. Finite multiplication and
addition of the multinomial weights (8) gives:

| Successive necessary filter | Labeled assignments | Unlabeled multiplicity vectors |
| --- | ---: | ---: |
| Side caps + one corner-only square per corner | 8,551,760 | 3,540 |
| Double-side multiplicity <=1 | 6,663,440 | 2,644 |
| Opposite double-side exclusion | 4,808,720 | 2,172 |
| Two adjacent doubles vs opposite 2+2 | 4,566,800 | 2,060 |
| **Plus triple vs opposite double (7)** | **3,995,040** | **1,656** |

Thus the last row removes precisely

    4,566,800-3,995,040=571,760

previously surviving labeled assignments, or
2,060-1,656=404 previously surviving
multiplicity vectors. It removes about 12.5%
of the last row's labeled possibilities.
From the initial side/corner count, the reduction
is 8,551,760-3,995,040=4,556,720, over 53%.

**Reproducible arithmetic definition.** The counts do not
rely on a numerical geometry solver. Enumerate all
nonnegative integer vectors of length twelve with
sum seven, corner-only counts <=1, compute populations
by (9), discard those violating the explicitly
listed finite Boolean conditions, and add
the factorial quotients (8). Equivalently start
with the truncated coefficient generating function

    7! [z^7] (1+z)^4
        exp(z*(x_R+x_L+x_U+x_D))
        product_(XY in {RU,RD,LU,LD}) (1+z*x_X*x_Y),

with exponents x_R,x_L,x_U,x_D tracking side
populations; retain precisely the allowed monomials
and impose the pair-of-corners and triple rules.
The exponential is truncated to degree seven.
The first row replaces the last product with
exp(z*sum_(XY) x_X*x_Y), allowing repeated doubles.

The remaining **3,995,040 are not geometrically feasible
packing configurations**: they are only labeled
12-status words not yet eliminated by these exact
necessary conditions. They may represent an arbitrarily
large or empty continuous feasible set.

## 4. Two adjacent triple sides: only their shared double can remain

As a direct consequence of (7), if R and U each
serve three whole exterior squares, then all double
statuses except possibly RU are impossible:

* triple R forbids LU and LD;
* triple U forbids RD and LD;
* RU is the only unexcluded double status.

The analogous rule holds after any reflection or
quarter-turn. It does **not** mean RU must actually
occur, nor that six distinct squares can be placed
under the two triple side constraints.

## 5. Cases that must NOT be incorrectly rejected

The new rules do **not** exclude a corner-only
own-axis square and a double-side square assigned
to the same signed central corner: the latter is
wholly in an origin quadrant, while the former
is constrained by an oblique separator and may
extend across a central axis. Their incompatibility
does not follow from sector replication. This
specific finer pattern is not being discarded.

The 31 coarse four-side count profiles in
FINITE_PATTERN_TAXONOMY.md are still not reduced
by the integer-status filters alone. The reductions
are at the finer **status assignment** level, and
the exact signed-offset inequalities (4)--(6)
must still be combined with the other seven
squares in a full sharp-radius argument.

The unrestricted eight-square radius lower bound
R8>=Rhat remains OPEN.


## 6. Exact three-square witness: same-corner own-axis + double-side is NOT locally forbidden

The fine status rule cannot be sharpened by saying that a
corner-only NE square and a double-side RU square may not coexist
near the same central corner. Here is an exact counterexample
using three unit squares, strictly below the eight-square
search radius ceiling. It is **not an eight-square packing**.

Let the central standard square be

    C=[-9/10,1/10] times [-9/10,1/10],

so its northeast vertex is v=(1/10,1/10) and
zero is in the open interior of C.
Put e=(99/101,20/101), f=(-20/101,99/101).
Let S be the unit square of frame (e,f) centered at

    p_S=v+e/2-f/4=(323/505,-93/2020).

Finally take the axis-parallel unit square

    T=[1/10,11/10] times [11/20,31/20].

**Status of S.** Its center difference relative to C is

    p_S-p_C=(105/101,143/404),

while the sum of the horizontal or vertical
central/S half-widths is

    W=(1+99/101+20/101)/2=110/101.

Thus both central-owned separators fail strictly:
105/101<W and 143/404<W.
Nevertheless the northeast own-frame separator
holds with equality,

    e dot(p_S-p_C)=W.

Indeed v=p_S-e/2+f/4 lies on S's negative-e side
and is the northeast vertex of C, so C and S
physically touch only at this corner/side point.
Therefore S is genuinely **corner-only NE**.

**Status of T.** It lies wholly in
x>=1/10 and y>=11/20>1/10,
so it is genuinely **double-side RU** relative
to C. It has no interior overlap with C.

**Pair S,T.** The highest y coordinate of S is

    -93/2020+(119/101)/2
       =1097/2020,

whereas the lowest y coordinate of T is
11/20=1111/2020. Hence S and T are
strictly separated by a horizontal gap of 7/1010.

**Containment.** T's farthest vertex squared
norm is

    (11/10)^2+(31/20)^2=289/80<9789/2500.

C's farthest squared vertex norm is 81/50<289/80.
For S, |p_S|<7/10 follows from
|p_S.x|<13/20 and |p_S.y|<1/20;
every square vertex is within 1/sqrt(2)<3/4
of its center. Thus every point of S has norm
less than 7/10+3/4=29/20, whose square is
841/400<289/80.

All three unit squares therefore fit in
D_(sqrt(289/80)) with disjoint open interiors
and exactly the stated two distinct statuses.

This proves only **local three-square compatibility**.
It does not assert the existence of five additional
unit squares at the sharp eight-square ceiling.
Nevertheless a global exclusion of this finer
status combination must use the space required
by the *other five units*, not merely the
three-square separator geometry.

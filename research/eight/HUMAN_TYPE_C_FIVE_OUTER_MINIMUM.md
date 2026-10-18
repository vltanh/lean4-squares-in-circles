# Saturated Type C requires at least five outer square centers

## Theorem — a complete k=3,4 macro-case rejection

Assume an eight-unit-square packing in a disk with
R²<=9789/2500, with unique origin-containing central
square C. In C's own coordinate frame suppose the four
signed central-side whole-square populations all equal
two:

    N_R=N_L=N_U=N_D=2.                              (1)

Suppose there is exactly one exterior square with a
double-side separator, of status RU, and all other six
exterior squares have single central-side statuses.
These are **precisely** the fine statuses of saturated
Type C in SATURATED_SIDE_STATUS_BRANCHES.md, after
reflection and quarter-turn symmetry:

    RU, R, L, L, U, D, D.                            (2)

**Conclusion:** at least FIVE of the seven exterior
square centers have Euclidean norm >=1.

Thus **no Type C packing exists** in outer-center
macro-branches k=3 or k=4 of
FINITE_PATTERN_TAXONOMY.md. The remaining Type C
branches k=5,6,7 are not excluded here.

This theorem allows arbitrary independent orientations,
does not require actual contacts or a chosen physical
stress, and gives a genuine joint central-status /
outer-center classification exclusion.

## 1. Two square centers of norm below one cannot share a moderate cap

**Cap-inner-pair lemma.** Let two pairwise
interior-disjoint unit squares lie wholly beyond

    n dot x >=h>=2/5,

with unit n. Their centers cannot both have norm <1.

**Hand proof.** Rotate n to the positive horizontal
axis and call the two centers (x_i,y_i).
For any unit square its projected half-width in
the x direction is >=1/2. Hence cap containment gives

    x_i>=h+1/2>=9/10.                               (3)

If both center norms were <1, then

    9/10<=x_i<1,
    |y_i|<sqrt(1-(9/10)^2)=sqrt(19)/10.

Consequently

    |x_1-x_2|<1/10,
    |y_1-y_2|<sqrt(19)/5,

and therefore

    |p_1-p_2|²
       < (1/10)²+(sqrt(19)/5)²
       = 1/100+19/25=77/100<1.                    (4)

But the open inscribed disks of radius 1/2
of the two unit squares are disjoint, forcing
center distance >=1. Contradiction. QED.

The lemma is entirely elementary and requires
no containing-circle bound beyond the stated
center-norm hypothesis.

We will also use its immediate stronger fact:

    h>=1/2 => every cap square center has
    n dot p>=h+1/2>=1, hence norm>=1.              (5)

## 2. Fix the central-square position and the RU member

Write p_C=(a,b), with |a|,|b|<1/2.
The orientation-free opposite 2+2 cap theorem
at the search ceiling forces

    |a|<5/24,       |b|<5/24.                        (6)

Since one square has RU double-side status,
the sharp one-square corner-cap theorem forces

    a+b< -1/5.                                      (7)

Equations (6)--(7) already imply that a and b
cannot both be nonnegative. They also show that
**if one is nonnegative, it is smaller than 1/120**:
for example b>=0 and a> -5/24 gives

    b< -1/5-a
      < -1/5+5/24=1/120.                            (8)

The double RU member has center p_RU satisfying

    p_RU.x>=1+a>19/24,
    p_RU.y>=1+b>19/24,                              (9)

because its entire square lies beyond the
positive right and upper support sides of C,
and every square has half-width >=1/2.
Thus

    |p_RU|²>2*(19/24)²=722/576>1.                  (10)

So the RU square itself is always **outer**
in Type C.

## 3. Three exhaustive signs of the central center

**Case A: a<=0 and b<=0.**
The *left* central side offset h_L=1/2-a
is >=1/2, and the *lower* side offset
h_D=1/2-b is >=1/2. Each side serves
two whole exterior squares. By (5) all
four are outer. They are **four distinct**
squares: Type C has only one double-side
status RU, so no square belongs to both
L and D. The RU square is a fifth distinct
outer square by (10). Thus k>=5.

**Case B: a>=0 and b<0.**
The right and lower offsets obey

    h_R=1/2+a>=1/2,
    h_D=1/2-b>1/2.

Their two cap squares each are outer
by (5). These are four distinct labels,
since the only double status RU cannot
lie on both R and D.

The opposite left side has two whole
square members, and by (7)--(8),

    0<=a<1/120,
    h_L=1/2-a>59/120>2/5.                           (11)

By the cap-inner-pair lemma, at least
one L square has center norm >=1.
Neither L square belongs to R (opposite
sides) or D (the only double status
is RU), so this is a fifth distinct
outer square. Hence k>=5.

**Case C: a<0 and b>=0.**
This is the reflected coordinate
analogue of Case B. The left and
upper sides have offsets >=1/2 and
supply four distinct outer squares;
their memberships cannot overlap
because LU is absent. Equation (8),
with a,b exchanged, gives b<1/120,
so the lower side offset is

    h_D=1/2-b>59/120>2/5.

Its two members include at least one
outer center by the cap-inner-pair lemma,
and neither belongs to the left or
upper side because the only double
status is RU. This gives a fifth.

The three cases exhaust a+b< -1/5,
including coordinate-zero boundaries.
In every case there are at least five
**distinct** center-norm-at-least-one
exterior squares, proving the theorem. QED.

## 4. What is actually eliminated

The classification in FINITE_PATTERN_TAXONOMY.md
allows k=3,4,5,6,7 outer centers, but
the **saturated Type C status branch** can
occur only in its k=5,6,7 macro-branches.
This rejects the intersections

    Type C with k=3,
    Type C with k=4

for all unit-square frames and all contact
graphs at q<=9789/2500.

The proof does not claim that Type C
itself is realizable, or that k=5,6,7
will all survive the complete eight-square
geometry. Its actual lower-bound obligation
R8>=Rhat remains open. The known equality
candidate belongs to single-side Type S4,
not Type C, so this exclusion does not
discard any established candidate equality.

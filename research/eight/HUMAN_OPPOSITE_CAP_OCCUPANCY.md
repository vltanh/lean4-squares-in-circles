# Opposite central-side populations of three and two are excluded

## Inputs

HUMAN_THREE_SQUARE_CAP.md proves that three whole unit squares in
D_R intersect {x>=h}, with 0<=h<=1/3, require

    R^2 >= (h+1)^2+9/4.

HUMAN_SHARP_CAPACITY_BOUND.md proves that two whole unit squares in
D_R intersect {x>=h}, with 2/3<=h<=1, require

    R^2 >= (h+1)^2+1.

Both theorems allow arbitrary independent orientations. This note integrates
the saved continuation's consequence of those two hand proofs.

## 1. Localize a central side which serves a triple

Let C contain the disk origin in its open interior. Let p be its center
and n an outward unit side normal. The supporting line has coordinate

    h=n dot p+1/2,       0<h<1.

Suppose three other squares admit separation beyond this side on the
central-owned axis n. All three whole squares lie in {x:n dot x>=h}.
Assume R<2.

Necessarily h<1/3. Otherwise apply the three-square theorem at threshold
1/3 to the larger containing cap, obtaining

    R^2 >= (4/3)^2+9/4=145/36>4,

which is impossible. At the actual h the same theorem gives

    h <= sqrt(R^2-9/4)-1,
    n dot p <= sqrt(R^2-9/4)-3/2.                         (1)

In particular the triple side faces inward: n dot p<-1/6.
The statement concerns available whole-square separators, not a count
of centers on a side of C.

## 2. The opposite 3+2 theorem

**Theorem.** Suppose three whole squares are separated beyond one central
side and two whole squares beyond the opposite central side, with R<2.
Then

    R^2 >= 2257/576.                                      (2)

**Proof.** The triple threshold is h in (0,1/3), by section 1. Reflecting
the opposite cap gives threshold 1-h in (2/3,1). Apply both sharp cap
bounds:

    R^2 >= max((h+1)^2+9/4, (2-h)^2+1).                  (3)

The first expression increases with h and the second decreases. They
agree at h=7/24 and there equal 2257/576. If h<=7/24 the second
expression is at least this value; if h>=7/24 the first is. This proves
(2). No frame equality among the five other squares was assumed.

The two caps are disjoint, so their five squares are automatically distinct.
Membership on adjacent central sides can overlap; no exclusive assignment
is needed here.

At equality h=7/24. The equality cases of both cap theorems force all
five frames parallel to C, the extreme triple members and the opposite
pair at their sharp placements, and only the allowed normal displacement
of the middle member of the triple.

## 3. Application to the sharp eight-square target

The exact projected-family radius Rhat satisfies

    Rhat^2 < 2257/576,

by the strict improvement from zero tilt proved in HUMAN_FIVE_CORNER.md.
Therefore a hypothetical eight-square packing below Rhat cannot have
these opposite side populations. Every triple central side has an
opposite side serving at most one whole square.

This closes the former conditional three-parallel-square-column exclusion
without that parallelism premise. It does not close the unrestricted
packing theorem. One still has to account for all seven exterior squares,
including genuine corner-owned exceptions, and produce the five-corner
obstruction or a sharp bound for every remaining occupancy.

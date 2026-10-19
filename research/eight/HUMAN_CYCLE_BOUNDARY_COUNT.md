# A five-square exterior cycle has a strictly interior square

## Theorem

Suppose unit squares with pairwise disjoint open interiors fit in a disk
D_R centered at zero, where

    sqrt(2)+1/2 < R < 2.

Every directed positive-contact-moment cycle consisting of five exterior
squares includes a square strictly inside D_R. Here exterior means that
the closed square omits zero. A directed contact moment has the convention
of HUMAN_GLOBAL_CYCLE_CLOSURE.md: the separator points from the source
square to the target and z cross n>0 at their contact point.

In an eight-square minimum-contact radius minimizer, this square therefore
has actual contact degree at least two. Degree two gives the aligned
opposite-contact transmitter already proved in HUMAN_CYCLE_ANALYSIS.md.
Degree at least three remains a separate possibility; it is not removed
by this theorem.

## 1. Angular shadow of a circle-contact square

Put a=1/sqrt(2), the distance from a unit square's center to its vertices.
Every unit square of center p lies in the closed disk of radius a centered
at p. If the square touches the containing circle, a point x of the square
satisfies |x|=R, and the triangle inequality gives

    |p| >= R-a.                                         (1)

For R>sqrt(2), this exceeds a. The angular shadow of the disk centered at
p with radius a has length

    2 asin(a/|p|).                                      (2)

For completeness, its two extreme rays from zero are tangent to that disk.
The radius to a tangent point is perpendicular to its tangent ray. The
resulting right triangle has hypotenuse |p| and opposite side a, so the
angle on either side of the ray through p is asin(a/|p|). The whole disk
lies between these rays, proving (2).

The square's angular shadow is contained in that of its circumdisk. By
(1) and monotonicity of arcsine, its angular length is therefore at most

    2 asin(a/(R-a)).                                    (3)

This is an upper bound on the square's entire angular shadow. It does not
assume that a contact point is a vertex or that the square is in a radial
frame.

## 2. An exact strict comparison with one fifth of a turn

At the radius R0=sqrt(2)+1/2, the ratio in (3) equals

    a/(R0-a) = 2-sqrt(2).

The following strict comparison is exact:

    2-sqrt(2) < sin(pi/5).                               (4)

Indeed both sides are positive and
`sin(pi/5)^2=(5-sqrt(5))/8`. Squaring (4) and rearranging reduces it to

    43+sqrt(5) < 32sqrt(2).

Squaring these positive quantities reduces that in turn to
`43sqrt(5)<97`, whose square comparison is `9245<9409`.
No decimal angle estimate is used.

As R>R0, equations (3)--(4) show that every square touching the containing
circle has angular shadow of length strictly less than

    2pi/5.                                              (5)

## 3. A winding cycle must cover every direction

The exterior contact-cycle theorem constructs a closed curve in the union
of the five cycle squares with positive winding about zero. Equivalently,
its argument lift makes at least one full positive turn. Every ray from
zero therefore meets that union. This also follows by observing that a
curve avoiding one ray has a single-valued continuous argument and hence
winding zero.

If all five squares touched the containing circle, the measure of their
combined angular shadows would be at most the sum of their individual
lengths, which by (5) is strictly less than 2pi. They could not cover every
direction. This contradiction proves the theorem.

A square in a closed disk which does not touch the circle lies strictly
inside the disk, by compactness. In a minimum-contact representative a
strictly interior square cannot have actual degree one; that follows by
translating it away from its only contact while preserving all positive
disk and pair gaps. Here it already has at least its two distinct cycle
neighbors. If its actual degree is two, the opposite-contact and alignment
theorem of HUMAN_CYCLE_ANALYSIS.md applies exactly as stated.

## 4. A useful general form

The same argument gives a necessary radius restriction for an exterior
winding cycle of k squares all touching the containing circle, whenever
R>sqrt(2):

    2pi <= 2k asin(a/(R-a)),
    R <= (1/sqrt(2)) [1+csc(pi/k)].                      (6)

One cannot reverse this inequality to claim existence of such a cycle.
For k=5 the sharper comparison in section 2 suffices at the analytical
lower bound already proved for eight squares.

Combined with HUMAN_CYCLE_INTERIOR_CAPACITY.md, the five-cycle case in an
eight-square minimizer now has two exact features: its two unused exterior
squares have winding zero, and at least one of its five cycle squares is
strictly inside the circle. The remaining task is to use their joint
placement, not to assume that this interior vertex has degree two or that
its neighbors are the desired twin scaffold.

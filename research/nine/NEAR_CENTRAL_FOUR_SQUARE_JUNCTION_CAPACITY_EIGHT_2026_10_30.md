# A four-square junction near the containing-circle center leaves capacity at most eight

Date: October 30, 2026 UTC.

**Status: complete proposed force-free hand theorem, awaiting independent
review. No original graph or roadmap flag is changed here.**

## 1. Exact statement

Let pairwise interior-disjoint unit squares lie in the disk centered
at O of squared radius at most Q=1105/256. Suppose four of the actual
squares meet at one point p and, in their common orthonormal side
frame, the two coordinates of p satisfy

    |p_x|<=1/60, |p_y|<=1/60.                              (1)

Then there are at most eight actual squares altogether. Equivalently,
the four-square block has capacity at most four other unit squares.
Every other square has arbitrary independent orientation.

Four interior-disjoint squares meeting at one point necessarily form
the aligned two-by-two block with union

    B=[p_x-1,p_x+1] x [p_y-1,p_y+1].                     (2)

Indeed their four disjoint local interior angles at p must sum to at
most 2*pi. A square contributes pi/2 at a vertex and pi at a side
interior. Four therefore all contribute pi/2 and fill the four
consecutive quadrants. Their sides have unit length, proving (2).

The theorem includes the closed thresholds in (1), every boundary
contact, every physical circle mask and all zero stress coefficients;
none of those coefficients is used.

## 2. The exact center disk and the block's center exclusion

Every contained unit-square center c has

    |c|<M:=91/60.                                        (3)

Its farthest actual corner squared norm is
`|c|^2+1/2+|c.u|+|c.v|>=|c|^2+|c|+1/2`, whereas

    M^2+M+1/2-Q=31/57600>0.

Any two distinct unit centers have distance at least one, because
their open radius-1/2 incircles lie in their respective disjoint
open square interiors.

For any other square E with center c, its open radius-1/2 incircle
misses int(B). Otherwise an open overlap contains a point away from
the internal block edges and overlaps an original block unit.
Consequently

    dist(c,B)>=1/2.                                      (4)

The statement remains valid when a nearest point is on the boundary
of B: if its distance were less than 1/2, nearby interior points of
B would also belong to the open incircle.

## 3. Every other center belongs to one of four narrow caps

Set

    a=59/60, b=89/60.                                    (5)

A center inside both coordinate intervals of B contradicts (4).
If it is outside only the horizontal interval, (4) gives
`|c_x-p_x|>=3/2`, hence `|c_x|>=b`. The vertical-only case gives
`|c_y|>=b`.

It cannot be outside both intervals. In that case write

    |c_x-p_x|=1+s, |c_y-p_y|=1+t,
    s,t>0, s^2+t^2>=1/4.

By (1), |c_x|>=a+s and |c_y|>=a+t. Since s+t>=1/2,

    |c|^2 >= 2*a^2+2*a*(s+t)+s^2+t^2
          >= 2*a^2+a+1/4
          = 5701/1800
          > M^2=8281/3600.                              (6)

The exact last reserve is 3121/3600, contradicting (3).
Thus every other actual center lies in at least one of the four caps

    x>=b, x<=-b, y>=b, y<=-b,
    x^2+y^2<=M^2.                                       (7)

These caps are pairwise disjoint: adjacent ones would require squared
norm at least 2*b^2>M^2, and opposite ones are plainly disjoint.

## 4. Each cap has center capacity one

In the eastern cap, b<=x<=M and |y|<=sqrt(M^2-b^2)=1/sqrt(10).
For any two points in that cap their squared distance is at most

    (M-b)^2+4*(M^2-b^2)
      =1/900+2/5=361/900<1.                              (8)

The same calculation holds for the other three caps by reflection
and swapping coordinates. The center-distance lower bound therefore
allows at most one actual square center in each cap. There are at
most four additional units, proving the capacity eight.

## 5. Sharpness and use in two-channel arguments

The count eight is attained within the smaller disk of squared radius
17/4. Take the four central axis-aligned units with centers
`(+-1/2,+-1/2)` and four outer axis-aligned units with centers
`(+-3/2,0),(0,+-3/2)`. All open interiors are disjoint; the outer
units' farthest corners have squared norm 17/4 and the central
block's corners have squared norm at most two.

Consequently two crossing physical channels are not impossible merely
as an eight-square configuration. A proof for nine squares must retain
the ninth actual unit. This theorem supplies precisely that final
capacity contradiction once a caller proves (1) for an actual
four-square junction.

The statement does not assert that two long channels automatically
cross or that their crossing lies at their middle contact. Those are
separate geometric caller obligations. No force or torque equation,
selection change, compilation, numerical pose search, certificate or
original-ledger mutation occurs in this proof.

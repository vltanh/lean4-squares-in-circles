# Review of whole-square return-side localization and the short-return normal cone

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen theorem source. No repair requested.**

## 1. Literal source and review boundary

Read the complete current manuscript

`LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md`

at 12,450 bytes, SHA256
`c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e`.

The reviewer authored the imported marked-cycle source but did not author
these new side and normal-cone arguments. The review independently
reconstructs the new complete proofs and checks their literal joins.
The expanded endpoint source was previously read and fully reviewed by
the reviewer. The marked-cycle source has separate full root and axial
reviews.

The exact witness and contact data in Section 6 were independently
checked geometrically. The no-triple-cap diagnostic is the explicitly
cited existing statement of `UNRESTRICTED_THREE_SQUARE_CAP.md`, Section
7; it is not a premise of either new theorem. No independent re-audit
of that source's entire sharp cap theorem is asserted by this note.

## 2. Long endpoint directions and the common complementary sector

The common-normal long run supplies an actual support gap of at least
two. The imported coupled-height lemma gives X_A,X_B>89/60 and
|y_A|+|y_B|<=1/8, including every endpoint tilt and circle mask.

Each endpoint's absolute angular deviation from its signed horizontal
axis is below atan(15/178). The source's exact comparison is sound:

    15/178<3/35,
    tan(3*atan(3/35))=5499/20965<4/15<2-sqrt(3).

The triple angle lies in (0,pi/2), so its comparison with tan(pi/12)
gives deviation less than pi/36. The final radical comparison is
equivalent to sqrt(3)<26/15 and follows by positive squaring.

The two long endpoints are consecutive marked bodies. The complete
physical marked-order theorem therefore puts every other mark on one
complementary arc. After a single reflection of the entire frame, this
arc runs from B near angle zero to A near pi through the upper side.
The first return mark is more than forty degrees past B and the last
is more than forty degrees before A. Every return mark consequently
has its direction strictly between 35 and 145 degrees. This uses one
common choice of side; no individual-body reflection is made.

The argument also covers exactly one return mark, whose separation
from both endpoints supplies both inequalities. No common-normal
condition on the rest of the cycle is inserted into Theorem 1.

## 3. Whole-square clearance

Every return mark is physically on the containing circle, so its center
radius is at least 79/40-1/sqrt(2). Its angle is strictly in the sector
above. Concavity of sine gives

    sin(35 degrees)>=(2/3)*sin(30 degrees)
                       +(1/3)*sin(45 degrees)
                    =1/3+sqrt(2)/6.

Multiplication gives exactly

    (79/40-sqrt(2)/2)*(1/3+sqrt(2)/6)
       =59/120+13*sqrt(2)/80
       >863/1200>43/60.

The final reserve is 1/400. Every point of the original unit lies
within 1/sqrt(2)<17/24 of its center, so its height is strictly above
43/60-17/24=1/120. This verifies whole closed-square containment in
the stated open halfplane, including its vertices and side endpoints.

The theorem retains all original poses and contact means. It does not
assume the long force line coincides with the coordinate axis or with
an internal square's center line.

## 4. The complete directional cap-width estimate

Return centers lie in |c|<M=91/60, y>H=43/60. The exact cap halfwidth
K satisfies K^2=134/75<(27/20)^2.

For a direction with vertical absolute component at least its
horizontal absolute component, reversal and horizontal reflection
reduce the width calculation to (a,b), 0<=a<=b, a^2+b^2=1. These
operations preserve the cap width and do not alter the asserted
physical direction in the final statement.

The maximum support is at most M. At height z the minimum support is
at least -a*sqrt(M^2-z^2)+b*z, an increasing function for z>=H.
It is therefore at least -aK+bH. The width is bounded by

    M+aK-bH <= M+(K-H)/sqrt(2)
             <91/60+(19/30)/sqrt(2)
             <91/60+19/42
             =827/420<2.

The last reserve is 13/420. This contradicts any supported center
projection gap at least two and proves the strict forty-five-degree
normal cone. Actual common-normal paths with one or more internal
bodies supply that gap by their unchanged support identities; no
torque or common endpoint frame is needed.

## 5. Seven-body terminal and equality witness

The opposite long/short cycle retains both direct joins B-C and D-A
and every completing body. The theorem supplies a common strict side
for C,D and a relative short-normal angle below forty-five degrees.
It does not equate the short and long frames or assert the sharp
radius lower bound from those conditions alone.

The displayed staggered nine-square pose has disjoint open interiors
by the exact coordinate separations. Its four outer anchors attain
Q; the two upper extras have farthest-corner squared norm
1709/400=Q-281/6400, and the other body corners are strictly within
the disk. The long contact means (-1,0),(0,0),(1,0) belong to their
original shared sides. The short means (+-1/2,-4/5) belong to their
original shared sides as well. Equal horizontal forces balance both
force and moment on each specified internal transmitter.

The source correctly refrains from asserting full endpoint equilibrium
for this particular mean choice. Its actual geometric witness still
shows why a common seam, equal internal heights, or placement of the
whole lower triple below the sharp cap ceiling cannot be inserted as
geometric normal forms.

## 6. Scope conclusion

Both new theorems apply to the entire stated compatible physical
marked-cycle family, with arbitrary additional marked endpoint edges
and zero circle weights at physically touching marks. All unmarked
full-degree and force premises are kept when the geometric result is
used as a stress caller. The unresolved sharp seven-body conclusion is
accurately left open.

No numerical pose search, Lean compilation, CI, new finite proof
certificate, original ledger mutation, or remote write was used in
this review.

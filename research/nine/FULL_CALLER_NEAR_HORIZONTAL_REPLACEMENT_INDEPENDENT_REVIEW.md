# Independent review of the aligned three-blocker argument

The source-bound hand proof `FULL_CALLER_NEAR_HORIZONTAL_REPLACEMENT_HAND_PROOF.md`
at SHA256 `3b3164cccab5bf09401eb2c3d8e56ac5dfdc9fc6bccb8a0e9a1d9390c188d7f1`
is accepted for its stated conditional full-nine caller. Its new geometric
lemma and the attachment of the previously accepted near-horizontal row are
sound. This review gives no original-cell or mask closure.

The arbitrary C square remains in its actual original frame. Folding its
two absolute side components gives horizontal and vertical halfwidth
`h=(a+b)/2` and bottom-vertex horizontal offset `j=(a-b)/2`. Thus `h+j=a<=1`
and `0<=j<=1/2`; these are facts about C, not an axis-aligned replacement.
Incircle separation, the original cone and the strict weak C–D bit give
`-3/14<x<3/10`. The strict inequalities at both ends are justified by the
rational comparisons to `1/sqrt(2)` and by the original strict bit.

The three geometric cases are exhaustive, including `y=v` and `x=0`.
When `y<v`, separation from X gives `y<-33/40`, while the cone gives
`y>-17/14`. Hence C is too close to G: the squared center distance is
strictly less than `109/196`. When `y>=v` and `x>0`, the original cone
and `v>=0` bound `0<=y-v<=1-x`, so C/X squared center distance is at most
`1-2x(1-x)<1`. Both contradictions are valid for every orientation of C.

In the remaining case `y>=v, x<=0`, a bottom vertex of C is
`P=(x±j,y-h)`. The lower horizontal margin is strictly positive because
`x-j+1/2=(x+h-1/2)+(1-a)>0`. The upper margin is nonnegative from
`x<=0,j<=1/2`; equality would force `x=0,j=1/2,a=1,b=0,h=1/2`, contradicting
strict weakness. The center of C also lies strictly in X's horizontal
strip. The cone and strict weak bit give `P_y<1/2<=v+1/2`, while the center
height obeys `y>=v>v-1/2`. To make the intersection fully explicit, set
`L=max(P_y,v-1/2)` and `U=min(y,v+1/2)`. The four strict comparisons imply
`L<U`. Choosing `z=(L+U)/2` gives a segment parameter
`t=(z-P_y)/(y-P_y)` strictly between zero and one. The corresponding point
is horizontally and vertically interior to X. It is interior to C because
it is a strict convex combination of C's center and one of its vertices.
This handles both chiralities and the case in which the bottom face is an
edge. It uses physical open-interior disjointness with all contacts retained.

The full-caller attachment uses only Sections 1–3 of the accepted general
near-horizontal B–X–D row. Original actual A–B and the actual E–F–G links
provide the two span lower bounds. The unrestricted A/E cap and the D/G cap
with the larger of the two separately valid tolls force equality at closed
Q. The row equality aligns B,X,D; its toll then vanishes, so the ordinary
cap equality classification aligns the other endpoint originals and fixes
the D/G coordinates. Neither original B–C actuality nor a large C–D height
gap nor a preassigned side for G is used. A common vertical reflection
preserves every original horizontal cone and bit, and X/G nonoverlap then
gives `0<=v<=1/8`. The actual original C satisfies the blocker hypotheses.

For X=C the equality contradiction is even shorter: both row gaps become
one and C,D align, violating strict weak C–D directly. The four C and six
H/I closed escape rows have the stated polarities and retain equality
faces. Their optional product is a necessary 4×6×6 cover, not a collection
of proved exclusions. The reduction to 3×6×6 requires the explicitly stated
common vertical reflection. The aligned contact control in the arithmetic
review verifies that replacing the strict C–D bit by a weak comparison
would invalidate the blocker claim.

The independent companion `review_aligned_three_blocker.py` reconstructs
the rational margins, both cap reflections, the sixteen literal escape
rows and the physical equality control without importing the author's
checker or any numerical solver. Those computations support the continuous
argument above; finite examples are not its proof. The retained UNKNOWN
nonlinear solver result is discovery history only.

# Independent review: restored one-eighth-clearance inner arc

Date: October 27, 2026.

Reviewer: rooted_blocks, independently of source author hexagon.

**Verdict: ACCEPTED after a fresh complete read.** The workspace reset
removed the earlier reviewed wording. I read the entire reconstructed
source and the reconstructed full direct prerequisite, checked all actual
feature intervals and exact bounds again, and accept the restored source
with no correction.

Current reviewed source:

    NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md
    SHA-256 4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366

Current direct prerequisite:

    NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md
    SHA-256 4da80eec56859a863f042257d8ae391c17409e2b0e82dbee2e6b7173838fa54b

The pre-reset source pin was f554268a5cd8edc5fb01db116e285ddc51da4ba611c000ec62f6d7c181b662b1;
the earlier full review pin was09a366975bfd958b709f2e24a40bb4eb90357b044768ada1a2f5c2eddb9b0358.
Those identify the historical version, not the current restored bytes.

## 1. Both entire actual coordinate domains are present

The actual own-axis ordering a>=b>=1/2 is obtained without moving
the circle origin. The squared distance is exactly
max(a-1,0)^2+max(b-1,0)^2. Both a>rho and a<=rho are retained.

For a>rho, the original fixed-q proof needs only the declared
coordinate inequalities, not the older stronger clearance premise.
I checked its full convexity reduction, both enlarged endpoints
61/320 and97/144, the diagonal bound below4/5, and all four
upper-minus-lower differences. The formal upper eta=pi/2 limit
cannot create an extra point because alpha<pi/2. The whole actual
circle intersection is covered.

## 2. The newly retained outer-face interval is complete

For a<=rho, strict clearance forces 0<B<=A<=1/8 and
A^2+B^2>1/64. Hence A>1/(8sqrt2)>1/12, a>13/12 and b>1.
The first-quadrant interval
[max(beta,theta),min(alpha,eta)] is exactly the full intersection.

The inner/inner difference has cosine at most8sqrt5/81<4/5.
Each unit-strip difference is at least asin(8/9)>gamma; I checked
the derivative signs on the entire actual intervals, including endpoints.

For the outer/outer pair the difference lies in the sine-monotonic
interval [-pi/2,pi/2]. The exact numerator bound is

    ab-sqrt((rho^2-a^2)(rho^2-b^2))
       >13/12-31/192,

using the squared radical bound901/36864<(31/192)^2. Thus its
sine exceeds59/81>3/5, proving that fourth difference exceeds
gamma. The actual a=rho and b=rho endpoints remain, with their
formal outer bounds superseded by the strict inner-face bound.
There is no discarded face or chosen favorable subarc.

## 3. Center point, all orientations and the strict threshold

The actual incircle gives |c_E|>5/8. The farthest-corner inequality
gives |c_E|^2+|c_E|+1/2<=Q, and its value at91/60 exceedsQ by
31/57600. Hence the radius-rho point in the actual center direction
lies strictly inside that incircle and in the unique open arc.

Distinct actual unit interiors give disjoint open arcs. The stated
capacity rule is valid only after a caller establishes full actual
gap routing, as the source explicitly requires. Strict arc lengths
handle equality in the gap-length bound.

The contained equality example [1/8,9/8] times[-1/2,1/2] genuinely
has two open arcs separated by its outer-side midpoint. Thus the
strict dist>1/8 premise is correctly retained.

The restored theorem keeps the same force-free, arbitrary-orientation,
all-endpoint scope. Its Section3 remains exactly the outer-face
prerequisite used by the byte-restored forty-degree strengthening.
No force, graph, circle mask or normal-selection premise has been
introduced. No compilation, CI or numerical pose was used in this review.

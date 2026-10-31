# Root review: every triangle body meets its full external-resultant ray

Date: October 27, 2026.
Reviewer: root proof worker.
Source: TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md.

**Verdict: accepted at the complete stated local scope.** The stronger
conclusion uses the already independently reviewed general ray lemma
and a short additional physical cap contradiction. It does not change
any genuine degree, force, mask or mean.

The input is an actual positive unit-square triangle. Every body's
full external aggregate has zero origin moment; in particular any
own circle resultant or attached branch force remains inside that
aggregate. Its root pair sum N is nonzero by the complete external-
resultant theorem. The assumption that the closed root avoids the
whole ray of -N is exactly the assumption of Section 1 of
TWO_TRIANGLE_TIP_LEAVES_D_TYPE_EXCLUSION.md. That general lemma was
proved before its D-type caller and imposes no D leaf, neighbor-load
or degree hypothesis.

I checked its invoked zero common moment and nonparallel alternatives
against the standalone source. They preserve proper-length endpoints
and actual original normal ownership. They leave only two equal
root normals along one actual own side axis m, a strictly positive
height h, and the original positive weighted mean h m in the root.

The new step is correct: the root's own-axis rectangle has m interval
[h-1,h] and a transverse interval containing zero. For 0<h<=1 it
contains O, including every boundary endpoint. Closed avoidance of
the whole ray therefore forces h>1. This requires neither an
origin-interior claim nor an interior contact mean.

Both original neighbors lie in the support half-plane m.x>=h.
A unit square has projection halfwidth at least 1/2 in any direction,
so their actual centers have m component greater than 3/2. The
contained-unit upper bound used here follows directly from the four
corners: their maximal squared norm is
|c|^2+1/2+|c.u|+|c.v|, at least |c|^2+|c|+1/2.
At M=91/60 its excess above 1105/256 is exactly 31/57600>0.
Every actual center therefore has norm strictly below M.

In the m,Jm frame both centers lie in the rectangle
(3/2,91/60) times (-sqrt(181)/60,sqrt(181)/60).
Its squared diameter is exactly 725/3600=29/144<1.
Thus their radius-1/2 open incircles overlap. This contradicts the
original physical units, with no circle-load premise on either one.

Consequently every actual triangle body meets the closed nonnegative
ray of its own full external aggregate. The two-triangle consequence
is also correctly limited: only after physical circle clearance and
the absence of other root forces are established do the two original
pair sums become opposites. Convexity of the actual root then gives
closed containment of O. It does not give O in the open interior,
and the source explicitly retains all zero/boundary cases.

No artificial branch unit, normal reselection, deleted circle force,
numerical pose, scalar certificate, Lean compilation, CI or coarse
closure is used.


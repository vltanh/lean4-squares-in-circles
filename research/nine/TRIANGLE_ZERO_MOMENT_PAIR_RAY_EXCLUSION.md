# A zero-moment triangle excludes its positive pair-resultant ray at an origin body

Date: October 27, 2026.

**Status: accepted complete hand local argument after two separate
independent full-source reviews in
REVIEW_TRIANGLE_ZERO_MOMENT_PAIR_RAY_ROOTED_BLOCKS_2026_10_27.md and
REVIEW_TRIANGLE_ZERO_MOMENT_PAIR_RAY_HEXAGON_2026_10_27.md.**
This strengthens the two-block
origin-interior criterion without extending the positive-external-ray
theorem into its false zero-moment domain. No coarse closure is claimed.

## 1. Actual triangle and statement

Keep an actual positive triangle K,U,V of three interior-disjoint
original unit squares, with the same original force and torque
equations. Each body's full external aggregate has zero origin
moment. The complete triangle external-resultant theorem supplies
nonzero noncollinear aggregates, at most one parallel body, and
equal outward signs for any parallel pair.

Suppose the common directed triangle moment is zero and O belongs
to the closed K. Write its two original outward triangle normals
as n_1,n_2, with positive magnitudes mu_1,mu_2, and set

    N=mu_1 n_1+mu_2 n_2.

Thus K's full external resultant is -N, and N is nonzero.

**Theorem.** The same closed K avoids the strictly positive ray of
its actual pair-force sum:

    K intersect {t N:t>0} is empty.                     (1)

The ray in (1) has the opposite direction from K's own full
external resultant. All original means and zero-length proper
ports are retained. No circle-load or degree assumption is made
on any triangle body.

## 2. Parallel K

If K's normals are parallel, their physical signs are the same:
n_1=n_2=m. Either other body, say U, is nonparallel, since at
most one actual triangle body can have a parallel pair.

Its two original force lines have zero origin moment and are
independent, so their concurrence is O. At the KU port the
physical proper-port identity at U gives

    P=-a m,        a>=0.

The unchanged actual port belongs to K's maximum-m support.
Hence h_K(m)=-a<=0. Since O belongs to K, h_K(m)>=0. Therefore
h_K(m)=0 and the whole K lies in m.x<=0.

The vector N is a positive multiple of m. Every tN with t>0
has strictly positive m coordinate, so lies outside K. This
proves (1) in the complete parallel case.

## 3. Nonparallel K and two nonparallel neighbors

Now K is nonparallel and its genuine concurrence is O. At least
one other body U is nonparallel and also has concurrence O.
Their shared edge has the two actual proper identities

    P=a n_1=-b n_1,       a,b>=0.

Thus P=O. In particular h_K(n_1)=0.

If V is nonparallel as well, the same argument at KV gives
h_K(n_2)=0. Both are original support directions at O. Since

    |N|^2=mu_1(N.n_1)+mu_2(N.n_2)>0,

at least one of N.n_1,N.n_2 is strictly positive. That support
inequality excludes every tN with t>0 from K. This includes all
shared-point and zero proper-length alternatives.

## 4. Nonparallel K with one parallel neighbor

The remaining V has two equal outward normals, say -n. The
actual normals K-to-V and U-to-V are consequently both n.
The genuine concurrences at K and U are O, so their original
ports toward V are

    P_K=a n,       P_U=b n,       a,b>=0.

Both points belong to V's same support face in direction -n.
Their -n coordinates therefore agree, so a=b. Put P=a n.
The two original units K,U both contain P as well as the
actual common KU point O found in Section 3.

If a=0, both K ports are O and the preceding positive-normal-
combination argument applies directly. Suppose a>0. The
actual KU support separates K and U and contains their entire
common segment [O,P]. If m denotes its actual outward normal
from K to U, then

    h_K(m)=0,        m.P=0,        m.n=0.

No normal is newly chosen: these equalities follow from the
two distinct shared points and the original separating plane.

K's pair sum now is N=mu m+nu n, with both magnitudes positive.
Thus N.m=mu>0. Since K lies in m.x<=0, every strictly positive
point of its N ray is outside K. This proves (1), keeping both
real V means even when the common face is a side.

Sections 2--4 exhaust the actual parallel/nonparallel cover.
The local theorem needs no radius bound beyond any premises
of its named triangle-resultant and proper-port dependencies.

## 5. Two triangle blocks: one nonzero moment already suffices

Work now in the original radius window

    79/40<=R<=sqrt(1105)/16.

Suppose two actual triangle blocks meet only at K, which is
physically circle-clear and has no positive force beyond their
four actual pair forces. Each complete private branch attaches
at one triangle vertex, so summing its original origin torques
supplies zero full external origin moment there. Keep all actual
private loads, degrees, physical masks and original means.

Assume at least one of the two actual triangle cycle moments
is nonzero. The full K equation makes the two original pair
sums N and -N. The accepted closed external-ray theorem gives
O in K by convexity of the two opposite-ray intersections.

If the other triangle had zero common cycle moment, apply (1)
to it. Its positive pair-sum ray is exactly the full external
resultant ray of the nonzero-moment triangle. The accepted
TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md puts a strictly
positive point of that ray in K, contradicting (1).

Both triangle moments are therefore nonzero. Section 5 of the
same accepted source then gives

    O belongs to the open interior of K.                (2)

This criterion retains the genuine moment of each triangle.
It does not assert a nonzero moment where both are originally
zero, and it does not replace a branch by a physical leaf.

All original physical squares, actual forces, true degrees,
contact normals, real means and individual circle weights remain.
No generic normal reselection, numerical certificate, Lean
compilation, CI or whole-parent closure is used.


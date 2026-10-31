# Independent review of the complete low-turn actual feature cover

Date: October 26, 2026.

Reviewer: certificate_reduction.

**Verdict: PASS for SIX_CYCLE_ONE_RADIAL_LOW_TURN_FEATURE_COVER.md.**
I independently reconstructed the complete six-row owner/nonowner table,
the whole-channel axis exclusion, the actual endpoint restrictions and
the high-radius near-corner estimate. This review accepts the full
necessary cover; it does not assert that every tuple in the table is
a realizable physical core.

## 1. Turn and physical support scope

The unique loaded-body upper-turn theorem used by the source is local
to the actual unit and its two true side transmitters. It therefore
applies with a physical radial third load. With the strict force-polygon
turn sum and \(\theta_S<\pi\), both unique turns cannot be at most
\(\pi/2\). If one is low, the other is strict and
\(3\pi/4\le\theta_S<\pi\), as stated.

For an actual reserve-one channel out of Q in direction n, I checked
\[
 n\cdot c_W=h_Q(n)+1+h_W(n)\ge h_Q(n)+3/2.
\]
The full contained-unit center bound gives
\(n\cdot c_W\le d+1/2\), hence \(h_Q(n)\le d-1\).
This uses the actual far endpoint and true channel, not a simplified
contact or a smaller graph. It works for every far physical circle
mask and orientation. The upper-radius square comparison gives
\(d-1<1/60\).

A unique unit's outer-axis supports are its actual own circle
coordinates a,b, each greater than \(1/2\). They are therefore
excluded as channel normals. The remaining inner-axis supports
give exactly \(a\ge2-d\) or \(b\ge2-d\), as appropriate.

## 2. Independent exhaustion of the six actual rows

Write the actual proper concurrence relative to the opposite vertex
as \((X,Y)=(1-ta,1-tb)\). The containing-unit inequalities give
\(0\le X,Y\le1\) and \(0\le t<1\).

For a nonowned application the original moment sign decides which
vertex can be incoming or outgoing. The determinants of the actual
vertex positions with the circle corner are
\[
 \det(z,p_{10})=-a,\qquad
 \det(z,p_{01})=b,\qquad
 \det(z,p_{00})=b-a.
\]
Thus the incoming nonowner can be \(p_{10}\), or \(p_{00}\) when
\(a>b\); the outgoing one can be \(p_{01}\), or \(p_{00}\) when
\(b>a\). With the distinct nonowner application theorem from the
cited complete local support proof, these give precisely the three
listed nonowner pairs.

I reconstructed their directed determinants and dot products:

| Pair | Positive determinant | Dot product |
| --- | --- | --- |
| \(p_{10}\) to \(p_{01}\) | \(1-t(a+b)\) | \(taX+tbY\) |
| \(p_{00}\) to \(p_{01}\) | \(X\) | \(Y(1-Y)-X^2\) |
| \(p_{10}\) to \(p_{00}\) | \(Y\) | \(X(1-X)-Y^2\) |

The first row is strictly acute with the displayed positive-turn
bound. The other two give exactly the source's low-turn quadratics,
including equality at a right turn.

For actual side-axis normals, the same moment signs permit only an
incoming outer-right or inner-bottom axis and an outgoing outer-top
or inner-left axis. The channel support bound removes both outer
axes. With an incoming bottom axis and a nonowned return, an opposite
return would have dot product \(-Y\) with the incoming direction.
The low-turn condition would force \(Y=0\), making the other
normal an axis as well. The zero-vector concurrence case also has
strictly obtuse turn when the other application is genuinely
nonowned. Thus only the stated adjacent return remains. Its strict
normal gives \(0<X<1,\ 0\le Y<1\) and the original incoming
mean \((X,0)\). The outgoing-owner case is the reflected calculation.

If both inner axes occur, their turn is exactly \(\pi/2\).
Their actual linked means are \((X,0)\) and \((0,Y)\).
All allowed endpoints and the possible \(X=Y=0\) coincidence
are retained; no strict-turn distinctness theorem is applied to
this row.

The original strict point-normal convention correctly distinguishes
an actual axis owner from a nonowned vertex. No physical genuine
mean is reassigned a singleton label. The exceptional case where
the concurrence is an actual vertex is handled by the cited local
theorem and by the explicit owner-row zero-vector argument; it
does not create an additional row.

## 3. Original S placement and near-corner comparison

The table keeps which original interface is S-incident. The two
adjacent nonowner row has two adjacent choices. Each same-inner-side
row has one adjacent and one opposite choice. A one-owner row has
one actual interior mean choice and one adjacent choice. The
both-owner row retains the full actual mean at whichever original
interface meets S. This is the complete physical placement cover.

For the original radial port
\(P=(d,1/2)\), \(G=(-\cos\alpha,\sin\alpha)\), \(Q=P+G\),
I independently obtained
\[
 |Q|^2-(R-1)^2=2R-1+\sin\alpha-2d(1+\cos\alpha).
\]
Its radius derivative is strictly negative on the comparison range.
At \(R=2\), \(d>187/200\) follows from the exact square reserve
\(231/40000\). For \(0\le\alpha\le1/2\), the signed elementary
bounds give the increasing quadratic whose endpoint is exactly
\(-1/160\). Thus an actual circle corner within distance one of Q
forces the original \(\alpha>1/2\).

The turn sum then gives the exact complementary
\(\beta<\pi/4-1/2<2/7\). The source invokes the distance premise
only at actual adjacent applications or actual endpoints that
themselves satisfy it. It makes no assertion that an arbitrary
interior mean or opposite vertex can use this bound.

## 4. Scope verdict for the final assembly

The source is a complete necessary cover for the original low-turn
one-radial domain with both positive radial weights. Its separate
weight-zero and all-strict-turn dependencies retain their original
physical masks. The low cover includes all right-turn endpoints at
the unique load, both S placements and every original owned mean.

Its six rows can therefore be joined to the separate low-adjacent,
single-S-owner mean, low-opposite and both-inner-axis exclusions.
That later join must cite their complete proofs; the cover alone
does not exclude its retained rows or close a parent gate.
No computational certificate, Lean compilation or CI was used.


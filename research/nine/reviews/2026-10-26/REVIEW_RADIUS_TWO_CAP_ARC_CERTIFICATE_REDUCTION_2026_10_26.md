# Independent review of the radius-two cap quarter-turn arc theorem

Date: October 26, 2026.

**Verdict: PASS.** Reviewed complete saved source
RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md.

I independently reconstructed the own-frame reduction, both convex
endpoint estimates, the full closed and open circle-intersection
formulas, all radical signs, the radial-center point inclusion, and
the precise conditional capacity consequence. No numerical samples,
root finder, orientation mesh, Lean compilation or CI were used.

## 1. The cap premise removes the entire outer-face case

The source uses only an actual unit square in \(D_R\), \(R\le2\),
lying wholly in an actual half-plane \(n\cdot p\ge H\), with
\(H>1/(2\sqrt2)\). All square orientations and all contact or
load statuses are allowed.

In its signed and ordered own axes,
\(S=[a-1,a]\times[b-1,b]\), \(a\ge b\ge1/2\),
and the farthest corner has \(q=a^2+b^2\le4\). If
\(a\le5/4\), both nonnegative coordinates of the actual closest
point to the origin are at most \(1/4\), whose squared norm is
at most \(1/8\). This contradicts the cap's strict lower norm.
Thus \(a>5/4\), \(q>29/16\), and for \(A=a-1,B=b-1\),
\[
                 1/4<A<1,\qquad-1/2\le B<1/2.
\]
The conclusion \(A^2+B^2<5/4<(5/4)^2\) is strict and valid
on the whole domain.

## 2. The complete convex scalar comparison is valid

I reexpanded
\(E=A^2+B^2+\sqrt2 AB\) as a quadratic in \(t=a+b\) at
fixed q; it is exactly equation (8) in the source, with positive
quadratic coefficient. The full fixed-q range of t has endpoints
\(b=1/2\) and \(a=b\). Enlarging to this range needs no cap
premise at its auxiliary endpoints.

At \(b=1/2\), \(A\in(1/4,1)\), and
\[
 E<A^2+1/4-(7/10)A\le11/20<3/5.
\]
The two endpoint polynomial values are \(11/80\) and \(11/20\).
The radical substitution has the correct direction because A is
strictly positive.

At \(a=b=v\), the enlarged interval \([3/4,\sqrt2]\)
contains the complete actual range. The convex function
\((2+\sqrt2)(v-1)^2\) has endpoint values
\((2+\sqrt2)/16<7/32\) and exactly \(2-\sqrt2<3/5\).
These strict bounds verify \(E<3/5<25/32\) without a coefficient
packet or an orientation split.

For the other needed sign, if \(B<0\) the actual closest point
is \((A,0)\); hence \(A\ge H>1/(2\sqrt2)\), giving
\(\sqrt2 A+B>0\). For \(B\ge0\), A>0 gives it directly.
Thus the cap premise is used in both places where it is needed.

## 3. Connectedness and the strict length bound

Since A>0 and the outer first face a exceeds \(r=5/4\), the
only possible circle points lie in the positive first half-plane.
The strict bound \(A^2+B^2<r^2\) gives
\(\beta=\arcsin(B/r)>-\alpha\), where
\(\alpha=\arccos(A/r)\). The other upper bound is
\(\gamma=\arcsin(\min(b/r,1))\). Consequently the exact
closed intersection is the single interval
\([\beta,\min(\alpha,\gamma)]\), and its open interval is
the entire intersection with the square's open interior.

The strict squared comparison
\[
  (\sqrt2 A+B)^2<r^2-B^2
\]
is exactly \(2E<r^2\), with its left base already known positive.
It gives \(A<r\cos(\beta+\pi/4)\). Both compared angles lie
in the decreasing cosine interval, so
\(\alpha-\beta>\pi/4\).

For \(b\le r\), the opposite-face strip difference increases
on \([1/2,r)\), because \(b\ge|b-1|\), and extends
continuously to b=r. Its minimum is
\(2\arcsin(2/5)>\pi/4\). For b>r, the other upper angle is
\(\pi/2\), while \(\beta<\pi/4\). These cases exhaust
the whole upper-face domain and prove the strict length claim.

The center norm satisfies \(k>3/4\) from the actual cap
half-width, and \(k\le(\sqrt{15}-1)/2<3/2\) from the
farthest-corner formula. Hence \(|5/4-k|<1/2\). Its radial
point on the inner circle lies in the actual open inscribed disk,
and therefore in the unique open arc just proved.

## 4. Exact accepted scope

Every actual unit square satisfying the two geometric premises has
one connected open inner-circle arc of length strictly greater than
\(\pi/4\), with its radial-center direction inside. Two such
interior-disjoint squares cannot occupy one free inner-circle
interval of length at most \(\pi/2\).

The source correctly keeps the required routing and actual cap
height estimates separate. It does not assert those premises for
any unproved C6 pocket and makes no global completion inference.
All original means, forces, masks, zero individual circle weights,
transmitters and additional physical squares are unaffected.

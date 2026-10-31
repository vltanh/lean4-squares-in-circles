# Independent full review: a near oblique-facing square forces a small origin-root corner

Date: October 27, 2026.

Reviewer: global_closure, independent of the joint geometric derivation
by c6_side and rooted_blocks.

**Verdict: ACCEPT without correction at the entire stated physical
scope.** This review covers the complete theorem, not just its final
numerical bound.

Reviewed source:

    GENERAL_NEAR_UNIT_OBLIQUE_FACING_CONTACT_SMALL_CORNER.md
    SHA256 9f10979656d694ce78aec002519caa58b792c17ca101d9de38ccea0196fa17ba

I read all 270 lines, reconstructed the whole maximum-support feature
cover and the actual crossing argument, and checked the exact rational
comparisons independently. The separate original two-leaf C4 caller is
reviewed in its own complete source review.

## 1. Exact physical premises and the genuine-leaf own-interval input

The statement requires actual disjoint squares H,B, open origin in H,
one specified actual H own normal h=(s,c), its positive height
sigma<=epsilon, every actual H vertex outside the closed 1/40 disk,
and the actual maximum-g B point N=(epsilon,k). It retains both a
point support and a whole support side with any original actual mean.

The additional own-interval hypothesis is stated explicitly and is
used only where needed. For a real S-leaf root its proof is complete:
an owned radial side contains d e, so the transverse interval contains
zero. At a strictly exposed radial vertex the intervals are
[d a-1,d a] and [d b-1,d b], with a,b>0 and a^2+b^2=1. If both avoided
zero, both lower endpoints would be positive, giving d^2>2.
The real d<61/60 excludes that alternative. Axis endpoints are already
the side case. No B force equation or changed degree enters.

Since O is open in H, the other three own side heights are positive.
The opposite one exceeds 59/60. Any adjacent height<=epsilon would
produce an actual vertex of squared norm at most 2epsilon^2<1/1600.
Therefore every point in the closed epsilon disk satisfies the other
three H inequalities strictly. A point of closed B in that disk must
have h coordinate at least sigma. The equality case is retained for
the subsequent crossing proof.

## 2. Complete signed vertex-support cover

For a unique maximum-g B vertex N, the inward axes
w_B=(-r,-z), v_B=(-z,r), r>0, cover the full possible quadrant containing
-g. The signed z includes both tilt signs and z=0; k>0 excludes the
otherwise degenerate r=0 orientation. The actual support inequalities
give z/r>=-k/A. No positive-z restriction is imposed.

I reconstructed the actual N coordinates (-beta,delta), with
beta=epsilon r+k z and delta=k r-epsilon z. The full alternatives are
correct:

- If beta<=0, then z<0 and delta>0. Both own intervals lie on the
  nonnegative side, and their closest point is the actual corner N,
  whose norm exceeds epsilon.
- If beta>0 but delta<=0, the bounds beta<13/20 and delta>-epsilon
  put zero in both actual own intervals, contradicting closed-origin
  avoidance.
- Otherwise 0<beta<13/20, delta>0, and the actual nearest point is
  p=delta v_B, so delta<=epsilon.

The H half-plane conclusion at this actual p gives
E=r c-z s>0. Together with the full negative-z support bound and the
positive-z H bound, this gives |z|<1/15, r>99/100 and E<37/330.
The crude estimate first fixes D=r s+z c>0; only then does
D^2+E^2=1 give D>49/50. Thus the square-root sign is justified,
including the weak support-angle endpoints allowed in the estimates.

## 3. Complete support-side and variable-mean cover

When B owns its maximum-g side, the actual frame is
w_B=-g, v_B=Jg, and its first interval is [-beta,1-beta],
where beta=N.g<=epsilon. The actual positive transverse coordinate
N.v_B=k(A+epsilon)/sqrt(A^2+k^2) is retained.

If beta<0, the first interval avoids zero. The expressly stated
own-interval hypothesis makes the second interval contain zero.
The actual nearest point (-beta)w_B has negative h coordinate,
contradicting the H half-plane condition for all closed-disk B points.

If beta>=0, the first interval contains zero. The positive actual
coordinate of N and closed-origin avoidance force the second interval
strictly positive, with lower endpoint delta in (0,epsilon].
The same E,D bounds follow. This covers every actual side mean and
both endpoints, including beta=0, where the nearest point may be
a B vertex. No equality of unrelated means is introduced.

## 4. The complete actual-side crossing and H vertex contradiction

In both support cases the actual near B side is
p+t w_B for -beta<=t<=1-beta, with p=delta v_B. The retained condition
delta E>=sigma gives the real nonnegative crossing parameter
lambda=(delta E-sigma)/D. Its strict bound lambda<epsilon/8 is far
below 1-beta>7/20, so the actual side continues a positive length
in direction w_B after the crossing K.

The coordinates and norm are exact:

    K.h=sigma,
    K.j=delta D+lambda E>0,
    |K|^2=delta^2+lambda^2<(65/64)epsilon^2.

If H's positive upper j height exceeded K.j, then K would lie in
the relative interior of its shallow side. For small positive t,
K+t w_B would satisfy all four H own inequalities strictly. It is
a point of the actual closed B, so this contradicts disjoint square
interiors. The argument remains valid when lambda=0 or beta=0:
the positive continuation segment is already established. Equality
at H's upper endpoint is retained, not assumed away.

Thus the upper H vertex has norm at most |K|, strictly less than
1/40. No force on HB, physical HB edge or replacement mean is used.

## 5. Independent exact arithmetic

The following complete exact values were reconstructed using rational
arithmetic, with all strictness coming from the stated strict domains:

    1/1600-2/3600=1/14400;
    1-(1/22)^2-(99/100)^2=21579/1210000;
    1/15-19/288=1/1440;
    1/60+19/30=13/20;
    1-(1/15)^2-(99/100)^2=1391/90000;
    (99/100)^2-1/330=322433/330000;
    1-(37/330)^2-(49/50)^2=36793/1361250;
    1/8-(37/330)(50/49)=137/12936;
    7/20-1/480=167/480;
    1/1600-65/230400=79/230400.

I also reconstructed the two orthogonal coordinate identities for N
and D^2+E^2=1 directly. The source's complete physical feature cover
and all closed tangent endpoints pass without correction.

The source may remain frozen at the reviewed pin. Parent root review
and the separate complete original-family join remain distinct.
No proof source, graph label, ledger, remote object, Lean file, CI
job or workflow was changed by this review.


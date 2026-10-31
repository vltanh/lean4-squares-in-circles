# Independent review: the radial two-mean derivative inequality

Date: October 26, 2026.

**Result: PASS for the complete scalar source and its stated scope.**

Reviewed source:
[SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md](SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md).

## 1. Positive clearing and the full domain

I independently rederived the clearing of the displayed derivative
bracket. With \(D=1-ur\), \(k=(1-u)/D\), multiplication by
\(a^2(u+r)D^3>0\) gives

\[
 D^3\{a(u+r)-(1+u)\}\{2a(1-k)+k^2\}
 -r(1+u)(u+r)D^2(a-k)^2.
\]

Its coefficients in \(a\) are exactly the three displayed \(A_2,A_1,A_0\).
This verifies the identity before any endpoint reduction. Every factor
cleared is positive on \(a\ge4/3,\ 4/7\le u\le1,\ 1/2\le r<1\).
In particular \(D>0\), including \(u=1\), because \(r<1\).

The proof of \(A_2\le0\) covers both ranges of \(r\). The possible
equality \(u=1,r=1/2\) is harmless: the endpoint value and its derivative
are both strictly negative there. The use of \(A_2\le0\), rather than
an unwarranted strict sign, is correct.

## 2. Endpoint value and endpoint derivative

I independently reconstructed all polynomial identities with exact
rational polynomial arithmetic:

* the full expansion of \(-9P(4/3,1-x,1-y)\);
* the identity \(4B_2B_4-B_3^2=64(1-x)^3W(x)\);
* the factorization \(-3P_a(4/3,1-x,1-y)=D\,T(x,y)\);
* the cubic endpoint-chord identity in the derivative proof.

These are identity checks, not sampled sign evidence.

The cubic factor in \(B_1\) is decreasing and has endpoint value
\(1291/343>0\). The stated lower bound
\(W''\ge10612/49>0\) follows by dropping the nonnegative cubic term
and using \(x\le3/7\) in the negative terms. Its exact endpoint values are

\[
 W'(3/7)=-60496/2401<0,\qquad
 W(3/7)=325146/16807>0.
\]

Thus the completed-square argument proves the quadratic in \(y\)
strictly positive for every real \(y\). Because \(y=1-r>0\), this
proves the required strict sign of the endpoint value on the entire
rectangle, including \(x=0\) and \(y=1/2\).

For the derivative, \(T_0\ge0\), and

\[
 T(x,1/2)\ge165/343>0,\qquad
 V(x)+W_3(x)\le-2034/343<0.
\]

The first bound follows from an increasing polynomial in \(u\);
the second from an increasing polynomial in \(x\). The exact chord
remainder has two nonpositive factors and is nonnegative on
\(0\le y\le1/2\). Its chord is strictly positive when \(y>0\).
This proves \(P_a(4/3,u,r)<0\) on the complete physical scalar domain.

Since \(P_a\) is nonincreasing in \(a\), the two endpoint signs prove
\(P<0\) for every \(a\ge4/3\), without an upper bound on \(a\).

## 3. Geometry and scope

I also checked the formal substitutions

\[
 A=as(u+r),\quad Z=as(1-ur),\quad C=s(1+u),\quad t=k/a,
\]

which give exactly the displayed bracket when
\(t'=HC/Z^2\) and \(H=Z-(s-c)\). The source correctly leaves
the actual physical chart, the derivative formula for the norm,
the connected interpolation, and the root bound \(\eta<\pi/3\)
to the separate geometric join.

No actual shared mean is moved, no individual radial weight is
deleted, and no completion or original gate is asserted by this
scalar source alone. No coefficient packet, interval subdivision,
numerical pose, Lean compilation, or CI result is a premise.

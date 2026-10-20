# The angular envelope for positive normal GA entry

## 1. Constants, coefficient families, and conclusion

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,\quad
 K=13/12,\quad k=.863,\quad \phi(t)=\cos t+\sin t .
\tag{1}
\]
All terminating decimals are exact rationals. For \(0\le d\le h\),
use one of the two families
\[
\begin{array}{c|c|c|c|c}
 &l&c&\eta&\lambda\\ \hline
 P&.5052+.49d-.108d^2&k&.25+.1645d&1.03\\
 N&.5054+.55d-.2d^2&.863+.35d-.15d^2&.38&.8888+.2d .
\end{array}
\tag{2}
\]
The family letter P is distinct from the positive angular total.
For \(0<p\le q\), define
\[
\begin{split}
 N_{p,q}(t)&=\sqrt{p^2+q^2+2pq\sin t},\\
 U_{p,q}(t)&=p\{\phi(t)-1\}-R\{N_{p,q}(t)-N_{p,q}(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)-R\{N_{p,q}(-t)-N_{p,q}(0)\},\\
 \Psi_{p,q}(P,N)&=p\{\phi(P)-1\}+q(\cos N-1)
                      -R\{N_{p,q}(P-N)-N_{p,q}(0)\}.
\end{split}
\tag{3}
\]
The ordinary outer pairs are
\[
                 H:(1,n),\quad A:(k,l),\quad B:(l,m),\quad D:(1,c).
\tag{4}
\]
In family P, \(n=kf(x),m=kf(z),x+z=d\), with
\(f(t)=\cos t+\eta\sin t\). The second tilted coefficient can
instead be moved from B to D, leaving B equal to \((l,k)\).
In family N, \(x=d,n=kf(d),m=c\).

A removed negative E primary may give H or D a one-angle
sorted-support minorant
\[
 -\gamma(s)t\quad(t\ge0),\qquad V_{k,1}(-t)\quad(t\le0),
 \qquad \gamma(s)=.545q_0\sec s,\quad q_0=\max(1,c)\le1.0345,
\tag{5}
\]
where s is the total magnitude of the removed negative primaries.
A genuine negative TD2 may replace the ordinary D pair by
\((1,c\sec t)\), \(t<.3\). A genuine negative BT3 with TD aligned
may replace B by \((l,c\sec t)\), \(t<.09\); that B block then
has only its AB angle.

Suppose the remaining actual signed angles satisfy
\[
 N_{\rm tot}-P_{\rm tot}=d-s,\qquad
 P_{\rm tot}\le h-d,\qquad N_{\rm tot}\le h-s.
\tag{6}
\]
Then their total angular increment is at least
\[
 \boxed{\begin{cases}
 V_{l,k}(d-s),&0\le s\le d,\\
 -\gamma(s)(s-d),&d\le s\le h .
 \end{cases}}
\tag{7}
\]
Also every possible single negative block at h satisfies
\[
                         V_{\rm block}(h)>l-.0696.
\tag{8}
\]
The proof below applies to actual weak witnesses and both AB
owners. It changes no geometric angle.

## 2. Ordinary blocks and exact concentration

For two incident weights \(\alpha,\beta\), the outer force norm
is
\(\sqrt{\alpha^2+\beta^2+2\alpha\beta\sin(u+v)}\).
An absent rotation is zero. The formula remains true when an
actual AB0 or AB2 assigns its rotation to the corresponding
outer endpoint. Combining its threshold
\(W(t)=(1+\cos t+|\sin t|)/2\) with the half-coordinate shifts
gives the trigonometric contribution
\[
                         \psi(t)=\cos t+\max(\sin t,0)-1.
\]
With \(p=\min(\alpha,\beta),q=\max(\alpha,\beta)\), concavity
and the zero values at the origin imply
\[
 \sum\alpha_i\{\phi(P_i)-1\}\ge p\{\phi(\sum P_i)-1\},\qquad
 \sum\alpha_i(\cos N_i-1)\ge q\{\cos(\sum N_i)-1\}.
\]
Thus the block is at least \(\Psi_{p,q}(P,N)\), with its actual signs.

For \(p/q\ge1/2\), Section 3 of
[the whole-angle concentration note](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
proves separate concavity of \(\Psi\) on \([0,h]^2\), and
concavity of U and V on \([0,h]\). First concentrate each
sign in one of its originally occupied blocks. Thus a block
with only one actual angle never acquires both signs in this
reduction. The remaining alternatives are one
\(\Psi\), or one U and one V. Along \(N-P=d-s\), varying
the total P is again a concave problem: the same-block norm
argument is constant, while its two trigonometric terms are
concave; separate blocks use concavity of U and V.
Only a pure sign or the saturated totals
\[
                              P=h-d,\quad N=h-s
\tag{9}
\]
remain. The enlarged modified block
\(-\gamma P+V_{k,1}(N)\) is separately concave as well.

We use the established universal estimates
\[
 U_{p,q}(t)\ge-.545qt,\qquad V_{p,q}(h)>.87p,
\tag{10}
\]
from [the scalar envelopes](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
V increases in its smaller coefficient. The
[near-equal-weight lemma](HAND_G3_NEGATIVE_NORM_MONOTONICITY_FOR_NEAR_EQUAL_WEIGHTS.md)
also gives
\[
 V_{n,1}\ge V_{k,1}\ge V_{k,k}\ge V_{l,k}
 \quad(.86\le k\le n\le1,\ l\le k),
\tag{11}
\]
and \(V_{p,q}\ge V_{k,k}\) when \(p\ge k,\ p/q\ge.86\).

## 3. The varying B coefficient

Here is a correlated comparison valid on the whole interval:
\[
 0<l\le k\le q,\quad 0\le t\le d\le h,\quad
 l/q\ge r(d):=.585+.255d
 \quad\Longrightarrow\quad V_{l,q}(t)\ge V_{l,k}(t).
\tag{12}
\]
At fixed l, put \(r=l/q\). Direct differentiation gives
\[
 D_r(t):=\partial_qV_{l,q}(t)
 =\cos t-1+R\int_0^{\sin t}I(r,u)\,du,\qquad
 I(r,u)=\frac{r^2(r-u)}{(1+r^2-2ru)^{3/2}}.
\tag{13}
\]
After removal of its positive denominator, the numerator of
\(\partial_r I\) is
\[
                 r\{r(3+u^2)-2u(1+r^2)\}>0
\]
on \(1/2\le r\le1,\ 0\le u\le.645\). The braces increase in
r and decrease in u; their least value is .0955125.
It suffices to use \(r=r(d)\), for which
\(r<.764\) and \(r>\sin d\). Moreover
\[
 I_u=\frac{r^2(2r^2-1-ru)}{(1+r^2-2ru)^{5/2}},\qquad
 I_{uu}=\frac{3r^3(3r^2-2-ru)}{(1+r^2-2ru)^{7/2}}<0.
\]
Hence \(I_u\le I_u(r,0)<.1\), and \(I\ge0\). Therefore
\[
 D_r''(t)=-\cos t+
 R\{-\sin t\,I(r,\sin t)+\cos^2t\,I_u(r,\sin t)\}
                         <-.7648+.1R<0.
\tag{14}
\]

The intrinsic endpoint \(D_{r(d)}(d)>0\) has one rational
polynomial certificate. Let \(S_j,C_j\) be the usual Taylor
polynomials and set
\[
\begin{split}
 A&=1+r^2,\quad B_-=A-2rS_9,\quad B_+=A-2rS_{11},\\
 H&=Qr^2S_{11}(2r-AS_9)+(1-C_{12})^2AB_-,\\
 {\cal P}(d)&=\{H^2-4Q(1-C_{10})^2AB_+^2\}/d^2.
\end{split}
\tag{15}
\]
All polynomials are evaluated at d. The quotient is a polynomial,
including at zero, and the whole-interval bounds are
\[
 \deg{\cal P}=70,\quad {\cal P}>.07925,\quad
                  2r-AS_9>.5022,\quad r-S_9>.095.
\tag{16}
\]
The exact coefficient operator and checks are given in
[the scalar companion](HAND_G5_POSITIVE_GA_CORE_E_SCALAR_CERTIFICATES.md).
To verify the certificate direction, write
\(u=\sin d,v=1-\cos d,B=A-2ru\). The required inequality is
\(R/\sqrt A-v>R(1-ru)/\sqrt B\); both sides are positive.
Its first positive square is equivalent to
\[
 Qr^2u(2r-Au)+v^2AB>2Rv\sqrt A\,B.
\]
The left side is positive and at least H. The square of the
right side is at most the subtracted term in (15).
Thus (16) proves the endpoint. Concavity (14), \(D_r(0)=0\),
and monotonicity in r prove (12).

For family P, \(0\le z\le d\) gives
\[
 \cos z+\eta\sin z\le1+.25d.
\tag{17}
\]
Indeed \(\cos z\le1-.479z^2,\ \sin z\le z\), and the
remaining difference is
\((d-z)(.25-.1645z)+(.479-.1645)z^2\ge0\).
The exact coefficient checks are
\[
 l_P-r(d)k(1+d/4)>.000344,\qquad l_N-r(d)c_N>.000544.
\tag{18}
\]
Thus (12) covers B, while (11) covers H/D.

For the short modified B, let \(t<.09\), \(t\le s\le d\),
and \(w=d-s\). Then
\[
 \frac l{c\sec t}\ge r(d)\cos t
 \ge r(d)(1-t^2/2)\ge r(d-t)\ge r(w),
\tag{19}
\]
since \(.255-.764(.09)/2>0\).
Apply (12) at argument w. This B has only one remaining angle.

## 4. Same-block saturation

If \(s\le d\), put \(w=d-s\). An ordinary saturated block
satisfies
\[
 \Psi(h-d,h-s)-V(w)
 =p\{\phi(h-d)-1\}+q\{\cos(h-s)-\cos(d-s)\}.
\tag{20}
\]
At fixed \(P=h-d\), the right side decreases with w, so its
least value occurs at \(w=d\). Dividing by q and using
\(p/q\ge r(d)\) leaves
\[
 \sin(h-d)
 \left[r(d)-\sin h+\{\cos h-r(d)\}\tan\frac{h-d}{2}\right]\ge0.
\tag{21}
\]
The bracket exceeds .006 at zero. While \(r\le\cos h\), its
derivative is at least
\(.255(1-.366)-.18(1+.366^2)/2>0\); afterwards the derivative
is plainly positive. The short modified B needs no such
comparison because it has only one angle.

If \(s\ge d\), let \(w=s-d\), so \(P=N+w\).
Then
\[
                 \Psi(P,N)-U(w)
       =p\{\phi(P)-\phi(w)\}+q(\cos N-1)\ge0.
\tag{22}
\]
The necessary ratio is at most
\(\tan(h/2)/(1-\tan(h/2))<.366/.634<.585\).
For completeness, its maximum follows by differentiating
\(\sin a/\{\cos(P-a)-\sin(P-a)\}\): after its positive
denominator is removed, the derivative is
\(\cos P-\sin P>0\).
Every block which can contain both signs has ratio at least .585.

## 5. Separated blocks and the secant coefficient

For \(p/q\ge2/3\),
\[
 \frac{V'_{p,q}(u)}q=-\sin u+
 \frac{R(p/q)\cos u}{\sqrt{1+(p/q)^2-2(p/q)\sin u}}
\tag{23}
\]
increases with \(p/q\). At the fixed ratio \(2/3\),
\[
 V'_{2/3,1}(h)>.6744,\qquad -V''_{2/3,1}(u)>.25823.
\tag{24}
\]
The first is one positive square. For the second, use
\(-RN''(-u)\le-RN''(0)<.50661\) and \(\cos h>.76484\).
Consequently, if \(u\le h-s,\ q\ge k\),
\[
 V'_{p,q}(u)\ge k(.6744+.25823s)
                            >.545(1.0345)\sec s.
\tag{25}
\]
The last difference is concave in s. It is positive at zero
and at h; at h, \(\sec h<1.308\) gives a reserve greater
than .00054.

For \(d\ge.3\), every ordinary block has ratio at least \(2/3\).
For the unmodified families, check the concave polynomials
\(l_P-\tfrac23k(1+d/4)\) and \(l_N-\tfrac23c_N\) at .3 and h.
For short B, check \(l_NC_6(.09)-\tfrac23c_N\) at those same
two endpoints. Modified D has larger coefficient below 1.084
and ratio above .86. Thus (25) handles every separated
alternative, including an enlarged modified block containing
both signs.

For \(d\le.3,\ s\le d\), all ordinary larger coefficients are
at most one, since \(c_N(.3)\sec(.3)<1\). Here
\(\gamma(s)<.571,\ V'_{l,k}(0)<1.04,\ l\ge l_P\).
Concavity and (10) yield
\[
 V_{\rm block}(h-s)-V_{l,k}(d-s)-\gamma(s)(h-d)
 \ge .87l_P-1.04d-.571(h-d)>.01855.
\tag{26}
\]
To check the first inequality, use
\(V_{\rm block}(u)\ge(.87l/h)u\) and
\(.87l/h-1.04<0\). The final quadratic is concave; its
endpoint checks at 0 and .3 prove the bound.

For \(d\le.3,\ s\ge d\), use
\[
 V_{.5052,q}(u)>.545\sec(h-u)\,u,\qquad q\in\{k,1\}.
\tag{27}
\]
For q=k, the square-root upper estimate
\(\sqrt{1-z}\le1-z/2-z^2/8\) gives
\(V\ge q(\cos u-1)+.8627\sin u+.1880\sin^2u\).
For q=1, replace the last two coefficients by .8922 and .1795.
The secant chord is \(\sec s<1+.44s\). After Taylor bounds,
the polynomial quotients
\[
 \{q(C_{10}-1)+aS_{11}+bS_{11}^2
                       -.71286u+.2398u^2\}/u
\tag{28}
\]
have lower bounds .0704 and .0465 on the entire interval.
V is concave in its larger coefficient on ratio at least
\(1/2\): the second derivative is
\[
 -Rp^2\left\{\frac{\cos^2u}{N_{p,q}(-u)^3}
                         -\frac1{N_{p,q}(0)^3}\right\}\le0,
\]
using \(2pq/(p^2+q^2)\ge.8>\sin u\).
Together with smaller-coordinate monotonicity, this extends
(27) to every low ordinary block. The H/D blocks in (11)
also satisfy it. Thus every separated alternative is at
least \(-\gamma(s)(s-d)\).

The pure alternatives, (20)--(22), and these separated
comparisons prove (7).

## 6. The actual one-angle support bound

The modified H/D estimate (5) is the sorted-support result in
[the secant-D note](HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md),
with its comparison coefficient extended from .85 to .863.
Only its final diagonal slope comparison changes:
\[
 V'_{k,1}(t)\le Rk/\sqrt{1+k^2}<1.294<1.327.
\]
The actual diagonal increment has derivative greater than 1.327.
All other hypotheses remain valid:
\(1\le q=\sec s<1.308,\ .7\le c_{\rm rot}\le1.4\).
Writing the baseline with the full-circle support only
increases the actual increment, so the estimate remains valid
with the full-circle baseline used here.

For a negative TD2 the remaining D angle is DE. Its full-circle
pair \((1,c\sec t)\), \(t<.3\), is ordinary and has ratio
greater than .86; (11) handles its negative increment.
When DE is also a removed negative primary, D has no angle.

## 7. The common far negative endpoint

Every block satisfies
\[
                         V_{\rm block}(h)>l-.0696.
\tag{29}
\]
For H/D use (11). For A/B it suffices to prove
\(V_{p,q}(h)-p+.0696>0\) on
\(.5052\le p\le.8,\ k\le q\le1.04\).
This function is concave separately in p and q. Indeed
\(p/q>.48,\ [2pq/(p^2+q^2)]\sin h>1/2,\ \cos^2h>1/2\);
these give the negative sign of both second derivatives
directly from the two norm denominators.
At the four intrinsic rectangle corners the rational lower
reserves are, respectively,
\[
 .03026,\quad .000314,\quad .00269,\quad .02651.
\tag{30}
\]
The scalar companion records the radical brackets.
Short B satisfies \(c\sec(.09)<1.04\), and modified D was
already reduced by (11). This proves (29).

## 8. The common linear secant gain

Define
\[
 F_a(s)=\sec s+K\tan s-R\sqrt{\sec^2s+a^2}
                                      -1+R\sqrt{1+a^2}.
\tag{31}
\]
It increases with a, and
\[
                             F_k(s)>1.03s\quad(0<s\le h).
\tag{32}
\]
Set \(C_0=1.613775,A_2=.557855,A_4=.059531\).
Positive squares give
\[
 R\sqrt{1+k^2}-1<C_0,\quad
 Rk^2/(2\sqrt{1+k^2})>A_2,\quad
 Rk^4/(8(1+k^2)^{3/2})>A_4.
\]
After multiplication by \(\cos s\), the square-root estimate
above bounds \(F_k(s)-1.03s\) below by
\[
 K\sin s-1.03s\cos s-C_0(1-\cos s)+A_2\sin^2s+A_4\sin^4s.
\]
Use \(S_{11}\), \(C_{12}\) for the negative cosine term, and
\(C_{10}\) for the last \(1-\cos\). The polynomial divided by s,
expanded at .45, has
\[
 b_0>.0019416,\quad |b_1|<.000845,\quad
 b_2-\sum_{j\ge3}|b_j|(.45)^{j-2}>.12849.
\]
Completion of the square gives reserve greater than .0019402,
proving (32).

In family N,
\[
 \lambda\le1.03,\quad \lambda\le1.03c,\quad c^{-1}>k.
\tag{33}
\]
Thus a negative TD2 secant gains
\(cF_{1/c}(t)\ge\lambda t\), while negative E secants gain
\(F_n(s)\) or \(F_c(s)\), each at least \(\lambda s\).
If two negative secants act on D's two coordinates, their
gains add: the mixed derivative of \(\sqrt{u^2+v^2}\) is
\(-uv/(u^2+v^2)^{3/2}<0\).

For short negative BT, \(r=l/c\ge1/2,\ t<.09\). The square
bound \(R/\sqrt{1+r^2\cos^2t}<1.78\) gives
\[
 F_r'(t)\ge K-.78t,\qquad F_r(t)>(K-.39(.09))t>1.048t.
\tag{34}
\]
Also \(1.048c-\lambda=.015624+.1668d-.1572d^2>0\), by
concavity and its two endpoints. Hence this secant also
gains at least \(\lambda t\).

Together with (7), these gains leave only
\[
                         V_{l,k}(d)\quad\hbox{or}\quad\lambda d.
\tag{35}
\]
For \(s\le d\), minimize the concave function
\(\lambda s+V_{l,k}(d-s)\) at its endpoints.
For \(s\ge d\), use \(\lambda\ge.8888>\gamma(s)\), since
\(.545(1.0345)(1.308)<.738\).
This covers every number and location of the specified
negative flat-core primaries, including two negative E errors.

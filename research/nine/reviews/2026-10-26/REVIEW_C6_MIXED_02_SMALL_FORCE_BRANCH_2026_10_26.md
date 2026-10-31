# Independent review: mixed 110, shares 02, full q >= p branch

Date: October 26, 2026.

**Result: PASS for the exact branch claimed.** Independently reviewed
the complete saved source
SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md, including the
original physical normalization, both closure identities, every
monotonicity, the radical endpoint, and the exact positive reserve.
This review does not treat the complementary q < p branch or either
other two-share orbit as closed.

No numerical sampling, optimizer output, interval grid, or polynomial
coefficient certificate is a premise of this review. The fixed
rational comparisons below were independently reproduced with exact
fraction arithmetic. No Lean compilation or CI was run.

## 1. Original physical join and local vectors

The complete cover in
SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md has three
two-share orbits. The reviewed source concerns exactly its third row:
corner bits 110, outgoing genuine share at loaded unit 0, incoming
genuine share at loaded unit 2, and nonshared loaded unit 1. Its force
order assumption is the original \(\mu_2\ge\mu_1\), which becomes
\(q\ge p\) only after division by \(\mu_0>0\).

I independently expanded the true local support vector at unit 1:

\[
 f_0+J(f_0-f_1)=(1+ps_1,1+pc_1).
\]

Consequently its squared norm is
\(2+p^2+2p(s_1+c_1)\). The constant term 2 is essential and is
correct throughout this source. The two actual shared directions are
\(u_0=(0,-1)\), \(u_2=(-s_1,-c_1)\). Their chord lengths remain
\(1-qA_0\) and \(1-(q/p)A_2\). In particular no genuine shared
mean with chord one is relabeled as nonshared.

The original force-value identities give

\[
 E_0=1+qh_0,\quad E_1=L,\quad E_2=p+qh_2,
\]

and hence exactly the stated numerator
\(N=2+2p+q(1+h_0+h_2)+L\). All three denominator terms have the
correct force pairs and cosine signs. The physical identity
\(R\sum D_i=N\) follows from the retained original equations; no
new square, aggregate body, or force has been substituted.

## 2. Both closure identities and the small-force consequence

Writing \(u_1=(X,Y)\), direct expansion of the two coordinates of
the actual closure equation gives

\[
 X=h_1+c_0-1-(q/p)A_2s_1,
\]
\[
 Y=1+s_0-s_1+c_1-qA_0-(q/p)A_2c_1.
\]

Subtracting and using \(X-Y=pA_1/L\) gives the source's second
identity exactly:

\[
 (q-1)A_0=2(1-s_1)+A_1[p/L+(q/p)A_2].
\]

Because the original \(\theta_1>\pi/2\), the right side is
strictly positive. Thus the recorded conclusions \(A_0>0\) and
\(q>1\) are valid. The branch proof itself correctly does not rely
on the latter restriction after its Cauchy elimination.

The trig identity \(c_0-A_2s_1=A_1c_2\) follows immediately from
the original angle sum. When \(q\ge p\), it gives

\[
 1/\sqrt2\le X\le h_1-1+A_1/\sqrt2.
\]

I checked the half-angle factorization of the last upper bound minus
\(1/\sqrt2\). It gives
\(\tan((\theta_1-\pi/2)/2)\le(\sqrt2-1)^2\).
At equality the corresponding sine is exactly \(1/3\), so the
closed enlargement \(c_1\le1/3,\ s_1\ge2\sqrt2/3\) is correct.

The bound \(X\le\sqrt3-1\) uses an ordinary Cauchy inequality.
Since \(X^2+Y^2=1\), it gives the exact ratio bound
\(X/Y\le\sqrt{2/\sqrt3}\). The source then derives

\[
 p\le\frac{3(H-1)}{2\sqrt2-H}<\frac3{23}<\frac17.
\]

The denominators are positive, and both substitutions have the
required directions. The subsequent scalar enlargement to
\(0\le p\le1/7\) is justified.

## 3. Cauchy elimination of the whole unrestricted force

Concavity of \(h\) on the complete angular interval gives the exact
minimum
\(h_0+h_2\ge\sqrt2(1+s_1)\); it is reached at one of the two
allowed angular endpoints. The stated upper bound
\(h_0+h_2\le2\sqrt2\) is also valid. Thus \(0<C<K\) and
\(T=\sqrt{K^2-C^2}>0\) throughout the entire enlarged domain.

The two inequalities

\[
 D_2\ge q+pc_2,\qquad
 KD_0\ge C(q+c_0)+Ts_0
\]

have positive right sides and follow respectively by subtracting
squares and by Cauchy. The coefficient of \(q\) cancels because
\(C=B-K\). The resulting lower gap is exactly the displayed \(G\).
This step is pointwise for every positive \(q\); it does not choose
or alter the original force.

## 4. Angular derivative with the coupled C,T retained

With \(B'=A_0-A_2\), independent differentiation gives

\[
 \frac{d}{d\theta_0}(Cc_0+Ts_0)
   =(T-B')[(C/T)s_0-c_0].
\]

I also checked the identity

\[
 (h_0+h_2)^2+(A_0-A_2)^2=4+4s_1,
\]

which gives exactly

\[
 T^2-(B')^2=2(K-1)B-3-4s_1.
\]

The source retains the negative coefficient of \(s_1\) when
inserting its lower bound for \(B\), so the minimum is the stated
\(\delta=-101/20+(39/10)\sqrt2>9/20\).

The stronger inequality \(C/T>\cot(\theta_1/4)\) is valid:
the auxiliary function is strictly concave and has positive values at
both endpoints. The two exact endpoint reserves, after the specified
root bounds, are

\[
 1+\frac{280}{99}-\frac{79}{40}\frac{77}{40}
       =\frac{4183}{158400}>0,
\]
\[
 \frac73+\frac{140}{99}-\frac{79}{40}\frac{17}{9}
       =\frac{67}{3960}>0.
\]

The two signs of \(B'\) are handled correctly. For \(B'\ge0\),
monotonicity of \(A\) yields \(\theta_0\le\theta_2\), and the
half-angle bound makes the second derivative factor greater than
one. For \(B'<0\), the two factors have the stated independent
positive lower bounds. Both give a derivative strictly greater than
\(3/10\). The remaining \(Kpc_2\) term has derivative
\(-Kps_2\), so

\[
 \partial_{\theta_0}G>3/10-K/7=1/56.
\]

Thus the minimum really is on the full face
\(\theta_2=3\pi/4\), with no missing endpoint or angle branch.

## 5. Force and final-angle monotonicities

On that face, the derivative of \((p+h_1)/L\) is exactly
\((2-h_1^2)/L^3\ge0\). This confirms the bound used to prove
\(\partial_pG<0\), and hence the reduction to \(p=1/7\).

For \(t=c_1\), \(s=\sqrt{1-t^2}\), I independently differentiated

\[
 H=\frac1{\sqrt2}[(s-t)C+(s+t)T]
\]

using \(C'=-\sqrt2t/s\) and \(T'=\sqrt2Ct/(sT)\). The result
factors exactly as

\[
 H'=-\frac1{\sqrt2}
       [(C-T)+(C+T)t/s]\left(1-\frac{\sqrt2t}{T}\right).
\]

The auxiliary identity
\(T^2-2t^2=\delta+2\sqrt2a(1-s)\) is also correct.
It proves the uniform factor bound in the source. The two elementary
factor estimates on \(t\le1/6\) and \(t\ge1/6\) have respective
strict reserves over \(3/10\) equal to

\[
 \frac{35}{104}-\frac3{10}=\frac{19}{520},\qquad
 \frac{77}{234}-\frac3{10}=\frac{17}{585}.
\]

The remaining radical has positive derivative because \(s>t\).
Thus the stated strict derivative \(G'<-1/56\) follows, and the
last minimum is at \(t=1/3\).

## 6. Exact radical corner and final reserve

Independent substitution gives

\[
 D^2=164/147,\qquad
 L_*^2=(311+28\sqrt2)/147,\qquad
 T_*^2=(319-129\sqrt2)/180.
\]

At this point \(C=43/120+\sqrt2\),
\(c_0=(4-\sqrt2)/6\), \(s_0=(4+\sqrt2)/6\).
The constant part of \(Kp/\sqrt2+Cc_0\) is exactly

\[
                -17/180+(377/504)\sqrt2,
\]

which confirms every term of the endpoint formula.

The three displayed squared reserves in the source were reproduced
exactly:

\[
 1172/2296875,\qquad 11707/5880000,\qquad 617/63000000.
\]

All substituted radical coefficients have the required positive
signs. The final rational expression is exactly

\[
                         11891/2835000>0.
\]

Some other independently checked supporting reserves are

\[
 \frac{43}{120}+\frac{140}{99}-\frac{23}{13}
       =\frac{167}{51480}>0,
\]
\[
 \left(\frac{23}{13}\right)^2-\frac45
           \left(\frac{79}{40}\right)^2
       =\frac{3271}{338000}>0,
\]
\[
 -\frac{101}{20}+\frac{39}{10}\frac{140}{99}
             -\frac9{20}=\frac1{66}>0.
\]

## 7. Accepted conclusion and remaining scope

The saved source proves, for every original mixed 110 two-share
configuration with shares at 02 and \(\mu_2\ge\mu_1\),

\[
 \frac{79}{40}\sum_iD_i-N
      >\frac{11891}{2835000}\mu_0>0.
\]

Its original positive virial identity therefore contradicts
\(R\ge79/40\). Both actual shared means, all individual corner
weights and masks, the complete transmitter intervals, and all three
physical extra squares are retained. The proof uses only necessary
consequences of their true equations.

The complementary force ordering must still be joined before the
whole mixed 02 orbit is excluded. The two other symmetry orbits
need their own complete proofs before the full two-share family is
excluded. No broader gate or equality claim is certified by this
review.

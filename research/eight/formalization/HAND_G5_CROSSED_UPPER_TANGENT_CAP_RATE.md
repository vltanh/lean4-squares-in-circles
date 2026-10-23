# The crossed inverse-HG cap loses less than the opposite hard cap gains

## 1. The rate comparison on the upper tangent interval

Put
\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
 \qquad q_L\le q\le Q.
\tag{1}
\]
Suppose a crossed HG0 side has already reached GA alignment,
with common A/B frame \(\rho\),
\(r=\rho-\theta_H\in[0,1/25]\), and
\(u=\rho-\theta_T\ge0\). At an active middle cap-sum
boundary write
\[
 Y=b_A+\frac12,\qquad B=b_B+\frac12=2-Y,
 \qquad \frac{26}{25}\le Y\le\sqrt{q-\frac94}.
\tag{2}
\]
Both middle corners are on their q-circles. Retain the actual
BT2 contact with \(b_T\ge0\), and the minimum G tangent
allowed by the actual HG0 contact and its own q-circle.

**Rate lemma.** When the common frame and G move together
toward H, the B transverse cap increases faster than the A
transverse cap decreases. More precisely, if \(\mathcal A\)
is the positive derivative of the inverse-HG A cap with
respect to increasing r and \(\mathcal B\) is minus the
derivative of the B cap with respect to increasing u, then
\[
 \mathcal B-\mathcal A>
 \frac9{1000}+\frac3{20}\left(Y-\frac{26}{25}\right)>0.
\tag{3}
\]
This uses no restriction on u beyond the actual hard contact.
It is a rate lemma on the upper tangent interval; the lower
tangent interval and the global continuation argument are
separate inputs to the common-frame clamp.

## 2. The inverse-HG rate and its whole-interval derivative

Set
\[
 R=\sqrt{q-Y^2},\quad D=R-1,\quad
 X=\sqrt{q-D^2},\quad t=\tan r,\quad k=D/X.
\tag{4}
\]
The aligned GA contact has G transverse corner D. At an
unsaturated HG0 contact, implicit differentiation of
\[
 X\sin r+D\cos r=\frac12+\cos r+\sin r-b_H
\]
gives
\[
 -D_r=\frac{(X-1)\cos r+(1-D)\sin r}
                         {\cos r-(D/X)\sin r}
       =E(D,r):=X-1+\frac{t(1-k)}{1-kt}.
\tag{5}
\]
Since \(Y^2+(1+D)^2=q\), the A cap rate is
\[
                         \mathcal A=\frac RY E.
\tag{6}
\]
When the G tangent floor is active, D is instead the constant
\(1/2\) and the A cap is constant. Its zero rate is smaller
than the positive expression in (5), so it suffices to prove
the estimate for (5) there as well. The two cap pieces meet
continuously at the floor, with their respective one-sided
rates.

At fixed q and r,
\[
 E_D=-k-\frac{q}{X^3}\frac{t(1-t)}{(1-kt)^2},
 \qquad
 \mathcal A_Y=-\frac{qE}{RY^2}-E_D.
\tag{7}
\]
The whole domain (1)--(2) satisfies
\[
 R\ge\frac32,\quad D<.708,\quad X>1.847,
 \quad E>.847,\quad k<.384,\quad 0\le t<.0401.
\tag{8}
\]
The last comparison follows from the degree-five upper sine
and degree-six lower cosine at \(1/25\). All terminating
decimals in this note are exact rational numbers.
Substitution into (7) gives
\[
 -E_D<.384+
 \frac{Q}{1.847^3}\frac{.0401}{(1-.384\cdot.0401)^2}
 <\frac5{12}.
\tag{9}
\]
For the other factor, write
\[
 \frac q{RY^2}=\frac1R+\frac{R}{q-R^2}.
\]
This increases with R whenever \(3R^2>q\), and decreases
with q at fixed R. Thus
\[
 \frac q{RY^2}\ge\frac23+\frac{3/2}{Q-9/4}.
\]
Equations (7)--(9) imply
\[
 -\mathcal A_Y>
 \frac{847}{1000}\left(\frac23+\frac{3/2}{Q-9/4}\right)
                           -\frac5{12}
 =\frac{632087}{694000}
 =\frac9{10}+\frac{7487}{694000}>\frac9{10}.
\tag{10}
\]
This derivative estimate holds for the entire Y interval at
each fixed q and r.

## 3. The weakest opposite rate occurs at the zero-tangent hard endpoint

Put
\[
                         Z=\sqrt{q-B^2}.
\]
The actual hard contact implies
\[
 (Z-1)\cos u-B\sin u\ge\frac12+b_T\ge\frac12.
\tag{11}
\]
Its transverse cap rate is
\[
 \mathcal B=Z\frac{(Z-1)\sin u+B\cos u}
                         {B\cos u+Z\sin u}
           =Z\frac{B+(Z-1)\tan u}{B+Z\tan u}.
\tag{12}
\]
For fixed q and B this decreases with u, since its derivative
with respect to \(\tan u\) is
\(-ZB/(B+Z\tan u)^2<0\).

Let z be the unique nonnegative solution of
\[
                         (Z-1)\cos z-B\sin z=\frac12.
\tag{13}
\]
Then (11) gives \(u\le z\). Write
\[
 s=\sin z,\quad c=\cos z,\quad
 U=(Z-1)\sin z+B\cos z
                     =\sqrt{q+\frac34-2Z}.
\]
It follows that
\[
             \mathcal B\ge\beta(B):=\frac{ZU}{U+s}.
\tag{14}
\]
Thus it remains to compare \(\beta(2-Y)\) with (6).

## 4. The opposite endpoint rate changes slowly with the tangent

Differentiating (13) at fixed q gives
\[
 z_B=-\frac{1+s/U}{Z},\qquad U_B=\frac B{ZU}.
\]
Consequently
\[
 \beta_B=
 \frac{c-BU/Z}{U+s}+\frac{Bs}{U(U+s)^2}.
\tag{15}
\]
Throughout the complete interval in (2),
\[
 .709<B\le.96,\quad Z<1.85,\quad U>.98,
                         \quad 0<z<.41,\quad s<.4.
\tag{16}
\]
For the angle bound, one may substitute
\(Z-1<.848\), \(B>.709\) into (13) and evaluate at .41
with the upper quartic cosine and lower cubic sine. The
result is strictly below \(1/2\). The degree-five upper
sine at .41 is less than .4.

There is a useful stronger denominator bound:
\[
                              U+s>1.3.
\tag{17}
\]
To prove it without partitioning B, differentiate:
\[
 (U+s)_B=\frac{B-c(U+s)}{ZU}
        =-\frac{s(1/2+c)}{ZU}<0.
\]
Its minimum on \(B\le.96\) is therefore at \(B=.96\).
At that single endpoint, positive squaring gives
\(1.73<Z<1.731\), hence \(U>1.09\).
Also
\[
 .73\left(1-\frac{.22^2}{2}\right)
       -.96\left(.22-\frac{.22^3}{6}+\frac{.22^5}{120}\right)
                                      >\frac12.
\]
Thus z>.22 and \(s>.21\), proving (17).

Apply (16)--(17) to (15). Even if its first numerator is
negative, the following positive upper bound is valid:
\[
 \begin{split}
 \beta_B
 &<\frac{1-.709\cdot.98/1.85}{1.3}
                         +\frac{.96\cdot.4}{.98\cdot1.3^2}\\
 &=\frac34-\frac{5793909}{153198500}<\frac34.
 \end{split}
\tag{18}
\]
Since B=2-Y, this is exactly
\[
                     \frac{d}{dY}\beta(2-Y)>-\frac34.
\tag{19}
\]

## 5. One rational endpoint starts the strict rate gap

It remains to compare the rates at \(Y_0=26/25\),
\(B_0=24/25\), uniformly in (1) and \(0\le r\le1/25\).
Positive squaring gives
\[
 1.6833<R<1.6835,\qquad D>.6833,\qquad X<1.8571,
 \qquad k>\frac{6833}{18571}=:k_0.
\tag{20}
\]
The expression \(t(1-k)/(1-kt)\) increases with t and
decreases with k on this range. With \(t_0=.0401\),
\[
 \begin{split}
 \mathcal A(Y_0)
 &<\frac{1.6835}{1.04}
       \left(1.8571-1+\frac{t_0(1-k_0)}{1-k_0t_0}\right)\\
 &=\frac{143}{100}
       -\frac{271298002337}{292751947200000}
 <\frac{143}{100}.
 \end{split}
\tag{21}
\]

For the opposite endpoint, \(1.73<Z<1.7304\).
The quartic upper cosine and cubic lower sine give
\[
 .7304\cos(.2231)-.96\sin(.2231)<\frac12,
\]
so z<.2231. The degree-five upper sine and degree-six lower
cosine at .2231 then give \(\tan z<.227\).
The expression in (12) increases with Z and decreases with
\(\tan z\) on these bounds. Hence
\[
 \begin{split}
 \beta(B_0)
 &>1.73\,\frac{.96+.73\cdot.227}{.96+1.73\cdot.227}\\
 &=\frac{1439}{1000}+\frac{92861}{135271000}
 >\frac{1439}{1000}.
 \end{split}
\tag{22}
\]
For the asserted Z monotonicity, its derivative is
\(1-B_0\tau/(B_0+Z\tau)^2>0\), since
\(B_0^2>B_0\tau\) for \(0\le\tau\le.227\).

Equations (21)--(22) start a gap larger than \(9/1000\)
at \(Y_0\). The two whole-interval derivative bounds
(10), (19) give
\[
 \frac{d}{dY}\{\beta(2-Y)-\mathcal A(Y)\}>
                              \frac9{10}-\frac34=\frac3{20}.
\]
Integrating proves (3) for every Y in (2), using (14).
At a G tangent-floor transition, use the one-sided rate
from (5) or the zero rate as appropriate; both satisfy the
same positive comparison.

The proof uses one intrinsic tangent endpoint, explicit
derivatives on the whole remaining interval, and rational
Taylor bounds. No sampled angle or tangent grid, numerical
acceptance premise, Lean run or CI result is used.

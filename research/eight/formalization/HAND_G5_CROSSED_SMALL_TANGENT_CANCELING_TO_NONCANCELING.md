# The smaller crossed canceling tangent also reduces to HG0

## 1. Scope and conclusion

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
Retain normal signs at H,G,A,B,T,D, either E sign, sorted
own-frame magnitudes, true core avoidance, corner circles at
most \(q\le Q\), and a real frame interval of length at most
\(7/10\). The retained witnesses are
\[
 HG=2,\quad GA=0,\quad BT=2,\quad TD\in\{0,2\},
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\]
Assume
\[
 \theta_A=\theta_B=\rho,\quad b_A+b_B=1,\quad
 \theta_T\le\rho\le\theta_G,\quad \theta_H<\rho,
 \qquad \frac{67}{200}\le b_A\le\frac12.
\tag{2}
\]

**Reduction.** There is a descendant at the same q with
\(\theta_G'=\rho>\theta_T\) and an actual HG0 witness with
strict slack. Only G is replaced: all H,A,B,T,D,E coordinates
and frames, including any separate strict A/B circle losses,
are unchanged. The original full HG error also satisfies
\[
                         \theta_G-\theta_H<\frac25.
\tag{3}
\]
The resulting HG0 state satisfies the stronger captures
\[
             b_A>\frac{47}{98},\qquad
             0<\rho-\theta_H<\frac1{100},\qquad b_H>\frac34.
\tag{4}
\]
For \(q\ge19577/5000\), it therefore joins the
[common-frame clamp](HAND_G5_CROSSED_COMMON_FRAME_CLAMP.md).
That clamp makes the common G/A/B frame equal to H and
creates separate strict losses at both middle circles.

This is the small-tangent companion of the
[large-tangent canceling reduction](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md).
The endpoint reflection in Section 2 of that note justifies
either E sign throughout the present argument.

## 2. A bound for the two middle angular envelopes

For a transverse corner \(Y\in[167/200,233/200]\), put
\[
 R(Y)=\sqrt{Q-Y^2},\quad P(Y)=R(Y)-1,
\]
\[
 V_Y(v)=P(Y)\cos v-Y\sin v,\qquad
 U_Y(v)=P(Y)\sin v+Y\cos v.
\]
Let \(z_Y\) be the first nonnegative solution of
\(V_Y(z_Y)=1/2\), and define
\[
                M(Y)=\max_{0\le v\le z_Y}\{V_Y(v)+pv\}.
\tag{5}
\]
Every P on this interval is greater than \(1/2\), so these
are nonempty hard-feasible intervals. The original GA and BT
contacts, after increasing only their primary bounds to the
Q-circle, imply
\[
 b_G+\frac12\le V_Y(t),\qquad
 b_T+\frac12\le V_{2-Y}(u),
\tag{6}
\]
where
\[
 Y=b_A+\frac12\in[167/200,1],\quad
 t=\theta_G-\rho\ge0,\quad u=\rho-\theta_T\ge0.
\]
In particular \(t\le z_Y\), \(u\le z_{2-Y}\).
We prove the whole-interval estimate
\[
 \boxed{\quad M(Y)+M(2-Y)<1+S_0+\frac3{1000}
                   \qquad(167/200\le Y\le1).\quad}
\tag{7}
\]
Its two intervals below are determined by whether the
opposite optimizer is the zero angle; they are not an
angular subdivision.

### 2.1 The optimizer and its derivatives

Since \(U_Y'=V_Y\ge1/2\), the derivative
\(p-U_Y(v)\) of the expression in (5) strictly decreases
on its whole hard-feasible interval. If \(Y\ge p\),
its maximum is therefore at zero and
\[
                             M(Y)=R(Y)-1.
\tag{8}
\]
For \(167/200\le Y<p\), the maximum is interior. At its
unique angle v,
\[
 U_Y(v)=p,\qquad
 V:=V_Y(v)=\sqrt{Q+1-2R-p^2}>\frac12.
\tag{9}
\]
The last bound follows already from \(R<1.794\) and
\(Q+1-2(1.794)-p^2>.535^2\). It also verifies that this
optimizer occurs before the hard endpoint.

Write \(c=\cos v,s=\sin v\). Differentiation at this
interior maximum gives
\[
 M'(Y)=-\frac YR c-s,
\]
\[
 \begin{split}
 M''(Y)
 &=-\frac{Qc}{R^3}+\frac{(V+c)^2}{R^2V}\\
 &=\frac{c(V+c)}{R^2V}-\frac{Y(p+s)}{R^3}.
 \end{split}
\tag{10}
\]
For example, the derivative of \(V_Y\) with respect to Y
is \(-Yc/R-s\), and its mixed derivative is
\(Ys/R-c=-(V+c)/R\); differentiating the first-order
condition proves the first expression in (10).
The second uses \(p+s=Rs+Yc\).

### 2.2 One concave scalar when the opposite optimum is zero

Put \(Y_c=2-p=48/49\). On
\(167/200\le Y\le Y_c\), the opposite term in (7) is
(8). Thus consider
\[
                   N(Y)=M(Y)+\sqrt{Q-(2-Y)^2}-1.
\tag{11}
\]
Positive squaring in this whole interval gives
\[
 1.719<R<1.794,\quad .535<V<.661,\quad
 R_B:=\sqrt{Q-(2-Y)^2}<1.696.
\tag{12}
\]
All terminating decimals here and below are exact rationals.
For \(C=Q+1-p^2\), the function
\[
             A(R)=\frac{1+1/\sqrt{C-2R}}{R^2}
\]
increases on the range (12): the sign of its derivative is
that of \(R-2V^2(V+1)\), which is positive already from
\(R>1.719\), \(V<.661\). Therefore (10) gives
\[
 M''(Y)
 <\frac{1+1/.535}{1.794^2}
       -\frac{(.835)p}{1.794^3}<\frac34.
\tag{13}
\]
The reserve in the final comparison is
\(92212380017/15136211173356>0\).
Also
\[
 \frac Q{R_B^3}>\frac Q{1.696^3}>\frac45,
 \qquad
 \frac Q{1.696^3}-\frac45=\frac{503077}{190562560}>0.
\]
Consequently
\[
                             N''(Y)<-\frac1{20}.
\tag{14}
\]

One rational comparison point suffices. At \(Y_*=.86\),
positive squaring and alternating sine/cosine polynomials
provide
\[
 1.78213<R<1.78214,\qquad
 1.6174<R_B<1.61741,
 \qquad .238<v<.239.
\tag{15}
\]
The angle interval follows by inserting .238 and .239 in
\(U_Y(v)-p\), which is strictly increasing. Formula (10)
then gives
\[
                              |N'(Y_*)|<.001.
\tag{16}
\]
For explicit rational bounds on (16), an upper and a lower
bound respectively are
\[
 \frac{1.14}{1.6174}
  -\frac{.86}{1.78214}\left(1-\frac{.239^2}{2}\right)
  -\left(.238-\frac{.238^3}{6}\right)<.001,
\]
\[
 \frac{1.14}{1.61741}
  -\frac{.86}{1.78213}
      \left(1-\frac{.238^2}{2}+\frac{.238^4}{24}\right)
  -\left(.239-\frac{.239^3}{6}+\frac{.239^5}{120}\right)>-.001.
\tag{17}
\]

At \(v_*=.238\), the angular derivative lies between zero
and .0003. The angular second derivative is \(-V_Y\le-1/2\),
so completing a square bounds the maximum's increase over
its value at \(v_*\) by \(.0003^2\). Using the quartic
upper cosine and cubic lower sine gives
\[
 \begin{split}
 N(Y_*)&<.78214
      \left(1-\frac{.238^2}{2}+\frac{.238^4}{24}\right)
      -.86\left(.238-\frac{.238^3}{6}\right)\\
 &\qquad+p(.238)+.61741+.0003^2<1.4177.
 \end{split}
\tag{18}
\]
The reserve in the final comparison is
\(15339946220057/175000000000000000>0\).

Now (14), (16), and another completed square give
\[
 N(Y)<1.4177+10(.001)^2=1.41771.
\tag{19}
\]
Because \(\sqrt{Q-1}>1.7075\), one has
\(1+S_0>1.415\). Thus (19) proves (7) on this whole
interval, with the explicit additional reserve
\[
                  .003-.0027-10(.001)^2=\frac{29}{100000}>0.
\tag{20}
\]

### 2.3 The short interval with two free optimizers

When \(Y_c\le Y\le1\), both arguments in (7) belong
to \([48/49,p]\). On this interval,
\[
 1.695<R<1.72,
 \qquad .65<V<.7,
 \qquad 0\le v<.07,
 \qquad \cos v>.997.
\tag{21}
\]
The two radical bounds follow from (9). To verify the
angle bound, the lower P bound is .695. At .07,
\[
 .695\left(1-\frac{.07^2}{2}\right)-p(.07)>.5,
\]
so the angle is still hard-feasible, while
\[
 \frac{48}{49}\left(1-\frac{.07^2}{2}\right)
  +.695\left(.07-\frac{.07^3}{6}\right)>p.
\]
Therefore its unique optimizer occurs earlier.
The first expression in (10) now gives
\[
 M''(Y)>
 \frac{(.65+.997)^2}{1.72^2(.7)}-\frac Q{1.695^3}
 >\frac12.
\tag{22}
\]
The final reserve is
\(156538459337/26892598854240>0\).
Thus \(M(Y)+M(2-Y)\) is convex on this interval, and its
maximum is at an endpoint. At \(Y=Y_c\), the preceding
interval already gives (7); the optimizer at p equals zero
continuously. At \(Y=1\), the angular function starts with
derivative \(p-1=1/49\) and second derivative at most
\(-1/2\). Hence
\[
 M(1)\le\sqrt{Q-1}-1+\frac1{2401}.
\]
Consequently
\[
 2M(1)\le1+S_0+\frac2{2401}<1+S_0+\frac3{1000}.
\tag{23}
\]
This completes (7). The proof used the two intrinsic
optimizer branches, derivative signs on each entire
interval, and one rational comparison point.

## 3. The full HG error is less than two fifths

Translate the common frame to zero, and write
\[
 \theta_G=t\ge0,\qquad\theta_H=-r<0,\qquad
 \theta_T=-u\le0,
 \qquad h=t+r.
\]
The signed-E endpoint estimate and the actual TD zero charge,
as used in the large-tangent canceling note, give
\[
                     b_H-b_T+p(r-u)<1-S_0.
\tag{24}
\]
Keep the nonnegative extra term in the
[all-sign HG zero charge](HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md):
\[
 b_H+b_G\ge1-ph+\gamma(h),\qquad
 \gamma(h)=\frac{\sin h+\cos h-1}{98}.
\tag{25}
\]
This zero-charge theorem uses only the true core, the actual
circle bounds, and the retained transverse witness, so it
applies to the present necessary system.

From (6), (24), and (25),
\[
 \begin{split}
 1-S_0
 &>b_H+pr-(b_T+pu)\\
 &\ge2-\{V_Y(t)+pt\}-\{V_{2-Y}(u)+pu\}+\gamma(h).
 \end{split}
\]
Therefore
\[
             M(Y)+M(2-Y)>1+S_0+\gamma(h).
\tag{26}
\]
If \(h\ge2/5\), then \(h\le7/10<\pi/4\) and gamma
is increasing, whereas the cubic lower sine and quadratic
lower cosine give
\[
 \gamma(2/5)-\frac3{1000}
 >\frac{(2/5)-(2/5)^3/6-(2/5)^2/2}{98}
                         -\frac3{1000}
 =\frac{23}{147000}>0.
\tag{27}
\]
This contradicts (7) and (26), proving (3).

## 4. Lower G to the common frame using the entire HG2 composite

Return to the actual A, and put
\[
 P=a_A-\frac12<.794,\qquad Y=b_A+\frac12\ge.835,
\]
\[
 V(t)=P\cos t-Y\sin t,\qquad U(t)=P\sin t+Y\cos t.
\]
The original GA0 inequality is \(V(t)\ge b_G+1/2\).
In particular \(a_A\ge1\). For the unchanged actual H put
\[
 S(h)=(a_H-\tfrac12)\sin h+(b_H-\tfrac12)\cos h,
\]
\[
 U_H(h)=(a_H-\tfrac12)\cos h-(b_H-\tfrac12)\sin h.
\]
Adding HG2 and GA0 eliminates the G tangent and gives
\[
                             V(t)+S(t+r)\ge1.
\tag{28}
\]
On its feasible portion, \(S\ge1-V\ge1-P>.206\).
Set \(m=\cos h+\sin h\), \(n=\cos h-\sin h>0\).
The actual H circle gives
\[
                 (S+m)^2+(U_H+n)^2\le Q,
\]
with \(U_H+n>0\) by sorting. Consequently
\[
 U_H<\sqrt{Q-(m+.206)^2}-\sqrt{2-m^2}.
\tag{29}
\]
This right side increases with m. Its derivative sign,
after positive squaring, is exactly
\(Q/2>(1+.206/m)^2\); it follows at \(m=1\), with
reserve \(125841/250000>0\).
By (3), it suffices to evaluate the upper endpoint \(h=.4\).
There
\[
 m+.206>1.515,\qquad n>.52,
 \qquad \sqrt{Q-1.515^2}<1.273.
\]
The final squared reserve is \(77/500000>0\).
Thus throughout the proposed decreasing-t path,
\[
                             U_H<.753.
\tag{30}
\]
On the other hand \(V\ge1/2\), \(U'=V\), and hence
\(U(t)\ge U(0)=Y\ge.835\). Wherever (28) holds,
\[
 \frac d{dt}\{V(t)+S(t+r)\}
                       =-U(t)+U_H(t+r)<-\frac{41}{500}.
\tag{31}
\]
A first-boundary argument now preserves (28) as t decreases
all the way to zero. The condition \(V\ge1/2\) persists
because V increases as t decreases, and (3) persists because
h decreases.

At each point choose
\[
 b_G'=\max\{0,\tfrac12-S(t+r)\},\qquad a_G'=\frac7{12}.
\tag{32}
\]
Then HG2 and GA0 hold, and
\[
               0\le b_G'\le V-\frac12<.294.
\]
This is a sorted point of the true flat core. Its corner
circle satisfies
\[
 (13/12)^2+.794^2<\frac{29}{10}
 <(3/2)^2+.835^2\le q,
\tag{33}
\]
where the last inequality uses the unchanged A.
The path changes only G and stays inside the original real
frame interval. It ends at \(\theta_G'=\rho\).
If \(u=0\), this descendant has \(G=T\), contradicting
the signed-E global intermediate-order theorem. Thus
\(\rho>\theta_T\).

## 5. Select a strict actual HG0 witness at the endpoint

Write \(g=b_G'\) after (32). At this endpoint \(r<.4\),
\(g<.294\), and HG2 says
\[
       g+(a_H-\tfrac12)\sin r+(b_H-\tfrac12)\cos r\ge\frac12.
\tag{34}
\]
If \(b_H\le g\), use \(a_H-1/2<.915\) and
\(\cos r>1-.4^2/2\). The left side of (34), minus its
right side, would be less than
\[
 -.206+.915(.4)-.206(1-.4^2/2)
                          =-\frac{369}{12500}<0.
\tag{35}
\]
Therefore \(b_H>g\).

Keep g and its aligned frame, and raise only G's primary to
\[
                    a_G''=\sqrt{q-(g+1/2)^2}-\frac12.
\tag{36}
\]
Because \(b_H>g\), this gives \(a_G''>a_H\).
Also \(g<.294<.335\le b_A\), so \(a_G''>a_A\ge1\).
Thus G remains sorted and satisfies the true core.
Neither HG2 nor aligned GA0 depends on this primary.
The two exact HG projections satisfy
\[
 P_{HG0}-P_{HG2}
       =(a_G''-a_H)\sin r+(b_H-g)(1-\cos r)>0.
\tag{37}
\]
This supplies an actual HG0 witness with strict slack while
all six other states remain unchanged.

Apply the
[small-tangent HG0 theorem](HAND_G5_CROSSED_SMALL_TANGENT_NONCANCELING_GA_ALIGNMENT.md)
to this descendant. It gives \(b_A>47/98\), \(r<.01\).
At its already aligned GA contact, write
\(Y=b_A+1/2>48/49\), \(P=\sqrt{Q-Y^2}-1<.72\).
The same-circle HG0 bound then gives
\[
 b_H>\frac12+.28(1-.01^2/2)-.915(.01)>\frac34,
\tag{38}
\]
which completes (4). The common-frame clamp now applies
whenever its stated lower q bound is retained.

Every step before that final clamp keeps A and B exactly
fixed; any inherited separate middle-circle losses persist.
The clamp creates strict losses at both whenever the crossed
distance is positive, as it is here. This is therefore
compatible with original-anchor equality bookkeeping.

No numerical minimum, state or angle mesh, compiled theorem,
or CI result is a premise. The new middle comparison is
proved by analytic curvature on its two intrinsic optimizer
branches, one rational comparison point, and ordinary Taylor
and positive-squaring arithmetic.

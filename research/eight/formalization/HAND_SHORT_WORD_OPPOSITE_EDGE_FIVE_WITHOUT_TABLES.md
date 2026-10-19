# The opposite-sign outer edge of 0010111, without angle tables

## The complete contact-family theorem

All decimals in this note are exact rationals. Put
\[
 Q=9789/2500,\qquad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\qquad
 d=\sqrt{Q/2}-\tfrac12.
\]
An outer state satisfies
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\qquad 0\le b\le a,\qquad
 b\le d.
\tag{1}
\]
Consider the outer/outer role-5 edge of the word \(0010111\), with source
sign negative and target sign positive. Its cost is
\[
 C=\phi+.50283-.20967a-.83048b-.21826A-.83472B.
\tag{2}
\]
Suppose one of the four retained original separating axes separates the
two squares, and \(|\phi-\pi/2|\le.7\). Then
\[
 \boxed{C>\frac{42643}{47500}=.897747368\ldots>.89765.}
\tag{3}
\]
Thus this theorem removes the entire opposite-sign role-5 outer contact
family, including all four original axes and both sides of alignment.
It includes the two lower-side secondary cases that previously required
five angle intervals each. No interval cover or coefficient-status table
is used below.

For orientation, the full short-word assembly uses the edge constants
\[
 \gamma_2=.8975,\qquad \gamma_i=.89765\quad(i\ne2),
\]
whose sum is \(31417/5000>710/113>2\pi\). Consequently (3) has the
correct reserve for that assembly.

## 1. Two coefficient tuples and two separator formulas

Reflecting and reversing an original target-owned axis gives the same
cost with the source and target labels interchanged as follows:
\[
\begin{aligned}
\mathcal A &: (p,q,P,t)=(-.20967,.83048,.21826,.83472),\\
\mathcal B &: (p,q,P,t)=(-.21826,.83472,.20967,.83048).
\end{aligned}
\tag{4}
\]
In either normalization put \(c=.50283\), and write
\[
 C=\phi+c+pa-qb-PA-tB,\qquad
 \phi=\pi/2+r u,\quad 0\le u\le.7,\quad r\in\{-1,1\}.
\tag{5}
\]
With \(s=\sin u,\ k=\cos u,\ W=(1+k+s)/2\), the normalized separators are
\[
 -b+Ak+rBs\ge W
 \quad\hbox{or}\quad
 a+rAs-Bk\ge W.
\tag{6}
\]
Tuple \(\mathcal A\) covers original axes 1 and 4, and tuple
\(\mathcal B\) covers original axes 3 and 2, respectively. This
normalization is the exact reflection/reversal identity for the original
axes; it introduces no freedom to change a square's sign or role label.

We shall use the elementary root bounds
\[
\begin{aligned}
1.914575671&<\sqrt{Q-\tfrac14}<1.914575672,\\
1.290581264&<\sqrt{Q-\tfrac94}<1.290581265,\\
\sqrt Q&<1.978788.
\end{aligned}
\tag{7}
\]
They follow by squaring. The rational bounds for \(\pi/2\) used below
follow, for example, from the alternating series in
\(\pi/4=4\arctan(1/5)-\arctan(1/239)\).

## 2. Lower-side secondary separators: contact removes one state

Take the first separator in (6) with \(r=-1\). Since
\[
 \frac{d}{db}\{pa(b)-qb\}
 =(-p)\frac{b+\tfrac12}{a+\tfrac12}-q<0,
\]
we may increase \(b\) until its separator is an equality. This never
reaches the diagonal endpoint: its largest possible value is at most
\(a_0k-W\le a_0-1<d\). If \(a_0k<W\), the separator is infeasible.

Set
\[
 v=b+\tfrac12,\quad z=v+k,\quad
 T=\sqrt{Q-z^2},\quad
 U=kz+sT,\quad V=-sz+kT,
\tag{8}
\]
so \(A=U-\tfrac12,\ B=V-\tfrac12\). Formula (8) is the unique
first-quadrant circle point satisfying the contact equation
\(Uk-Vs=z\). Put
\[
 D=Pk-ts,\qquad E=Ps+tk,\qquad
 c'=c+\frac{-p+q+P+t}{2}.
\]
The contact cost is exactly
\[
 C(v,u)=\frac\pi2-u+c'
       +p\sqrt{Q-v^2}-(q+D)v-Dk
       -E\sqrt{Q-(v+k)^2}.
\tag{9}
\]
The feasible values have \(v\ge\tfrac12\). Their angle range is
strictly smaller than \(.571\). Indeed feasibility implies
\[
 (2a_0-1)\cos u-\sin u\ge1.
\tag{10}
\]
The left side is strictly decreasing while \(0\le u\le.7\).
At \(x=\tan(u/2)=h:=733/2500\), substitution of
\(\cos u=(1-x^2)/(1+x^2)\), \(\sin u=2x/(1+x^2)\) and the upper bound
in (7) makes it less than 1. Hence every feasible angle satisfies
\[
 0\le x<h=.2932,\qquad u<2h<.587,\qquad u<.571.
\tag{11}
\]
For the last inequality one may substitute \(u=.571\) directly in
(10), using the alternating sine and cosine bounds. These are single
endpoint comparisons of a strictly decreasing expression.

On this range \(k>.84\), and the concave function \(Ps+tk\) exceeds
\(.81\): at zero it is \(t\), and at \(.571\) it exceeds
\(.54P+.84t>.81\). Differentiating (9) twice gives
\[
 C_{vv}
 =\frac{(-p)Q}{(Q-v^2)^{3/2}}
  +\frac{EQ}{(Q-(v+k)^2)^{3/2}}
 >
 \frac{.20967Q}{1.915^3}
 +\frac{.81Q}{1.457^3}
 >1.14.
\tag{12}
\]
Here \(v\ge\tfrac12\) and \(v+k>1.34\). The final rational comparison
is
\[
 \frac{24812857579275945036}{21721258807592973875}>1.14.
\]

Let \(C_0(u)=C(\tfrac12,u)\), and
\(H(u)=C_v(\tfrac12,u)\). At \(v=\tfrac12\), write
\[
 z=\tfrac12+k,\quad T=\sqrt{Q-z^2},\quad
 \kappa=\frac{-p}{2\sqrt{Q-\tfrac14}}-q.
\]
The first derivative has the useful form
\[
 H(u)=\kappa-D+\frac{Ez}{T}
     =\kappa+t\frac UT-P\frac VT.
\tag{13}
\]
We have \(V/T=k-sz/T\le1\), and
\[
 \frac UT\ge\frac{3}{2T_0},\qquad
 T_0=\sqrt{Q-\tfrac94}.
\tag{14}
\]
Here is a whole-angle proof of (14). Put
\(r_0=3/(2T_0)>1.16\), and
\[
 A_k=\frac{k+2}{k+1},\qquad
 \frac32\le A_k<1.57,\qquad T^2=T_0^2+A_ks^2.
\]
The asserted inequality is \(kz\ge(r_0-s)T\), with both sides
positive. Their squared difference is
\[
 s\{2r_0T^2-Qs(1+A_k/T_0^2)\}.
\tag{15}
\]
For \(s\le.65\), the expression in braces is bounded below by
\[
 2(1.16)(T_0^2+1.5s^2)
      -Qs(1+1.57/T_0^2).
\]
This quadratic is decreasing on \([0,.65]\), and at \(.65\) it is
\(135432269/347000000>0\). This proves (14), including its endpoint.

Equations (13) and (14) now imply
\[
 H(u)\ge
 \frac{-p}{2\sqrt{Q-\tfrac14}}-q+
 \frac{3t}{2T_0}-P>-.024
\tag{16}
\]
for each tuple (4), by (7). No derivative enclosure in a moving
two-variable box is needed.

The exact scalar argument in Section 5 proves
\[
 C_0(u)>.898
\tag{17}
\]
on the entire feasible angle interval. Taylor's formula with (12) and
(16), or an elementary completed square, consequently gives
\[
\begin{aligned}
 C(v,u)
 &>C_0(u)-.024(v-\tfrac12)+\frac{1.14}{2}(v-\tfrac12)^2\\
 &>.898-\frac{.024^2}{2(1.14)}
   =\frac{42643}{47500}.
\end{aligned}
\tag{18}
\]

## 3. Lower-side primary separators: an increasing axial reference

Take the second separator in (6), again with \(r=-1\). The source cost
\(pa-qb(a)\) has derivative \(p+q(a+\tfrac12)/(b+\tfrac12)>0\).
We may therefore decrease \(a\) to the contact equation
\[
 a=W+As+Bk.
\]
This contact is above the source diagonal, since \(a\ge W\ge1>d\).
Write
\[
 y=B+\tfrac12,\quad X=\sqrt{Q-y^2},\quad
 z=sX+ky,\quad K=1+z,\quad
 V=\sqrt{Q-K^2},\quad T=kX-sy.
\tag{19}
\]
Then \(A=X-\tfrac12,\ a=K-\tfrac12,\ b=V-\tfrac12\), and the contact
cost, up to its fixed translated constant, is
\[
 -u+pK-qV-PX-ty.
\tag{20}
\]
Feasibility implies
\[
 a_0(1-\sin u)\ge W,
\]
whose left side minus right side is strictly decreasing. At \(.226\)
it is negative by the alternating sine and cosine bounds and (7).
Thus \(u<.226\), so \(k>.974,\ s<.225\). Moreover
\[
 \tfrac12\le z<.915,\quad T^2=Q-z^2>1.75^2,\quad V<1.291.
\]

Differentiating (20) twice with respect to \(y\), using
\(K_y=T/X\), gives the exact identity
\[
 C_{yy}=\frac{Q}{X^3}
 \left[
 P-ps+
 q\frac{kT^3+s(3z^2+3z+1-Q)}{V^3}
 \right].
\tag{21}
\]
For example the \(q\)-numerator follows from
\[
 T^2X-sK V^2
 =kT^3+s(3z^2+3z+1-Q).
\]
The bounds just obtained imply
\[
 C_{yy}>
 \frac{Q}{1.915^3}
 \left[
 .20967+
 \frac{.83048\{.974(1.75)^3-.225(Q-3.25)\}}{1.291^3}
 \right]>1.20>1.14.
\tag{22}
\]
The first displayed rational number equals
\(18254146202344978692/15110716642087209625\).

At the target axial reference \(y=\tfrac12\), put
\[
 X_0=\sqrt{Q-\tfrac14},\quad
 K=1+X_0s+\tfrac12k,\quad T=X_0k-\tfrac12s.
\]
The reference cost \(L_0(u)=C(\tfrac12,u)\) satisfies
\[
 L_0'(u)=-1+(p+qK/V)T,\qquad
 C_y(\tfrac12,u)=(p+qK/V)T/X_0+P/(2X_0)-t.
\tag{23}
\]
The expression \((p+qK/V)T\) is strictly increasing. Indeed its
derivative is
\[
 \frac{q}{V^3}\{QT^2-K(K-1)V^2\}-p(K-1)>0,
\tag{24}
\]
since \(K\in[1.5,1.915]\),
\[
 QT^2-K(K-1)V^2
 >Q\{Q-.915^2\}-(1.915)(.915)(Q-2.25)>0.
\]
At \(u=0\), (7) gives \(L_0'(0)>.43\) and
\(C_y(\tfrac12,0)>-.024\), for each tuple.
The two reference values are the same two numbers as
\(C_0(0)\) in Section 2, in reversed order. In particular both exceed
\(.8986\). Consequently \(L_0(u)>.8986\) and
\(C_y(\tfrac12,u)>-.024\) throughout the feasible interval.
Completing the square with (22) gives a bound stronger than (18).

## 4. Upper-side separators

### 4.1 Secondary axes

Take \(r=1\) and the first separator in (6). In translated circle
coordinates
\[
 z_s=(a+\tfrac12,b+\tfrac12),\quad
 z_t=(A+\tfrac12,B+\tfrac12),
\]
the separator is
\[
 d_s\cdot z_s+d_t\cdot z_t\ge k+s,\qquad
 d_s=(0,-1),\quad d_t=(k,s).
\]
The cost coefficient vectors are \(v_s=(p,-q)\) and \(v_t=(-P,-t)\).
For any \(\mu,\nu>0\) and \(\lambda\ge0\), completing the two
circle squares gives
\[
\begin{split}
 C\ge{}&\frac\pi2+u+c+\frac{-p+q+P+t}{2}
       -Q(\mu+\nu)
       -\frac{|v_s-\lambda d_s|^2}{4\mu}
       -\frac{|v_t-\lambda d_t|^2}{4\nu}
       +\lambda(k+s).
\end{split}
\tag{25}
\]
This holds for the original circles, since it is simply the sum of two
nonnegative Euclidean squares and the nonnegative separator slack.

Choose
\[
 \mu=11/200,\quad \nu=41/125,\quad
 A=\frac1{4\mu}+\frac1{4\nu}=\frac{9575}{1804},
\]
and define
\[
\begin{aligned}
 K_0&=c+\frac{-p+q+P+t}{2}-Q(\mu+\nu)
      -\frac{p^2+q^2}{4\mu}-\frac{P^2+t^2}{4\nu},\\
 B(u)&=\frac q{2\mu}+
       \left(1-\frac P{2\nu}\right)k+
       \left(1-\frac t{2\nu}\right)s.
\end{aligned}
\]
Both coefficient tuples give \(B(u)>0\). Optimizing the quadratic
right side of (25) at \(\lambda=B/(2A)\) proves
\[
 C\ge F(u):=\frac\pi2+u+K_0+\frac{B(u)^2}{4A}.
\tag{26}
\]
Put \(x=\tan(u/2)\). Since
\[
 x\le\tan(.35)
 \le\frac{.35}{1-.35^2/2}
 =\frac{280}{751}<\frac38,
\]
we may use \(0\le x<3/8\). Direct expansion of the quartic
\((1+x^2)^2F'(u)\), with either exact tuple (4), gives the common lower
bound
\[
 .789-1.047x+2.102x^2-.899x^3+1.173x^4>.34.
\tag{27}
\]
The last inequality already follows on dropping the positive quadratic
and quartic terms and setting \(x=3/8\) in the negative terms.
For checking the expansion, if
\(B=b_0+b_ck+b_ss\), its exact quartic numerator is
\[
 (1+x^2)^2+
 \frac{\{b_0(1+x^2)+b_c(1-x^2)+2b_sx\}
       \{-2b_cx+b_s(1-x^2)\}}{2A}.
\]
Thus \(F\) is increasing on its whole angle range.

Using only \(\pi/2>1.570795\), its two initial values exceed \(.8981\):
the exact positive differences are
\[
 \frac{20143580253}{34546600000000},\qquad
 \frac{2202776717}{34546600000000}.
\tag{28}
\]
This completes both upper-side secondary cases.

### 4.2 Primary axes

Take the second separator in (6), with \(r=1\). Use the fixed
nonnegative multiplier \(\lambda=.776\) for tuple \(\mathcal A\) and
\(\lambda=.774\) for tuple \(\mathcal B\). The exact full-circle support
bound for the source is
\[
 S=\frac{\lambda-p+q}{2}
        -\sqrt Q\sqrt{(\lambda-p)^2+q^2}.
\]
The corresponding target support bound gives
\[
 C\ge G(u):=\frac\pi2+u+c+S+\frac{\lambda+P+t}{2}
  +\lambda s-\sqrt Q\sqrt{P^2+t^2+\lambda^2+
                         2\lambda(Ps-tk)}.
\tag{29}
\]
If \(N\) is the final radical without its factor \(\sqrt Q\), then
\[
 |Pk+ts|\le N,
\]
because \((Pk+ts)\) is the dot product of the unit vector \((k,s)\)
with \((P+\lambda s,t-\lambda k)\). Therefore
\[
 G'(u)\ge1+\lambda k-\sqrt Q\,\lambda
 >1-.776(1.978788-.76)>0.
\tag{30}
\]
This proves monotonicity on the entire angle range.

At zero the two pairs of radicals
\[
 \left(\sqrt{(\lambda-p)^2+q^2},
       \sqrt{P^2+(t-\lambda)^2}\right)
\]
are bounded above respectively by
\((1.288892,.226021)\) and \((1.296664,.217144)\), by squaring.
Together with (7) and \(\pi/2>1.570795\), these give
\[
 G_{\mathcal A}(0)>
 \frac{224624583639}{250000000000}>.8984,\qquad
 G_{\mathcal B}(0)>
 \frac{14041951489}{15625000000}>.8986.
\tag{31}
\]
The four upper-side cases are therefore stronger than (3).

## 5. The two whole-angle axial inequalities

This section proves (17). It uses one algebraic factorization on the
entire feasible interval for each of the two fixed label tuples.
There is no subdivision of that interval.

Write \(x=\tan(u/2)\), \(D_x=1+x^2\),
\[
 k=\frac{1-x^2}{D_x},\qquad s=\frac{2x}{D_x},\qquad
 Z=\tfrac12+k,\qquad T^2=Q-Z^2,
\]
and \(D=Pk-ts,\ E=Ps+tk\), as before. Put
\[
 L=1.57079632679489+c+p(1.414575672)
                      +\frac{P+t}{2}-.898,
\]
and use the alternating arctangent majorant
\[
 A_5(x)=x-\frac{x^3}{3}+\frac{x^5}{5}
           -\frac{x^7}{7}+\frac{x^9}{9}\ge\arctan x.
\]
Define the polynomial
\[
 f=(L-2A_5-DZ)D_x^2.
\tag{32}
\]
The quantity before \(D_x^2\) is positive: \(L>1.38\),
\(2A_5\le2x\le.5864\), and \(DZ\le1.5P<.328\).
It is therefore legitimate to prove
\[
 {\cal P}(x):=f(x)^2-E^2T^2D_x^4>0.
\tag{33}
\]
Indeed (33) implies \(L-2A_5-DZ>ET\), and hence \(C_0(u)>.898\).

For an explicit and short arithmetic description, (32) is the sparse
polynomial
\[
\begin{split}
 f={}&(L-\tfrac32P)+(-2+3t)x+(2L+2P)x^2
       +(-\tfrac{10}{3}-t)x^3+(L-\tfrac12P)x^4\\
    &-\frac{16}{15}x^5+\frac{16}{105}x^7
       -\frac{16}{315}x^9-\frac{10}{63}x^{11}
       -\frac29x^{13}.
\end{split}
\tag{34}
\]
The subtracted term in (33) has degree 8, so every higher coefficient
comes solely from the square in (34).

### 5.1 A common bound for the high-degree tail

Writing \(p_j\) for the coefficient of \(x^j\) in \({\cal P}\), direct
multiplication of the sparse expression (34) gives, for either tuple,
\[
 |p_9|<1.8855,\quad |p_{10}|<.1838,\quad
 |p_{11}|<.2771,\quad |p_{12}|<.0618,\quad
 |p_j|<3\quad(13\le j\le26).
\tag{35}
\]
The last uniform comparison can also be seen without expanding the
high-degree terms. The absolute even coefficients of \(f\) are bounded
by \(1.08,3.25,1.30\). The absolute odd coefficients of degrees
1, 3, 5, 7 are bounded by \(.505,4.17,1.067,.153\), and those of degrees
9, 11, 13 by \(.051,.159,.223\).
For an odd output degree at least 13, the coefficient is bounded by
\(2(.223)(1.08+3.25+1.30)<3\). For an even output degree at least 14 it
is bounded by
\[
 .153^2+2(.223)(.505+4.17+1.067+.153)
                 +(.051+.159+.223)^2<3.
\]
For the first four comparisons in (35), if \(f_j\) denotes the
coefficient in (34), the exact expressions are
\[
\begin{aligned}
 p_9&=2(f_0f_9+f_2f_7+f_4f_5),\\
 p_{10}&=f_5^2+2f_1f_9+2f_3f_7,\\
 p_{11}&=2(f_0f_{11}+f_2f_9+f_4f_7),\\
 p_{12}&=2(f_1f_{11}+f_3f_9+f_5f_7).
\end{aligned}
\]
These formulas with the two exact tuples give (35) by rational
arithmetic. Consequently, on \(0\le x\le h=.2932\),
\[
 \left|\sum_{j=9}^{26}p_jx^j\right|
 \le x^9\left(1.8855+.1838h+.2771h^2+.0618h^3+
                         \frac{3h^4}{1-h}\right)\le2x^9.
\tag{36}
\]

### 5.2 The two low-degree factors

Using (34), keeping degrees at most 8, and absorbing (36), gives
\({\cal P}(x)>L_{\mathcal A}(x)\) for tuple \(\mathcal A\), where
\[
\begin{split}
L_{\mathcal A}={}&.00184988-.12669362x+2.75886083x^2
 -11.29910079x^3+16.64986399x^4\\
 &-23.93610952x^5+22.62536812x^6
 -14.73514417x^7+7.58x^8.
\end{split}
\tag{37}
\]
For tuple \(\mathcal B\), the corresponding lower polynomial is
\[
\begin{split}
L_{\mathcal B}={}&.00139186-.10601133x+2.65965496x^2
 -11.13153209x^3+16.40798861x^4\\
 &-23.67380575x^5+22.45323221x^6
 -14.60933832x^7+7.56x^8.
\end{split}
\tag{38}
\]
For example the two unrounded degree-8 coefficients exceed 8.17209
and 8.14825; subtraction of \(2h=.5864\) permits precisely the
conservative last coefficients displayed here. The other displayed
coefficients are obtained by substituting (4) into the explicit degree-8
part of (33), so (37) and (38) are fixed polynomial inequalities rather
than references to computed signs on a variable domain.

For either polynomial \(L_i\), define
\[
 R_i=L_i-.0001-3x^8,\qquad
 r_i=R_i(h),\qquad
 Q_i(x)=\frac{R_i(x)-R_i(h)}{h-x}.
\tag{39}
\]
These are polynomials, and exact substitution gives
\[
 r_{\mathcal A}>.0000352,\qquad r_{\mathcal B}>.0000303.
\]
The division in (39), followed by \(x\le h\) in its negative terms of
degrees 5 and 7, gives
\[
\begin{aligned}
 Q_{\mathcal A}(x)&>
 .0058479-.4121613x+8.0037503x^2-12.8805661x^3=:q_{\mathcal A}(x),\\
 Q_{\mathcal B}(x)&>
 .0043024-.3468926x+7.8880026x^2-12.691901x^3=:q_{\mathcal B}(x).
\end{aligned}
\tag{40}
\]
The positive degree-4 and degree-6 terms are simply dropped.

For completeness, the positivity of these two cubics is one completed
square on the whole interval. For a cubic \(q=a_0+a_1x+a_2x^2+a_3x^3\),
the exact Taylor identity at \(m\) is
\[
 q(x)=q(m)+q'(m)(x-m)
               +(x-m)^2\{a_2+a_3(x+2m)\}.
\tag{41}
\]
For \(q_{\mathcal A}\), use \(m=.027\). Direct substitution gives
\[
 q_{\mathcal A}(m)>.0003007,\quad
 |q'_{\mathcal A}(m)|<.0082,\quad
 a_2+a_3(h+2m)>3.53.
\]
For \(q_{\mathcal B}\), use \(m=.023\); the corresponding three bounds
are \(.0003422,\ .0042,\ 3.58\). Thus (41) is positive in both cases,
since
\[
 .0003007-\frac{.0082^2}{4(3.53)}>0,\qquad
 .0003422-\frac{.0042^2}{4(3.58)}>0.
\tag{42}
\]
Equations (39)--(42) prove
\[
 L_i(x)=.0001+3x^8+r_i+(h-x)Q_i(x)>0
 \qquad(0\le x\le h).
\tag{43}
\]
This proves (33), then (17), and completes the entire family theorem.

## Scope

This note proves a full, explicitly identified original-axis contact
family. It does not assert the exclusion of the whole word by itself.
The role labels remain the same labels on both incident edges at every
vertex. The remaining role and radial families must still supply their
stated pair inequalities before the cyclic telescoping argument can be
applied.

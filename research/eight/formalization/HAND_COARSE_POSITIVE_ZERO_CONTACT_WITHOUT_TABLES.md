# A whole-domain charged support for a positive zero edge

All decimals in this note are exact rationals. The theorem below is a
completed contact-family component of the coarse mismatch argument. It
does not assert the whole seven-cycle bound or any of its other sign or
quarter families.

The point of this component is that an explicit degree-five potential
supports both original transverse separators throughout a continuous
angle interval, including every radial state. The proof uses the whole
circle, one stationary-radius chord, and two polynomial remainders. No
state mesh, angle mesh, or sampled inequality is a premise.

## 1. The exact support theorem

Put
\[
 Q=\frac{9789}{2500},\qquad c=\frac{111}{112},\qquad
 d=\sqrt{Q/2}-\frac12,\qquad
 a_*(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12.
\tag{1}
\]
Define \(F\) by \(x=2b-1\) and
\[
 F(b)=-.01115329+.30696053x+.01518450x^2
       +.21272089x^3-.01877136x^4-.09850696x^5.
\tag{2}
\]
Equivalently,
\[
\begin{split}
 F(b)={}&-.43591461+.99460968b+.99785308b^2\\
        &-5.57810616b^3+7.58021504b^4-3.15222272b^5 .
\end{split}
\tag{3}
\]

**Theorem.** Let
\[
\begin{gathered}
 a\ge b\ge0,\quad A\ge B\ge0,\\
 (a+\tfrac12)^2+(b+\tfrac12)^2\le Q,\qquad
 (A+\tfrac12)^2+(B+\tfrac12)^2\le Q,\\
 0\le\delta\le.7,\qquad
 h(\delta)=\frac{\sin\delta+\cos\delta-1}{2}.
\end{gathered}
\tag{4}
\]
Suppose that at least one of
\[
 b+A\sin\delta+B\cos\delta\ge1+h(\delta),
\tag{5}
\]
\[
 a\sin\delta+b\cos\delta+B\ge1+h(\delta)
\tag{6}
\]
holds. Then
\[
 \boxed{\displaystyle
 \delta-\frac{\delta}{112}+F(b)-F(1-B)\ge0.}
\tag{7}
\]
The inequality is strict if \(\delta>0\). Equality holds exactly when
\(\delta=0\) and \(b+B=1\).

In the original signed coordinates, (5) and (6) are the two transverse
separators for a zero-quarter edge with source sign \(+\), target sign
\(-\), and positive frame increment. They are original zero-based axes
0 and 2, respectively; weak separators and ties are included. The
unconditional zero-primary cyclic exclusion, when applicable, supplies
this owner disjunction. That exclusion is not an assumption of the
scalar proof itself.

The reflected potential \(F(1-B)\) makes every aligned contact
\(b+B=1\) an exact equality. Thus the continuum of aligned contacts is
retained identically. If a cycle marker uses
\[
 L_{\rm source}=F(b),\qquad L_{\rm target}=F(1-B)-\gamma,
\]
then (7) is exactly
\[
 \delta-\delta/112+L_{\rm source}-L_{\rm target}\ge\gamma .
\tag{8}
\]
This is an interpretation of this one family, not a claim that the
other cycle markers have been proved.

## 2. The polynomial bounds used below

Write \(p=F'\). From (3),
\[
 p(y)=.99460968+1.99570616y-16.73431848y^2
                  +30.32086016y^3-15.7611136y^4,
\tag{9}
\]
and
\[
 p''(y)=-33.46863696+181.92516096y-189.1333632y^2 .
\tag{10}
\]
We establish all the needed bounds here by ordinary global calculus.
For convenience, if \(f''\ge\kappa>0\), we use
\[
 f(x)\ge f(x_0)-\frac{f'(x_0)^2}{2\kappa};
\tag{11}
\]
the reversed inequality holds when \(f''\le-\kappa\). This follows by
integrating the derivative bound and completing a square.

### 2.1 Positivity and the lower half of the interval

On \(0\le y\le.2\), (10) increases and
\[
 p''(y)\le p''(.2)=-4.648939296<-4.64,\qquad p'(y)<2.
\tag{12}
\]
Concavity and the two endpoint values give \(p>.94\) there. Also
\[
 p(.075)<1.063,\qquad |p'(.075)|<.03
\]
and (11) give
\[
 p<1.063+\frac{.03^2}{2(4.64)}<1.07
 \qquad(0\le y\le.2).
\tag{13}
\]
On \([.2,.25]\), \(p'\) is convex and is negative at both endpoints,
so \(p\ge p(.25)>.85\). On \([.25,.5]\), the concave quadratic
\(p''\) exceeds .19 at both endpoints. Since
\[
 p(.49)>.6132,\qquad |p'(.49)|<.0191,
\]
(11) gives \(p>.6132-.0191^2/.38>.6\) on this interval.

To bound \(p\) above on \([.2,.5]\), put \(t=y-.2\). Exact expansion
gives
\[
\begin{split}
 p(.2+t)={}&.94172727232-1.563873648t-2.324469648t^2\\
          &+17.71196928t^3-15.7611136t^4.
\end{split}
\]
For \(0\le t\le.3\), it follows that
\[
 p(.2+t)<.942-1.563t+2.99t^2\le.942 .
\tag{14}
\]

### 2.2 Three upper-half supports

For \(m=y-.5\), (9) becomes
\[
 p(.5+m)=.61392106+.121476m+5.10530136m^2
                         -1.20136704m^3-15.7611136m^4 .
\tag{15}
\]
Its first derivative is concave on \(0\le m\le.5\) and is positive
at zero. It therefore changes sign at most once, from positive to
negative, so the minimum of (15) is at an endpoint. Both endpoints
exceed .6. Together with Section 2.1, this proves
\[
 p(y)>.6\qquad(0\le y\le1).
\tag{16}
\]

The difference
\[
\begin{split}
 E(m)&=.62+5.5m^2-p(.5+m)\\
     &=.00607894-.121476m+.39469864m^2
                         +1.20136704m^3+15.7611136m^4
\end{split}
\]
satisfies \(E''>.789\) for \(m\ge0\). The fixed rational comparisons
\[
 E(.08)>.0001476,\qquad |E'(.08)|<.00298
\]
and (11) prove \(E>0\).

The derivative of (15) is positive on \([0,.25]\): it is concave
and positive at both endpoints. Hence (15) is at most
\(p(.75)=.883033185\) there. On \([.25,.5]\), its second derivative
is less than \(-3.4\). At \(m=.381\),
\[
 p(.881)<1.00274,\qquad |p'(.881)|<.0018.
\]
The concave version of (11) now proves
\[
 p(.5+m)<\min\{1.004,\ .62+5.5m^2\}
       \qquad(0\le m\le.5).
\tag{17}
\]
The same derivative concavity, using endpoints 0 and .2, also gives
\[
 p(y)\le p(.7)=.80759959632<.808
       \qquad(.5\le y\le.7).
\tag{18}
\]

Finally, on \(.2\le m\le.5\), put
\[
\begin{split}
 E_2(m)&=1.004-5(m-.38)^2-p(.5+m)\\
       &=-.33192106+3.678524m-10.10530136m^2\\
       &\hspace{20mm}+1.20136704m^3+15.7611136m^4 .
\end{split}
\]
Here \(E_2'''\!>0\), so \(E_2'\) is convex. On \([.2,.31]\) it
cannot change from negative to positive and then end at the negative
value \(E_2'(.31)<0\). Thus \(E_2\) has no interior minimum on that
interval. The endpoint comparisons
\[
 E_2(.2)>.0344,\qquad E_2(.31)>.01864
\]
prove positivity there. On \([.31,.5]\),
\[
 E_2''\ge E_2''(.31)>.19,\qquad
 E_2(.382)>.001251,\qquad |E_2'(.382)|<.00172.
\]
Applying (11) proves the third support
\[
 p(.5+m)<1.004-5(m-.38)^2
       \qquad(.2\le m\le.5).
\tag{19}
\]

### 2.3 A short source tangent

For \(0\le b\le.0315\), exact subtraction gives
\[
\begin{split}
 p(b)-(.99460+1.49b)
  =.00000968+b\{.50570616-16.73431848b\\
 \hspace{34mm}+30.32086016b^2-15.7611136b^3\}.
\end{split}
\]
The expression in braces decreases on this entire interval and its
value at .0315 exceeds .008. Consequently,
\[
 p(b)>.99460+1.49b\qquad(0\le b\le.0315).
\tag{20}
\]

## 3. Contact coordinates and two global speed estimates

For \(0\le b\le d\), define
\[
\begin{gathered}
 n=a_*(b)-\tfrac12,\qquad m=b-\tfrac12,\qquad
 r=\frac{b+\tfrac12}{a_*(b)+\tfrac12},\\
 \psi(b,\delta)=\tfrac12+n\sin\delta+m\cos\delta,\\
 v=\psi_\delta=n\cos\delta-m\sin\delta,\qquad
 K=\psi_b=\cos\delta-r\sin\delta,\\
 R_b^2=n^2+m^2=Q-2(a_*(b)+b).
\end{gathered}
\tag{21}
\]
Both \(v\) and \(K\) are positive on \(0\le\delta\le.7\). Indeed,
\(0<r\le1\), \(n>0\), \(n\ge m\), and \(.7<\pi/4\).
Also
\[
 \psi(b,\delta)\ge b,
\tag{22}
\]
strictly when \(\delta>0\). For \(m\le0\) this follows directly from
\(\psi-b=n\sin\delta-m(1-\cos\delta)\); for \(m>0\), use
\(n\ge m\) and \(\sin\delta+\cos\delta>1\).

The exact circle identity is
\[
 v^2=R_b^2-(\psi-\tfrac12)^2.
\tag{23}
\]
The function \(R_b^2\) decreases on \([0,d]\), strictly before \(d\).
Squaring positive quantities proves
\[
\begin{gathered}
 1.914575671<\sqrt{Q-\tfrac14}<1.914575672,\qquad d<.9,\\
 R_0^2<\rho_0:=1.086449,\qquad
 R_{.0315}^2<\rho_1:=1.04046.
\end{gathered}
\tag{24}
\]
For the last comparison, for example,
\[
 \sqrt{Q-.5315^2}>1.90607
\]
is exactly the required positive-square comparison.

### 3.1 The speed estimate after the source leaves its axis

We claim that, for every \(0\le y\le1\),
\[
 p(y)\sqrt{\rho_1-(y-\tfrac12)^2}<c.
\tag{25}
\]
On \(0\le y\le.2\), write the expression as \(H(y)=p(y)w(y)\).
Here \(w>.889\), and differentiation gives
\[
 H''=p''w-\frac{2p'(y-\tfrac12)}w-\frac{p\rho_1}{w^3}
 <-4.64(.889)+\frac2{.889}<-1.8.
\]
We used (12), positivity of \(p\), and the fact that the middle term
can be positive only when \(p'>0\). The fixed comparisons
\[
 H(.1)<.99049,\qquad |H'(.1)|<.024
\]
give
\[
 H<.99049+\frac{.024^2}{3.6}=.99065<c.
\]
These fixed radical comparisons follow by squaring; there is no
variable root enclosure in this step.

On \([.2,.5]\), (14) gives
\[
 H<.942(1.021)<.962<c.
\]
On \([.5,1]\), put \(A=(y-.5)^2\) and
\[
 A_0=\frac{1.004-.62}{5.5}.
\]
By (17), \(H^2\) is bounded by
\[
 \min\{1.004^2,\ (.62+5.5A)^2\}(\rho_1-A).
\]
The second branch increases up to \(A_0\), as direct differentiation
shows; the first branch decreases after \(A_0\). Their common value is
\[
 1.004^2(\rho_1-A_0)<.978423<c^2.
\]
This proves (25). In particular, whenever \(b\ge.0315\) and
\(0\le\psi\le1\),
\[
 p(\psi)v<c.
\tag{26}
\]

### 3.2 The speed estimate away from the small target window

We next claim
\[
 p(y)\sqrt{\rho_0-(y-\tfrac12)^2}<c
       \qquad(.16\le y\le1).
\tag{27}
\]
On \([.16,.2]\), (10) implies \(p'\le p'(.16)<-1.288\).
Writing the left side as \(H_0=pw_0\), we have \(w_0>.985\), so
\[
 H_0'<-1.288(.985)+\frac{1.07(.34)}{.985}<0.
\]
The fixed comparison \(H_0(.16)<.985<c\) finishes this part.
On \([.2,.5]\), use
\[
 H_0<.942(1.043)<.983<c,
\]
and on \([.5,.7]\), use \(H_0<.808(1.043)<.843<c\).

For \(.7\le y\le1\), put \(m=y-.5\). Both sides of
\[
 \sqrt{\rho_0-m^2}<1.103-.345m
\tag{28}
\]
are positive. The difference of their squares is a quadratic whose
global minimum equals
\[
 \frac{33816311}{44761000000}>0,
\]
so (28) holds throughout. By (19), \(H_0\) is less than the cubic
\[
\begin{split}
 V(m)&=\{1.004-5(m-.38)^2\}(1.103-.345m)\\
     &=.311046+4.09411m-6.826m^2+1.725m^3.
\end{split}
\]
On \([.2,.5]\), \(V''<-8\), while
\[
 V(.345)<.981885,\qquad |V'(.345)|<.000125.
\]
Thus
\[
 V<.981885+\frac{.000125^2}{16}<.982<c.
\]
This proves (27).

## 4. The harder transverse owner

We prove the following stronger scalar statement:
\[
\boxed{\quad
 c\delta+F(b)-F(y)\ge0
 \quad\text{if }0\le b\le d,\ 0\le\delta\le.7,\
 0\le y\le1,\ y\le\psi(b,\delta).
 \quad}
\tag{29}
\]
It is strict for \(\delta>0\), and at zero equality means \(y=b\).
Since \(F\) is strictly increasing, it is enough to take
\(y=\min\{\psi(b,\delta),1\}\). Initially restrict to \(\psi\le1\)
and put
\[
 C(b,\delta)=c\delta+F(b)-F(\psi(b,\delta)).
\]
Then
\[
 C_\delta=c-p(y)v,\qquad C_b=p(b)-p(y)K,\qquad
 C_{\delta\delta}=-p'(y)v^2+p(y)(y-\tfrac12).
\tag{30}
\]

### 4.1 The stationary-radius chord excludes an interior minimum

At an angular stationary point define
\[
 J(y)=(y-\tfrac12)^2+\frac{c^2}{p(y)^2}.
\]
Equations (23) and (30) give
\[
 R_b^2=J(y),\qquad C_{\delta\delta}=\frac{p(y)}2J'(y).
\tag{31}
\]
By (25) and (27), such a point must satisfy
\[
 b<.0315,\qquad y<.16.
\tag{32}
\]
If \(y\le.097\), then \(J'<0\). This is immediate if \(p'\ge0\).
Otherwise, (12) implies that \(p'\) decreases up to .097, whence
\[
 p'(y)\ge p'(.097)>-.453,\qquad
 p(y)\ge p(.097)>1.057.
\]
Consequently,
\[
 J'(y)\le-.806+\frac{2c^2(.453)}{1.057^3}<0.
\]
At a local minimum \(C_{\delta\delta}\ge0\). It follows that every
possible interior minimum lies in
\[
 b<.0315,\qquad .097<y<.16.
\tag{33}
\]

On this region \(n>.9\), \(m<0\), so
\[
 y-b\ge n\sin\delta.
\]
Since \(.9\sin(.18)>.16\), (33) forces \(\delta<.18\).
The elementary alternating-series estimates now give
\[
 \sin\delta\ge.9946\delta,\qquad
 \cos\delta\le1-.49865\delta^2.
\]
Moreover, \(r>.261\), \(v<1.043\), and
\(y-b=\int_0^\delta v(b,t)\,dt\le1.043\delta\).
Therefore
\[
 K\le1-.248(y-b)-.458(y-b)^2 .
\tag{34}
\]
Indeed, the two coefficients follow from
\[
 \frac{.261(.9946)}{1.043}>.248,\qquad
 \frac{.49865}{1.043^2}>.458.
\]

The function \(R_b^2\) is convex, since \(a_*\) is concave. Its
tangent at zero, with the positive-square bounds in (24), gives
\[
 R_b^2\ge1.086448656-1.47770b.
\tag{35}
\]
At a stationary point, (31) therefore implies
\[
 b\ge L(y):=\frac{1.086448656-J(y)}{1.47770}.
\tag{36}
\]
On \([.097,.16]\), \(p''<0\); hence
\[
 J''=2-2c^2\left(\frac{p''}{p^3}
                              -\frac{3p'^2}{p^4}\right)>0.
\]
Thus \(L\) is concave. Direct rational substitution gives
\[
 L(.097)>.03040,\qquad L(.16)>-.00852.
\]
The lower chord is consequently
\[
 L(y)\ge\ell(y):=.03040-\frac{139}{225}(y-.097).
\tag{37}
\]

Use (20) and (34) in (30):
\[
 C_b>
 G(b,y):=.99460+1.49b
       -p(y)\{1-.248(y-b)-.458(y-b)^2\}.
\tag{38}
\]
For \(\ell(y)\le b\le.0315\), one has \(y-b<.169\), and (13)
gives
\[
 G_b=1.49-p(y)\{.248+.916(y-b)\}
 >1.49-1.07\{.248+.916(.169)\}>0.
\]
It is therefore enough to put \(b=\ell(y)\). With \(t=y-.097\),
exact expansion of this degree-six polynomial yields the lower
polynomial
\[
\begin{split}
 G(\ell(y),y)
 &>.00248+.05194t
       +t^2\{9.678-28.699t-18.893t^4\}\\
 &>.00248+.05194t+7.8t^2>0
       \qquad(0\le t\le.063).
\end{split}
\tag{39}
\]
For transparency, subtracting the first displayed lower polynomial
from the exact expression in (38) leaves a polynomial with all seven
coefficients positive. The second inequality uses the one comparison
\[
 9.678-28.699(.063)-18.893(.063)^4>7.8.
\]
Thus \(C_b>0\), contradicting an interior minimum.

### 4.2 The axial endpoint has one positive polynomial remainder

It remains to control \(b=0\). By (27), \(C(0,\delta)\) increases
whenever \(\psi(0,\delta)\ge.16\). It suffices to treat
\(\psi(0,\delta)\le.16\), where the argument above gives
\(\delta<.18\).

Put
\[
 z=\tan(\delta/2),\qquad D=1+z^2,\qquad
 \nu=.914575672,\qquad N=2\nu z+z^2.
\]
Here \(0\le z<.091\), since \(\tan(.09)<.091\). The root bound
in (24) and the half-angle formulas give
\[
 \psi(0,\delta)\le N/D<1.
\]
If \(F(Y)=\sum_{j=0}^5 f_jY^j\), with the exact coefficients (3),
define
\[
 P(z)=2c(1-z^2/3)D^5+
 \frac{F(0)D^5-\sum_{j=0}^5 f_jN^jD^{5-j}}{z}.
\tag{40}
\]
The numerator in the quotient is divisible by \(z\), so \(P\) is
an explicitly defined polynomial of degree twelve, also at zero.
Since \(\arctan z\ge z-z^3/3\) and \(F\) is increasing,
\[
 C(0,\delta)\ge \frac{zP(z)}{D^5}.
\tag{41}
\]

We now verify \(P>0\) on the entire interval \(0\le z\le.091\).
Expanding (40), its second derivative has the following single
coefficient lower bound:
\[
\begin{split}
 P''(z)>{}&64.9203-263.149z-329.775z^2\\
          &-60.65z^7-118.929z^8-87.215z^{10}
          >38.24 .
\end{split}
\tag{42}
\]
Every coefficient of the difference between \(P''\) and the first
polynomial is nonnegative, with positive constant coefficient. The
last inequality follows by substituting .091 in its negative terms.
The two fixed rational evaluations of (40) are
\[
 P(.0804)>.000485,\qquad |P'(.0804)|<.01248.
\]
Consequently (11) gives
\[
 P(z)>.000485-\frac{.01248^2}{2(38.24)}
       >.0004829>0.
\tag{43}
\]
This proves strict axial positivity for every \(\delta>0\), and
then extends past \(\psi=.16\) by (27).

### 4.3 All boundaries and strictness

Apply the compact minimum principle to
\[
 0\le b\le d,\qquad0\le\delta\le.7,\qquad\psi(b,\delta)\le1.
\]
At \(\delta=0\), \(C=0\). The boundary \(b=0\) is strictly positive
for positive angles by Section 4.2. The boundary \(b=d\) has
\(C_\delta>0\) by (25), so reducing a positive angle reduces its
cost. The same is true at \(\psi=1\), by (27). Finally, at
\(\delta=.7\), either \(b\ge.0315\) and (25) applies, or
\[
 \psi(b,.7)>.9\sin(.7)>.16
\]
and (27) applies. Thus this upper angle boundary also has
\(C_\delta>0\).

Every remaining minimum would be an interior one, excluded in
Section 4.1. This proves \(C\ge0\). The same argument excludes a
zero minimum at a positive angle, so \(C>0\) there. When
\(\psi>1\), the clamped cost \(c\delta+F(b)-F(1)\) increases with
\(\delta\) after \(\psi\) first reaches 1. This covers the entire
domain of (29). At zero, the strict increase of \(F\) gives exactly
the equality assertion in (29).

To deduce (7) from the original separator (6), take \(y=1-B\).
Since \(B\le d<1\), this lies in \([0,1]\), and (6) gives
\[
 y\le a\sin\delta+b\cos\delta-h(\delta)
      \le\psi(b,\delta).
\]
The last inequality uses \(a\le a_*(b)\) and
\(\sin\delta\ge0\). Thus it preserves every radial state; it has
not assumed that the source was already on the outer circle.

## 5. The other original transverse owner

Define the reflected increasing function
\[
 \widetilde F(t)=-F(1-t),\qquad
 \widetilde F'(t)=p(1-t)>0.
\]
We prove the companion support
\[
 c\delta+\widetilde F(B)-\widetilde F(x)\ge0
 \quad\text{when }0\le B\le d,\quad
 0\le x\le1,\quad x\le\psi(B,\delta).
\tag{44}
\]
Again it suffices to put \(x=\min\{\psi,1\}\). Before clamping, the
angle derivative of this cost is
\[
 c-p(1-\psi)v.
\tag{45}
\]
It is strictly positive throughout the domain. If \(B\ge.0315\),
apply (25) to \(1-\psi\), since
\[
 (1-\psi-\tfrac12)^2=(\psi-\tfrac12)^2.
\]
If \(B<.0315\), the whole-angle bound
\[
\begin{split}
 \psi(B,\delta)
 &\le B+.915\sin(.7)+\tfrac12(1-\cos(.7))\\
 &<.0315+.915(.645)+\tfrac12(.236)
   =.739675
\end{split}
\]
gives \(1-\psi>.26>.16\), so (27) applies instead. After clamping,
the derivative is simply \(c>0\).

At zero the clamped cost is zero. Integration proves (44), strictly
for positive angles. If the actual \(x\) is smaller, the strict
increase of \(\widetilde F\) only improves it.

Under original separator (5), put \(x=1-b\). Then
\[
 x\le A\sin\delta+B\cos\delta-h(\delta)
      \le\psi(B,\delta),
\]
using \(A\le a_*(B)\) and \(\sin\delta\ge0\). Equation (44)
becomes
\[
 c\delta+\widetilde F(B)-\widetilde F(1-b)
 =c\delta+F(b)-F(1-B)\ge0.
\]
This proves the second original owner, including all its radial
states. At zero, both separators reduce to \(b+B\ge1\), and
strict monotonicity of \(F\) makes equality equivalent to
\(b+B=1\). The theorem and all of its strictness claims follow.

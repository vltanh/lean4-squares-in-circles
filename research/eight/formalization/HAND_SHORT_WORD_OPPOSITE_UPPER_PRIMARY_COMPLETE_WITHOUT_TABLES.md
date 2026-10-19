# Complete short-word opposite primary owners above a quarter turn

At \(Q=9789/2500\), all six original outer/outer opposite-sign primary
owners on edges \(2,4,6\) of \(0010111\) satisfy the assembly bound on
their entire upper angle halves
\[
 \phi=\frac\pi2+u,\qquad 0\le u\le.7.
\tag{1}
\]
Original owners
\[
 (2,-,+,4),\quad(4,-,+,4),\quad(6,-,+,2)
\]
were proved in
[HAND_SHORT_WORD_UPPER_PRIMARY_CONTACTS_WITHOUT_TABLES.md](HAND_SHORT_WORD_UPPER_PRIMARY_CONTACTS_WITHOUT_TABLES.md).
This note proves their complete complement
\[
 (2,-,+,2),\quad(4,-,+,2),\quad(6,-,+,4)
\tag{2}
\]
with \(C>.898\). In conjunction with
[HAND_SHORT_WORD_NEGATIVE_PRIMARY_FAMILIES_WITHOUT_TABLES.md](HAND_SHORT_WORD_NEGATIVE_PRIMARY_FAMILIES_WITHOUT_TABLES.md),
this closes all twelve original opposite-primary angle halves.

The proof retains the true contact curve. It uses its one intrinsic
diagonal transition, global curvature in the state coordinate, and an
explicit quartic bound for the speed of the contact point. No angle
mesh, coefficient-status appendix, or computed minimum is a premise.
All terminating decimals are exact rationals.

## 1. Exact normalization and the contact reduction

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12,\quad
 \rho=\frac1{2(a_0+\tfrac12)}.
\tag{3}
\]
Both outer states satisfy
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\qquad
 A=\sqrt{Q-(B+\tfrac12)^2}-\tfrac12,\qquad 0\le b,B\le d.
\tag{4}
\]
After exact reflection and reversal for original axis 2, all three
owners in (2) have source axis 4 and signs \((-,+)\). In their order,
the exact coefficient tuples \((c,p,q,P,t)\) are
\[
\begin{aligned}
 {\cal I}&=(.6618,-.51554,1.19909,-.09133,.88074),\\
 {\cal II}&=(-.25931,0,.86884,-.19335,.76744),\\
 {\cal III}&=(-.1866,.18602,.80996,0,.94766).
\end{aligned}
\tag{5}
\]
They are literal adjacent role-label differences. Reflection and
reversal applies the rule \((p,q,P,t)\mapsto(-P,t,-p,q)\) and preserves
both the angle and cost.

Write \(s=\sin u,\ k=\cos u,\ W=(1+k+s)/2\). The normalized original
weak separator and corrected cost are
\[
 a+As-Bk\ge W,\qquad
 C=\frac\pi2+u+c+pa-qb-PA-tB.
\tag{6}
\]
Regard the source cost as a function of \(a\). Its derivative is
\[
 L=p+q\frac{a+\tfrac12}{b+\tfrac12}\ge p+q>0.
\tag{7}
\]
Thus at fixed \(B\), the least feasible source coordinate is
\[
 a=\max\{d,a_c(B)\},\qquad a_c(B)=W-As+Bk.
\tag{8}
\]
Since
\[
 a_c'(B)=k+s\frac{B+\tfrac12}{A+\tfrac12}>0,
\]
the contact part of the feasible arc is an interval. On a possible
preceding part where \(a=d\), the cost derivative is
\(P(B+\tfrac12)/(A+\tfrac12)-t<0\). Its minimum is therefore at the
first contact point. It suffices to analyze the entire contact interval
beginning there; this also includes the axial and source-diagonal
boundary possibilities.

On this interval the exact derivatives in \(B\) are
\[
\begin{aligned}
 C_B&=L\left(k+s\frac{B+\tfrac12}{A+\tfrac12}\right)
                      +P\frac{B+\tfrac12}{A+\tfrac12}-t,\\
 C_{BB}&=
 \frac{qQ}{(b+\tfrac12)^3}
       \left(k+s\frac{B+\tfrac12}{A+\tfrac12}\right)^2
 +\frac{Q}{(A+\tfrac12)^3}(Ls+P).
\end{aligned}
\tag{9}
\]
This is a convexity statement about the actual coupled contact states.

The elementary bounds
\[
\begin{gathered}
 1.414575671<a_0<1.414575672,\qquad
 .899214065109<d<.899214065110,\qquad R<1.978788,\\
 .26115<\rho<.262,\qquad k>.764,\qquad 0\le s<.645
\end{gathered}
\tag{10}
\]
give the following uniform state curvatures:
\[
 C_{BB}>.86\quad({\cal I}),\qquad
 C_{BB}>.44\quad({\cal II}),\qquad
 C_{BB}>.67\quad({\cal III}).
\tag{11}
\]
For instance the first is already
\[
 \frac{1.19909(3.9156)(.764)^2}{1.4^3}
             -\frac{3.9156(.09133)}{1.399^3}>.86.
\tag{12}
\]
Use \(q=.86884,\ |P|=.19335\) or \(q=.80996,\ P=0\) in the same
formula for the other two.

## 2. The intrinsic lower endpoint of contact

At \(B=0\), write
\[
 K(u)=a_c(0)+\tfrac12
 =1+\frac k2-(a_0-\tfrac12)s,\quad
 v(u)=\sqrt{Q-K(u)^2},\quad
 h(u)=\frac s2+(a_0-\tfrac12)k.
\tag{13}
\]
Then \(K'=-h<0\). There is a unique transition \(u_d\) defined by
\[
 K(u_d)=d+\tfrac12,\qquad .1072<u_d<.1073<.108.
\tag{14}
\]
The two inequalities follow by direct substitution of the alternating
series at \(.1072,.1073\), followed by squaring the fixed radicals.
Before \(u_d\), the contact interval begins at \(B=0\).
After \(u_d\), its lower endpoint is the contact with \(a=b=d\).

On \(0\le u\le u_d\), the cost and its \(B\)-derivative at the lower
endpoint are
\[
\begin{aligned}
 F(u)&=\frac\pi2+u+c+p(K-\tfrac12)-q(v-\tfrac12)-Pa_0,\\
 H(u)&=L(k+\rho s)+P\rho-t,\qquad L=p+qK/v.
\end{aligned}
\tag{15}
\]
The useful derivative formulas are
\[
 F'=1-Lh,\qquad
 F''=\frac{qQh^2}{v^3}-Lh',\qquad
 L'=-\frac{qQh}{v^3}.
\tag{16}
\]
On this interval,
\[
\begin{gathered}
 k>.99417,\quad s<.108,\quad
 1.399<K\le1.5,\quad 1.290<v<1.4,\\
 .914575671<h<.968576,\qquad h'\le\tfrac12.
\end{gathered}
\tag{17}
\]
In (9), the sharper cosine bound also proves
\[
 C_{BB}>1.56\qquad({\cal I},\ 0\le u\le u_d),
\tag{18}
\]
since the lower expression (12) with \(.764\) replaced by \(.99417\)
exceeds \(1.5605\).

## 3. Uniform geometry of the diagonal contact

For \(u_d\le u\le.7\), put
\[
 z_0=d-\tfrac12,\quad z=z_0-s,\quad T=\sqrt{Q-z^2},
 \qquad U=kT-sz,\quad V=sT+kz.
\tag{19}
\]
These give the lower contact endpoint
\[
 A=U-\tfrac12,\qquad B=V-\tfrac12.
\]
Indeed \(U^2+V^2=Q\) and \(kV-sU=z_0-s\), exactly the
source-diagonal contact equation obtained from (6).

The full-domain bounds are
\[
\begin{gathered}
 1.938<T<R,\quad 0<U<1.915,\quad .5\le V<1.088,\\
 U>1.65,\quad 0<\frac VU<.66,\quad U\le T.
\end{gathered}
\tag{20}
\]
Here \(-.246<z<.399215\) proves the bound on \(T\).
Set \(\omega=1-k/T\). Then
\[
 U'=-V\omega,\qquad V'=U\omega>0.
\tag{21}
\]
Initially \(U=a_0+\tfrac12,\ V=.5\), so \(U<1.915\).
At the right endpoint, the elementary sine/cosine bounds give
\[
 V(.7)<.64422(1.978788)
               -.76484(.64421-.399215)
 =\frac{27184820739}{25000000000}<1.088.
\]
Now \(U^2=Q-V^2\) gives \(U>1.65\) and \(V/U<.66\).
For \(z\ge0\), \(U\le T\) is immediate. For \(z<0\), we have
\(s>.3992,\ k<.917\), so
\[
 \frac UT=k+\frac{s(s-z_0)}T
 <.917+\frac{.645(.645-.3992)}{1.938}<1.
\tag{22}
\]

### A global contact-speed bound

The identity (21) gives
\[
 B'=V'=kT-k^2-sz(1-k/T).
\tag{23}
\]
If \(z\ge0\), this is at most \(kT-k^2\le Q/4=.9789\).
If \(z<0\), use \(R/2>.9893,\ k\le1-s^2/2\), and
\(1-k/T<.614\). Since \(s>.3992\),
\[
 B'\le
 .9789+.614s(s-.3992)-(s^2/2-.0107)^2.
\tag{24}
\]
The derivative of this explicit quartic is
\[
 s(1.2494-s^2)-.2451088>0
 \quad\text{on }[.3992,.645].
\]
For example its lower bound
\(.3992(1.2494-.645^2)-.2451088\) is positive.
Thus the right side of (24) is at most
\[
 \frac{33193982443}{32000000000}<1.04.
\]
Together with the \(z\ge0\) case, this proves
\[
 0<B'<1.04
       \qquad(u_d\le u\le.7).
\tag{25}
\]
This is a single global derivative argument, without an angle
subdivision.

At this lower contact endpoint define
\[
 G(u)=\frac\pi2+u+c+(p-q)d-P(U-\tfrac12)-t(V-\tfrac12).
\tag{26}
\]
Equations (20), (25) give
\[
 G'=1-(t-PV/U)B'
 >1-1.04(t+.66|P|)>0
\tag{27}
\]
for all three tuples in (5). The three final rational lower bounds
are respectively greater than \(.021,\ .069,\ .014\).
Thus each diagonal-reference cost increases on its entire domain.

## 4. The second and third tuples are minimized at the endpoint

For \({\cal II}\) and \({\cal III}\), the lower-endpoint derivative
\(H\) in (15) is positive before the transition. In fact,
\[
 H>.86884(.99417)-.19335(.262)-.76744>.04
                                  \quad({\cal II}),
\]
and
\[
 H>.99598(.99417)-.94766>.04
                                  \quad({\cal III}).
\tag{28}
\]
The state curvature (11) therefore puts the minimum at that endpoint.

For \(u\ge u_d\), the lower-endpoint derivative becomes
\[
 H=(p+q)(k+sV/U)+PV/U-t.
\tag{29}
\]
Writing \(L=p+q\), the identity \(kU+sV=T\) gives
\[
 HU=LT+PV-tU
 \ge L(1.938)-R\sqrt{P^2+t^2}>0
\tag{30}
\]
for both tuples. This last fixed comparison follows by squaring;
the left positive margin exceeds \(.05\) for each tuple.
Thus the contact minimum stays at its lower endpoint after the
transition as well.

For \({\cal II}\), (17) gives \(L<1.011\) before the transition and
hence \(F'=1-Lh>.02\). Its initial value exceeds \(.89810\).
Equation (27) preserves this lower bound after the transition.

For \({\cal III}\), the same bounds give \(L<1.129\), so \(F'>-.1\).
Its initial value exceeds \(.92987\). Therefore
\[
 F(u)>.92987-.1(.108)>.919
 \quad(0\le u\le u_d).
\]
Again (27) preserves this lower bound after the transition. These two
original upper owners are now completely covered.

## 5. The first tuple before the transition

For \({\cal I}\), direct fixed endpoint arithmetic in (15)--(16)
gives
\[
 F(0)>.89826,\qquad F'(0)>.196,\qquad H(0)>-.027.
\tag{31}
\]
Moreover \(L<.879\), and (16)--(17) show
\[
 F''>
 \frac{1.19909(3.9156)(.914575671)^2}{1.4^3}
                                  -.879/2>.99.
\tag{32}
\]
Thus \(F(u)>.89826+.196u\).

Differentiating \(H\) from (15) gives
\[
 H'=-\frac{qQh(k+\rho s)}{v^3}
                         +L(\rho k-s).
\tag{33}
\]
The first term has magnitude less than
\[
 \frac{1.19909(3.9156)(.968576)(1.028296)}{1.290^3}<2.18.
\]
The second term is bounded below by
\[
 .68355\{.26115(.99417)-.108\}.
\]
Consequently \(H'>-2.08\), and
\[
 H(u)>-.027-2.08u.
\tag{34}
\]

The exact strong-convexity remainder from (18) now gives every contact
state the lower bound
\[
 C\ge F(u)-\frac{\min\{H(u),0\}^2}{2(1.56)}
 >.89826+.196u-\frac{(.027+2.08u)^2}{3.12}.
\tag{35}
\]
The last expression is a concave quadratic. Its minimum on
\([0,.108]\) is at an endpoint. Those values satisfy
\[
 .89826-\frac{.027^2}{3.12}>.89802,\qquad
 .89826+.196(.108)-\frac{(.027+2.08(.108))^2}{3.12}
 =\frac{584435973}{650000000}>.89913.
\tag{36}
\]
This proves \(C>.898\) throughout the whole pre-transition domain.

## 6. The first tuple after the transition

For \({\cal I}\), let
\[
 L=p+q=.68355,\qquad P=-.09133,\qquad t=.88074.
\]
We prove on the entire diagonal-reference curve that
\[
 H=Lk+(Ls+P)V/U-t>-.216.
\tag{37}
\]
Only signs of the displayed analytic factors are used in the following
three cases.

If \(Ls+P<0\), then \(s<.134\) and \(k>.9909\).
Also \(u\ge u_d>.1072\) gives \(s>.10679\). Thus (20) yields
\[
 H>L(.9909)+(L(.10679)+P)(.66)-t>-.216.
\tag{38}
\]

If \(Ls+P\ge0\) and \(z\ge0\), then \(V/U\ge s\) by (19)--(20).
Also \(k\ge1-s^2/1.764\). Therefore
\[
 H\ge L-t+Ps+.433Ls^2
 \ge L-t-\frac{P^2}{4(.433)L}>-.205.
\tag{39}
\]

If \(z<0\), then \(Ls+P>0\). From \(U\le T\) and \(T>1.938\),
\[
 \frac VU\ge\frac VT=s+\frac{kz}{T}
       \ge s+\frac{z}{1.938}
       >s+\frac{.3992-s}{1.938}.
\]
It follows that \(H\) is at least the rational quadratic
\[
\begin{split}
 &L-t+\frac{P(.3992)}{1.938}\\
 &\quad+
 \left[\frac{L(.3992)}{1.938}
                        +P\left(1-\frac1{1.938}\right)\right]s\\
 &\quad+
 L\left(1-\frac1{1.938}-\frac1{1.764}\right)s^2.
\end{split}
\tag{40}
\]
Its quadratic coefficient is negative. At both endpoints of
\([.3992,.645]\), its value exceeds \(-.187\), by direct substitution.
Thus it exceeds \(-.187\) throughout this interval. This completes (37).

The exact reference value satisfies
\[
 G(u_d)=F(u_d)>F(.1072)>.9272.
\tag{41}
\]
The first inequality uses (14), (32); the final one is a single fixed
substitution into (13), (15). Since \(G'>0\), the state curvature
\(C_{BB}>.86\) and (37) give, for every contact state after the transition,
\[
 C\ge G(u)-\frac{\min\{H(u),0\}^2}{2(.86)}
 >.9272-\frac{.216^2}{1.72}>.90007.
\tag{42}
\]
This proves the entire post-transition part of the first original owner.

## 7. Endpoint verification and complete scope

All fixed values above involve only (3), the coefficients (5), and the
explicit functions (13), (15). To check the delicate initial comparisons,
one may use
\[
 1.29058126439213<\sqrt{Q-\tfrac94}<1.29058126439214,
 \qquad \frac\pi2>1.570795.
\]
At \(u=0\), the exact formulas are
\[
\begin{aligned}
 F(0)&=\frac\pi2+c+p
             -q\left(\sqrt{Q-\tfrac94}-\tfrac12\right)-Pa_0,\\
 F'(0)&=1-\left[p+\frac{3q}{2\sqrt{Q-\tfrac94}}\right]
                                             (a_0-\tfrac12),\\
 H(0)&=p+\frac{3q}{2\sqrt{Q-\tfrac94}}+P\rho-t.
\end{aligned}
\]
These give (31), \(F_{\cal II}(0)>.89810\), and
\(F_{\cal III}(0)>.92987\) directly.

For (14), evaluate the decreasing \(K\) at its two displayed endpoints.
For (41), evaluate \(F(.1072)\). The alternating sine/cosine series and
squaring give \(F_{\cal I}(.1072)>.92720\). These are endpoint
comparisons for global arguments already established, not estimates
on a collection of angle boxes.

Sections 1--6 cover the entire original weak separating domain for all
three tuples (5): the free-source segment, both contact endpoints,
the intrinsic diagonal transition, and every contact state between.
Their strict inequalities also cover all simultaneous owners.
Together with the three earlier upper-primary owners and the complete
negative-primary theorem, every opposite-primary quarter-one branch
of the short word is now table-free.


# Three whole-angle primary contact families for 0010111

All decimals below are exact rationals. This note proves the complete
upper angle half \(0\le\phi-\pi/2\le.7\) for the following original
outer/outer branches of the short wrong word:

* edge 2, signs \((-,+)\), original source-primary axis 4;
* edge 4, signs \((-,+)\), original source-primary axis 4;
* edge 6, signs \((-,+)\), original target-primary axis 2.

Their corrected costs all exceed \(.8978\). This is stronger than the
required \(.8975\) on edge 2 and \(.89765\) on the other edges.
The proof covers every state and every angle in the indicated half.
It uses exact contact curves and a single intrinsic change of contact
type, followed in one case by the sign of its exact angular derivative.
It uses no mesh of angles or states.

## 1. Coordinates, labels, and the common contact geometry

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 X_0=\sqrt{Q-\tfrac14},\quad a_0=X_0-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12,\quad \rho=\frac1{2X_0}.
\]
Both outer states satisfy
\[
 (a+\tfrac12)^2+(b+\tfrac12)^2
 =(A+\tfrac12)^2+(B+\tfrac12)^2=Q,\qquad
 0\le b\le a,\quad0\le B\le A.
\]
Reflect and reverse the third original branch. The three exact normalized
costs are
\[
 C=\frac\pi2+u+c+pa-qb-PA-tB,\qquad0\le u\le.7,
\tag{1}
\]
with coefficient tuples
\[
\begin{aligned}
{\cal I}&:\quad(c,p,q,P,t)=(.6618,.09133,.88074,.51554,1.19909),\\
{\cal II}&:\quad(c,p,q,P,t)=(-.25931,.19335,.76744,0,.86884),\\
{\cal III}&:\quad(c,p,q,P,t)=(-.1866,0,.94766,-.18602,.80996).
\end{aligned}
\tag{2}
\]
The original separator becomes, in each case,
\[
 a+A\sin u-B\cos u\ge W,\qquad
 W=\frac{1+\cos u+\sin u}{2}.
\tag{3}
\]
The source cost \(pa-qb(a)\) strictly increases with \(a\), since
\[
 L:=\frac{d}{da}(pa-qb)=p+q\frac{a+\tfrac12}{b+\tfrac12}>0.
\]
The target cost \(-PA-tB\) strictly decreases with \(B\), since
\(P(B+\tfrac12)/(A+\tfrac12)-t<0\). Thus a minimum is on the contact
curve
\[
 a=W-A\sin u+B\cos u.
\tag{4}
\]
If reducing \(a\) first reaches \(a=d\) with slack, increase \(B\)
until (4) is attained. The contact formulas below show that this happens
before \(B=d\).

Write
\[
 s=\sin u,\quad k=\cos u,\quad
 U=A+\tfrac12,\quad V=B+\tfrac12,\quad
 K=a+\tfrac12=1+s-Us+Vk,\quad
 Z=b+\tfrac12=\sqrt{Q-K^2}.
\]
Then
\[
 a_B=k+s\frac VU,\qquad
 a_{BB}=\frac{sQ}{U^3}.
\]
Along the contact, therefore,
\[
 C_B=L\left(k+s\frac VU\right)+P\frac VU-t,
\tag{5}
\]
\[
 C_{BB}=
 \frac{qQ}{Z^3}\left(k+s\frac VU\right)^2+
 \frac{Q}{U^3}(Ls+P).
\tag{6}
\]
In all three cases this is positive throughout the actual contact
domain. For \({\cal I},{\cal II}\), every term is nonnegative and the
first is positive. For \({\cal III}\), even dropping the \(Ls\) term
gives
\[
 C_{BB}>
 \frac{.94766Q(.764)^2}{1.4^3}
 -\frac{.18602Q}{1.399^3}>.52.
\tag{7}
\]
Here \(Z<1.4,\ U>1.399\), and \(\cos u>.764\). In case \({\cal I}\)
the uniform lower bound from (6) is stronger:
\[
 C_{BB}>
 \frac{.88074Q(.764)^2}{1.4^3}
 +\frac{.51554Q}{1.915^3}>1.
\tag{8}
\]

### The two intrinsic lower contact endpoints

The least feasible target \(B\) is axial until the source reaches its
diagonal. Define \(u_d\) by
\[
 1+\tfrac12\cos u_d-(X_0-1)\sin u_d=d+\tfrac12.
\tag{9}
\]
The left side strictly decreases. Single endpoint comparisons give
\[
 .1072<u_d<.1073.
\tag{10}
\]
For \(0\le u\le u_d\), the lower endpoint has \(B=0\), with
\[
 K_0(u)=1+\tfrac12k-(X_0-1)s,\qquad
 Z_0(u)=\sqrt{Q-K_0(u)^2}.
\tag{11}
\]
For \(u_d\le u\le.7\), the lower endpoint has \(a=b=d\). Put
\[
 z_0=d-\tfrac12,\quad z=z_0-s,\quad T=\sqrt{Q-z^2},
\]
and then
\[
 U=kT-sz,\qquad V=sT+kz.
\tag{12}
\]
This is the unique positive-circle solution of its contact equation
\(Vk-Us=z\).

The formulas in (12) give
\[
 V'=U\omega>0,\qquad U'=-V\omega,\qquad
 \omega=1-\frac{k}{T}>0.
\tag{13}
\]
When \(z\ge0\), \(V\le .4R<.8\). When \(z<0\),
\[
 V\le sR+.764(z_0-s)
 <.645(1.978788-.764)+.764(.4)<1.09.
\]
Thus this entire contact lies inside the actual outer arc:
\(V<1.09<\sqrt{Q/2}<U\), and \(B<d\). This also justifies the
contact reduction following (4).

We shall repeatedly use the rational root bounds
\[
\begin{gathered}
1.914575671<X_0<1.914575672,\qquad
1.290581264<\sqrt{Q-\tfrac94}<1.290581265,\\
.899214065109<d<.899214065110,\qquad
.26115<\rho<.262,\qquad R<1.978788.
\tag{14}
\end{gathered}
\]
Every one follows by squaring. Values of sine and cosine at a named
rational point below follow from their alternating series; no variable
interval enclosure is a premise.

## 2. Cases II and III: the contact minimum is its lower endpoint

For case \({\cal II}\), the derivative at that endpoint, and indeed at
any actual contact, satisfies
\[
 C_B\ge(p+q)(k+\rho s)-t
 >(.96079)(.932)-.86884>0.
\tag{15}
\]
The uniform inequality \(k+\rho s>.932\) follows by concavity in \(u\):
at zero it is 1, and at \(.7\) it exceeds
\(.764+.26115(.644)>.932\).

For case \({\cal III}\), at the lower endpoint (5) is at least
\[
 qk-t+(qs+P)\frac VU.
\tag{16}
\]
If \(qs+P\ge0\), use \(V/U\ge\rho\). The same endpoint inequality gives
\[
 (16)>.94766(.932)-.18602(.262)-.80996>0.
\]
If \(qs+P<0\), then \(s<.197\) and \(k>.98\). At either lower endpoint,
\(V/U<.44\): this is immediate at the axial endpoint; in (12),
\[
 V<.4+.197R<.79,\qquad U>1.81.
\]
Consequently
\[
 (16)>.94766(.98)-.80996-.18602(.44)>0.
\tag{17}
\]
The convexity in (7) now makes the contact cost increasing in \(B\).
Both cases reduce exactly to the two lower endpoint curves.

### 2.1 The axial endpoint

Let \(F(u)\) denote the cost at (11), and put
\[
 h=\tfrac12s+(X_0-1)k.
\]
Then
\[
 F'=1-\left(p+qK_0/Z_0\right)h,\qquad
 F''=\frac{qQh^2}{Z_0^3}
       -\left(p+qK_0/Z_0\right)(K_0-1).
\tag{18}
\]
On \(0\le u\le u_d\), use
\[
 h>.908,\quad Z_0<1.4,\quad Z_0>1.29,\quad
 K_0\le1.5,\quad K_0-1\le.5.
\]
For both cases \({\cal II},{\cal III}\), this yields
\[
 F''>
 \frac{.76744Q(.908)^2}{1.4^3}
 -\frac12\left(.19335+\frac{.94766(1.5)}{1.29}\right)
 =\frac{14705244143311}{57613281250000}>\frac14.
\tag{19}
\]
Their exact initial values and slopes satisfy
\[
 F(0)>.8981,\qquad F'(0)>-.008.
\tag{20}
\]
Hence the elementary completed-square estimate gives
\[
 F(u)>.8981-\frac{.008^2}{2(1/4)}
       =.897972>.8978.
\tag{21}
\]

### 2.2 The source-diagonal endpoint

Let \(G(u)\) be the cost at (12). From (13),
\[
 G'=1-(tU-PV)\omega.
\tag{22}
\]
For every \(u_d\le u\le.7\),
\[
 B'=U\omega
 =k(T-k)+sz(k/T-1)
 <\frac Q4+.645(.246)(.614)
 <1.077.
\tag{23}
\]
For the first term use \(k(T-k)\le T^2/4\le Q/4\). The second is
nonpositive if \(z\ge0\); otherwise
\(|z|<.246\) and \(1-k/T<.614\).

For case \({\cal II}\), (22) is greater than \(1-.86884(1.077)>0\).
For case \({\cal III}\), also using \(V<1.09\),
\[
 G'>1-.80996(1.077)-.18602(1.09)(.614)
 =\frac{7943337}{2500000000}>0.
\tag{24}
\]
Thus these endpoints increase from their common axial join \(u_d\).
Equation (21) completes both cases.

## 3. Case I: uniform control in the target coordinate

This case has a small interior contact region, so a lower-endpoint
monotonicity assertion would be false. We retain that region explicitly.

On the axial angle range \(0\le u\le u_d\), (6) gives the sharper
uniform bound
\[
 C_{BB}>
 \frac{.88074Q(.99417)^2}{1.4^3}
 +\frac{.51554Q}{1.915^3}>1.52.
\tag{25}
\]
Let \(J(u)=C_B(0,u)\) be the derivative at its axial endpoint. With
\(g=k+\rho s\), formula (5) becomes
\[
 J=\left(p+qK_0/Z_0\right)g+P\rho-t.
\tag{26}
\]
This decreases on \([0,u_d]\). Indeed
\[
 J'=-\frac{qQh}{Z_0^3}g+
                (p+qK_0/Z_0)(-s+\rho k)<0:
\]
the magnitude of the first term exceeds
\(.88074Q(.908)/1.4^3\), while the positive part of the second is less
than
\((.09133+.88074(1.5)/1.29)(.262)\).
Here \(g\ge1\), since \(u_d<.108<2\arctan\rho\).

At the source-diagonal endpoint, put \(\ell=p+q=.97207\). Then
\[
 J_d(u)=\ell k-t+(\ell s+P)V/U.
\tag{27}
\]
This increases on \([u_d,.7]\). Differentiating and using (13) gives
\[
 J_d'=\frac{\ell z}{U}
       +(\ell s+P)\frac{Q\omega}{U^2}>0.
\tag{28}
\]
If \(z\ge0\), this is immediate. If \(z<0\), multiply by \(U^2\):
the negative term has magnitude less than
\(.97207(.246)(1.978788)\), while the positive term exceeds
\[
 \{.97207(.3992)+.51554\}\,Q(.532),
\]
which is larger. The bounds \(k<.917,\ T>1.963,\ \omega>.532\) in this
case follow directly from \(s>z_0>.3992\) and \(|z|<.246\).

At the common join, (10) and (14) give
\[
\begin{split}
 J(u_d)=J_d(u_d)
 &>.97207\{.99417+.10679(.26115)\}
                 +.51554(.26115)-1.19909\\
 &=-\frac{14188921252681}{200000000000000}>-.071.
\end{split}
\tag{29}
\]
Thus every lower endpoint derivative of case \({\cal I}\) is greater
than \(-.071\), with the sharpest value at the intrinsic join.

## 4. Case I on the source-diagonal branch

We prove the whole-branch estimate
\[
 G(u)>.9004\qquad(u_d\le u\le.7).
\tag{30}
\]
Equations (8) and (29) then give, for every feasible contact on this
angle range,
\[
 C>.9004-\frac{.071^2}{2}
   =\frac{1795759}{2000000}=.8978795>.8978.
\tag{31}
\]

### 4.1 A uniform positive angular curvature

Put
\[
 H=tU-PV>0,\qquad E=PU+tV.
\]
By (13),
\[
 G''=\omega^2E-\omega'H,\qquad
 \omega'=\frac{z_0+(Q-1-z_0^2)s+z_0s^2}{T^3}.
\tag{32}
\]
The numerator is bounded above by
\[
 N(s)=.4+2.7563s+.4s^2.
\]
We shall show \(G''>.02\) on the entire branch by the two intrinsic
possibilities \(z\ge0\) and \(z<0\).

If \(z\ge0\), then \(0\le s\le z_0<.4\). Set
\(T_-(s)=1.9379+.102s\). We have \(T\ge T_-\): the polynomial
\[
 Q-(.4-s)^2-T_-^2
 =.00014359+.4046684s-1.010404s^2
\]
is concave and positive at both 0 and \(.4\). Also \(k\le1-s^2/2\).
It follows that \(\omega'\le.73\omega^2\) from the following single
polynomial inequality on \(0\le s\le.4\):
\[
\begin{split}
&.73T_-(T_--1+s^2/2)^2-N(s)\\
&\quad=.84442089456547-2.4201302831342s
       +.955780925704s^2+.21490674984s^3\\
&\qquad\quad+.36126167s^4+.018615s^5>0.
\end{split}
\tag{33}
\]
Its derivative is increasing but still less than \(-1.45\) at
\(.4\); its value there exceeds \(.052\). These two fixed comparisons
prove (33) throughout its stated interval.
Furthermore \(U>1.8,\ V/U\ge\rho>.26115,\ \omega>.483\). Hence
\[
\begin{split}
G''&>\omega^2(E-.73H)\\
&>(.483)^2(1.8)
 \left[(.51554-.73(1.19909))
       +(1.19909+.73(.51554))(.26115)\right]\\
&>.02168>.02.
\end{split}
\tag{34}
\]
For \(U>1.8\), use \(V\le .4R<.8\) in the circle equation.

If \(z<0\), then \(T>1.963\). The inequality
\(\omega'\le.9\omega^2\) follows from
\[
\begin{split}
&.9(1.963)(.963+s^2/2)^2-N(s)\\
&\quad=1.2383828123-2.7563s+1.3013321s^2+.441675s^4>0
\qquad(0\le s\le.645).
\end{split}
\tag{35}
\]
Again its derivative is increasing and negative at the right endpoint,
where it is less than \(-.60\); its endpoint value exceeds \(.078\).
Since \(V/U\) increases by (13), its value after \(z=0\) exceeds
\(z_0>.3992\). Also \(U>1.399,\ \omega>.532\). Therefore
\[
\begin{split}
G''&>\omega^2(E-.9H)\\
&>(.532)^2(1.399)
 \left[(.51554-.9(1.19909))
       +(1.19909+.9(.51554))(.3992)\right]\\
&>.03969>.02.
\end{split}
\tag{36}
\]
This proves the asserted uniform curvature, with no angle subdivision
other than the sign in its exact contact formula.

### 4.2 The value at the intrinsic join

At \(u_d\), the target is axial and the source diagonal. From (10),
(14), and \(\pi/2>1.570795\),
\[
\begin{split}
 G(u_d)
 &>1.570795+.1072+.6618
       -(.78941)(.899214065110)
       -(.51554)(1.414575672)\\
 &=\frac{9006760829186349}{10000000000000000}>.900676.
\end{split}
\tag{37}
\]
At this endpoint,
\[
 G'(u_d)=1-(tX_0-P/2)
             \left(1-\frac{\cos u_d}
                               {X_0\cos u_d+\tfrac12\sin u_d}\right)
 >-.0028.
\tag{38}
\]
For a fully rational comparison in (38), use
\[
 .994248<\cos u_d<.99426,\qquad \sin u_d<.107095
\]
from (10), together with (14). The resulting lower bound is greater
than \(-.002661\).
Taylor's formula and \(G''>.02\) now give
\[
 G(u)>.900676-\frac{.0028^2}{2(.02)}
       =.90048>.9004.
\tag{39}
\]
This proves (30).

## 5. Case I before the source reaches its diagonal

For the axial reference \(F\) from (11), (18) gives
\[
 F''>
 \frac{.88074Q(.908)^2}{1.4^3}
 -\frac12\left(.09133+\frac{.88074(1.5)}{1.29}\right)
 >.47.
\tag{40}
\]
The exact fixed-point comparisons are
\[
 F(0)>.89835,\qquad F'(0)>-.02,\qquad
 F(.09)>.8997,\qquad F'(.09)>.05.
\tag{41}
\]
The first two imply, throughout the axial angle range,
\[
 F(u)>.89835-\frac{.02^2}{2(.47)}>.897924>.8978.
\tag{42}
\]
The last two and (40) show that \(F(u)>.8997\) for \(u\ge.09\).
Using (25) and (29), every feasible contact in
\(.09\le u\le u_d\) therefore satisfies
\[
 C>.8997-\frac{.071^2}{2(1.52)}>.89804>.8978.
\tag{43}
\]

It remains to rule out an unaccounted interior minimum at a smaller
angle. This uses the exact angular derivative, not a grid.
At a stationary point in \(B\), equation (5) says
\[
 L=\frac{tU-PV}{Uk+Vs}.
\]
Since \(a_u=k-(Uk+Vs)\), its angular derivative is
\[
 C_u=1-(tU-PV)\left(1-\frac{k}{Uk+Vs}\right).
\tag{44}
\]
For fixed \(0\le u\le u_d\), the subtracted expression in (44)
decreases with \(B\). Indeed \(tU-PV\) decreases, is positive, and
\[
 \frac{d}{dB}(Uk+Vs)=s-kV/U<0,
\]
because \(Vk-Us>.5(.99417)-1.915(.108)>0\).
Thus at any such stationary point
\[
 C_u\ge\Omega(u):=
 1-(tX_0-P/2)
       \left(1-\frac1{X_0+\tfrac12\tan u}\right).
\tag{45}
\]
The function \(\Omega\) is strictly decreasing. Its single zero \(u_s\)
satisfies
\[
 .09<u_s<.1072<u_d,
\tag{46}
\]
because direct fixed-point evaluation gives
\(\Omega(.09)>.00196\) and \(\Omega(.1072)<-.00262\).
This zero identifies the only possible change in the sign of the
interior angular derivative.

Apply the compact minimum principle on \(0\le u\le u_s\).
An interior stationary point with \(u<u_s\) has \(C_u>0\), so cannot be
a minimum. The upper \(B\)-boundary on this range is \(a=a_0\);
indeed the formal value of \(a\) at \(B=d\) exceeds
\(.5+1.399(.99417)-.4(.108)>a_0\).
There (5) is positive, since
\[
 L=.09133+.88074(2X_0)>3.46,\qquad a_B>.99417.
\]
It therefore cannot supply an additional minimum.
The lower \(B\)-boundary is the axial curve, covered by (42).
At \(u=0\), \(J(0)>.05\), and convexity again puts the minimum at that
axial boundary. Finally, the endpoint \(u=u_s>.09\) is covered by (43).
Every possible minimum is accounted for. Together with (31), (42),
and (43), this proves case \({\cal I}\) on its full angle half.

## 6. Original-axis coverage and strictness

Every reduction used its stipulated original separating axis. Reflection
and reversal in case \({\cal III}\) preserve that separator and the
corrected cost exactly. Axis ties are included because the proof requires
only the weak inequality (3); all strict reserves arise later from the
displayed arithmetic. The result is the complete three-family theorem
stated at the beginning.

This theorem, together with the full opposite-sign role-5 theorem, is a
component of the short-word proof. It does not by itself assert the
remaining short-word role or radial families.


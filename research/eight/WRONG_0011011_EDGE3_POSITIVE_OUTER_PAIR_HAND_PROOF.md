# Wrong word 0011011: the whole positive outer edge-3 quarter row

## Theorem

For edge 3 with two positive outer states, every retained separating axis
and every angle
\[
 p-.7\le\phi\le p+.7,\qquad p=\pi/2,
\]
imply
\[
 C=\phi+R(b)-J(B)>.89777>\gamma,\qquad \gamma=.89765,
\tag{1}
\]
where, at \(Q=9789/2500\),
\[
 \begin{aligned}
 a(b)&=\sqrt{Q-(b+.5)^2}-.5,\qquad A=a(B),\\
 R(b)&=-.01025a(b)+.16031b+.63457a(b)b,\\
 J(B)&=.03965+3.85510B-1.49748B^2-1.89442A B.
 \end{aligned}
\tag{2}
\]
Every decimal denotes an exact rational. These are exactly the positive
outer labels of roles 3 and 4. The own-frame centers are \((a,-b)\)
and \((A,-B)\). Reflected reversal supplies the corresponding edge-5 row.

This proof covers all four retained axes and the complete angle interval.
Its companion performs 147 fixed rational comparisons. The only finite
tables are four scalar support intervals and four contact-derivative
intervals; there is no adaptive cover or sampled minimum. Two explicit
one-variable facts about the same target label are reused from the
already proved mixed-row notes.

Put
\[
 d=\sqrt{Q/2}-.5,\quad a_0=\sqrt{Q-.25}-.5,\quad
 B_1=\sqrt{Q-2.25}-.5,\quad \ell=p-.7.
\tag{3}
\]
Then \(0\le b,B\le d\), \(.899<d<.9\), and
\(1.4145<a_0<1.415\).

## 1. Derivatives, chords, and a contact principle

For an outer coordinate, write
\[
 U=a+.5,\quad V=b+.5,\quad r=V/U,\quad
 r'=Q/U^3,\quad r''=3QV/U^5.
\tag{4}
\]
In particular \(a'=-r\), \(.261<r\le1\), \(r'<1.431\), and
\(r''/r'<2.15\).

For the source label, put
\(p_0=-.01025,\ q_0=.16031,\ t_0=.63457\).
Then
\[
 \begin{aligned}
 R'&=-p_0r+q_0+t_0(a-br),\\
 R''&=-2t_0r-(p_0+t_0b)r',\\
 R'''&=-\frac{3Q\{t_0Q+(p_0-t_0/2)V\}}{U^5}<0.
 \end{aligned}
\tag{5}
\]
The numerator in braces is positive even at \(V=1.4\).
Since \(R''(0)<0\), the first derivative decreases and
\[
 .170<R'<1.061,\quad R'(0)>1.0424,\quad
 R''(.1)<-.434,\quad R'(.6)>.639.
\tag{6}
\]
Also \(R(0)>-.01450\). Concavity supplies the two lower chords
\[
 \begin{array}{ll}
 R(b)\ge R(0)+.736b,&0\le b\le d,\\
 R(b)\ge R(0)+.98b,&0\le b\le .35.
 \end{array}
\tag{7}
\]
Their slopes are smaller than the exact endpoint secant slopes.

For \(k=1.89442\),
\[
 \begin{aligned}
 J'&=3.85510-2.99496B-k(A-Br),\\
 J''&=-2.99496+k(2r+Br'),\\
 J'''&=k(3r'+Br'')>0.
 \end{aligned}
\tag{8}
\]
Here and below \(r,r',r''\) in a target expression are evaluated at \(B\).
The fixed middle and endpoint checks give
\[
 .622<J'<1.176,\quad J(d)<.763568,\quad J''(B_1)>2,
 \quad J''(.5)<0.
\tag{9}
\]
For the lower bound, use
\(J'(.5)>.624,\ J''(.5)>-.032,\ J''(.55)>0\).
The possible decrease between .5 and .55 is less than .0016.
Convexity of \(J'\) gives its upper bound from the two outer endpoints.

We reuse the global affine bound
\[
 J(B)<.108+.73B.
\tag{10}
\]
It is proved independently of any SAT condition in Section 1 of
**WRONG_0011011_EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md**:
strong concavity through .5 and the convex derivative thereafter give
the two required endpoint reductions.

Set \(s=\sin\phi,c=\cos\phi,\ W=(1+s+|c|)/2\). The four retained axes are
\[
\begin{array}{c|l}
1&b+As-Bc\ge W,\\
2&-a\cos\phi+bs+A\ge W,\\
3&as+bc-B\ge W,\\
4&a-Ac-Bs\ge W.
\end{array}
\tag{11}
\]
Because \(R\) increases and \(J\) increases, all least-source and
greatest-target reductions made below have the required cost direction.

A useful principle is that a differentiable function with concave
derivative and positive derivative at its left endpoint has its minimum
at an endpoint. Its derivative can first be positive and then negative,
without a subsequent negative-to-positive crossing.

## 2. Alignment and lower axis-1 contacts

Below the quarter turn, least-source contact for axis 1 is
\[
 b=\max(0,b_*(B,\phi)),\qquad
 b_*=W-As+Bc.
\tag{12}
\]
On contact,
\[
 b_B=r s+c>0,\quad b_{BB}=r's,\quad b_{BBB}=r''s.
\]
Writing \(F(B)=\phi+R(b_*)-J(B)\),
\[
 F'''=R'''b_B^3+3R''b_Br's+R'r''s-J'''<0.
\tag{13}
\]
Indeed the first two terms are negative and the last two are at most
\[
 r'\{1.061(2.15)-3k\}<0.
\]
Thus \(F'\) is concave on every feasible contact interval.

At \(\phi=p\), axes 1 and 2 coincide and require \(b+A\ge1\).
If \(A\ge1\), take \(b=0\); its cost decreases up to \(B=B_1\).
For \(B_1\le B\le d\), contact is \(b=1-A\).
At \(B=B_1\),
\[
 F'=R'(0)r(B_1)-J'(B_1)>0.
\]
The principle after (11), using (13), reduces alignment to
\[
 \begin{aligned}
 p+R(0)-J(B_1)&>.9025,\\
 p+R(1-d)-J(d)&>.8977886.
 \end{aligned}
\tag{14}
\]

### 2.1. Lower angles \(\ell\le\phi\le1.3\): small source coordinate

First suppose \(b\le .35\) and \(B\le .5\).
Use the second chord in (7). The target is concave through .5, so the
following four upper tangents are valid:
\[
\begin{array}{c|r|r|r}
 \phi\text{ interval}&\text{tangent point}&q&k_0\\ \hline
[\ell,1]&.172&.878955401&.063716016\\
[1,1.1]&.209&.828547105&.073303502\\
[1.1,1.2]&.252&.776312419&.085318707\\
[1.2,1.3]&.302&.724514843&.099625668
\end{array}
\tag{15}
\]
The table is the same target-only tangent table used in the positive
core-to-positive outer theorem. Each slope and intercept is rounded
upward; the companion checks those two inequalities afresh.

Subtract \(g=.98\) times the axis-1 SAT margin from
\(\phi+R(0)+gb-k_0-qB\). The source coordinate cancels.
Minimizing the remaining linear functional on the full target circle gives
\[
 F_{q,k_0}(\phi)=
 \phi+R(0)-k_0+\frac{g+q}{2}+g\sin\phi
 -\sqrt Q\,\sqrt{g^2+q^2-2gq\cos\phi}.
\tag{16}
\]
This remains valid when the relaxed source contact is negative.
If \(N^2=g^2+q^2-2gq\cos\phi\), the identity
\[
 N''+N/4=(g^2-q^2)^2/(4N^3)\ge0
\]
and \(g\sin\ell>\sqrt Q\,\sqrt{g^2+.879^2}/4\) show
\(F_{q,k_0}''<0\). The eight interval endpoints in (15) all exceed .9013.

If instead \(B>.5\) while \(b\le .35\), contact has \(B<.78\).
Its derivative is bounded below by
\[
 G(B,\phi)=R'(.35)(r(B)\sin\phi+\cos\phi)-J'(B).
\tag{17}
\]
This is concave separately in \(B\) and \(\phi\), by the same inequality
used in (13). Its four corners on
\([.5,.78]\times[\ell,1.3]\) are positive.
Thus decreasing \(B\) decreases the cost until \(B=.5\).
The source contact remains nonnegative:
\(b_*(.5,1.3)>.08\), and \(b_*(.5,\phi)\) decreases with \(\phi\).
The preceding support proof therefore covers this case too.

### 2.2. The same lower angles: source coordinate \(b\ge .35\)

The target coordinate \(B_{.35}(\phi)\) at the source cut \(b=.35\)
increases with \(\phi\). An explicit expression is
\[
 \begin{aligned}
 Z&=.15+\sin\phi,&Y&=\sqrt{Q-Z^2},\\
 U&=Z\sin\phi+Y\cos\phi,&
 V&=Y\sin\phi-Z\cos\phi,\qquad B_{.35}=V-.5.
 \end{aligned}
\tag{18}
\]
Here \(B_{.35}'=U(1-\cos\phi/Y)>0\).
The four exact enclosing rectangles are
\[
\begin{array}{c|c}
 \phi\text{ interval}&B_{.35}\text{ enclosure}\\ \hline
[\ell,.95]&[.252,.346]\\
[.95,1.05]&[.345,.466]\\
[1.05,1.15]&[.465,.590]\\
[1.15,1.3]&[.589,.779]
\end{array}
\tag{19}
\]
The four corners of (17) are positive in each rectangle.
Hence \(F'\) is positive at the source cut. Its concavity (13)
reduces every remaining contact to \(b=.35\), \(b=d\), or \(B=d\).
The first has just been covered. Sections 3.1–3.2 cover the two diagonals.

### 2.3. Later lower angles \(1.3\le\phi\le p\)

The least feasible target contact starts at \(b=0\), on
\[
 \begin{aligned}
 Z&=.5+\sin\phi,&Y&=\sqrt{Q-Z^2},\\
 U&=Z\sin\phi+Y\cos\phi,&
 V&=Y\sin\phi-Z\cos\phi,\qquad B_z=V-.5.
 \end{aligned}
\tag{20}
\]
Section 3.2 of
**WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md**
proves, on this entire zero curve,
\[
 1.0424(r\sin\phi+\cos\phi)-J'(B_z)>0,\qquad
 \phi-.01449-J(B_z)>.9025.
\tag{21}
\]
These are target-geometry statements; the source radius does not enter
axis 1 when \(b=0\).
Since \(R'(0)>1.0424\) and \(R(0)>-.01450\), our contact derivative
is positive and our zero cost exceeds .90249.
Use (13) and the endpoint principle again.
For \(B<B_z\), \(b=0\) and the cost decreases with \(B\).
For \(B\ge B_z\), only the zero endpoint and \(B=d\) remain.
The latter has \(b\le b_*(d,1.3)<.5<d\), so no missing source-diagonal
exit occurs in this later range.

## 3. Two complete diagonal contact curves

### 3.1. Source diagonal \(b=d\)

Set \(k_0=.5-d<0\) and use (18) with \(Z=k_0+\sin\phi\).
Its target \(B(\phi)\) increases from \(B(\ell)>.75\) to \(d\)
at a unique angle \(\phi_*\), with
\[
 1.014<\phi_*<1.015.
\tag{22}
\]
If \(f=1-\cos\phi/Y\), differentiation gives
\[
 B'=Uf,\qquad B''=-Vf^2+Uf',\qquad
 f'=\frac{\sin\phi(Q-1-k_0^2)-k_0(1+\sin^2\phi)}{Y^3}>0.
\tag{23}
\]
On the physical curve,
\[
 B'>1.399(.668)>.93,\quad f<.73,\quad
 B''>-1.4(.73)^2,\quad J''(B)>1.6.
\]
Therefore
\[
 \{\phi+R(d)-J(B(\phi))\}''
 <-1.6(.93)^2+1.176(1.4)(.73)^2<0.
\tag{24}
\]
The two endpoint costs satisfy
\[
 \begin{aligned}
 \ell+R(d)-J(B(\ell))&>.8977888,\\
 \phi_*+R(d)-J(d)&>1.014+R(d)-J(d)>.8984.
 \end{aligned}
\tag{25}
\]
This proves the whole source-diagonal curve.

### 3.2. Target diagonal \(B=d\)

Its source coordinate is
\[
 b(\phi)=.5+(.5-d)\sin\phi+(.5+d)\cos\phi,
 \qquad \phi_*\le\phi\le p.
\tag{26}
\]
It decreases from \(d\) to \(1-d>.1\), with
\[
 b''=.5-b\le.4,\qquad |b'|>1.399\sin(1.014).
\]
Since \(R''(b)<-.434\) and \(R'<1.061\),
\[
 \{\phi+R(b(\phi))-J(d)\}''
 <-.434\{1.399\sin(1.014)\}^2+1.061(.4)<0.
\tag{27}
\]
Its minimum is at \(\phi_*\) or \(p\), covered by (25) and (14).
This completes lower axis 1.

## 4. Axis 2 below the quarter turn

For fixed target \(A\), the source projection
\(b\sin\phi-a(b)\cos\phi\) increases in \(b\).
The contact can be written explicitly. Put \(P=A-.5\) and
\[
 \begin{aligned}
 Z&=\sin\phi-P,&Y&=\sqrt{Q-Z^2},\\
 U&=Y\sin\phi-Z\cos\phi,&
 V&=Y\cos\phi+Z\sin\phi,\qquad b=V-.5,\\
 f&=1-\cos\phi/Y.
 \end{aligned}
\tag{28}
\]
Then
\[
 b_\phi=-Uf<0,\qquad b_{\phi\phi}=-Vf^2-Uf'<0.
\tag{29}
\]
Indeed \(Y>\cos\phi\), since
\(Q-1-P^2+2P\sin\phi>0\), and
\[
 f'=\frac{\sin\phi(Q-1-P^2)+P(1+\sin^2\phi)}{Y^3}>0.
\]
Thus the contact cost is strictly concave in \(\phi\):
\(R''b_\phi^2+R'b_{\phi\phi}<0\).
At a fixed target its feasible contact angles form an interval.
The only possible endpoints are \(\phi=\ell,\ \phi=p,\ b=0,\ b=d\).
On a source-zero inactive interval the cost increases with \(\phi\),
so it introduces no further minimum.

At \(\phi=\ell\), use the whole-source chord in (7), \(a\ge d\), and (10).
Subtract \((.736/\sin\phi)\) times the SAT margin.
The full-circle target bound is
\[
 \begin{aligned}
 F_0(\phi)=&\ \phi+R(0)-.108+\frac{.736+.73}{2}\\
 &+\frac{.736\{1+(d+.5)\cos\phi\}
    -\sqrt Q\,\sqrt{.736^2+.73^2\sin^2\phi}}{\sin\phi}.
 \end{aligned}
\tag{30}
\]
The single endpoint value \(F_0(\ell)>.9209\) closes this boundary.
Alignment is (14).

At \(b=0\), the target requirement is
\[
 A_{\rm req}=.5+.5\sin\phi+(a_0+.5)\cos\phi.
\]
Feasibility forces \(\phi>1.3\).
The target coordinate increases with speed
\[
 B'=\{(a_0+.5)\sin\phi-.5\cos\phi\}/r>1.7.
\]
Together with \(J'>.622\), this makes the zero-source cost strictly
decreasing. Its minimum is the quarter endpoint in (14).

At \(b=d\), the target primary coordinate is the right side of (26).
The target coordinate increases from \(B(\ell)>.66\) to \(d\), and
the final angle is the same \(\phi_*\) from (22).
Write
\[
 v=(d-.5)\cos\phi+(d+.5)\sin\phi>1.32.
\]
Here \(B'=v/r\). On \(B\ge .66\),
\[
 J'/r>.95.
\tag{31}
\]
To verify (31), the ratio and its derivative numerator
\(N=J''r-J'r'\) are positive as required at .66.
Moreover
\[
 N'=J'''r-J'r''
 \ge r'\{3k(.7)-1.176(2.15)\}>0,
\]
because \(r(.66)>.7\).
Consequently the source-diagonal cost decreases:
\(1-J'B'<1-.95(1.32)<0\).
Its minimum at \(\phi_*\) is covered by (25).
All lower axis-2 endpoints are now proved.

## 5. Both first axes above the quarter turn

The direct bound
\[
 C\ge1.676+R(0)-J(d)>.8979
\tag{32}
\]
closes every \(\phi\ge1.676\).
Since \(1.676<p+.11\), it suffices to consider
\(x=\phi-p\in[0,.11]\).

### 5.1. Axis 1

Its least source coordinate is the nonnegative part of
\[
 b=.5-(A-.5)\cos x-(B-.5)\sin x.
\tag{33}
\]
The derivative in \(B\) is \(r\cos x-\sin x>0\).
The source-zero target \(B_z\) lies in \([B_1,d]\), and
every active source has \(b\le1-d<.101\).
For the contact cost as a function of \(B\),
\[
 F_{BB}=R''b_B^2+R'r'\cos x-J''
 <1.061(1.431)-2<0.
\tag{34}
\]
Thus only \(b=0\) and \(B=d\) remain.
The diagonal contact has \(b_x>-.4\), so its cost increases.
The zero contact has
\[
 B_z'\le\frac{.4}{r(B_1)\cos(.11)-\sin(.11)}<.54,
\]
so its cost increases too. Both minima are at alignment (14).
For \(B<B_z\), the inactive source-zero cost decreases up to \(B_z\),
which proves complete coverage.

### 5.2. Axis 2: target-coordinate concavity

The source projection \(a\sin x+b\cos x\) increases with \(b\).
At \(b=.101\) every target is already feasible: the margin is positive
at \(x=0\), and its derivative in \(x\) is positive.
Hence every least active source has \(b<.101\).

Let
\[
 D=\cos x-r_s\sin x>.958,
\]
where \(r_s\) belongs to the source. The zero-source target begins at
\(B_1\) and increases. On the active contact,
\[
 b_B=r_t/D<1.044,\qquad
 b_{BB}=\{r_t'+r_s'\sin x\,b_B^2\}/D<1.58.
\tag{35}
\]
These follow from \(r_s'<.585,\ r_t'<1.431\).
Since \(B\ge B_z\ge B_1\),
\[
 F_{BB}=R''b_B^2+R'b_{BB}-J''
 <1.061(1.58)-2<0.
\tag{36}
\]
Again only the source-zero and target-diagonal boundaries remain.

### 5.3. Axis 2: the two endpoint curves

At \(B=d\), write
\[
 M(b,x)=d-.5+(a-.5)\sin x+(b-.5)\cos x=0.
\tag{37}
\]
The source coordinate decreases with \(x\), and \(|b_x|<1.02\).
The implicit second derivative has numerator
\[
 -D b_{xx}=M_{xx}+2M_{bx}b_x+M_{bb}b_x^2
 >.399-.585(.11)(1.02)^2>0.
\tag{38}
\]
Indeed \(M_{xx}=d-.5\), the middle term is positive, and
\(M_{bb}=-r_s'\sin x\).
Thus \(b_{xx}<0\), and the cost along this curve is strictly concave.
Its active interval ends at \(b=0,\ x=x_z\), where
\[
 .107<x_z<.108
\]
by the two signs of
\(d-.5+(a_0-.5)\sin x-.5\cos x\).
Its endpoints are alignment and
\[
 p+x_z+R(0)-J(d)>.8997.
\tag{39}
\]

The source-zero boundary has
\[
 A_{\rm req}=.5+.5\cos x-(a_0-.5)\sin x.
\]
It runs from \(B_1\) to \(d\) over \(0\le x\le x_z\).
If \(m=A-.5,\ v=.5\sin x+(a_0-.5)\cos x\), then
\[
 B'=v/r>.908,\qquad
 B''=Um/V-Qv^2/V^3>-1.32.
\tag{40}
\]
For the second bound, use
\[
 Um/V>1.399(.399)/1.4,\quad v<.97,\quad V>1.29.
\]
Therefore its cost is concave:
\[
 \{p+x+R(0)-J(B(x))\}''
 <-2(.908)^2+1.176(1.32)<0.
\tag{41}
\]
Its endpoints are the zero aligned contact and (39).
For \(x\ge x_z\), every target admits the inactive source \(b=0\);
the minimum is at \(B=d\) and increases with \(x\).
This closes both upper axes.

## 6. Axis 3

### 6.1. The whole lower half

The SAT inequality gives
\[
 B\le a\sin\phi+b\cos\phi-W\le a_0-1<.415.
\]
The final inequality uses the outer center norm bound, proved from its
circle equation and the concavity of \(a+b\).
Since \(J''<0\) through .5 and \(J'(0)<1.176\),
\[
 J(B)\le.03965+1.176B.
\]
After this substitution, the source part is
\[
 R(b)-j a(b)\sin\phi-jb\cos\phi,\qquad j=1.176.
\]
Its derivative is \(R'+jr\sin\phi-j\cos\phi>0\) on the entire arc.
For \(b\le .6\), use \(R'>.639,\ r>.261\); for \(b\ge .6\), use
\(R'>.170,\ r>.668\).
In both cases \(\sin\phi>.764,\ \cos\phi<.645\) make the lower bound
strictly positive. Hence the relaxed source minimum is at \(b=0\),
even if that endpoint itself is not feasible.

The resulting scalar is
\[
 F_3(\phi)=\phi+R(0)-.03965+j/2+(j/2)\cos\phi
                       -j(a_0-.5)\sin\phi.
\tag{42}
\]
Its second derivative increases and is greater than .44 at \(\ell\).
At the rational reference \(\phi=1.04\),
\[
 F_3>.9439,\qquad |F_3'|<.052.
\]
Completing a square gives
\[
 F_3>.9439-\frac{(.052)^2}{.88}>.9408.
\tag{43}
\]

### 6.2. The upper half

For \(0\le x\le .11\), axis 3 gives directly
\(B\le a_0-1<.415\). Thus
\[
 C\ge p+R(0)-J(.415)>1.16.
\]
The later upper angles are already covered by (32).

## 7. Axis 4

On the lower half, a necessary condition is
\[
 a_0-.5-.5\sin\phi-(d+.5)\cos\phi\ge0.
\]
Its left side increases with \(\phi\), and is still negative at 1.2.
Therefore this axis requires \(\phi>1.2\).
The target has the necessary cap
\[
 B\le (a_0-.5)\csc\phi-.5-(d+.5)\cot\phi,
\tag{44}
\]
which increases throughout the lower interval.
At 1.4 it is less than .187, and at \(p\) it is less than .415.
The two angle intervals consequently give
\[
 \begin{array}{ll}
 1.2\le\phi\le1.4:&C>1.2+R(0)-J(.187)>.957,\\
 1.4\le\phi\le p:&C>1.4+R(0)-J(.415)>.990.
 \end{array}
\tag{45}
\]

On the upper strip \(0\le x\le .11\), use \(a,A\le a_0\) in the SAT
inequality to get
\[
 B\le(a_0-.5)(\sec x+\tan x)-.5<.523.
\]
Thus \(C\ge p+R(0)-J(.523)>1.09\).
All later angles are closed by (32).

## 8. Arithmetic and coverage

Every bound used above is continuous on its stated closed interval.
The contact flows either remain on the declared outer arcs or terminate
at one of the explicitly covered coordinate endpoints. The source-zero
and inactive regions are included; no strict-coordinate assumption
discards a boundary.

The 147 comparisons in
verify_wrong_0011011_edge3_positive_outer_pair.js use exact integer
fractions, fixed Taylor bounds, an exact Machin enclosure for \(\pi\),
and rational radical brackets verified by integer squares.
The four support rows (15) use endpoint concavity.
The four contact rows (19) use concavity in each variable, so their
sixteen corners cover the full rectangles analytically.
All remaining comparisons are the displayed global derivative,
endpoint, or reference-point inequalities.

The four axes in (11), their lower and upper halves, and every feasible
boundary are now covered. Their smallest displayed endpoint reserves
are (14) and (25), both strictly above .89777. This proves (1).


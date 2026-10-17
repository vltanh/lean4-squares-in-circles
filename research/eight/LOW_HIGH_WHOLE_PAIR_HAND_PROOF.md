# The entire low/high frame-pair entry by hand

This proves the L/H entry **.8833** in the four-type frame table, for both ordered types, all four sign pairs, and every retained separating axis. It uses the whole type arcs and the already proved center gap \(\delta>.76\); it does not assume frame concentration.

All terminating decimals in this note are exact rational numbers. The argument consists of continuous contact deformations, derivative inequalities, circle support bounds, and six explicit positive polynomials. The optional companion JavaScript file checks the printed rational comparisons; no search, mesh, numerical minimizer, or subdivision certificate is a premise.

The three previously proved delicate strips are used with their stated hypotheses:

- [LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md](LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md);
- [LOW_HIGH_PARALLEL_STRIP_HAND_PROOF.md](LOW_HIGH_PARALLEL_STRIP_HAND_PROOF.md);
- [LOW_HIGH_QUARTER_STRIP_HAND_REDUCTION.md](LOW_HIGH_QUARTER_STRIP_HAND_REDUCTION.md).

The existing high-positive/low-positive interval \([.08,.3]\) is supplied by [HIGH_LOW_NONALIGNED_SHORT_HAND_PROOF.md](HIGH_LOW_NONALIGNED_SHORT_HAND_PROOF.md) and its support formula. Section 8 below extends that explicit polynomial argument to \(.77\).

## 1. Constants, domains, and the quantity to bound

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 \mu=.403875,\quad q=1.089065,\quad
 k=.569472,\quad v=.390886,\quad K=k+v=.960358,
 \quad \gamma=.8833,\quad\beta=.18.
\]
Write
\[
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\qquad
 r(b)=\frac{b+1/2}{a(b)+1/2},\qquad
 c=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2.
\]
Then
\[
 a'=-r,\qquad r'=\frac{Q}{(a+1/2)^3}>0.                 \tag{1}
\]
The L arc is \(0\le b/a\le1/4\); the H arc is \(3/7\le b/a\le1\).
Their cut endpoints are \((a_L,b_L)\), \(b_L=a_L/4\), and
\((a_H,b_H)\), \(b_H=3a_H/7\). The labels are
\[
 L(b)=\mu(a(b)-a_0)+qb,\qquad
 H(b)=\pi/4-k(a(b)-c)+v(b-c).
\]
Equivalently, \(L=c_L+\mu a+qb\), \(H=c_H-ka+vb\), where
\(c_L=-\mu a_0,\ c_H=\pi/4+(k-v)c\). Both labels increase:
\[
 L'=q-\mu r>0,\quad L''=-\mu r'<0,\qquad
 H'=v+kr>0,\quad H''=kr'>0.                             \tag{2}
\]

For source and target signs \(\sigma,\tau\), their own-frame centers
are \((a,-\sigma b)\) and \((A,-\tau B)\). Put
\[
 \phi=\delta+\alpha_t-\alpha_s,\qquad
 h(\phi)=\frac{|\sin\phi|+|\cos\phi|-1}{2},\quad W=1+h.
\]
The desired bound is
\[
 {\cal C}=\phi-\beta h(\phi)+\sigma\ell_s-\tau\ell_t>\gamma.
                                                               \tag{3}
\]
The two retained source separating-axis inequalities are
\[
 \begin{array}{ll}
 f:&\sigma b+A\sin\phi-\tau B\cos\phi\ge W,\\
 e:&a-A\cos\phi-\tau B\sin\phi\ge W.
 \end{array}                                                  \tag{4}
\]
Both orders and both source axes are treated. Reflection followed by
reversal preserves \(\phi,\delta,{\cal C}\), changes the ordered signs
to \((-\tau,-\sigma)\), and exchanges target and source axes. Thus (4)
also covers all retained target axes.

For the primary axis \(e\), its hypothesis is independent of \(\sigma\).
Because the source labels are nonnegative, it suffices to prove the
lower cost with source sign \(-\). This also proves source sign \(+\).

## 2. Rational bounds and common reductions

Squaring the proposed endpoints in the circle equation gives
\[
\begin{array}{c|c}
R&(1.978787507,\ 1.978787508)\\
c&(.899214065,\ .899214066)\\
a_0&(1.414575670,\ 1.414575672)\\
a_L&(1.298747247,\ 1.298747249)\\
a_H&(1.199256060,\ 1.199256062).
\end{array}                                                  \tag{5}
\]
We use \(3.14159<\pi<355/113\). The lower estimate follows from the
Machin calculation in the aligned-contact note. Substitution in the
labels and (1) gives
\[
\begin{gathered}
 0\le L<.30683,\qquad .46394<H\le\pi/4,\\
 .26<r_L<.46,\quad r_L'<.675,\qquad
 .596<r_H\le1,\quad H'>.73,\quad H''>.453,\\
 H'\le K,\qquad 0\le\beta h<.0378.                         \tag{6}
\end{gathered}
\]
For example \(H''>.453\) follows from \(a_H+1/2<1.7\) and
\(kQ>.453(1.7)^3\). The width bound follows from \(\sqrt2<1.42\).

The alternating arctangent sum
\(.25-.25^3/3+.25^5/5<.246\), and \(\pi/4<.786\), imply
\[
 \phi>.76-.246-.786=-.272.                               \tag{7}
\]
For \(-.272<\phi\le0\), the secondary axis can separate only in the
sign case \((\sigma,\tau)=(+,-)\). This follows directly from (4),
not from the center-gap hypothesis alone. For H/L with signs \((+,+)\),
its projection is at most the source transverse coordinate \(b\le c<1\).
For L/H with signs \((-,-)\), it is at most the target transverse
coordinate \(B\le c<1\). The case \((-,+)\) has nonpositive projection.
For H as source and L as target, the negative-source \(f\) axis is
impossible at every angle: its separating projection is at most the
target center radius minus \(b_H\), which is less than
\(1.415-.513<1\). For both ordered types, the primary axis is
impossible when \(-.272<\phi\le0\). Upper bounds for its projection are
\[
 1.2-1.298(1-.272^2/2)+.325(.272)<1,
\quad
 1.415-.899(1-.272^2/2)+.9(.272)<1.                       \tag{8}
\]
Both bounds use \(|\sin\phi|\), and hold for either target sign.

The aligned-contact note proves, with \(b_0=1-c\),
\[
 F_0=L(b_0)+\pi/4>.88336697765,\qquad
 0<d_0=q-K-\mu r(b_0)<.0001.                            \tag{9}
\]
It proves the parallel opposite-sign contact cost at least \(F_0\),
and the quarter positive-sign contact cost greater than
\(F_0-2d_0^2>\gamma\). The two cited strip lemmas extend these
respective bounds to \(|\phi|\le.02\) and
\(|\phi-\pi/2|\le.02\), with their stated signs and source \(f\) axis.

Several tails follow at once from (6):
\[
\begin{array}{c|c|c}
\text{cost form}&\text{angle range}&\text{lower bound}\\ \hline
\phi-\beta h+H+L&\phi\ge.46&.46-.0378+.46394\\
\phi-\beta h+H-L&\phi\ge.77&.77-.0378+.46394-.30683\\
\phi-\beta h-L+H&\phi\ge.8&.8-.0378-.30683+.46394\\
\phi-\beta h-L-H&\phi\ge2.02&2.02-.0378-.30683-\pi/4.
\end{array}                                                  \tag{10}
\]
Every displayed lower bound is greater than \(\gamma\).

## 3. A support formula used below

For a label \(\ell_i=c_i+p_i a+q_i b\), subtract \(\lambda\ge0\)
times the appropriate separating margin in (4). This gives
\[
 {\cal C}\ge
 \phi-\beta h+\lambda W+\sigma c_s-\tau c_t
 +\min_s(U_s a+V_s b)+\min_t(U_t A+V_t B),                \tag{11}
\]
where
\[
\begin{array}{c|rrrr}
 &U_s&V_s&U_t&V_t\\ \hline
 f&\sigma p_s&\sigma(q_s-\lambda)&-\tau p_t-\lambda\sin\phi&
                    \tau(\lambda\cos\phi-q_t)\\
 e&\sigma p_s-\lambda&\sigma q_s&-\tau p_t+\lambda\cos\phi&
                    \tau(\lambda\sin\phi-q_t).
\end{array}
\]
On the full circle the support is
\[
 \min(Ua+Vb)\ge-\frac{U+V}{2}-R\sqrt{U^2+V^2}.           \tag{12}
\]
This is just Cauchy–Schwarz after translating the circle center.
On an arc the derivative is \(-Ur+V\). If \(U\ge0\), the function
is concave, so its minimum is at an endpoint. If \(U<0\), it is
convex, so a positive derivative at the first endpoint selects that
endpoint, and a negative derivative at the last selects the last.

For an L source with positive sign on \(f\), fix
\(\lambda=.945\) and \(\epsilon=.00001\). Concavity and the endpoint
comparison \(L(b_L)-.945b_L>-\epsilon\) give the useful uniform bound
\[
 L(b)-.945b\ge-\epsilon.                                \tag{13}
\]
This small loss is included in every use below.

## 4. H source, L target: the secondary axis

The negative H source is impossible by Section 2.

### 4.1. Positive source, positive target

Angles \(\phi\le0\) are impossible. For \(0\le\phi\le.08\), the
\(f\)-margin is at most
\[
 c-\tfrac12+(a_0-\tfrac12)\sin\phi-\tfrac12\cos\phi.
\]
It increases with \(\phi\) and is negative at \(.08\).
The existing nonaligned short proof applies on \([.08,.3]\).
Section 8.3 proves the same support inequality on \([.3,.77]\);
both use \(\lambda=.990906-.28\phi\) and full circles for the two
supports. The tail \(\phi\ge.77\) is (10). This covers the whole regime.

### 4.2. Positive source, negative target: negative angles

Write \(x=\phi\). Decrease the H transverse coordinate to contact
\[
 z=W-A\sin x-B\cos x.
\]
For \(-.272<x<0\), this contact stays above \(b_H\), because its value
at zero is \(1-B\ge1-b_L>.675>b_H\). As \(x\) increases to zero,
\(z\) decreases and remains below its initial value, hence below \(c\).
Put
\[
 P=(A+\tfrac12)\cos x+(\tfrac12-B)\sin x.
\]
Then \(z'=-P\), and
\[
 \frac{d}{dx}\{x-\beta h+H(z)+L(B)\}
 \le1.09-.73\{1.798(1-.272^2/2)-.5(.272)\}<0.            \tag{14}
\]
This deformation reaches the aligned parallel contact with decreasing
cost. Its cost is therefore greater than \(\gamma\), by (9).

### 4.3. The positive-angle contact surface

It remains to treat \(0\le x\le.46\); the tail is (10).
Both labels and both separating projections increase with their
transverse coordinates. The lower corner \(z=b_H,B=0\) is infeasible
throughout this interval. Indeed its required contact height is
\[
 z_0(x)=\tfrac12+\tfrac12\cos x+(\tfrac12-a_0)\sin x,     \tag{15}
\]
which decreases, and \(z_0(.46)>b_H\). Thus decreasing coordinates
reaches contact without increasing cost.

At contact, \(z=W-A(B)\sin x-B\cos x\). With
\[
 D=\cos x-r(B)\sin x>0,\qquad
 F(x,B)=x-\beta h+H(z)+L(B),
\]
one has
\[
 F_B=L'-H'D,\qquad
 F_{BB}=H''D^2+H'r'\sin x-\mu r'.                       \tag{16}
\]
For \(0\le x\le.2\), \(D>.888\), so
\[
 F_{BB}>.453(.888)^2-.675\mu>.08.                       \tag{17}
\]

For \(0\le x\le.11\), let \(B_d(x)\) be the diagonal contact root
\(z=c\), allowing a small extension to negative \(B\). At that root
\(B_d\le b_0\), \(D\le1\), hence
\[
 F_B(x,B_d)\ge q-\mu r(b_0)-K=d_0>0.
\]
Convexity (17) therefore shows that every physical contact has cost
at least \(F(x,B_d(x))\), even where \(B_d(x)<0\).
For \(.11\le x\le.2\), the first feasible low coordinate is \(B=0\):
\(z_0(.11)<c\) and \(z_0(.46)>b_H\). At \(B=0\),
\(F_B\ge L'(0)-K>0\), so (17) selects \(B=0\).
Finally, on \([.2,.46]\), if \(D\le0\) then \(F_B>0\). If \(D>0\),
\[
 F_B\ge q-.46\mu-K(\cos x-.26\sin x)>0.                 \tag{18}
\]
The right side increases on this interval and is positive at \(.2\).
Thus here too the minimum is at \(B=0\).

Only the diagonal scalar on \([0,.11]\) and the axial scalar on
\([.11,.46]\) remain.

### 4.4. The diagonal scalar is concave

The equation defining the extended root is
\[
 A(B_d)\sin x+B_d\cos x=W-c.                            \tag{19}
\]
For \(0\le x\le.11\) it has a unique root in
\([-.003,.101]\). The projection margin increases with \(B\) and
with \(x\) on this rectangle; its value at \((-.003,.11)\) is
negative, and at \((.101,0)\) positive. Throughout it,
\[
 1.385<A<1.416,\quad .259<r<.319,\quad r'<.59.
\]
Set \(P=(A-\tfrac12)\cos x+(\tfrac12-B_d)\sin x\) and
\(D=\cos x-r\sin x\). Implicit differentiation gives
\[
 B_d'=-P/D,\qquad -1.02<B_d'<-.87,
\]
\[
 B_d''=
 \frac{-(c-\tfrac12)+2(r\cos x+\sin x)B_d'
                   +r'\sin x(B_d')^2}{D}<-.77.         \tag{20}
\]
For the last inequality the numerator is at most
\[
 -.399-2(.259)(1-.11^2/2)(.87)
                +.59(.11)(1.02)^2<-.77,
\]
and \(0<D\le1\). Since \(L'>.95\), \(L''<0\), the scalar
\[
 J_d(x)=x-\beta h(x)+\pi/4+L(B_d(x))
\]
satisfies
\[
 J_d''<.09(1.11)-.95(.77)<0.                            \tag{21}
\]
Its value at zero is \(F_0\). At the other endpoint, substituting
the rational brackets in (19) gives
\[
 -.002731159<B_d(.11)<-.002731156,\qquad
 J_d(.11)>.88337.
\]
A concave function lies above the lesser endpoint value. Therefore
\(J_d>\gamma\) on the entire interval.

### 4.5. The normal axial scalar is strongly convex

Let \(F_N(x)=x-\beta h(x)+H(z_0(x))\) on \([.11,.46]\), and put
\[
 P=(a_0-\tfrac12)\cos x+\tfrac12\sin x=-z_0'(x).
\]
Here \(P>.96\), \(0<P'<.398\), \(H''>.453\), and \(H'\le K\).
Consequently
\[
 F_N''=.09(\sin x+\cos x)+H''P^2-H'P'
 >.09+.453(.96)^2-K(.398)>.12.                          \tag{22}
\]
Direct endpoint arithmetic at the single rational reference point
\(x_*=.115\) gives
\[
 F_N(x_*)>.88352,\qquad |F_N'(x_*)|<.001.
\]
Integrating (22) and completing the square yields
\[
 F_N(x)\ge F_N(x_*)+F_N'(x_*)(x-x_*)+.06(x-x_*)^2
 >.88352-\frac{.001^2}{.24}>\gamma.                     \tag{23}
\]
Sections 4.2–4.5 prove the entire opposite-sign H/L secondary regime.

## 5. H source, L target: the primary axis

Use the smaller source label \(-H\), as explained after (4).
For \(0\le\phi\le1.2\), the primary margin is at most
\[
 .7-1.798\cos\phi-.175\sin\phi.
\]
It is convex and negative at both endpoints, hence negative throughout.
Together with (8), feasibility therefore requires \(\phi>1.2\).

Rotate the negative H source frame by \(\pi/2\), transpose its
coordinates, and set \(x=\phi-\pi/2>-.4\).
Its new transverse coordinate \(z=a_{\rm old}\) lies in \([c,a_H]\);
its primary coordinate is \(a(z)=b_{\rm old}\). Define the upper label
\[
 G(z)=\pi/2-H
 =c_U-va(z)+kz,\qquad c_U=\pi/4-(k-v)c.                 \tag{24}
\]
Then
\[
 G(c)=\pi/4,\quad G'=k+vr\ge K,\quad G''=vr'>0.
\]
The potential and width penalty are unchanged. The primary separator
and cost become
\[
 z+A\sin x-\tau B\cos x\ge W,\qquad
 x-\beta h+G(z)-\tau L(B).                             \tag{25}
\]

### 5.1. A common upper axial bound

Use the expression (15) and define
\[
 F_U(x)=x-\beta h(x)+G(z_0(x)),\qquad 0\le x\le.11,
\]
allowing analytic continuation slightly below \(z=c\).
Throughout this interval, \(.79<a(z_0)<.903\),
\(G''>.55,\ G'<1.025,\ P>.9145,\ P'\le.5\). Hence
\[
 F_U''>.09+.55(.9145)^2-1.025(.5)>0.                    \tag{26}
\]
A direct comparison gives \(F_U'(.11)<0\). Its derivative is increasing
and still negative at the right endpoint, so \(F_U\) decreases and
\[
 F_U(x)\ge F_U(.11)>.88353>\gamma.                      \tag{27}
\]

### 5.2. Negative target: the negative-angle deformation

Both labels in (25) now increase. Reduce to contact, decreasing \(z\)
first and then \(B\) if the boundary \(z=c\) is met. The corner
\(z=c,B=0\) is infeasible for \(x<0\), so contact is reached.

At fixed \(B\), contact has \(z=W-A\sin x-B\cos x\).
For \(-.4<x<0\),
\[
 P=(A+\tfrac12)\cos x+(\tfrac12-B)\sin x
 >1.798(.92)-.5(.4)=1.45416.
\]
Thus its cost derivative is at most \(1.09-KP<0\).
Increase \(x\) toward zero. If \(z=c\) is reached first, keep this
boundary fixed and continue contact by decreasing \(B\). Now
\(B'=-P/D\), \(D=\cos x-r\sin x<1+.46(.4)=1.184\), and
\[
 L'P/D>
 \frac{(q-.46\mu)(1.45416)}{1.184}>1.09.                \tag{28}
\]
This second path also decreases cost. It stays above its eventual
low coordinate \(1-c>0\), and never encounters an upper type boundary.
The endpoint at \(x=0\) is the quarter-aligned contact covered by (9).

### 5.3. Negative target: no interior minimum on the remaining contact surface

For \(0\le x\le.108\), reduce to contact by decreasing \(z\), then
\(B\). If the corner \(z=c,B=0\) is reached with slack, decrease \(x\)
until contact; the corner was infeasible at zero, and its cost increases
with \(x\), since \(1-\beta h'\ge.91\).

At contact,
\[
 z=\tfrac12+(\tfrac12-B)\cos x+(\tfrac12-A)\sin x,
 \qquad c\le z\le1,\quad 0\le B\le1-c<.101.             \tag{29}
\]
The last bounds follow because the displayed \(z\) decreases with \(x\)
at fixed \(B\), so \(z\le1-B\). Put
\[
 P=(A-\tfrac12)\cos x+(\tfrac12-B)\sin x,\quad
 D=\cos x-r\sin x,\quad E=r\cos x+\sin x.
\]
On this whole contact region,
\[
\begin{gathered}
 .55<G''<.714,\quad K\le G'<1.025,\quad
 .55<r_L'<.59,\\
 .879<P<.969,\quad .959<D\le1,\quad E>.258.
\end{gathered}
\]
For \(F=x-\beta h+G(z)+L(B)\), direct differentiation gives
\[
\begin{split}
 F_{xx}&=.09(\sin x+\cos x)+G''P^2+G'(\tfrac12-z),\\
 F_{BB}&=G''D^2+G'r'\sin x-\mu r',\\
 F_{xB}&=G''PD+G'E.
\end{split}
\]
The rational bounds imply
\[
 F_{xx}<.4,\qquad .26<F_{BB}<.6,\qquad F_{xB}>.7.
\]
For example their respective bounding expressions are
\[
\begin{split}
 .09(1.108)+.714(.969)^2-K(.399)&<.4,\\
 .714+1.025(.59)(.108)-\mu(.55)&<.6,\\
 .55(.959)^2-\mu(.59)&>.26,\\
 .55(.879)(.959)+K(.258)&>.7.
\end{split}
\]
Therefore
\[
 \det\nabla^2F<.4(.6)-.7^2<0.                           \tag{30}
\]
An interior local minimum would have positive semidefinite Hessian;
(30) excludes it. The compact contact domain has only four boundary
pieces: \(x=0\), \(x=.108\), \(B=0\), and \(z=c\).
The first is (9), the third is (27), and the fourth is the already
proved diagonal scalar (21). The second, and every \(x\ge.108\), obey
\[
 x-\beta h+G+L\ge .91x+\pi/4
 \ge .91(.108)+\pi/4>\gamma,                            \tag{31}
\]
because \(h(x)\le x/2\) for \(x\ge0\) and \(G\ge\pi/4,L\ge0\).
This proves the whole negative-target primary regime.

### 5.4. Positive target: negative angles and the first positive strip

For \(x<0\), reduce \(z\) to the contact
\(z=W-A\sin x+B\cos x\). Its value at zero is \(1+B>c\), so this
deformation and the motion toward zero stay above the lower high boundary.
The contact derivative uses
\[
 P=(A+\tfrac12)\cos x+(\tfrac12+B)\sin x
 >1.798(.92)-.825(.4)=1.32416.
\]
Thus the cost decreases toward zero, since \(1.09-KP<0\).
At zero the function is \(G(1+B)-L(B)\). It increases with \(B\):
\(G'(1)>1.023\), while \(L'<.985\). Its least value is \(F_U(0)\),
already bounded by (27).

For \(0\le x\le.08\), the contact
\(z=W-A\sin x+B\cos x\) stays above \(c\), because its minimum at
\(B=0\) is \(z_0(x)\ge z_0(.08)>c\).
At contact, with \(D_+=\cos x+r\sin x\),
\[
 F_B=G'D_+-L',\qquad
 F_{BB}=G''D_+^2+G'r'\sin x+\mu r'>0.                  \tag{32}
\]
It suffices to check \(F_B\) at \(B=0\). There \(D_+\ge1\) and
\(D_+'<.262\); its derivative in \(x\) is at most
\[
 -.55(.9145)+1.025(.262)<0.
\]
The endpoint comparison \(F_B(.08,0)>0\) therefore proves positivity
throughout. The minimum is \(B=0\), giving (27).

On \([.08,.11]\) use the constant multiplier \(\lambda=K\) in (25),
and on \([.11,.46]\) use \(\lambda=1.005-.407x\).
In both cases \(0<\lambda\le K\), so \(G-\lambda z\) is minimized
at \(z=c\). Use the full-circle support for the low target.
The two polynomial rows of Section 8.1 prove the resulting cost
greater than \(\gamma\). Finally, for \(x\ge.46\),
\[
 x-\beta h+G-L\ge .46-.0378+\pi/4-.30683>\gamma.        \tag{33}
\]
This completes all primary H/L cases.

## 6. L source, H target: the primary axis

Again use the smaller source sign \(-\). With \(\lambda=.7\) or
\(.9\), the source functional \(-L-\lambda a\) decreases along L:
\[
 \frac{d}{db}(-L-\lambda a)=(\mu+\lambda)r-q<0,
\]
because \((\mu+.9)(.46)<q\). Its minimum is the cut endpoint.

### 6.1. Negative target

Angles \(\phi\le0\) are impossible by (8).
For \(0\le\phi\le.6\), the target projection \(-A\cos\phi+B\sin\phi\)
increases along H, so its maximum is the diagonal. The primary margin
is at most
\[
 a_0-\tfrac12-(c+\tfrac12)\cos\phi+(c-\tfrac12)\sin\phi.
\]
This increases with \(\phi\) and is negative at \(.6\).
On \([.6,.8]\), use \(\lambda=.7\), the L cut endpoint, and the
full H circle in (11). If \(E_L=L(b_L)\), the resulting scalar is
\[
\begin{split}
 F(x)={}&x+.09+c_H-E_L-\lambda a_L+\lambda/2+(k-v)/2\\
 &+(\lambda-.09)\sin x-.09\cos x-RN(x),\\
 N^2={}&k^2+v^2+\lambda^2-2\lambda(k\cos x+v\sin x).
\end{split}                                                  \tag{34}
\]
The norm of a fixed vector minus a rotating vector of length \(\lambda\)
is \(\lambda\)-Lipschitz, so \(|N'|\le\lambda\). Hence
\[
 F'\ge1+.61\cos(.8)+.09\sin(.6)-.7R>0.
\]
Its left endpoint exceeds \(1.11099\). The tail \(\phi\ge.8\) is (10).

### 6.2. Positive target

For \(0\le\phi\le\pi/2\), \(A,B>.513\), so the primary margin is at
most
\[
 a_0-\tfrac12-1.013(\sin\phi+\cos\phi)<0.
\]
Together with (8) this forces \(\phi>\pi/2\).
Set \(z=\phi-\pi/2\), \(0\le z\le.45\), and take \(\lambda=.9\).
The target radial coefficient is \(k-\lambda\sin z>0\), so its support
is concave along H and it is enough to check both H endpoints.
For either such endpoint \((A,B)\), the bound is
\[
\begin{split}
 F(z)={}&\pi/2+z-E_L-H(A,B)+(\lambda+\beta)/2-\lambda a_L\\
 &+[d+\lambda B]\cos z+[d-\lambda A]\sin z,
 \qquad d=(\lambda-\beta)/2=.36.
\end{split}                                                  \tag{35}
\]
Both functions are concave on this interval. Indeed \(d+\lambda B>0\),
\(d-\lambda A<0\), and
\[
 (d+\lambda B)\cos(.45)>
       (\lambda A-d)\sin(.45)
\]
for each endpoint. All four endpoint values in (35) exceed \(.9937\).
The tail \(\phi\ge2.02\) is (10), and
\(\pi/2+.45>2.02\), so the intervals overlap.

## 7. L source, H target: the secondary axis

### 7.1. Negative source, negative target

Angles \(\phi\le0\) are impossible. For \(0\le\phi\le.3\), the source
term is at most zero and the target projection is maximal at its diagonal.
Thus the margin is at most
\[
 (c-\tfrac12)(\sin\phi+\cos\phi)-\tfrac12<0;
\]
the expression increases up to \(.3\), where it is still negative.
On \([.3,.8]\) use \(\lambda=1\). The source functional
\(-L+\lambda b\) increases, since
\[
 \lambda-q+\mu r>1-q+.26\mu>0;
\]
its minimum is zero at the L axial endpoint. Use the full H circle.
The scalar and its single positive polynomial are given in Section 8.2.
The tail \(\phi\ge.8\) is (10).

### 7.2. Negative source, positive target

For \(0\le\phi\le1.35\), the projection \(A\sin\phi-B\cos\phi\)
decreases along H, so its maximum is the first H endpoint. The margin is
at most
\[
 -\tfrac12+(a_H-\tfrac12)\sin\phi-(b_H+\tfrac12)\cos\phi,
\]
which increases and is negative at \(1.35\).
Negative angles are impossible. On \([1.35,2.02]\), take \(\lambda=1.02\).
The source functional increases by the same derivative test as above,
and is zero at its axial endpoint. The full H circle gives, with
\[
 N^2=(k-\lambda\sin x)^2+(\lambda\cos x-v)^2,\qquad
 B_\lambda=.09+\lambda/2-c_H-(k-v)/2,
\]
the scalars
\[
 \begin{array}{ll}
 x+B_\lambda+.93\sin x-.09\cos x,
       &1.35\le x\le\pi/2,\\
 x+B_\lambda+.93(\sin x-\cos x),
       &\pi/2\le x\le2.02,
 \end{array}
 \quad\text{each minus }RN.                              \tag{36}
\]

Here and below the useful exact identity for such a rotating norm is
\[
 N''+\frac N4=
 \frac{(k^2+v^2-\lambda^2)^2}{4N^3}\ge0.                 \tag{37}
\]
It follows by differentiating \(N^2\) twice; the norms on the stated
intervals are nonzero. The norm increases after \(1.35\), and
\[
 N(\pi/2)<.597,\qquad N(2.02)<.905.
\]
Consequently the first scalar in (36) is strictly concave because
\[
 .93\sin(1.35)>.09\cos(1.35)+R(.597)/4,
\]
and the second is strictly concave because \(.93>R(.905)/4\).
Their endpoint lower bounds are respectively
\[
 .89708175,\qquad .88524446,\qquad 1.03740259.
\]
Thus the whole interval is above \(\gamma\). The tail is (10).

### 7.3. Positive source, negative target

Use (13), with \(\lambda=.945\), \(\epsilon=.00001\), and
\(d=(\lambda-\beta)/2=.3825\).

For \(-.272<\phi\le-.02\), put \(x=-\phi\).
The target functional decreases along H: its derivative is at most
\[
 K-\lambda(\cos x+\sin x)<0.
\]
To justify taking this maximum at \(r=1\), its coefficient
\(k-\lambda\sin x\) is positive. The displayed inequality holds already
at \(x=.02\), and \(\sin x+\cos x\) increases to \(.272\).
Thus use the target diagonal. The resulting scalar is
\[
 F_-(x)=-x+\pi/4-\epsilon+(\lambda+\beta)/2
 +(d-\lambda c)\cos x+(d+\lambda c)\sin x.              \tag{38}
\]
Since \(d-\lambda c<0\),
\[
 F_-'(x)\ge-1+(d+\lambda c)\cos(.272)>0.
\]
Its minimum is \(F_-(.02)>.88536715\).
The entire parallel strip \(|\phi|\le.02\) is the previously proved
parallel contact deformation.

For \(.02\le x=\phi\le.46\), use the full H circle. The bound is
\[
\begin{split}
 F_+(x)={}&x+.09+\lambda/2+c_H+(k-v)/2-\epsilon\\
         &+(\lambda-.09)(\sin x+\cos x)-RN,\\
 N^2={}&(k+\lambda\sin x)^2+(\lambda\cos x-v)^2.
\end{split}                                                  \tag{39}
\]
This norm increases and \(N(.46)<1.2\). Identity (37), equally valid
with this sign of the sine term, gives
\[
 F_+''\le-.855(\sin x+\cos x)+RN/4
 <-.855+R(1.2)/4<0.
\]
Its endpoint lower bounds are \(.89065261\) and \(1.04853600\).
The tail \(\phi\ge.46\) is (10).

### 7.4. Positive source, positive target

The \(f\)-margin is impossible on \(0\le\phi\le1.1\):
its maximum is bounded by
\[
 b_L-\tfrac12+(a_H-\tfrac12)\sin\phi
                       -(b_H+\tfrac12)\cos\phi<0.
\]
The expression increases and is negative at \(1.1\).
Negative angles are impossible. Continue to use (13).

On \([1.1,1.35]\), the target radial coefficient
\(k-\lambda\sin\phi\) is negative. The target support is convex, and
its derivative at the first endpoint is bounded below by
\[
 \lambda(.596\sin\phi+\cos\phi)-.596k-v.
\]
This decreases with \(\phi\) and is positive at \(1.35\), so that
endpoint minimizes the support. The scalar has the form
\[
 \phi+\text{constant}+A_*\cos\phi+B_*\sin\phi,\quad
 A_*=d+\lambda b_H>0,\quad B_*=d-\lambda a_H<0.
\]
Its first derivative is convex and negative at the right endpoint.
It can therefore have no interior minimum: a zero of the first
derivative, if present, changes from positive to negative.
The two endpoint values exceed \(.92324078\) and \(.90611618\).

On \([1.35,\pi/2-.02]\), use the full H circle. The scalar is the
first expression in (36), with \(.93\) replaced by \(.855\),
\(\lambda=.945\), and with the extra subtraction \(\epsilon\).
Here \(N(\pi/2)<.543\); (37) and
\[
 .855\sin(1.35)>.09\cos(1.35)+R(.543)/4
\]
prove concavity. The endpoint lower bounds are \(.90482983\)
and \(.88535591\).

The entire strip \(|\phi-\pi/2|\le.02\) is the cited quarter-strip
deformation and aligned-contact bound.

For \(e=\phi-\pi/2\in[.02,.108]\), the target functional decreases
along H, since its derivative is at most
\(\lambda(\sin\phi+\cos\phi)-K<\lambda-K<0\).
Use the diagonal. The scalar becomes
\[
 \pi/4+e-\epsilon+(\lambda+\beta)/2
             +(d-\lambda c)(\cos e+\sin e).            \tag{40}
\]
Its derivative is at least \(1-(\lambda c-d)>0\).
The left endpoint exceeds \(.89137840\).
For every \(e\ge.108\),
\[
 {\cal C}\ge\pi/4+e-\beta h(e)\ge\pi/4+.91e>\gamma,
\]
which covers the remaining tail.

## 8. The six new polynomial rows

For \(S_{2j+1}\) and \(C_{2j}\), use the ordinary alternating sine
and cosine Taylor polynomials, truncated at their indicated degrees.
Every interval in this section is within \([0,.8]\), so the alternating
bounds have their usual directions.

To check a polynomial on \([l,u]\), substitute \(x=l+(u-l)y\).
If its power expansion is \(\sum_{j=0}^n a_jy^j\), then its Bernstein
coefficient of index \(r\) is
\[
 b_r=\sum_{j=0}^r a_j\frac{\binom rj}{\binom nj}.        \tag{41}
\]
The polynomial equals
\(\sum_{r=0}^n b_r\binom nr y^r(1-y)^{n-r}\).
These nonnegative basis terms sum to one. Positive lower bounds for all
the \(b_r\) therefore prove a strict inequality on the whole interval.

### 8.1. Upper H positive source, L positive target

Use \(\lambda=K\) on \([.08,.11]\), and
\(\lambda=1.005-.407x\) on \([.11,.46]\), as in Section 5.4.
With the source at its diagonal support and the target enlarged to its
full circle, (11) gives
\[
\begin{split}
 F={}&x+.09+\pi/4+\mu a_0+(\mu+q)/2
       +(.5-c)\lambda\\
    &+(\lambda-.09)\sin x-.09\cos x-RN,\\
 N^2={}&\mu^2+q^2+\lambda^2+
                         2\lambda(\mu\sin x-q\cos x).
\end{split}
\]
Define the explicit polynomials
\[
\begin{split}
 T={}&x+.09+3.14159/4+\mu(1.414575670)+(\mu+q)/2-\gamma\\
     &+(.5-.899214066)\lambda
              +(\lambda-.09)S_7-.09C_8,\\
 V={}&\mu^2+q^2+\lambda^2+2\lambda(\mu S_9-qC_{10}),\\
 P={}&T^2-QV.
\end{split}                                                  \tag{42}
\]
The rational bounds give \(F-\gamma\ge T-RN\), \(N^2\le V\),
and \(T>0\). Thus \(P>0\) proves \(F>\gamma\).

Both polynomials have degree 16. Their Bernstein coefficients, in
increasing index order, are strictly greater than the following positive
integers divided by \(10^8\):

| Interval and multiplier | Lower coefficient numerators |
|---|---|
| \([.08,.11]\), \(\lambda=.960358\) | 36350, 39352, 42034, 44398, 46446, 48180, 49601, 50711, 51512, 52005, 52192, 52075, 51656, 50936, 49916, 48599, 46986 |
| \([.11,.46]\), \(\lambda=1.005-.407x\) | 46907, 23046, 22603, 48835, 104890, 193825, 318639, 482291, 687724, 937892, 1235776, 1584407, 1986883, 2446388, 2966207, 3549739, 4200512 |

The sign \(T>0\) can be checked without another polynomial:
discard its nonnegative sine term, bound \(-.09C_8\ge-.09\),
and use the maximum multiplier in the negative term
\((.5-.899214066)\lambda\). The resulting constant lower bound,
with \(x\) at its left endpoint, is positive in each row.
The affine multiplier stays positive and below \(K\).

### 8.2. L negative source, H negative target

With \(\lambda=1\), the axial source contributes zero and (11) gives
\[
 F=x+.09+\tfrac12+c_H+(k-v)/2
       +.91(\sin x+\cos x)-RN,
\quad
 N^2=k^2+v^2+1+2(k\sin x-v\cos x).
\]
On \([.3,.8]\), put \(c_H^- =3.14159/4+(k-v)(.899214065)\) and
\[
\begin{split}
 T&=x+.09+\tfrac12+c_H^-+(k-v)/2-\gamma+.91(S_7+C_6),\\
 V&=k^2+v^2+1+2(kS_9-vC_6),\qquad P=T^2-QV.
\end{split}                                                  \tag{43}
\]
Again \(T>0\), \(N^2\le V\), and \(F-\gamma\ge T-RN\).
The degree-14 polynomial \(P\) has Bernstein coefficients on
\([.3,.8]\) strictly greater than these integers divided by \(10^8\):
\[
\begin{gathered}
57629693,\ 64106927,\ 70385371,\ 76417041,\ 82155685,\\
87557161,\ 92579804,\ 97184758,\ 101336287,\ 105002051,\\
108153349,\ 110765317,\ 112817092,\ 114291931,\ 115177288.
\end{gathered}
\]
This proves the continuous premise in Section 7.1.

### 8.3. Extending the high-positive/low-positive support bound

On \([.3,.77]\), put \(\lambda=.990906-.28x\), \(w=x-.19\),
and reuse the quartics
\[
\begin{split}
 P_1={}&.7895001401-.1939323304w+.0258329638w^2
                         +.0063465589w^3+.0011353387w^4,\\
 P_2={}&.6048369308+.9594403346w-.2050884018w^2
                         -.0610720222w^3+.0449392223w^4.
\end{split}
\]
This extension uses the explicitly enlarged upper bounds
\[
 U_1=P_1+.000003,\qquad U_2=P_2+.000001.                 \tag{44}
\]
Let \(S=S_9\), \(C=C_8\), \(e=.00000003\). The remainders satisfy
\[
 S-e<\sin x<S,\qquad C-e<\cos x<C,
\]
since \(.77^{10}/10!<e\) and \(.77^{11}/11!<e\).
Put
\[
 X_1=k^2+(\lambda-v)^2,\quad
 X_2=\mu^2+q^2+\lambda^2+2\lambda(\mu S-qC).
\]
The true support norms satisfy \(n_1^2=X_1\) and
\(|n_2^2-X_2|<3e\). Both \(U_i\) are positive by bounding their
negative terms on \(.11\le w\le.58\). Define
\[
\begin{split}
 V={}&x-.09C+(\lambda-.09)(S-e)+\lambda+3.14159/4\\
 &+(k-v)(.899214)+\mu(1.414575)
          +(k-v+\mu+q+.18)/2\\
 &-1.978788(U_1+U_2)-\gamma.
\end{split}                                                  \tag{45}
\]
The full-circle support formula in the existing nonaligned short proof
gives \(F-\gamma>V\), provided the first two polynomials below are
positive. Their positivity supplies \(n_1<U_1,n_2<U_2\).
Here are all three rows on the single interval \([.3,.77]\);
each listed integer is divided by \(10^{10}\).

| Polynomial | Degree | Positive lower coefficient numerators |
|---|---:|---|
| \(U_1^2-X_1\) | 8 | 46107, 45428, 44692, 43715, 41998, 38553, 32151, 22091, 9625 |
| \(U_2^2-X_2-3e\) | 10 | 14892, 26291, 72150, 224495, 650842, 1676221, 3836335, 7920705, 15005681, 26478271, 44052700 |
| \(V\) | 10 | 7887247, 13045323, 20098966, 28832262, 38936090, 50011101, 61569449, 73035241, 83743732, 92939289, 99772210 |

Equations (41), (44), and (45) specify every finite comparison, with no
unstated partition. Together with the earlier interval \([.08,.3]\),
this proves the full nonaligned support interval needed in Section 4.1.

## 9. Endpoint arithmetic and complete coverage

For completeness, here are the sixteen scalar support endpoint lower
bounds used above. They come directly from (11)–(13) at the indicated
states, not from minimization over a numerical grid.

| Regime, support choices | Angle | Strict cost lower bound |
|---|---|---:|
| L/H primary, target \(-\); L cut, H circle; \(\lambda=.7\) | .6 | 1.11099071 |
| L/H primary, target \(+\); L cut, H first; \(\lambda=.9\) | \(\pi/2\) | .99372284 |
| Same | \(\pi/2+.45\) | 1.04894964 |
| L/H primary, target \(+\); L cut, H diagonal; \(\lambda=.9\) | \(\pi/2\) | 1.01899206 |
| Same | \(\pi/2+.45\) | 1.15715877 |
| L/H \(f,(-,+)\); L axial, H circle; \(\lambda=1.02\) | 1.35 | .89708175 |
| Same | \(\pi/2\) | .88524446 |
| Same | 2.02 | 1.03740259 |
| L/H \(f,(+,+)\); (13), H first | 1.1 | .92324078 |
| Same | 1.35 | .90611618 |
| L/H \(f,(+,+)\); (13), H circle | 1.35 | .90482983 |
| Same | \(\pi/2-.02\) | .88535591 |
| L/H \(f,(+,+)\); (13), H diagonal | \(\pi/2+.02\) | .89137840 |
| L/H \(f,(+,-)\); (13), H diagonal | \(-.02\) | .88536715 |
| L/H \(f,(+,-)\); (13), H circle | .02 | .89065261 |
| Same | .46 | 1.04853600 |

All constants are bracketed in (5). For a positive rational angle
\(x\le2.02\), use \(S_{11}\le\sin x\le S_{13}\) and
\(C_{14}\le\cos x\le C_{12}\). For a negative argument, apply parity
to the positive bounds; for \(\pi/2+e\), use
\(\sin(\pi/2+e)=\cos e\), \(\cos(\pi/2+e)=-\sin e\).
These substitutions, directed rational interval arithmetic, and squaring
positive rational root brackets prove the displayed endpoint bounds.
For each root \(\sqrt t\), the optional replay uses a rational upper
bound with denominator \(10^{10}\), certified by its square.

The case cover can now be read independently of the arithmetic replay:

| Ordered pair and source axis | Signs | Complete cover |
|---|---|---|
| H/L, \(f\) | \((-,\pm)\) | Impossible, Section 2 |
| H/L, \(f\) | \((+,+)\) | Barrier to .08; existing .08–.3; Section 8.3 to .77; tail |
| H/L, \(f\) | \((+,-)\) | Negative contact deformation; diagonal and axial scalars to .46; tail |
| H/L, \(e\) | either source, target \(-\) | Barrier to 1.2; upper-coordinate negative deformation; Hessian boundary reduction; tail |
| H/L, \(e\) | either source, target \(+\) | Same barrier; upper axial bound; two polynomials; tail |
| L/H, \(e\) | either source, target \(-\) | Barrier to .6; increasing scalar to .8; tail |
| L/H, \(e\) | either source, target \(+\) | Barrier to \(\pi/2\); two endpoint scalars; tail |
| L/H, \(f\) | \((-,-)\) | Barrier to .3; polynomial to .8; tail |
| L/H, \(f\) | \((-,+)\) | Barrier to 1.35; two concave scalars; tail |
| L/H, \(f\) | \((+,-)\) | Negative scalar; parallel strip; positive scalar; tail |
| L/H, \(f\) | \((+,+)\) | Barrier; first-endpoint scalar; circle scalar; quarter strip; diagonal scalar; tail |

These are all sixteen ordered source-axis sign branches. Reflection and
reversal, as stated after (4), give every retained target branch.
Thus every feasible L/H pair has corrected cost strictly greater than
\(.8833\), as required. \(\square\)

### Optional arithmetic replay

Run
\[
 \texttt{node verify\_low\_high\_whole\_pair\_hand.mjs}.
\]
The companion file uses only exact integer fractions and directed rational
bounds. It checks 232 strict comparisons: 95 geometric and derivative
comparisons, 45 support/endpoint comparisons, and 92 polynomial comparisons.
The latter include all 80 coefficients of the six new rows. The 31
coefficients of the previously proved short nonaligned interval remain in
that cited lemma's replay. The output records the exact rational reserves.
The continuous contact arguments, sign reductions, and coverage table are
the mathematical proof; the replay is a reproducibility aid for its finite
arithmetic.

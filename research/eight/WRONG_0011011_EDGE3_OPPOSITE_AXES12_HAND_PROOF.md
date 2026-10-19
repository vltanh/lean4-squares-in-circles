# Wrong word 0011011: opposite-sign edge 3, axes 1 and 2

**Table-free completion.**
[HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md](formalization/HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md)
replaces this note's derivative-range premises by whole-domain
curvature and contact-envelope arguments. Together with the unchanged
geometric reductions below, it proves all four original axes and both
angle halves, including aligned and zero-coordinate boundaries.

## 1. Statement and exact data

This note proves the full-angle outer/outer edge-3 \((-,+)\) row whenever
one of the first two retained signed SAT inequalities holds. It also
proves the aligned bound for either of the other two axes. It makes no
inference about those two axes away from alignment.

Put
\[
 Q=\frac{9789}{2500},\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12,\quad a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 b_1=\sqrt{Q-\tfrac94}-\tfrac12.
\]
Both coordinates \(b,B\) lie in \([0,d]\); write \(a=a(b)\), \(A=a(B)\).
The exact labels and cost are
\[
\begin{aligned}
 T(b)&=.01670+2.42322b-.91744b^2-.95769a(b)b,\\
 L(B)&=.03965+3.85510B-1.49748B^2-1.89442a(B)B,\\
 C&=\phi-T(b)-L(B),\qquad |\phi-\pi/2|\leq.7.
\end{aligned}                                                     \tag{1}
\]
All terminating decimals denote rationals. The conclusion is
\[
                         C>.89777>.89765.                         \tag{2}
\]
The last quantity is the declared exact role-table entry.
For these signs the four retained axes are
\[
\begin{array}{c|l}
1&-b+A\sin\phi-B\cos\phi\geq W\\
2&-a\cos\phi-b\sin\phi+A\geq W\\
3&a\sin\phi-b\cos\phi-B\geq W\\
4&a-A\cos\phi-B\sin\phi\geq W
\end{array}\qquad W=\frac{1+\sin\phi+|\cos\phi|}{2}.                 \tag{3}
\]
The full-angle statement of this note is for axes 1 and 2.

The companion verify_wrong_0011011_edge3_opposite_axes12_hand.py
checks 108 fixed strict rational comparisons used below. Radicals use
directed rational square bounds, trigonometric endpoints use adjacent
Taylor sums, and the two nonaligned point angles use adjacent arctangent
sums with 24 and 25 terms and argument below .31. There is no optimizer,
adaptive cover, or discovery-data input.

## 2. Scalar derivatives and both aligned contact bounds

Set \(u=a(y)+1/2\), \(r=(y+1/2)/u\). Then
\[
 a'=-r,\quad r'=Q/u^3,\quad r''=3Q(y+\tfrac12)/u^5.
\]
For \(D=c+py+sy^2+h\,a(y)y\),
\[
\begin{aligned}
 D'&=p+2sy+h(a-yr),\\
 D''&=2s-2hr-hyQ/u^3,\\
 D'''&=-3hQ[Q-(y+\tfrac12)/2]/u^5.
\end{aligned}                                                     \tag{4}
\]
Both labels have \(h<0\); their third derivatives are positive and
increasing. The sign of the next derivative is that of
\(5Q(y+1/2)-2(y+1/2)^2-Q/2\), which increases and starts at \(2Q-1/2>0\).
Useful consequences are
\[
\begin{gathered}
 .899<d<.9,\quad1.4145<a_0<1.415,\quad.7905<b_1<.791,\\
 T''<0\ (b\leq.415),\quad T'''>1.6,\quad0<T'<1.069,\\
 T'(.1)<.944,\quad T'(.4),T'(d)<.774,\\
 L'''>3.17,\quad .624<L'<1.176,\quad L''(.5)<0.                     \tag{5}
\end{gathered}
\]
For the nontrivial lower derivative bound, use
\(L'(.5)>.62481\), \(|L''(.5)|<.032\), and
\(.62481-.032^2/6.34>.624\). Upper bounds follow from convexity
of the first derivatives and their endpoints. Positivity of \(T'\)
also follows from \(T'(.6)>.6101\), \(|T''(.6)|<.049\),
and the same square-completion argument.

At alignment, axes 1/2 require \(A-b\geq1\), so monotonicity of the
labels reduces their minimum to
\[
 H_{12}(B)=\pi/2-T(a(B)-1)-L(B),\qquad 0\leq B\leq b_1.
\]
Its derivatives are
\[
 H_{12}'=T'r-L',\quad H_{12}''=-T''r^2+T'r'-L'',\quad
 H_{12}'''=T'''r^3-3T''rr'+T'r''-L'''.
\]
Direct endpoint bounds justified by (4) give:

| \(B\) interval | Upper bound for \(H_{12}'''\) |
|---|---:|
| \([0,.2]\) | \(-2.2\) |
| \([.2,.4]\) | \(-1.9\) |
| \([.4,.6]\) | \(-1\) |
| \([.6,.7]\) | \(-1.2\) |
| \([.7,.791]\) | \(-.4\) |

In the last row the physical argument \(a(B)-1\) is clipped at zero.
Thus \(H_{12}''\) decreases, and its endpoint is \(>.22\).
At \(B=.685356885\), its value is \(>.8980812\) and its derivative
has magnitude \(<10^{-6}\). Consequently
\[
 H_{12}>.8980812-\frac{10^{-12}}{.44}>.89808.                       \tag{6}
\]

Axes 3/4 at alignment similarly reduce to
\[
 H_{34}(b)=\pi/2-T(b)-L(a(b)-1).
\]
Here \(H_{34}''=-T''-L''r^2+L'r'\). On \([l,h]\), a lower bound is
\(-T''(h)-L''(a(l)-1)r(l)^2+L'(a(l)-1)r'(l)\).
For \([0,.4],[.4,.6],[.6,.791]\), respectively, this exceeds
\(.97,.88,.79\). At \(b=.59709465\),
\(H_{34}>.8977817\), \(|H_{34}'|<10^{-6}\); hence
\[
                         H_{34}>.89778.                           \tag{7}
\]

## 3. Axis 1 below alignment

Write \(\phi=\pi/2-x\), \(0\leq x\leq.7\). The first axis gives
\[
 b\leq(A-\tfrac12)\cos x-(B+\tfrac12)\sin x-\tfrac12.               \tag{8}
\]
Increasing \(b\) decreases cost, so use equality. Its exact contact
domain is the convex quarter-disk
\[
 b,B\geq0,\quad b\leq A(B)-1,\quad
 (b+\tfrac32)^2+(B+\tfrac12)^2\leq Q.                              \tag{9}
\]
Every contact angle is below .571: the largest is at \(b=B=0\),
and \((a_0-.5)\cos(.571)-.5\sin(.571)<.5\). Thus there is no
additional angle boundary in (9).

Use target quantities \(u=A+.5\), \(r=(B+.5)/u\), and put
\[
 q=Q+1-2u,\quad z=b+.5,\quad v=\sqrt{q-z^2},\quad
 N=4Qu-2u^2-Q(Q+1),\quad f_1=(Q-u)/(uq).
\]
For \(f=-x(b,B)\), differentiation of (8) gives
\[
\begin{aligned}
 f_b&=1/v,& f_B&=f_1-rz/(qv),\\
 f_{bb}&=z/v^3,& f_{bB}&=-r/v^3,\\
 f_{BB}&=-\frac{rN}{u^2q^2}
 -\frac z{qv}\left(\frac Q{u^3}-\frac{2r^2}q-\frac{r^2}{v^2}\right).
\end{aligned}                                                     \tag{10}
\]
The contact cost is \(C=\pi/2+f-T-L\).

### 3.1 A convex rectangle controls the interior low minimum

When \(B\leq.4\), \(C_{bb}>0\), and \(C_b\) decreases in \(B\).
The check \(C_b(.1,.4)>0\) shows that any point with \(b>.1\)
decreases in cost upon decreasing \(b\) to .1, preserving (9).
The relevant rectangle is
\[
                           0\leq b\leq.1,\quad0\leq B\leq.4.      \tag{11}
\]
It lies wholly in (9), because \(1.6^2+.9^2<Q\).
Throughout it, (10) gives \(C_{bb}>1.5\), and:

| \(B\) interval | \(C_{BB}\) lower bound | \(|C_{bB}|\) upper bound |
|---|---:|---:|
| \([0,.1]\) | \(1.16\) | \(.515\) |
| \([.1,.2]\) | \(.85\) | \(.545\) |
| \([.2,.3]\) | \(.51\) | \(.561\) |
| \([.3,.35]\) | \(.40\) | \(.526\) |
| \([.35,.4]\) | \(.21\) | \(.526\) |

For each row \(B\in[l,h]\), substitute \(z\in[.5,.6]\),
\(u\in[u(h),u(l)]\), and the monotone endpoint range of \(N\) in
(10), then subtract \(L''(h)\) for the lower bound. The cross bound
is at most
\[
 \frac{(h+.5)/u(h)}{[Q+1-2u(l)-.36]^{3/2}}.
\]
Every row satisfies
\((1.5-.01)(C_{BB,\min}-.01)-|C_{bB}|_{\max}^2>0\).
Thus \(D^2C>.01I\).
At \((b,B)=(.05878084,.33400286)\),
\[
 C>.8977764,\quad |C_b|,|C_B|<10^{-6}.
\]
The angle uses the explicit radical expression
\[
 \tan x=\frac{(A-.5)v-(B+.5)z}{(A-.5)z+(B+.5)v}\in(0,.31).
\]
Strong convexity on the convex rectangle gives
\[
 C>.8977764-\frac{2\cdot10^{-12}}{.02}>.89777.                      \tag{12}
\]

### 3.2 All other interior minima are excluded

On \(.4\leq B\leq.5\), the check \(C_b(.105,.5)>.0014\)
forces \(b<.105\) at a simultaneous stationary point. The negative
mixed derivative implies
\(C_B\geq f_B(.105,B)-L'(B)\).
Formula (10) gives \(f_{BB}<-.073\) at \(b=.105\) throughout this
interval. Both \(f_B\) and \(L'\) decrease; the three endpoint
differences
\[
\begin{array}{c|ccc}
[l,h]&[.4,.42]&[.42,.45]&[.45,.5]\\ \hline
f_B(.105,h)-L'(l)&>.0019&>.0054&>.0073
\end{array}
\]
prove \(C_B>0\). No interior minimum occurs here.

On the rest of the physical domain, (10) gives the following negative
upper bounds for \(C_{BB}\):

| \(B\) interval | Upper bound |
|---|---:|
| \([.5,.525]\) | \(-.06\) |
| \([.525,.55]\) | \(-.18\) |
| \([.55,.6]\) | \(-.27\) |
| \([.6,.7]\) | \(-.45\) |
| \([.7,.791]\) | \(-1.1\) |

Here \(z\in[.5,u(l)-1]\), and the important physical bound
\(v\geq B+.5\geq l+.5\) follows from \(z\leq u-1\).
Subtract \(L''(l)\) for the upper bound. Thus there is again no
interior minimum.

The boundary of (9) is also covered: its curved part is alignment (6);
\(B=0\) lies in (11) or decreases into it. On \(b=0,B>.4\),
\(C_b(0,.4)<0\) and \(C_b\) decreases in \(B\), so increasing \(b\)
decreases cost unless already at the aligned endpoint.
This proves the whole lower half of axis 1.

## 4. Axis 1 above alignment: the zero-exit lemma

For \(\phi=\pi/2+x\), the maximal source coordinate is
\[
 b_{\max}=(A-.5)\cos x+(B-.5)\sin x-.5.                            \tag{13}
\]
Its maximum is below
\(\sqrt{Q-2a_0}-.5<.543<d\), so there is no diagonal clamp.
Since \((b_{\max})_x\leq B-.5<.4\), the active contact cost has
derivative \(>1-1.069(.4)>0\). It flows to alignment, or to its
zero exit \(b_{\max}=0\).

The common zero-exit curve is
\[
 (a(z)-.5)\cos x+(z-.5)\sin x=.5,\qquad b_1\leq z\leq d.           \tag{14}
\]
Its root is below .31. Indeed the left side is separately concave in
\(z,x\) on \([b_1,d]\times[.31,.7]\), and all four corner values
exceed .5. On the earlier root branch,
\[
 x_z=\frac{r(z)\cos x-\sin x}
            {(z-.5)\cos x-(a(z)-.5)\sin x}>1.25.                  \tag{15}
\]
The denominator is positive by
\((b_1-.5)\cos(.31)-.5\sin(.31)>0\), and below .4.
The numerator is \(>.5\), by \(r(z)>.86\) and
\(.86\cos(.31)-\sin(.31)>.5\).
Consequently the zero-exit cost
\(\pi/2+x-T(0)-L(z)\) increases, since \(L'<1.176\).
Its least endpoint is alignment \(z=b_1\), proving this half too.

## 5. Axis 2 below alignment

For \(\phi=\pi/2-x\), the target primary coordinate satisfies
\[
 A\geq.5+(a+.5)\sin x+(b+.5)\cos x.                               \tag{16}
\]
The right side increases in \(x\leq.7<\pi/4\), so \(A\geq1+b\);
thus \(b<.415,B\leq b_1\). Take equality to maximize \(B\)
and minimize cost. Write \(N_L(A)=-L(B(A))\).
Its derivative is \(L'(B)/r(B)>.624/.861\).
The positive angular speed satisfies
\[
 A_x^2=Q-(A-.5)^2>Q-.915^2,\qquad
                  (.624/.861)^2(Q-.915^2)>1.
\]
It follows that \(C_x=-1+N_L'(A)A_x>0\), and the contact
flows down to alignment (6).

## 6. Axis 2 above alignment

Here the least target primary coordinate is
\[
 A\geq\max(d,A_*),\qquad
 A_*=.5+(b+.5)\cos x-(a-.5)\sin x.                                \tag{17}
\]
On an inactive diagonal piece \(A_*<d\), increasing \(b\)
decreases cost and reaches \(A_*=d\) before \(b=d\).
This follows from
\(.5+(d+.5)\cos(.7)-(d-.5)\sin(.7)>d\).
So consider active contacts.

Use source \(u=a+.5,r=(b+.5)/u,q=Q+1-2u\), and set
\(z=A(B)-.5>0,v=\sqrt{q-z^2}\).
Implicit differentiation gives
\[
 x_b=f_1+\frac{rz}{qv},\quad x_B=\frac{r(B)}v,\qquad
                     f_1=\frac{Q-u}{uq}.                         \tag{18}
\]
On \(B=d\), let \(z_0=d-.5\) and \(J(b)=\pi/2+x(b,d)-T(b)-L(d)\).
Then
\[
\begin{aligned}
 J'&=f_1+\frac{rz_0}{qv}-T',\\
 J''&=-\frac{rN}{u^2q^2}
 +\frac{z_0}{qv}\left(\frac Q{u^3}-\frac{2r^2}q-\frac{r^2}{v^2}\right)-T''.
\end{aligned}                                                     \tag{19}
\]
One direct interval substitution gives \(J''>1\) on \([0,.1]\).
At \(b=.00542853\),
\[
 J>.8977735,\qquad |J'|<10^{-6}.
\]
The angle is explicitly
\[
 \tan x=\frac{(b+.5)v-(a-.5)z_0}{(b+.5)z_0+(a-.5)v}\in(0,.31).
\]
Thus \(J>.8977735-10^{-12}/2>.89777\) on this interval.

The diagonal derivative is positive after .1. First,
\(f_1>.84\) everywhere: after multiplication by its positive denominator
this is the quadratic inequality
\[
 1.68u^2-[1+.84(Q+1)]u+Q>0,
\]
whose minimum \(Q-[1+.84(Q+1)]^2/6.72\) is positive.
For \(.1\leq b\leq.4\), \(N>0\), so \(f_1\) decreases in \(b\), and
\[
 f_1+\frac{rz_0}{qv}
 \geq f_1(.4)+\frac{r(.1)z_0}{q(.4)\sqrt{q(.4)}}>.955>T'(b).
\]
For \(b\geq.4\), the bound \(.84>.774\) suffices.
This proves the entire target-diagonal boundary.

For all other active contacts \(z\geq z_0\), and
\(z/\sqrt{q-z^2}\) increases in \(z\).
Hence \(C_b\geq J'(b)>0\) for \(b\geq.1\).
Decreasing \(b\) at fixed \(B\) decreases cost and angle until
\(b=.1\) or alignment; it preserves the allowed domain.
It remains to take \(b\leq.1\).
Now \(A\leq1+b\leq1.1\), so \(B>\sqrt{Q-1.6^2}-.5>.664\).
Every such contact is below .7, since \(A_*(.1,.7)<d\).
Also \(v\geq a(.1)-.5>.885\), because \(v_x=A-.5>0\).
At fixed \(b\),
\[
 C_{BB}=\frac Q{(A+.5)^3v}-\frac{(A-.5)r(B)^2}{v^3}-L''(B).
                                                               \tag{20}
\]
Three direct rows give:

| \(B\) interval | Upper bound for \(C_{BB}\) |
|---|---:|
| \([.664,.74]\) | \(-.12\) |
| \([.74,.82]\) | \(-.51\) |
| \([.82,.9]\) | \(-1\) |

For a row \([l,h]\), use \(v\geq.885\) and
\(v\leq\sqrt{Q+1-2u(.1)-(a(h)-.5)^2}\), and subtract \(L''(l)\).
Thus the fixed-\(b\) contact cost is concave in \(B\); its endpoints
are alignment and the target diagonal. Both have already been proved
strictly above .89777.

## 7. Scope and strictness

All minimizations above are over explicitly described compact domains.
Every motion decreases cost or reduces the minimum to a covered boundary.
No hidden gap or nonneighbor condition is imposed. Each final bound is
strictly above .89777, hence contributes a positive reserve above the
declared edge entry .89765. A whole edge-3 row additionally requires the
nonaligned cases of axes 3 and 4.

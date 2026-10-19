# The complete conditional equality family from coarse stationary geometry

## Theorem and scope

Let \((q_*,u_*,t_*)\) be the actual stationary zero constructed in
[the stationary existence proof](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md).
The only radius enclosure used here is

\[
3.9154<q_*<3.915534138<3.9156.
\tag{1}
\]

This note proves the complete weak five-parameter equality domain and
an explicit five-dimensional box of pairwise noncongruent configurations.
It replaces the narrow-coordinate arithmetic in Sections 5--6 of
[the earlier equality-domain note](../COMPLETE_EQUALITY_PARAMETER_DOMAIN.md).
Neither the nine local position brackets, the four derivative rectangles,
the five-interval family enclosure, the narrow sharp-radius bracket, nor
the equality-box arithmetic transcription is an input.

The classification has precisely the following global hypothesis. An
original radius-\(\sqrt{q_*}\) packing must admit the named cyclic roles
and a boundary representative, preserving its originally selected signed
witnesses and all frames, to which
[the new conditional terminal](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md)
applies. Under that hypothesis, every original equality packing is one of
the configurations below, up to an isometry and relabeling. Conversely,
every point of the displayed parameter domain is an actual eight-square
packing with least enclosing radius \(\sqrt{q_*}\).

This closes the conditional equality part of G9. It does not assert the
still separate unrestricted word, cut, owner, or mismatch capture gates.
All terminating decimals below are exact rational numbers.

## 1. Only a coarse stationary window is needed

Use the positive radicals

\[
\begin{aligned}
r&=\sqrt{q-u^2},&U&=\sqrt{q-(2-u)^2},&V&=3-U,\\
Y&=\sqrt{q-V^2},&v&=2-Y,&w&=\sqrt{q-v^2},\\
h&=\tan t,&c&=(1+h^2)^{-1/2},&s&=hc,\\
k_1&=2-c(r-1)+su,&k_2&=1+cv-s(w-1),\\
F(q,u,t)&=k_1^2+k_2^2-q.
\end{aligned}
\tag{2}
\]

The stationary-position proof gives a unique position minimum
\(u(q,t)\) and

\[
.895<u(q,t)<1-.6h\le .94
\quad(3.9154\le q\le3.9156, .1\le h\le .164).
\tag{3}
\]

On this whole rectangle put

\[
p=\frac{(2-u)V}{UY},\quad
a=s+cu/r,\quad b=p(c+sv/w),
\quad d=s(r-1)+cu,\quad  e=c(w-1)+sv.
\]

The exact identities are

\[
F_u=2(k_1a-k_2b),\qquad F_t=2(k_1d-k_2e),
\]
\[
F_{ut}=2\{da+k_1(c-su/r)+eb-k_2p(cv/w-s)\}.
\tag{4}
\]

In addition to \(F_{uu}>0\), the primitive bounds in Section 2 of
the terminal proof give \(F_{ut}>4\) on this entire rectangle.
Here is the complete rational lower substitution, to make the sign
independent of any derivative table:

\[
\begin{aligned}
F_{ut}>2\bigg\{&[.0995(.741)+.9868(.895)](.599)\\
&+1.327\left(.9868-\frac{.162(.94)}{1.741}\right)
  +.938(.582)\\
&-1.470(.637)
    \left(\frac{.9951(.562)}{1.897}-.0995\right)\bigg\}
=\frac{2009576205379701}{471811000000000}>4.
\end{aligned}
\tag{5}
\]

Every factor bounded here has the indicated positive sign. In
particular \(cv/w-s>0\), so the last term is the only negative
one in (4).

### 1.1 Two comparison tilts

We prove

\[
\boxed{.1<\tan t_*<.13,\qquad  .916<u_*<.94.}
\tag{6}
\]

These coarse bounds follow from two endpoint derivative signs, with no
cover of the intervening tilts. They will be enough for every geometric
claim below.

For convenient exact substitutions, write \(L=\sqrt{1+h^2}\) and

\[
A_1=2L-(r-1)+hu,\qquad B_1=L+v-h(w-1).
\]

Then (4) becomes

\[
\frac{F_u}{2c^2}=A_1(h+u/r)-B_1p(1+hv/w),
\qquad
\frac{F_t}{2c^2}=A_1[h(r-1)+u]-B_1[(w-1)+hv].
\tag{7}
\]

At \((u,h)=(.94,.1)\), throughout the radius interval in (3),
successive positive-square comparisons give

\[
\begin{gathered}
1.74120<r<1.74127,\quad 1.67086<U<1.67093,\\
1.46587<Y<1.46601,\quad 1.90528<w<1.90538,\\
1.004987<L<1.004988.
\end{gathered}
\]

Substitution in (7) gives

\[
\frac{F_u}{2c^2}>.015,\qquad 
\frac{F_t}{2c^2}<-.0065.
\tag{8}
\]

For example, the second upper comparison is explicitly

\[
1.362776[.1(.74127)+.94]
 -1.448439[.90528+.1(.53399)]<-.0065.
\]

The position minimum at this tilt lies below .94, by (8) and strict
position convexity. Since \(F_t\) increases with position by (5),
the actual envelope derivative satisfies
\(M_t(q,\arctan .1)<0\).

At \((u,h)=(.916,.13)\), the corresponding positive-square bounds are

\[
\begin{gathered}
1.75395<r<1.75401,\quad 1.65539<U<1.65546,\\
1.45169<Y<1.45184,\quad 1.90125<w<1.90135,\\
1.008414<L<1.008415.
\end{gathered}
\]

Here (7) gives

\[
\frac{F_u}{2c^2}<-.004,\qquad 
\frac{F_t}{2c^2}>.001.
\tag{9}
\]

For example, in the second lower comparison one may use
\(A_1>1.381898\), \(B_1<1.4395625\), obtaining

\[
1.381898[.13(.75395)+.916]
 -1.4395625[.90135+.13(.54831)]>.001.
\]

All root bounds just displayed follow in the order \(r,U,Y,w\)
from their four radicands in (2); each assertion compares the square
of a positive decimal endpoint with the preceding radicand. The
two bounds for \(L\) are squares against 1.01 and 1.0169.
Thus (8)--(9) are fixed endpoint inequalities for the actual function,
not assumptions about approximate stationary roots.

By (9), the position minimum at \(h=.13\) lies above .916.
Equation (5) now gives \(M_t(q,\arctan .13)>0\).
The broad actual-envelope theorem, used after the existence construction,
says there is at most one critical tilt; at \(q=q_*\), that critical
tilt is the zero minimum \(t_*\). The two opposite derivative signs
therefore put it strictly between the endpoints in (6).

Finally implicit differentiation gives
\(u_t=-F_{ut}/F_{uu}<0\) between those endpoints. Applying the
position bounds at \(h=.1,.13\) proves the position assertion
in (6). No uniform reduced-curvature constant is needed.

### 1.2 Consequences of the coarse window

From now on all quantities in (2) are evaluated at the stationary zero.
Successive squaring using only (1) and (6) gives

\[
\begin{gathered}
1.741<r<1.755,\quad 1.655<U<1.671,\quad 1.329<V<1.345,\\
1.451<Y<1.467,\quad  .533<v<.549,\quad 1.9<w<1.906,\\
.991<c<.996,\qquad  .099<s<.13.
\end{gathered}
\tag{10}
\]

For example,
\(3.9154-.94^2>1.741^2\) and
\(3.9156-.916^2<1.755^2\); the other roots follow in their
printed order. The sine bounds follow from monotonicity of
\(h/\sqrt{1+h^2}\).

The formulas and the whole-graph \(k_2\) bound in Section 5 of
the terminal proof give

\[
1.338<k_1<1.39,\qquad 1.4<k_2<1.45.
\tag{11}
\]

For the first bound, direct substitution gives
\(2-.996(.755)+.099(.916)=1.338704>1.338\) and
\(2-.991(.741)+.13(.94)=1.387869<1.39\).

We shall also retain the more informative inequality

\[
k_1-1=1-c(r-1)+su>.245+.916s.
\tag{12}
\]

The narrower historical coordinates near .92065 and .1233 will not
be used.

## 2. Equality returns to the original five anchors

Write \(e=(c,s)\), \(f=(-s,c)\). The five anchor centers and
their frames are

\[
\begin{array}{lll}
P_A=(r-1/2,1/2-u),&P_B=(U-1/2,3/2-u),&\text{frame }0,\\
P_D=(U-5/2,Y-1/2),&P_E=(1/2-w,1/2-v),&\text{frame }0,\\
P_H=(1/2-k_1)e+(1/2-k_2)f,&&\text{frame }t_*.
\end{array}
\tag{13}
\]

The fixed-witness radial-boundary argument retains every frame, the
cyclic order, and each initially selected signed separator. Apply the
new terminal to the captured representative at squared radius \(q_*\).
Its nonnegative terms force \(S=0\) and \(M(q_*,t)=0\), hence
\(t=t_*\). These are also the original frames.

For clarity, the remaining pullback is a direct algebraic identity.
Use the positive stationary disk weights \(\mu_i\), summing to one,
and positive contact weights \(\lambda_j\). For the original
selected corners and original signed gaps \(g_j\ge0\), put

\[
\mathcal D=\sum_{i=A,B,D,E,H}\mu_i|p_i+o_i|^2
              -\sum_j\lambda_jg_j.
\]

At zero frame error the force equations give exactly

\[
\mathcal D=q_*+
 \sum_{i=A,B,D,E,H}\mu_i|p_i-P_i|^2.
\tag{14}
\]

Containment gives

\[
q_* -\mathcal D
 =\sum_i\mu_i(q_*-|p_i+o_i|^2)+\sum_j\lambda_jg_j\ge0.
\]

Every summand is nonnegative, so the five original anchors equal
(13), and all seven originally selected gaps are zero. The two zero
slider forces and their incident gap equalities give exactly

\[
P_T=(U-3/2,z),\qquad 
P_G=P_H+e+\eta f,
\tag{15}
\]

with frames 0 and \(t_*\), respectively. Thus no original-center
proximity or original projected-slider bounds need to be pulled back.
This is the geometric proof in
[the fixed-witness equality pullback](../EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md),
with its old quantitative terminal replaced by (14) and the new
\(\mu_HM+S/500\) inequality.

## 3. The exact two exterior-slider ranges

Define

\[
\begin{aligned}
z_+&=\sqrt{q_*-(U-1)^2}-\frac12,\\
\eta_-&=k_2-\sqrt{q_*-(2-k_1)^2},\qquad
\eta_+=k_2-\frac{13}{12}.
\end{aligned}
\tag{16}
\]

The complete exterior ranges are

\[
\boxed{\frac7{12}\le z\le z_+,\qquad 
        \eta_-\le\eta\le\eta_+.}
\tag{17}
\]

We prove both necessity and the fact that these ranges alone supply
containment and all 21 exterior-pair separations.

### 3.1 Necessity, including the sign of each slider

The original central square contains the closed radius-\(1/12\)
disk in its open interior. Every exterior square avoids that disk.
The preserved cyclic order is \(H,G,A,B,T,D,E\).

The centers \(B,D\) lie strictly in the upper halfplane by (10),
with one on each side of the vertical axis. Their intervening sector
has angle less than \(\pi\), so the intervening center \(T\)
has \(z>0\). Also \(f\cdot P_H=1/2-k_2<0\), whereas

\[
f\cdot P_A=-s(r-1/2)+c(1/2-u)<0,\qquad  e\cdot P_A>0.
\]

Since \(e\cdot P_H=1/2-k_1<0\), the intervening sector
from \(H\) to \(A\) lies in \(f\cdot P<0\) and has
angle less than \(\pi\). Thus \(f\cdot P_G<0\).

Now \(0<U-3/2<1/2\). The distance from the origin to \(T\)
is \((z-1/2)_+\); core avoidance gives \(z\ge7/12\).
Its farthest corner has squared norm
\((U-1)^2+(z+1/2)^2\), giving the upper bound in (17).

In its own frame \(G\) has center coordinates

\[
\xi=3/2-k_1\in(0,1/2),\qquad 
\zeta=1/2-k_2+\eta<0.
\]

Core avoidance says \(\zeta\le-7/12\), or
\(\eta\le\eta_+\). Its farthest squared norm is

\[
(2-k_1)^2+(k_2-\eta)^2,
\]

where \(k_2-\eta>0\). Containment gives \(\eta\ge\eta_-\).
The displayed core endpoints are weak deliberately. The strict central
core and actual central-pair separations below exclude an exterior square
touching that core, so no spurious boundary packing is introduced.

### 3.2 Containment and all exterior pairs throughout (17)

The five selected anchor vertices are

\[
(r,-u),\quad(U,2-u),\quad(-V,Y),\quad(-w,-v),
\quad-k_1e-k_2f.
\tag{18}
\]

All have squared norm \(q_*\), using \(F=0\). The signs in
(10)--(11) make them the farthest vertices of their respective squares.
The two computations in Section 3.1 prove containment for the sliders.

The five standard-frame squares form three separated columns:
\(D,E\), then \(T\), then \(A,B\). Indeed \(r>U\)
because \(u<1\), and \(w>V=3-U\), since
\(w^2-V^2=Y^2-v^2=4(1-v)>0\). Adjacent column gaps are
one for \(D,T\) and \(T,B\), and larger for the other
nearby choices. Within either two-square column the vertical center
gap is exactly one. These facts cover all ten standard-frame pairs,
independently of \(z\).

Put \(W_0^*=(1+c+s)/2\). Direct substitution of (13)--(15)
gives the four mixed or tilted separations

\[
\begin{gathered}
e\cdot(P_G-P_H)=1,\qquad  e\cdot(P_A-P_G)=W_0^*,\\
e\cdot(P_A-P_H)=W_0^*+1,\qquad 
f\cdot(P_E-P_H)=W_0^*.
\end{gathered}
\tag{19}
\]

For \(E,G\), the leftmost horizontal coordinate of \(G\)
decreases with \(\eta\). At its largest allowed value it is

\[
c(1-k_1)+s/12>-.39,
\]

while the right edge of \(E\) is \(1-w<-.9\).
This proves their horizontal separation throughout (17).

The top of \(H\) is
\(s(1-k_1)+c(1-k_2)<0\). The top of \(G\) increases
with \(\eta\), and at \(\eta_+\) is

\[
s(2-k_1)-c/12=c\{h(2-k_1)-1/12\}<0.
\tag{20}
\]

Here is a uniform proof of the last sign, which is the only mildly
tight exterior comparison. From (2), (6), and (10),

\[
h(2-k_1)=hc(r-1-hu)<h(.755-.916h).
\]

The final quadratic increases on \([.1,.13]\), because its
derivative is \(.755-1.832h>0\). Therefore

\[
h(2-k_1)<.13[.755-.916(.13)]
=.0826696<\frac1{12}.
\tag{21}
\]

The bottoms of \(B,D,T\) are respectively
\(1-u>0\), \(Y-1>0\), and \(z-1/2\ge1/12\).
They are vertically separated from each of \(H,G\). These
six pairs complete the count \(10+4+1+6=21\).

## 4. The full weak five-parameter domain

Let \((x,y)\) be the central square's center. Parameterize one
quarter-turn fundamental frame interval by

\[
1-\sqrt2\le\kappa<\sqrt2-1,\qquad 
C=\frac{1-\kappa^2}{1+\kappa^2},\qquad 
\Sigma=\frac{2\kappa}{1+\kappa^2}.
\tag{22}
\]

Its frame is \(\theta=2\arctan\kappa\in[-\pi/4,\pi/4)\).
The five free parameters are \((x,y,\kappa,z,\eta)\).
For any vector \(d=(d_x,d_y)\), define

\[
\begin{aligned}
M_0(d)&=\max\{|d_x|,|d_y|,|Cd_x+\Sigma d_y|,
                                  |-\Sigma d_x+Cd_y|\},\\
M_t(d)&=\max\{|cd_x+sd_y|,|-sd_x+cd_y|,
                   |Cd_x+\Sigma d_y|,|-\Sigma d_x+Cd_y|\},\\
W_0&=\frac{1+C+|\Sigma|}{2},\\
W_t&=\frac{1+cC+s\Sigma+|c\Sigma-sC|}{2}.
\end{aligned}
\tag{23}
\]

Here \(C>0\), and \(cC+s\Sigma=\cos(\theta-t_*)>0\),
because (6) gives \(0<t_*<.13<\pi/4\). Thus (23) has
exactly the needed absolute values, even at the allowed frame endpoints.
Write \(d_i=P_i-(x,y)\) with the explicit centers (13), (15).

The parameter domain is

\[
\boxed{
\begin{gathered}
1-\sqrt2\le\kappa<\sqrt2-1,\qquad 
7/12\le z\le z_+,\qquad  \eta_-\le\eta\le\eta_+,\\
|Cx+\Sigma y|<5/12,\qquad |-\Sigma x+Cy|<5/12,\\
M_0(d_i)\ge W_0\quad(i=A,B,D,E,T),\\
M_t(d_i)\ge W_t\quad(i=H,G).
\end{gathered}}
\tag{24}
\]

All quantities in this formula are explicit radicals, rational functions,
absolute values, and maxima of its five real arguments. In particular,
there is no unquantified pose or choice of a separating axis.

The two strict core inequalities say exactly that the central square
contains the closed radius-\(1/12\) disk in its open interior. They
also make its containment automatic, since its farthest squared norm is

\[
(|Cx+\Sigma y|+1/2)^2+(|-\Sigma x+Cy|+1/2)^2
<2(11/12)^2=121/72<q_*.
\]

For two unit squares, along any of their four side normals, the sum
of their half-widths is
\((1+|\cos\phi|+|\sin\phi|)/2\), where \(\phi\)
is their frame difference. The separating-axis theorem therefore gives
exactly the last two lines of (24) for the seven central pairs. Their
weak inequalities preserve all boundary contacts and simultaneous-axis
ties. Section 3 supplied the other 21 pairs and all exterior containment.
This proves sufficiency of (24) for an actual packing.

Conversely, the conditional equality pullback gives (13), (15), and
the preserved order; Section 3 gives (17). The central-core theorem,
the quarter-turn frame convention, and the same separating-axis theorem
then give every remaining condition in (24). This proves necessity.

## 5. An entire five-dimensional box, with direct geometric reserves

The following parameters vary independently:

\[
\boxed{
.139\le x\le.141,\quad  -.001\le y\le.001,\quad 
.099\le\kappa\le.101,\quad 1.349\le z\le1.351,\quad 
-.321\le\eta\le-.319.}
\tag{25}
\]

We prove directly that the whole closed box is inside (24). There is
no subdivision or equality-box row list in the argument.

Monotonicity of the two rational functions in (22) gives

\[
.979<C<.981,\qquad  .196<\Sigma<.2.
\tag{26}
\]

The central frame is strictly larger than \(t_*\), because
\(\tan\theta=2\kappa/(1-\kappa^2)>.198>.13>h\).
Both frames lie between zero and \(\pi/4\). Hence
\(D_0=cC+s\Sigma>0\), \(E_0=c\Sigma-sC>0\), and

\[
W_t\le W_0<1.0905.
\tag{27}
\]

The first inequality follows from monotonicity of \(\cos x+\sin x\)
on \([0,\pi/4]\), applied to \(\theta-t_*<\theta\).

### 5.1 The five standard-frame neighbors

For \(A,E,T\), use the positive horizontal, negative horizontal,
and positive vertical normals, respectively. Their projected gaps
minus \(W_0\) are bounded below by

\[
\begin{aligned}
&1.741-.5-.141-1.0905=.0095,\\
&1.9-.5+.139-1.0905=.4485,\\
&1.349-.001-1.0905=.2575.
\end{aligned}
\tag{28}
\]

For \(B\), use the central normal \((C,\Sigma)\); for
\(D\), use \((-\Sigma,C)\). In these two directions each
summand of the projected gap is positive. Their reserves exceed

\[
.979(1.655-.5-.141)+.196(1.5-.94-.001)-1.0905
=.01177,
\]
\[
.196(2.5+.139-1.671)+.979(1.451-.5-.001)-1.0905
=.029278.
\tag{29}
\]

Thus all five standard-frame central pairs separate with strict margins.

### 5.2 The two tilted neighbors

For \(G\), use \(-f=(s,-c)\). The projected center gap is

\[
k_2-.5-\eta-sx+cy.
\]

Equations (10)--(11), (25), and (27) give the strict reserve

\[
1.4-.5+.319-.13(.141)-.996(.001)-1.0905
=.109174>0.
\tag{30}
\]

For \(H\), use the negative first central normal \((-C,-\Sigma)\).
Subtracting its exact support sum, its margin is

\[
Cx+\Sigma y+(k_1-1)D_0+(k_2-1)E_0-\frac12.
\tag{31}
\]

This expression retains the useful correlation with tilt. From
(10), (26), and (12),

\[
D_0>.991(.979)+.099(.196)>.989,\qquad 
E_0>.991(.196)-.981s>0,
\]

and \(k_1-1>.245+.916s\), \(k_2-1>.4\). Therefore (31)
is greater than

\[
\begin{aligned}
&.979(.139)-.2(.001)+.989(.245+.916s)\\
&\hspace{25mm}+.4[.991(.196)-.981s]-.5\\
&\ge .979(.139)-.2(.001)+.989(.245)
        +.4(.991)(.196)-.5\\
&\hspace{25mm}+[.989(.916)-.4(.981)](.099)\\
&=\frac{1679819}{250000000}>.0067.
\end{aligned}
\tag{32}
\]

The coefficient of \(s\) is positive, which justifies the one
endpoint substitution. This proves the delicate central--\(H\)
separation over the entire box without any narrow anchor enclosure.

### 5.3 Core and containment, including both slider interiors

The two central core coordinates satisfy

\[
|Cx+\Sigma y|<.981(.141)+.2(.001)<.139,
\qquad
|-\Sigma x+Cy|<.2(.141)+.981(.001)<.030.
\tag{33}
\]

Thus the core inequalities are strict. Both sliders also lie strictly
inside their permitted circle boundaries. For \(T\), (10), (25)
give the squared-radius reserve

\[
q_*-(U-1)^2-(z+1/2)^2
>3.9154-.671^2-1.851^2=.038958>0.
\tag{34}
\]

For \(G\), use \(2-k_1<.662\) and
\(0<k_2-\eta<1.771\), obtaining

\[
q_*-(2-k_1)^2-(k_2-\eta)^2
>3.9154-.662^2-1.771^2=.340715>0.
\tag{35}
\]

Their core distances are strictly greater than \(1/12\):
\(z-.5\ge.849\), while
\(-\zeta=k_2-.5-\eta>1.219\).
Together with (34)--(35), this puts both sliders strictly inside
(17). Equations (28)--(35) prove that the whole box (25) is in (24),
with every inequality involving its five varying parameters strict.

## 6. Dimension and noncongruence do not need a numerical root

The five anchor vertices in (18) lie on the circle. The other three
squares are strictly inside it throughout (25), by (33)--(35).
The circle is the unique least enclosing circle of every configuration
in (24), independently of any unrestricted lower-bound assertion.
Indeed the segment joining \((r,-u)\) and \((U,2-u)\)
crosses the horizontal axis at a positive abscissa. The segment joining
\((-V,Y)\) and \((-w,-v)\) crosses it at a negative abscissa.
Thus the origin is a convex combination of these four circle points.
For a proposed distinct center \(a\), one of those points \(P\)
has \(P\cdot a\le0\), and consequently

\[
|P-a|^2=q_*+|a|^2-2P\cdot a>q_*.
\]

An isometry between two configurations in (25) must preserve this
circle and its center. Among the five boundary squares, four have
the same standard frame and \(H\) alone has the distinct frame
\(t_*\). Thus it must preserve the standard frame and send \(H\)
to \(H\).

The coarse bounds already prove

\[
-.8<(P_H)_x<-.7,\qquad  -1.07<(P_H)_y<-.97.
\tag{36}
\]

For example substitute (10)--(11) in
\((P_H)_x=-c(k_1-.5)+s(k_2-.5)\) and
\((P_H)_y=-s(k_1-.5)-c(k_2-.5)\). A rotation preserving
the standard frame is a quarter turn; only the identity can fix this
nonzero center. A reflection preserving that frame has an axial or
diagonal mirror through the origin. The inequalities (36) put \(P_H\)
on none of those mirrors. Hence the isometry is the identity.

The unique central square and the distinct slider positions then recover
all five parameters. Different points of (25) are pairwise noncongruent.
The map \(\kappa\mapsto2\arctan\kappa\) has nonzero derivative,
and the other four parameters move their stated coordinates independently.
The family therefore has local dimension five after isometries and
relabeling are factored out.

## 7. Dependency conclusion

The weak equality domain (24), its converse, and the noncongruent
five-dimensional box (25) use only the new stationary existence and
uniqueness theorem, the whole-domain stationary/terminal estimates,
the fixed-witness geometric pullback, and the explicit inequalities
above. The two new tilt signs (8)--(9) are enough; none of the
historical narrow coordinate or radius brackets is necessary.

In particular the 49 local stationary/formula checks are not needed
to select or use the stationary witness; the old five-interval
enclosure is not needed for the conditional terminal or this equality
classification; and the equality-box arithmetic file is not a premise.
The remaining unrestricted capture gates stay separate from these
completed conditional conclusions.

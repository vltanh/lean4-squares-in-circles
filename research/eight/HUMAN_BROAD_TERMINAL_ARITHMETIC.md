# A hand-sized stationary and owner calculation for the broad terminal

**Table-free successor.**
[The whole-domain terminal proof](formalization/HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md)
now supplies all force weights, owner reserves, automatic sliders, and
remainder estimates for the needed \(S\le1/1000\) theorem. It retains
the exact force identities below while replacing this note's numerical
rectangles and derivative estimates. The body below records the earlier
four-rectangle argument.

This note replaces the large terminal coefficient calculation by nine scalar
inequalities on four predetermined rational rectangles. It also gives a
coarse enclosure of the exact family radius without a root-isolation program.
The arithmetic appendix consists of explicit radical and rational inequalities;
its identities, comparisons, and ordinary mean-value argument can be checked
directly. Independent review of this replacement is pending.

This is a **conditional terminal theorem**. It assumes the named signed
separators, frame lifts, small aligned mismatch and projected-slider bounds.
It does not prove that every unrestricted packing has those properties.
The remaining global hand-proof requirements are recorded in the
[gated roadmap](GATED_ROADMAP_2026_10_16.md).

## 1. The comparison family and its derivatives

Use the family coordinates

\[
\begin{aligned}
x_1&=\sqrt{q-y^2},&
x_2&=\sqrt{q-(y+2)^2},&
x_3&=x_2-3,\\
y_3&=\sqrt{q-x_3^2},&
y_4&=y_3-2,&
x_4&=-\sqrt{q-y_4^2},\\
c&=\frac{1-z^2}{1+z^2},&
s&=\frac{2z}{1+z^2},&
t&=2\arctan z,\\
h_1&=cx_1+sy-2-c,&
h_2&=-sx_4+cy_4-1-s,&
F&=h_1^2+h_2^2-q .
\end{aligned}
\tag{1}
\]

Throughout the calculation,

\[
\frac{7831}{2000}\le q\le\frac{9789}{2500},\qquad
\frac1{20}\le z\le\frac{81}{1000},\qquad
-\frac{937}{1000}\le y\le-\frac{179}{200}.
\tag{2}
\]

Subscripts y and t denote partial derivatives with the other coordinate
fixed. The complete derivative rules needed below are

\[
\begin{aligned}
x_{1y}&=-y/x_1,&x_{1yy}&=-q/x_1^3,\\
x_{2y}&=-(y+2)/x_2,&x_{2yy}&=-q/x_2^3,\\
y_{4y}&=-x_3x_{2y}/y_3,&
y_{4yy}&=-q x_{2y}^2/y_3^3-x_3x_{2yy}/y_3,\\
x_{4y}&=-y_4y_{4y}/x_4,&
x_{4yy}&=-q y_{4y}^2/x_4^3-y_4y_{4yy}/x_4,\\
h_{1y}&=cx_{1y}+s,&h_{1yy}&=cx_{1yy},\\
h_{2y}&=-sx_{4y}+cy_{4y},&
h_{2yy}&=-sx_{4yy}+cy_{4yy},\\
h_{1t}&=-s(x_1-1)+cy,&h_{1tt}&=-h_1-2,\\
h_{2t}&=-c(x_4+1)-sy_4,&h_{2tt}&=-h_2-1 .
\end{aligned}
\tag{3}
\]

Thus

\[
\begin{aligned}
F_{yy}/2&=h_{1y}^2+h_1h_{1yy}+h_{2y}^2+h_2h_{2yy},\\
F_{yt}/2&=h_{1t}h_{1y}+h_1(-sx_{1y}+c)
 +h_{2t}h_{2y}+h_2(-cx_{4y}-sy_{4y}),\\
F_{tt}/2&=h_{1t}^2+h_{2t}^2-h_1(h_1+2)-h_2(h_2+1).
\end{aligned}
\tag{4}
\]

There are no transcendental quantities in (1)--(4) after z is chosen.

## 2. Nine rational position brackets and four rectangles

The following are terminating decimals, hence exact rationals. Each row
holds uniformly over the entire q interval in (2). At its lower y endpoint
one has \(F_y<-1/10000\), and at its upper endpoint
\(F_y>1/20000\).

| z | Lower y | Upper y |
|---:|---:|---:|
| 0.050000 | -0.9357 | -0.9356 |
| 0.053875 | -0.9308 | -0.9307 |
| 0.057750 | -0.9259 | -0.9258 |
| 0.061625 | -0.9211 | -0.9209 |
| 0.065500 | -0.9162 | -0.9161 |
| 0.069375 | -0.9114 | -0.9113 |
| 0.073250 | -0.9066 | -0.9065 |
| 0.077125 | -0.9018 | -0.9017 |
| 0.081000 | -0.8971 | -0.8969 |

Direct substitution of (2) into (3)--(4) also gives

\[
\frac{6723}{1000}<F_{yy}<\frac{8637}{1000},\qquad
-\frac{5327}{1000}<F_{yt}<-\frac{423}{100},
\tag{5}
\]

and

\[
\frac{413}{1000}
<h_{2t}-h_{2y}\frac{F_{yt}}{F_{yy}}
<\frac{88}{125}.
\tag{6}
\]

In particular \(F_{yy}>6\), \(F_{yt}<-4\). The signs at the first
and last rows, together with (5), give a unique stationary position
\(y=Y(q,t)\) for every t in the chart. It is increasing in t, since

\[
Y_t=-F_{yt}/F_{yy}>0.
\tag{7}
\]

For k=0,1,2,3 put

\[
z_k=\frac1{20}+\frac{31k}{4000},\qquad
m_k=z_k+\frac{31}{8000}.
\]

The four rectangles are \(z\in[z_k,z_{k+1}]\), with y between the
lower bracket at \(z_k\) and the upper bracket at \(z_{k+1}\).
Equation (7) puts the entire stationary graph in these four rectangles.
The rows at \(m_k\) give its midpoint brackets.

Here and below all arithmetic table entries follow by substituting the
displayed rational intervals into (1)--(4) and the displayed weight formulas.
Products and quotients use their endpoint bounds. A proposed nonnegative
square-root interval [a,b] is checked by \(a^2\le X\le b^2\).
The derivative in the later owner table is the explicit differential
operator

\[
\mathcal L=\partial_t-\frac{F_{yt}}{F_{yy}}\partial_y .
\tag{8}
\]

It is evaluated by the sum, product and quotient rules, and
\((\sqrt X)'=X'/(2\sqrt X)\). These rules specify every comparison in
the small tables; no adaptive subdivision or assumed numerical root is used.

## 3. The exact target lies in the coarse q interval

On the four rectangles the reduced second derivative

\[
C=F_{tt}-F_{yt}^2/F_{yy}
\tag{9}
\]

has the respective lower bounds 0.88, 0.90, 0.92 and 0.94. In particular
\(C>3/4\). At the left endpoint \(F_t<-3211/100000<0\); at the right
endpoint \(F_t>1071/20000>0\). The unique minimum of the stationary
envelope therefore lies inside this chart.

The global family theorem in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md) proves that this is the
unique family minimum in the full admissible strip, and that its value
decreases strictly with q. Here is a short strict lower bound at
\(q_L=7831/2000\), eliminating the need for a tiny isolated root.

Take \(y_0=-4603/5000\) and \(z_0=619/10000\). Successive squaring gives:

| Radical | Lower bound | Upper bound |
|---|---:|---:|
| \(x_1\) | 1.75156947 | 1.75156948 |
| \(x_2\) | 1.65843168 | 1.65843169 |
| \(y_3\) | 1.45454269 | 1.45454271 |
| \(-x_4\) | 1.90209787 | 1.90209788 |

Using the rational c and s in (1), these four intervals give

\[
F(q_L,y_0,t_0)>\frac1{8000},\qquad
|F_y(q_L,y_0,t_0)|<\frac1{2000},\qquad
|F_t(q_L,y_0,t_0)|<\frac1{4000}.
\tag{10}
\]

Write \(M(q,t)=F(q,Y(q,t),t)\). Since \(F_{yy}>6\),

\[
M(q_L,t_0)\ge F(q_L,y_0,t_0)-F_y(q_L,y_0,t_0)^2/12.
\]

The mean-value theorem gives
\(|Y(q_L,t_0)-y_0|\le |F_y(q_L,y_0,t_0)|/6\). Since
\(|F_{yt}|<6\), it follows that

\[
|M_t(q_L,t_0)|<1/4000+1/2000.
\]

Finally \(M_{tt}>3/4\) throughout the chart, so

\[
\begin{aligned}
\min_t M(q_L,t)
&>\frac1{8000}
-\frac1{12\cdot2000^2}
-\frac23\left(\frac1{4000}+\frac1{2000}\right)^2\\
&=\frac{5981}{48000000}>0 .
\end{aligned}
\tag{11}
\]

The exact construction supplies the upper family radius \(q_U=9789/2500\).
Strict radius monotonicity and (11) prove

\[
\boxed{\frac{7831}{2000}<q_*\le\frac{9789}{2500}.}
\tag{12}
\]

Thus all subsequent bounds apply to the exact, globally selected family
radius. At q=q_* the unique stationary minimum t_* lies in the chart
and has value zero. Equation (9) gives

\[
F(q_*,Y(q_*,t),t)\ge\frac38(t-t_*)^2.
\tag{13}
\]

## 4. Positive force weights

Introduce unnormalized quantities

\[
\begin{aligned}
A&=\frac c{2x_1},&
a&=s-\frac{cy}{x_1},&
B&=\frac a{2(y+2)},&
b&=\frac{a x_2}{y+2},\\
D&=-\frac b{2x_3},&
d&=2D y_3,&
H&=-\frac1{2h_1},&
e&=\frac{h_2}{h_1},&
E&=-\frac{se}{2x_4},
\end{aligned}
\]

and set

\[
\omega=\frac1{A+B+D+E+H},\qquad
(\mu_A,\mu_B,\mu_D,\mu_E,\mu_H)=\omega(A,B,D,E,H).
\tag{14}
\]

The seven edge weights are

\[
\lambda_{AB}=\alpha=\omega a,\quad
\lambda_{TB}=\lambda_{DT}=\beta=\omega b,\quad
\lambda_{ED}=\delta=\omega d,\quad
\lambda_{HE}=\epsilon=\omega e,\quad
\lambda_{GA}=\lambda_{HG}=\omega .
\tag{15}
\]

All weights are positive, and the five circle weights sum to one.
On the stationary graph \(F_y=0\), their vector force identities are

\[
\begin{aligned}
2\mu_A P_A&=\omega e_t-\alpha f_0,&
2\mu_B P_B&=\beta e_0+\alpha f_0,\\
2\mu_D P_D&=-\beta e_0+\delta f_0,&
2\mu_E P_E&=\epsilon f_t-\delta f_0,\\
2\mu_H P_H&=-\omega e_t-\epsilon f_t.
\end{aligned}
\tag{16}
\]

Here the selected comparison vertices are
\(P_A=(x_1,y)\), \(P_B=(x_2,y+2)\),
\(P_D=(x_3,y_3)\), \(P_E=(x_4,y_4)\) and
\(P_H=h_1e_t+h_2f_t\). The T and G forces vanish by the equalities
of the two incident weights in (15).

One useful scalar consequence of (16) is

\[
\delta-\epsilon c=\epsilon s\,y_4/x_4>0.
\tag{17}
\]

These are exact algebraic identities, not numerical equalities.

## 5. Why 32 owner choices reduce to nine scalars

Let the reference T height be \(Z\in[29/50,7/5]\), and let
the G offset be \(\eta\in[-1/2,37/100]\). Define

\[
\begin{gathered}
Y=x_1-x_2,\qquad J=\frac{\epsilon c}{\beta}-\frac{y_3x_4}{x_3},\\
X=\beta(y+2+J),\qquad K=\beta(y_3+J),\\
L=\epsilon s\,y_4/x_4,\qquad
N=-\epsilon(h_1+h_{2t}).
\end{gathered}
\tag{18}
\]

The elementary coordinate bounds give \(0<Y<1\), \(x_4-x_3<0\),
and \(\alpha<\beta\). Identities (15)--(17) give

\[
K=\epsilon c+\delta(x_4-x_3),\qquad L=\delta-\epsilon c.
\tag{19}
\]

Set the actual A frame to zero, and use the actual G frame for t.
For the remaining five frame errors a_i take the tree differences

\[
\Delta_{AB}=-a_B,\quad
\Delta_{TB}=a_T-a_B,\quad
\Delta_{DT}=a_D-a_T,\quad
\Delta_{ED}=a_E-a_D,\quad
\Delta_{HG}=a_H.
\]

Their absolute values sum to S. After the exact center forces cancel,
the smooth angular term is \(\sum c_e\Delta_e\), and the aligned support
cusps contribute \(\sum(\lambda_e/2)|\Delta_e|\).
For each edge, its cut coefficient depends only on that edge's owner:
both ends of every other aligned edge lie on the same side of its tree cut.

Expanding (16) gives the entire owner table:

| Edge | The two possible smooth coefficients |
|---|---|
| AB | \(-\alpha/2+X\); \(-\alpha/2+X+\alpha Y\) |
| TB | \(-\beta(Z+J)\); \(-\beta(y+3/2+J)\) |
| DT | \(\beta/2-K\); \(-\beta(Z+J)\) |
| ED | \(\delta/2-\epsilon c\); \(\delta/2-\epsilon c-\delta(x_4-x_3)\) |
| HG | \(-\omega/2+N\); \(-\omega/2+N-\omega\eta\) |

For example, the ED cut contains E alone. Its vertex and mixed-edge
smooth terms simplify, using (17), to \(\delta/2-\epsilon c\).
The choice of E as the ED owner subtracts
\(\delta(x_4-x_3)\). Adding the D cut uses
\(\delta x_3=-\beta y_3\) and gives the displayed DT alternatives.
Adding T gives TB, and the B cut gives AB. The H cut uses
\(\mu_Hh_1=-\omega/2\), \(\mu_Hh_2=-\epsilon/2\), yielding HG.
Thus the table covers all 32 assignments without enumerating them.

The following nine lower bounds suffice for every owner reserve:

\[
\begin{array}{lll}
V_1=X,&V_2=\alpha(1-Y)-X,&V_3=K,\\
V_4=\beta-K,&V_5=\beta(-9/10-J),&
V_6=\beta(27/25+J),\\
V_7=L,&V_8=N-(37/100)\omega,&V_9=\omega/2-N.
\end{array}
\tag{20}
\]

Indeed, AB follows from V_1,V_2. The varying T height in TB/DT is
controlled by V_5,V_6; its other DT choice uses V_3,V_4.
The remaining TB choice has reserves X and \(\beta-X\), and
\(\beta-X>\alpha(1-Y)-X\). The ED reserves follow from V_3,V_7
and \(\epsilon c>K\). The full G interval follows from V_8,V_9.
Consequently

\[
V_j>\rho\ (j=1,\ldots,9)
\quad\Longrightarrow\quad
\lambda_e/2-|c_e|>\rho
\tag{21}
\]

for all five edges, all slider values, and every owner assignment.

## 6. Nine short mean-value bounds

For each V_j, the table gives a lower bound C_j at all four midpoints
\(z=m_k\), using their displayed y brackets. It also gives an upper
bound D_j for \(|\mathcal L V_j|\) on all four closed rectangles.
Every number is rational.

| j | C_j | D_j | C_j − (31/4000)D_j |
|---:|---:|---:|---:|
| 1 | 0.0345 | 2.04 | 0.0186900 |
| 2 | 0.3633 | 2.16 | 0.3465600 |
| 3 | 0.3211 | 1.27 | 0.3112575 |
| 4 | 0.4102 | 1.51 | 0.3984975 |
| 5 | 0.0760 | 1.53 | 0.0641425 |
| 6 | 0.0425 | 1.52 | 0.0307200 |
| 7 | 0.0238 | 0.26 | 0.0217850 |
| 8 | 0.0371 | 0.33 | 0.0345425 |
| 9 | 0.0549 | 0.35 | 0.0521875 |

Since \(dt/dz=2/(1+z^2)\le2\), the distance in t from any point
of one rectangle to its midpoint is at most \(31/4000\).
Therefore the ordinary mean-value theorem gives

\[
V_j\ge C_j-\frac{31}{4000}D_j>\frac9{500}
\qquad(j=1,\ldots,9).
\tag{22}
\]

The smallest displayed lower bound is 0.01869, strictly larger than 0.018.
Thus the first-order angular reserve is at least \(9S/500\) for
every one of the 32 owner assignments and the full slider rectangle.

## 7. Remaining uniform constants

For an anchored square set
\(b_i=2\mu_i+\sum_{e\ni i}\lambda_e\). Substitution into (14)--(15)
on the same four rectangles gives:

| Rectangle | Reduced curvature > | Young sum < | Minimum circle weight > | Maximum edge weight < |
|---:|---:|---:|---:|---:|
| 1 | 0.88 | 106.2 | 0.0195 | 0.8418 |
| 2 | 0.90 | 96.1 | 0.0223 | 0.8340 |
| 3 | 0.92 | 88.4 | 0.0250 | 0.8263 |
| 4 | 0.94 | 82.3 | 0.0276 | 0.8188 |

In particular, every circle weight exceeds 19/1000,
every edge weight is less than 17/20, their total is less than 26/5,
and

\[
\sum_i \frac{b_i^2}{2\mu_i}<110.
\tag{23}
\]

The reference neighbor vectors and the two reference slider centers have
squared norm less than 3 throughout the entire box (2) and the full slider
rectangle. This follows directly from the reference formulas

\[
\begin{aligned}
p_A^0&=(x_1-1/2,y+1/2),&
p_B^0&=(x_2-1/2,y+3/2),\\
p_D^0&=(x_3+1/2,y_3-1/2),&
p_E^0&=(x_4+1/2,y_4+1/2),\\
p_H^0&=(h_1+1/2)e_t+(h_2+1/2)f_t,\\
p_T^0&=(x_2-3/2,Z),&
p_G^0&=p_H^0+e_t+\eta f_t .
\end{aligned}
\tag{24}
\]

For clarity, convenient outer bounds from (1)--(2) are

\[
\begin{gathered}
1.7428<x_1<1.7649,\quad 1.6414<x_2<1.6691,\\
1.4387<y_3<1.4643,\quad -1.9049<x_4<-1.8974,\\
-1.4263<h_1<-1.3198,\quad -1.5316<h_2<-1.3202.
\end{gathered}
\tag{25}
\]

Bounding the four corners of the affine slider rectangle suffices for the
norm bounds, by convexity. The five reference selected vertices also have
norm less than 2: four have squared norm q<4. For H,
\(h_1^2+h_2^2=q+M(q,t)\) is convex in t by (9), so its maximum is at
a chart endpoint. At the endpoints its upper bounds are, respectively,
3.91619 and 3.91703, both less than 4.

Equation (6) makes the stationary h_2 increasing. Its endpoint enclosures are

\[
-1.44369<h_2(z=1/20)<-1.44356,\qquad
-1.40827<h_2(z=81/1000)<-1.40806.
\]

Consequently \(-29/20<h_2<-7/5\) on the entire stationary graph,
as required by the projected-slider interfaces.

## 8. The nonlinear terminal inequality

Assume the actual seven squares lie in a disk of squared radius r≤4,
have the named signed separators of
[CENTER_FREE_PROJECTED_SLIDER_REMAINDER.md](CENTER_FREE_PROJECTED_SLIDER_REMAINDER.md),
satisfy \(1/10\le t\le4/25\), and have \(S\le1/10000\).
The actual projected coordinates satisfy
\(Z=(p_T)_y\in[29/50,7/5]\) and
\(\eta=(p_G-p_H^0-e_t)\cdot f_t\in[-1/2,37/100]\).
These are the hypotheses that the global argument must establish.

The actual tilt interval is contained in the rational z chart used above:
\(\tan(1/20)>1/20\), while the elementary sine and cosine bounds give

\[
\tan(2/25)
\le\frac{2/25}{1-(2/25)^2/2}
=\frac{50}{623}<\frac{81}{1000}.
\]

Thus \(z=\tan(t/2)\) lies between \(1/20\) and \(81/1000\)
whenever \(1/10\le t\le4/25\).

Choose the comparison at q=q_*, t equal to the actual G frame, and the
two sliders from these actual projections. Then

\[
d_T=p_T-p_T^0=\tau e_0,\qquad d_G=p_G-p_G^0=\upsilon e_t.
\tag{26}
\]

For the five actual selected vertices and seven actual nonnegative signed
gaps g_e, the positive weighted dual satisfies

\[
r\ge\sum_i\mu_i|p_i+o_i|^2-\sum_e\lambda_e g_e .
\]

At the comparison it equals \(q_*+\mu_HF\). The exact force equations
(16) cancel every term linear in a center displacement.

The elementary rotation estimates
\(|R(a)v-v|\le|a||v|\) and
\(|R(a)v-v-aJv|\le a^2|v|/2\) give a pure angular loss at most
12S², including all true support widths and their aligned cusps.
Young's inequality and (23) absorb the anchored center/angle terms into
half of the positive center squares and at most 110S².

Both actual slider centers have norm at most 2, while (24)--(25) put both
reference slider centers inside the radius-2 disk. Thus
\(|d_T|,|d_G|<4\). By (26),

\[
(R(a)n-n)\cdot(\xi n)=\xi(\cos a-1).
\]

The two T incidences consequently lose less than 4S², and the two G
incidences lose less than 4S²; the GA term is in fact zero because its
normal defines the reference tilt. The total slider loss is at most 8S².

Combining (13), (22), and these three remainder bounds gives

\[
\begin{aligned}
r\ge q_*&
+\frac{3\mu_H}{8}(t-t_*)^2
+\frac12\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2\\
&+\left(\frac9{500}-130S\right)S\\
\ge q_*&
+\frac{3\mu_H}{8}(t-t_*)^2
+\frac12\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2
+\frac1{200}S
\ge q_* .
\end{aligned}
\tag{27}
\]

This is the same full-slider, arbitrary-center terminal mechanism as the
completed computer-assisted assembly, now reduced to the explicit small
arithmetic appendix above. Equality in this terminal requires
\(t=t_*\), \(S=0\), and equality of all five anchored centers.
The two chosen slider coordinates remain free.

The unrestricted hand proof still requires analytic derivation of the
global contact/owner and capture hypotheses. The central core has its separate hand proof in
[HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md](HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md). Equation (27)
does not supply those global hypotheses by itself.


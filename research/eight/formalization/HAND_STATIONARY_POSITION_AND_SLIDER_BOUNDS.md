# Stationary position and slider coefficient on the whole terminal interval

## Statement and scope

Let

\[
 3.9154\le q\le Q=3.9156,\qquad .1\le h=\tan t\le .164.
 \tag{1}
\]

The actual nested-circle family in
[the stationary-existence proof](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
has a unique position minimizer \(u=u(q,t)\). This note proves

\[
 \boxed{.895<u(q,t)<1-.6\tan t},\qquad
 \boxed{-1.029<J(q,t)<-.98}.                         \tag{2}
\]

Here \(J\) is the slider coefficient of the terminal equilibrium stress,
defined explicitly below. These bounds hold throughout (1); they use the
actual stationarity equation, one affine comparison curve, and whole-domain
derivative inequalities. No subdivision of the position, tilt, or radius
interval is used. All decimals are exact rational numbers.

The existence proof places the sharp radius \(q_*\) strictly between
\(3.9154\) and \(Q\). Also \(.1\le t\le .16\) implies
\(.1\le\tan t\le .164\), by the elementary sine and cosine bounds.
Thus (2) applies throughout the conditional sharp terminal theorem.
It supplies no global word or mismatch-capture premise.

## 1. Actual circle coordinates and derivatives

Use positive square roots and set

\[
\begin{aligned}
 r&=\sqrt{q-u^2},& l&=2-u,& U&=\sqrt{q-l^2},\\
 V&=3-U,& Y&=\sqrt{q-V^2},& v&=2-Y,\\
 w&=\sqrt{q-v^2},& c&=(1+h^2)^{-1/2},&s&=hc.
\end{aligned}                                                       \tag{3}
\]

These are the actual radical coordinates, not independent fitted
variables. In particular the first component of the second corner is
\(l=2-u\), not \(u\). Define

\[
\begin{aligned}
 p&=\frac{lV}{UY},&
 Z&=\frac{q}{lU^2}+\frac{pq}{YV^2},\\
 a&=s+\frac{cu}{r},&
 b&=p\left(c+\frac{sv}{w}\right),\\
 k_1&=2-c(r-1)+su,&
 k_2&=1+cv-s(w-1),\\
 F(q,u,t)&=k_1^2+k_2^2-q.
\end{aligned}                                                       \tag{4}
\]

The existence proof establishes strict convexity \(F_{uu}>0\) on the
larger actual position interval \([.87,1.1]\), with opposite derivative
signs at its ends. Its unique minimizer therefore satisfies \(F_u=0\).
For the sharper bounds needed here, differentiate (3) directly:

\[
 r_u=-u/r,\quad U_u=l/U,\quad V_u=-l/U,\quad
 Y_u=p,\quad v_u=-p,\quad w_u=pv/w,\quad p_u=-pZ.
 \tag{5}
\]

Consequently \((k_1)_u=a\), \((k_2)_u=-b\), and
\(F_u=2(k_1a-k_2b)\). Put

\[
 d=s(r-1)+cu,\quad e=c(w-1)+sv,\quad
 a_t=c-su/r,\quad b_t=p(-s+cv/w).
\]

The two derivatives used below are the exact identities

\[
\begin{aligned}
 F_{uu}={}&2\left[a^2+b^2+\frac{k_1cq}{r^3}
 +k_2\left\{pZ\left(c+\frac{sv}{w}\right)
                      +\frac{sp^2q}{w^3}\right\}\right],\\
 F_{ut}={}&2(da+k_1a_t+eb-k_2b_t).
\end{aligned}                                                       \tag{6}
\]

All denominators in (3)--(6) are positive on the stated domains.

## 2. A uniform derivative bound along an affine comparison curve

Consider \(u_0(h)=1-.6h\). Its full range on (1) is
\([.9016,.94]\). We may therefore bound (6) on the single larger
rectangle

\[
 3.9154\le q\le3.9156,\quad
 .9016\le u\le.94,\quad .1\le h\le.164.             \tag{7}
\]

For clarity, the elementary arithmetic in this estimate can be performed
as follows. If \(u\in[A,B]\), set

\[
\begin{aligned}
 r_-^2&=3.9154-B^2,&r_+^2&=3.9156-A^2,\\
 U_-^2&=3.9154-(2-A)^2,&U_+^2&=3.9156-(2-B)^2,\\
 V_-&=3-U_+,&V_+&=3-U_-,\\
 Y_-^2&=3.9154-V_+^2,&Y_+^2&=3.9156-V_-^2,\\
 v_-&=2-Y_+,&v_+&=2-Y_-,\\
 w_-^2&=3.9154-v_+^2,&w_+^2&=3.9156-v_-^2.
\end{aligned}                                                       \tag{8}
\]

Every root is positive, so squaring verifies any chosen rational upper
or lower bound. With \(A=.9016,B=.94\), equations (8) give

\[
\begin{gathered}
 1.741206476<r<1.761453221,\quad
 1.645878924<U<1.670927888,\\
 1.329072112<V<1.354121076,\quad
 1.442829201<Y<1.466003864,\\
 .533996136<v<.557170799,\quad
 1.898673403<w<1.905373490.
\end{gathered}                                                       \tag{9}
\]

For the trigonometric factors, it suffices to use
\(.986817330<c<.995037193\) and
\(.098681733<s<.163186100\). Substitute these bounds and (9) into
the positive products and quotients of (4), then into (6). The only
negative summand in \(F_{ut}/2\) is \(-k_2b_t\), and \(b_t>0\).
The resulting strict rational estimates, rounded outwards, are

\[
 \boxed{6.74<F_{uu}<8.5},\qquad
 \boxed{4.29<F_{ut}<5.29}.                          \tag{10}
\]

For direct reproduction of these substitutions, intermediate bounds are
\(.57512412<p<.62633290\),
\(2.1144315<Z<2.3258885\),
\(.60378427<a<.70036247\),
\(.58344828<b<.65321798\),
\(1.33129717<k_1<1.42195955\), and
\(1.37921226<k_2<1.46572303\).
In the second formula of (6), one may use
\(.96285803<d<1.05959356\),
\(.93952214<e<.99180284\),
\(.89872039<a_t<.94452696\), and
\(.06520602<b_t<.12107931\).
The reserves in (10) exceed the rounding losses in all these displayed
bounds. These are single algebraic comparisons over (7); their validity
does not depend on any intermediate sample or numerical search.

Define \(f(h)=F_u(q,u_0(h),\arctan h)\), with \(q\) fixed.
The chain rule, including \(dt/dh=1/(1+h^2)\), gives

\[
 f'(h)=-.6F_{uu}+\frac{F_{ut}}{1+h^2}.
\]

Thus (10) implies

\[
 -.93<-.6(8.5)+\frac{4.29}{1+.164^2}
       <f'(h)
       <-.6(6.74)+\frac{5.29}{1+.1^2}<1.2.         \tag{11}
\]

At the single pivot \(h=.13\), \(u_0=.922\), direct substitution
in \(F_u=2(k_1a-k_2b)\) gives, for every radius in (1),

\[
 .0366393<F_u(q,.922,\arctan .13)<.0372351.
 \tag{12}
\]

For example, (8) at this fixed position yields
\(1.750804384<r<1.750861505\),
\(1.659311903<U<1.659372173\),
\(1.455319697<Y<1.455443931\), and
\(1.902294235<w<1.902382374\);
also \(.991655614<c<.991655620\). These rational squared
comparisons and (4) imply (12) directly.

For \(h\le.13\), integrate the upper derivative bound in (11);
for \(h\ge.13\), integrate its lower bound. This proves respectively

\[
 f(h)>.0366-1.2(.03)=.0006>0,
 \qquad
 f(h)>.0366-.93(.034)=.00498>0.
\]

Hence \(F_u>0\) on the entire affine curve. Strict convexity of
\(F\) in its actual position variable proves

\[
 u(q,t)<1-.6h.                                      \tag{13}
\]

## 3. The lower position endpoint

At the fixed position \(u=.895\), the same formulas (3)--(6) give
\(F_{ut}>4.39\) for the whole radius and tilt intervals (1).
At their upper tilt endpoint, substitution gives

\[
 -.0118268<F_u(q,.895,\arctan .164)<-.0111848<-.011.
 \tag{14}
\]

Here the positive roots obey
\(1.764759188<r<1.764815857\),
\(1.641455145<U<1.641516070\),
\(1.438664613<Y<1.438791652\),
\(1.897446330<w<1.897536614\), and
\(.986817330<c<.986817336\). Equations (4) and (6), using (8)
with \(A=B=.895\), give both claimed derivative bounds by rational
arithmetic. Since \(F_u\) increases with \(t\) at this fixed
position, (14) makes it negative throughout (1). Strict convexity now
implies \(u(q,t)>.895\), completing the first bound in (2).

## 4. Stationarity simplifies the slider coefficient exactly

Write the unnormalized equilibrium weights as

\[
 \alpha=a,\quad \beta=\frac{aU}{l},\quad
 \delta=\frac{\beta Y}{V},\quad
 \epsilon=\frac{k_2}{k_1}.
\]

The defining slider coefficient is
\(J=\epsilon c/\beta-Yw/V\). At the actual position minimum,
\(F_u=0\) says

\[
 a=\epsilon p(c+sv/w),\qquad
 \delta=\frac{a}{p}=\epsilon(c+sv/w).
\]

Substitute this equality before estimating \(J\). With

\[
 C=\frac1{1+hv/w},\qquad K=\frac YV,
\]

it becomes the exact identity

\[
 \boxed{J=K(C-w)}.                                  \tag{15}
\]

The letter \(\beta\) in this section denotes the unnormalized edge
weight; it is unrelated to a width-penalty coefficient in the frame
proof. A common normalization of all stress weights does not change
\(J\).

## 5. Two monotonicity statements and a positive derivative on the curve

On the entire enlarged rectangle \(.895\le u\le.94\), (3) gives
\(v>.53\), \(w>1.89\), and \(w>C\), since \(0<C<1\).
The identities (5) imply

\[
 \frac{K_u}{K}=\frac{pq}{YV^2}>0,
 \qquad
 (w-C)_u=\frac p w\left(v-\frac{hqC^2}{w^2}\right)>0.
\]

For the last sign, it is enough that
\(.53-.164(4)/1.89^2>0\). Thus \(J=-K(w-C)\) strictly
decreases with \(u\). At fixed \(u\), it also strictly decreases
with \(h\), because

\[
 J_h=-K\frac{vC^2}{w}<0.                            \tag{16}
\]

It remains to control the lower bound along \(u=u_0(h)\).
Differentiate (15) along that curve, retaining the correlation between
position and tilt. The exact result is

\[
 \frac1K\frac{d}{dh}J(q,u_0(h),\arctan h)
 =.6p\left[\frac{q(w-C)}{YV^2}
                   +\frac vw-\frac{hqC^2}{w^3}\right]
                   -\frac{C^2v}{w}.                \tag{17}
\]

On this curve (9) allows the coarse bounds
\(p>.57\), \(q>3.9\), \(1.89<w<1.91\),
\(Y<1.47\), \(V<1.36\), and \(.53<v<.56\).
Since \(C<1\), the right side of (17) is greater than

\[
\begin{aligned}
 .6(.57)\left[
 \frac{3.9(.89)}{1.47(1.36)^2}
 +\frac{.53}{1.91}-\frac{.164(4)}{1.89^3}\right]
 -\frac{.56}{1.89}
 &=\frac{33452740020121}{165628132236000}\\
 &>\frac15>0.
\end{aligned}                                                       \tag{18}
\]

Thus the value on the affine comparison curve increases with \(h\).
By (13) and monotonicity in \(u\), the actual stationary value is
strictly larger than that curve's value, hence larger than its value
at \(h=.1,u=.94\). The upper bound uses the opposite endpoint
\(u=.895,h=.1\) and both monotonicity statements.

At these two fixed points, (3) and (15) give uniformly in \(q\)

\[
\begin{aligned}
 J(q,.94,\arctan .1)&>-1.028731>-1.029,\\
 J(q,.895,\arctan .1)&<-.980793<-.98.
\end{aligned}                                                       \tag{19}
\]

These follow by the same positive-root bounds (8), using the exact
\(c=1/\sqrt{1.01}\); in fact (15) itself no longer involves \(c\).
Only squaring positive rational bounds, multiplication, and division
are needed. Combining (13), (15)--(19) proves the second assertion
of (2) on the complete terminal domain.

## 6. Consequence for the owner reserves

The normalized edge weight, again denoted \(\beta>0\), multiplies
three formerly delicate enlarged reserves as

\[
 \beta(l+J),\qquad \beta(-.917-J),\qquad
 \beta(1.057+J).
\]

Because \(u<.94\), the estimates just proved give respectively
the strict lower bounds \(.031\beta\), \(.063\beta\), and
\(.028\beta\). This is a whole-interval use of the actual stationary
equations. The remaining equilibrium weights, reserves, Taylor
remainders, and automatic slider bounds are separate ingredients of
the terminal assembly.

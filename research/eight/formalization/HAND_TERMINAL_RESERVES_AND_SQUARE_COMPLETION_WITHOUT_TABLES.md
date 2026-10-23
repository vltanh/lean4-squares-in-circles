# The complete conditional terminal without arithmetic tables

**Status.** This note proves the stationary force-weight bounds, all
nine owner reserves on the enlarged automatic-slider rectangle, and
the exact square-completion remainder on their whole continuous
domains. It replaces the numerical rectangle inputs of
`../HUMAN_BROAD_TERMINAL_ARITHMETIC.md`,
`../HAND_EXACT_CENTER_SQUARE_COMPLETION.md`, and
`../HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md`.

The only position input is the whole-domain argument in
`HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md`. The existence and
uniqueness of the stationary minimum come from
`HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md`. In particular,
neither a uniform reduced-curvature table nor a numerical isolated
root is needed. All terminating decimals below are exact rationals.

## 1. Conditional sharp theorem

Consider seven exterior unit squares in a centered disk of squared
radius \(r_0\le Q_0=9789/2500\), each avoiding the open disk of
radius \(1/12\). Give them the cyclic roles

\[
 (H,G,A,B,T,D,E)
\]

and canonical quarter offsets \((-1,-1,0,0,1,1,2)\). Normalize
A's actual frame to zero and G's actual frame to \(t\). Assume

\[
 \frac1{10}\le t\le\frac4{25},\qquad
 S=|a_B|+|a_T-a_B|+|a_D-a_T|+|a_E-a_D|+|a_H|
 \le\frac1{1000}.                                    \tag{1}
\]

Here \(a_B,a_T,a_D,a_E\) are the actual frame errors from zero,
and \(a_H\) is H's error from the G frame. Assume actual signed
separation on the following seven edges, with either indicated
owner allowed independently:

* A to B: the positive \(f\)-axis of A or B;
* T to B and D to T: the positive \(e\)-axis of either endpoint;
* E to D: the positive \(f\)-axis of E or D;
* G to A: G's positive \(e\)-axis;
* H to G: the positive \(e\)-axis of H or G;
* H to E: H's positive \(f\)-axis.

These are the original signed witnesses, including their possible
ties. There are \(2^5\) assignments of the five aligned owners.

Let \(q_*\) be the unique stationary minimum radius proved in
`HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md`. At this actual \(t\), use its unique stationary position
\(u=u(q_*,t)\) and the
positive normalized force weights defined below. Write

\[
 M(q_*,t)=F(q_*,u(q_*,t),t).
\]

Then the actual squares satisfy

\[
 \boxed{
 r_0\ge q_*+\mu_H M(q_*,t)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{S}{500}\ge q_*.}                              \tag{2}
\]

The actual selected corner offsets \(o_i\) and center forces \(F_i\)
are those specified in Section 7 below. The stationary existence
theorem gives

\[
 M(q_*,t)\ge0,
 \qquad M(q_*,t)=0\Longleftrightarrow t=t_* .           \tag{3}
\]

Thus equality in the sharp radius conclusion forces \(S=0\), \(t=t_*\), and the five completed center squares
to vanish. At zero
errors these are exactly the displacements from the five stationary
anchors. The remaining slider freedom is subject to the actual
packing inequalities. No projected-slider or signed-tangent bound
is an additional hypothesis of (2).

This is a conditional terminal theorem. Proving that every
unrestricted packing enters the owner, tilt, and mismatch domain
(1) remains a separate global capture problem.

## 2. One stationary rectangle and explicit primitive bounds

For this section and the force estimates, work on

\[
 3.9154\le q\le3.9156,\qquad
 .895\le u\le.94,\qquad .1\le h\le.164,
 \qquad t=\arctan h.                                 \tag{4}
\]

The application lies in this domain: the stationary construction has

\(3.9154<q_*<3.915534138\), and (1) gives

\[
 .1<\tan t\le\frac{.16}{1-.16^2/2}
       =\frac{100}{617}<.164.
\]

Use the actual positive radicals

\[
 \begin{gathered}
 r=\sqrt{q-u^2},\qquad U=\sqrt{q-(2-u)^2},\qquad V=3-U,\\
 Y=\sqrt{q-V^2},\qquad v=2-Y,\qquad w=\sqrt{q-v^2},\\
 c=(1+h^2)^{-1/2},\qquad s=hc,\\
 k_1=2-c(r-1)+su,\qquad k_2=1+cv-s(w-1),
 \qquad F=k_1^2+k_2^2-q.
 \end{gathered}                                       \tag{5}
\]

The translation to the older comparison coordinates is

\[
 (x_1,x_2,x_3,y_3,y_4,x_4,y,h_1,h_2)
 =(r,U,-V,Y,-v,-w,-u,-k_1,-k_2).                      \tag{6}
\]

Repeated squaring on the single rectangle (4) gives

\[
 \begin{gathered}
 1.741<r<1.765,\quad1.641<U<1.671,
 \quad1.329<V<1.359,\\
 1.438<Y<1.467,\quad .533<v<.562,
 \quad1.897<w<1.906,\\
 .9868<c<.9951,\qquad .0995<s<.162.                   \tag{7}
 \end{gathered}
\]

For clarity, the successive radicands are bounded respectively by

\[
 \begin{gathered}
 3.0318\le r^2\le3.114575,\qquad
 2.694375\le U^2\le2.792,\\
 2.068519<Y^2<2.149359,\qquad
 3.599556<w^2<3.631511.
 \end{gathered}
\]

The weak versions at extreme endpoints suffice for every strict
enclosure in (7). The sine bound uses the monotonicity of

\(h/\sqrt{1+h^2}\); for example \(\(.0995\)^2<1/101\).
No subdivision of (4) is being made.

Set

\[
 p=\frac{(2-u)V}{UY},\quad
 a=s+\frac{cu}{r},\quad
 b=p\left(c+\frac{sv}{w}\right),\quad
 E=c(w-1)+sv.                                         \tag{8}
\]

The letters \(a,b\) in (8) are derivatives, not square-center
coordinates. Direct positive-product bounds from (7) give

\[
 \begin{gathered}
 .574<p<.637,\quad .599<a<.700,\quad .582<b<.665,\\
 1.327<k_1<1.422,\quad1.379<k_2<1.470,
 \quad .938<E<.993.                                  \tag{9}
 \end{gathered}
\]

The stationary-position theorem proves, on the entire \(q,h\)
domain in (4),

\[
 .895<u(q,t)<1-.6h\le.94,
 \qquad F_u(q,u(q,t),t)=0,                             \tag{10}
\]

and the exact scalar identity and bounds

\[
 J=\frac{Y}{V}
       \left(\frac1{1+hv/w}-w\right),
 \qquad -1.029<J<-.98.                               \tag{11}
\]

Only (10)--(11) from that note are imported below.

## 3. Positive force weights with one normalization estimate

Define the unnormalized weights

\[
 A=\frac{c}{2r},\qquad
 B=\frac{a}{2(2-u)},\qquad
 \mathfrak b=\frac{aU}{2-u},\qquad
 D=\frac{\mathfrak b}{2V},
\]
\[
 H=\frac1{2k_1},\qquad e=\frac{k_2}{k_1},\qquad
 E_0=\frac{se}{2w},\qquad
 \omega=\frac1{A+B+D+H+E_0}.                          \tag{12}
\]

The normalized circle weights are

\[
 (\mu_A,\mu_B,\mu_D,\mu_E,\mu_H)
       =\omega(A,B,D,E_0,H),
\]

and the edge weights are

\[
 \alpha=\omega a,\quad\beta=\omega\mathfrak b,
 \quad\delta=\beta\frac{Y}{V},\quad
 \epsilon=\omega e,
 \quad\lambda_{GA}=\lambda_{HG}=\omega.              \tag{13}
\]

All are positive and the five circle weights sum to one. Substituting
(7)--(9) in the single denominator

\[
 \omega^{-1}=\frac{c}{2r}+
 a\left(\frac1{2(2-u)}+\frac{U}{2(2-u)V}\right)
 +\frac1{2k_1}+\frac{s k_2}{2wk_1}
\]

gives

\[
 \frac54<\omega^{-1}<\frac32,
 \qquad \boxed{\frac23<\omega<\frac45}.              \tag{14}
\]

There is a useful cancellation in the bound for \(\beta\).
Stationarity gives \(k_1a=k_2b\), whence

\[
 \mathfrak b=\frac{k_2}{k_1}\frac{V}{Y}
                    c(1+hv/w).
\]

Dividing the five terms in (12) by \(\mathfrak b\) therefore
gives the exact identity

\[
 \begin{split}
 \beta^{-1}={}&\frac{2-u}{2U(u+hr)}+\frac1{2U}+\frac1{2V}\\
 &+\frac{Y}{2k_2Vc(1+hv/w)}
   +\frac{hY}{2V(w+hv)}.
 \end{split}                                          \tag{15}
\]

Every summand is positive. The same primitive bounds place their
sum strictly between \(1.293\) and \(1.439\): for instance the five
individual lower bounds \(.257,.299,.367,.344,.026\) and upper
bounds \(.315,.305,.377,.395,.047\) follow immediately by
multiplication of the positive endpoints in (15). This is one
explicit rational inequality over (4), not a varying-domain check.
Consequently

\[
 \boxed{.69<\beta<.78}.                               \tag{16}
\]

The remaining ratios are particularly simple:

\[
 \frac\alpha\beta=\frac{2-u}{U}<.674,
 \qquad\frac\delta\beta=\frac{Y}{V}<1.104,
 \qquad
 1<\frac\epsilon\beta=
       \frac{Y}{Vc(1+hv/w)}<1.09.                     \tag{17}
\]

Thus every one of the seven edge weights is strictly less than

\[
 \boxed{\Lambda=87/100}.                              \tag{18}
\]

For later positivity, all circle weights also exceed \(1/60\).
The smallest coarse lower bound is the E bound,

\[
 \mu_E>\frac23\frac{.0995(1.379)}{2(1.906)(1.422)}
 >\frac1{60};                                        \tag{19}
\]

the other four lower substitutions in (12) exceed \(.18\).

## 4. A monotonicity proof for the difficult H reserve

Put

\[
 n=\frac N\omega=k_2\left(1-\frac E{k_1}\right).
\]

We prove the whole-rectangle bounds

\[
 \boxed{.41<n<.44}.                                  \tag{20}
\]

This proof does not require stationarity until the bounds are applied
to its graph.

### 4.1 Monotonicity in position

The elementary derivative identities are

\[
 k_{1u}=a,\qquad k_{2u}=-b,\qquad
 E_u=p(cv/w-s).
\]

Hence

\[
 n_u=-b(1-E/k_1)-\frac{k_2p}{k_1}(cv/w-s)
                  +\frac{k_2Ea}{k_1^2}.              \tag{21}
\]

All factors needed for the following lower bound have the displayed
positive signs by (7)--(9). Substitution gives

\[
 \begin{split}
 n_u>{}&-.665\left(1-\frac{.938}{1.422}\right)\\
 &-\frac{1.470}{1.327}(.637)
          \left(\frac{.9951(.562)}{1.897}-.0995\right)
 +\frac{1.379(.938)(.599)}{1.422^2}
 >\frac1{100}.
 \end{split}                                          \tag{22}
\]

Thus the lower and upper tests for (20) need only be made at

\(u=.895\) and \(u=.94\), respectively, while \(q\) and \(h\)
retain their complete domains.

### 4.2 Two endpoint functions, each on the entire \(h\) interval

For a proposed bound \(m\), set \(R_1=r-1,W_1=w-1\), and define

\[
 \begin{array}{ll}
 L_0=-(1-m)R_1-W_1+2v,&
 L_1=(1-m)u-v-2W_1,\\
 Q_0'=-v(R_1+W_1),&
 Q_1'=W_1(R_1+W_1)+v(u-v),\\
 Q_2'=-W_1(u-v).&
 \end{array}
\]

Expanding the definition of \(n\) gives the exact identity

\[
 \begin{split}
 P_m(h)&:=(1+h^2)k_1(n-m)\\
 &=2(1-m)(1+h^2)+\sqrt{1+h^2}(L_0+hL_1)
       +Q_0'+hQ_1'+h^2Q_2'.
 \end{split}                                          \tag{23}
\]

Let

\[
 \begin{gathered}
 p_0=2(1-m)+L_0+Q_0',\quad p_1=L_1+Q_1',\\
 p_2=2(1-m)+L_0/2+Q_2',\quad p_3=L_1/2,
 \qquad P_0(h)=p_0+p_1h+p_2h^2+p_3h^3.
 \end{gathered}
\]

For \(u=.895,m=.41\), the fixed-position radical bounds are

\[
 .764759<R_1<.764816,\quad
 .561208<v<.561336,\quad .897446<W_1<.897537.
\]

They follow by repeated squaring over \(3.9154\le q\le3.9156\).
For example the intermediate bounds are

\(1.641455145<U<1.641516070\) and

\(1.438664613<Y<1.438791652\). Substitution in (23) gives

\[
 L_0,L_1<0,\qquad
 p_0>.02,\quad p_1>-.15,\quad p_2>.767,\quad p_3>-.915.
\]

Since \(\sqrt{1+h^2}\le1+h^2/2\) and \(L_0+hL_1<0\),

\[
 \begin{split}
 P_{.41}(h)&\ge P_0(h)\\
 &>.02-.15h+(.767-.915(.164))h^2\\
 &>.02-.15h+.61h^2>0.
 \end{split}                                          \tag{24}
\]

The last quadratic is positive by a completed square, since

\(\(.15\)^2<4\(.02\)\(.61\)\). This proves the lower bound in (20).

For \(u=.94,m=.44\), the corresponding fixed-position bounds are

\[
 .741206<R_1<.741264,\quad
 .533996<v<.534119,\quad .905286<W_1<.905374.
\]

They give \(L_0,L_1<0\), \(|L_0|<.253\), \(|L_1|<1.819\), and

\[
 p_0<-.011,\quad p_1<-.11,\quad p_2<.63,\quad p_3<0.
\]

Now use

\(\sqrt{1+h^2}\ge1+h^2/2-h^4/8\). Its additional upper
error in (23) is bounded by

\[
 \frac{h^4}{8}(|L_0|+h|L_1|)
 <\frac{(.164)^4}{8}(.253+1.819(.164))<.0001.
\]

Thus, throughout \(.1\le h\le.164\),

\[
 P_{.44}(h)<-.011-.11(.1)+.63(.164)^2+.0001<0.          \tag{25}
\]

Equations (22)--(25) prove (20) on the entire rectangle, with no
angle subdivision or derivative sample.

## 5. The automatic sliders require no additional capture input

First we prove the sharper stationary bound

\[
 \boxed{1.4<k_2(q,u(q,t),t)<1.45}.                    \tag{26}
\]

Set

\[
 Z_0=\frac q{(2-u)U^2}+\frac{pq}{YV^2}>2.09.
\]

The last inequality follows directly from (7)--(9). The exact second
derivative is

\[
 F_{uu}=2\left[
 a^2+b^2+\frac{k_1cq}{r^3}
 +k_2\left(pZ_0(c+sv/w)+\frac{sp^2q}{w^3}\right)
 \right].                                            \tag{27}
\]

Using only the positive terms except the last, (7)--(9) give

\[
 \begin{split}
 F_{uu}>2\bigg[&.599^2+.582^2+
 \frac{1.327(.9868)(3.9154)}{1.765^3}\\
 &+1.379(.574)(2.09)
       \left(.9868+\frac{.0995(.533)}{1.906}\right)
 \bigg]>6.6.
 \end{split}                                          \tag{28}
\]

Let \(d=s(r-1)+cu\). Differentiating \(F_u=2(k_1a-k_2b)\)
gives

\[
 F_{ut}=2\left[
 da+k_1(c-su/r)+Eb-k_2p(cv/w-s)
 \right]<5.5.                                        \tag{29}
\]

For a visible rational upper substitution, discard the last negative
term and bound the remaining bracket by

\[
 [ .162(.765)+.9951(.94)](.700)
 +1.422\left(.9951-\frac{.0995(.895)}{1.765}\right)
 +.993(.665)<\frac{5.5}{2}.
\]

Along the stationary graph \(u_t=-F_{ut}/F_{uu}\). Therefore

\[
 \frac d{dt}k_2=-E+b\frac{F_{ut}}{F_{uu}}
 <-.938+.665\frac{5.5}{6.6}<-.38<0.                   \tag{30}
\]

Only two fixed endpoint substitutions remain. At \(h=.1\), repeated
squaring in (5) gives uniformly in \(q\)

\[
 F_u(q,.935,\arctan .1)<-.0056,
 \qquad k_2(q,.935,\arctan .1)<1.445.
\]

By (28), \(u(q,\arctan .1)>.935\), and \(k_{2u}=-b<0\)
makes its stationary \(k_2\) smaller than \(1.445\). At \(h=.164\),
(10) gives \(u<.9016\), while the fixed substitution gives

\[
 k_2(q,.9016,\arctan .164)>1.404.
\]

Monotonicity (30) proves (26) between these endpoints. This does not
use the old position-bracket or four-rectangle derivative tables.

For any actual exterior square, let \(a\ge b\ge0\) be its
unsigned canonical center coordinates. Core avoidance and containment
give directly

\[
 \frac{447}{800}<a<\frac{283}{200},\qquad |p|<\frac32.
                                                               \tag{31}
\]

Indeed the distance from the origin to the square is

\(\sqrt{(a-1/2)_+^2+(b-1/2)_+^2}\le\sqrt2(a-1/2)_+\),
so \(a\ge1/2+\sqrt2/24>447/800\). Its farthest corner gives

\(a\le\sqrt{Q_0-1/4}-1/2<283/200\). Finally the disk of
radius \(1/2\) about its center lies in the containing disk of
radius less than 2, proving the center-norm bound.

The T error has magnitude at most \(S\). Its true vertical projection

\(Z=(p_T)_y\) therefore differs from \(a_T\) by less than

\(3S/2\). Equations (1) and (31) put it strictly inside

\[
 \boxed{.557\le Z\le1.417}.                           \tag{32}
\]

The G frame is exactly \(t\). Its transverse comparison coordinate is

\[
 \eta=(p_G-p_H^0-e_t)\mathbin\cdot f_t
      =-a_G+k_2-\frac12,
\]

where \(p_H^0=(-k_1+1/2)e_t+(-k_2+1/2)f_t\).
Using (26) and (31) gives, again strictly inside,

\[
 \boxed{-.515\le\eta\le.392}.                         \tag{33}
\]

This proves both automatic slider bounds for original centers, with
no tangent sign or radial boundary restriction.

## 6. All nine enlarged owner reserves exceed \(3/250\)

Write \(\Delta=r-U\) and define

\[
 X=\beta(2-u+J),\qquad K=\beta(Y+J),\qquad
 L=\epsilon s v/w,\qquad N=\omega n.
\]

The force identities imply

\[
 K=\epsilon c+\delta(V-w),\qquad
 L=\delta-\epsilon c.                                \tag{34}
\]

Also \(0<\Delta<1\), \(w>V\), and \(\alpha<\beta\), by
(7), (10), and (17). With the enlarged sliders (32)--(33), the
nine required reserves are

\[
 \begin{gathered}
 V_1=X,\qquad V_2=\alpha(1-\Delta)-X,\qquad
 V_3=K,\qquad V_4=\beta-K,\\
 V_5=\beta(-.917-J),\qquad V_6=\beta(1.057+J),
 \qquad V_7=L,\\
 V_8=N-.392\omega,\qquad V_9=.485\omega-N.
 \end{gathered}                                       \tag{35}
\]

There is a useful exact simplification of the second one:

\[
 \frac{V_2}{\beta}=-J-\frac{(2-u)(r-1)}{U}.           \tag{36}
\]

The first six estimates follow immediately from (7), (10)--(11),
(16), and (36):

\[
 \begin{gathered}
 V_1>.69(.031),\qquad
 V_2>.69\left(.98-\frac{1.105(.765)}{1.641}\right),\\
 V_3>.69(.409),\quad V_4>.69(.513),\quad
 V_5>.69(.063),\quad V_6>.69(.028).
 \end{gathered}                                       \tag{37}
\]

Each of these six displayed rational numbers exceeds \(.012\).
The remaining three satisfy

\[
 V_7>.69\frac{.0995(.533)}{1.906}>.012,
\]
\[
 V_8>\frac23(.41-.392)=.012,
 \qquad V_9>\frac23(.485-.44)=.03>.012.                \tag{38}
\]

Thus

\[
 \boxed{V_j>\rho:=3/250\quad(1\le j\le9).}            \tag{39}
\]

For completeness, the exact smooth coefficients for the five tree
differences are, with the two possible owners separated by a comma,

\[
 \begin{aligned}
 c_{AB}&=-\alpha/2+X,\quad -\alpha/2+X+\alpha\Delta,\\
 c_{TB}&=-\beta(Z+J),\quad-\beta(3/2-u+J),\\
 c_{DT}&=\beta/2-K,\quad-\beta(Z+J),\\
 c_{ED}&=\delta/2-\epsilon c,
             \quad\delta/2-\epsilon c-\delta(V-w),\\
 c_{HG}&=-\omega/2+N,
             \quad-\omega/2+N-\omega\eta.
 \end{aligned}                                       \tag{40}
\]

These are the algebraic force cancellations in the broad terminal's
Section 5; they hold for all coordinates in (32)--(33). Each aligned
support cusp has coefficient \(\lambda_e/2\).

The two AB choices are controlled by \(V_1,V_2\). The varying T
choices use \(V_5,V_6\), and the other DT choice uses \(V_3,V_4\).
The other TB choice has reserves \(X,\beta-X\), with

\(\beta-X>V_2\). For ED, (34) and \(V-w<0\) show that

\(K,L\) bound both choices. The full G interval uses \(V_8,V_9\).
This proves directly that

\[
 \lambda_e/2-|c_e|>\rho                              \tag{41}
\]

for all five edges, all enlarged sliders, and every owner assignment.
Consequently the complete first-order angular term is greater than

\(\rho S\) when \(S>0\), and is zero when \(S=0\).

## 7. Exact completion and a fresh global remainder bound

We use the exact geometric identities in Sections 2--5 of
`../HAND_EXACT_CENTER_SQUARE_COMPLETION.md`, not its arithmetic
inputs. They are recalled here to specify the entire remaining
estimate.

The selected reference corner offsets are

\[
 o_A^0=(1/2,-1/2),\quad o_B^0=(1/2,1/2),\quad
 o_D^0=(-1/2,1/2),\quad o_E^0=(-1/2,-1/2),
 \quad o_H^0=-(e_t+f_t)/2,
\]

and \(o_i=R(a_i)o_i^0\). For each actual signed gap

\(g_e=n_e\cdot(p_j-p_i)-w_e\ge0\), use its actual chosen
owner normal. If \(b_0,u_0,v_0,d_0\) denote the owners' errors
on AB, TB, DT, ED, respectively, and \(n=R(a_H)e_t\) when H
owns HG or \(n=e_t\) when G owns it, the center forces are exactly

\[
 \begin{aligned}
 F_A&=\alpha R(b_0)f_0-\omega e_t,&
 F_B&=-\alpha R(b_0)f_0-\beta R(u_0)e_0,\\
 F_D&=\beta R(v_0)e_0-\delta R(d_0)f_0,&
 F_E&=\delta R(d_0)f_0-\epsilon R(a_H)f_t,\\
 F_H&=\omega n+\epsilon R(a_H)f_t,&
 F_T&=\beta(R(u_0)e_0-R(v_0)e_0),\\
 F_G&=\omega(e_t-n).&&
 \end{aligned}                                       \tag{42}
\]

The positive normalized disk weights and nonnegative actual gaps give

\[
 r_0\ge\sum_i\mu_i|p_i+o_i|^2-\sum_e\lambda_e g_e.
\]

Complete each of the five anchored center squares by the identity

\[
 \mu_i|p_i+o_i|^2+F_i\cdot p_i
 =\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
       -F_i\cdot o_i-\frac{|F_i|^2}{4\mu_i}.          \tag{43}
\]

The remaining scalar function has reference value

\(q_*+\mu_HM(q_*,t)\). The force identities cancel every term
linear in an anchored center displacement. The reference slider
coordinates are the actual projections (32)--(33), so they give the
same first angular derivative as the actual slider centers. Therefore
(40)--(41) are its full first-order term.

### 7.1 Five force-norm terms

The nonconstant part of \(-\sum |F_i|^2/(4\mu_i)\) consists of
five elementary sine or cosine terms. Their positive coefficients
simplify exactly to

\[
 K_A=\alpha r/c,\qquad K_B=\beta(2-u),\qquad
 K_D=\delta V,\qquad K_E=\delta w/s,
 \qquad K_H=\epsilon k_1.                            \tag{44}
\]

The \(K_H\) term is absent for one HG owner. Using

\(|\sin x-x|\le|x|^3/6\) and

\(0\le1-\cos x\le x^2/2\), their remainder is bounded below by

\[
 -\frac{K_As+K_E}{2}S^2
 -\frac{K_A+K_B+K_D+K_H}{6}S^3.                      \tag{45}
\]

### 7.2 Support/offset and actual-slider terms

For every aligned owner choice, the exact support/offset contribution
has cosine coefficient at most 1, smooth sine coefficient of absolute
value at most \(1/2\), and cusp coefficient exactly \(1/2\), after
division by its edge weight. Hence the five aligned terms lose at
most

\[
 \frac\Lambda2 S^2+\frac\Lambda6 S^3.                 \tag{46}
\]

On HE the cosine terms cancel exactly; its contribution is

\(\epsilon[1+\sin(t+a_H-a_E)]\). The angle remains between
zero and \(\pi/2\) under (1), so its remainder is bounded by

\[
 \frac{\epsilon s}{2}S^2+\frac\epsilon6 S^3.           \tag{47}
\]

GA is constant in the errors. For the T slider, write

\(p_T=X_Te_0+Zf_0\). The two error angles in its force have
magnitudes at most \(S_C=S-|a_H|\), so

\[
 F_T\cdot p_T
 =\beta X_T(\cos u_0-\cos v_0)
       +\beta Z(\sin u_0-\sin v_0).
\]

The cosine difference has magnitude at most \(S_C^2/2\), and

\(|X_T|,|Z|<3/2\) by (31). Its remainder after the linear term
is therefore at most \(3\beta S_C^2/4+\beta S_C^3/2\).
The G slider contributes at most

\(3\omega |a_H|^2/4+\omega |a_H|^3/4\), or zero for its
other owner. Since \(S_C+|a_H|=S\), the combined slider loss is
bounded by

\[
 \frac{3\Lambda}{4}S^2+\frac\Lambda2 S^3.             \tag{48}
\]

No reference-slider containment or actual-center proximity is used.

### 7.3 Two explicit rational constants finish the estimate

Combining (44)--(48) with (7), (9), and (18) bounds the quadratic
coefficient by

\[
 \begin{split}
 C_2&=\frac{.87}{2}
       \left(\frac{1.906}{.0995}+1.765(.164)+.162\right)
        +\frac{5(.87)}4\\
 &=\frac{19137131349}{1990000000}<\frac{97}{10},
 \end{split}                                          \tag{49}
\]

and the cubic coefficient by

\[
 \begin{split}
 C_3&=\frac{.87}{6}
       \left(\frac{1.765}{.9868}+1.105+1.359+1.422+5\right)\\
 &=\frac{381846799}{246700000}<\frac85.
 \end{split}                                          \tag{50}
\]

Both comparisons are single cross-multiplications. For \(S\le1/1000\),

\[
 C_2S^2+C_3S^3
 <\left(\frac{97}{10}+\frac8{5000}\right)S^2
 <\frac{39}{4}S^2.                                   \tag{51}
\]

At \(S=0\), use equality of all zero remainders instead of the strict
version of (51).

## 8. Conclusion and equality conditions

The exact completion, the whole-domain reserve (39), and (51) give

\[
 r_0\ge q_*+\mu_HM(q_*,t)
  +\sum_i\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
  +\left(\frac3{250}-\frac{39}{4}S\right)S.
\]

On (1), the final coefficient is at least

\[
 \frac3{250}-\frac{39}{4000}=\frac9{4000}>\frac1{500}.
\]

This proves (2), including \(S=0\). The retained term

\(\mu_HM(q_*,t)\) is nonnegative by the table-free compact
stationary construction. Its unique zero is \(t=t_*\), so no
quantitative reduced-curvature estimate is required for sharpness
or for the stated equality implications.

All arithmetic premises of this conditional terminal are now the
explicit formulas and whole-domain estimates above and in the
position/J note. The old nine-midpoint reserve calculation, its four
rectangles, its position-bracket table, and its reduced-curvature
table are not inputs to this proof.

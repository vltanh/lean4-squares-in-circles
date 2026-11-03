# An all-sign seven-original near-row terminal

November 3, 2026. Complete hand proof after seven-original numerical
discovery. Every physical separator owner and both signs of every original
frame are retained. No Lean, Lake, or CI.

## 1. Statement

Let seven distinct original physical unit squares A,H,I,D,E,F,G have
pairwise disjoint open interiors. Suppose that in one fixed coordinate
frame:

1. `x_A<x_H<x_I<x_D` and
   `|y_H-y_A|+|y_I-y_H|+|y_D-y_I|<=1/12`.
2. E,F,G form an actual horizontal projection chain. No center-cone
   assumption on these two links is needed for this theorem.
3. `y_E>y_A` and `y_G>y_D`.
4. Each of these seven original frames has a representation
   `(alpha_i,beta_i),(-beta_i,alpha_i)` with
   `alpha_i>0`, `alpha_i^2+beta_i^2=1`, and `|beta_i|<=1/50`.

Then their containing radius satisfies

\[
                         R^2\ge Q=\frac{1105}{256}.
\]

Equality forces all seven originals to be aligned with the coordinate
axes, and `x_D-x_A=3`. No height or orientation is substituted for an
original square. In particular the theorem does **not** assume actual
projection separation on any of the three links A,H,I,D. Both endpoint
tilts can have either sign, including equal signs.

The same conclusion holds when both endpoint shoulders are below instead
of above, by a common vertical reflection.

In the original strict `001/00` caller, take H,I to be the two extras and
retain the original B,C as well. The already established E/A and G/D
orders supply condition 3. Under conditions 1 and 4, the full original
strict mask is impossible **even at closed Q**; Section 8 excludes the
equality face using the original AB,BC actual links and CD strict weak
bit. Original B and C need no small-angle assumption.

## 2. Constants and a small-angle physical support estimate

It suffices to consider `R^2<=Q`. Use the exact constants

\[
\begin{gathered}
a=46,\quad B=\frac{27}{2},\quad k=\frac{207}{16},
\quad T=\frac{211}{4},\quad \rho=\frac{91}{60},\\
b=\frac1{50},\quad U=\frac1{12},\quad
z=1-b^2=\frac{2499}{2500},\quad
\delta=\frac{b}{2-b^2}=\frac{50}{4999},\\
c=\frac{1-b-3b^2-4b^3}{2}=\frac{61173}{125000}.
\end{gathered}                                                    \tag{1}
\]

Every original center has norm less than rho. Indeed its farthest corner
has squared norm at least `|center|^2+|center|+1/2`, while

\[
\rho^2+\rho+\frac12-Q=\frac{31}{57600}>0.
\]

For any one of the seven small-angle originals,

\[
\alpha_i\ge z,\qquad
1-\alpha_i=\frac{\beta_i^2}{1+\alpha_i}
\le\delta|\beta_i|,\qquad
\frac12\le h_i=\frac{\alpha_i+|\beta_i|}{2}\le\frac{51}{100}.
                                                               \tag{2}
\]

For two such originals put `d_beta=|beta_i-beta_j|`. Directly from their
unit-circle equations,

\[
|\alpha_i-\alpha_j|
=\frac{|\beta_i+\beta_j|\,d_\beta}{\alpha_i+\alpha_j}
\le2b\,d_\beta.
\]

Consequently their frame dot product is positive and obeys

\[
\alpha_i\alpha_j+\beta_i\beta_j
=1-\frac{(\alpha_i-\alpha_j)^2+d_\beta^2}{2}
\ge1-b(1+4b^2)d_\beta>0,
\]

and the absolute determinant obeys

\[
|\alpha_i\beta_j-\beta_i\alpha_j|
\ge\alpha_i d_\beta-|\beta_i|\,|\alpha_i-\alpha_j|
\ge(1-3b^2)d_\beta.
\]

The sum S of the two original supports along any owned side normal is
`(1+|dot|+|det|)/2`, regardless of which original owns the axis and
whether it is the shallow or steep axis. Thus

\[
                             S\ge1+c\,d_\beta.       \tag{3}
\]

This estimate retains the **signed** difference of the two original beta
components. Folding it to a difference of unsigned widths would lose the
orientation variation used below.

## 3. The endpoint pairs lie in the correct horizontal bands

For consecutive members of A,H,I,D let their positive horizontal gap be
d_j and their signed vertical gap be v_j. Original unit-center distance
gives `d_j>=sqrt(1-v_j^2)`. The function
`g(t)=1-sqrt(1-t^2)` is convex, increasing, and zero at zero, so
`sum g(|v_j|)<=g(sum |v_j|)<=g(U)`. Therefore

\[
x_D-x_A\ge2+\sqrt{1-U^2}=2+\frac{\sqrt{143}}{12}
>\frac{719}{240}.
\]

The final squared reserve is
`143/144-(239/240)^2=79/57600>0`. The center bound then implies

\[
x_D>\frac{71}{48},\qquad x_A<-\frac{71}{48},\qquad
x_D-h_D,\;-x_A-h_A>\frac{1163}{1200}.                \tag{4}
\]

Apply the already accepted unconditional physical pair cap to A,E on the
left and D,G on the right. This requires only their genuine physical
nonoverlap and disk containment, already assumed. From (4),

\[
x_G-h_G<C_0,\qquad x_E+h_E>-C_0,\qquad
C_0=\frac{T-a(1163/1200)}{B}=\frac{4901}{8100}.
\]

The two actual E/F and F/G comparisons also give
`x_G-h_G>=x_E+h_E+2h_F>=x_E+h_E+1`. Hence

\[
1-C_0<x_G-h_G<C_0,\qquad
-C_0<x_E+h_E<C_0-1.
\]

Using (2), (4), and the center bound yields the complete endpoint bands

\[
\boxed{0<x_E-x_A<\frac58,\qquad 0<x_D-x_G<\frac58.} \tag{5}
\]

For their upper bounds the sharper expression is

\[
\rho-\frac32+C_0=\frac{1259}{2025}<\frac58,
\qquad \frac58-\frac{1259}{2025}=\frac{53}{16200}>0.
\]

For the strict order signs, use
`C0+51/100<71/48`, so E is strictly to the right of A and G strictly to
the left of D. No original pair has been replaced by a proxy.

## 4. Force the directions of the actual owned separators

The separating-axis theorem supplies an axis owned by one of the two
original squares for each physical pair. Its support sum is at least one.

For a main-row pair, either steep owned axis has absolute center
projection at most

\[
2b\rho+U=\frac{18}{125}<1.
\]

It therefore cannot separate. The normal with positive horizontal
component is the remaining shallow axis `(alpha_o,beta_o)`. Its opposite
has projection `-alpha_o d_j-beta_o v_j<=bU<1`, since `d_j>0`, and cannot
separate. Thus (3) gives

\[
d_j\ge1+c|\beta_{j+1}-\beta_j|
             -\frac{\beta_o}{\alpha_o}v_j.            \tag{6}
\]

For the A/E and D/G pairs, (5) and the center bound make either shallow
axis projection at most

\[
\frac58+2b\rho<1.
\]

Their separating axes must therefore be steep. For either endpoint pair,
the downward steep normal projects at most `(5/8)b<1`, since its vertical
center gap is positive. The usable normal is therefore
`(-beta_o,alpha_o)`. Writing
`d_L=x_E-x_A>0` and `d_R=x_G-x_D<0`, (3) yields

\[
y_E-y_A\ge1+c|\beta_A-\beta_E|
                    +\frac{\beta_o}{\alpha_o}d_L,
\]

\[
y_G-y_D\ge1+c|\beta_D-\beta_G|
                    +\frac{\beta_o}{\alpha_o}d_R.      \tag{7}
\]

Both possible owners remain present in (6)--(7). Put

\[
M=\max(|\beta_A|,|\beta_H|,|\beta_I|,|\beta_D|),\qquad
V=|\beta_H-\beta_A|+|\beta_I-\beta_H|+|\beta_D-\beta_I|,
\]

and

\[
\lambda=\frac{5k}{8z}=\frac{215625}{26656}.
\]

Adding (6), the absolute variation bound on the original heights gives

\[
a(x_D-x_A)\ge3a+acV-\frac{aU}{z}M.                 \tag{8}
\]

For (7), nonnegative owner beta on the left has a nonnegative extra
term, while negative owner beta can cost at most `(5/(8z))|beta_o|`.
The right side reverses this sign. Therefore

\[
\begin{aligned}
k(y_E-y_A+y_G-y_D)\ge{}&2k+kc(|\beta_A-\beta_E|+|\beta_D-\beta_G|)\\
&-\lambda\max(-\beta_A,-\beta_E,0)
 -\lambda\max(\beta_D,\beta_G,0).
\end{aligned}                                                    \tag{9}
\]

## 5. Four fixed circle supports, with signed frame components retained

Use the circle-support vectors

\[
(-a,-k)\text{ on A},\quad (a,-k)\text{ on D},\quad
(-B,k)\text{ on E},\quad (B,k)\text{ on G}.
\]

Their lengths are `23 sqrt(Q),23 sqrt(Q),9 sqrt(Q),9 sqrt(Q)`.
Consequently, if Hsum is the sum of the four original centered supports
in these vectors,

\[
a(x_D-x_A)+B(x_G-x_E)+k(y_E-y_A+y_G-y_D)
                         +H_{\rm sum}\le64Q.          \tag{10}
\]

The inequality is strict when `R^2<Q`. All relevant support-coordinate
signs are fixed by `|beta|<=b`; for example `k alpha>a|beta|` and
`B alpha>k|beta|`. Direct expansion gives

\[
\begin{aligned}
H_{\rm sum}={}&P(\alpha_A+\alpha_D)
 +\frac{B+k}{2}(\alpha_E+\alpha_G)\\
&+C(\beta_D-\beta_A)+\frac{B-k}{2}(\beta_E-\beta_G),
\end{aligned}                                                    \tag{11}
\]

where

\[
P=\frac{a+k}{2}=\frac{943}{32},\qquad
C=\frac{a-k}{2}=\frac{529}{32},\qquad
J=B+\frac k2=\frac{639}{32}.
\]

The unchanged actual short chain contributes

\[
B(x_G-x_E)\ge B(h_E+2h_F+h_G).
\]

Combine this with (2) and (11). The constant part of the full lower
bound in (8)--(10) is

\[
3a+2B+2k+(a+B+2k)=4a+3B+4k=64Q.
\]

The nonconstant lower bound is

\[
acV-\frac{aU}{z}M+L(\beta_A,\beta_E)
              +L(-\beta_D,-\beta_G)+B(1-\delta)|\beta_F|,   \tag{12}
\]

where, for arbitrary real x,y,

\[
\begin{aligned}
L(x,y)={}&kc|x-y|+e_+ y_++e_-(-y)_+\\
&-\lambda\max(-x,-y,0)-Cx-P\delta|x|,
\end{aligned}                                                    \tag{13}
\]

`y_+=max(y,0)` and

\[
e_+=B-k/2-J\delta=\frac{1092825}{159968},\qquad
e_-=k/2-J\delta=\frac{1002843}{159968}.
\]

Equation (12) is only a sum of unchanged original physical inequalities;
no two separate toll bounds for one physical pair have been added.

## 6. A complete signed-angle variation payment

The following exact scalar comparisons hold:

\[
e_-<kc<e_+,\qquad kc+e_--\lambda>0.
\]

For fixed x, the expression (13) is piecewise affine in y, with possible
breakpoints only at y=0 and y=x. The preceding positive tail slopes
and the displayed order give its complete minimum:

\[
L(x,y)\ge f(x):=
\begin{cases}
-p x,&x\ge0,\\
q(-x),&x\le0,
\end{cases}                                                     \tag{14}
\]

where

\[
\begin{split}
p&=C+P\delta-kc=\frac{104924920311}{9998000000},\\
q&=e_-+C-P\delta-\lambda=\frac{1921027237}{133253344}.
\end{split}
\]

For completeness, before the two x-only terms in (13), its value at
y=0 is `kc x` for x>=0 and `(kc-lambda)(-x)` for x<=0. At y=x it is
`e_+x` for x>=0 and `(e_--lambda)(-x)` for x<=0. Thus y=0 minimizes
when x>=0, and y=x minimizes when x<=0. On the two exterior rays the
positive coefficients are `kc+e_+` and `kc+e_--lambda`; this proves
the minimum over the whole real line, not just a finite sample.

Exact arithmetic also gives

\[
ac\ge q>p>0.
\]

Put `c1=(q-p)/2` and `c2=(q+p)/2`. Then
`f(x)=c1|x|-c2 x`. Since `|beta_D-beta_A|<=V`,

\[
\begin{aligned}
acV+f(\beta_A)+f(-\beta_D)
&\ge(ac-c_2)V+c_1(|\beta_A|+|\beta_D|)\\
&\ge c_1(V+|\beta_A|+|\beta_D|)\\
&\ge(q-p)M.                                         \tag{15}
\end{aligned}
\]

For the last inequality, split the original four-term beta path at a
square attaining M. Its variation plus its two endpoint magnitudes is
at least 2M. This includes a maximum attained at an endpoint and all
possible sign changes of the two intermediate originals.

Finally the exact remaining coefficient is strictly positive:

\[
q-p-\frac{aU}{z}
=\frac{6513193240933}{74955006000000}>0.               \tag{16}
\]

Equations (12)--(16) make the full lower bound in (10) at least 64Q.
This contradicts its strict upper bound whenever `R^2<Q`, proving the
stated sharp seven-original lower bound for all four endpoint-sign
patterns.

## 7. Equality, without assumptions on unused centers

At `R^2=Q`, (16) forces M=0, so all four originals in A,H,I,D are
aligned. The positive `B(1-delta)|beta_F|` term makes F aligned.
With x=0, formula (13) is strictly positive for y!=0, since its two
coefficients are `kc+e_+` and `kc+e_--lambda`. Therefore E and G are
aligned as well.

The three main vertical gaps are below one. For aligned physical unit
squares in horizontal order, original nonoverlap then gives every main
horizontal gap at least one. The actual short chain contributes at
least two, and the upward endpoint pairs with horizontal gap below 5/8
contribute at least one each vertically. Equality in (10) leaves no
slack in their weighted sum, so each of the three main gaps is exactly
one. In particular `x_D-x_A=3`.

No statement about F's center height or the two physical squares omitted
from this seven-original subsystem is needed for this conclusion.

## 8. Closed-Q terminal inside the original strict `001/00` mask

Now keep the full original-nine caller, with original main A,B,C,D and
short E,F,G, and use its two extras for H,I. If the hypotheses of Section 1
hold, the preceding theorem rules out strict radius. At closed Q it
forces the original A,D to be aligned and `x_D-x_A=3`.

The original AB and BC actual comparisons and original CD cone-inset
comparison then give

\[
3=x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D
=1+2h_B+(h_C+g_C)\ge3.
\]

Since `h_C+g_C-1=(2h_C-1)^2/(4h_C)`, equality forces B and C aligned.
Both C,D are aligned, and their original inset comparison gives
`x_D-x_C>=1=h_C+h_D`, contradicting the retained strict weak CD bit.
This excludes the complete closed-Q row region, with no B/C angle
restriction and no endpoint-sign restriction.

## 9. Scope of the discovery and exact companion

The exploratory model retained all seven frames, all 28 original corners,
all 21 physical pairs, the actual E/F and F/G comparisons, and the three
main-row center-cone comparisons. Fifty starts at total variation 11/30
and twenty starts at 1/2 found no numerical value below Q beyond solver
roundoff. Those outcomes suggested an all-sign theorem but prove no
continuous domain. The hand proof above establishes the narrower explicit
region `U<=1/12`, `|beta_i|<=1/50`, with the two stated shoulder orders.

`all_sign_small_angle_row_arithmetic.py` checks the support identities,
all rational constants, all sign-separation reserves, the complete scalar
minimum conditions, and the positive final reserve. The proofs of the
continuous physical implications and equality are printed above.

The theorem is a reusable analytic terminal. It does not prove that every
remaining original-nine configuration enters this region; no whole-mask,
positional-root, or roadmap count changes on this result alone.

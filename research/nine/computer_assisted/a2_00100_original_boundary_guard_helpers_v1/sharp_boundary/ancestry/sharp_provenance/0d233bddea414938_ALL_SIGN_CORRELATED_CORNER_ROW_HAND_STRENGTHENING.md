# All-sign near rows using the correlated endpoint corner deficits

November 3, 2026. Complete pen-and-paper strengthening of
`ALL_SIGN_SMALL_ANGLE_THREE_LINK_ROW_HAND_TERMINAL.md`. Numerical exploration
of the seven-original physical model and exact rational exploration of the
criterion below preceded this proof. No numerical optimizer output is a
premise. No Lean, Lake, or CI.

## 1. Two explicit seven-original terminals

Let seven distinct original physical unit squares A,H,I,D,E,F,G have
pairwise disjoint open interiors and lie in a circle of radius R. In one
fixed frame assume:

- `x_A<x_H<x_I<x_D`;
- E,F,G form an actual horizontal projection chain;
- `y_E>y_A` and `y_G>y_D`;
- each of these seven original frames is
  `(alpha_i,beta_i),(-beta_i,alpha_i)`, with `alpha_i>0`,
  `alpha_i^2+beta_i^2=1`.

Either of the following two sets of quantitative guards suffices:

| Total variation of the row heights | Maximum absolute beta among the seven originals |
|---|---|
| at most 11/30 | at most 1/30 |
| at most 9/20 | at most 1/50 |

Then

\[
                         R^2\ge Q=\frac{1105}{256}.                 \tag{1}
\]

Equality forces all seven squares aligned and `x_D-x_A=3`. Both endpoint
signs and every intermediate frame remain unrestricted within the stated
absolute bounds. The same conclusion holds with both shoulder height
orders reversed, by a common vertical reflection.

In the original strict `001/00` nine-square caller, with H,I its two
extras, either region is impossible even at closed Q: the original
AB,BC actual and CD cone-inset inequalities contradict the retained
strict weak CD bit on this equality face. Original B,C require no angle
bound. This is an analytic terminal, not a claim that every remaining
nine-square configuration meets these guards.

## 2. A rational criterion usable with other bounds

Retain the exact constants

\[
a=46,\quad B=27/2,\quad k=207/16,\quad T=211/4,\quad
\rho=91/60,\quad P=(a+k)/2,\quad C=(a-k)/2,\quad J=B+k/2.
\]

For proposed bounds `0<b<1/2`, `U>0`, and an endpoint horizontal-pair
bound L, define

\[
\begin{gathered}
z=1-b^2,\quad \delta=\frac{b}{2-b^2},\quad
c=\frac{1-b-3b^2-4b^3}{2},\quad
X_0=3-\frac{bU}{z},\\
C_0=\frac{T-a[X_0-\rho-(1+b)/2]}B,\quad
\lambda=\frac{kL}{z},\\
e_+=B-k/2-J\delta,\quad e_-=k/2-J\delta,\\
p=C+P\delta-kc,\quad q=e_-+C-P\delta-\lambda,\\
\mathcal A=ac-\frac{aU}{2z^3}-\frac{ab(b+1/2)}z,
\qquad K=\frac{a^2}{23z^2}-a.
\end{gathered}                                                       \tag{2}
\]

The following finite list of rational conditions implies the same
theorem with guards `sum |Delta y|<=U` and all seven `|beta_i|<=b`:

\[
\begin{gathered}
0<b<1/2,\quad U>0,\quad L>0,\quad c>0,\quad 2b\rho+U<1,\quad L+2b\rho<1,\\
\rho-3/2+C_0<L,\qquad C_0+(1+b)/2<X_0-\rho,\\
az>kb,\quad kz>ab,\quad Bz>kb,\quad kz>Bb,\\
e_-<kc<e_+,\quad kc+e_--\lambda>0,\quad p>0,\\
q>p,\quad \mathcal A>p,\quad K\ge0,\qquad
\boxed{\varepsilon=\min(\mathcal A,q)-p-Kb>0.}
\end{gathered}                                                       \tag{3}
\]

Both displayed terminal rows satisfy (3) with the same simple choice
`L=7/10`. For the first row, `mathcal A<q` and

\[
\begin{gathered}
p=\frac{931916369}{86352000},\quad
q=\frac{12115211}{924172},\quad
\mathcal A=\frac{126268435381231}{9808731436500},\\
K=\frac{37342754}{808201},\qquad
\varepsilon=\frac{305395948055079229}{564669051336432000}>0.
\end{gathered}                                                       \tag{4}
\]

For the second row, again `mathcal A<q`, and

\[
\varepsilon=
\frac{13240758374442033713}{52010454158334000000}>0.                   \tag{5}
\]

All conditions in (3) are evaluated as exact fractions in the companion.
The argument below proves their continuous physical implications.

## 3. The unchanged physical estimates and endpoint bands

It suffices to consider `R^2<=Q`. Every original center has norm less
than rho, since its farthest original corner has squared norm at least
`|center|^2+|center|+1/2` and
`rho^2+rho+1/2-Q=31/57600>0`. For every small-angle original,

\[
\alpha\ge z,\quad 1-\alpha\le\delta|\beta|,\quad
1/2\le h=(\alpha+|\beta|)/2\le(1+b)/2.                              \tag{6}
\]

For any two originals, their sum of supports along any axis owned by
either square is at least

\[
                         1+c|\beta_i-\beta_j|.                     \tag{7}
\]

Here is the complete estimate. Unit-circle subtraction gives
`|alpha_i-alpha_j|<=2b|beta_i-beta_j|`, since `z>1/2`. If
`d_beta=|beta_i-beta_j|<=2b`, their positive dot product is at least
`1-b(1+4b^2)d_beta`; their determinant magnitude is at least
`(1-3b^2)d_beta`. The owned-axis support sum is one half of one plus
the absolute dot product plus the absolute determinant. This is (7).
Positivity of the dot lower bound follows from
`1-2b^2(1+4b^2)>0` for `b<1/2`.

Each of the three forward main-row pairs has vertical gap at most U.
A steep owned axis projects at most `2b rho+U<1`, so it cannot separate.
The reversed shallow normal projects at most `bU<1`. Thus a genuine
physical separator is the forward shallow normal of one of the two
originals. With its signed owner slope `s_o=beta_o/alpha_o`, (7) gives

\[
d_j\ge1+c|\Delta\beta_j|-s_o v_j,
\qquad d_j>0,\quad v_j=\Delta y_j.                                  \tag{8}
\]

In particular, summing `d_j>=1-(b/z)|v_j|` gives `x_D-x_A>=X_0`.
Therefore `x_D>X_0-rho`, `x_A<-(X_0-rho)`, and the two main outward
edges exceed `X_0-rho-(1+b)/2`.

The accepted unconditional physical pair cap, applied to A/E and D/G,
now gives

\[
x_G-h_G<C_0,\qquad x_E+h_E>-C_0.
\]

The actual short chain gives
`x_G-h_G>=x_E+h_E+2h_F>=x_E+h_E+1`, so

\[
1-C_0<x_G-h_G<C_0,\qquad -C_0<x_E+h_E<C_0-1.
\]

The two band conditions in (3), together with (6) and the center bound,
imply

\[
                 0<x_E-x_A<L,\qquad 0<x_D-x_G<L.                   \tag{9}
\]

These are actual original center bands. In particular their shallow
owned-axis projections are at most `L+2b rho<1`. The upward height
orders and the bound `bL<1` also rule out the downward steep normal.
Both actual endpoint-pair separators are therefore upward steep normals.
Keeping both possible owners in (7) gives

\[
\begin{aligned}
k(y_E-y_A+y_G-y_D)\ge{}&2k+kc(|\beta_A-\beta_E|+|\beta_D-\beta_G|)\\
&-\lambda\max(-\beta_A,-\beta_E,0)
 -\lambda\max(\beta_D,\beta_G,0).
\end{aligned}                                                       \tag{10}
\]

The first loss uses the left horizontal gap in `(0,L)` and the second
uses the right gap in `(-L,0)`. No owner or frame sign is fixed.

## 4. Keep the common signed slope, rather than charging it to U

Let V be the total variation of the four signed beta components along
A,H,I,D, and M their maximum absolute value. Put

\[
m=\frac{\min_i\beta_i+\max_i\beta_i}{2},\qquad
s=\frac{m}{\sqrt{1-m^2}},\qquad \Delta y=y_D-y_A.
\]

The slope function `t(beta)=beta/sqrt(1-beta^2)` has derivative at most
`1/z^3` on the entire beta interval. Each genuine owner beta is within
half the interval width of m, and that width is at most V. Hence

\[
\left|s_o-s\right|\le\frac{V}{2z^3},\qquad
\sum_j s_{o_j}v_j\le s\Delta y+\frac{UV}{2z^3}.
\]

Adding (8) therefore preserves the common signed height drift:

\[
a(x_D-x_A)\ge3a+\left(ac-\frac{aU}{2z^3}\right)V-a s\Delta y.
                                                                        \tag{11}
\]

This is the step that permits a substantially larger height variation.
The circle corners pay for the remaining common drift.

## 5. The two main corner deficits are correlated

Use the same fixed circle-support vectors as in the accepted all-sign
terminal:

\[
w_A=(-a,-k),\quad w_D=(a,-k),\quad
w_E=(-B,k),\quad w_G=(B,k).
\]

Their lengths are `23 sqrt(Q),23 sqrt(Q),9 sqrt(Q),9 sqrt(Q)`. The
four support sign conditions in (3) determine the actual maximizing
corner of each original. In particular the selected main corners have
vertical coordinates

\[
y(z_A)=y_A-\frac{\alpha_A+\beta_A}{2},\qquad
y(z_D)=y_D+\frac{\beta_D-\alpha_D}{2}.                               \tag{12}
\]

Write `r=sqrt(Q)`. For any actual corner z in the disk and any nonzero
vector w, the following is an exact identity followed by a lower bound:

\[
r|w|-w\cdot z
=\frac{|w|}{2r}
 \left(\left|z-r\frac w{|w|}\right|^2+r^2-|z|^2\right)
\ge\frac{|w|}{2r}\left|z-r\frac w{|w|}\right|^2.                     \tag{13}
\]

For A,D, the target corner vectors in (13) are
`(-2,-9/16)` and `(2,-9/16)`. Dropping their horizontal errors and
using `u^2+v^2>=(u-v)^2/2` proves that the sum of the four circle-support
deficits is at least

\[
\mathcal D=\frac{23}{4}Z^2,\qquad
Z=\Delta y+\frac{\beta_A+\beta_D+\alpha_A-\alpha_D}{2}.              \tag{14}
\]

The other two deficits are nonnegative and have not been double counted.
If `R<r`, (13) has positive additional radial error, so the total deficit
is strictly larger than the bound in (14).

Consequently the fixed support inequality is strengthened to

\[
a(x_D-x_A)+B(x_G-x_E)+k(y_E-y_A+y_G-y_D)+H_{\rm sum}
 +\mathcal D\le64Q,                                                  \tag{15}
\]

strictly for `R<r`. Here the exact original centered-support sum is

\[
\begin{aligned}
H_{\rm sum}={}&P(\alpha_A+\alpha_D)
 +\frac{B+k}{2}(\alpha_E+\alpha_G)\\
&+C(\beta_D-\beta_A)+\frac{B-k}{2}(\beta_E-\beta_G).
\end{aligned}                                                       \tag{16}
\]

To pay the drift in (11), write

\[
\beta_A+\beta_D+\alpha_A-\alpha_D=2m+e.
\]

The extrema defining m give
`|beta_A+beta_D-2m|<=max beta-min beta<=V`; unit-circle subtraction
also gives `|alpha_A-alpha_D|<=2bV`. Hence `|e|<=(1+2b)V`.
Substitute `Delta y=Z-m-e/2` and complete the square in Z:

\[
\begin{aligned}
\mathcal D-a s\Delta y
&=\frac{23}{4}Z^2-a s Z+a s m+\frac{a s e}{2}\\
&\ge-\frac{a^2s^2}{23}+a m^2
       -\frac{a(b+1/2)}z|m|V\\
&\ge-KbM-\frac{ab(b+1/2)}z V.                                      \tag{17}
\end{aligned}
\]

For the second line use `s m>=m^2` and `|s|<=|m|/z`; for the last,
use `K>=0`, `|m|<=b`, and `m^2<=bM`. All signs of m and of both endpoint
heights remain present in this calculation.

## 6. The exact remaining signed-angle minimization

The actual short chain supplies
`B(x_G-x_E)>=B(h_E+2h_F+h_G)`. Combine (6), (10), (11), (16), and
(17). The constant sum is exactly

\[
3a+2B+2k+(a+B+2k)=4a+3B+4k=64Q.
\]

The remaining lower bound in (15) is

\[
\mathcal A V-KbM+\mathcal L(\beta_A,\beta_E)+\mathcal L(-\beta_D,-\beta_G)
                  +B(1-\delta)|\beta_F|,                            \tag{18}
\]

where the scalar function is

\[
\mathcal L(x,y)=kc|x-y|+e_+y_++e_-(-y)_+
 -\lambda\max(-x,-y,0)-Cx-P\delta|x|.                               \tag{19}
\]

The exact conditions
`e_-<kc<e_+` and `kc+e_--lambda>0` prove

\[
\mathcal L(x,y)\ge f(x)=
\begin{cases}-px,&x\ge0,\\q(-x),&x\le0.\end{cases}                  \tag{20}
\]

For a complete verification, the only y-breakpoints are 0 and x. When
`x>=0`, the value before the x-only terms at `y=0` is `kcx`, less
than its value `e_+x` at `y=x`. When `x<=0`, the value at `y=x` is
`(e_--lambda)(-x)`, less than `(kc-lambda)(-x)` at `y=0`.
The exterior-ray costs are `kc+e_+` and `kc+e_--lambda`, both positive.
This proves the complete scalar minimum over all real y.

Here a sharper path inequality retains the endpoint difference rather
than bounding it independently by V:

\[
\mathcal A V+f(\beta_A)+f(-\beta_D)
\ge[\min(\mathcal A,q)-p]M.                                         \tag{21}
\]

To prove it, first suppose a row beta equals M. Splitting the path at
that original gives `V>=2M-beta_A-beta_D`. For `|x|<=M` and
`mathcal A>=p`, direct evaluation of the two branches of f gives

\[
f(x)-\mathcal A x\ge-(\mathcal A+p)M,
\quad
f(-x)-\mathcal A x\ge-\max(\mathcal A-q,0)M.
\]

Substitution proves (21). If instead a row beta equals -M, use
`V>=2M+beta_A+beta_D`; the same two scalar bounds exchange roles.
These cases include extrema at an endpoint and M=0.

Equations (18)--(21) give the nonnegative excess

\[
\varepsilon M+B(1-\delta)|\beta_F|\ge0,
\qquad \varepsilon>0.                                               \tag{22}
\]

This contradicts strictness in (15) for `R^2<Q`, proving the theorem.

## 7. Equality and the original closed-Q caller

At `R^2=Q`, (22) forces M=0 and `beta_F=0`. In (19), when x=0 the
two nonzero-y coefficients are `kc+e_+` and `kc+e_--lambda`, both
strictly positive. Thus `beta_E=beta_G=0` as well. All seven originals
are aligned.

Every main-row vertical gap is at most U<1, so physical nonoverlap
gives every main horizontal gap at least one. The short chain spans
at least two; both upward endpoint pairs have horizontal gap below
L<1, so each endpoint vertical gap is at least one. The centered-support
sum is now `a+B+2k`. In (15) these separate nonnegative lower bounds
already sum to 64Q. Therefore all three main gaps equal one and
`x_D-x_A=3`. This argument requires no assigned height for F or for the
two originals omitted from the seven-square subsystem.

For the original strict `001/00` caller, the unchanged AB,BC actual
and CD cone-inset comparisons give

\[
3\ge h_A+2h_B+h_C+g_C+g_D
=1+2h_B+(h_C+g_C)\ge3.
\]

Here the aligned A,D have halfwidth and inset halfwidth 1/2, and
`h_C+g_C-1=(2h_C-1)^2/(4h_C)`. Equality forces B,C aligned. The original
CD inset comparison then reads `x_D-x_C>=1=h_C+h_D`, contradicting
the strict weak CD bit. The two stated seven-original row regions are
therefore excluded even at closed Q inside that original-nine mask.

## 8. Verification scope

`all_sign_correlated_corner_row_arithmetic.py` evaluates every condition
in (3) as an exact rational number for both displayed specializations,
checks all fixed-support norm and coefficient identities, and checks the
continuous scalar-sector signs and final reserves. It proves no box cover
or original-nine routing on its own. The corner-deficit identity,
signed-slope integration, path inequality, and equality proof above are
the continuous hand argument. No whole-mask closure count changes merely
from adding this terminal.

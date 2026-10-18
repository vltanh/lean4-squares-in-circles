# The whole high/high frame-pair inequality by hand

This proves the strict H/H entry
\[
 \delta-.18h+\psi_j-\psi_i>.9099                       \tag{1}
\]
for adjacent exterior boundary states in the physical seven-square ring.
The upstream hand angle and backward-axis lemmas apply to that ring.
No frame-concentration conclusion is assumed. All terminating decimals
below are exact rational numbers.

This restored version gives the complete geometry and continuous case
cover, eighteen fixed scalar endpoint comparisons, and one explicit
degree-14 polynomial. The optional arithmetic replay checks 108 fixed
strict comparisons; it uses no mesh, minimizer, or subdivision tree.

## 1. Fold the high arc toward its diagonal

Put
\[
 Q=9789/2500,\quad \mathcal R=\sqrt{2Q},\quad
 u=.089293,\quad v=.480179,\quad \gamma=.9099.
\]
For an original high state, whose positive coordinates satisfy
\[
 (a_{\rm old}+1/2)^2+(b_{\rm old}+1/2)^2=Q,
 \qquad 3/7\le b_{\rm old}/a_{\rm old}\le1,
\]
set
\[
 a=a_{\rm old}+b_{\rm old},\qquad
 b=a_{\rm old}-b_{\rm old},\qquad
 \sigma=-\sigma_{\rm old}.
\]
Rotate the square frame by `-sigma_old*pi/4`. Its actual center in the
new coordinates is `(a,-sigma*b)/sqrt(2)`. The folded arc is
\[
 (a+1)^2+b^2=2Q,\qquad 0\le b/a\le2/5.                \tag{2}
\]
Write its endpoints as `(a0,0)` and `(a1,b1)`, where
\[
 a_0=\mathcal R-1,\qquad b_1=.4a_1,
\]
and put `a(b)=sqrt(2Q-b^2)-1`, `r=b/(a+1)`.
Then `a'=-r`, `a''<0`.

The new positive label is
\[
 \ell=u(a-a_0)+vb=\pi/4-\ell_{\rm old}.                \tag{3}
\]
If `alpha` is the signed frame-to-center angle, then
\[
 \alpha=\alpha_{\rm old}-\sigma_{\rm old}\pi/4,
 \qquad \alpha-\sigma\ell
       =\alpha_{\rm old}-\sigma_{\rm old}\ell_{\rm old}.
\]
Thus the potential `psi=alpha-sigma*ell` is exactly unchanged. The
relative folded frame increment differs from the original one by zero
or a quarter turn, so the width penalty is unchanged as well.

Direct substitution in (2), with positive squaring, gives
\[
\begin{array}{c|c}
 \mathcal R&(2.79842813,2.79842814)\\
 a_1&(1.71322294,1.71322295)\\
 r&[0,.253)\\
 \ell&[0,.321454).
\end{array}                                             \tag{4}
\]
The label increases since `ell'=v-u*r>0`; hence its maximum is its
cut-endpoint value. Let `ell1=ell(a1,b1)`.

## 2. The folded angle is positive; only one source axis remains

The physical center radius `rho` satisfies
\[
 \rho^2=(a^2+b^2)/2=Q-a-1/2,
 \qquad 1<\rho<4/3.                                  \tag{5}
\]
Two disjoint unit squares have center distance at least one, because
each contains its concentric radius-`1/2` disk. For radii `rho,tau`
in `[1,4/3]`, the expression
\[
 \frac{\rho^2+\tau^2-1}{2\rho\tau}
\]
increases in each variable: its derivative in `rho` has numerator
`rho^2-tau^2+1 >= 2-16/9>0`. Consequently the actual smaller angle
`delta` between the centers obeys
\[
 \cos\delta<23/32<21/29=\cos(2\arctan(2/5)).
\]
The upstream ring angle bound gives `delta<3*pi/4<pi`. Therefore
`delta>2*atan(2/5)`. In particular
\[
 \phi=\delta+\alpha_t-\alpha_s>0.                     \tag{6}
\]

The retained original source axes become the central folded normal
`(-1,+1)/sqrt(2)` and one extra diagonal normal. For source sign `+`,
the extra normal is `(+1,+1)/sqrt(2)`. Its separating projection is
at most the target center radius minus the source's original
transverse coordinate. The latter is
\[
 (a-b)/2\ge(a_1-b_1)/2=.3a_1>.51,
\]
so its projection is less than `4/3-.51<1`. Its required support sum
is at least one. This extra axis is impossible.

For source sign `-`, the extra normal is `(-1,-1)/sqrt(2)`. Put
`C=sin(phi)+cos(phi)` and `D=sin(phi)-cos(phi)`. In the first quadrant,
twice its projection is
\[
 a+b-CA-\tau DB
 \le (a_1+b_1)-(a_1-b_1)<2,
\]
because `C>=1`, `|D|<=1`. Twice its required support sum is at least
two, so this extra axis is also impossible there.

For `phi>=pi/2` every sign case already satisfies (1). Indeed `h` is
`1/2`-Lipschitz and vanishes at `pi/2`; hence
\[
 \phi-.18h(\phi)\ge\pi/2+.91(\phi-\pi/2),
\]
and
\[
 \mathcal C:=\phi-.18h+\sigma\ell_s-\tau\ell_t
 \ge\pi/2-2\ell_1>.927887>\gamma.                     \tag{7}
\]
Here and below `3.14159<pi<355/113` is the already established
elementary Machin bound.

It remains to consider the central source separator in `0<phi<pi/2`.
Twice its actual projection is
\[
 a+\sigma b+D A-\tau C B.
\]
Thus its exact separating margin is
\[
 M=a+\sigma b+D A-\tau C B-1-C\ge0.                  \tag{8}
\]
This follows directly from the scaled centers and the central unit
normal; the factor of two on both sides is essential.

Reflection followed by reversal preserves `phi`, `delta`, and the
cost, changes the ordered signs to `(-tau,-sigma)`, and exchanges
source and target axes. The four source sign cases below therefore
cover the retained target axes as well.

## 3. Initial barriers, tails, and support formula

The maximum of `a+sigma*b` is at the cut endpoint for `sigma=+`, and
at the axial endpoint for `sigma=-`. The derivative of the target
term in (8) is `-D*r-tau*C`. It is negative for `tau=+` and positive
for `tau=-`, since `r<1`, `C>=1`, and `|D|<=1`. Hence the following
are uniform upper bounds on the margin:

| Cases covered | Margin upper bound | Negative through |
|---|---|---:|
| All signs | `(a1+b1-1)+(a1+b1-1)sin(phi)-(1+a1-b1)cos(phi)` | `.35` |
| `--` | `(a0-1)+(a1+b1-1)sin(phi)-(1+a1-b1)cos(phi)` | `.6` |
| `-+` | `(a0-1)+(a0-1)sin(phi)-(a0+1)cos(phi)` | `1` |

Each expression increases in the first quadrant, so a single strict
endpoint comparison proves its whole initial barrier.

Since `sqrt(2)<1.42`, we have `0<=.18h<.0378`. The following tails
will finish the other intervals:
\[
\begin{array}{c|c|c}
\text{signs}&\text{tail begins}&\text{lower bound}\\\hline
 +- &1.05&1.05-.0378>\gamma\\
 -- &1.27&1.27-.0378-.321454>\gamma\\
 -+ &1.5543&1.09(1.5543)-.09(\pi/2)-2(.321454)>\gamma.
\end{array}                                             \tag{9}
\]
For the last row, use the Lipschitz bound from `pi/2` at `1.5543`,
and then that `x-.18h(x)` increases with slope at least `.91`.

Write `c0=-u*a0`, so `ell=c0+u*a+v*b`. For a multiplier `lambda>=0`,
subtract `lambda*M` from the cost. With `x=phi`, `s=sin(x)`,
`c=cos(x)`, this gives
\[
\begin{split}
 \mathcal C\ge F={}&x-.09(s+c-1)+\lambda(1+s+c)
                  +(\sigma-\tau)c_0\\
 &+\min(U_sa+V_sb)+\min(U_tA+V_tB),                    \tag{10}\\
 U_s={}&\sigma u-\lambda,\quad V_s=\sigma(v-\lambda),\\
 U_t={}&-\tau u-\lambda(s-c),\quad
 V_t=\tau(\lambda(s+c)-v).
\end{split}
\]
The full translated circle (2) supplies the unconditional lower bound
\[
 Ua+Vb\ge-U-\mathcal R\sqrt{U^2+V^2}.                 \tag{11}
\]
If `U>=0`, the functional is concave along the physical arc and its
minimum is at an endpoint. Otherwise its derivative is `-U*r+V`.
These facts suffice for every support choice below.

## 4. The complete support cover

In this table `a` denotes the axial endpoint, `b` the cut endpoint,
`a,b` both separate endpoint bounds, and `o` the full-circle bound
(11). All intervals include their endpoints.

| Signs | Interval | Multiplier | Source / target | Scalar argument |
|---|---|---|---|---|
| `++` | `[.35,1.2]` | `.39` | `a / a,b` | No interior minimum |
| `++` | `[1.2,pi/2]` | `.39` | `a / o` | Concavity |
| `+-` | `[.35,.6]` | `.55` | `o / b` | No interior minimum |
| `+-` | `[.6,.8]` | `.43` | `a / b` | No interior minimum |
| `+-` | `[.8,1.05]` | `.34` | `a / a,b` | Increasing |
| `--` | `[.6,.95]` | `.734-.4x` | `o / b` | One polynomial |
| `--` | `[.95,1.27]` | `.34` | `o / a,b` | Increasing |
| `-+` | `[1,1.3]` | `.4` | `o / a` | No interior minimum |
| `-+` | `[1.3,1.5543]` | `.365` | `b / o` | Concavity |

Here is a verification of every non-circular support choice.

* For a positive source with `lambda=.34,.39,.43`, `U_s<0` and
  `V_s>0`; hence its minimum is axial.
* In the first `++` interval, `C>1.28` gives `V_t>0`. If `U_t>=0`,
  concavity selects the endpoints; if `U_t<0`, the minimum is axial.
  Thus the two endpoint bounds suffice throughout.
* In the first `+-` interval, `D<0`, so `U_t=u-.55D>0`, while
  `V_t=v-.55C<0`. The functional decreases, selecting the cut.
  On the next interval, `D<.021` and `C>1.38` give the same strict
  signs with `lambda=.43`.
* For `lambda=.34` and negative target sign, the two endpoints always
  suffice in the first quadrant. If `U_t>=0`, use concavity. If
  `U_t<0`, then `lambda*D>u`; were `V_t<0` also true, we would have
  `lambda*C>v`, contradicting
  \[
    2\lambda^2=\lambda^2(C^2+D^2)<u^2+v^2.
  \]
  Thus `V_t>=0`, and the minimum in this case is axial.
* In the varying `--` row, `.354<=lambda<=.494`, `D<.232`, and
  `C>1.38`. The target derivative is uniformly at most
  \[
   .253(.494\cdot.232-u)+v-.354(1.38)<0.               \tag{12}
  \]
  The first term is positive and also bounds the possible positive
  part of `-U_t*r`; if `U_t>=0` that part is zero. Hence this row
  genuinely uses the cut endpoint throughout.
* In the first `-+` row, `D>0` and `C>1.23`. Thus `U_t<0`,
  `V_t>.4(1.23)-v>0`, selecting the axial target. In the last row,
  the source derivative is at most
  \[
   (u+.365)(.253)+.365-v<0,
  \]
  so the source is at the cut endpoint.

The bounds on `C` follow by its concavity and endpoint comparisons;
the bounds on `D` follow from its monotonicity in the first quadrant.
All other support entries are unconditional instances of (11).

## 5. Fixed-endpoint and circle scalars

For a fixed target endpoint `(A,B)` and constant multiplier, the
nonconstant part of (10) is
\[
 x+A_*\cos x+B_*\sin x,\quad
 A_*=\lambda(1+A+\tau B)-.09,\quad
 B_*=\lambda(1-A+\tau B)-.09.                          \tag{13}
\]
In each row marked "no interior minimum", the following fixed tests
hold: `A_*>0`, `B_*<0`, and the first derivative at the right endpoint
is negative. They are checked for both target endpoints in the `++`
row. Since the first derivative is strictly convex on the first
quadrant, its zero, if any, cannot be a negative-to-positive crossing
before a negative right endpoint. The scalar has no interior minimum.

For either target endpoint with `lambda=.34`, the exact amplitude
comparison `A_*^2+B_*^2<1` gives a strictly positive derivative.
Only the left endpoint is needed in those increasing rows.

For the two rows with a circle target, the remaining scalar is
\[
 x+\text{constant}+(2\lambda-.09)\sin x-.09\cos x
                  -\mathcal R N(x),                  \tag{14}
\]
where
\[
\begin{split}
 N^2&=(u+\lambda D)^2+(\lambda C-v)^2\\
    &=u^2+v^2+2\lambda^2
       +2\lambda[(u-v)\sin x-(u+v)\cos x].
\end{split}
\]
These norms are nonzero because `u^2+v^2<2*lambda^2`. Differentiation
of their squared norm gives the exact identity
\[
 N''+\frac N4=
 \frac{(u^2+v^2-2\lambda^2)^2}{4N^3}>0.               \tag{15}
\]
They increase on the stated intervals: the sign of their derivative
is the sign of `(u-v)cos(x)+(u+v)sin(x)`, which is positive already
at the left endpoint and increases through the first quadrant.

At `pi/2`, their norm bounds are
\[
 N<.5\quad(\lambda=.39),\qquad
 N<.47\quad(\lambda=.365).
\]
Consequently strict concavity of (14) follows respectively from
\[
\begin{split}
 .69\sin(1.2)&>.09\cos(1.2)+\mathcal R(.5)/4,\\
 .64\sin(1.3)&>.09\cos(1.3)+\mathcal R(.47)/4.
\end{split}                                           \tag{16}
\]
It again suffices to check the two endpoints.

Here are all eighteen scalar lower comparisons, directly from (10).
Every displayed bound is strict.

| Signs, multiplier, source/target | Angle | Cost greater than |
|---|---|---:|
| `++`, `.39`, `a/a` | `.35` | `.93165390` |
| Same | `1.2` | `.96736501` |
| `++`, `.39`, `a/b` | `.35` | `.93308297` |
| Same | `1.2` | `1.01078638` |
| `++`, `.39`, `a/o` | `1.2` | `.96464278` |
| Same | `pi/2` | `.92448679` |
| `+-`, `.55`, `o/b` | `.35` | `.97618308` |
| Same | `.6` | `.91873464` |
| `+-`, `.43`, `a/b` | `.6` | `.92317976` |
| Same | `.8` | `.91701035` |
| `+-`, `.34`, `a/a` | `.8` | `.95942374` |
| `+-`, `.34`, `a/b` | `.8` | `.95200094` |
| `--`, `.34`, `o/a` | `.95` | `.91318792` |
| `--`, `.34`, `o/b` | `.95` | `.91629877` |
| `-+`, `.4`, `o/a` | `1` | `.96406430` |
| Same | `1.3` | `.93326925` |
| `-+`, `.365`, `b/o` | `1.3` | `.93611106` |
| Same | `1.5543` | `.90994723` |

For reproducibility, use the root brackets (4),
`S11<=sin(x)<=S13`, `C14<=cos(x)<=C12` at positive rational
arguments, and `sin(pi/2)=1`, `cos(pi/2)=0`. Each norm is bounded
above by a rational with denominator `10^10`, whose square exceeds
the resulting rational upper bound on its square. These are fixed
arithmetic operations, not a search for a minimizing state.

## 6. The single varying-multiplier polynomial

Consider the `--` row on `[.6,.95]`, and write
\[
 \lambda=.734-.4x,
 \quad a^-=1.71322294,\quad a^+=1.71322295,
 \quad b^-=.4a^-,\quad b^+=.4a^+.
\]
The source circle and target cut in (10) give
\[
\begin{split}
 F={}&x+.09+2\lambda+u(1+a_1)+vb_1\\
 &+[\lambda(1+a_1-b_1)-.09]\cos x\\
 &+[\lambda(1-a_1-b_1)-.09]\sin x
       -\mathcal R\sqrt{(u+\lambda)^2+(v-\lambda)^2}.
\end{split}                                           \tag{17}
\]
Let `C6` and `S5` be the ordinary cosine and sine Taylor polynomials
through degrees six and five. Define the explicit degree-seven
polynomial
\[
\begin{split}
 T={}&x+.09+2\lambda+u(1+a^-)+vb^--\gamma\\
 &+[\lambda(1+a^--b^+)-.09]C_6(x)\\
 &+[\lambda(1-a^+-b^+)-.09]S_5(x),
\end{split}
\]
and the degree-fourteen polynomial
\[
 P=T^2-2Q\bigl((u+\lambda)^2+(v-\lambda)^2\bigr).       \tag{18}
\]
The cosine coefficient is positive and the sine coefficient negative.
On this interval `C6<=cos` and `sin<=S5`; all coordinate roundings
above are adverse. Thus `F-gamma` is at least `T` minus the displayed
norm term.

The quantity being squared is positive. In fact
\[
 C_6>1-.95^2/2-.95^6/720>0,
 \qquad S_5<.95+.95^5/120<1.
\]
Dropping the positive cosine term, and using the most negative sine
coefficient, gives
\[
 T\ge .6+2(.354)+u(1+a^-)+vb^--\gamma
          +.494(1-a^+-b^+)>.278.                      \tag{19}
\]

Substitute `x=.6+.35y` into (18). Its fifteen Bernstein coefficients
are strictly greater than the following positive integers divided by
`10^8`, in increasing index order:
\[
\begin{gathered}
6008661,\ 4521736,\ 3269000,\ 2241201,\ 1427808,\\
817238,\ 397075,\ 154297,\ 75489,\ 147054,\\
355411,\ 687182,\ 1129359,\ 1669462,\ 2295674.
\end{gathered}                                         \tag{20}
\]
For an explicit check, if the power coefficients after substitution
are `p_j`, coefficient `k` in the degree-14 Bernstein basis equals
\[
 \sum_{j=0}^k p_j\frac{\binom{k}{j}}{\binom{14}{j}}.
\]
The basis functions are nonnegative and sum to one on `[0,1]`.
Hence (20) proves `P>0` on the entire interval. Together with (19),
this proves `F>gamma` without an ambiguous squaring step.

## 7. Conclusion and equality scope

The initial barriers, complete support table, and tails overlap at
every endpoint. The two extra source directions were either impossible
or already covered by the angle tail. Reflected reversal supplies all
retained target directions. Thus every physical H/H pair in the
seven-ring satisfies the strict inequality (1).

This entry has no equality case for the rounded constant `.9099`.
It does not claim that isolated pairs allowing globally discarded
backward axes satisfy the same theorem, and it does not classify the
equality family at the sharp eight-square radius. Those are separate
scope statements. \(\square\)

## Arithmetic and restoration record

Run `python verify_high_high_whole_pair_hand.py`. Its 108 strict
comparisons include all root, derivative, barrier, endpoint, and
polynomial checks used here. The polynomial coefficient list (20)
is the same list independently checked in the earlier 83-comparison
version. The present source explicitly restores the full argument
and adds several elementary intermediate checks; it is a new
hash-bound version rather than the lost source of that earlier audit.

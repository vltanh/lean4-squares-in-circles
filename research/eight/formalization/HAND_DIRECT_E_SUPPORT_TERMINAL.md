# A direct E-circle support proves the sharp terminal at S <= 3/200

## 1. The complete conditional theorem

Consider seven exterior unit squares in a centered disk of squared radius
`r0 <= Q0 = 9789/2500`, each avoiding the open disk of radius `1/12`.
Use the cyclic roles `(H,G,A,B,T,D,E)` and canonical quarter offsets
`(-1,-1,0,0,1,1,2)`. Normalize A's physical frame to zero and G's to `t`.
Assume the following actual geometric hypotheses:

\[
 -4/5\le u_G\le-1/20,\qquad 1/20\le u_T\le4/5,
 \qquad 1/10\le t\le4/25,
\]
\[
 S=|\theta_B|+|\theta_T-\theta_B|+|\theta_D-\theta_T|
       +|\theta_E-\theta_D|+|\theta_H-t|\le3/200.
\tag{1}
\]

The intended original signed separators must be feasible: AB along the
positive f-axis of A or B; TB and DT along the positive e-axis of either
endpoint; ED along the positive f-axis of E or D; GA along G's positive
e-axis; HG along H's or G's positive e-axis; and HE along H's positive
f-axis. Here TB, DT, ED, HG and HE have respectively the directed center
differences B-T, T-D, D-E, G-H and E-H. Every permitted owner choice and
all simultaneous-owner ties are included.

**Theorem.** These hypotheses imply `r0 >= q_*`. If `r0 <= q_*`, then
`r0=q_*`, `S=0`, `t=t_*`, and the five anchors A,B,D,E,H are exactly the
stationary anchors. Thus the existing full equality-family theorem applies.

More precisely, at the stationary comparison `(q_*,u(q_*,t),t)`, the proof
below gives, whenever `r0<=q_*`,

\[
\boxed{
 (1-\mu_E)(r_0-q_*)\ge
 \mu_H M(q_*,t)+\sum_{i=A,B,D,H}\mu_i
     \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
     +D_E+\frac{S}{1000},}
\tag{2}
\]

where

\[
 D_E=F_E\mathbin\cdot(p_E+o_E)+\sqrt{q_*}\,|F_E|\ge0.
\tag{3}
\]

The stationary existence/uniqueness theorem proves `M(q_*,t)>=0`, with
its unique zero at `t_*`. All quantities in (2) are defined below.

This is a **conditional sharp theorem on the whole domain (1)**, not
an unrestricted capture theorem. In particular it does not assume that
mixed-owner rigidity, the G/T cuts, or the tilt window have already been
proved at `S<=3/200`. Those remain separate capture obligations. Unlike
the previous terminal, this theorem does not require the preceding
contraction to `S<=1/1000` once its stated owners and tilt are available.
No Lean source or historical certificate data is changed by this note.

## 2. Stationary data and the actual slider bounds

Import the whole-domain stationary identities and bounds from
`HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md`, Sections
2--6, and `HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md`. Their proofs
use the actual nested-circle formulas, not interval tables. In their
notation, all terminating decimals here are exact rationals:

\[
\begin{gathered}
 .895<u<.94,\quad l=2-u,\quad
 1.741<r<1.765,\quad1.641<U<1.671,\quad1.329<V<1.359,\\
 1.438<Y<1.467,\quad .533<v<.562,\quad1.897<w<1.906,\\
 .9868<c=\cos t,\quad .0995<s=\sin t<.162,
 \quad .1<\tan t<.164,\quad1.4<k_2<1.45.
\end{gathered}
\tag{4}
\]

The stationary edge weights satisfy

\[
 2/3<\omega<4/5,\quad .69<\beta<.78,\quad
 \alpha/\beta<.674,\quad 0<\delta,\epsilon<.87,
 \quad\epsilon>\beta.
\tag{5}
\]

Consequently `alpha<.526`. All five circle weights are positive, sum
to one, and satisfy the identities used in Section 3. The additional
stationary quantities are

\[
\begin{gathered}
 J=\frac YV\left(\frac1{1+\tan t\,v/w}-w\right),
 \qquad-1.029<J<-.98,\\
 X=\beta(l+J),\quad K=\beta(Y+J),\quad
 L=\epsilon s v/w=\delta-\epsilon c,\\
 \Delta=r-U>.07,\quad N=\omega n,\quad .41<n<.44,
 \quad K=\epsilon c+\delta(V-w).
\end{gathered}
\tag{6}
\]

The G/T cuts give `7/12<=a_G,a_T<1.396`. This follows from core avoidance
and the increasing farthest-corner expression, as in the existing capture
interface; it also holds for original contained centers, not only boundary
centers. For clarity, if `a<7/12` and `b<=.8a`, then `b<.5`, so core
avoidance would force `a-.5>=1/12`, a contradiction. At `a=1.396` and
`b/a=.05`, the farthest-corner squared norm exceeds Q0.

There is also the useful bound `b_G,b_T<.797`: if `b>=.797` and
`a>=b/.8`, the farthest-corner squared norm exceeds Q0 by at least

\[
 (.797/.8+.5)^2+(.797+.5)^2-Q_0=85969/16000000>0.
\]

Write the actual T center in the A frame as `(X_T,Z)`, and the G center
in its own physical frame as `b_G e_t-a_G f_t`. Since `|theta_T|<=S`,
rotation and (1) imply

\[
\begin{gathered}
 |X_T|<.797+1.396(.015)=.81794<.82,\\
 Z\ge(7/12)(1-.015^2/2-.8(.015))=.576267708\ldots>.576,\\
 Z\le1.396(1+.8(.015))=1.412752<1.413.
\end{gathered}
\tag{7}
\]

The ellipsis in the middle line abbreviates the exact fraction
`553217/960000`; no approximate comparison is needed. The G projection
parameter used by the existing first-derivative identities is

\[
 \eta=-a_G+k_2-1/2,
 \qquad -.496<\eta<11/30.
\tag{8}
\]

These are whole-domain bounds for the actual sliders. They require no
proximity of any center to an optimal configuration.

## 3. Complete four center squares and support E directly

Choose each original owner once. Put

\[
 x_1=\theta_B,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h=\theta_H-t.
\]

Their absolute values sum to S. Let the owner indicators `a,b,d,e,g`
be zero or one, with value one meaning respectively B owns AB, T owns
TB, D owns DT, E owns ED, and G owns HG. Then the exact owner frames are

\[
 b_0=a x_1,\quad u_0=x_1+b x_2,\quad
 v_0=x_1+x_2+d x_3,\quad d_0=x_1+x_2+x_3+e x_4.
\tag{9}
\]

For HG the actual normal is `e_t` if `g=1`, and `e_(t+h)` if `g=0`.
As usual `e_z=(cos z,sin z)`, `f_z=(-sin z,cos z)`. The actual forces are

\[
\begin{aligned}
 F_A&=\alpha f_{b_0}-\omega e_t,&
 F_B&=-\alpha f_{b_0}-\beta e_{u_0},\\
 F_D&=\beta e_{v_0}-\delta f_{d_0},&
 F_E&=\delta f_{d_0}-\epsilon f_{t+h},\\
 F_H&=\omega n_H+\epsilon f_{t+h},&
 F_T&=\beta(e_{u_0}-e_{v_0}),\\
 F_G&=\omega(e_t-n_H).
\end{aligned}
\tag{10}
\]

Use the existing actual corner offsets
`o_A=(e_0-f_0)/2`, `o_B=(e_(theta_B)+f_(theta_B))/2`,
`o_D=(-e_(theta_D)+f_(theta_D))/2`,
`o_E=-(e_(theta_E)+f_(theta_E))/2`, and
`o_H=-(e_(t+h)+f_(t+h))/2`.

For the four centers A,B,D,H apply the exact identity

\[
 \mu_i|p_i+o_i|^2+F_i\cdot p_i
 =\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
       -F_i\cdot o_i-\frac{|F_i|^2}{4\mu_i}.
\tag{11}
\]

For E instead use its actual containing disk. Under `r0<=q_*`,
Cauchy's inequality gives (3), hence

\[
 F_E\cdot p_E\ge -F_E\cdot o_E-\sqrt{q_*}|F_E|.
\tag{12}
\]

Subtract the nonnegative weighted actual separating gaps from the four
weighted corner inequalities. Equations (11)--(12) leave the four positive
center squares, D_E, and a scalar function of the five errors and actual
slider projections. This is the same scalar as in the previous terminal,
except that its E norm term is replaced by the direct support (12).

At zero errors stationarity gives

\[
 \delta=\epsilon(c+s v/w),\qquad
 \mu_E=\epsilon s/(2w),\qquad
 F_E^0=2\mu_E(w,v),\qquad |F_E^0|=2\mu_E\sqrt{q_*}.
\tag{13}
\]

Thus the new E support has the same first derivative as the old square
completion. Its reference value is smaller by `mu_E q_*`. The full scalar
reference value is therefore exactly

\[
                    (1-\mu_E)q_*+\mu_H M(q_*,t).
\tag{14}
\]

## 4. Uniform curvature of the direct E support

Keep the comparison weights fixed, and define

\[
 A(z)=\sqrt{\delta^2+\epsilon^2-2\delta\epsilon\cos z}.
\]

The actual argument is `z=t+h-d_0`, so `|z-t|<=S` and
`.085<=z<=.175`. Let `j=v/w<.297`, and put

\[
 r_E=\delta/\epsilon=c+s j,
 \qquad \rho_E=r_E-1=s\{j-\tan(t/2)\}>0.
\tag{15}
\]

Positivity follows from `j>.533/1.906` and
`tan(t/2)<=.08/(1-.08^2/2)<.081`. Also

\[
 0<\rho_E\le t(.297-t/2).
\]

Direct differentiation, without any Taylor substitution in the radicand,
gives

\[
 A''(z)=
 \frac{\delta\epsilon(\delta-\epsilon)^2\cos z
       -\delta^2\epsilon^2(1-\cos z)^2}{A(z)^3}.
\tag{16}
\]

Since `sin(z/2)>=.9987 z/2` for `0<=z<=.175`,
`A(z)>=sqrt(delta epsilon)*.9987 z`. Using (15) and `r_E>=1` in (16) gives

\[
 \frac{\sqrt{q_*}}2 A''(z)
 \le \frac{1.978788(.87)}2
       \frac{t^2(.297-t/2)^2}{\{.9987(t-.015)\}^3}.
\tag{17}
\]

The right side decreases throughout `.1<=t<=.16`: the logarithmic
derivative of its varying factor is

\[
 2/t-1/(.297-t/2)-3/(t-.015)<0.
\]

Its value at `.1` is the exact rational number

\[
 \frac{466798991422400}{543762688679571}<.859.
\tag{18}
\]

It follows, by integrating the second-derivative bound on the entire
segment between t and its actual argument, that the direct E support
remainder is at least

\[
 -.859(h-d_0)^2
 \ge-.859 S\bigl(|x_1|+|x_2|+|x_3|+e|x_4|+|h|\bigr).
\tag{19}
\]

Only an upper bound on A'' is needed. Negative curvature of A improves
(19); it has not incorrectly been replaced by an unproved absolute bound.
There is no coefficient proportional to `1/sin(t)` in this estimate.

## 5. All the other smooth second derivatives

Remove the aligned cusp terms `lambda_i |sin(x_i)|/2` from the scalar.
Call the remaining smooth function `F`, including the direct E support,
and call `F_rest` the result of also removing that E support. Every
coefficient below is fixed at the comparison `(q_*,u(q_*,t),t)`.

### 5.1 The four other force norms

Apart from a constant, these are exactly

\[
 K_A\sin(t-a x_1)-K_B\sin((1-a)x_1+b x_2)
       +K_D\sin(-(1-d)x_3-e x_4)+g K_H\sin h,
\tag{20}
\]

where

\[
 K_A=\alpha r/c<.942,\quad K_B=\beta l<.862,
 \quad K_D=\delta V<1.183,
 \quad K_H=\epsilon k_1<1.238.
\]

Along the full segment of errors of norm at most `.015`, every Hessian
entry of (20) has absolute value less than `.178`. Indeed the only
possible overlap is the A and B terms on the x1 diagonal, bounded by
`.942(.175)+.862(.015)<.178`. The B, D, H terms otherwise involve disjoint
coordinate groups and are bounded by `.013`, `.018`, `.019`, respectively.

In the x1 row when A owns AB, and in the x2 row when T owns TB, only
the B term can occur, so that entire row is bounded by `.013`.
If D owns ED, the x4 row of (20) is zero.

### 5.2 Support widths and selected corner offsets

Combining these per actual edge gives an especially simple formula.
After division by the edge weight, the AB and ED terms are

\[
                 1+\cos x+(\sin x+|\sin x|)/2.
\]

For TB or DT the term is either
`1+cos(x)/2+|sin(x)|/2` or
`1/2+cos(x)+sin(x)/2+|sin(x)|/2`.
For HG it is either `1+cos(h)/2+|sin(h)|/2` or
`1/2+cos(h)-sin(h)/2+|sin(h)|/2`.
These identities follow by taking the two dot products with the offsets
in Section 3. They include either actual owner.

After removing the cusp, each aligned term therefore has second
derivative of absolute value at most `lambda_i(1+.015/2)` and depends
on just its own error coordinate. The mixed GA term is constant;
the mixed HE term is exactly

\[
                         \epsilon[1+\sin(t+h-\theta_E)].
\tag{21}
\]

Every Hessian entry of (21) has absolute value less than
`.87(.175)<.153`. In particular the combined smooth support/offset
entries are bounded by `.877+.153`. On an AB or TB diagonal one may
use `.78(1+.015/2)=.78585` instead of `.877`; on the HG diagonal use
`.8(1+.015/2)=.806`.

### 5.3 The actual sliders and the shared-prefix cancellation

The T term is

\[
 \beta\{X_T(\cos u_0-\cos v_0)+Z(\sin u_0-\sin v_0)\}.
\tag{22}
\]

The coefficient vector of `u_0` in (9) is coordinatewise no larger than
that of `v_0`; each entry is zero or one. Thus a Hessian entry is either
zero, one endpoint term, or a difference of the two endpoint terms.
By (7), a single endpoint has absolute value at most

\[
 .78(.82+1.413(.015))<.657.
\]

A difference of endpoint terms is bounded more sharply by

\[
 .78\{.82(.015)^2+1.413(.015)\}<.017,
\tag{23}
\]

using `|cos v_0-cos u_0|<=S |v_0-u_0|` and the sine Lipschitz bound.

In the x1 row, both owner phases have coefficient one. The same is true
in the x2 row when T owns TB. Their diagonal entries therefore use
(23); all off-diagonal entries still use `.657`. This is a symbolic
shared-prefix argument for every owner choice, not 32 separate tests.

The G term is zero when G owns HG. Otherwise it is

\[
               \omega\{b_G(1-\cos h)+a_G\sin h\},
\]

whose only second derivative has absolute value less than
`.8(.797+1.396(.015))<.655`. T and G have disjoint error coordinates,
so their Hessian bounds do not add in any entry. Neither slider has
an x4 derivative.

### 5.4 A weighted Taylor bound on all five errors at once

The preceding estimates prove the following row bounds for the Hessian
of `F_rest`, at every point of the whole error segment:

* Every row has entries of absolute value less than
  `.178+.877+.153+.657=1.865`.
* The x1 row when A owns AB, and x2 row when T owns TB, are bounded by
  `max(.013+.78585+.153+.017, .013+.153+.657)<.970`.
* The h row is bounded by `.019+.806+.153+.655=1.633`.
* If D owns ED, the x4 row is bounded by `.877+.153=1.030`.

For any symmetric Hessian with row bounds `m_i`,

\[
 \left|\sum_{ij}H_{ij}x_ix_j\right|
 \le S\sum_i m_i|x_i|.
\]

Integrate Taylor's second derivative, then add the E estimate (19).
This proves

\[
 F(x)-F(0)-DF(0)x\ge -S\sum_i c_i|x_i|,
\tag{24}
\]

where one may take `c_AB=27/20` when A owns AB, `c_TB=27/20` when T owns
TB, `c_ED=13/25` when D owns ED, and `c_HG=17/10`; every other coefficient
can be `9/5`. For example the two small-reserve rows cost less than
`.970/2+.859=1.344<27/20`, the generic rows cost less than
`1.865/2+.859<9/5`, and the D-owned ED row has no E charge.

This establishes one simultaneous Taylor bound. It does not allocate
an independent copy of S to each pair.

## 6. First derivatives dominate the entire error remainder

Because of (13), the direct support has exactly the old terminal first
derivatives. With the error directions of Section 3, their smooth
coefficients are

\[
\begin{aligned}
 g_{AB}&=\alpha/2-X-a\alpha\Delta,\\
 g_{TB}&=-\beta(Z+J)\quad(b=0),\qquad
           -\beta(3/2-u+J)\quad(b=1),\\
 g_{DT}&=\beta/2-K\quad(d=0),\qquad-\beta(Z+J)\quad(d=1),\\
 g_{ED}&=\delta/2-\epsilon c\quad(e=0),\qquad
            \delta/2-K\quad(e=1),\\
 g_{HG}&=-\omega/2+N-(1-g)\omega\eta.
\end{aligned}
\tag{25}
\]

These identities also follow directly by differentiating (10)--(12),
(20)--(22). The aligned cusp has coefficient `lambda_i/2`.
Let `r_i=lambda_i/2-|g_i|` be its first-order reserve.

The small AB and TB reserves in (24) exceed

\[
                         X> .69(.031)=.02139.
\tag{26}
\]

For the A-owned AB choice the other reserve is `alpha-X`, which exceeds
`alpha(1-Delta)-X>.320`; for the T-owned TB choice it is `beta-X`, also
larger. For B-owned AB the two reserves are `X+alpha Delta` and
`alpha(1-Delta)-X`. The former exceeds
`.02139+(2/3)(.599)(.07)>.049`, and the latter exceeds

\[
 .69\{.98-1.105(.765)/1.641\}>.320.
\]

The varying T-slider reserves are both greater than

\[
 .69\min\{.5-1.413+.98,\ .5+.576-1.029\}
 =.69(.047)=.03243.
\tag{27}
\]

The other DT reserves are `K` and `beta-K`, both greater than `.28`
by the existing stationary bounds. For E-owned ED they are `K` and
`delta-K`; the latter exceeds

\[
 .69\{1.438/1.359-1.467+.98\}>.394.
\]

For D-owned ED its small reserve is

\[
 L=\epsilon s v/w>.69(.0995)(.533)/1.906>.019;
\tag{28}
\]

the other reserve `epsilon c` is larger. Finally (6), (8) give for HG,
uniformly for both owners,

\[
 r_{HG}>\frac23\min\{.41-11/30,\ 1-.496-.44\}
                         =13/450.
\tag{29}
\]

Thus every generic reserve in (24) is greater than `.032`; the two
special AB/TB reserves exceed `.02139`; the D-owned ED reserve exceeds
`.019`; and the HG reserve exceeds `13/450`.

The elementary sine remainder gives

\[
 \sum_i\frac{\lambda_i}{2}|\sin x_i|
 \ge\sum_i\frac{\lambda_i}{2}|x_i|
                      -\frac{.87}{12}S^3.
\tag{30}
\]

For `S<=.015`, the weakest of the resulting per-unit-error reserves
is already

\[
 .02139-\frac{27}{20}(.015)-\frac{.87}{12}(.015)^2
                 =.0011236875>1/1000.
\tag{31}
\]

The other three comparisons are larger: use respectively
`.032-(9/5)(.015)`, `.019-(13/25)(.015)`, and
`13/450-(17/10)(.015)`, and subtract the same cusp correction.
Equations (24)--(31) prove that the complete angular part is at least
`S/1000`, with strict reserve for `S>0`. The bound includes zero errors
and all closed owner and coordinate boundaries.

## 7. Sharpness, equality and remaining capture obligations

Combining (11)--(14) and Section 6 proves (2). Every term on its right
is nonnegative. Since `1-mu_E>0`, no `r0<q_*` is possible. If `r0=q_*`,
then `S=0`, the family defect is zero, and all four completed center
squares and D_E vanish. The family uniqueness theorem gives `t=t_*`.
At zero errors `F_E=2mu_E(w,v)` is nonzero; equality in the disk support
(12) forces `p_E+o_E=(-w,-v)`. This recovers the fifth stationary anchor,
not merely a missing one-sided bound for E. The existing weak slider
and central-square conditions then give exactly the full five-parameter
equality family and its converse.

The theorem preserves all original intended owner choices and works with
the untouched actual centers. It has no local position box, angle mesh,
Bernstein coefficient row, sampled stationary point, or external acceptance
claim as a premise. The numerical constants in (18), (23), and (31) are
single explicitly displayed rational comparisons in whole-domain proofs.

This removes the **small-mismatch input of the sharp terminal**, subject
to its explicitly stated G/T cuts, tilt window and full intended owners.
It does not itself prove mixed-owner or tilt capture at `S<=3/200`, nor
the preceding global tangent cuts or contractions. Those logical boundaries
must be retained when updating the capture roadmap.

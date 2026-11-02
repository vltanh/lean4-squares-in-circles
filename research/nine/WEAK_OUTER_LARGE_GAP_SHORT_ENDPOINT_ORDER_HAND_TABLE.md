# The right short endpoint lies above the weak outer pair

November 2, 2026. Computer-assisted discovery followed by the complete
physical reduction and rational finite table below. The entire table has
passed an independent exact arithmetic replay. No Lean, Lake, or CI.

This is a complete theorem on the original `001/00` domain after the
transverse sign is normalized. It is not, by itself, a whole-mask closure.
Its reflection and simultaneous chain reversal have the corresponding
unchanged-original conclusions.

## 1. Original-square statement

Put

\[
 Q=1105/256,\qquad r=\sqrt Q<133/64,\qquad
 \rho=91/60,\qquad a=46,\quad b=27/2,\quad T=211/4.
\]

Retain the nine original physical squares of the fixed `001/00`
predicate. Write its main chain as A,B,C,D and its actual short chain
as E,F,G. The two other original squares keep all their physical
constraints. Choose the transverse sign so that

\[
 v=y_D-y_C\ge7/30.
\]

**Theorem.** The original right short endpoint satisfies

\[
                         \boxed{y_G>y_D.}                 \tag{1}
\]

The conclusion holds at closed Q, and the proof retains the closed
boundary `x_D-x_C=h_C+h_D` as well. It does not require a bound
`v<=5/8`, a main-angle restriction, an assumed physical separator
owner, or any restriction on the two unselected original squares.
In conjunction with the already proved exclusion of `|v|<=7/30`, it
covers every remaining normalized configuration of this mask.

For a square S, write

\[
 h_S=(|u_{S,x}|+|v_{S,x}|)/2,\qquad g_S=1/(4h_S).
\]

The universal center-radius bound is `|c_S|<rho`. One direct proof is
that the largest squared corner norm is
`|c_S|^2+|c_S dot u_S|+|c_S dot v_S|+1/2`, which is at least
`|c_S|^2+|c_S|+1/2`. Hence
`|c_S|<=sqrt(Q-1/4)-1/2<91/60`.

## 2. A necessary three-original subsystem

The first two actual main links and the actual short chain give

\[
 x_C-x_A\ge h_A+2h_B+h_C\ge3/2+h_C,
 \qquad x_G-x_E\ge h_E+2h_F+h_G\ge3/2+h_G.
\]

Therefore

\[
 x_C>h_C-1/60,\qquad x_G>h_G-1/60.                    \tag{2}
\]

Apply the accepted physical pair cap to the unchanged original pair
(A,E), in the leftward endpoint convention:

\[
 a(-x_A-h_A)+b(-x_E-h_E)\le T.
\]

The two chains bound its left side below by
`a(1-x_C+h_C)+b(1-x_G+h_G)`. Consequently

\[
                 a(x_C-h_C)+b(x_G-h_G)\ge b/2=27/4.    \tag{3}
\]

The original cone comparison for C,D and their contained aligned
inset squares give, with `d=x_D-x_C`,

\[
 d\ge v\ge7/30,\qquad d\ge g_C+g_D,\qquad
 d<h_C+h_D.                                           \tag{4}
\]

In the finite table the last strict inequality is relaxed to `<=`;
all three original corner systems and all three original physical
pairs C/D, C/G, D/G remain. Equations (2) are likewise relaxed to
closed inequalities. Exclusion of this larger three-original domain
therefore proves (1) for the full original-nine mask.

No seven-square packing is silently treated as nine. A smaller
subsystem is used only after the necessary inequalities (2)--(4)
have been proved from the original configuration.

## 3. The horizontal D/G gap and the sign of every usable normal

Set `Delta=x_D-x_G`. From (4) and `h+g>=1`,

\[
 x_C-h_C\le x_D-1-g_D,
 \qquad x_G-h_G\le x_D-\Delta-1/2.
\]

Combining these with (3) yields

\[
 b\Delta\le(a+b)(x_D-1)-a g_D.
\]

Containment gives `x_D+h_D<=r`. The function

\[
 (a+b)h+\frac a{4h}
\]

is increasing on `h>=1/2`, because its derivative is at least `b>0`.
Its value at `1/2` is `a+b/2=T`. Thus

\[
 b\Delta\le(a+b)(r-1)-T<1459/128,
 \qquad \boxed{\Delta<1459/1728<1.}                   \tag{5}
\]

For the other sign, (2),(4) give

\[
 x_D>h_C-1/60+g_C+g_D\ge59/60+g_D,
\]

whereas `x_G<rho`. Hence

\[
 x_G-x_D<8/15-1/(2\sqrt2)<1.                           \tag{6}
\]

Suppose, for contradiction, `y_G<=y_D`. A separating unit normal n,
pointing from D to G, with `n_y>=0`, would obey

\[
 n\cdot(c_G-c_D)\le |x_G-x_D|<1,
\]

while the sum of the two physical supports is at least one. Therefore
**every usable owned D/G separator has `n_y<0`**. This is an implication
of the unchanged physical geometry, not an imposed separator choice.

For C/D, every usable normal has at least one positive component,
since both components of `(d,v)` are positive. These two exact sign
facts are the only omitted ownership branches in the finite table.

## 4. A finite table with three orientation coordinates

Represent each of the three unchanged original frames by

\[
 u_i=\frac{(1,t_i)}{\sqrt{1+t_i^2}},\qquad
 v_i=\frac{(-t_i,1)}{\sqrt{1+t_i^2}},\qquad -1\le t_i\le1.
                                                               \tag{7}
\]

A quarter-turn of the frame does not change its physical square, so
(7) represents every original orientation. There are eight initial
closed boxes, obtained by taking each `t_i` in either `[-1,0]` or
`[0,1]`; their common boundary faces are retained.

The finite forest is
`computer_assisted/weak_outer_hand_G_order_certificate.json.gz`.
Every internal angle node bisects one rational interval and retains
both closed children. Every separator node branches over the signed
axes owned by the relevant original pair, in the order D/G, C/G,
C/D. Only the normals proved unusable in Section 3 may be omitted.
The independent replayer reconstructs this union itself.

At each terminal, six real center variables remain. The certificate
contains nonnegative rational multipliers proving a contradiction
from necessary linear inequalities in those same six variables.
Thus a leaf is an explicit rational inequality identity, not the
outcome of a numerical optimization or a list of sampled poses.

### 4.1. Exact support bounds on a closed angle interval

For a fixed rational vector `w=(p,q)`,

\[
 H_i(w)=\frac{|p+qt_i|+|q-pt_i|}{2\sqrt{1+t_i^2}}.
                                                               \tag{8}
\]

Its minimum on an interval occurs at an endpoint or at one of the
projection sign changes `t=-p/q`, `t=q/p` that belongs to the
interval. Indeed, on a fixed-sign interval expressed in angle
coordinates, (8) is a positive sine-cosine expression whose second
derivative is its negative. It is concave and has no strict interior
minimum. All zero denominators are handled by omitting the irrelevant
sign-change formula.

For each interval let `[h_i^-,h_i^+]` enclose its halfwidths, and put
`g_i^-=1/(4h_i^+)`. Since `(1+|t|)/(2sqrt(1+t^2))` increases with
`|t|` on `[0,1]`, these bounds come from the interval endpoints and
zero, when present.

The lower support required by an owned separator between i,j is

\[
 \frac{1+|\cos(\theta_j-\theta_i)|
             +|\sin(\theta_j-\theta_i)|}{2}.
                                                               \tag{9}
\]

If the two angle intervals overlap, one is a valid lower bound.
Otherwise the minimum is bounded by the smaller endpoint value of
`(1+cos(delta)+|sin(delta)|)/2` on their signed difference interval.
That function is concave on each sign half of `[-pi/2,pi/2]`.
The two endpoint values are obtained directly from rational slopes:

\[
 \frac12\left(1+
   \frac{1+t_i t_j+|t_j-t_i|}
        {\sqrt{(1+t_i^2)(1+t_j^2)}}\right).             \tag{10}
\]

Every radical is enclosed outward on the exact grid `2^-48` by integer
square comparisons. Divisions use the appropriate positive lower or
upper endpoint. Neither the producer's floating bounds nor its claimed
reserves are accepted by the independent replayer.

### 4.2. The center rectangles

Equations (2),(4) and the universal center bound imply

\[
\begin{aligned}
 h_C^- -1/60&\le x_C\le\rho-g_C^- -g_D^-,\\
 h_C^- -1/60+g_C^-+g_D^-&\le x_D\le\rho,\\
 h_G^- -1/60&\le x_G\le\rho.
\end{aligned}                                         \tag{11}
\]

All lower bounds in (11) are positive. Let `l_i` denote one of them,
and set `k_i^-=sqrt(max(0,1/2-(h_i^+)^2))`, bounded below outward.
An actual corner in the outward quadrant of a center `(x_i,y_i)` has
offsets either `(h_i,k_i)` or `(k_i,h_i)`, with signs chosen toward
the center. Therefore

\[
 |y_i|\le\min\!\left\{\rho,
 \max\!\left(
 \sqrt{(Q-(l_i+h_i^-)^2)_+}-k_i^-,
 \sqrt{(Q-(l_i+k_i^-)^2)_+}-h_i^-\right)\right\}.       \tag{12}
\]

A negative radicand excludes that corner alternative; replacing it by
zero is a harmless relaxation in the displayed maximum. A negative
resulting upper bound itself excludes the entire physical interval.
All operations in (11)--(12) are reconstructed with directed rational
rounding.

### 4.3. The complete linear row list

The rows consist of the following necessary inequalities:

1. The six center coordinate intervals (11)--(12).
2. For each original i and each primitive integer vector
   `(p,q)` with `-4<=p,q<=4`, not both zero,
   `p x_i+q y_i<=sqrt(Q(p^2+q^2))-H_i^-(p,q)`.
   These are ordinary circle-support consequences of its original
   four-corner containment.
3. Equations (3),(4), the contradiction assumption `y_G<=y_D`,
   and `x_D-x_G<=1459/1728`, all weakened with the interval halfwidth
   bounds in the direction that enlarges the allowed domain.
4. The chosen original physical separator inequalities, linearized
   outward as described next.

For a selected normal whose coordinate intervals are N_x,N_y, let m
be the vector obtained by rounding their midpoints to multiples of
`2^-30`. If the center difference coordinate is in D_j, then

\[
 n\cdot(c_j-c_i)\le m\cdot(c_j-c_i)
       +\sum_{k=x,y}\max\{ed:e\in N_k-m_k,\ d\in D_k\}.
\]

The maximum of each bilinear product is at an interval corner.
Combining this bound with (9)--(10) gives the necessary linear row

\[
 m\cdot(c_j-c_i)\ge H_{ij}^-
       -\sum_{k=x,y}\max\{ed:e\in N_k-m_k,\ d\in D_k\}.
                                                               \tag{13}
\]

The difference intervals are obtained from (11)--(12). For D/G they
are intersected with `-1459/1728<=x_G-x_D<=1` and `y_G-y_D<=0`.
For C/D they are intersected with
`g_C^-+g_D^-<=d<=31/30` and `7/30<=v<=31/30`.
The bound `d<31/30` follows from `x_C>29/60` and `x_D<91/60`.
Every intersection therefore retains the same actual original centers.

### 4.4. The rational contradiction at every leaf

Write the reconstructed rows as `A_j X<=b_j`, with X the six original
center coordinates. A terminal supplies nonnegative integer weights
`w_j`, interpreted as multipliers `lambda_j=w_j/2^40`.
Let

\[
 r_0=\sum_j\lambda_j A_j,
 \qquad b_0=\sum_j\lambda_j b_j.
\]

Every original center coordinate is in `[-rho,rho]`. Thus the single
strict rational comparison

\[
                     -b_0-\rho\sum_{k=1}^6|(r_0)_k|>0 \tag{14}
\]

is a contradiction: the weighted rows give `r_0 X<=b_0`, whereas
`r_0 X>=-rho sum |(r_0)_k|>b_0`.

Exact cancellation is not assumed. The displayed residual term pays
for every nonzero coefficient remaining in the sum. The same physical
center variables are used in all rows.

## 5. The complete finite cover and exact replay

The eight closed root boxes have the following complete subtrees.
The signs identify `t_C,t_D,t_G` in that order; minus means `[-1,0]`
and plus means `[0,1]`.

| Root | Nodes | Strict rational leaves |
|---|---:|---:|
| --- | 5,279 | 2,996 |
| --+ | 3,552 | 2,169 |
| -+- | 8,303 | 4,603 |
| -++ | 6,838 | 3,946 |
| +-- | 3,211 | 1,972 |
| +-+ | 3,468 | 2,188 |
| ++- | 12,865 | 6,883 |
| +++ | 18,781 | 9,995 |
| **Total** | **62,297** | **34,752** |

There are 26,145 angle splits and 1,400 separator splits; the maximum
depth is 18. Every root and every child is covered. There is no unresolved
frontier. Every leaf satisfies (14), with a uniform positive lower bound

\[
                         608951/10^{12}>0.              \tag{15}
\]

The exact least reserve, before rounding down for (15), is recorded in
`weak_outer_hand_G_order_exact_replay.json`. The compressed finite table
has SHA-256

`d5699c099813ad3b078bbd7c91c87081c210d1c8588f348546312a2454500fc8`.

Five damaged controls were rejected: an omitted orientation root, an omitted
closed angle child, an omitted owned-separator child, a false whole-root leaf,
and a negative multiplier. The reproducible control program and exact report
are `weak_outer_hand_G_order_controls.py` and
`weak_outer_hand_G_order_rejection_controls.json`.

The independent source `weak_outer_hand_G_order_verify.py` imports no
producer or numerical optimizer. It reconstructs each closed interval,
all necessary rational rows, the complete signed-owner union, and every
strict rational combination. The numerical producer is only a search
for these finite identities.

Sections 2--4 prove that every purported original configuration with
`y_G<=y_D` enters this complete table. Section 5 contradicts every
terminal. This proves (1).

## 6. Consequence for the signed endpoint cap

Equations (5)--(6) give `|x_G-x_D|<1`. After (1), every usable physical
normal from D to G must have positive vertical component: a normal with
nonpositive vertical component would have support below one exactly as
in Section 3. Consequently a signed endpoint cap whose hypotheses
require an upward original D/G separator may be applied with that
premise now proved.

This consequence preserves the original endpoint G. It does not replace
G by another upper witness or confer a new cone comparison on a square
that was not selected by the fixed mask.

## 7. Scope

The theorem settles an entire original geometric alternative and can be
used throughout the normalized weak-outer mask, including the large-gap
range above 5/8. It earns no independent fixed-mask closure. The remaining
branches, the unrestricted nine-square bound, and equality classification
must still be assembled with their other required physical theorems.

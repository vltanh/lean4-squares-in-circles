# Positive-tilt weak-outer transfer through transverse gap 2/3

November 2, 2026. Complete hand argument with a separate exact scalar
check. This extends the positive-tilt transfer used in the 5/8 assembly.
The original physical squares and the strict weak bit are retained.
No Lean, Lake, or CI.

## 1. Statement and the original span bound

Retain the original `001/00` predicate at `Q=1105/256`, normalize the
transverse sign, and put

\[
 d=x_D-x_C>0,\qquad 0\le v=y_D-y_C\le V:=2/3.
\]

Assume that the unchanged original D has canonical nonnegative tilt,
with side frame `(alpha,beta),(-beta,alpha)`, where
`alpha>=beta>=0` and `alpha^2+beta^2=1`. Put

\[
 h=(\alpha+\beta)/2,\quad j=(\alpha-\beta)/2,\quad
 \tau=46\alpha+\frac{529}{16}\beta-46.
\]

Thus `tau/46=alpha+(23/32)beta-1`, the already proved signed endpoint
cap toll. We prove the strict transfer

\[
                     d+h_C-h_D+\tau/46>1.             \tag{1}
\]

The first two actual main links, the universal original-center radius
`rho=91/60`, and `x_D+h_D<=sqrt(Q)<133/64` give

\[
 x_C>h_C-1/60,\qquad
 d+h_C+h_D<133/64+1/60=2011/960.                     \tag{2}
\]

## 2. Every original owned separator is shallow

Let n be any usable separating unit normal of the original C/D pair,
owned by an axis of one of those two squares and directed from C to D.
Its horizontal component is positive: otherwise its center projection
would be at most `v<=2/3`, whereas its physical support sum is at least one.
Write `c=n_x>0`, `s=|n_y|`, and `t=s/c`.

The owner's normal support is exactly 1/2 and its coordinate halfwidth
is `(c+s)/2`. For the other unchanged square S the complete free-frame
support inequality, proved in
`WEAK_OUTER_SIGNED_SMALL_GAP_TRANSFER.md`, is

\[
 H_S(n)+c h_S\ge(1+c^2+cs)/2.
\]

Using `n_y v<=sV`, adding both coordinate halfwidths to the physical
separation inequality, and writing `c=cos(phi),s=sin(phi)` gives

\[
 d+h_C+h_D\ge J_V(\phi):=
 \sec\phi+\cos\phi+\sin\phi-V\tan\phi.             \tag{3}
\]

This includes both original owners and both signs of the vertical normal.
Over `0<=phi<pi/2`,

\[
 J_V'(\phi)=\frac{\sin^3\phi+\cos^3\phi-V}{\cos^2\phi}>0,
\]

because `sin^3(phi)+cos^3(phi)>=1/sqrt(2)>2/3`. At `tan(phi)=1/3`,

\[
 J_V(\phi)=\frac{22}{3\sqrt{10}}-\frac29>\frac{2011}{960}.
\]

The last comparison is equivalent, after multiplying positive factors
and squaring, to

\[
                    21120^2-10\cdot6673^2=765110>0.
\]

Together with (2)--(3), this proves for **every usable original owned
normal** that

\[
                              0\le t<1/3.             \tag{4}
\]

## 3. Only two transfer endpoints are needed

Use the support reduction from the positive-tilt transfer source, with
the new value `V=2/3`. For either vertical sign, (4) lies within the
range where the comparison of the two D chiralities is valid. With

\[
 A(t)=\frac{\sqrt{1+t^2}}2+\frac{1+t}{2\sqrt{1+t^2}},
 \qquad t_D=\beta/\alpha,
\]

the original physical pair satisfies

\[
 d+h_C-h_D\ge
 \begin{cases}
 F_-(t)=A(t)-t(j+V),&t\le t_D,\\
 F_+(t)=A(t)-\beta+t(h-V),&t\ge t_D.
 \end{cases}                                         \tag{5}
\]

The exact derivative identity

\[
 A''(t)=\frac{3t(t-1)}{2(1+t^2)^{5/2}}
\]

shows that `A'` has its global minimum at `t=1`, with
`A'(1)=1/(2sqrt(2))`. Therefore

\[
 F_+'(t)\ge\frac1{2\sqrt2}+\frac12-\frac23>0
 \quad(t\ge0).                                      \tag{6}
\]

Also `F_-` is concave on `[0,1/3]`. Equations (4)--(6) reduce the entire
transfer to `t=0` and `t=min(t_D,1/3)`. In particular the old slope-one
endpoint is unnecessary in this narrower owned-normal domain.

At zero, `F_-(0)+tau/46=1+tau/46`. If `beta>0`, write
`z=(1-alpha)/beta=beta/(1+alpha)<=sqrt(2)-1<1/2`; then

\[
 \tau/46=\beta(23/32-z)>0.                           \tag{7}
\]

## 4. The remaining endpoint, with all D tilts covered

### 4.1. The original D slope is at most 1/3

If `0<t_D<=1/3`, the common value at the kink is
`F_-(t_D)=F_+(t_D)=(1-V beta)/alpha`. Its toll-adjusted surplus over one
is exactly

\[
 \frac\beta\alpha
 \left(\frac{23}{32}\alpha+z(1-\alpha)-\frac23\right).
\]

Here `alpha>=3/sqrt(10)`, so the bracket is strictly positive:

\[
 \frac{23}{32}\alpha+z(1-\alpha)-\frac23
 \ge\frac{69}{32\sqrt{10}}-\frac23>0,
\]

where `207^2-10*64^2=1889>0`. This closes the whole small-slope D range.

### 4.2. The original D slope is at least 1/3

If `t_D>=1/3`, the second endpoint is `t=1/3`. Substitution in (5) gives
the exact surplus

\[
 F_-(1/3)+\tau/46-1
 =\frac{11}{3\sqrt{10}}-\frac{20}{9}
           +\frac56\alpha+\frac{85}{96}\beta.        \tag{8}
\]

The last two terms are a positive linear combination of cosine and sine
on the closed D-angle interval `[atan(1/3),pi/4]`, hence are concave.
Their minimum is at an endpoint. At `atan(1/3)`, (8) becomes

\[
 \frac{677}{96\sqrt{10}}-\frac{20}{9}>0,
 \qquad 6093^2-10\cdot1920^2=260649>0.
\]

At `pi/4`, (8) becomes

\[
 \frac{11}{3\sqrt{10}}+\frac{55}{32\sqrt2}-\frac{20}{9}>0.
\]

Indeed `sqrt(10)<19/6` and `sqrt(2)<10/7`, so this value is greater than

\[
                 \frac{22}{19}+\frac{77}{64}-\frac{20}{9}
                       =\frac{1519}{10944}>0.
\]

Both D-angle endpoints, and therefore their entire closed interval, have
strict positive surplus. Concavity of `F_-`, (6), and (7) prove (1) for
every `beta>0`.

## 5. The aligned boundary and the original endpoint caller

If `beta=0`, then `t_D=0`, `tau=0`, and `F_+(0)=1`. Equation (6) gives
`F_+(t)>1` for every `t>0`. A usable horizontal normal would assert
`d>=h_C+h_D`, contrary to the original strict weak bit. Thus (4) has
`t>0`, proving (1) on the aligned boundary as well.

For `7/30<=v<=2/3`, the already complete G-order forest supplies
`y_G>y_D`. The proved horizontal D/G localization makes every usable
D/G separator point upward. Hence the signed right cap and ordinary
left cap may be added exactly as in
`WEAK_OUTER_LOW_GAP_HAND_TABLE_ASSEMBLY.md`: (1) makes the weighted main
and short spans strictly exceed `2*46+27/2=211/2`, while their caps bound
the same expression above by `211/2`. This is a contradiction at closed Q.
The inherited theorem handles `0<=v<=7/30` without an order-table premise.

The companion `verify_weak_outer_positive_two_thirds_arithmetic.py` checks
every displayed rational comparison and coefficient identity. The new
normal bound, endpoint analysis, and strictness are hand arguments on
complete continuous domains; no sampled pose or numerical optimizer is
used as proof.

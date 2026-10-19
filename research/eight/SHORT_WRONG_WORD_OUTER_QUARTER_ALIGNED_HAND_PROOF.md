# Wrong word 0010111: the six coupled quarter contacts

## Statement

This note proves the six near-aligned outer/outer regimes listed below.
Write `x=phi-pi/2`. A `+f` row is proved on `-.3<=x<=.1`; a `-e` row is
proved on `-.03<=x<=.06`. Every cost is strictly greater than
`17953/20000=.89765`. The tails of the same six regimes are included in
`SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF.md`.

The argument is a continuous contact and derivative proof. The companion
`verify_short_outer_quarter_aligned_hand.js` checks its 80 fixed rational
comparisons. It does not minimize a function, select a contact by sampling,
or divide a state domain into boxes.

All decimal constants are exact rationals. Put

\[
 Q=9789/2500,\quad p_0=\pi/2,\quad
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad b_0=1-d.
\]

An outer state has `0<=b<=d`, primary coordinate `a=a(b)`, and

\[
 r_b=\frac{b+1/2}{a+1/2},\quad
 a'=-r_b,\qquad r_b'=\frac{Q}{(a+1/2)^3},\qquad a\ge b.
\tag{1}
\]

We use the following fixed bounds, obtained by squaring positive rationals:

\[
 1.399<d+.5<1.4,\quad a_0+.5<1.915,\quad
 .1<b_0<.101,\quad a(b_0)+.5>1.885.
\tag{2}
\]

Reflection followed by reversal changes the original signs to
`(-target,-source)`, interchanges axes1/3 and2/4, and negates each reversed
label's constant and primary coefficient. It preserves `phi` and corrected
cost. Thus the six original cases reduce to the following three pairs.
The checker independently reconstructs every coefficient from
`short_hand_labels.json`.

| Original case for +f | Original case for -e | c | p | q | P | t |
|---|---|---:|---:|---:|---:|---:|
| edge2 -- axis3 | edge2 -- axis4 | -.53489 | .33147 | 1.1336 | -.09133 | .88074 |
| edge4 -- axis3 | edge4 -- axis4 | -.53062 | .20967 | .83048 | -.19335 | .76744 |
| edge6 ++ axis1 | edge6 ++ axis2 | -.20704 | .21826 | .83472 | 0 | .94766 |

The table gives the `+f` coefficients. Its normalized cost and separator are

\[
 C=p_0+x+c+pa+qb-PA-tB,
 \qquad b+A\cos x+B\sin x\ge W,
 \quad W=\frac{1+\cos x+|\sin x|}{2}.
\tag{3}
\]

The paired `-e` coefficients are `(p,q,P,t)=(-P_old,t_old,-p_old,q_old)`;
its cost and separator are

\[
 C=p_0+x+c+pa-qb-PA+tB,
 \qquad a+A\sin x+B\cos x\ge W.
\tag{4}
\]

## 1. The aligned contact

At `x=0`, both separators describe the same contact after interchanging
source and target. In the `-e` coordinates it is `a+B=1`. For fixed `B`,
the source cost increases with `a`, while the target cost increases with
`B`. Consequently its minimum is on that contact, with `0<=B<=b0`.
Writing `b=a(1-B)`, its cost is

\[
 H(B)=p_0+c+p(1-B)-q\,a(1-B)-P\,a(B)+tB.
\tag{5}
\]

For rows2 and3, `p+q>t`, `P<=0`, and `(1.5-B)/(b+.5)>=1`, so `H'<0`.
Their minima are at `B=b0`; direct radical brackets give respectively
`H(b0)>.8981` and `H(b0)>.8981`.

For row1,

\[
 H''=\frac{qQ}{(b+.5)^3}+\frac{PQ}{(A+.5)^3}
 \ge \frac{.88074Q}{1.4^3}-\frac{.33147Q}{1.885^3}>1.
\tag{6}
\]

At the one rational reference point `B=.0517`, the fixed calculation gives

\[
 H(.0517)-\tfrac12 H'(.0517)^2>.8981.
\tag{7}
\]

The ordinary second-derivative inequality proves `H(B)>.8981` everywhere.
It also gives `H'(1/80)<0`. Together with the preceding monotonicity,
all three aligned functions decrease on `[0,1/80]`. The separate fixed
comparisons needed below are

\[
 H_j(1/80)-.0012>.89765\qquad(j=1,2,3).
\tag{8}
\]

## 2. The source +f neighborhoods

For every row in (3), `q-p>0`; hence the source cost strictly increases
with `b`. For fixed `B,x`, replace `b` by its least feasible value, namely
the nonnegative part of the contact value. On a part with `b=0` and strict
separation, increasing `B` lowers the cost until contact. This is possible
because the contact value at `B=0` is negative and at `B=d` is positive.
The displayed endpoint comparisons below establish both facts throughout
the stated strips. Thus every minimum is on contact.

### 2.1. Negative half

Put `x=-u`, `0<=u<=.3`, `S=sin u`, `K=cos u`, `U=A+.5`, `V=B+.5`.
The contact and its derivatives are

\[
 b=.5+(.5-A)K+(.5+B)S,\quad
 b_B=(VK+US)/U,\quad b_u=VK+(U-1)S.
\tag{9}
\]

The contact value increases with `B` and `u`. The fixed comparison
`b(.35,.3)<0` shows that every feasible contact has `B>.35`; hence
`V>.85`. The comparison `0<b(d,0)<b(d,.3)<d` shows that the contact's
admissible interval has only the endpoints `b=0` and `B=d`.

At an interior stationary point in `B`, differentiating the cost gives

\[
 q-pr_b=\frac{tU-PV}{VK+US},\qquad
 C_u=-1+(tU-PV)\left(1-\frac{S}{VK+US}\right).
\tag{10}
\]

Exactly the second expression holds along the moving boundary `b=0`, by
implicit differentiation. The function `tU-PV` is a positive linear
functional on the quarter circle. Its minimum is at an endpoint; direct
comparison of the two endpoints gives

\[
 tU-PV\ge(t-P)(d+.5)\ge .94766(1.399).
\]

The ratio `S/(.85 K+1.399S)` increases with `u`. Therefore (10) is positive
by the single rational comparison

\[
 .94766(1.399)\left(1-
 \frac{\sin .3}{.85\cos .3+1.399\sin .3}\right)>1.
\tag{11}
\]

On the other boundary `B=d`,

\[
 C_u=-1+(q-pr_{b(u)})[(d-.5)\sin u+(d+.5)\cos u].
\tag{12}
\]

The first factor decreases with `u`, and the bracket is positive and
concave. On each of the two fixed intervals `[0,.15]` and `[.15,.3]`,
multiply the first factor at the right endpoint by the bracket at either
endpoint. All twelve products exceed1. Hence (12) is positive.

For completeness, apply this reasoning to a global minimum on the compact
contact domain. At an interior `B` its `B` derivative vanishes, so (10)
allows decreasing `u` to lower the cost unless `u=0`. On either boundary,
(10) or (12) gives the same conclusion using its boundary parameterization.
This also rules out a minimum at the upper endpoint `u=.3`. Thus the entire
negative strip reduces to (5). There is no assumption that a numerical
stationary-point list is exhaustive.

### 2.2. Positive half

For `0<=x<=.1`, put `D=V cos x-U sin x`. It is positive because
`.5 cos .1-1.915 sin .1>0`. Contact gives

\[
 b_x=-D+\cos x-\sin x.
\]

At a `B` stationary point, and also along `b=0`,

\[
 C_x=1-(tU-PV)\left(1-
 \frac{\cos x-\sin x}{D}\right)>0.
\tag{13}
\]

Indeed `tU-PV<1.82`, `D<1.4`, `cos x-sin x>.895`, and
`1-1.82(1-.895/1.4)>0`. If the parenthesis in (13) is negative the
conclusion is immediate. At `B=d`, the source contact is
`b=.5+(.5-d)(cos x+sin x)`; here `C_x>1-1.2(.4)>0`.
The endpoint comparisons `b(0,.1)<0<b(d,.1)` and `b(d,0)<d` give the same
complete contact-boundary description. The compact-minimum argument above
therefore reduces this half to alignment as well.

## 3. The source -e neighborhoods

In (4), the source cost increases with `a`, with derivative

\[
 L_a=p+q\frac{a+.5}{b+.5}>0.
\tag{14}
\]

The target cost increases with `B` because `t+P r_B>0`. A minimum is
therefore on contact: reduce `a` until contact or `a=d`; on a remaining
strict part of `a=d`, reduce `B` until contact. For the short strips below,
`a=d,B=0` is infeasible, so this second operation always reaches contact.

### 3.1. Negative half

Put `x=-y`, `0<=y<=.03`. Contact gives

\[
 a=W+A\sin y-B\cos y,\qquad
 a_y=(A+.5)\cos y+(B-.5)\sin y.
\]

Since `a>=b`, `L_a>=p+q>=.94766`. Thus

\[
 C_y=-1+L_a a_y
 >-1+.94766[1.399\cos .03-.5\sin .03]>0.
\tag{15}
\]

Decreasing `y` at fixed `B` lowers the cost until alignment or `a=d`.
On `a=d`, separation bounds

\[
 B\le \frac{W(.03)+a_0\sin .03-d}{\cos .03}<.16.
\]

Consequently `V<.66`, `U>1.86`, and implicit differentiation gives

\[
 C_y=-1+(tU+PV)\left(1-
 \frac{\sin y}{U\cos y+V\sin y}\right)>0.
\tag{16}
\]

The last inequality follows from the fixed comparison

\[
 [ .83048(1.86)-.33147(.66)]
 \left(1-\frac{\sin .03}{1.86\cos .03}\right)>1.
\]

Following that boundary completes the reduction to alignment.

### 3.2. Positive half

For `0<=x<=.06`, every contact has `0<=B<=b0`, `d<=a<=1`. Put
`u=a+.5`, `v=b+.5`, and

\[
 h=-a_x=(A-.5)\cos x+(.5-B)\sin x.
\]

Then

\[
 C_x=1-L_a h,\qquad
 (L_a h)'=-qQh^2/v^3+L_a(u-1)<0.
\tag{17}
\]

The uniform bounds are `v>1.29`, `v<1.4`, `h>.88`, `q>.767`,
`Q>3.9`, `u<=1.5`, and
`L_a<.19335+.94766(1.5)/1.29<1.3`.
Their substitution gives
`-.767(3.9)(.88)^2/1.4^3+1.3(.5)<0`, proving (17).

At `x=0`,

\[
 C_x(0,B)=1-
 \left(p+q\frac{1.5-B}{\sqrt{Q-(1.5-B)^2}}\right)
 (A(B)-.5)
\tag{18}
\]

increases with `B`, since both positive factors being subtracted decrease.
For each row the fixed comparisons give

\[
 C_x(0,0)>-.02,\qquad C_x(0,1/80)>0.
\tag{19}
\]

If `B>=1/80`, (17)--(19) show that the cost increases from alignment.
If `B<=1/80`, the possible loss is less than `.02(.06)=.0012`.
The aligned function decreases on this small `B` interval, so (8) proves
the required strict bound. The whole segment from0 to the actual `x`
remains in the contact domain because `a_x<0`; if a formal continuation
would pass `a=d`, the actual `a=d` cost instead has derivative1, which
only improves the estimate.

This completes all six stated near-aligned regimes.

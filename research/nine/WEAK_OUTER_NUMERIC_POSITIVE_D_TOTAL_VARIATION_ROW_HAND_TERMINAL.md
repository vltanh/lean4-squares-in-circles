# A positive-D replacement row with total vertical variation at most one half

November 3, 2026. Complete scalar hand proof, discovered after testing
the actual owned-axis support gate. The original positive-D signed cap
is used. Every B and X chirality and every physical separator owner
is retained. No Lean, Lake, or CI.

Independent review: the root integrator, the hand-proof reviewer and
the global-extraction reviewer each accepted the complete physical,
scalar and equality argument and replayed its exact arithmetic.
The joint signed-row review is
`GLOBAL_OUTER_LINK_EXTRACTION_ASYMMETRIC_ROW_INDEPENDENT_REVIEW.md`.

## 1. Statement and original support input

Let B,X,D be distinct physical original unit squares, in horizontal
order `x_B<x_X<x_D`. Write

`v_1=y_X-y_B`, `v_2=y_D-y_X`,

and assume only

`|v_1|+|v_2|<=1/2`.

D has nonnegative signed canonical angle. Its folded components are
`alpha_D>=beta_D>=0`, and the accepted normalized signed cap toll is

`sigma_D=alpha_D-1+(23/32)beta_D`.

Then

\[
\boxed{x_D-x_B+h_B-h_D+\sigma_D\ge2.}                 \tag{1}
\]

Equality forces B,X,D all to be aligned and each new horizontal gap
to equal one. No common orientation, small angle, actual projection
separation or individual prescribed owner is assumed.

Use the complete physical owned-support estimate proved in Section 1
of `WEAK_OUTER_NUMERIC_NEAR_HORIZONTAL_REPLACEMENT_ROW_HAND_TERMINAL.md`:
for a physical pair with `d>0`, vertical gap v and `d>=|v|`, an actual
owned axis gives

\[
d\ge1+|h_i-h_j|+\sqrt{1+s^2}-1-|v|s,                 \tag{2}
\]

where s is the absolute tangent of that original owner's angle.
The steep-axis case is included by the quarter-turn invariance of
square support and the comparison
`beta*d+alpha*|v|<=alpha*d+beta*|v|`.

Here the original inscribed disks give
`d>=sqrt(1-v^2)>=sqrt(3)/2>|v|`, because `|v|<=1/2`.
Thus (2) applies to both links, including every owner and axis.

## 2. Reduce the three original frames to two scalar slopes

Put

\[
r(s)=\sqrt{1+s^2},\quad h(s)=\frac{1+s}{2r(s)},
\quad q(s)=r(s)-1-s/2,\quad0\le s\le1.
\]

Let `s_1,s_2` be the two chosen original-owner slopes, and let
`s=max(s_1,s_2)`. If `t=beta_D/alpha_D`, the signed toll is

\[
\sigma(t)=\frac{1+(23/32)t-r(t)}{r(t)}.
\]

The same original width variation as in the earlier row theorem is

\[
V=|h_B-h_X|+|h_X-h_D|+h_B-h_D.
\]

It satisfies `V>=2(max(h_B,h_X,h_D)-h_D)`, and therefore
`V>=2(h(s)-h(t))_+`. Also

\[
|v_1|s_1+|v_2|s_2\le s/2,
\qquad
[r(s_1)-1]+[r(s_2)-1]\ge r(s)-1.
\]

Adding the two actual physical estimates (2) shows that the surplus
on the left of (1) is at least

\[
                     q(s)+2(h(s)-h(t))_++\sigma(t).  \tag{3}
\]

This reduction keeps both original selected owners; the maximum s
is used only to make a valid scalar lower bound.

## 3. Complete scalar payment and equality

The function q decreases until `s_0=1/sqrt(3)` and increases thereafter,
with `q(s_0)=sqrt(3)/2-1`. Moreover

\[
(q+2h)'(s)=\frac{1+s^3}{(1+s^2)^{3/2}}-\frac12
            \ge\frac1{\sqrt2}-\frac12>0.             \tag{4}
\]

The lower bound is the familiar minimum of `cos^3(phi)+sin^3(phi)`
on the first quadrant. Since h is increasing, splitting at `s=t`
shows that the minimum of the first two terms of (3) is

`q(min(t,s_0))`.

For `0<=t<=s_0`, set `r=r(t)`. Direct algebra gives

\[
q(t)+\sigma(t)
=\frac{(r-1)^2}{r}
 +t\left(\frac{23}{32r}-\frac12\right)\ge0.          \tag{5}
\]

It is strictly positive for t>0: `r<=sqrt(2)` and
`23>16sqrt(2)`, whose squared reserve is `529-512=17`.
For t=0, (4) makes (3) strictly positive for every s>0.

For `s_0<=t<=1`, the signed toll has derivative

`sigma'(t)=(23/32-t)/(1+t^2)^(3/2)`.

It is unimodal, so its minimum on this interval is at an endpoint.
At `s_0`, (5) is already strict. At t=1, the required sum is

\[
\sigma(1)+q(s_0)
=\frac{55}{32\sqrt2}+\frac{\sqrt3}{2}-2
>\frac{77}{64}+\frac67-2=\frac{27}{448}>0.            \tag{6}
\]

The two strict rational bounds use `sqrt(2)<10/7` and
`sqrt(3)>12/7`, with squared reserves `2/49` and `3/49`.
This proves (3) over its complete continuous square, with equality
only `s=t=0`.

Consequently equality in (1) makes D and both selected owners aligned.
The remaining original width variation V must be zero. As `h_D=1/2`,
this forces B and X to align too. Their vertical gaps are less than
one, so original physical separation gives horizontal gaps at least
one, and equality in their sum makes both exactly one.

## 4. Closed-Q exclusion in the original strict caller

Retain the original-nine `001/00` predicate, with `v_CD>=2/3` and
nonnegative D tilt. The complete G-order theorem supplies `G_y>D_y`,
and its inherited horizontal bounds give
`-1459/1728<x_G-x_D<11/60`, in particular `|x_G-x_D|<1`.
Every unit normal with nonpositive vertical component has projection
on `c_G-c_D` strictly below one, while the physical support sum is
at least one. Thus an actual D/G owned separator points upward, as
required by the independently accepted signed cap. Suppose an
unchanged extra X obeys the horizontal order and total-variation
hypothesis above.

Original actual AB, (1), and original actual EFG give a weighted
adjusted span at least `211/2`. The ordinary A/E cap and signed D/G
cap give at most the same quantity. Equality is necessary throughout,
so B,X,D align and the accepted ordinary cap equality theorem yields

`D=(3/2,-1/16)`, `G=(1,15/16)`, `x_B=-1/2`, `x_X=1/2`.

The row bound gives `y_X<=y_D+1/2<y_G`. Since aligned X and G have
horizontal gap one half, their physical separation forces
`y_X<=y_D`. It also gives `y_X>=y_D-1/2>y_C`.

Original actual BC implies `x_C>=h_C>=1/2`; the original C/D cone
and its transverse bound imply `x_C<=5/6`. With `p=x_C-1/2`, the
unchanged C,X centers satisfy

\[
0\le p\le1/3,
\qquad
1\le|c_C-c_X|^2\le p^2+(1-p)^2.
\]

Thus p=0, whence `h_C=1/2`. The original C/D gap is now exactly
`1=h_C+h_D`, contradicting its retained strict weak bit.

The closed horizontal-order faces are already impossible by unit
center distance, since the corresponding vertical gap is at most
one half. Hence this is a complete closed-region analytic terminal
for positive D. It does not by itself prove the negative-D extension
or the whole fixed mask.

The exact scalar companion is
`computer_assisted/weak_outer_numeric_positive_total_variation_arithmetic.py`.
Its arithmetic supports (4)--(6); the continuous physical and equality
arguments are the hand proof above.

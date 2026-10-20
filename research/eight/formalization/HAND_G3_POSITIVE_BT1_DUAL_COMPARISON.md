# Removing a positive BT1 error in the global path dual

## 1. Scope and conclusion

Use the actual G0--G2 cycle, with

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 c_0=\sqrt{Q/2}-1/2,\quad \kappa=49/50.
\tag{1}
\]

The global sign results under a forbidden original BT owner give
`y_A=b_A>0`, `y_T=b_T>0`, and `y_D=-b_D<0`; B can have either sign.
Original AB and TD owners are 0 or 2. Let the original BT owner be 1
and let its error be `x>=0`. All individual errors have absolute value
less than `7/10`.

Give TD any multiplier `0<c<=kappa` and give AB any fixed positive
multiplier. Give BT the multiplier `kappa cos x`. Relax each unsigned
T state to the full sorted shifted disk, and each signed B state to
the full signed sorted shifted disk. These relaxations include every
actual core and outer state. Keep the other centers, errors, and
terms unchanged.

**Dual comparison.** The resulting lower-bound expression is at
least its value with `x=0` and BT multiplier `kappa`. The comparison
is independent of the original AB owner, AB error, AB multiplier,
B sign, and radial kinds.

This is a comparison of lower bounds. It does not claim that moving
the BT frame preserves the actual separating inequalities. In
particular one may first use this comparison and then use the
aligned-BT coefficient `kappa` in the AB comparisons of
`HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md`.

## 2. Support-function comparison

Write `S=sin x`, `C=cos x`, and

\[
 W(x)=(1+C+S)/2.
\]

The original BT1 projection is

\[
 P_{BT1}=a_T+a_B S+y_B C.
\tag{2}
\]

The dual expression contains `x+kappa C(W-P_BT1)` and the unchanged
AB and TD terms. In the convention that a center force is subtracted
from the charge, the B force at positive x differs from its force at
zero by

\[
 \delta_B=\kappa S(C,-S)
\tag{3}
\]

in `(a_B,y_B)` coordinates. For any actual or relaxed signed B,

\[
 \delta_B\cdot(a_B,y_B)
 \le \kappa S\{R-(C+S)/2\}.
\tag{4}
\]

Indeed replacing `y_B` by `-|y_B|` only increases this expression.
Apply Cauchy--Schwarz to `(a_B+1/2,|y_B|+1/2)`, whose norm is at
most R, and to the unit vector `(C,S)`. Support-function
subadditivity therefore bounds the possible B-support increase by
the right side of (4), irrespective of the unchanged AB force.

The T force loses exactly `kappa(1-C)` in its primary component when
passing from zero to positive x. Its secondary component is positive:
it equals c for TD0 and `c cos w` for TD2. Its primary component at
positive x is positive as well: it equals `kappa C` for TD0 and
`kappa C+c sin w` for TD2. In the latter case,

\[
 \kappa C+c\sin w
 \ge\kappa\{\cos(7/10)-\sin(7/10)\}>0.
\tag{5}
\]

A positive linear functional in these two components reaches its
maximum over the sorted shifted disk on the outer circular arc.
Every point of that arc has `a>=c0`, including its two endpoints.
Take a maximizer for the positive-x T force and evaluate it at the
zero-x T force. The T-support decrease is consequently at least

\[
                         \kappa c_0(1-C).
\tag{6}
\]

Adding the change in the BT right-hand-side term, the angle charge,
(4), and (6), the positive-x dual minus the zero-x dual is at least

\[
\begin{aligned}
 G(x)&=x+\kappa C W(x)-\kappa
       -\kappa S\{R-(C+S)/2\}+\kappa c_0(1-C)\\
 &=x+\kappa\{(c_0-1/2)(1-C)-(R-C)S\}.
\end{aligned}
\tag{7}
\]

It remains to prove `G(x)>=0` on the whole intrinsic interval.

## 3. Exact whole-interval scalar proof

The rational bounds

\[
 R<1979/1000,\qquad c_0>899/1000
\tag{8}
\]

follow by squaring: the reserves are respectively `841/1000000`
and `599/1000000`. On `[0,7/10]`, use

\[
 \sin x\le x-x^3/6+x^5/120,\quad
 \cos x\ge1-x^2/2,\quad
 1-\cos x\ge x^2/2-x^4/24.
\tag{9}
\]

All factors being multiplied in the negative sine term of (7) are
nonnegative. Thus `G(x)>=x P(x)`, where the following polynomial has
exact rational coefficients:

\[
\begin{aligned}
P(x)={}&1-\kappa\frac{979}{1000}
 +\kappa\frac{399}{2000}x
 -\kappa\left(\frac12-\frac{979}{6000}\right)x^2
 -\kappa\frac{399}{24000}x^3\\
 &+\kappa\left(\frac1{12}-\frac{979}{120000}\right)x^4
 -\frac{\kappa}{240}x^6.
\end{aligned}
\tag{10}
\]

Drop the negative cubic and sextic contributions from `P''` and
bound `x^2<=(7/10)^2`. This gives the uniform exact upper bound

\[
                 P''(x)\le-\frac{34050737}{150000000}<0.
\tag{11}
\]

The two endpoint values are

\[
 P(0)=\frac{2029}{50000}>0,\qquad
 P(7/10)=\frac{273094329}{10000000000}>0.
\tag{12}
\]

Concavity now proves `P>0` throughout `[0,7/10]`, hence
`G(x)>=0`, strictly for `x>0`. The positivity in (5) can also be
checked without a decimal trigonometric premise: the degree-6 lower
cosine polynomial minus the degree-5 upper sine polynomial at 7/10
equals `86836931/720000000>0`.

The proof uses one fixed support comparison and one concave
polynomial on the whole intrinsic interval. No sampled angle bound
or numerical premise is used.

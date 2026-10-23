# Marker bounds and a negative-AB dual comparison for the BT path

## 1. Scope

This note supplies two whole-chart bounds for the unchanged G1 marker
and one pointwise comparison for an original AB witness. Its intended
application is the still-open A-positive AB--BT--TD--DE owner branch.
It does not assert that this branch has been excluded.

Use the G0 boundary cycle at

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad c_0=\sqrt{Q/2}-1/2.
\]

An unsigned state satisfies `a>=b>=0`, `a>447/800`, `b<9/10`.
An outer state satisfies `(a+1/2)^2+(b+1/2)^2=Q`.
Retain exactly the C/L/M/H marker in
[the global DE theorem](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md),
Section 2. At a chart junction both possible retained marker values
obey the bounds below. Every terminating decimal is an exact rational.

## 2. A stronger lower marker bound

On every radial kind and every chart,

\[
                         \boxed{F(a,b)\ge\frac{43}{50}b.}
\tag{1}
\]

For C, `a<=7/12` and
`F_C=7.506931(7/12-a)+1.077372b`, so this is immediate.

For L, the circle identity gives, when `b>0`,

\[
 \frac{a_0-a}{b}=\frac{b+1}{a_0+a+1}<\frac25.
\]

Indeed `b<=a/4`, `a_0>7/5`, and `a>447/800` imply
`1+a/4<(2/5)(a_0+a+1)`. Consequently

\[
 F_L\ge(1.089065-\tfrac25 .403875)b=.927515b.
\]

The case `b=0` has `F_L=0`.

On M, the function

\[
 F_M-.86b=-2.143075+1.489593a(b)+.720219b
\]

is concave because `a(b)=sqrt(Q-(b+1/2)^2)-1/2` is concave.
Its minimum is therefore at an intrinsic endpoint. The primary
coordinates of the endpoints at `b/a=1/4` and `b/a=3/7` satisfy

\[
 a_{1/4}>\frac{649}{500},\qquad
 a_{3/7}>\frac{1199}{1000}.
\]

Substitution into the increasing corner-square expression gives the
positive reserves `11983/4000000` and `26771/24500000`, respectively.
The resulting endpoint lower bounds for `F_M-.86b` are

\[
 \frac{48255559}{2000000000},\qquad
 \frac{11407099}{875000000}.
\]

For H, put `p=.569472` and `k=.86-.390886=.469114`. Circle support gives

\[
 \begin{aligned}
 F_H-.86b
 &=\frac\pi4+(p-.390886)c_0-pa-kb\\
 &\ge\frac\pi4+(p-.390886)c_0+\frac{p+k}{2}
        -R\sqrt{p^2+k^2}.
 \end{aligned}
\]

Use `pi>3.14159`, `c_0>.899`, and `R<1.979`. For the first bound,
Machin's identity `pi=16 arctan(1/5)-4 arctan(1/239)`, the alternating
lower polynomial `t-t^3/3+t^5/5-t^7/7` at `t=1/5`, and
`arctan(1/239)<1/239` give a rational lower bound greater than
`3.14159`. The exact comparison

\[
 (7379/10000)^2-p^2-k^2
       =\frac{6505311}{50000000000}>0
\]

then gives

\[
 F_H-.86b>\frac{2467607}{500000000}>\frac{49}{10000}.
\]

This proves (1) on the whole outer circle and the whole core boundary.

## 3. A sharper upper plane on every outer chart

For every outer state,

\[
 \boxed{F_O(a,b)\le\frac38(a-a_0)+\frac{1091}{1000}b.}
\tag{2}
\]

For L, both coefficients of the difference have the required sign:
`.375<.403875`, `a-a_0<=0`, and `1.091>1.089065`.

For M, let D be the right side of (2) minus `F_M`. Its derivative
along the outer circle is

\[
 D'(b)=1.114593\frac{b+1/2}{a+1/2}-.489219.
\]

Since `b/a>=1/4` and `a<283/200`,

\[
 \frac{b+1/2}{a+1/2}\ge\frac{683}{1532},\qquad
 D'(b)>\frac{11783511}{1532000000}>0.
\]

At the left endpoint, `a_{1/4}<1299/1000`; its exact corner-square
reserve above Q is `16217/16000000`. Hence `b_{1/4}<1299/4000`.
Using also `a_0<283/200` yields

\[
 D(b_{1/4})>\frac{22879291}{4000000000}>0.
\]

For H, the difference is

\[
 D(b)=.944472a(b)+.700114b
       -.375a_0-\frac\pi4-.178586c_0.
\]

It is concave, so its minimum is at one of the intrinsic endpoints.
At `b/a=3/7`, use `a>1199/1000`, `b>(3/7)(1199/1000)`,
`a_0<283/200`, `c_0<9/10`, and `pi<355/113`. This gives

\[
 D(b_{3/7})>\frac{6102516601}{395500000000}>0.
\]

At the diagonal endpoint the expression simplifies before bounding:

\[
 D(c_0)=1.466c_0-.375a_0-\frac\pi4
       >\frac{215917}{113000000}>0,
\]

using `c_0>.899`. Thus (2) holds on every whole outer chart.

## 4. Pointwise comparison for an original negative AB error

Suppose A has its already proved positive signed tangent `y_A=b_A>0`.
The B signed tangent `y_B` may have either sign. Write an original
negative AB error as `v=-z`, where `0<=z<7/10`, and set

\[
 c=\cos z,\quad s=\sin z,\quad
 W(z)=\frac{1+\cos z+\sin z}{2}.
\]

The original AB projections are

\[
 P_0=b_A-a_Bs-y_Bc,\qquad
 P_2=-a_As+b_Ac-y_B.
\tag{3}
\]

Consider a weighted necessary-inequality argument in which the retained
BT inequality contributes `-kappa*y_B` to the Lagrangian. Thus `kappa`
is its actual multiplier for the signed source tangent: it equals the
BT weight for owner 0, and that weight times `cos(d_BT)` for owner 1.
Keep all other terms, all actual centers, and every other multiplier
fixed. Give (3) the positive multiplier

\[
                         \alpha=\frac\kappa{\cos z}.
\tag{4}
\]

Compare the unboosted AB angular term plus these weighted margins with
the expression using AB error zero and AB multiplier `kappa`.
This is an algebraic comparison of two dual expressions. It does not
assert existence of a new packing or feasibility of an aligned edge.

For original axis 0, their exact difference is

\[
 -z+\kappa\{(a_B+1/2)\tan z
                    -(b_A-1/2)(\sec z-1)\}.
\tag{5a}
\]

For original axis 2, the difference is

\[
 -z+\kappa\{(a_A+1/2)\tan z
                    +(y_B+1/2)(\sec z-1)\}.
\tag{5b}
\]

The global entry bounds make both expressions at least

\[
 -z+\kappa J(z),\qquad
 J(z)=\frac{847}{800}\tan z-\frac25(\sec z-1).
\tag{6}
\]

There is a direct whole-interval derivative proof:

\[
 J'(z)-1
 =\frac{(\sin z-1/5)^2+3/160}{\cos^2z}
 \ge\frac3{160}.
\]

Since `J(0)=0`,

\[
 \boxed{-z+\kappa J(z)\ge
          \left(\frac{163\kappa}{160}-1\right)z.}
\tag{7}
\]

In particular, `kappa>=1` gives gain at least `3z/160`. This statement
includes either B sign, both original zero owners, every radial kind,
and every weak witness. No marker bound is needed in this comparison:
the actual A and B states, and their marker values, remain fixed.

## 5. The return-path boost in the comparison

Let `d=x+w+y` be the sum of the three unchanged BT, TD, DE errors.
The four-edge boost is `(9/50)h(|d-z|)`, where
`h(t)=(sin t+cos t-1)/2` on `[0,7/10]`. The aligned expression has
boost `(9/50)h(|d|)`. Both distances lie in this interval because
they are actual endpoint-frame differences in the common real lift.

If `d<=0`, the boost increases under the comparison from `d` to
`d-z`. Thus the gain in (7) applies unchanged to the boosted expression.

For an arbitrary sign of d, `|h'(t)|<=1/2` gives boost loss at most
`9z/100`. Therefore the boosted gain is at least

\[
 \left(\frac{163\kappa}{160}-\frac{109}{100}\right)z.
\tag{8}
\]

For example `kappa>=107/100` gives a gain of at least `z/16000`
without a sign assumption on d.

## 6. What remains to apply the comparison

The marker bounds are unconditional on the G0 boundary cycle.
The AB comparison is conditional on the stated coefficient and, for
the smaller coefficient `kappa>=1`, the remaining-tail sign when the
boost is included. A complete four-edge proof must still select
compatible positive multipliers for BT, TD and DE and prove the
resulting scalar lower bound throughout their actual angle domain.
Equations (1)--(8) do not supply that missing assertion.

No Lean source, generator, table, or build was changed or invoked.

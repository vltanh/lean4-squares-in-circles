# The aligned-prefix scalar for a core E and negative DE3

All decimals in this note are exact rationals. Put

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad \kappa=49/50,
 \quad m=1.077372,\quad A=13/12,
 \quad T_*=16761/4520.
\tag{1}
\]

This note proves the following whole-interval scalar inequality:

\[
\begin{split}
 L_0(t):={}&\pi-t+\frac52\kappa+\frac65
 +e(t)\{1+\tfrac12\cos t+A\sin t\}\\
 &-R\left\{\sqrt{\kappa^2+9/25}
                   +\sqrt{e(t)^2+9/25}\right\}>T_*,
 \qquad 0\le t\le7/10,
\end{split}
\tag{2}
\]

where

\[
 e(t)=
 \begin{cases}
 13/20+2t,&0\le t\le1/5,\\
 m\sec t,&1/5<t\le7/10.
 \end{cases}
\tag{3}
\]

Both formulas are valid at the joining point. The two definitions
need not agree there: each independently supplies a valid positive
dual multiplier. This is a two-piece analytic choice by the actual
DE angle, not a subdivision into sampled configurations.

The scalar is the aligned AB--BT--TD lower bound with TD multiplier
`c=3/5`, DE3 multiplier e, core E, and actual DE error `-t`. It is
also suitable for comparison arguments that reduce another path
dual to the same expression. This note claims the scalar (2); it
does not by itself remove nonzero BT or TD errors.

## 1. Why the core endpoint term is valid

For a core E the unchanged marker is

\[
 F_E=7.506931(7/12-a_E)+m b_E,
 \qquad a_E\le7/12,\quad b_E\ge0.
\]

If `e cos t<=m` and `e sin t<=7.506931`, then

\[
\begin{split}
 F_E+e a_E\sin t-e b_E\cos t
 ={}&e\frac7{12}\sin t
 +(7.506931-e\sin t)(7/12-a_E)\\
 &+(m-e\cos t)b_E
 \ge{}&e\frac7{12}\sin t.
\end{split}
\tag{4}
\]

The choices (3) satisfy these conditions: on the first interval
`e<=1.05<m`; on the second `e cos t=m`, and throughout `e<1.41`.
Thus the endpoint support used in (2) includes all core E states.

## 2. Polynomial ingredients

Set

\[
\begin{split}
 S(t)&=t-t^3/6+t^5/120-t^7/5040,\\
 C(t)&=1-t^2/2+t^4/24-t^6/720,\\
 U(t)&=1-t^2/2+t^4/24.
\end{split}
\tag{5}
\]

On `[0,7/10]`, `S<=sin`, `C<=cos<=U`, with all three
polynomials positive except `S(0)=0`. We use the exact rational
bounds

\[
 \pi>3.14159,\qquad R<1.979,
 \qquad R\sqrt{\kappa^2+9/25}<2.2738.
\tag{6}
\]

The first is the Machin-series bound already recorded in
`HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md`; the second
has squared reserve `841/1000000`. For the third,

\[
 2.2738^2-Q(\kappa^2+9/25)=41/5000000>0.
\]

For every positive P and nonnegative X,

\[
                    \sqrt X\le\frac{X+P^2}{2P}.
\tag{7}
\]

Thus the explicit positive polynomials P below may be used as norm
envelopes without any approximation-error premise.

## 3. The first interval

For `0<=t<=1/5`, put

\[
 e=13/20+2t,\qquad P=0.884+1.498t+0.651t^2,
\]

and define the explicit degree-10 polynomial

\[
\begin{split}
 H_<(t)={}&2P\left[
 3.14159-t+\frac52\kappa+\frac65-2.2738-T_*
 +e\{1+\tfrac12 C(t)+A S(t)\}\right]\\
 &-1.979\{e^2+9/25+P^2\}.
\end{split}
\tag{8}
\]

Equations (5)--(7) give

\[
                     L_0(t)-T_*\ge H_<(t)/(2P).
\tag{9}
\]

Here is an exact whole-interval verification of positivity. If
`H_<'''(1/10+z)=sum_j d_j z^j`, expansion of (8) gives

\[
 d_0-\sum_{j\ge1}|d_j|(1/10)^j
 =\frac{35379380187503}{1800000000000}>19.
\tag{10}
\]

So `H_<'` is convex. Its endpoint values are both negative:

\[
 H_<'(0)=-\frac{10978071253}{42375000000}<0,
 \qquad
 H_<'(1/5)=-\frac{356954238440953}{26696250000000000}<0.
\tag{11}
\]

Convexity bounds the derivative above by the chord between these
two endpoints. Hence `H_<` decreases on the whole interval. Direct
substitution in the displayed polynomial yields

\[
                         H_<(1/5)>0.01655>0.
\tag{12}
\]

This proves (2) on the first interval.

## 4. The second interval

For `1/5<=t<=7/10`, set `e=m sec t` and

\[
                      P=1.2332-0.146t^2+0.032t^4>0.
\tag{13}
\]

Multiplying `L_0-T_*` by the positive number `cos t` before
applying (7) removes the secant from the norm. Define

\[
\begin{split}
 H_>(t)={}&2P\left[
 \{3.14159-t+\tfrac52\kappa+\tfrac65-2.2738-T_*+m/2\}C(t)
            +m\{1+A S(t)\}\right]\\
 &-1.979\{m^2+(9/25)U(t)^2+P^2\}.
\end{split}
\tag{14}
\]

The coefficient multiplying `C(t)` is positive throughout the
interval. Also
`m^2+(9/25)cos(t)^2<=m^2+(9/25)U(t)^2`. Thus

\[
                  L_0(t)-T_*\ge H_>(t)/(2P\cos t).
\tag{15}
\]

Write the explicit degree-11 polynomial (14) as
`H_>(9/20+z)=sum_j A_j z^j`. A single coefficient-sum estimate on
the entire interval, `|z|<=1/4`, gives

\[
\begin{split}
 H_>(t)&\ge A_0-\sum_{j\ge1}|A_j|(1/4)^j\\
 &=\frac{201779193615893880738613}
          {101248000000000000000000000}>0.00199>0.
\end{split}
\tag{16}
\]

All quantities in (10)--(16) are fixed rational expressions in the
displayed polynomials. The two whole-interval derivative and
coefficient estimates finish the proof of (2).

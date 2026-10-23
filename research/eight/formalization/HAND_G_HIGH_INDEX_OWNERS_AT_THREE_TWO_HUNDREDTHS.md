# G axes 2 and 3 are impossible at S <= 3/200

## 1. Conditional theorem and inputs

Assume exactly the geometric hypotheses of
`HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md`. That theorem proves
that every feasible E witness is 0 or 1, and supplies

\[
 q\le Q=9789/2500,\quad S\le3/200,\quad k=251/250,
\]
\[
 L=447/800<a_i<U=283/200,\quad b_i<9/10,
 \quad a_A<A_*=1303/1000,\quad b_A>79/250,
\]
\[
 7/12\le a_G,a_T<349/250,\qquad a_H<29/25.
\]

**Theorem.** Every originally feasible G witness belongs to `{0,1}`.
No final mixed owner, tilt window, or `S <= 1/1000` input is assumed.
The proof covers all original aligned owners and all ties.

Write `c=cos(t)`, `s=sin(t)`, `W=(1+c+|s|)/2`. The actual nominal
projections, their shared losses, and the four original G/E formulas
are equations (3)--(5) of the cited note. Its positive-arc bounds give
`s<3/20` for G2 and `s<3/25` for G3.

For negative sine `s=-r`, an E0 witness gives

\[
 r<9/50,\qquad c>49/50,                               \tag{1}
\]

because `E0 <= (29/25)(c-r/2)` and feasibility imply
`(27/25)r <= 4/25+2S <= 19/100`.
For E1, `E1 <= 29/25-Lr` and the circle chord give

\[
 (1/2+L)r-(2/7)r^2\le4/25+2S\le19/100.
\]

The left side increases on `[0,7/10]`, and its value at `r=1/5` is
larger than `19/100`. Hence

\[
 r<1/5,\qquad c>97/100.                              \tag{2}
\]

These are consequences of the actual witnesses at the present threshold.

## 2. One stress handles six of the eight sign alternatives

Put `h=9/20`, `b=4/3`, `e=3/5`. Give HG,G,AB,BT,TD,DE,E the weights

\[
 (h,1,a,b,b,d,e),\qquad
 a=1\text{ for G2},\ a=c\text{ for G3},
 \qquad d=e\text{ for E0},\ d=ec\text{ for E1}.       \tag{3}
\]

All weights are positive. The equal BT/TD weights cancel the T
transverse coordinate. The a choice cancels the unwanted A transverse
term, and the d choice cancels the E transverse term at zero errors.
Complete the G,B,D,H circles with masses

\[
 (7/25,5/12,7/20,3/16).                              \tag{4}
\]

Before completing D, add the nonnegative cone slack
`((b-d)/2)(a_D-b_D)`. Its two nominal force coordinates become
`(b+d)/2`. The four force vectors before this cone correction are

\[
 G:(c,h-s)\text{ or }(1,h),\qquad B:(b,a),\qquad D:(d,b),
\]
\[
 H:(ec,h+es)\text{ for E0},\qquad H:(e,h)\text{ for E1}.
\]

The G3 leftover is `-s a_A`; the E1 leftover is `es a_E`.
For s>=0 bound these using `a_A >= L`, `a_E <= U`; for s<=0 use
`a_A <= A_*`, `a_E >= L`. The square-completion support is

\[
 T_q(X,Y;m)=mq+(X^2+Y^2)/(4m)-(X+Y)/2.
\]

At zero sine the gap is

\[
 B(q)=2063/50400+(1481/1200)(47/12-q),
 \qquad B(Q)=1330843/31500000>21/500.                 \tag{5}
\]

Expanding just the four displayed squared norms, and substituting
`c^2+s^2=1`, gives the following identities for demand minus the
coordinate upper bound:

\[
\begin{aligned}
 \Psi_{20}&=B+(8/5)(c-1)+(4/5)|s|-(163/1400)s,\\
 \Psi_{21}&=B+(57/35)(c-1)+(9/70)s^2+(4/5)|s|
                              +(17/56-(3/5)A_E)s,\\
 \Psi_{30}&=B+(13/5)(c-1)+(3/5)s^2+(4/5)|s|
                              +(A_A-21/50)s,\\
 \Psi_{31}&=B+(92/35)(c-1)+(51/70)s^2+(4/5)|s|
                              +(A_A-(3/5)A_E)s.
\end{aligned}                                       \tag{6}
\]

Here `A_A,A_E` are the endpoint bounds just specified. These are the
four original witness alternatives, not an angular subdivision.

For G2/E0, the coefficients of positive and negative |s| exceed
`2/3` and `9/10`, respectively; the cosine loss is at most
`(32/35)s^2`. For G2/E1 those coefficients exceed `1/4` and `4/5`,
while its combined negative quadratic coefficient is `393/490`.
The positive G2 bound `s<3/20` and (1)--(2) show `Psi >= B` in all
four of these regimes.

For positive G3/E0 the sine coefficient exceeds `9/10` and its
negative quadratic coefficient is `31/35`. For positive G3/E1 they
are respectively greater than `1/2` and equal to `379/490`.
Since positive G3 forces `s<3/25`, these two gaps also satisfy `Psi>=B`.

The complete nominal loss of (3) is at most

\[
 (kb+2e)S\le119/3125<21/500.                         \tag{7}
\]

Thus (5)--(7) exclude all six regimes on their whole arcs. Only the
two negative G3 alternatives require the sharper error treatment below.

## 3. Two fixed stresses for the negative G3 alternatives

Keep the structure (3), now with `a=c` and the following fixed constants.
For G3/E0 use

\[
 h=14/25,\quad b=53/40,\quad e=31/40,\quad d=e,
\]
\[
 (m_G,m_B,m_D,m_H)=(29/100,21/50,3/8,23/100).
\tag{8}
\]

For G3/E1 use

\[
 h=11/20,\quad b=53/40,\quad e=177/200,\quad d=ec,
\]
\[
 (m_G,m_B,m_D,m_H)=(29/100,21/50,79/200,53/200).
\tag{9}
\]

Again add the fixed nonnegative D cone slack `(b-d)(a_D-b_D)/2`.
For arbitrary actual aligned errors, collect the four anchor forces
before applying their circle supports. Leave the actual A,T,E
coordinates free. Let Phi be the resulting demand-minus-upper-support
scalar. Feasibility implies `Phi <= 0`.

For this purpose the E width may be replaced by its smooth lower
branch `(1+cos(z)-sin(z))/2`, where

\[
 x_1=\theta_B,\ x_2=\theta_T-\theta_B,\
 x_3=\theta_D-\theta_T,\ x_4=\theta_E-\theta_D,
 \quad h_0=\theta_H-t,
 \quad z=t+h_0-x_1-x_2-x_3-x_4.
\]

This branch is no larger than the actual width even when z crosses
zero. It agrees at the zero-error negative reference. Thus a positive
lower bound for this scalar remains a valid contradiction at all ties.

### 3.1 A nominal gap greater than 3/100 on each whole arc

The zero-error lower bound has the form

\[
 \Psi=B+C(c-1)+Kr^2+Jr,\qquad s=-r.
\tag{10}
\]

For both stresses,

\[
 B=3+2h+3b+3e-Q(m_G+m_B+m_D+m_H)
 -\frac{1+h^2}{4m_G}-\frac{b^2+1}{4m_B}
 -\frac{(b+e)^2}{8m_D}-\frac{e^2+h^2}{4m_H}.
\tag{11}
\]

For (8),

\[
 C=2+e,\quad K=1/(4m_B),\quad J=1/2+eh/(2m_H)-A_*.
\]

Direct rational substitution gives

\[
 B=969183679/28014000000>.0345,\qquad J>.14,
 \quad C/(1+.98)-K<.81.
\]

Consequently (1), (10) give `Psi > .0345+.14r-.81r^2`.
This concave quadratic is greater than `.03` at both endpoints of
`[0,.18]`, hence throughout that interval.

For (9),

\[
 C=2(1+e)-be/(4m_D),\quad
 K=1/(4m_B)+e^2/(8m_D),\quad J=(1+e)/2+eL-A_*.
\]

The rational substitutions give

\[
 B=166558676173/5099766000000>.0326,\qquad J>.133,
 \quad C/(1+.97)-K<.70.
\]

Equation (2) now gives `Psi > .0326+.133r-.70r^2`, again greater
than `.03` at both endpoints of `[0,.2]`. This proves

\[
                         \Phi(0)>3/100.              \tag{12}
\]

The actual free coordinates need not equal the endpoint bounds used
in (11): `ra_A-er a_E` is bounded above by `rA_*-erL` in the E1 case,
and `ra_A` by `rA_*` in the E0 case. These are one-sided comparisons,
not substitutions of an assumed reference packing.

### 3.2 One first-order bound for every actual aligned owner

At zero errors, the derivative of an anchor support in its force is
its virtual center `(X/(2m)-1/2,Y/(2m)-1/2)`. Let D denote e times
the derivative of the E nominal margin in its angle. Exact cancellation
gives

\[
 D=e\{ch/(2m_H)-r\}\quad\text{for (8)},
\]
\[
 D=e\{c(a_E+1/2)-r(b_E+1/2)\}\quad\text{for (9)}.
\tag{13}
\]

In the second formula E retains its actual free coordinates. Equations
(1)--(2), (8)--(9) and the coordinate bounds imply

\[
                         .65<D<1.70.                 \tag{14}
\]

The smooth first coefficients on `x_1,x_2,x_3,x_4` are `D-lambda R`;
on `h_0` the sign is reversed. Their actual receiver alternatives are

\[
 R_{HG}\in\{a_G^*,a_H^*\},\quad
 R_{AB}\in\{a_B^*,a_A\},\quad
 R_{BT}\in\{b_B^*,a_T\},
\]
\[
 R_{TD}\in\{a_D^*,a_T\},\qquad
 R_{DE}\in\{b_D^*,a_E\}.
\tag{15}
\]

Stars indicate the displayed virtual centers, not actual-position
assumptions. For HG, `1.1<R<1.25` and `.55<=lambda<=.56`.
For the other four edges,

\[
 .55<R<1.415,\qquad .75<\lambda\le53/40.
\]

These bounds follow immediately by division of the nominal forces in
(8)--(9) by their positive masses; the free coordinates use (1).
Together with (14), they imply

\[
 |D-\lambda R|-\lambda/2<1.
\tag{16}
\]

For example, for the four non-HG edges the two possible excesses are
bounded by `1.70-.75(1.05)<1` and `(53/40)(.915)-.65<1`.
For HG use `1.70-.55(1.6)<1` and `.56(.75)-.65<1`.
The aligned linear cusps therefore make the complete first-order term
at least `-S`, simultaneously for all actual owners.

### 3.3 A uniform Hessian bound, with no owner enumeration

Remove the five aligned sine cusps. For an anchor force F, suppose
`|F|<=M`, `|partial_j F|,|partial_j partial_k F|<=D_0` on the full
error segment. Its support (including its linear corner shift) has
Hessian entries of absolute value at most

\[
 (D_0^2+M D_0)/(2m)+(3/4)D_0.                         \tag{17}
\]

The last term uses `sqrt(2)/2<3/4`. For G,B,D,H respectively, valid
whole-segment triples `(M,D_0,m lower bound)` are

\[
 (1.56,.56,.29),\quad(2.325,1.325,.42),
 \quad(2.65,1.325,.375),\quad(1.45,1.45,.23).
\]

At G only HG depends on the errors. At B the two incident rotations
use different error coordinates. The same holds at D; its fixed cone
correction increases M but has zero derivatives. At H both incident
terms may contribute to one derivative, giving their sum bound 1.45.
Thus these bounds retain every actual owner without changing witnesses.

The free A,T,E terms contribute at most `1.5+1.9875+2.655=6.1425`
to a Hessian entry: T's two rotations have disjoint error coordinates,
while E's two contributions are bounded together. The smooth widths
contribute at most `1.32625`. Adding these bounds and (17) gives exactly

\[
                   195716401/5602800<35<40.
\]

Taylor's theorem in the five shared errors consequently loses at most
`20S^2`. Restoring the aligned cusps loses at most `S^3/8`, because
their largest weight is `53/40<3/2`.

By (12), (16), and this whole-segment bound,

\[
 \Phi>3/100-S-20S^2-S^3/8
       \ge671973/64000000>1/100>0.                   \tag{18}
\]

This contradicts feasibility for both entire negative arcs, including
t=0 and all axis ties.

## 4. Conclusion

Section 2 excludes the six sign regimes to which its coarse shared
loss applies. Section 3 excludes the two remaining negative G3 regimes
by retaining the first-order cusps before estimating the errors.
Hence a G2 or G3 witness cannot be paired with either feasible E0 or
E1 witness. The preceding E theorem already excludes E2/E3. Therefore
**every** feasible G witness is 0 or 1.

This closes the high-index part of mixed-owner capture at `S<=3/200`.
The bad low-index pairs, tilt capture, and the earlier global cuts and
contractions remain separate obligations. No Lean or historical table
source was changed, no compilation or CI was run, and no optimizer
output is a premise of this proof.

# Global BT0 exclusion with DE2, or with an outer E

## 1. Statement and exact scope

Use the actual G0--G2 boundary cycle at

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad c_0=\sqrt{Q/2}-1/2,
 \quad \kappa=49/50.
\tag{1}
\]

All decimals below are exact rationals. Retain the unchanged C/L/M/H
marker F from the global G1 theorem. The global owner and sign results
give original AB and TD owners 0 or 2, original DE owners 2 or 3,
`y_A=b_A>0`, `y_T=b_T>0`, `y_D=-b_D<0`, and the reflection
normalization `y_E=-b_E<=0`. B has either sign. Write the four actual
errors as

\[
 (v,x,w,y)=(d_{AB},d_{BT},d_{TD},d_{DE}).
\]

**Theorem.** If original BT owner 0 is a witness, and either original
DE owner 2 is a witness or E is outer, then

\[
 \boxed{\pi+v+x+w+y+\kappa b_A+F_E>
                    \frac{16761}{4520}.}
\tag{2}
\]

The global return theorem in
`HAND_G3_GLOBAL_RETURN_WITH_LINEAR_A_CHARGE.md` gives the complementary
charge greater than `103/40`. Their sum is exactly `2 pi`, whereas
`16761/4520+103/40=710/113>2 pi`. Thus all the stated candidates are
excluded globally. No frame ordering, mismatch bound or tangent cut is
assumed. A, B, T and D retain both radial kinds. The only BT0 case not
covered here is a core E with an original DE3 witness at negative DE
error. This note does not claim to close that separate case or BT1.

The proof uses three continuous affine weight families on a whole
interval, indexed only by the intrinsic E chart. The six final scalar
inequalities are proved by whole-interval polynomial bounds; neither a
mesh nor a numerical feasibility test is a premise.

## 2. Total negative error is below 7/10

Put `h(t)=(sin t+cos t-1)/2`. The complete G1 cycle theorem gives

\[
 \sum_i h(|d_i|)<\Delta:=\frac{10394}{25425},\qquad
 |d_i|<7/10,\qquad \sum_i d_i=0.
\tag{3}
\]

Concavity and `h(0)=0` give
`h(t)>=(10/7)h(7/10)t` on `[0,7/10]`. Moreover

\[
 2h(7/10)-\Delta>
                  \frac{201866893}{813600000000}>0.
\tag{4}
\]

For (4), substitute the alternating lower polynomials of degrees 7
and 6 for sine and cosine at 7/10. Therefore

\[
 \boxed{\sum_i\max(0,-d_i)=\tfrac12\sum_i|d_i|<7/10.}
\tag{5}
\]

In particular the sum of any selected negative errors is below 7/10,
even after positive errors are set to zero in a dual expression.

## 3. Two comparison lemmas for AB and positive errors

Throughout, `W(t)=(1+cos t+|sin t|)/2`. Giving an actual inequality
`P>=W` a positive multiplier lambda adds `lambda(W-P)<=0` to the
charge. Every comparison below is between these lower-bound
expressions at the same actual centers. It does not assert that an
altered frame configuration is feasible.

### 3.1. Positive zero-type errors

For `0<=t<=7/10`, define

\[
 f_\lambda(t)=t+\lambda\sin t-2\lambda R\sin(t/2).
\tag{6}
\]

For `0<lambda<=kappa`,

\[
                         f_\lambda(t)\ge0.
\tag{7}
\]

Indeed `f_kappa(0)=0`, and

\[
 f_\kappa''(t)=\kappa\sin(t/2)
                    \{R/2-2\cos(t/2)\}<0\quad(t>0).
\]

The endpoint has the exact lower bound

\[
 f_\kappa(7/10)>
                 \frac{37065577129}{28800000000000}>0.
\tag{8}
\]

Use `R<1.979`, the degree-7 lower sine polynomial at 7/10,
and the degree-5 upper sine polynomial at 7/20 to obtain (8).
Concavity proves (7) at lambda=kappa. Decreasing lambda increases
the expression because `sin t-2R sin(t/2)<0` for positive t.

The signed corner disk gives, for every actual state,

\[
 a\sin t+b(1-\cos t)
 \le 2R\sin(t/2)-\tfrac12\{\sin t+1-\cos t\}.
\tag{9}
\]

Consequently a positive original AB error, with multiplier kappa,
can be replaced by zero in its dual expression with nonnegative
gain. For AB0 the projection increment is
`a_B sin t+y_B(1-cos t)`; for AB2 it is
`a_A sin t-b_A(1-cos t)`. Each is bounded by (9).
The same comparison applies to a positive TD error with multiplier
at most kappa, and to a positive DE3 error with multiplier at most
kappa.

### 3.2. Negative AB with multiplier kappa sec z

For an original AB error `v=-z<=0`, give AB multiplier
`kappa/cos z`. The exact comparison formulas (5a)--(6) in
`HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md` give gain at
least

\[
 -z+\kappa J(z),\qquad
 J(z)=\frac{847}{800}\tan z-\frac25(\sec z-1).
\tag{10}
\]

A slightly sharper bound than the one needed there is

\[
                   J(z)\ge\frac{41}{40}z,
 \qquad -z+\kappa J(z)\ge\frac9{2000}z.
\tag{11}
\]

Here is a whole-interval verification. Monotonicity of `tan t/t`
and the degree-5 upper sine and degree-2 lower cosine polynomials at
7/20 give

\[
 \tan(z/2)\le\frac{261}{500}z.
\]

The endpoint cross-product reserve is `9317/76800000`. Since
`sec z-1=tan z tan(z/2)` and `tan z>=z+z^3/3`,

\[
 J(z)-\frac{41}{40}z\ge z P(z),\quad
 P(z)=\frac{27}{800}-\frac{261}{1250}z
              +\frac{847}{2400}z^2-\frac{87}{1250}z^3.
\tag{12}
\]

On `[0,2/5]`, replace the last term by `-(87/3125)z^2`.
Completing the square in the resulting quadratic gives the positive
reserve `86373/390092000`. On `[2/5,7/10]`, P is increasing:
`P'(2/5)=15047/375000>0`, and `P''>0` throughout that interval.
This proves (11), for both AB owners and both B signs.

### 3.3. Positive BT0 and DE2 errors

For either of these two rotations the projection increment has form
`a(cos t-1)+b sin t`. Since `a>1/2` and `b<9/10`, its dual gain
with multiplier lambda is at least

\[
 t+\lambda\{(a-1/2)(1-\cos t)+(1/2-b)\sin t\}
 \ge(1-2\lambda/5)t.
\tag{13}
\]

It is nonnegative for every multiplier used below.

## 4. An outer E converts negative DE3 to DE2

Suppose `y=-z<=0`, and put `t=tan(z/2)`, so `0<=t<.366`.
The two original DE projections obey

\[
 P_3-P_2=\sin z\{t a_D+b_D-a_E-t b_E\}.
\tag{14}
\]

Sorted circle containment gives
`t a_D+b_D<=c_0(1+t)`: write its left side as
`((1+t)/2)(a_D+b_D)+((t-1)/2)(a_D-b_D)`.
On the outer circle, `a_E+t b_E>=c_0(1+t)`. Indeed the left side
is concave as a function of b_E, so its minimum is at `b_E=0` or
`b_E=c_0`. The first value a_0 exceeds the second because
`a_0>1.414`, `c_0<.9`, and `t<.366`.
Thus `P_3<=P_2`. An actual DE3 witness then also supplies DE2.

For positive DE3 error, use Section 3.1 to set its error to zero in
the dual expression. Its zero-error projection is the same as DE2.
Therefore an outer E is covered by the DE2 calculation below for
either original DE owner.

## 5. Three whole-chart endpoint inequalities

The following exact pairs `(e,m)` satisfy

\[
                              F_E-e b_E\ge m:
\tag{15}
\]

- C or L: `e=.9449`, `m=0`.
- M: `e=.797`, `m=.0458`.
- H: `e=.64`, `m=.134`.

For C, `F_C>=1.077372 b_E` proves the first bound. For L, the
circle identity and the intrinsic endpoint enclosures give

\[
 \frac{a_0-a}{b}=\frac{b+1}{a_0+a+1}
 <\frac{5299}{14850},
\]

using `a_0>1.4145`, `a>1.298`, and `b<.32475`.
The reserve for the first primary enclosure is `1159/4000000`;
the other endpoint enclosures are already established in the marker
helper. Thus

\[
 1.089065-.403875\frac{5299}{14850}-.9449
                         =\frac{637}{13200000}>0.
\tag{16}
\]

On M, `F_M-.797b=-2.143075+1.489593a+.783219b` is concave in b.
At its endpoints use `a_{1/4}>1.29874` and
`a_{3/7}>1.19925`. Their corner-square reserves below Q are
`1162527/40000000000` and `10139/392000000`, respectively.
The two endpoint reserves above `.0458` are

\[
                 \frac{3694767}{200000000000},\qquad
                 \frac{230997}{3500000000}.
\tag{17}
\]

For H, `F_H-.64b` is increasing. Its derivative is
` .569472(b+1/2)/(a+1/2)+.390886-.64>0`, using the H-chart
ratio bound `(b+1/2)/(a+1/2)> .59`. At the left endpoint use
`a<6/5`, `b=(3/7)a`, `c_0>.899`, and `pi>3.14159`.
The resulting reserve above `.134` is `1624499/3500000000`.
This proves (15), including either retained marker at a junction.

## 6. Removing positive errors and concentrating negative errors

Set

\[
 q=\max(0,-x)+\max(0,-w)+\max(0,-y),\qquad 0\le q<7/10.
\tag{18}
\]

Use the following affine TD multiplier c(q), together with the e and
m in Section 5:

- C or L: `c(q)=.567+.445q`.
- M: `c(q)=.52+.365q`.
- H: `c(q)=.46+.25q`.

Every family satisfies `0<c(q)<min(kappa,e)` on the whole interval.
Give BT0 multiplier kappa and DE multiplier e. Give AB multiplier
kappa when v is nonnegative, and `kappa/cos v` otherwise.

Sections 3 and 4 show that replacing the positive x,w,y by zero,
and then replacing AB by its zero-error dual expression, can only
decrease this lower bound. At zero AB error, its projection is
`b_A-y_B`. The terms in A and B cancel exactly against the endpoint
charge and the retained BT0 projection. Both signs of y_B are included.

Write the remaining errors as `(-r,-s,-t)` with nonnegative r,s,t
and `r+s+t=q`. Full shifted-circle support, valid for every radial
kind and every real force `(u,v)`, is

\[
 ua+vb\le R\sqrt{u^2+v^2}-\frac{u+v}{2}.
\tag{19}
\]

Put

\[
 N_{a,c}(z)=\sqrt{a^2+c^2-2ac\sin z}.
\tag{20}
\]

For original TD0, (19) on the retained T and D circles gives

\[
 \begin{aligned}
 L_0={}&\pi-q+\tfrac32\kappa+c+\tfrac12e+m
              +\kappa\cos r+c\cos s+e\cos t\\
       &-R\{N_{\kappa,c}(r)+N_{e,c}(s+t)\}.
 \end{aligned}
\tag{21}
\]

For TD2, replace the two norm arguments in (21) by `r+s` and t.
These formulas retain both actual shared circles before applying
their supports; no independent-edge marker sum is substituted.

For fixed `s+t`, concavity of cosine and `e>=c` show that the
TD0 expression is no smaller than the expression with `s=0`.
For fixed `r+s`, the same conclusion follows for TD2 using
`kappa>=c`. Thus both expressions are bounded below by the
`s=0`, `r+t=q` expression.

The function

\[
                  z\longmapsto a\cos z-RN_{a,c}(z)
\tag{22}
\]

is strictly concave on `[0,7/10]` for all positive a,c. Here is a
uniform derivative proof. With
`u=(a-c sin z)/N`, `v=c cos z/N`, one has `u^2+v^2=1` and

\[
 -N''/a=uv^2-u^2v\tan z\le\frac{2}{3\sqrt3}.
\]

If u is negative the left side is negative; otherwise use
`uv^2<=2/(3 sqrt 3)`. Consequently the second derivative of (22)
is less than `a(.763-.764)<0`. The required exact enclosures are

\[
 (.763)^2-4Q/27=\frac{18721}{9000000}>0,\qquad
 \cos(7/10)-.764>\frac{605351}{720000000}>0.
\tag{23}
\]

Apply concavity to the sum of (22) at r and q-r. Its minimum is at
an endpoint. We have therefore reduced every original angle and TD
owner in scope to the following two whole-interval scalar bounds:

\[
 \begin{aligned}
 B(q)={}&\pi-q+\tfrac32\kappa+2c+\tfrac12e+m
       +\kappa\cos q+e
       -R\{N_{\kappa,c}(q)+N_{e,c}(0)\},\\
 D(q)={}&\pi-q+\tfrac32\kappa+2c+\tfrac12e+m
       +\kappa+e\cos q
       -R\{N_{\kappa,c}(0)+N_{e,c}(q)\}.
 \end{aligned}
\tag{24}
\]

## 7. Exact scalar proof on the entire interval

This section supplies all constants for an algebraic verification of
`B(q),D(q)>16761/4520` on `[0,7/10]`.
Set

\[
 S=q-q^3/6+q^5/120-q^7/5040,\qquad
 C=1-q^2/2+q^4/24-q^6/720,
\]

and use `sin q>=S`, `cos q>=C`, `R<1.979`, and
`pi>3.14159`. For the B expression define

\[
 X_1=\kappa^2+c^2-2\kappa cS,\quad X_2=e^2+c^2,
 \quad Z=\kappa C+e;
\]

for D define

\[
 X_1=\kappa^2+c^2,\quad X_2=e^2+c^2-2ecS,
 \quad Z=\kappa+eC.
\]

The following positive quadratic polynomials P_1,P_2 are chosen
separately for the two expressions. No approximation property is
assumed of them: the exact identity

\[
             \sqrt X\le\frac{X+P^2}{2P}\qquad(P>0)
\tag{25}
\]

is the only fact used. Every displayed P is greater than 1/2 on the
whole interval, directly from its coefficient signs and endpoints.

For C/L, use

\[
 \begin{array}{ll}
 B:&P_1=1.132205-.274033q-.308441q^2,\\
   &P_2=1.101964+.232011q+.052697q^2;\\
 D:&P_1=1.132205+.225750q+.052828q^2,\\
   &P_2=1.101964-.264348q-.296959q^2.
 \end{array}
\tag{26}
\]

For M, use

\[
 \begin{array}{ll}
 B:&P_1=1.109414-.291174q-.290425q^2,\\
   &P_2=.951635+.201690q+.039207q^2;\\
 D:&P_1=1.109414+.172770q+.039524q^2,\\
   &P_2=.951635-.242875q-.241022q^2.
 \end{array}
\tag{27}
\]

For H, use

\[
 \begin{array}{ll}
 B:&P_1=1.082589-.312978q-.232552q^2,\\
   &P_2=.788162+.146966q+.021489q^2;\\
 D:&P_1=1.082589+.106793q+.021222q^2,\\
   &P_2=.788162-.232523q-.178814q^2.
 \end{array}
\tag{28}
\]

For each of these six explicit choices define the degree-10 polynomial

\[
 \begin{aligned}
 H(q)={}&2P_1P_2
  \left(3.14159-q+\tfrac32\kappa+2c+\tfrac12e+m+Z
                              -\frac{16761}{4520}\right)\\
 &-1.979\{P_2(X_1+P_1^2)+P_1(X_2+P_2^2)\}.
 \end{aligned}
\tag{29}
\]

Equations (25)--(29) give
`B(q)-16761/4520>=H(q)/(2P_1P_2)` or the corresponding D inequality.
It remains only to verify H positive. The following rational
coefficient bounds do so on the whole interval at once.

Write `H(7/20+z)=sum_{j=0}^{10} A_j z^j` and put `h=7/20`.
For the two C/L polynomials, exact expansion of (29) gives:

- B: `A_0>.01549`, `|A_1|<.01229`, and
  `A_2-sum_{j=3}^{10}|A_j|h^(j-2)>.1036`.
- D: `A_0>.00820`, `|A_1|<.03272`, and
  `A_2-sum_{j=3}^{10}|A_j|h^(j-2)>.0983`.

Since `|z|<=h`, completing the square proves positivity:

\[
 \begin{aligned}
 H_B&>.01549-\frac{(.01229)^2}{4(.1036)}>.0151,\\
 H_D&>.00820-\frac{(.03272)^2}{4(.0983)}>.0054.
 \end{aligned}
\tag{30}
\]

For M and H, exact expansion instead gives the following derivative
bounds, again with the same single center and the whole interval:

- M, B: `A_1<-.1891` and
  `sum_{j=2}^{10}j|A_j|h^(j-1)<.1073`.
- M, D: `A_1<-.2580` and the same derivative sum is below `.1007`.
- H, B: `A_1<-.4008` and the derivative sum is below `.0883`.
- H, D: `A_1<-.4470` and the derivative sum is below `.1265`.

Thus each of these four H polynomials is decreasing. Direct rational
substitution at their right endpoint gives, respectively,

\[
 H_{M,B}(.7)>.0577,\quad H_{M,D}(.7)>.0032,\quad
 H_{H,B}(.7)>.0667,\quad H_{H,D}(.7)>.0272.
\tag{31}
\]

All coefficient and endpoint inequalities in (30)--(31) are ordinary
rational consequences of the explicitly factored polynomial (29).
They bound one whole polynomial at a time; they do not sample the
angle interval. This completes (24), hence (2), and the claimed global
owner exclusions.

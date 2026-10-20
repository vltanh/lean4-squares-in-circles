# Whole-arc exclusions under the forbidden H cone at S <= 3/200

## 1. Scope and inputs

Assume the G0--G2 candidate geometry, the weak normalization `y_E<=0`,
original core avoidance and corner containment at

\[
 Q=9789/2500,\qquad
 S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le\rho=3/200.
\]

Suppose, for contradiction, that `b_H<=a_H/2`. The zero-edge signs
and both short-quarter owner restrictions are supplied without tangent
cuts by `HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md`.
Thus the six signs are `(+,-,+,-,+,-)`, E has its weak negative sign,
the three zero witnesses are in `{0,2}`, and every BT/DE witness is
in `{2,3}`. No mixed owner or tilt window is assumed.

This note excludes all original GA witnesses 0 and 2, every
nonnegative GA tilt, and the negative pairs

\[
 (G1,E2),\ (G1,E3),\ (G3,E1),\ (G3,E2),\ (G3,E3).
\]

The other three negative pairs `(G1,E0),(G1,E1),(G3,E0)` are separate
obligations in `HAND_G3_H_LOW_PRIMARY_BRANCHES_AT_THREE_TWO_HUNDREDTHS.md`.
The present proof never substitutes a preferred original witness for
an actually feasible one. Weak ties are included throughout.

All terminating decimals in the proof denote exact rational numbers.
The continuous stresses below are explicit formulas on entire arcs;
no angular mesh or generated state inventory is a premise.

## 2. Forward bounds forced by the H-low assumption

Use the constants

\[
 L=447/800,\quad U=283/200,\quad V=349/250,
 \qquad K=37/40,\quad M=383/200.
\]

The cited quarter-owner theorem gives `a_i>L`, `|p_i|<U`, `b_i<.9`,
and `a_i<V` for the six strict-sign roles. For the five aligned
edges it gives the single nominal-loss estimate

\[
\begin{split}
 b_H+b_G&\ge1-K|d_H|,& b_A+b_B&\ge1-K|d_A|,\\
 a_B-b_T&\ge1-K|d_B|,& b_T+b_D&\ge1-K|d_T|,\\
 a_D+b_E&\ge1-K|d_D|.
\end{split}                                                     \tag{1}
\]

In particular each of the six strict transverse magnitudes exceeds
`1-.9-K rho=.086125`, hence exceeds `43/500`.

The H-low cone and its circle imply `b_H<29/50`: at `b_H=29/50`
the lower corner value `5b_H^2+3b_H+1/2` is `3.922=Q+4/625`.
Consequently HG forces

\[
 b_G>.42-K\rho=.406125>203/500,
 \qquad a_G<63/50.                                           \tag{2}
\]

The second assertion follows because the corner value at
`(a,b)=(63/50,203/500)` exceeds Q by `709/250000`.

The shared BT--TD--AB argument also gives

\[
                  b_A>79/250=.316,\qquad a_A<1303/1000.       \tag{3}
\]

Here is the dependency check. The diagonal corner gives
`b_D<8993/10000`. We may weaken K in (1) to `k=251/250`.
Adding BT and TD gives
`a_B+1/2>C+z`, where
`C=5/2-8993/10000-kS`, `z=k|d_A|`. Thus the original B circle
and AB imply

\[
 b_A>3/2-z-\sqrt{Q-(C+z)^2}.
\]

This expression increases with z because `(C+z)^2>Q/2`.
At `S=rho`, `C>=39641/25000`, and

\[
 (39641/25000)^2+(3/2-79/250)^2-Q=318881/625000000>0.
\]

This proves the first part of (3); the A corner comparison for the
second has reserve `213/200000`. No H cone was used in this shared
quarter-path calculation.

One weak core consequence needed later is

\[
                         a+b/20\ge7/12.                     \tag{4}
\]

If `b<=1/2`, core avoidance gives `a>=7/12`. If `b>1/2`, the
entry bound gives `a+b/20>L+1/40=467/800>7/12`. Equality in (4)
is allowed.

Normalize A's frame to zero and let G's frame be t. Put

\[
 c=\cos t,\quad s=\sin t,\quad W=(1+c+|s|)/2.
\]

The real frame has `|t|<.7`, `c>=3/4`, `|s|<13/20`. The actual
EH tilt is

\[
                     z=t-d_H-d_A-d_B-d_T-d_D.                \tag{5}
\]

Every actually feasible EH witness has its nominal projection at
t at least `W-MS`. A sum with HG weight at most one and EH weight
at most one therefore loses at most

\[
                         (K+M)S\le213/5000.                 \tag{6}
\]

This spends a single shared S, not an independent error per edge.

## 3. Only G1/G3 on a negative arc can remain

The four original nominal GA projections are

\[
 ca_A-sb_A-b_G,\quad a_A-sa_G-cb_G,\quad
 ca_G-sb_G-b_A,\quad a_G-sa_A-cb_A.                            \tag{7}
\]

### GA0 is impossible on the whole frame interval

Adding HG to GA0 gives the necessary demand `1+W-K|d_H|`.
By (2)--(3), its difference from the coordinate upper bound is

\[
 1+W-(b_H+ca_A-sb_A)
 >.92-.803c-.4|s|>.02>K\rho.
\]

The strict middle bound follows from
`.803^2+.4^2=.804809<.9^2` and Cauchy's inequality.

### Nonnegative sine is impossible for every other GA witness

For G1, G2, G3 respectively, (2)--(3) give

\[
\begin{split}
 W-P_{G1}&>-.803+.906c+(1/2+L)s\ge.103,\\
 W-P_{G2}&>.816-.76c+.906s\ge.056,\\
 W-P_{G3}&>-.76+.816c+(1/2+L)s\ge.056.
\end{split}
\]

Use `c+s>=1` and `1/2+L>.906>.816`. Thus put `s=-r<0`
from now on.

### GA2 is impossible on the entire negative arc

The G corner gives `a_G+b_G/2<293/200`: indeed its unrestricted
circle support is `sqrt(5Q/4)-3/4<293/200`.
If `r<=c/2`, (2) implies

\[
 ca_G+rb_G<1.262c+.406r,
 \qquad W-P_{G2}>.816-.762c+.094r\ge.054.
\]

If `r>=c/2`, we also have `r<c`, since `r<.65` and `c>.75`.
Then `(2r-c)(2c-r)>=0` gives `cr>=2/5`, so `c+r>67/50`.
The directional G circle and `sqrt Q<99/50` give instead

\[
 W-P_{G2}>.816+c+r-99/50>.176.
\]

### A feasible negative G3 has |t|>S

If `0<=r<=1/20`, its gap in (7) is

\[
 W-P_{G3}>-.76+.816c-.803r
 >-.76+.816(.998)-.803/20>0.
\]

Here `c>.998` follows by squaring. Consequently a feasible G3 has
`r>1/20`, and hence `-t>1/20>S`.

## 4. EH-forced arcs and three elementary mixed exclusions

The four original nominal EH projections at `s=-r` are

\[
 ca_H-rb_H-b_E,\quad a_H-ra_E-cb_E,\quad
 ca_E-rb_E-b_H,\quad a_E-ra_H-cb_H.                            \tag{8}
\]

An E1 witness forces `r<9/20`. By (4), its projection is at most
`V-(7/12)r`, because `c-r/20>0`. The difference from W is at least
`.5-V+c/2+(13/12)r`, which increases on the full frame interval.
At `r=9/20`, use `c>.89`; the difference exceeds `.0365>M rho`.
Thus on this arc

\[
                  r<9/20,\quad c>.89,
                  1-c\le(100/189)r^2.                        \tag{9}
\]

An E2 witness forces `r<1/2`. Since `b_H>.086`, its gap is at
least `.586-.915c+r/2`. For `r>=1/2` use `c<.87`; the gap is
greater than `.03995>M rho`. Hence

\[
                  r<1/2,\quad c>.86,
                  1-c\le(100/186)r^2.                       \tag{10}
\]

An E3 witness forces `r<2/5`. Its gap is at least
`-.915+.586c+(1/2+L)r`. This increases on `0<=r<=.65`;
at `r=2/5`, `c>.91` gives a gap greater than `.04176>M rho`.
Consequently

\[
                  r<2/5,\quad c>.91,
                  1-c\le(100/191)r^2.                       \tag{11}
\]

### G1/E2

Use weights `c,1,c` on HG, G1, E2. The demand is `c+(1+c)W`,
and the coordinate sum is
`a_A+r a_G+c^2 a_E-cr b_E`.
Equations (2)--(3) give a demand-minus-bound gap at least

\[
 -.803+2c-.915c^2+\{(1+c)/2-1.26\}r.
\]

The c polynomial increases on `[.86,1]`. By (10), this gap is
greater than its lower bound
`-.803+2(.86)-.915(.86)^2-.33/2=.075266`, which exceeds (6).

### G1/E3

Use weights `c,1,1`. The coordinate sum is
`a_A+a_E+r(a_G-a_H)`. Its gap is at least

\[
 .282-2(1-c)+.29875r
 \ge .282-(200/191)r^2+.29875r>23/100
\]

on (11), by the endpoints of this concave quadratic. Again this
exceeds (6).

### G3/E3

Use weights `c,1,1` and complete the G circle with mass `3/8`.
The coordinate sum before completion is
`a_G+cb_G+ra_A-cb_A+a_E-ra_H`.
At `r=0,c=1` the gap is

\[
 B_0=8/3-U+.316-3Q/8=5959/60000.
\]

Its c polynomial is `(2.5+.316)c-(2/3)c^2`. On (11) its
derivative is less than `13/8`, and its positive r coefficient
is `1+L-1.303=1023/4000`. Thus the gap is at least

\[
 B_0+(1023/4000)r-(325/382)r^2>3/50.
\]

Both endpoint comparisons on `[0,2/5]` are strict rational ones.
Subtracting (6) leaves more than `87/5000`.

## 5. Exact support and error calculus used in the two remaining arcs

For a positive mass m the original corner disk gives

\[
 Xa+Yb\le T(X,Y;m):=mQ+(X^2+Y^2)/(4m)-(X+Y)/2.               \tag{12}
\]

This holds for arbitrary real forces X,Y. Its derivative with
respect to its force is the virtual center
`(X/(2m)-1/2,Y/(2m)-1/2)`; that center is not assumed to be an
actual packing position.

For explicit error bookkeeping, the two retained projections on
each aligned edge, in the forward increments of (5), are

\[
\begin{array}{c|l}
 HG&b_H+a_G\sin d_H+b_G\cos d_H;\quad
       a_H\sin d_H+b_H\cos d_H+b_G\\
 AB&b_A+a_B\sin d_A+b_B\cos d_A;\quad
       a_A\sin d_A+b_A\cos d_A+b_B\\
 BT&a_B\cos d_B+b_B\sin d_B-b_T;\quad
       a_B+a_T\sin d_B-b_T\cos d_B\\
 TD&b_T+a_D\sin d_T+b_D\cos d_T;\quad
       a_T\sin d_T+b_T\cos d_T+b_D\\
 DE&a_D\cos d_D+b_D\sin d_D+b_E;\quad
       a_D+a_E\sin d_D+b_E\cos d_D.
\end{array}                                                    \tag{13}
\]

For a specified stress, collect the two incident forces at every
completed anchor before using (12). Keep all free centers actual
except for a stated one-sided coordinate comparison. Let Phi be
weighted width demand minus this upper support. Original feasibility
then implies `Phi<=0`.

At zero errors, an aligned derivative of Phi is `D-lambda R`,
where D is the common derivative of the nominal EH margin and R
is the relevant actual or virtual primary coordinate. The linear
width cusp adds `lambda |d|/2`. Thus

\[
 |D-\lambda R|-\lambda/2\le L_1
 \quad\Longrightarrow\quad
 \text{the full first-order term is at least }-L_1 S.          \tag{14}
\]

Formula (13), together with `partial z/partial d_i=-1`, proves
this simultaneously for all original aligned owners.

For second derivatives, if an anchor force on the entire error
segment obeys
`|F|<=M_0`, `|partial_j F|,|partial_j partial_k F|<=D_0`, then a
Hessian entry of its support is bounded in absolute value by

\[
                   (D_0^2+M_0D_0)/(2m)+(3/4)D_0.             \tag{15}
\]

The last term uses `sqrt(2)/2<3/4` for the corner offset. The
five aligned sine cusps are removed before this estimate and are
restored afterward using `|sin d|>=|d|-|d|^3/6`.

## 6. G3/E1: one continuous four-circle stress

Work on (9). Section 3 already shows `t<-S`. Use weights

\[
 (h,1,\alpha,\beta,\beta,\delta,e)
\]

on HG, GA, AB, BT, TD, DE, EH, where the same formulas apply on
the entire arc:

\[
\begin{split}
 h&=1/2+3r/8,&\beta&=11/8+r/2,\\
 e&=18/25+29r/20,&\kappa&=7/15,\\
 \alpha&=c+\kappa r,&\delta&=e(c-r/20).
\end{split}                                                     \tag{16}
\]

Complete the G, B, D, H circles with masses

\[
 m_G=9/32+3r/50,\quad m_B=43/100+r/5,
 \quad m_D=3/8+13r/40,\quad m_H=11/50+19r/50.                 \tag{17}
\]

Before completing D add the nonnegative cone slack
`((beta-delta)/2)(a_D-b_D)`. Here `beta>delta>0` on (9).
At zero errors its two D force coordinates are both
`(beta+delta)/2`. A and T remain free.

### 6.1 The core comparison is valid for the actual errors

The coefficient of `a_E` in the weighted projection sum is
`e sin z` for DE axis 2 and `delta sin d_D+e sin z` for DE axis 3.
Both are nonpositive throughout the straight error segment.
Indeed `t<-S` gives `z<0`; for `d_D<=0` both sine terms are
nonpositive. For `d_D>=0`, use `delta<=e` and

\[
 \sin z+\sin d_D
   =2\sin((z+d_D)/2)\cos((z-d_D)/2)\le0.
\]

The cosine is positive on the frame range and `z+d_D<0`.
Thus replacing only `a_E` by `A_E=7/12-b_E/20`, using (4),
increases the coordinate upper bound. Keep the same actual `b_E`.
This is a one-sided inequality, not an assumed feasible comparison
packing.

At zero errors the E coordinate sum is exactly
`-er(a_E+b_E/20)`, so after this comparison it is `-(7/12)er`.
The A force is `r(a_A+kappa b_A)`. Apply its fixed directional
circle support only at zero errors:

\[
 a_A+\kappa b_A\le A_*:=T(1,\kappa;7/25)
                         =5710699/3937500.                   \tag{18}
\]

No small A mass is introduced in the nonzero-error stress.

### 6.2 A nominal gap greater than 39/1000 on the whole arc

The exact zero-error lower bound is

\[
\begin{split}
 N(r,c)={}&h+\alpha+2\beta+\delta+(1+e)W-rA_*+(7/12)er\\
 &-T(1,h;m_G)-T(\beta,\alpha;m_B)\\
 &-T((\beta+\delta)/2,(\beta+\delta)/2;m_D)-T(e,h;m_H).
\end{split}                                                     \tag{19}
\]

Here `Phi(0)>=N(r,c)`. The following is a single rational
polynomial verification of its lower bound.
Let `D_*=4m_Gm_Bm_Dm_H`. After substituting `c^2=1-r^2`,
write `D_* N=A(r)+B(r)c`. The coefficients of B, in ascending
powers of r, are exactly

\[
\begin{split}
B(r)={}&.1109480625+.4180394930625r+.5796979164825r^2\\
 &+.39862020041125r^3+.13593573595625r^4\\
 &+.017916486375r^5+.00047937r^6.
\end{split}
\]

They are all positive. Define the explicit polynomial

\[
 P(r)=A(r)+B(r)(1-100r^2/189)-(39/1000)D_*.
\]

Direct rational expansion of (16)--(19) bounds its coefficients
from below as follows:

\[
\begin{split}
P(r)\ge{}&133/10^6-(89/50000)r+(47/5000)r^2
             +(1/20)r^3+(3/100)r^4\\
 &-(1/40)r^5-(23/1000)r^6-(1/200)r^7-(1/1000)r^8.           \tag{20}
\end{split}
\]

This coefficient comparison is an identity calculation with the
displayed rational weights, not a sampled assertion. The first
three terms in (20) form a positive quadratic: its constant minus
the completed-square loss is
`133/10^6-(89/50000)^2/(4*(47/5000))>47/10^6`.
For `0<=r<=9/20<1/2`, the negative terms after factoring `r^3`
have total coefficient less than
`1/160+23/8000+1/3200+1/32000<1/100`.
The remaining `r^3/20` and `3r^4/100` are nonnegative.
Hence `P(r)>0`. Equation (9) and `B(r)>0` prove

\[
                             \Phi(0)>39/1000.               \tag{21}
\]

### 6.3 First derivatives retain all five signed errors

After the legitimate E comparison the common flux in (14) is

\[
 D=e\{c(A_E+1/2)-r(b_E+1/2)\}.
\]

On the entire arc,

\[
                            2/5<D<21/20.                    \tag{22}
\]

For the lower bound, use `0<=b_E<.9` and (9). The resulting
cubic lower bound is
`e{(623/600)(1-100r^2/189)-(7/5)r}`. It is concave;
its endpoint values are `1869/2500` and `130479/320000`,
both greater than `2/5`.
For the upper bound use `c<=1-r^2/2`. The resulting cubic is
`39/50+(1453/1200)r-(223/200)r^2-(377/480)r^3`.
The inequality `r^3>=r/3-2/27` bounds this by
`27157/32400+(6833/7200)r-(223/200)r^2`.
Its completed-square maximum is `26720249/25689600<21/20`.

The receiver alternatives in (14) are

\[
\begin{array}{c|c}
 HG&a_G^*,a_H^*\\
 AB&a_A,a_B^*\\
 BT&a_T,b_B^*\\
 TD&a_T,a_D^*\\
 DE&A_E,b_D^*.
\end{array}
\]

Stars are the virtual coordinates from (17),(19). Direct division
of the displayed nominal forces gives `1/2<R<V` for every such
receiver. For example `a_G^*<=23/18<V`,
`a_H^*=e/(2m_H)-1/2`,
`a_B^*=beta/(2m_B)-1/2`, `b_B^*=alpha/(2m_B)-1/2`, and
`a_D^*=b_D^*=(beta+delta)/(4m_D)-1/2`.
The free receivers obey the same bounds by (1)--(4).
All five aligned weights satisfy `1/2<=lambda<=8/5`.
Thus (22) implies

\[
 |D-\lambda R|-\lambda/2
 <\max\{21/20-1/2,\ (8/5)(V-1/2)-2/5\}<26/25.             \tag{23}
\]

### 6.4 One Hessian bound on the complete error segment

For G,B,D,H, valid triples `(m lower bound,M_0,D_0)` in (15) are

\[
 (9/32,1.67,.67),\quad(.43,2.71,1.6),\quad
 (3/8,3.2,1.6),\quad(.22,2.05,2.05).
\]

At G only HG varies. At B and D the two incident rotations use
separate aligned increments; the D cone correction is constant.
At H the EH and HG terms may contribute to the same derivative,
so their sum is used. Their four bounds in (15) sum to less than 45.

The free A term contributes less than `1.571`, the two free T
terms less than `4.53`, and the compared E terms less than `3` to
any Hessian entry. For E use
`|(A_E,b_E)|<1.08`, `delta+e<2.745`.
The smooth widths contribute less than `4.56`. Their total with
the four support bounds is less than 60. Taylor's theorem
therefore loses at most `30S^2`.
Restoring the sine cusps loses less than `S^3/7`.
Equations (21),(23) now give

\[
\begin{split}
 \Phi&>39/1000-(26/25)S-30S^2-S^3/7\\
 &\ge932373/56000000>0.
\end{split}                                                     \tag{24}
\]

This contradicts original feasibility and excludes the entire
G3/E1 arc, with every original aligned owner and every weak tie.

## 7. G3/E2: one fixed three-circle stress

Work on (10). Section 3 gives `t<-S`, so the actual EH width
has its negative smooth branch on the entire error segment.
Use the weights

\[
 (e,1,\alpha,\beta,\beta,\delta,e),\qquad
 e=103/100,\quad\beta=3/2,\quad
 \alpha=c+(7/15)r,\quad\delta=er.                            \tag{25}
\]

Complete G,B,D with masses `29/80,15/32,7/20`. Add the same
nonnegative D cone slack `((beta-delta)/2)(a_D-b_D)`.
Keep A,T,E,H actual in the nonzero-error stress.

At zero errors H and T cancel. E's transverse term cancels
because `delta=er`; its remaining term `ec a_E` is at most
`ecU`. The A term is bounded by (18). Consequently

\[
\begin{split}
\Phi(0)\ge{}&e+\alpha+2\beta+\delta+(1+e)W-rA_*-ecU\\
 &-T(1,e;29/80)-T(\beta,\alpha;15/32)\\
 &-T((\beta+\delta)/2,(\beta+\delta)/2;7/20)\\
={}&-249328889/243600000+(5560477/7875000)r
       +(28949/756000)r^2\\
 &+(21151/20000-(112/225)r)c.                               \tag{26}
\end{split}
\]

The coefficient of c is positive on `[0,1/2]`. Inserting (10)
and collecting powers gives a cubic with constant
`8290291/243600000>17/500`, and the coefficients of
`r,r^2,r^3` respectively greater than `.208`, greater than
`-.531`, and greater than `.267`. To avoid any decimal premise,
these are simply the rational comparisons obtained from (26)
and `c>=1-(50/93)r^2`. The quadratic
`.208-.531r+.267r^2` decreases on `[0,1/2]` and has endpoint
value `.00925>0`. Hence

\[
                             \Phi(0)>17/500.                \tag{27}
\]

The common derivative is now

\[
                  D=e\{r(a_E-1/2)+c(b_E+1/2)\}.
\]

It satisfies `.44<D<7/4`. The lower bound uses `c>.86` and
`a_E>L>1/2`. For the upper bound, the E corner gives
`(a_E-1/2)^2+(b_E+1/2)^2<=Q-2a_E<Q-2L<1.675^2`;
then `e(1.675)<7/4`.
All receivers in (14) are greater than `1/2` and less than U;
all aligned weights are between 0 and `3/2`. Thus

\[
 |D-\lambda R|-\lambda/2<7/4.                               \tag{28}
\]

For the G,B,D supports, valid triples in (15) are
`(29/80,2.03,1.03)`, `(15/32,2.61,1.5)`,
`(7/20,3,1.5)`. Their bounds sum to less than 24.
The free A,H,T,E terms contribute respectively less than
`1.571,1.458,4.245,2.187`; the smooth widths contribute less
than `3.858`. Thus every smooth Hessian entry is less than 40.
The actual E coordinate was used in these derivatives; its
replacement by U in (26) was only a nominal upper bound.

The full error estimate is consequently

\[
 \Phi>17/500-(7/4)S-20S^2-S^3/8
          \ge207973/64000000>0,                             \tag{29}
\]

again a contradiction on the entire arc.

## 8. What this establishes

The H-low domain now leaves only the three negative pairs listed
in Section 1. The two stress proofs retain the unchanged centers,
all five signed frame errors, and all original allowed aligned
owners. No small-mismatch terminal, captured mixed owner, tangent
cut, numerical minimizer, or external verification assertion was
used as a premise. The mismatch bound `S<=3/200` remains an explicit
conditional input.

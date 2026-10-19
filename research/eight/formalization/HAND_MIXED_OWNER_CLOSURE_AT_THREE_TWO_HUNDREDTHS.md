# Full mixed-owner rigidity at S <= 3/200

## 1. The theorem and the exact earlier inputs

Assume the actual candidate geometry, signed role cuts, zero owners,
intended BT/DE quarter owners, core avoidance, and corner containment at
`q <= Q=9789/2500`, with `S <= 3/200`. These are precisely the hypotheses
of `HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md`.

**Theorem.** Every originally feasible G witness is 0, and every
originally feasible E witness is 1, in zero-based forward-axis numbering.
In particular the complete original owner restriction is

\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},\{0,2\},\{2,3\},\{1\}).
\tag{1}
\]

This theorem does not assume a tilt window or the old contraction to
`S <= 1/1000`. It includes all actual aligned owners, all free-slider
coordinates, and all weak separating ties.

The E2/E3 exclusions are proved at this threshold in
`HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md`; the G2/G3 exclusions
are in `HAND_G_HIGH_INDEX_OWNERS_AT_THREE_TWO_HUNDREDTHS.md`.
It remains to exclude G0/E0, G1/E0, and G1/E1. The whole positive G1/E1
alternative is already proved at this threshold in
`HAND_MIXED_PRIMARY_AT_THREE_TWO_HUNDREDTHS.md`.

The new whole-cycle cusp proof
`HAND_NEAR_ZERO_MIXED_TILT_AT_THREE_TWO_HUNDREDTHS.md` excludes `|t|<=S`
for all four low-index mixed pairs, including the intended one. Hence
only `t>S` and `t<-S` remain. The present note proves all five remaining
bad sign alternatives on these complete arcs. It does not establish the
earlier cuts or mismatch contractions; those remain prerequisites.

All terminating decimals below are exact rationals.

## 2. One four-circle support and its exact first derivatives

Use A's physical frame zero, G's frame t, and

\[
 x_1=\theta_B,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h_0=\theta_H-t,
\]
\[
 S=|x_1|+|x_2|+|x_3|+|x_4|+|h_0|,
 \qquad z=t+h_0-x_1-x_2-x_3-x_4.
\tag{2}
\]

Write `c=cos(t)`, `s=sin(t)`, `p=24/41`, `e=36/31`,
`m=12/41`, `n=12/31`. Use the edge weights

\[
 (h,1,p,1,1,e,e),\qquad h=1\text{ for G0},\quad h=c\text{ for G1},
\tag{3}
\]

and the circle masses `(m,m,n,n)` on A,B,D,H. Collect actual forces
before applying the four supports

\[
 T_q(X,Y;\mu)=\mu q+(X^2+Y^2)/(4\mu)-(X+Y)/2.
\tag{4}
\]

Keep the G,T,E coordinates actual and free, except for the explicitly
justified one-sided comparisons in Section 6. Let Phi be weighted demand
minus this upper support. Actual feasibility implies `Phi<=0`.

At zero aligned errors, the anchor forces are

\[
 A:(c,p-s)\text{ for G0},\quad A:(1,p)\text{ for G1},
 \qquad B:(1,p),\quad D:(e,1),
\]
\[
 H:(ec,h+es)\text{ for E0},\quad H:(e,h)\text{ for E1}.
\tag{5}
\]

The all-zero-tilt gap of this stress is

\[
 \Psi_0=\frac{3027}{794375}.
\tag{6}
\]

The coordinate bounds already proved at this threshold are

\[
 L=447/800<a_i<U=283/200,\quad b_i<.9,
 \qquad 7/12\le a_G,a_T<U_G=349/250,
\]
\[
 b_G,b_T<.8,\quad a_A<1.303,\quad b_A>.316,
 \qquad a_H<1.16.
\tag{7}
\]

The positive arcs are `s<.27` for G0 and `s<.26` for G1. For negative
sine `s=-r`, E0 forces `r<.18,c>.98`, and E1 forces `r<.2,c>.97`.
These implications come from the actual witnesses at `S<=3/200`, as
proved in the preceding two owner notes.

The derivative of (4) in its force is the virtual center
`(X/(2mu)-1/2,Y/(2mu)-1/2)`. Write stars for these centers from (5).
For an aligned edge, the smooth first coefficient is `D-lambda R`
(on HG its negative), where the possible receivers are

\[
 R_{HG}\in\{a_G,a_H^*\},\quad
 R_{AB}\in\{a_A^*,a_B^*\},\quad
 R_{BT}\in\{a_T,b_B^*\},
\]
\[
 R_{TD}\in\{a_T,a_D^*\},\qquad
 R_{DE}\in\{a_E,b_D^*\}.
\tag{8}
\]

Here D is e times the derivative of the nominal E margin. These formulas
follow by differentiating the literal aligned projections (8) in the
near-zero note and the E0/E1 projections. The same actual owner is
retained in the force, its support, and its derivative.

The aligned linear cusp has coefficient `lambda/2`. Thus a bound

\[
 |D-\lambda R|-\lambda/2\le\mathcal L
\tag{9}
\]

for every receiver gives a total first-order lower bound `-Lcal S`.
Define the useful constants

\[
 c_0=97/1550,\qquad E_{\max}=e(U-1/2)=1647/1550=1+c_0,
 \quad K=31/48.
\tag{10}
\]

## 3. A shared second-order estimate on the entire error segment

For E0 the actual E angle z has the sign of t because `|t|>S`.
Use that sign's smooth width branch. Remove only the five aligned sine
cusps from Phi, and hold t and the comparison weights fixed.

The varying negative force-norm terms have coefficients 1 on A and B,
3/2 on D, and `(3/2)h` on H. Their arguments are the actual incident
error sums; A may include the fixed t, and the H argument may include z.
Each error coefficient is 0 or +/-1. The positive G0 arc gives `t<.274`,
so every such argument has absolute value less than `.29`; the other
arcs are shorter. The only possible overlap besides the H term is A/B
on the x1 diagonal. Hence every force-norm Hessian entry has absolute
value less than

\[
                    (3/2)(.29)+.29+.015<.75.
\]

Combining the aligned widths and linear corner shifts in (4) with the
free coordinates gives one-angle terms. The estimates (7), exactly as
in the near-zero note, bound each aligned smooth second derivative by
`1.321`; these occupy separate diagonals.
The E0 mixed term is, apart from an error-independent constant,

\[
 e\{1/2+\cos z+\sin z+b_E\}\quad(t>0),
 \qquad e\{1/2+\cos z+b_E\}\quad(t<0).
\]

Its Hessian entries are bounded by `e(1+.29)<1.5`. G has no aligned
error. Thus every smooth Hessian entry is less than

\[
                         .75+1.321+1.5<4.
\tag{11}
\]

Taylor's theorem loses at most `2S^2`. Restoring the aligned cusps loses
at most `S^3/10`, since all their weights are below 6/5. Consequently,
if the nominal gap is at least `Psi0+g(t)` and (9) holds, then

\[
 \Phi\ge\Psi_0+g(t)-\mathcal L(t)S-2S^2-S^3/10.
\tag{12}
\]

This is one five-variable error estimate. No separate copy of S is
spent on each edge. A corresponding bound for negative G1/E1 is proved
in Section 6 after its coordinate comparisons.

## 4. G0/E0, both complete tails

### 4.1 Positive t>S

Expanding (5) in (4) gives the exact nominal excess

\[
 g(t)=(1+e)(c-1)+(e-1/2)s.
\tag{13}
\]

The common flux is

\[
                         D=e s+(21/62)c.
\tag{14}
\]

Every lower endpoint `lambda(R-1/2)` in (8) is at most Emax; every
upper endpoint `lambda(R+1/2)` is at least c. For example the A endpoint
uses `p=2m`, so its upper endpoint is exactly c. The free G/T endpoints
use (7), while the largest possible lower endpoint is `e(a_E-1/2)`.
On `0<=s<=.27`, (14) gives `D<c` and `D<Emax`. Thus (9) holds with

\[
                         \mathcal L=E_{\max}-D.
\tag{15}
\]

Both g and D increase on the whole positive arc: their derivatives are
`(e-1/2)c-(1+e)s>0` and `ec-(21/62)s>0`, respectively, using
`c>=.96,s<=.27`. Therefore `g(t)-Lcal(t)S` is minimized over `t>=S`
at t=S. The elementary sine and cosine bounds show

\[
 g(S)-\mathcal L(S)S\ge-c_0S.
\tag{16}
\]

For a complete remainder check, the left side after adding c0 S is
bounded below by

\[
 \frac{e-1}{2}S^2
 -\left(\frac{e-1/2}{6}+\frac{21}{124}\right)S^3
 -\frac e6S^4\ge0
\]

on `0<=S<=.015`. In (12) the resulting reserve, at the largest S, is

\[
 \Psi_0-c_0(3/200)-2(3/200)^2-(3/200)^3/10
                         =246217683/101680000000>0.
\tag{17}
\]

### 4.2 Negative t=-u<-S

Now `r=sin(u)<.18`, `c>.98`, and the nominal excess and flux are

\[
 g(u)=(1+e)(c-1)+(3/2)r,\qquad D=(3/2)c-er.
\tag{18}
\]

The same cusp endpoints have lower endpoints at most Emax and upper
endpoints at least c. Here `D>Emax`, so one may take
`Lcal=D-c<=1/2`. Since `1-c=r^2/(1+c)`, (18) gives `g>=1.3r`.
Also `r=sin u>=u cos u>=.98S`. Consequently `g-Lcal S>=0`.
Equation (12) is again strictly positive, even after discarding this
additional linear reserve. This excludes all negative G0/E0 witnesses.

## 5. G1/E0, both complete tails

Put `C=2+e`.
The virtual A and B primary coordinates are 29/24; D is unchanged.
With HG weight c, all lower cusp endpoints in (8) are at most Emax,
and all upper endpoints are at least 1 on the forced arcs. For HG,
for instance, its smallest possible free upper endpoint is `13c/12>1`.

### 5.1 Positive t>S

The nominal G leftover is `-s a_G`, bounded above using `a_G>=7/12`.
The resulting nominal excess and common flux are

\[
 g(t)=C(c-1)+Ks^2+(13/12+e-(3/2)c)s,
 \qquad D=e s+(3/2)c^2-e c.
\tag{19}
\]

On `s<=.26,c>=.96`, `D<1`, so take `Lcal=Emax-D`.
The derivatives of g and D are positive throughout this arc. For g,
a lower bound is

\[
 (e-5/12)(.96)+\{2K(.96)-C\}(.26)>0;
\]

for D, use `D'=e(c+s)-3cs>0`. Hence the least value of
`g(t)-Lcal(t)S` for `t>=S` occurs at t=S.
On `[0,.015]`, `D'>1`; moreover `D(0)=21/62` and

\[
 \rho=(e-5/12)-(E_{\max}-21/62)=193/9300>.02.
\]

Using `sin S>=S-S^3/6`, `cos S>=1-S^2/2`, and `D(S)>=D(0)+S` gives

\[
 g(S)-\mathcal L(S)S
 \ge\rho S-(e/2)S^2-((e-5/12)/6)S^3\ge0.
\tag{20}
\]

The final inequality uses `e/2<.6`, `e-5/12<.75`, and `S<=.015`.
Thus (12) contradicts feasibility.

### 5.2 Negative t=-u<-S

Here the nominal G leftover is bounded using `a_G<=U_G` and

\[
 g(u)=C(c-1)+Kr^2+(1/2-U_G+(3/2)c)r,
 \qquad D=(3/2)c^2-er.
\tag{21}
\]

On `r<=.18,c>=.98`, `D>Emax`; take `Lcal=D-1<=1/2`.
D decreases with u. The derivative of g is positive: a sufficient
rational lower bound is

\[
 .574(.98)+\{2K(.98)-C\}(.18)-(3/2)(.18)^2>0.
\]

Again it suffices to evaluate `g-Lcal S` at u=S. The elementary bounds
give the convenient weaker inequality

\[
 g(S)-\mathcal L(S)S\ge .104S-1.6S^2-.86S^3\ge0.
\tag{22}
\]

To see the constants directly, the linear nominal coefficient at zero
is `2-U_G=.604`, the cusp loss is at most `.5S`, `C/2<1.6`, and the
cubic loss is at most `.604/6+3/4<.86`. This proves the entire second
tail by (12).

## 6. G1/E1 on the complete negative tail

The positive alternative is already covered by the complete proof cited
in Section 1. Suppose `t=-u<-S`, with `r=sin u<.2,c>.97`.

### 6.1 Two justified comparisons before taking derivatives

In the actual weighted projection sum, the coefficient of aG is r
when G owns HG and `r-c sin(h0)` when H owns it. Both are nonnegative
because `u>=S>=|h0|`. Replacing aG by U_G therefore raises the coordinate
upper bound and lowers Phi.

For E-owned DE the aE coefficient is `e sin z<=0`. For D-owned DE it is
`e(sin z+sin x4)`. Put `z0=t+h0-x1-x2-x3`; then `z0<=-|x4|`, and

\[
 \sin(z_0-x_4)+\sin x_4
           =2\sin(z_0/2)\cos(z_0/2-x_4)\le0.
\]

All these angles have magnitude below .3. Thus replacing aE by L also
raises the upper bound and lowers Phi. These are comparisons of free
coordinate coefficients on the entire error segment, not assumptions
that an actual slider has an endpoint position. Retain the actual
bG,bT,bE and both actual T coordinates.

### 6.2 Nominal and first-order bounds

The H nominal force is `(e,c)`. The nominal excess after the two
comparisons and `b_E<=.9` is at least

\[
 g(u)=C_1(c-1)+Kr^2+J_1r,
\]
\[
 C_1=2+(7/5)e=562/155,\qquad
 J_1=(1+e)/2+eL-U_G>.33.
\tag{23}
\]

Since `C1/1.97-K<1.2`, the chord bound gives

\[
 g(u)\ge.33r-1.2r^2\ge.09r.
\tag{24}
\]

The flux in (8), now at the comparison aE=L, is

\[
 D=e\{c(L+1/2)-r(b_E+1/2)\},\qquad .86<D<1.23.
\tag{25}
\]

All lower cusp endpoints in (8) are at most .896; all upper endpoints
are at least 1. This includes HG with weight c and fixed aG=U_G, and
DE with fixed aE=L. Hence (9) holds with `Lcal=.23`.
Since `r>=cu>=.97S`, equations (24)--(25) imply

\[
                         g(u)-.23S\ge-.15S.
\tag{26}
\]

### 6.3 Full error remainder and contradiction

After the comparisons, the varying force norms have arguments of
magnitude at most S and sum of coefficients at most 5, so their
Hessian entries are below .075. The aligned smooth terms remain below
1.321. The E mixed smooth term is now

\[
                e\{1+(.5+b_E)\cos z-(L+.5)\sin z\}.
\]

As `|z|<.22`, its entries are below
`e(1.4+(L+.5)(.22))<1.9`. Thus the complete smooth Hessian is still
bounded by 4, and (12) applies to the compared scalar. Equations
(26) and (12) give

\[
 \Phi\ge\Psi_0-.15S-2S^2-S^3/10
 \ge112885683/101680000000>0.
\tag{27}
\]

This contradicts feasibility and completes the final negative pair.

## 7. Universal owner quantifiers and consequence

Retain any originally feasible pair of G and E witnesses. The earlier
E and high-index G theorems restrict it to four low-index pairs.
The near-zero theorem excludes `|t|<=S`. Sections 4--6 exclude all bad
pairs on the complementary tails, except positive G1/E1, which is
excluded in its cited complete companion. Hence only G0/E1 remains.
A forbidden feasible witness tied with an intended one can be paired
with any feasible witness on the other mixed edge and gives the same
contradiction. Therefore every witness, not merely a chosen witness,
satisfies (1).

**The mixed-owner gate is now closed at S<=3/200 without the final
mismatch contraction.** To bypass that contraction in the unrestricted
proof, the tilt window must still be supplied at the same threshold.
Once it is, `HAND_DIRECT_E_SUPPORT_TERMINAL.md` supplies sharpness and
the full equality implications. The earlier global G3--G5 cuts and
contractions remain separate, unproved inputs of this assembly.

All estimates above are exact force identities, circle supports,
whole-arc derivative bounds, and a single shared-error Taylor estimate.
No state mesh, angle mesh, owner certificate list, sampled bound, or
external success assertion is a premise. No Lean or historical table
source was changed; no compilation or CI was run.

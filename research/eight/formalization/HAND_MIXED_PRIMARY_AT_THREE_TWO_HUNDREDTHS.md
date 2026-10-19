# Positive G1/E1 is impossible already at S <= 3/200

## 1. The full conditional owner theorem

Assume the candidate frame, the signed role pattern `(+, -, +, -, +, -, -)`,
the G/T tangent cuts, the zero-owner restrictions and the intended B/T and
D/E quarter-owner restrictions. Let every actual exterior square satisfy
core avoidance and corner containment at `q<=Q0=9789/2500`. Assume

\[
 S=|\theta_B|+|\theta_T-\theta_B|+|\theta_D-\theta_T|
       +|\theta_E-\theta_D|+|\theta_H-t|\le3/200,
 \quad \theta_A=0,\quad\theta_G=t.
\tag{1}
\]

**Theorem.** If `t>=0`, original mixed axes G1 and E1 cannot both be
feasible. Indices 1 here are zero based, as in
`HAND_MIXED_OWNER_CLOSURE.md`. Every original aligned owner choice and
every weak separating tie is included. No preceding contraction to
`S<=1/1000`, intended mixed owner, or terminal tilt window is assumed.

The proof uses two intrinsic alternatives, `t>=S` and `0<=t<S`.
The first retains the existing one-parameter circle stress; the second
keeps both mixed angular cusps and uses one exact cycle-flux bound.
Neither alternative subdivides a state coordinate or an angle range
into a numerical cover.

This closes the entire positive G1/E1 alternative at `S<=3/200`.
The other wrong mixed-owner alternatives, tilt capture, and the earlier
global cuts/contractions remain separate obligations.

## 2. Exact projections and the forced positive arc

Write the positive canonical coordinates as `a_i,b_i`, with the signs
specified in Section 1. Set

\[
 x_1=\theta_B,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h=\theta_H-t,
\]
\[
 z=t+h-x_1-x_2-x_3-x_4,\qquad c=\cos t,\quad s=\sin t.
\]

The actual G1 and E1 projections are exactly

\[
 a_A-s a_G-c b_G,\qquad a_H+a_E\sin z-b_E\cos z.
\tag{2}
\]

The aligned projections, with the two actual owners separated by a
comma, are

\[
\begin{aligned}
 HG:&\quad b_H-a_G\sin h+b_G\cos h,
                 \quad-a_H\sin h+b_H\cos h+b_G;\\
 AB:&\quad b_A+a_B\sin x_1+b_B\cos x_1,
                 \quad a_A\sin x_1+b_A\cos x_1+b_B;\\
 BT:&\quad a_B+a_T\sin x_2-b_T\cos x_2,
                 \quad a_B\cos x_2+b_B\sin x_2-b_T;\\
 TD:&\quad b_T+a_D\sin x_3+b_D\cos x_3,
                 \quad a_T\sin x_3+b_T\cos x_3+b_D;\\
 DE:&\quad a_D+a_E\sin x_4+b_E\cos x_4,
                 \quad a_D\cos x_4+b_D\sin x_4+b_E.
\end{aligned}
\tag{3}
\]

The widths are `(1+cos x+|sin x|)/2` on aligned edges, and the same
formula at t and z on G and E. The full frame chart supplies `c>=3/4`
and `0<=s<=.7` before the sharper bound below.

For `0<=e<=.015`, the true width cusp and the center-norm bound give
nominal aligned projection at least

\[
 1-e-e^2/4-e^3/12\ge1-ke,
                  \qquad k=251/250.
\tag{4}
\]

Indeed the projection rotation loses at most `3e/2`, while the width
is at least `1+e/2-e^2/4-e^3/12`; and
`e/4+e^2/12<.004` on this whole interval.

Adding the nominal BT and TD inequalities gives
`a_B+b_D>=2-kS`. Since `b_D<.9`, we have `a_B>1.084`.
If `b_B>=.7`, then `(a_B+.5)^2+(b_B+.5)^2>Q0`; hence `b_B<.7`.
The AB inequality gives `b_A>.28`. Consequently `a_A<1.32`, because

\[
                       1.82^2+.78^2>Q_0.
\]

Add c times HG to G1. Use `b_H<.9`, `a_G>=7/12` and `a_A<1.32`.
Equations (2)--(4) imply

\[
 -.82+.6c+(13/12)s\le kS.
\]

As `1-c<=4s^2/7` and `s<=.7`, the left side is at least
`-.22+(253/300)s`. Its value at `s=.28` is greater than `k(.015)`.
Therefore

\[
                  0\le s<7/25,
 \qquad c>24/25,\qquad 0\le t<.284,
 \qquad1-c\le25s^2/49.
\tag{5}
\]

The last angle comparison follows from `sin(.284)>.28`, using the
alternating cubic lower bound. These are forced whole-arc bounds.

The common coordinate bounds used below are

\[
 447/800\le a_i\le283/200,
 \quad0\le b_i<.9,
 \quad7/12\le a_G,a_T<1.396,
 \quad b_G,b_T<.797.
\tag{6}
\]

The final bound follows from the G/T ratio at most `.8` and the single
corner comparison in `HAND_DIRECT_E_SUPPORT_TERMINAL.md`, Section 2.
We also use the global oblique support

\[
                          a_E+b_E/4\le283/200,
\tag{7}
\]

proved by Cauchy on the farthest-corner disk: `17Q0/16<(51/25)^2`.

## 3. A circle-stress scalar with all original owners retained

For a nonnegative parameter `s<=7/25`, use the functions

\[
\begin{gathered}
 p=24/41-s/4,\quad b=1-3s/4,\quad e=36/31-3s/2,
 \quad d=e(c+s/4),\quad H=c,\\
 m_A=12/41-s/32,\quad m_B=12/41-3s/16,
 \quad m_D=12/31-s/3,\quad m_H=12/31-s/4.
\end{gathered}
\tag{8}
\]

The edge weights in cyclic order HG,G,AB,BT,TD,DE,E are
`(H,1,p,b,b,d,e)`. All are positive, and all aligned weights are less
than `1.162`; in particular `d<=36/31` follows from
`e(c+s/4)<=e(1+s/4)<=36/31`.

For any resulting force `(X,Y)` on a positive canonical center,
containment gives the exact upper support

\[
 T_q(X,Y;m)=mq+(X^2+Y^2)/(4m)-(X+Y)/2\ge Xa_i+Yb_i.
\tag{9}
\]

Apply (9) to A,B,D,H, with the masses in (8); keep the actual G,T,E
coordinates in the other terms. The resulting demand-minus-upper-support
scalar will be called `Phi`. Feasibility of all seven selected original
axes implies `Phi<=0`. Proving a positive lower bound for this scalar is
therefore sufficient, for any actual owner choices.

At zero aligned errors the four forces are `(1,p),(b,p),(d,b),(e,c)`.
When `a_G=7/12` and `a_E+b_E/4=283/200`, its reference value is precisely
the function `Psi(c,s)` in equations (7)--(12) of
`HAND_MIXED_PRIMARY_ADAPTIVE_STRESS.md`.

That note's single exact degree-seven identity remains valid on the
larger interval in (5). Its positivity proof extends as follows. With
its notation `A0=572973160660992` and its printed polynomial P,

\[
 \begin{aligned}
 P(s)/A0&\ge1-5s+s^2\{13-42s+s^2(64-44s)\}+s^6(12-s)\\
 &\ge1-5s+(26/5)s^2\ge24/3125>0
                                  \quad(0\le s\le7/25).
 \end{aligned}
\tag{10}
\]

Here `64-44s>51`, the decreasing quadratic `13-42s+51s^2` exceeds
`26/5` at `7/25`, and the final quadratic is decreasing with the
stated positive endpoint. The cosine coefficient in the cited identity
stays positive and all four denominator factors keep their signs on
this larger interval. Hence its exact chord argument gives

\[
                 \Psi(c,s)\ge\Psi_0=3027/794375.
\tag{11}
\]

Thus (11) is a whole-domain consequence of the already displayed stress
identity, not a claim based on additional parameter evaluations.

## 4. The regime t >= S: remove the two free primary coordinates

First the coefficient of `a_G` in the weighted projection sum is `-s`
when G owns HG, and `-s-c sin h` when H owns it. Both are nonpositive
when `t>=S>=|h|`. Replacing `a_G` by `7/12` can only increase the
projection upper bound and decrease Phi.

For E-owned DE the coefficient of `a_E` is `e sin z>=0`. For D-owned
DE it is `e sin z+d sin x4`. This too is nonnegative. Indeed put
`z0=t+h-x1-x2-x3` and `y=x4`. Then

\[
 z_0\ge t-S+|y|\ge|y|,\qquad z_0<.3,
\]
\[
 (e\sin z+d\sin y)/e
 =\sin z_0\cos y+(c+s/4-\cos z_0)\sin y.
\]

Its first term is at least `.98 z0`; the absolute coefficient in its
second term is at most `s/4+|z0-t|<=.085`. Thus the expression is
nonnegative, including at the zero endpoint.
By (7), replacing `a_E` by `283/200-b_E/4` again lowers Phi.
Call these substituted primary coordinates the comparison free
coordinates. They need not form an actual square: the coefficient
signs prove the comparison for every actual state.

The remaining free quantities satisfy

\[
 a_G=7/12,\quad0\le b_G<.797,\quad
 7/12\le a_T<1.396,\quad0\le b_T<.797,
 \quad0\le b_E<.9,\quad a_E=1.415-b_E/4.
\tag{12}
\]

At zero errors this scalar is at least (11), independently of the
remaining free coordinates.

### 4.1 One first-derivative bound for every owner

The derivative of the circle support (9) in its force is the virtual
center `(X/(2m)-1/2,Y/(2m)-1/2)`. Accordingly define

\[
\begin{gathered}
 A_*=1/(2m_A)-1/2,\quad B_*=b/(2m_B)-1/2,
 \quad B^*=p/(2m_B)-1/2,\\
 D_*=d/(2m_D)-1/2,\quad D^*=b/(2m_D)-1/2,
 \quad H_*=e/(2m_H)-1/2.
\end{gathered}
\]

Remove the five aligned cusp terms from Phi. Its smooth first
coefficients are of the form `D-lambda R` on x1,x2,x3,x4 and
`H R-D` on h, where

\[
 D=e\{c(a_E-1/2)+s(b_E+1/2)\},
\tag{13}
\]

and the possible receivers R are, respectively,

\[
 \{A_*,B_*\},\quad\{a_T,B^*\},\quad
 \{a_T,D_*\},\quad\{a_E,D^*\},\quad\{7/12,H_*\}.
\tag{14}
\]

Their aligned weights are `p,b,b,d,H`. Equations (13)--(14) follow
also by differentiating the literal projections (2)--(3).

Here are two sufficient bounds on the one common correction D:

\[
               .896b-.1<D<bp/(2m_B)+.1.
\tag{15}
\]

We give the full parameter proof. From (12),

\[
 D=e\{.915c+.5s+b_E(s-c/4)\}.
\]

Since `max(s-c/4,0)<=s/7` on (5),

\[
 D\le e(.915+22s/35)<1.063-.642s.
\]

Direct subtraction gives

\[
 bp-(1-.6s)(2m_B)=s(61/1640-3s/80)\ge0,
\]

so this upper bound is smaller than `bp/(2m_B)+.1`.
For the lower bound, D is at least e times the smaller of
`.69c+1.4s` and `.915c+.5s`. Replace c by `1-25s^2/49`.
After subtracting `.896b-.1`, these two expressions are bounded below
by, respectively,

\[
 .005+s(1.262-2.51s),\qquad .266-.120s-1.293s^2.
\]

Both are positive throughout `[0,.28]`, by substituting `.28` in their
negative terms. This proves (15), in particular `D>.60784`.

The elementary virtual-center bounds needed in (14) are

\[
 A_*,B_*<1.27,\quad .5\le B^*\le7/12,
 \quad7/12\le D_*,H_*\le1,\quad .5\le D^*\le.9.
\tag{16}
\]

For reproduction, `m_A>.283` bounds A*, and
`(41/12)m_B-b=7s/64>=0` bounds B*. The identity
`p-2m_B=s/8` and the inequality
`(13/12)(2m_B)-p=2/41-5s/32>0` bound B*.
The upper D* bound follows from `3m_D-d>=0`; its lower follows from

\[
 d-(13/6)m_D>.322-.488s-.968s^2>0.
\]

For H*, use `3m_H-e=3s/4` and
`e-(13/6)m_H=10/31-23s/24>0`. For D^*, use
`b-2m_D=7/31-s/12>0` and
`(14/5)m_D-b=13/155-11s/60>0`.
Finally

\[
 m_B-bm_A=s(83/1312-3s/128)\ge0
\]

shows `bp/(2m_B)<=p/(2m_A)`.

Equations (15)--(16) prove, for every receiver except the direct E
receiver, that its smooth coefficient lies within `.1` of the interval
`[-lambda/2,lambda/2]`. To see the potentially tight cases explicitly:
the AB upper comparison and the B^* comparison are the upper bound in
(15); the actual T and D_* receivers use
`D>.896b-.1` and `D<13b/12+.1`. The other lower comparisons follow
already from `D>.60784`. For HG, `D<1.063` is smaller than
`(24/25)(13/12)+.1`. For D^*, use
`d/(2m_D)>=13/12` with the same upper bound in (15).

For the direct E receiver the two reserves are nonnegative without
`.1`: substituting (13) and `d=e(c+s/4)` gives

\[
 D-da_E+d/2=e s(b_E+5/8-a_E/4)\ge0,
\]
\[
 d/2-(D-da_E)=e\{c+s(a_E/4-b_E-3/8)\}>0.
\]

Consequently the complete first-order term, including the aligned
linear cusps, is at least `-S/10` for every original owner assignment.

### 4.2 A uniform Hessian bound of 5

For clarity the second-derivative estimate can be checked without a
symbolic table. Each weighted anchor force is the sum of an e-like and
an f-like vector, with one or both rotated through its incident aligned
error. Thus the only nonconstant force-norm terms, up to sign, are sine
functions of sums of consecutive aligned errors, with coefficients

\[
 p/(2m_A)<1.04,\quad bp/(2m_B)<1.22,
 \quad db/(2m_D)<1.98,\quad eH/(2m_H)<1.84.
\]

The only overlap in one Hessian entry is the A/B pair on x1; its
absolute contribution is less than `(1.04+1.22)(.015)<.035`.
Every other norm entry is smaller.

Combining an aligned width with the linear terms `(X+Y)/2` in (9)
gives second derivatives of absolute value at most
`lambda(1+.015/2)<1.171`, only on that aligned coordinate's diagonal.
The mixed E smooth term, including its comparison free coordinates,
is

\[
              e\{(b_E+.5)\cos z+(.5-a_E)\sin z\}.
\]

Since `0<=z<.3`, every one of its Hessian entries is bounded by
`1.162(1.4+.915(.3))<1.947`. The remaining free T and G terms depend
only on their single incident aligned errors and have second derivatives
less than `.819`; the free E term on DE, when present, has second
derivative less than `1.162(.9+1.415(.015))<1.072`.
The free T, free G and free E aligned terms occupy disjoint diagonals,
so their bounds do not add in an entry. The mixed G term is fixed in
this regime. Therefore every smooth Hessian entry is bounded by

\[
                    .035+1.171+1.947+1.072<5.
\tag{17}
\]

Taylor's theorem in the five errors loses at most `5S^2/2`.
The aligned sine cusps lose at most `S^3/10` compared with their linear
cusps. Equations (11), (15)--(17) therefore give

\[
 \Phi\ge3027/794375-S/10-(5/2)S^2-S^3/10>1/2000.
\tag{18}
\]

The last inequality follows by putting `S=.015` into its three
increasing loss terms. It contradicts feasibility on the whole regime
`t>=S`.

## 5. The regime 0 <= t < S: retain both mixed cusps

Now use the **single constant stress** obtained by setting `s=0,c=1`
in (8): weights `(1,1,24/41,1,1,36/31,36/31)` and masses
`(12/41,12/41,12/31,12/31)` on A,B,D,H. Its all-zero reference value is
again exactly `3027/794375`, for every actual G,T,E coordinate.
No comparison replacement of their primary coordinates is made.

The virtual A and B centers are `(29/24,1/2)`; the D and H centers
are `(1,19/24)`. Put `p0=24/41`, `e0=36/31`, and

\[
                         D=\max\{4/5,e_0(a_E-1/2)\}.
\tag{19}
\]

By (6),

\[
 .8\le D<1.063<a_G+1/2,
 \qquad e_0(a_E-1/2)\le D\le e_0(a_E+1/2).
\tag{20}
\]

The upper endpoint in the second inequality follows since
`e0(447/800+1/2)>.8`.
Thus the exact elementary support of the E cusp is

\[
                 (e_0/2)|z|-e_0a_E z\ge-Dz.
\tag{21}
\]

The G first-order term, including its own cusp and `t>=0`, is
`(a_G+1/2)t`. Using `z=t+h-x1-x2-x3-x4`, (21) makes the combined
first-order expression at least

\[
 (a_G+1/2-D)t+(R_H-D)h
          +\sum_{i=1}^4(D-\lambda_iR_i)x_i
          +\sum_{i=1}^5(\lambda_i/2)|x_i|.
\tag{22}
\]

Here the possible receivers are exactly

\[
 R_H\in\{a_G,1\},\quad
 R_1=29/24,\quad R_2\in\{a_T,1/2\},
 \quad R_3\in\{1,a_T\},\quad R_4\in\{a_E,19/24\}.
\]

The first term of (22) is nonnegative by (20). Each of its five
remaining smooth coefficients is within `.1` of its cusp interval.
For the T and G receivers this is the pair of inequalities
`D>=.8>1.396-.6` and `D<1.063<.5+.6`. For AB its interval enlarged
by `.1` is `[17/41-.1,1.1]`, containing D. For the direct E receiver
(20) gives the exact cusp interval; the alternative receiver has the
larger interval `[21/62-.1,1.6]`. Thus (22) is at least `-S/10`.

This is a cycle-flux argument with a real parameter D chosen from two
explicit coordinate bounds. It is not an enumeration of sign vectors.
In particular it keeps the correlation between the two mixed angles
and the five aligned errors, even when the actual HE angle changes sign.

### 5.1 The whole small-tilt remainder

Remove all seven angular sine cusps and consider the resulting smooth
scalar in the six variables `(x1,x2,x3,x4,h,t)`. Its argument norm is at
most `S+t<=2S<=.03`. The two mixed angles have magnitudes at most
`.015` and `.03`, respectively.

The four force-norm coefficients now simplify exactly to `1,1,3/2,3/2`;
their Hessian entries have absolute value at most `.03`. Aligned
width/offset entries are less than `1.171`, on separate diagonals.
The mixed E smooth term is now

\[
                      e_0\{(b_E+.5)\cos z-a_E\sin z\},
\]

whose entries have absolute value less than
`e0(1.4+1.415(.03))<1.676`.
The free G and T aligned terms have second derivatives less than `.818`,
on their respective diagonals. The free E term on DE is less than
`e0(.9+1.415(.015))<1.071`, again on only its own diagonal.
On the t diagonal, the mixed G smooth term has absolute curvature
less than `1.297+1.396(.015)<1.318`.

Consequently the largest possible diagonal bound is the DE bound
`1.676+1.171+1.071+.03<4`. The t bound is `1.676+1.318<4`;
the other diagonal and all off-diagonal bounds are smaller. Every
smooth Hessian entry is therefore bounded by 4 throughout the whole
segment. Taylor loses at most `2(S+t)^2<=8S^2`.

The aligned sine cusps lose less than `S^3/10`, the G cusp loses at most
`S^3/12`, and the E cusp loses less than `4S^3/5`.
Their total is less than `S^3`. Combining these remainders with (22),

\[
 \Phi\ge3027/794375-S/10-8S^2-S^3.
\tag{23}
\]

At `S=.015`, the right side equals

\[
                     5156883/10168000000>1/2000.
\]

All its loss terms increase with S, so (23) is positive on the whole
remaining regime, including `t=0`. This again contradicts feasibility.

## 6. Coverage and consequence

Sections 4 and 5 exhaust every nonnegative t permitted by the original
frame. The positive-arc restriction (5) was deduced from the actual
G1 witness and the actual aligned chain at `S<=3/200`; it is not a
borrowed consequence of the old `S<=1/1000` theorem.

Each actual owner was retained in (3), through the four weighted anchor
forces, and in the receiver alternatives (14), (22). The Hessian bounds
hold on the full error segment with one shared norm S. The exact cusp
support (21) includes both signs of the HE angle and every zero tie.
Every mathematical premise is an explicit circle support, a derivative
bound on its whole parameter domain, or the single printed polynomial
identity in the earlier analytic stress note with its extended positivity
proof (10). There is no continuous state/angle table or external acceptance
assertion.

This proves the claimed full positive G1/E1 exclusion at `S<=3/200`.
Together with `HAND_DIRECT_E_SUPPORT_TERMINAL.md`, it removes two specific
uses of the old `.001` threshold. It does not yet remove all other mixed
owner or tilt-capture uses of that threshold. The unrestricted theorem
therefore remains dependent on those explicitly separate capture gates.

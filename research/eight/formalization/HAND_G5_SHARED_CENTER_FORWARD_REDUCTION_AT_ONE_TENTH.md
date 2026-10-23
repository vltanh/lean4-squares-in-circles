# A shared-center forward reduction at S <= 1/10

## 1. Proved reduction and its scope

This note proves an explicit necessary scalar inequality for an actual
cycle. It retains the common middle center at every step of

\[
       E\longrightarrow D\longrightarrow T\longrightarrow B
       \longrightarrow A\longrightarrow H.
\]

All five signed errors are retained. In particular, the two quarter
errors are not bounded independently and then combined using unrelated
intermediate squares.

Assume G0--G2, `q<=Q=9789/2500`, the G2 sign `y_E<=0`, and

\[
 S=|d_H|+|d_A|+|x|+|d_T|+|y|\le\frac1{10},
 \qquad x=d_B,\quad y=d_D.
\tag{1}
\]

Retain original feasible BT and DE witnesses in `{2,3}`, an original
GA witness 0, and an original EH witness 1. Either quarter owner is
allowed independently, including ties. These owner hypotheses are
**inputs** at the scale (1); the owner theorems at `S<=1/32` cannot be
used to supply them here.

No G/T/H/D tangent cut, sign of either mixed tilt, outer-contact
condition, or comparison-center replacement is assumed. The result is
the necessary inequality (19) below. Positivity of its left side on
the proposed contraction annulus is a separate analytic target; this
note does not assert that positivity or either G5 contraction.

## 2. Original signs, corner coordinates, and exact error budget

The global zero-owner theorem and
`HAND_ZERO_EDGE_SIGN_RIGIDITY_AT_ONE_TENTH.md` give the six strict
zero-edge signs. Write

\[
 (y_H,y_G,y_A,y_B,y_T,y_D)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_E=-y_E\ge0.
\]

For every role put `X_i=a_i+1/2`, `Z_i=b_i+1/2`. The unchanged
original centers satisfy

\[
 X_i^2+Z_i^2\le Q,\quad X_i\ge Z_i\ge\tfrac12,
 \quad X_i>L_c:=\frac{847}{800},\quad Z_i<\frac75.
\tag{2}
\]

The last bound is the entry estimate `b_i<9/10`. One additional
all-role core bound, useful for the B-owned BT branch, is

\[
 a_i+\frac{b_i}{20}\ge\frac7{12},\qquad
 X_i+\frac{Z_i}{20}\ge\frac{133}{120}.
\tag{3}
\]

Indeed, if `b_i<=1/2`, core avoidance gives `a_i>=7/12`. Otherwise
`a_i+b_i/20>447/800+1/40=467/800>7/12`.

Set

\[
 q_i=1-d_i+\frac{|d_i|}{32}\quad(i=H,A,T).
\tag{4}
\]

The proved signed zero inequality in
`HAND_G5_SIGNED_ZERO_COERCIVITY_AT_ONE_TENTH.md` gives

\[
 b_H+b_G\ge q_H,\quad b_A+b_B\ge q_A,
 \quad b_T+b_D\ge q_T.
\tag{5}
\]

In particular `q_i>=289/320`. These are three directional charges,
each using its actual signed error.

Normalize A's real frame to zero and write G's frame as t. The frames
of H, B, T, D, E are respectively

\[
 t-d_H,\quad d_A,\quad d_A+x,\quad d_A+x+d_T,
 \quad d_A+x+d_T+y.
\]

Thus the actual EH mixed tilt is exactly

\[
 \phi=t-d_H-d_A-x-d_T-y.
\tag{6}
\]

The real-frame spread gives `|t|,|phi|<7/10`. If
`R=|d_H|+|d_A|+|d_T|`, then `|phi-(t-x-y)|<=R` and
`S=R+|x|+|y|`. Formula (6), rather than a new independent error,
is used below.

Write

\[
 W(v)=\frac{1+\cos v+|\sin v|}{2},\qquad z_+=\max(z,0).
\]

All angles used in W lie in `(-7/10,7/10)`, so cosine is positive.
For the two quarter errors, `cos x,cos y>=199/200` and
`|sin x|,|sin y|<=1/10`.

## 3. A continuous circular-cap formula

Suppose `c>0`, `c^2+s^2=1`, `k>=0`, `k>sqrt(Q)*s`, and

\[
 X^2+Z^2\le Q,\qquad cX+sZ\ge k.
\]

Then feasibility gives `k<=sqrt(Q)` and

\[
 Z\le \mathcal C(c,s,k):=sk+c\sqrt{Q-k^2}.
\tag{7}
\]

To see this, put `v=cX+sZ`. Orthogonal decomposition bounds
`Z<=sv+c*sqrt(Q-v^2)`. This last function decreases for `v>=k`:
if `s<=0` this is immediate, and if `s>0` its derivative is
negative precisely after `v=s*sqrt(Q)`. This proves (7).

Whenever a radicand below would be negative, or an inferred upper
corner bound would be less than `1/2`, the original inequalities are
already inconsistent. All following formulas are evaluated on the
remaining domain, where their radicals exist.

## 4. DE: retain the original E corner and its actual owner

Let

\[
                         (X,Z)=(X_E,Z_E).
\]

These are actual corner coordinates; in particular
`X^2+Z^2<=Q`, `X>=Z>=1/2`, and (2)--(3) hold.

### DE axis 3: D owns ED

The actual projection is

\[
 a_D+a_E\sin y+b_E\cos y\ge W(y).
\]

Consequently define

\[
 Y_D=\max\left\{L_c,
 1+(1-X)\sin y+(1-Z)\cos y+(-\sin y)_+\right\}.
\]

Then `X_D>=Y_D`, and the D circle gives

\[
 V_D=\min\left\{\frac75,\sqrt{Q-Y_D^2}\right\},
                         \qquad Z_D\le V_D.
\tag{8a}
\]

### DE axis 2: E owns ED

Its actual projection is
`a_D*cos y+b_D*sin y+b_E>=W(y)`. In corner coordinates this is

\[
 X_D\cos y+Z_D\sin y\ge k_D,
 \qquad k_D=1-Z+\cos y+(\sin y)_+.
\]

Here `k_D>=119/200>sqrt(Q)*sin y`; therefore (7) gives

\[
 V_D=\min\left\{\frac75,
 \mathcal C(\cos y,\sin y,k_D)\right\},
                         \qquad Z_D\le V_D.
\tag{8b}
\]

These are the two intrinsic DE alternatives. They use the same E
corner (X,Z), which reappears in the final EH constraint.

## 5. TD and BT: keep the common T corner

By (5), define

\[
                T_0=q_T+1-V_D,\qquad Z_T\ge T_0.
\tag{9}
\]

The bound `V_D<=7/5` gives `T_0>=161/320>1/2`.

### BT axis 2: T owns TB

Its actual projection is
`a_B*cos x+b_B*sin x-b_T>=W(x)`. Thus

\[
 X_B\cos x+Z_B\sin x\ge k_B,
 \qquad k_B=T_0+\cos x+(\sin x)_+.
\]

Since `k_B>=2397/1600>sqrt(Q)*sin x`, (7) gives

\[
 V_B=\min\left\{\frac75,
 \mathcal C(\cos x,\sin x,k_B)\right\},
                         \qquad Z_B\le V_B.
\tag{10a}
\]

### BT axis 3: B owns TB

Its actual projection is
`a_B+a_T*sin x-b_T*cos x>=W(x)`. Equivalently,

\[
 X_B\ge1+(\sin x)_+-X_T\sin x+Z_T\cos x.
\tag{11}
\]

If `sin x>=0`, use the T circle at its actual `Z_T`.
The function
`z*cos x-sin x*sqrt(Q-z^2)` increases for `z>=0`, so (9) gives

\[
 U_B=1+\sin x+T_0\cos x
                  -\sin x\sqrt{Q-T_0^2}.
\tag{12+}
\]

If `sin x=-r<=0`, use all three actual lower bounds for `X_T`
from (2)--(3). The function

\[
 z\cos x+r\max\{L_c,z,133/120-z/20\}
\]

is increasing: the three affine slopes are `cos x`, `cos x+r`,
and `cos x-r/20`, all positive. Hence

\[
 U_B=1+T_0\cos x+r\max\{L_c,T_0,133/120-T_0/20\}.
\tag{12-}
\]

In both cases `X_B>=U_B>0`. Complete the B circle:

\[
 V_B=\min\left\{\frac75,\sqrt{Q-U_B^2}\right\},
                         \qquad Z_B\le V_B.
\tag{10b}
\]

For positivity in the plus case, a sufficient coarse comparison is
`U_B>=1+(199/200)(1/2)-1/10>0`; the minus case is immediate.
The two expressions (12) agree at x=0.

## 6. AB, GA, and HG: keep the common A corner

The actual AB charge gives

\[
                     A_0=q_A+1-V_B,\qquad Z_A\ge A_0.
\tag{13}
\]

Again `A_0>=161/320>1/2`. Define the exact circular support with
this lower transverse coordinate by

\[
 \mathcal A(t,A_0)=
 \begin{cases}
 \sqrt Q,& A_0\le-\sqrt Q\sin t,\\
 \cos t\sqrt{Q-A_0^2}-A_0\sin t,&
                          A_0>-\sqrt Q\sin t.
 \end{cases}
\tag{14}
\]

Then

\[
                     X_A\cos t-Z_A\sin t
                         \le\mathcal A(t,A_0).
\tag{15}
\]

Indeed, for fixed `Z_A=z`, the circle bounds the expression by
`cos t*sqrt(Q-z^2)-z*sin t`. Its unique unconstrained maximum
occurs at `z=-sqrt(Q)*sin t` when this point is allowed; otherwise
the maximum on `z>=A_0` occurs at `A_0`. This proves (14)--(15)
for both signs of t. The two branches meet continuously.

Add the retained original GA0 projection
`a_A*cos t-b_A*sin t-b_G>=W(t)` to the actual HG charge (5).
After converting to corners and applying (15), obtain

\[
 Z_H\ge K_1:=q_H+1+\cos t+(-\sin t)_+
                              -\mathcal A(t,A_0).
\tag{16}
\]

This lower bound is positive. For example,
`q_H>=289/320`, `cos t>=3/4`, and `sqrt(Q)<2` give
`K_1>209/320>1/2`.

## 7. EH: close the path using the same E corner

The retained original EH1 projection is

\[
            a_H+a_E\sin\phi-b_E\cos\phi\ge W(\phi),
\]

with the exact shared-error angle (6). Thus

\[
 X_H\ge1+Z\cos\phi-(X-1)\sin\phi+(-\sin\phi)_+.
\tag{17}
\]

The H primary cone and core bound also give `X_H>=Z_H>=K_1`
and `X_H>L_c`. Put

\[
 K_2=\max\left\{L_c,K_1,
 1+Z\cos\phi-(X-1)\sin\phi+(-\sin\phi)_+\right\}.
\tag{18}
\]

Applying the original H circle proves the promised scalar condition:

\[
                \boxed{K_1^2+K_2^2-Q\le0.}
\tag{19}
\]

Every operation above is an inequality on an original shared center,
a monotone scalar substitution, or one circular support. No comparison
packing is assumed feasible. Every original quarter-owner choice is
retained in (8) and (10); no owner tie is resolved by preference.

## 8. A concrete remaining scalar target

For the owner hypotheses in Section 1, one sufficient contraction
target is strict positivity in (19) whenever

\[
 \frac1{32}\le |d_H|+|d_A|+|x|+|d_T|+|y|\le\frac1{10},
\tag{20}
\]

on the E-corner domain (2)--(3), with the exact angle (6) and
`|t|,|phi|<7/10`. There are only the two intrinsic choices in each
of (8) and (10). This is a specified analytic target, not a proved
positivity assertion; if its relaxation admits a nonpositive value,
additional original constraints must be retained.

The hard two-quarter subdomain has

\[
 d_H=d_A=d_T=0,\quad x=-u\le0,\quad y=v\ge0,
 \quad\phi=t+u-v,
\]

with `u+v` in (20). On `t,phi>=0`, the actual E primary coordinate
may be increased to `X=sqrt(Q-Z^2)` in this necessary bound: in
the D-owned DE projection and EH projection this weakens their lower
corner demands, and the E-owned DE projection does not use X.
Thus this subdomain reduces to the four real variables `(u,v,t,Z)`.

For example, for T-owned TB and D-owned ED, the unsaturated formulas
are particularly short:

\[
\begin{gathered}
 X=\sqrt{Q-Z^2},\quad
 Y=1+(1-X)\sin v+(1-Z)\cos v,\quad V=\sqrt{Q-Y^2},\\
 C=2+\cos u-V,\quad
 \ell=\cos u\sqrt{Q-C^2}-C\sin u,\\
 a=2-\ell,\quad r=\sqrt{Q-a^2},\\
 K_1=2-\cos t(r-1)+a\sin t,\quad
 K_2\ge1+Z\cos(t+u-v)-(X-1)\sin(t+u-v).
\end{gathered}
\tag{21}
\]

Here “unsaturated” means that none of the displayed minima or maxima
in Sections 4--7 is active. On other inputs those proven min/max
formulas must be retained; (21) is not a license to drop their domain
conditions. This two-error expression already couples BT and ED
through D, T, B, A, H, and the same E corner.

No angle mesh, state cover, numerical minimum, generated row
certificate, Lean compilation, or CI run is a premise of the reduction.
The unresolved steps are the scalar positivity in (20), or a stronger
shared-center inequality if needed, and the owner capture needed to
apply this branch to every cycle at the larger mismatch scale.

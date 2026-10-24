# A uniform support-height bound for every circle-touching unit square

**Status: complete hand geometric inequality; root and separate independent full
hand audits passed.** Let S be a unit square contained in the radius-R disk
about O, with at least one physical circle corner, and suppose

\[
                              R\ge\frac{79}{40}.
\tag{1}
\]

Let e be a unit direction, and let delta be the unsigned angle between
e and the nonzero center vector c_S-O. If 0<=delta<=pi/4, then

\[
 \min_{x\in S} e\cdot(x-O)
 \ge (R-\sqrt2)\cos\delta
                   -\frac9{40}\frac{\sin^2\delta}{\cos\delta}.
\tag{2}
\]

The inequality uses the complete independently oriented unit-square
domain. It has no force, load-weight, contact-owner or shared-mean
premise. Both physical one- and two-circle-corner masks are included.

## 1. The exact farthest-corner radius and the full vertical halfwidth

Translate O to0. Put sigma=1/sqrt(2) and r=|c_S|. A physical circle
corner and the square half-diagonal give r>=R-sigma>0.

Choose a corner diagonal direction v nearest to c_S/r. The unsigned
angle u between those directions belongs to[0,pi/4]. The four corners
are c_S plus or minus sigma*v or sigma*Jv. Since S touches the circle,
its farthest corner gives the exact equation

\[
 R^2=r^2+2\sigma r\cos u+\sigma^2,
 \qquad
 r=\sqrt{R^2-\sigma^2\sin^2u}-\sigma\cos u.
\tag{3}
\]

This includes u=pi/4, when two physical corners are equally farthest.
No corner is chosen according to a possibly zero stress weight.

Write c=cos(delta), s=sin(delta), C=cos(u), S_0=sin(u). The square's
halfwidth in direction e is

\[
 h_e=\sigma\max\{|e\cdot v|,|e\cdot Jv|\}.
\]

The angle addition formulas, with either relative orientation sign,
give

\[
 |e\cdot v|\le cC+sS_0,
 \qquad |e\cdot Jv|\le sC+cS_0.
\]

Both delta and u are at most pi/4, so

\[
 (cC+sS_0)-(sC+cS_0)=(c-s)(C-S_0)\ge0.
\]

Consequently the complete halfwidth satisfies

\[
                         h_e\le\sigma(cC+sS_0).
\tag{4}
\]

There is no assumption that the nearest radial diagonal is the one
with greatest e-projection; the maximum in (4) covers both diagonals.

## 2. A quadratic lower bound covers the entire frame interval

Define

\[
 \kappa=\frac1{2\bigl(R+\sqrt{R^2-1/2}\bigr)}.
\tag{5}
\]

The exact difference of squares gives, for every u in[0,pi/4],

\[
 \sqrt{R^2-\tfrac12\sin^2u}
 \ge R-\kappa\sin^2u.
\tag{6}
\]

Indeed its actual denominator is
2(R+sqrt(R^2-(1/2)sin^2u)), at least the denominator used in (5).
From (1), sqrt(R^2-1/2)>9/5 and
R+sqrt(R^2-1/2)>151/40>15/4. Thus

\[
                       0<\kappa<\frac2{15},
                 \qquad \sigma>\frac7{10}.
\tag{7}
\]

Combining (3)--(6) and using 1-C>=S_0^2/2 gives

\[
\begin{split}
 \min_{x\in S}e\cdot x
 &=rc-h_e\\
 &\ge c\sqrt{R^2-\tfrac12 S_0^2}
                     -\sigma(2cC+sS_0)\\
 &\ge (R-2\sigma)c
                 +(\sigma-\kappa)cS_0^2-\sigma sS_0\\
 &\ge (R-\sqrt2)c
             -\frac{\sigma^2}{4(\sigma-\kappa)}\frac{s^2}{c}.
\end{split}
\tag{8}
\]

The last line completes a positive quadratic square; it covers the
whole S_0 interval, including both endpoints. The coefficient obeys

\[
 \frac{\sigma^2}{4(\sigma-\kappa)}
       =\frac1{8(\sigma-\kappa)}
       <\frac{15}{68}<\frac9{40},
\tag{9}
\]

because sigma-kappa>17/30. Substituting this bound in (8) proves (2).

## 3. The complete coupled-angle consequence for a unit support gap

Set

\[
 \theta=\arccos(9/25),\qquad \alpha=3\theta-\pi,
 \qquad
 f_R(t)=(R-\sqrt2)\cos t-\frac9{40}\frac{\sin^2t}{\cos t}.
\tag{10}
\]

The exact triple-angle comparison in
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md gives
0<alpha<pi/6 and cos(alpha)=13959/15625>89/100.
The function

\[
 f_R(t)=\left(R-\sqrt2+\frac9{40}\right)\cos t
                                      -\frac9{40}\sec t
\tag{11}
\]

is strictly concave on[0,alpha] and strictly decreasing away from0.
For two nonnegative angles with delta_1+delta_2<alpha, concavity at
fixed sum and then monotonicity give

\[
             f_R(\delta_1)+f_R(\delta_2)
                       >f_R(0)+f_R(\alpha)>1.
\tag{12}
\]

Here is an exact uniform check of the last strict inequality. Since
sqrt(2)<99/70 and R>=79/40, put D=R-sqrt(2)>157/280. If
c_alpha=cos(alpha)>89/100, then

\[
\begin{split}
 f_R(0)+f_R(\alpha)
 &=D(1+c_\alpha)-\frac9{40}\frac{1-c_\alpha^2}{c_\alpha}\\
 &>\frac{157}{280}\left(1+\frac{89}{100}\right)
       -\frac9{40}\frac{1-(89/100)^2}{89/100}\\
 &=\frac{2241}{2225}>1.
\end{split}
\tag{13}
\]

The expression is increasing in D and in c_alpha, so the substitution
has the stated direction. Equations (2),(12) prohibit two such boundary
units from having their opposing actual support heights sum to1.
This corollary requires the stated center directions and coupled-angle
bound; it does not infer them from containment alone.

No numerical pose, sampled frame interval, circle-weight assumption,
Lean compilation or CI is used.

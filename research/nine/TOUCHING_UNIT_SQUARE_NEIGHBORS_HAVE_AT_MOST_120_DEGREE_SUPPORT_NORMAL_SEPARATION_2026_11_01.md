# Touching neighbors of a unit square have supporting normals at most 120 degrees apart

Date: November 1, 2026. Author: module_universal.

**Status: complete new hand geometry, frozen for independent review.**
The theorem is radius-free and force-free. It covers all actual support
normals and applications, including side-interior means and every normal
cone endpoint. No strict-selection premise is needed. The earlier
weaker touching-neighbor estimate is unchanged in its frozen source.

## 1. Exact statement

Let U,A,B be three distinct closed unit squares with pairwise disjoint
open interiors. Suppose all three physical contacts U--A, U--B, A--B
are present. Choose any actual common unit support normal n_A from U
toward A and n_B from U toward B, at any corresponding original
applications p_A,p_B. Thus U maximizes each normal at its application,
and the neighboring square minimizes it there.

**Theorem.**

\[
n_A\cdot n_B\ge-\frac12.                              \tag{1}
\]

Equivalently their principal angular separation is at most 120 degrees.
For every pair of positive weights a,b it follows that

\[
|a n_A+b n_B|\ge\frac{a+b}{2}.                         \tag{2}
\]

The constants are sharp in the force-free physical setting, as the
exact equality construction in Section 5 shows. The theorem neither
asserts a full equilibrium on these three bodies nor removes any force
at a higher-degree body.

## 2. A unit support-face reach bound

Let S be any unit square, p any minimum support point for a unit vector
n=(a,b) in fixed orthonormal coordinates, and assume a>0. Then every
x in S satisfies

\[
x_1\ge p_1-|b|.                                        \tag{3}
\]

If p is a minimum-support vertex, write

\[
S=p+[0,1]u+[0,1]v,
\]

where u,v are orthonormal unit side directions into S. They satisfy
`n.u>=0` and `n.v>=0`. The two numbers u_1,v_1 cannot both be negative,
because n is their nonnegative-coordinate combination and n_1>0.
For any one of u,v, denoted w, with w_1<0, its support inequality gives

\[
|b|\,|w_2|\ge a|w_1|.
\]

Squaring and using `a^2+b^2=|w|^2=1` gives `|w_1|<=|b|`. At most one
side direction has negative first coordinate, so the minimum first
coordinate in the displayed square differs from p_1 by at most |b|.
This proves (3) at every vertex, including a normal-cone endpoint.

If p lies in the relative interior of a minimum support side, then n
is its inward own-side normal. In its actual side frame every point is

\[
p+s t+r n,\qquad -\alpha\le s\le1-\alpha,\quad0\le r\le1,
\]

where t is a unit side direction and `0<alpha<1`. The term `r n_1` is
nonnegative and `|t_1|=|b|`; the possible negative side displacement is
at most |b|. This proves (3) for every side-interior application too.

Reflection gives the corresponding statement for a<0:

\[
x_1\le p_1+|b|.                                        \tag{4}
\]

Exchanging the coordinate axes gives the identical vertical versions.
These are bounds on all actual points of S, not on a chosen edge
endpoint or a replaced contact mean.

## 3. Complete support-normal cover in the actual U frame

Place U=[-1/2,1/2]^2 in its own frame. If `n_A.n_B>=0`, (1) is
immediate. Suppose the dot product is negative. Some product of the
two corresponding components is strictly negative. Reflect the relevant
coordinate and, if necessary, exchange the axes so that

\[
n_A=(a,b),\quad n_B=(-c,d),\qquad a,c>0.
\]

The actual U support applications consequently have first coordinates
`(p_A)_1=1/2`, `(p_B)_1=-1/2`, even when either application is a mean
on a vertical side. Apply (3)--(4) to the actual neighboring squares.
Every common point z in A intersect B must satisfy

\[
\frac12-|b|\le z_1\le-\frac12+|d|.
\]

Therefore

\[
|b|+|d|\ge1.                                           \tag{5}
\]

In particular b and d are both nonzero: if either were zero, the
other would have absolute value strictly below one because a,c>0,
contradicting (5). Thus neither normal is an own-axis direction in
this negative-dot-product case.

If b,d had opposite signs, reflect the vertical coordinate if needed
and write b>0,d<0. The support applications would be the two opposite
U vertices `(1/2,1/2)` and `(-1/2,-1/2)`. The vertical versions of
(3)--(4) would then give, for the same common point z,

\[
\frac12-a\le z_2\le-\frac12+c.                         \tag{6}
\]

All four numbers a,c,|b|,|d| belong to (0,1). The horizontal bounds
preceding (5) and the vertical bounds in (6)
place both coordinates of z strictly between -1/2 and 1/2. Thus z
would lie in the open interior of U. No point of either closed A or
B can lie there: every point of a square is a limit of its interior
points, which would then overlap the open U. This is impossible.

Hence b,d have the same sign. Reflecting vertically, assume b,d>0.
Equation (5) now says b+d>=1. The normal sum therefore satisfies

\[
|n_A+n_B|\ge b+d\ge1.
\]

Since both normals are unit, this is exactly
`2+2 n_A.n_B>=1`, which proves (1). The cases cover every actual
support vertex, owned side, mean and axis endpoint.

## 4. Weighted forces and full-star consequence

For positive weights a,b, (1) gives

\[
\begin{aligned}
|a n_A+b n_B|^2
&\ge a^2+b^2-ab\\
&=\frac{(a+b)^2}{4}+\frac{3(a-b)^2}{4}
\ge\frac{(a+b)^2}{4}.
\end{aligned}
\]

This proves (2), and also retains the displayed exact reserve when
the magnitudes differ.

In particular, if U is unloaded and its **entire** positive neighbor
set is {A,B,C}, and A physically touches B, the complete U translation
shows that the C-force magnitude is at least half the sum of the A-
and B-force magnitudes. This is valid with arbitrary outside degrees
and physical masks. At a higher-degree U, only the combined resultant
of ALL remaining forces is asserted to have that lower bound.

The result strengthens the earlier bound
`1/(1+sqrt(7))` in
`GLOBAL_UNLOADED_MODULE_TERMINAL_CONTACT_CLUSTER_FORCE_COMPENSATION_AND_COMPLETE_THREE_PORT_PATH_REDUCTION_2026_10_31.md`,
Section 6. That source and its complete later conclusions are not
edited or silently reinterpreted by this independent addendum.

## 5. Exact sharp physical equality configuration

Set `s=sqrt(3)/2` and keep U=[-1/2,1/2]^2. Let

\[
\begin{aligned}
A&=(1/2,1/2)+[0,1](s,1/2)+[0,1](-1/2,s),\\
B&=(-1/2,1/2)+[0,1](-s,1/2)+[0,1](1/2,s).
\end{aligned}
\]

Each pair of side directions is orthonormal, so these are unit squares.
Their interiors lie strictly above U's top side; their respective
interiors have positive and negative first coordinate. They therefore
have pairwise disjoint interiors. Each touches U at its displayed
base corner, and they touch each other at `(0,1/2+s)`.

The normals `n_A=(s,1/2)`, `n_B=(-s,1/2)` are genuine U-to-neighbor
support normals. Their dot product is -1/2, and their equal-weight
resultant has norm one. Thus both (1) and (2) attain equality in the
force-free physical setting. This construction is not a minimizing
packing or a claim of a compatible full stress. In particular a
strict singleton convention may exclude these exact normal endpoints;
the unrestricted geometric inequality already covers them.

Every argument above is exact hand geometry. No pose search, angle
sampling, numerical optimization, graph enumeration, Lean or CI is a
premise.

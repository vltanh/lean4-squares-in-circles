# A rational core radius for the eleven-square window

Set

\[
Q_0=491/100,\qquad \rho=27/20,\qquad r_*=41/40.
\]

**Arc theorem.** If a unit square lies in the disk of squared radius at most
`Q_0`, and its center has norm at least `r_*`, its intersection with the
circle of radius `rho` is a connected arc of angular length strictly greater
than `7/10`.

**Unrestricted consequence.** Every eleven-square packing in the certified
window `q<=49013/10000<Q_0` has at least three centers of norm strictly less
than `41/40`. Equivalently it has at most eight centers at or outside that
threshold. No orientation or origin-occupancy assumption is used.

The proof follows the complete side-branch analysis of
[ARC_CORE_RADIUS_REFINEMENT.md](ARC_CORE_RADIUS_REFINEMENT.md), with new
parameters and the exact estimates supplied here.

## 1. The exact arc branches

In a square's own frame choose center coordinates `a>=b>=0`. Put

\[
r=\sqrt{a^2+b^2},\quad x=a-1/2,\ y=b-1/2,\quad
A=a+1/2,\ B=b+1/2.
\]

Containment gives `A^2+B^2<=Q_0`. The center bound
`r^2+r+1/2<=Q_0<89/18` implies `r<5/3`. Since `r>=41/40>1`,

\[
x>0,\qquad x^2+y^2\le r^2-r+1/2<29/18<\rho^2.    \tag{1}
\]

We also have `x<7/6<rho`, `y>=-1/2`. Thus the near corner is strictly
inside the auxiliary disk and the square's circle intersection is restricted
to the right semicircle.

If `A>=rho`, the lower circle angle is `asin(y/rho)`. Its upper angle is
`min(acos(x/rho),asin(B/rho))` when `B<=rho`, and `acos(x/rho)` otherwise.
The near-corner estimate (1) retains negative values of `y` and shows that
the lower primary-side branch cannot cut this interval.

If `A<rho`, then `a<17/20` and

\[
b^2=r^2-a^2>(41/40)^2-(17/20)^2=21/64>1/4.
\]

Hence `y>0` and `B<=A<rho`; there is no negative-angle component. The
complete intersection interval is

\[
\left[
\max\{\arcsin(y/\rho),\arccos(A/\rho)\},\quad
\min\{\arccos(x/\rho),\arcsin(B/\rho)\}
\right].                                                       \tag{2}
\]

Its length is the minimum of four endpoint differences. They correspond to
two parallel-side strips, the two near sides, and the two far sides. The
following bounds show that every applicable difference exceeds `7/10`;
in particular the interval is nonempty and connected. At `A=rho` the two
branch formulas agree, and `B=rho` is included by continuity.

## 2. Parallel-side differences

For `z>=0`, wherever `z+1/2<=rho`,

\[
L_s(z)=\arcsin((z+1/2)/\rho)-\arcsin((z-1/2)/\rho)
\ge2\arcsin(1/(2\rho))>1/\rho=20/27>7/10.         \tag{3}
\]

The first inequality follows by differentiating: `(z+1/2)^2` is at least
`(z-1/2)^2`, so `L_s` is nondecreasing. Continuity includes tangencies.
The primary-strip expression is the same by the identity
`acos(x/rho)-acos(A/rho)=asin(A/rho)-asin(x/rho)`.

## 3. The near-side difference

This difference is

\[
L_n=\pi/2-\arcsin(x/\rho)-\arcsin(y/\rho).
\]

Increasing `a` at fixed `b` until `A^2+B^2=Q_0` can only decrease `L_n`.
On this boundary parameterize `A=sqrt(Q_0) cos(theta)`,
`B=sqrt(Q_0) sin(theta)`, with `theta<=pi/4`. All displayed radicals remain
strictly positive. For `H(z)=(z+1)sqrt(rho^2-z^2)`, differentiation of the
arcsine sum has the sign of `H(x)-H(y)`. Exact expansion gives

\[
H(x)^2-H(y)^2=(x-y)
\left[(x+y)^2-\frac7{80}(x+y)+\frac{147}{200}\right]. \tag{4}
\]

The bracket equals `(x+y-7/160)^2+18767/25600>0`. Thus the arcsine sum
is maximal at `x=y`, and

\[
L_n\ge\pi/2-2\arcsin\frac{\sqrt{491/200}-1}{27/20}. \tag{5}
\]

The argument of this arcsine is less than `21/50`: indeed
`sqrt(491/200)<1567/1000`, since `1567^2=2455489>2455000`, and
`(567/1000)/(27/20)=21/50`.

Here are short exact comparisons proving `21/50<sin(pi/4-7/20)`.
Put `t=7/20` and use the elementary alternating Taylor bounds on `[0,1]`:

\[
\sin t\le t-t^3/6+t^5/120=:S_5,\qquad
1-t^2/2=:C_2\le\cos t\le1-t^2/2+t^4/24=:C_4.
\]

Since `1/sqrt(2)>7071/10000`, direct rational arithmetic gives

\[
\sin(\pi/4-t)=\frac{\cos t-\sin t}{\sqrt2}
>\frac{7071}{10000}(C_2-S_5)
=\frac{21}{50}+\frac{1698553901}{1280000000000}.
\]

All angles used for sine/arcsine monotonicity lie between zero and `pi/2`.
Equation (5) therefore gives `L_n>7/10`.

## 4. The far-side difference

This difference occurs only when `A,B<rho` and is

\[
L_f=\arcsin(A/\rho)+\arcsin(B/\rho)-\pi/2.
\]

At fixed `r>=41/40`, write `a=r cos(theta)`, `b=r sin(theta)`. Increasing
`theta` toward `pi/4` keeps both far coordinates below `rho`. For
`K(z)=z sqrt(rho^2-(z+1/2)^2)`, the derivative of the arcsine sum has
the sign of `K(a)-K(b)`. With `s=a+b`, exact expansion gives

\[
K(a)^2-K(b)^2=(a-b)
\left[(\rho^2-1/4-r^2)s-\frac{s^2+r^2}{2}\right]. \tag{6}
\]

The bracket is at most `(rho^2-1/4-r^2-r)s<0`, because
`rho^2-1/4=629/400<2` and `r>1`. The arcsine sum is therefore minimized
at `a=b`, and then is increasing in `r`. Consequently

\[
L_f\ge2\arcsin\frac{(41/40)/\sqrt2+1/2}{27/20}-\pi/2. \tag{7}
\]

Using the same Taylor bounds and `sqrt(2)>7071/5000`, direct arithmetic gives

\[
\frac{41}{40}+\frac{\sqrt2}{2}
-\frac{27}{20}(\sin(7/20)+\cos(7/20))
>\frac{2639837}{2560000000}>0.
\]

Thus the arcsine argument in (7) exceeds `sin(pi/4+7/20)`, proving
`L_f>7/10`. This completes every branch of (2).

## 5. Counting, endpoint cases, and scope

A square boundary meets the auxiliary circle in finitely many points, so
open and closed square intersections have the same angular measure. The open
square intersections are pairwise disjoint. Nine qualifying squares would
occupy more than `63/10>44/7>2pi`, using `pi<22/7`. Hence there are at most
eight qualifying squares and at least three centers strictly inside `41/40`.

Threshold equalities belong to the outer class. The result also supplies
overlapping closed charts when required, since an assigned core may be
allowed norm `<=41/40` while every assigned ring still has norm `>=41/40`.
This is an unrestricted geometric reduction, not an optimality theorem.
Every original square, orientation and pairwise separation remains present.

# Wrong word 0011011: every core/core pair

## Statement and scope

This is a hand proof of **all core/core entries** of the rational role
table for the orientation word `0011011`. Every physical such pair has
corrected angular cost strictly greater than `91/100`, and hence greater
than the table threshold `17953/20000`.

It does not assert any outer/outer or mixed entry. The proof uses one
elementary angle lemma, one circle-distance comparison, and the ten
explicit scalar rows below. The companion
`verify_wrong_0011011_core_core_hand.py` checks only the fixed rational
comparisons printed here. All terminating decimals are exact rationals.

## 1. Core coordinates, signs, and labels

Put

\[
\rho=\frac1{12},\qquad a_c=\frac7{12},\qquad
d_c=\frac12+\frac{\sqrt2}{24}.
\]

The positive half of a core boundary state consists of the side
`a=a_c`, `0<=b<=1/2`, and the corner arc

\[
a=\frac12+\sqrt{\rho^2-(b-\frac12)^2},
\qquad \frac12\le b\le d_c.
\tag{1}
\]

In its own frame the actual center is `(a,-sigma b)`, where
`sigma=+1` or `-1`, and its local angle is
`alpha=atan(b/a)`. A signed role label is `sigma L_i^sigma(a,b)`.
The independent core labels are:

| Role | Sign | Positive-half polynomial `L` |
|---:|:---:|---|
| 0 | + | `.00125+1.03981 b` |
| 0 | - | `.19911+.63607 b` |
| 1 | either | `.19555+.63132 b` |
| 3 | + | `-.01449+1.04240 b` |
| 3 | - | `.22042-.34492 a+.98439 b-.05334 b^2` |
| 4 | + | `.04970+.94831 b` |
| 4 | - | `.16823+.62312 b` |

The remaining roles are defined by the exact reflection rule

\[
L_{2-i\pmod7}^{\sigma}=L_i^{-\sigma}.
\tag{2}
\]

On edge `i`, let `phi` be the lifted change of frame and `delta` the
positive change of center ray. Then

\[
\delta=\phi+\sigma\alpha-\tau\alpha',\qquad
C_i=\phi+\sigma L_i^\sigma-\tau L_{i+1}^\tau
     =\delta-\psi_i^\sigma+\psi_{i+1}^\tau,
\quad \psi_i^\sigma=\sigma(\alpha-L_i^\sigma).
\tag{3}
\]

The exterior common-point lemma supplies `delta>.76`, and the already
proved frame concentration puts all lifted frames in an interval of
length less than `.7`. On the two consecutive zero-quarter edges,
their center gaps sum to more than `1.52`, while their total frame
change is at most `.7`. Thus `alpha_0-alpha_2>.82>pi/4`: role 0 has
positive sign and role 2 has negative sign. A zero-quarter edge cannot
have sign pair `(-,+)`, since then `delta<=phi<=.7`.

Reflection and reversal take edge `i` to `1-i mod 7` and signs
`(sigma,tau)` to `(-tau,-sigma)`, preserving both `phi` and `C_i`.
Therefore the ten rows in Section 4 are a complete list of distinct
core/core cases. This is a symmetry of the stated role polynomials,
not an assumed interchangeability of two arbitrary labels.

## 2. A core linear-label endpoint lemma

For every core state and every `0<=g<=8/7`,

\[
0\le \alpha-gb\le\frac\pi4-gd_c.
\tag{4}
\]

For the lower bound, concavity of `atan` on `[0,1]` gives
`alpha>=pi b/(4a)>=9b/7`, using `pi>3` and `a<=7/12`.
The last inequality is strict when `b>0`. This is stronger than required.

On the side, write `x=b/a_c`, so `0<=x<=6/7`. Because `d_c-b>0`,
the upper bound is hardest when `g=8/7`. Its difference from equality is

\[
J(x)=\frac\pi4-\arctan x-\frac87d_c+\frac23x.
\]

Here `J'=2/3-1/(1+x^2)`, so the unique minimum is at
`x=1/sqrt(2)`. With `v=3-2sqrt(2)`, the tangent subtraction identity gives

\[
J(1/\sqrt2)=\arctan v-\frac{1+v}{7}
\ge v-\frac{v^3}{3}-\frac{1+v}{7}>\frac1{400}.
\tag{5}
\]

The final comparison follows directly from
`1.41421356237<sqrt(2)<1.41421356238`.

On the corner, write `a=1/2+e`, `b=1/2+d`, where
`e^2+d^2=rho^2` and `0<=d<=e`. Then
`a'=-d/e`, `a''=-rho^2/e^3`, and

\[
\alpha''=
\frac{-b a''(a^2+b^2)-2(a-ba')(aa'+b)}{(a^2+b^2)^2}>0.
\tag{6}
\]

Indeed the first term of the numerator is at least
`(1/2)*12*(1/2)=3`. Also `0<=2(aa'+b)=1-d/e<=1` and
`a-ba'<=a+b<=7/6`, so the subtracted term is at most `7/6`.
Thus `alpha-gb` is convex on the corner and its maximum is at an
endpoint. The side endpoint was just handled; at the diagonal endpoint
it equals `pi/4-gd_c`. This proves (4) on the entire core curve.

For a label `L=c+gb`, (4) immediately yields

\[
-c\le\alpha-L\le\frac\pi4-c-gd_c.
\tag{7}
\]

The one nonaffine label is equally harmless. Put

\[
c_*=.22042-.34492\frac7{12},\qquad
E=.34492(a_c-a)-.05334b^2.
\]

Then `L_3^-=c_*+.98439b+E` and

\[
-.05334d_c^2\le E\le0.
\tag{8}
\]

The upper bound is immediate on the side. On the corner,
`a>=d_c>.55`, so `a_c-a<1/30`, whereas `b^2>=1/4`;
the strict rational comparison `.34492/30<.05334/4` proves it.
The lower bound follows from `a<=a_c`. Therefore

\[
-c_*\le\alpha-L_3^-
\le\frac\pi4-c_*-.98439d_c+.05334d_c^2.
\tag{9}
\]

## 3. Every core/core ray gap exceeds 1.35

Each core center has norm less than `4/5`. On the side this follows from
`(7/12)^2+(1/2)^2<16/25`; on the corner its squared norm is at most

\[
\frac12+\frac{\sqrt2}{12}+\frac1{144}<\frac{16}{25}.
\]

Disjoint unit squares have center distance at least one, since their
open radius-`1/2` incircles are disjoint. If their ray gap were at most
`27/20`, their squared center distance would be at most

\[
\max\left\{\frac{16}{25},
 \frac{32}{25}\left(1-\cos\frac{27}{20}\right)\right\}<1.
\tag{10}
\]

To obtain this bound, maximize the separately convex squared-distance
expression over the two radii in `[0,4/5]`, and use the decrease of
cosine on `[0,27/20]`. The last strict comparison follows from the
alternating cosine lower bound through degree ten. Hence

\[
\delta>\frac{27}{20}=1.35.
\tag{11}
\]

## 4. Complete fixed comparison table

Apply (7)--(9), multiply by the sign in (3), and use (2). For the
listed rows except `(3,+,-)`, the lower bound is exactly
`1.35-upper(psi_i^sigma)+lower(psi_(i+1)^tau)`.
Using

\[
.55892556<d_c<.55892557,\qquad \pi<355/113,
\]

gives the following strictly smaller rational lower bounds:

| Edge | Signs | Strict lower bound for `C_i` |
|---:|:---:|---:|
| 0 | ++ | `.95147` |
| 0 | +- | `.91004` |
| 2 | -+ | `1.36323` |
| 2 | -- | `1.11609` |
| 3 | -- | `1.06188` |
| 3 | -+ | `1.28108` |
| 3 | +- | `1.02374` |
| 3 | ++ | `1.08303` |
| 4 | ++ | `.97610` |
| 4 | +- | `.93867` |

The exceptional row is simpler directly. Here
`phi>=pi/2-.7>.87`, and the two labels in its cost are
`L_3^+=-.01449+1.04240 b` and `L_4^-=.16823+.62312 B`.
Their sum is at least `.15374`, so its cost exceeds `1.02374`.

Each displayed bound exceeds `.91`, which in turn exceeds
`17953/20000`. Reflection and reversal recover every unlisted edge and
sign case. All core/core entries are therefore proved, with strict
reserve. They have no equality cases at the wrong-word threshold.

# Wrong word 0011011: every same-sign mixed zero-quarter case

## Statement and scope

This is a hand proof of all **32 permitted same-sign mixed core/outer
zero-quarter cases** in the rational role table for `0011011`, counting
the four possible separating axes separately. Every case has corrected
angular cost strictly greater than

\[
\gamma=\frac{17953}{20000}=.89765.
\]

The proof treats the complete allowed frame-angle interval. It uses
endpoint reduction, circle support, and one contact curve with eight
fixed curvature intervals. The companion
`verify_wrong_0011011_same_sign_mixed_zero_hand.py` checks the 126 fixed
strict comparisons displayed or specified below. Terminating decimals
throughout this note denote exact rationals. Opposite-sign mixed cases,
outer/outer cases, and quarter-one cases remain separate statements.

## 1. Coordinates, role labels, and the exact case list

Put

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad
 a_c=\frac7{12},\quad d_c=\frac12+\frac{\sqrt2}{24}.
\tag{1}
\]

An outer state on its positive half is

\[
 a=a(b)=\sqrt{Q-(b+\frac12)^2}-\frac12,
 \qquad 0\le b\le d.
\tag{2}
\]

A core state consists of the side `a=a_c`, `0<=b<=1/2`, and the corner

\[
 a=\frac12+\sqrt{\frac1{144}-(b-\frac12)^2},
 \qquad \frac12\le b\le d_c.
\tag{3}
\]

The actual center in its own frame is `(a,-sigma b)`, with
`sigma` equal to `+1` or `-1`. If the target is `(A,-tau B)` and its
frame is ahead by `phi`, then the center-ray gap and corrected cost are

\[
 \delta=\phi+\sigma\arctan(b/a)-\tau\arctan(B/A),
 \qquad C=\phi+\sigma L_i^\sigma-\tau L_{i+1}^\tau.
\tag{4}
\]

We use the already established geometric premises `delta>.76` and a
common lifted frame interval of length less than `.7`. The quarter word
is `0011011`, so its zero edges are 0, 1, and 4. The two consecutive
zero edges give `alpha_0-alpha_2>.82>pi/4`, where the alphas are signed.
Consequently role 0 has positive sign and role 2 has negative sign.
Also a zero edge cannot have signs `(-,+)`, since then `delta<=phi<=.7`.
Thus the same-sign cases are exactly

\[
 (0,+,+),\quad(1,-,-),\quad(4,+,+),\quad(4,-,-).
\tag{5}
\]

Reflection and reversal take edge `i` to `1-i mod 7` and signs
`(sigma,tau)` to `(-tau,-sigma)`, preserving both `phi` and `C`.
The exact label identity is
`L_{2-i mod 7}^sigma=L_i^{-sigma}`. It suffices, therefore, to prove
edges 0 and 4 with signs `(+,+)`, in both radial orders. Their needed
outer polynomials are

| Name | Positive-half outer label |
|---|---|
| `P` | `.02478+.93015 b+.02363 b^2-.11055 a b` |
| `J` | `-.00026 a+.83194 b-.11864 b^2+.17627 a b` |
| `L` | `.03965+3.85510 b-1.49748 b^2-1.89442 a b` |
| `K` | `-.02112 a+.29090 b+.44642 a b` |

The corresponding core labels are affine in `b`:

| Edge | Core source, outer target | Outer source, core target |
|---:|---|---|
| 0 | `.00125+1.03981 b`, target `J` | source `P`, `.19555+.63132 B` |
| 4 | `.04970+.94831 b`, target `K` | source `L`, `.16823+.62312 B` |

These are precisely the entries of `wrong_0011011_labels.json`.
There are four classes in (5), two radial orders, and four axes, hence
the stated 32 cases.

For reference, write

\[
 W=\frac{1+|\cos\phi|+|\sin\phi|}{2}.
\]

After the earlier cap and angular exclusions, the retained signed
separating projections are

\[
\begin{array}{ll}
\text{source }+f:&\sigma b+A\sin\phi-\tau B\cos\phi,\\
\text{target }+e:&-a\cos\phi+\sigma b\sin\phi+A,\\
\text{target }+f:&a\sin\phi+\sigma b\cos\phi-\tau B,\\
\text{source }-e:&a-A\cos\phi-\tau B\sin\phi.
\end{array}
\tag{6}
\]

At least one of (6) must be at least `W`. Every surviving axis is
treated below; no nearest-contact or generic-position premise is used.

## 2. The frame angle is positive; reduction to four families

The elementary enclosures needed repeatedly are

\[
 R<1.979,\quad .899<d<.900,\quad
 .5589<d_c<.559,\quad a_0<1.415.
\tag{7}
\]

For signs `(+,+)`, (4) implies
`phi>.76-pi/4>-.026`. If `phi<=0`, both transverse projections in
(6) are less than `d<1`. Each primary projection is at most

\[
 1.415-.5589\cos(.026)+.9\sin(.026)<1\le W.
\tag{8}
\]

Hence every feasible same-sign representative has `0<phi<=.7`.
Write `s=sin(phi)`, `c=cos(phi)`; then `c>s>0` and
`W=(1+c+s)/2`.

A core source cannot use its negative primary axis, even if the target
sign is negative: its projection is at most
`a_c-A(c-s)<1`. By reflected reversal this also removes the target
primary axis when an outer source has a positive core target.
A positive core source cannot use the target transverse axis, since
its center norm is less than `.8` and subtracting `B` only decreases
that projection.

For an outer positive source and core positive target, the source
primary margin is bounded above by

\[
 a_0-\frac12-(d_c+\frac12)c-\frac12s<0.
\tag{9}
\]

Indeed `(d_c+1/2)c+s/2` is concave on `[0,.7]`, and its two endpoint
values exceed `a_0-1/2`. These exclusions leave the following four
families, where the last two are reflected reversals of target-owned
axes of the first two radial orders:

| Family | Kind and signs | Axis | Outer/core data |
|---:|---|---|---|
| I | `C+ -> O+` | source `+f` | `(F,c0,g)=(J,.00125,1.03981)` or `(K,.04970,.94831)` |
| II | `O+ -> C+` | source `+f` | `(F,c0,g)=(P,.19555,.63132)` or `(L,.16823,.62312)` |
| III | `C- -> O-` | source `+f` | the same `P,L` data as II |
| IV | `O- -> C-` | source `-e` | the same `J,K` data as I |

This table is an exact cover of the remaining axes in (6).

## 3. Scalar facts about the four outer labels

Put `u=a+1/2`, `v=b+1/2`, and `r=v/u`. For

\[
 F(b)=c_0+p a+q b+r_2b^2+s_2ab
\]

direct differentiation gives

\[
\begin{aligned}
 F'&=-p r+q+2r_2b+s_2(a-br),\\
 F''&=2r_2-2s_2r-(p+s_2b)Q/u^3,\\
 F'''&=-3Q\{s_2Q+(p-s_2/2)v\}/u^5.
\end{aligned}
\tag{10}
\]

The ratio `r` is increasing. For `J,K`, the first two derivatives
satisfy

\[
 F''<0,\qquad F'(d)>0,\qquad F'(0)<1.1,\qquad F(0)<0.
\tag{11}
\]

For example a direct upper bound for `F''` is

\[
 2r_2-2s_2\frac{1/2}{a_0+1/2}
       +|p|\frac{Q}{(d+1/2)^3}<0.
\]

It follows that both labels are increasing and strictly concave, and

\[
 J(b)\le1.1b,\qquad K(b)\le1.1b.
\tag{12}
\]

For `P`, (10) gives `P''>0`, `P'''>0`, and the endpoint comparisons

\[
 .773<P'(0)\le P'(b)\le P'(d)<1.
\tag{13}
\]

For `L`, write `D=L'`. Formula (10), or differentiation of `a(b)`, gives

\[
 D''=1.89442\left(\frac{3Q}{u^3}
                  +\frac{3bQv}{u^5}\right)
 >\frac{3(1.8)(3.9)}{2^3}>2.
\tag{14}
\]

The fixed point bounds

\[
 D(.5)>.6248,\qquad -.0311<D'(.5)<0,\qquad D'(.6)>.5
\]

therefore imply, by completion of a square,

\[
 D(b)>.6248-\frac{.0311^2}{4}>.6245.
\tag{15}
\]

On `b>=.624`, both `L'` and `L''` are positive and increasing.
In particular

\[
 P'>.63132,\quad L'>.62312,\quad
 P(b)\ge P(0)+.7b,\quad L(b)\ge L(0)+.6b.
\tag{16}
\]

The formulas extend slightly beyond `b=d`; when such an extension is
used in an endpoint curvature bound below, it is an analytic enclosure
of the same explicitly defined radical function, not an extra state.

## 4. Family I: positive core source, positive outer target

The cost and nonnegative separating margin are

\[
 C=\phi+c_0+gb-F(B),\qquad
 M=b+A s-Bc-W\ge0.
\tag{17}
\]

Feasibility forces `phi>.44`. In fact

\[
 M\le d_c-\frac12-\frac12c+(a_0-\frac12)s,
\]

whose right-hand side is increasing and is negative at `.44`.
Subtract `gM` from the cost and use (12). With `h=1.1`, the unrestricted
circle support inequality for `(A+1/2,B+1/2)` gives

\[
 C\ge E(\phi):=
 \phi+c_0+\frac g2+\frac h2+g\sin\phi-RN(\phi),
 \quad N^2=g^2+h^2-2gh\cos\phi.
\tag{18}
\]

This lower bound holds for every target point on the actual outer arc.
The identity

\[
 N''+\frac14N=\frac{(g^2-h^2)^2}{4N^3}>0
\tag{19}
\]

and `N(.7)<.75` show that

\[
 E''<-g\sin(.44)+R(.75)/4
       <-.94831(.425)+1.979(.75)/4<0.
\]

Thus `E` is concave on `[.44,.7]`. Its four required endpoint
comparisons, two for each data row, are

| Target label | `E(.44)` | `E(.7)` |
|---|---:|---:|
| `J` | `>.96` | `>.96` |
| `K` | `>.96` | `>.96` |

This proves all of family I with a strict surplus.

## 5. Family II: positive outer source, positive core target

Here

\[
 C=\phi+F(b)-c_0-gB,\qquad M=b+A s-Bc-W\ge0.
\tag{20}
\]

Feasibility forces `phi>.49`, since

\[
 M\le d-\frac12-\frac12c+\frac1{12}s
\]

is increasing and is negative at `.49`. Subtract `M`, use
`c>cos(.7)>.764>g`, `A<=a_c`, and then (16). With `m=.7` for `P`
and `m=.6` for `L`,

\[
 C\ge\phi+\frac12+\frac12\cos\phi-\frac1{12}\sin\phi
          -c_0+F(0)-(1-m)d.
\tag{21}
\]

The derivative of this scalar expression is positive. At `.49` the
lower bounds are `>.95` for `P` and `>.903` for `L`.

## 6. Family III: negative core source, negative outer target

We have

\[
 C=\phi-c_0-gb+F(B),\qquad
 M=-b+A s+Bc-W\ge0.
\tag{22}
\]

The function `A(B)s+B c` is strictly increasing, since its derivative
is `c-rs>0`. Hence feasibility requires

\[
 (d-\tfrac12)(\sin\phi+\cos\phi)\ge\tfrac12.
\tag{23}
\]

Let `phi_0` be the unique equality point. Direct endpoint comparisons
give `.3024<phi_0<.7`.

At fixed `phi`, increasing the source coordinate `b` decreases the
cost. Relaxing its core upper bound gives the valid lower expression
obtained by setting

\[
 b=A\sin\phi+B\cos\phi-W\ge0.
\]

Its derivative with respect to the outer coordinate `B` is
`F'(B)-g(c-rs)>0`, by (16). Therefore the minimum occurs at the first
feasible outer coordinate, where `b=0`. This endpoint really is on the
core side; the preceding relaxation only supplied a lower bound.

The remaining outer contact has an explicit parameterization:

\[
\begin{gathered}
 m=\sin\phi+\cos\phi,\quad Z=\tfrac12+m,\quad
 Y=\sqrt{Q-Z^2},\\
 U=Z\sin\phi+Y\cos\phi,\quad
 V=Z\cos\phi-Y\sin\phi,\quad B=V-\tfrac12,\\
 f=1-\frac{\cos\phi-\sin\phi}{Y},\qquad
 f'=\frac{m(Q-9/4)-m^2/2-1}{Y^3}.
\end{gathered}
\tag{24}
\]

Here `U=A+1/2`, `V=B+1/2`, and

\[
 U'=Vf,\qquad V'=-Uf.
\tag{25}
\]

On the slightly enlarged interval `[.3024,.7]`, the fixed endpoint
comparisons give

\[
 .624<B<.900,\qquad f>0,\qquad f'>0,\qquad m<Q-9/4.
\tag{26}
\]

The numerator of `f'` increases with `m`, and `Y` decreases, so `f'`
is increasing. Thus `U,f,f'` increase and `V,B` decrease.
For

\[
 H(\phi)=\phi-c_0+F(B(\phi)),
\]

the exact curvature formula is

\[
 H''=F''(B)(Uf)^2-F'(B)(Vf^2+Uf').
\tag{27}
\]

By (13)--(16), `F'` and `F''` are positive and increasing as functions
of `B` throughout (26). On any fixed interval `[l,h]`, a valid upper
bound for (27) is consequently

\[
 F''(B(l))(U(h)f(h))^2
 -F'(B(h))\{V(h)f(l)^2+U(l)f'(l)\}.
\tag{28}
\]

Substitution in (28) gives the following strict rational bounds. The
intervals are declared here in advance and cover the entire curve.

| Interval | Upper bound for `P` | Upper bound for `L` |
|---|---:|---:|
| `[.3024,.35]` | `-.55` | `-.11` |
| `[.35,.4]` | `-.69` | `-.16` |
| `[.4,.45]` | `-.89` | `-.23` |
| `[.45,.5]` | `-1.15` | `-.31` |
| `[.5,.55]` | `-1.48` | `-.40` |
| `[.55,.6]` | `-1.90` | `-.49` |
| `[.6,.65]` | `-2.41` | `-.62` |
| `[.65,.7]` | `-2.96` | `-.86` |

Hence `H` is strictly concave. At the initial endpoint `B=d`, and

\[
 H(\phi_0)>.3024+F(d)-c_0>.89773
\]

for both rows. At the other endpoint `H(.7)>1.04` for both rows.
This proves the whole third family.

## 7. Family IV: negative outer source, negative core target

Now

\[
 C=\phi-F(b)+c_0+gB,\qquad
 M=a-Ac+Bs-W\ge0,
\tag{29}
\]

with `F=J` or `K`. Feasibility forces `phi>.45`, because

\[
 M\le a_0-\frac12-(d_c+\frac12)c+(d_c-\frac12)s
\]

is increasing and is negative at `.45`.
For fixed core point and frame angle, increasing `b` reduces both
`a` and the cost. Thus a minimum occurs at the true contact

\[
 a=W+Ac-Bs,\qquad b=\sqrt{Q-(a+\frac12)^2}-\frac12.
\tag{30}
\]

The other outer endpoint `b=d` is infeasible: its required primary
coordinate in (30) exceeds `W>=1>d`. We analyze separately the core
side and corner. This separation prevents any mixing of the two core
arcs in a support bound.

### 7.1. The core side

On the core side `A=a_c`, `B<=1/2`, contact feasibility gives
`phi>.56`: the maximal margin at `B=1/2` is
`a_0-1/2-(13/12)cos(phi)`, which is negative at `.56`.
All side contacts satisfy

\[
 b\le\sqrt{Q-[1+(13/12)\cos(.7)]^2}-\frac12<.257.
\tag{31}
\]

Write

\[
 T_F(b)=F'(b)\frac{a(b)+1/2}{b+1/2}.
\tag{32}
\]

It is positive and strictly decreasing, by (11). The fixed point
comparisons give `T_J(.257)>2` and `T_K(.257)>2`.
Along the contact, differentiation in `B` gives

\[
 C_B=g-T_F(b)\sin\phi
       <1.03981-2(.531)<0.
\tag{33}
\]

Thus the side minimum lies at `B=1/2`. On that boundary the derivative
in `phi` is

\[
 C_\phi=1-\frac{13}{12}T_F(b)\sin\phi
       <1-\frac{13}{12}2(.531)<0.
\tag{34}
\]

The minimum is at `.7`. The corresponding costs are strictly greater
than `.956` for `J` and `1.025` for `K`.

### 7.2. The entire core corner is concave after contact reduction

On the core corner put

\[
 t=\frac{B-1/2}{A-1/2}\in[0,1],\quad
 \kappa=-A''=12(1+t^2)^{3/2},\quad w=t c+s.
\]

With `u=a+1/2`, `v=b+1/2`, (30) gives

\[
 b_B=\frac uvw,\qquad
 b_{BB}=\frac uv\kappa c-\frac Q{v^3}w^2.
\]

Therefore

\[
 \frac{\frac{d^2}{dB^2}F(b(B))}{F'(b)b_B^2}
 =\frac{F''}{F'}+\frac vu\frac{\kappa c}{w^2}
                  -\frac Q{u^2v}.
\tag{35}
\]

Here is a uniform hand bound for its geometric factor:

\[
 \frac{\kappa c}{w^2}>10\qquad(0\le t\le1,\ 0<\phi\le.7).
\tag{36}
\]

For fixed `t`, the left side decreases with `phi`, since
`w'=c-ts>0`. At `.7`, use `.764<c<.765` and `s<.645`.
If `t<=.4`, it suffices that
`12(.764)>10(.951)^2`. If `.4<=t<=.5`, it suffices that
`12(.764)(1.16)(1.07)>10(1.0275)^2`, using `sqrt(1.16)>1.07`.
If `t>=.5`, Cauchy's inequality gives `w^2<=1+t^2`, so it suffices
that `12(.764)(1.11)>10`, using `sqrt(1.25)>1.11`.
These are the three fixed comparisons proving (36).

The largest possible contact value occurs at `B=A=d_c`, `phi=.7`;
direct substitution gives `b<.381`. Define

\[
 K_0(v)=\frac{10v}{\sqrt{Q-v^2}}
              -\frac Q{v(Q-v^2)}.
\tag{37}
\]

It is increasing for `.5<=v<=.881`, as follows by differentiation
and `3v^2<Q`. The fixed comparisons are

\[
 K_0(.5)>.4,\qquad K_0(.6)>1.2.
\tag{38}
\]

For each `F=J,K`, direct use of (10) on the two indicated rectangles
gives

\[
\begin{array}{ll}
F''+.4F'>0,&0\le b\le.1,\\
F''+1.2F'>0,&.1\le b\le.381.
\end{array}
\tag{39}
\]

For clarity these are four ordinary interval comparisons of the explicit
formula (10); they use endpoint bounds for `b`, `u`, and `v`, and have
strict positive reserves. Equations (35)--(39) prove that `F(b(B))`
is strictly convex on every feasible corner contact. Consequently the
cost `phi+c0+gB-F(b(B))` is strictly concave in `B`.

The feasible core coordinates form a terminal interval, since the
right side of the first equation in (30) decreases with `B`.
Its endpoint alternatives are therefore: the side junction `B=1/2`,
the diagonal `B=d_c`, or its first feasible point, where `b=0`.
The side junction has already been treated. At `b=0`,

\[
 C>.45+c_0+g/2-F(0)>.97
\tag{40}
\]

for both labels. Only the core diagonal remains.

### 7.3. The core diagonal

When `A=B=d_c`, put

\[
 u=1+(d_c+\tfrac12)\cos\phi+(\tfrac12-d_c)\sin\phi.
\]

Let

\[
 w_0=(d_c+\tfrac12)\sin\phi+(d_c-\tfrac12)\cos\phi
 =\sqrt{(d_c+\tfrac12)^2+(d_c-\tfrac12)^2-(u-1)^2}.
\tag{41}
\]

The positive square root is correct because `phi>.45`. The derivative
of the cost is

\[
 C_\phi=1-T_F(b)w_0(b).
\tag{42}
\]

The function `w_0` increases with `b` on `[0,.381]`, since `u>1`.
The following six point bounds hold, the first two rows for both `J,K`:

| Quantity | Strict lower bound |
|---|---:|
| `T_F(.25)` | `2.07` |
| `T_F(.381)` | `1.577` |
| `w_0(0)` | `.536` |
| `w_0(.25)` | `.658` |

For `b<=.25` the product in (42) exceeds `2.07(.536)>1`;
for `b>=.25` it exceeds `1.577(.658)>1`. Hence the cost is strictly
decreasing in `phi` on the entire feasible diagonal boundary.
At `phi=.7`, the exact endpoint comparisons give

| Label | Cost at the diagonal endpoint |
|---|---:|
| `J` | `>.89778` |
| `K` | `>.9796` |

This completes family IV and therefore all cases in the theorem.

## 8. Arithmetic reproducibility and strictness

Every strict lower bound used for a terminal cost exceeds `.89765`.
The smallest displayed lower bound is `.89773` in family III.
Thus none of these same-sign mixed cases can carry equality at the
role-table threshold.

The companion checker uses only exact rational interval arithmetic.
Square-root endpoints are rational multiples of `10^-14` and are
checked by integer squaring. Sines are enclosed by their alternating
Taylor sums through degrees 11 and 13, and cosines through degrees 14
and 12. All evaluation arguments lie in `[0,.7]`, so the alternating
remainders have the stated directions. The only nontrivial variable
enclosures are the eight explicitly declared curvature intervals in
(28) and the two derivative rectangles in (39); all monotonicity
needed to justify their endpoint substitutions was proved above.

The script reports **126 strict comparisons, PASS**, and writes
`wrong_0011011_same_sign_mixed_zero_hand_arithmetic.json`. Its data are
the rational constants and formulas in this note. It makes no numerical
minimization, adaptive subdivision, or unproved first-contact choice.

# A width-dependent clearance between the original D and G squares

November 2, 2026. Complete hand proof; the separate weak-outer hand agent
independently checked the algebra and both sign branches. This is a reusable
input to the original-nine large-gap proof, not a whole-mask closure.

Work in the original `001/00` domain with `v=y_D-y_C>=7/30`, after vertical
reflection. The complete accepted endpoint-order theorem gives `y_G>y_D`.
The following derivation supplies every scalar input explicitly.

Write `g_S=1/(4h_S)` for the original contained aligned-square halfwidth;
then `h_S+g_S>=1`. The original C,D cone link implies
`x_D-x_C>=g_C+g_D`, and containment gives `x_D+h_D<=sqrt(Q)`. Therefore

\[
 \begin{split}
 x_C-h_C
 &\le x_D-(h_C+g_C)-g_D\\
 &\le\sqrt Q-(h_C+g_C)-(h_D+g_D)\\
 &\le\sqrt Q-2<5/64.                                \tag{1}
 \end{split}
\]

The original left physical endpoint cap for A,E is
`46(-x_A-h_A)+(27/2)(-x_E-h_E)<=211/4`. The first two actual main links
give `x_C-x_A>=h_A+2h_B+h_C`, and the two actual short links give
`x_G-x_E>=h_E+2h_F+h_G`. Since `h_B,h_F>=1/2`, substitution yields

\[
 46(x_C-h_C)+\frac{27}{2}(x_G-h_G)\ge
 46+\frac{27}{2}-\frac{211}{4}=\frac{27}{4}.          \tag{2}
\]

Combining (1) and (2) proves

\[
 x_G-h_G>
 \frac{27/4-46(5/64)}{27/2}=\frac{101}{432}.          \tag{3}
\]

Also `x_A>-91/60` and the first two actual main links give
`x_C>h_C-1/60`. Thus the original C,D inset comparison implies

\[
 x_D>h_C+g_C+g_D-1/60
       \ge59/60+1/(2\sqrt2)>4/3.                     \tag{4}
\]

The final strict inequality follows from `1/8-(7/20)^2=1/400>0`.
Equations (3)-(4), original corner containment, and the universal
center-radius bound now give the required inputs

\[
 x_G-h_G>101/432,\qquad x_D>4/3,
 \qquad x_D+h_D\le\sqrt Q<133/64,
 \qquad x_G<91/60.
\]

Set `S=h_D+h_G` and `K=3187/1728`. Each physical halfwidth lies between
`1/2` and `1/sqrt(2)`, so `1<=S<=sqrt(2)<10/7`. The forward horizontal
gap satisfies

\[
 x_D-x_G<\frac{133}{64}-\frac{101}{432}-S=K-S.
\]

The reverse horizontal gap satisfies `x_G-x_D<11/60`. It too is smaller
than `K-S`, since

\[
 K-10/7-11/60=14057/60480>0.
\]

Consequently `|x_G-x_D|<K-S`, where `0<K-S<1` throughout the interval.
The radius-1/2 open disks centered at D and G lie in the interiors of their
original squares. Their disjointness therefore gives center distance at
least one. Using the accepted positive height order,

\[
 y_G-y_D>\sqrt{1-(K-S)^2}.
\]

Define `L(S)=8/15+(7/8)(S-1)=7S/8-41/120`. It is positive on
`1<=S<=10/7`. The polynomial

\[
 P(S)=1-(K-S)^2-L(S)^2
\]

has leading coefficient `-113/64`, hence is concave. Its two endpoint
values are the strictly positive rational numbers

\[
 P(1)=\frac{198911}{74649600},\qquad
 P(10/7)=\frac{7595279}{3657830400}.
\]

Thus `P(S)>0` throughout the full closed interval. Taking nonnegative
square roots proves the complete original-pair inequality

\[
 \boxed{\quad y_G-y_D>
 \frac8{15}+\frac78\bigl(h_D+h_G-1\bigr).\quad}
\]

The same original D and G widths appear in this bound and every other
constraint. The argument preserves both chiralities and every physical
separator owner. No numerical optimization or interval search is a premise.

For linear certificate replay, a valid closed relaxation is

\[
 y_D-y_G+\frac78(h_D+h_G)\le\frac{41}{120}.
\]

The companion `weak_outer_numeric_dg_clearance_arithmetic.py` checks every
constant and polynomial endpoint using exact fractions. No Lean, Lake,
or CI is used.

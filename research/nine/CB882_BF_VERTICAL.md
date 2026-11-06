# The original B/F insets separate vertically

This chapter proves a whole-parent reduction for the original Cb882
packing. It does not choose the upper or lower B/F order. All squares
retain their physical frames and all original pairwise disjointness.
Write Q=1105/256, rho=91/60, h_P for a physical projection halfwidth,
and g_P=1/(4h_P) for the halfwidth of its contained axis-aligned square.

## 1. The endpoint-span version of the outsider strip

Let P,Z be two original physical unit squares in the Q-disk with

\[
                 x_Z-x_P\ge h_P+h_Z+2.                    \tag{1}
\]

Every additional physical unit square T in that disk, interior-disjoint
from P and Z, then satisfies

\[
                         |x_T|<13/12.                    \tag{2}
\]

The existing [physical outsider-strip proof](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md)
applies under (1). Here are the endpoint bounds needed to justify
this slightly more general statement without assuming intermediate
members of an actual four-chain.

The universal center bound gives |c_P|,|c_Z|<rho. Since h_P,h_Z>=1/2,
(1) gives x_Z-x_P>=3. Consequently

\[
 x_P<-89/60,\qquad x_Z>89/60,\qquad
 h_P,h_Z<8/15.                                           \tag{3}
\]

For example h_P<2rho-5/2=8/15. Equation (1) also gives

\[
                    |x_P|-h_P>59/60,
                    \qquad x_Z-h_Z>59/60.                \tag{4}
\]

For either endpoint put X=|x|, Y=|y| and
k=sqrt(1/2-h^2). From X>89/60 and X^2+Y^2<rho^2 we have
Y^2<1/10 and Y<X. An actual outward-quadrant corner has offsets (h,k) or (k,h).
Since X>Y, its squared norm is at least the latter expression, so

\[
                        (X+k)^2+(Y+h)^2\le Q.
\]

On 1/2<=h<=8/15, concavity gives h+k>149/150. Thus (4) gives
X+k>593/300, and Y>=1/5 would imply

\[
 Q>(593/300)^2+(7/10)^2
   =Q+116359/1440000,
\]

an impossibility. This proves Y<1/5 at both endpoints.

For completeness, set S=|y_P|+|y_Z| and U=h_P+h_Z-1.
The endpoint span (1), their two corner inequalities, and the triangle
inequality give exactly

\[
 4Q\ge(2+h_P+k_P+h_Z+k_Z)^2+(S+h_P+h_Z)^2.
\]

Thus Section 2 of the cited proof, which uses no intermediate square,
gives

\[
 S+(37/50)U\le1/8,
 \qquad g_P-|y_P|,\ g_Z-|y_Z|\ge4421/12000>221/600.       \tag{5}
\]

Sections 3--5 of that proof use only (3), (5), physical disjointness
from the appropriate endpoint, and disk containment. They exclude
x_T>=13/12 using endpoint Z and x_T<=-13/12 using endpoint P,
which proves (2). In particular no intermediate actual projection link
is an additional hypothesis of the endpoint-span statement.

## 2. Both horizontal B/F alternatives are impossible

In the whole Cb882 parent, AB, BC, EF and FG are actual positive
horizontal projection links. The whole-parent localization gives

\[
                         x_D>4/3,
                         \qquad x_A<-23/16.              \tag{6}
\]

The elementary inequality

\[
                         h+g=h+\frac1{4h}\ge1            \tag{7}
\]

follows from (2h-1)^2>=0.

Suppose first that x_F-x_B>=g_B+g_F. Summing this inequality with
the actual AB and FG links, and then using (7), gives

\[
\begin{aligned}
 x_G-x_A
 &\ge h_A+h_B+g_B+g_F+h_F+h_G\\
 &\ge h_A+h_G+2.
\end{aligned}
\]

Apply Section 1 with endpoints A,G and outsider D. It gives
|x_D|<13/12, contrary to (6).

If instead x_B-x_F>=g_B+g_F, summing with the actual EF and BC
links gives

\[
\begin{aligned}
 x_C-x_E
 &\ge h_E+h_F+g_F+g_B+h_B+h_C\\
 &\ge h_E+h_C+2.
\end{aligned}
\]

Section 1 with endpoints E,C and outsider A now contradicts (6).
Both horizontal alternatives are therefore excluded.

The contained axis-aligned B/F squares have disjoint open interiors,
so one of their four coordinate separating inequalities must hold.
Only the two vertical alternatives remain:

\[
 \boxed{\ y_F-y_B\ge g_B+g_F
       \quad\text{or}\quad
          y_B-y_F\ge g_B+g_F.\ }                         \tag{8}
\]

This complete height split is valid before either A/E order is chosen.
The proof uses originals A--G and requires no property of H or I.

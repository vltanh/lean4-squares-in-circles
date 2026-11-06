# C-slant for nonpositive D: complete secondary-axis table, conditional on G-order

This chapter proves the upper-G part of nonpositive-D C-slant under
the explicit hypothesis y_G>y_D. It uses the physical pair cap from
[the foundation](FOUNDATION.md), the hand primary-axis reduction in
[the preceding chapter](00100_C_SLANT_PRIMARY_AXES.md), and the precise
G-order input y_G>y_D. Its complete arithmetic tables are plain text:

* [21 root cases](tables/c-slant-secondary-roots.tsv);
* [all 4,204 weighted rows and their complete angle subdivisions](tables/c-slant-secondary.tsv).

The tables specify positive integer multipliers and a rational inequality
for every leaf. The rules below define every coefficient. They require
neither a numerical solver nor an external encoded certificate to read.
The [lower-G complement](00100_C_SLANT_LOWER_COMPLEMENT.md) proves that
every hypothetical contrary-domain witness has y_G>y_D. Thus the
assembled nonpositive-D C-slant proof requires no archived G-order
result. This chapter keeps the height-order hypothesis explicit so
that its own domain and the complementary chapter remain distinct.

No whole original, whole mask, unrestricted lower bound, positive-D
C-slant theorem or global equality classification is established here.

## 1. Exact original caller

Retain all nine independently framed physical originals of `001/00`.
All 36 original pairs have disjoint open interiors; every original
corner lies in the closed Q-disk, where

\[
 Q=1105/256,\quad r=\sqrt Q<133/64=:r_0,
 \qquad \rho=91/60.
\]

The links AB, BC, EF, FG are actual horizontal projection links.
The link CD is a strict weak horizontal cone link. Write

\[
 d=x_D-x_C\ge v=y_D-y_C\ge2/3,\quad d<h_C+h_D.
\]

D has nonpositive canonical tilt. For contradiction assume

\[
                  y_C+(7/8)x_C\ge-7/32.                        \tag{1}
\]

The additional input in this chapter is precisely

\[
                            y_G>y_D.                          \tag{2}
\]

It is the explicit input for this upper-G component. Its use in the
complete proof is justified by the lower-G chapter, without assuming
the conclusion being proved.
No C-slant result is imported. The intended conclusion, under (2), is
y_C+(7/8)x_C<-7/32.

## 2. Earlier necessary inequalities, with their hand derivations

Put g_S=1/(4h_S) for the halfwidth of S's actual contained aligned
inset. The foundation gives h_S+g_S>=1, g_S>=1/(2sqrt(2)),
|c_S|<rho and physical center distances at least one.
The preceding primary-axis chapter supplies the cap load and transfer:

\[
\begin{gathered}
 x_C>h_C-1/60,\qquad d\ge g_C+g_D,\qquad d\le1-h_C+h_D,\\
 46(x_C-h_C)+(27/2)(x_G-h_G)\ge27/4,\\
 46(x_D-h_D)+(27/2)(x_G-h_G)\le211/4.             \tag{3}
\end{gathered}
\]

The CD inset comparison and x_D+h_D<=r give
x_C+g_C<=r-1, and hence x_C-h_C<=r-2<5/64.
Substitution into the load gives x_G-h_G>101/432.
Also x_D>h_C+g_C+g_D-1/60>=59/60+g_D>4/3.

For completeness, the two horizontal D/G bounds are

\[
          x_D-x_G<1459/1728,\qquad x_G-x_D<11/60.              \tag{4}
\]

For the first, set a=46,b=27/2,T=211/4 and Delta=x_D-x_G.
The load in (3), x_C-h_C<=x_D-1-g_D and h_G>=1/2 imply
b Delta<=(a+b)(x_D-1)-a g_D. The function
(a+b)h+a/(4h) increases for h>=1/2 and equals T at 1/2.
Using x_D<=r-h_D gives
b Delta< (a+b)(133/64-1)-T=1459/128, as required.
The reverse bound uses x_G<rho and x_D>4/3.

Set S=h_D+h_G and K=3187/1728. The original D containment and
x_G-h_G>101/432 give x_D-x_G<K-S. Since K<2 and
g_D+g_G>=2-S, the two D/G inset horizontal projections overlap.
Their interiors are disjoint, so (2) fixes the vertical separation:

\[
                          y_G-y_D\ge g_D+g_G.                 \tag{5}
\]

The following additional height bound is also a hand consequence:

\[
             y_G-y_D>7(h_D+h_G)/8-41/120.                     \tag{6}
\]

Indeed 1<=S<=sqrt(2)<10/7 and both horizontal gaps in (4) are
less than K-S; for the reverse gap use
K-10/7-11/60=14057/60480>0. The original incircles give
y_G-y_D>sqrt(1-(K-S)^2). The concave quadratic

\[
 1-(K-S)^2-(7S/8-41/120)^2
\]

has positive endpoint values 198911/74649600 and
7595279/3657830400 at S=1 and S=10/7 respectively.
The affine expression is positive, so taking square roots proves (6).

## 3. Two uniform reductions before the table

First, in the contrary region (1),

\[
 x_D+y_D>\frac16+\frac{43}{96}+\frac78\frac{707}{1000}.        \tag{7}
\]

To prove this, v>=2/3 and (1) give
y_D>=43/96-(7/8)x_C. Also d>=g_C+g_D>707/1000 and
x_D>4/3. Substitute x_C<x_D-707/1000.
The bound 1/sqrt(2)>707/1000 is 707^2<500000.

**G is strictly left of D.** If x_G>=x_D, the original D/G
incircles and (2) give
(x_G-x_D)+(y_G-y_D)>=1. Write the canonical absolute components
of G as a>=b>=0. The support of G in direction (1,1) is a,
with a>=1/sqrt(2)>707/1000. From (7),

\[
\begin{aligned}
 x_G+y_G+a
 &>1+\frac16+\frac{43}{96}+\frac{15}{8}\frac{707}{1000}\\
 &=147/50+1/4800.
\end{aligned}
\]

But disk containment gives x_G+y_G+a<=r sqrt(2)<147/50;
the last squared reserve is 863/80000. This is impossible. Thus

\[
                             x_G<x_D.                         \tag{8}
\]

**A positive-G primary axis cannot separate toward G.** For such an
axis u_G=(a,b), a>=b>=0, physical separation would imply
a Delta_x+b Delta_y>=R>=1, where
Delta_x=x_G-x_D and Delta_y=y_G-y_D>0. Hence
a(Delta_x+Delta_y)>=1 and
x_G+y_G>=x_D+y_D+1/a. The weaker version of (7), replacing
707/1000 by 7/10, gives x_D+y_D>589/480>1.
Consequently x_G+y_G+a>1+a+1/a>=3, whereas containment gives
x_G+y_G+a<=r sqrt(2)<3. This excludes the entire alternative,
including the aligned endpoint.

Every usable D/G normal has positive vertical component: a normal
with nonpositive vertical component has projection at most
|x_G-x_D|<1 by (2),(4), below the physical threshold R>=1.
Therefore the remaining upward normals are -u_D or v_D;
for negative G they also include -u_G or v_G; for positive G they
include only v_G. No physical signed axis is omitted.

## 4. Rational frame rules for every angle box

Use the rational half-angle functions a(t),b(t),h(t),k(t) of
equation (12) in the preceding chapter. A frame box is a triple
(l,u,s), meaning its half-angle magnitude is in [l,u] and its
canonical angle has sign s in {-1,+1}. Every physical magnitude
is at most sqrt(2)-1. The common initial interval is [0,5/12].

For each original P define

\[
 H_P=h(l_P),\quad
 U_P=\begin{cases}h(u_P),&u_P<2/5,\\707107/1000000,&u_P\ge2/5,
 \end{cases}\quad
 g_P^-=1/(4U_P),\quad A_P=a(l_P),
\]

\[
 t_P^-=\frac{2l_P}{1-l_P^2},\qquad
 t_P^+=\min\{1,2u_P/(1-u_P^2)\}.                              \tag{9}
\]

Then H_P<=h_P<=U_P, g_P>=g_P^- and the actual primary cosine
is at most A_P. The rational upper bound for 1/sqrt(2) is valid
because 707107^2-500000000000=309449>0. All lower endpoints
in the delivered table are inside the canonical range.

For a rational unit direction n=(p,q), define M_P(n) as follows.
At each of t=l_P,u_P form
c=p a(t)+q s_P b(t), e=-p s_P b(t)+q a(t), and include
(|c|+|e|)/2. Also include 1/2 if the two endpoint c-values
have nonpositive product or the two endpoint e-values have
nonpositive product. Take the minimum of these included values.
This is a lower bound for the same original's support: between
successive projection corners the support is concave in its angle;
a corner is exactly a zero of c or e and has support 1/2.

For two boxes P,T let R^-_{PT} be the maximum of 1 and the minimum
of the following candidates:

\[
 \frac{1+a(l)a(m)+s_Ps_T b(l)b(m)
       +|a(l)s_Tb(m)-s_Pb(l)a(m)|}{2},                         \tag{10}
\]

for all four endpoint choices l in {l_P,u_P}, m in {l_T,u_T};
include 1 as an extra candidate when their signed half-angle
intervals overlap. Then R^-_{PT} is a lower bound for the common
physical pair threshold. To check this, use concavity of
cos(theta)+sin(theta) between zero and the largest absolute
relative angle, retaining a possible zero relative angle. At
the harmless enlarged canonical endpoints the formula without
an absolute cosine can only weaken the bound. The universal
threshold at least one remains valid. For a direct concavity check
on the enlargement, the largest relative angle is at most
4 arctan(5/12)<5/3<3 pi/4; cos(theta)+sin(theta) is positive
there and its second derivative is its negative. Every endpoint
calculation in (10) is rational.

## 5. Complete fixed list of affine rows

Let X=(x_C,y_C,x_D,y_D,x_G,y_G). Every numbered row has the
form A_j X<=B_j. Indices start at zero. Put beta=27/92,
Delta_x=x_G-x_D, Delta_y=y_G-y_D, and

\[
 L=\max\{g_D^-+g_G^-,7(H_D+H_G)/8-41/120\}.
\]

For each original P=C,D,G, with local number i=0,1,2,
rows 36i through 36i+3 are x_P<=rho, -x_P<=rho,
y_P<=rho, -y_P<=rho, in that order. Rows 36i+4+j,
j=0,...,31, are

\[
                  n_j\cdot c_P\le r_0-M_P(n_j).               \tag{11}
\]

The directions, in their exact index order, are:

| j | n_j | j | n_j |
|---:|---|---:|---|
| 0 | (-1,0) | 16 | (0,1) |
| 1 | (-63/65,-16/65) | 17 | (15/113,-112/113) |
| 2 | (-63/65,16/65) | 18 | (15/113,112/113) |
| 3 | (-15/17,-8/17) | 19 | (7/25,-24/25) |
| 4 | (-15/17,8/17) | 20 | (7/25,24/25) |
| 5 | (-55/73,-48/73) | 21 | (39/89,-80/89) |
| 6 | (-55/73,48/73) | 22 | (39/89,80/89) |
| 7 | (-3/5,-4/5) | 23 | (3/5,-4/5) |
| 8 | (-3/5,4/5) | 24 | (3/5,4/5) |
| 9 | (-39/89,-80/89) | 25 | (55/73,-48/73) |
| 10 | (-39/89,80/89) | 26 | (55/73,48/73) |
| 11 | (-7/25,-24/25) | 27 | (15/17,-8/17) |
| 12 | (-7/25,24/25) | 28 | (15/17,8/17) |
| 13 | (-15/113,-112/113) | 29 | (63/65,-16/65) |
| 14 | (-15/113,112/113) | 30 | (63/65,16/65) |
| 15 | (0,-1) | 31 | (1,0) |

Every direction has squared norm exactly one.
The remaining rows are the following:

| Row | Affine inequality |
|---:|---|
| 108 | -x_C<=-H_C+1/60 |
| 109 | x_C<=min(U_C+5/64,r_0-1-g_C^-) |
| 110 | -x_D<=-4/3 |
| 111 | -x_G<=-H_G-101/432 |
| 112 | -v<=-2/3 |
| 113 | v-d<=0 |
| 114 | -d<=-g_C^- -g_D^- |
| 115 | d<=U_C+U_D |
| 116 | d<=1-H_C+U_D |
| 117 | -(7/8)x_C-y_C<=7/32 |
| 118 | -x_C-beta x_G<=-27/184-H_C-beta H_G |
| 119 | x_D+beta x_G<=211/184+U_D+beta U_G |
| 120 | -Delta_x<=1459/1728 |
| 121 | Delta_x<=11/60 |
| 122 | -Delta_y<=-L |

Rows 108--122 follow from Sections 1--3 and the interval rules.
No variable product is approximated.

Row 123 records the selected C/D secondary owner O in {C,D}:

\[
                  -t_O^+ d-v\le-R^-_{CD}/A_O.                 \tag{12}
\]

Its original normal is (t_O,1) before unit normalization. Since
d>0, replacing t_O by its upper bound enlarges the projection.
The threshold after normalization is at least R^-_{CD}/A_O.

For row 124 let O be the selected D/G owner. For a primary
alternative the remaining normal is (-1,t_O), and the row is

\[
              Delta_x-t_O^+ Delta_y\le-R^-_{DG}/A_O.           \tag{13}
\]

For a secondary alternative put p=t_O^- when O has negative
tilt, and p=-t_O^+ when O=G has positive tilt. The row is

\[
                      -p Delta_x-Delta_y\le-R^-_{DG}/A_O.     \tag{14}
\]

Equations (13)--(14) are necessary owned-axis inequalities because
Delta_y>0 and Delta_x<0. They use the actual same pair threshold
and preserve its original frame owner. Finally row 125 is
Delta_x<=0, by (8). These are all the rows used in the table.

## 6. How to read and check every arithmetic entry

Each line in the [leaf table](tables/c-slant-secondary.tsv) gives a leaf
number, root number, angle path, positive integer m, and a list j:w
of row numbers and positive integer weights. Start every magnitude
interval at [0,5/12]. A path symbol C0, D0 or G0 takes the lower
closed midpoint half of that original's current interval; C1,D1,G1
take the upper closed half. Apply the symbols from left to right.
The root fixes the two orientation signs and the actual owners.

For that rational box reconstruct rows (9)--(14). Let

\[
 a=\sum_j w_j A_j,\quad b=\sum_jw_j B_j,\quad W=\sum_jw_j.
\]

Every printed line satisfies the explicit rational comparison

\[
                 -b-\frac{91}{60}\sum_{k=0}^5|a_k|
                                      \ge \frac{mW}{100000}>0. \tag{15}
\]

The original center bounds give a X>=-rho sum|a_k|, while the
weighted row sum gives a X<=b. Equation (15) contradicts these
two facts. Coefficients need not cancel exactly: the full residual
on all six original coordinates is paid in (15).
All weights and all coefficients are rational and printed or defined
above; no floating-point cancellation is a proof input.

For example, leaf 0 has path C0.D0.G0.C0.D0.G0.D0 in root 0.
Its weights are 291235,37206,19775,307289,29765,29765,284966
on rows 36,100,109,111,117,123,124 respectively. Their sum is
1000001. Direct rational substitution gives sum|a_k|<3/2 and
-b>26427, so the reserve exceeds
26427-(91/60)(3/2)=26424.725, which exceeds
2642(1000001)/100000 as printed. Every other leaf uses the same
explicit rule. Across the complete table m is at least 29.

## 7. Whole-domain coverage and exact outcome

The preceding chapter gives three complete C-sign/C-D-owner cases:
negative C with owner C or D, and positive C with owner D.
For each, retain both signs of G. Sections 2--3 cover all usable
upward D/G axes. Negative G has four remaining owner/axis choices;
positive G has three. Thus there are exactly 3(4+3)=21 roots,
listed with their complete leaf counts in
[the root table](tables/c-slant-secondary-roots.tsv).

In every root the delivered paths form a complete binary cover:
each nonterminal prefix has exactly two children, obtained by the
two closed midpoint halves of the same original angle interval.
There are 4,183 such splits and 4,204 terminal paths, with no
unresolved or omitted child. Their union covers the original box
including every shared face and aligned endpoint. Each terminal is
excluded by its printed inequality (15).

Therefore no secondary C/D axis is possible under (1)--(2).
The primary-axis chapter excluded every other physical C/D axis.
The separating-axis theorem gives the promised conditional conclusion:

> In the normalized original `001/00` domain with nonpositive D,
> y_D-y_C>=2/3 and the G-order input y_G>y_D, one has
> y_C+(7/8)x_C<-7/32.

The lower-G chapter supplies (2) under the contrary assumption (1),
and thereby completes the nonpositive-D C-slant assembly without
an archived G-order input. The positive-D callers and the remaining
original-nine domains still need proofs. No unrestricted or whole-mask
completion is counted here.

The finite combinations were found computationally. The mathematical
proof delivered here is their fully specified rational table, the
physical derivations, and the complete subdivision cover. Exact
fraction arithmetic checked the entries locally. No independent
human review, Lean, Lake, CI or kernel verification is claimed.

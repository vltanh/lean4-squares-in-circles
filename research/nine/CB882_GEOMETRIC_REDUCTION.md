# Whole-domain localization of the downward-cone original

This chapter gives necessary inequalities on the entire original Cb882
domain. It keeps all nine physical originals, their independent frames,
all pair conditions, the actual links AB, BC, EF, FG, and the strict weak
CD bit. It does not exclude that whole domain or supply the missing cover
of the [local sharp terminal](CB882_LOCAL_SHARP_TERMINAL.md).

The conclusions are stronger endpoint-coordinate bounds and the strict
localization **x_H<-1/40**. In particular, the latter is not restricted to
the previously excluded low-B subdomain.

Put Q=1105/256 and rho=91/60. Every corner is in the closed Q-disk;
the statements therefore also apply to the strict-radius caller. Retain
the Cb882 normalization theta_D<=0 and y_D-y_C>2/3, and its literal
downward-cone condition

\[
                 y_H-y_B\le-|x_H-x_B|.                 \tag{1}
\]

For each original P, let h_P be its coordinate projection halfwidth and
g_P=1/(4h_P) its contained aligned-inset halfwidth. The inputs are:

* [Extraction, Lemma 2.1](EXTRACTION.md): |x_P|-g_P<17/16,
  |c_P|<rho, g_P>=1/(2 sqrt(2))>7/20, and h_P+g_P>=1.
* [The inner-frame theorem](00100_INNER_FRAME_AND_DOWNWARD_CONE.md):
  |tan(theta_B)|<1/12 and x_B>-31/60.
* [The complete nonpositive-D C-slant proof](00100_C_SLANT_LOWER_COMPLEMENT.md):
  y_C+(7/8)x_C<-7/32. Its lower-right-pocket consequence is proved
  in Section 4 of the inner-frame chapter: no additional original X
  has x_X>=0 and y_X<=y_C.

These inputs are whole-parent theorems. None assumes an E/G height
order, an H height order relative to C, or the conclusions below.

## 1. A sharper one-sided horizontal span

CD is a horizontal center-cone link. Its actual insets give
x_D-x_C>=g_C+g_D. Since x_D>0, the unary inset bound gives

\[
 x_D-g_D<\frac{17}{16},\qquad
 x_C+g_C\le x_D-g_D<\frac{17}{16}.                  \tag{2}
\]

Subtract h_C+g_C>=1 and then use the actual BC and AB links:

\[
\begin{aligned}
 x_C-h_C&<\frac1{16},\\
 x_B+h_B&\le x_C-h_C<\frac1{16},\\
 x_A+h_A+2h_B&\le x_B+h_B<\frac1{16}.              \tag{3}
\end{aligned}
\]

Thus the following bounds hold on the whole caller:

\[
 \boxed{\quad x_C<\frac{57}{80},\qquad
 x_B<-\frac7{16},\qquad x_A<-\frac{23}{16}.\quad}   \tag{4}
\]

The C bound follows from g_C>7/20 in (2); the other two use h>=1/2.
The correlated inequalities (2)--(3), which retain the actual frame
halfwidths, are stronger than these constant consequences.

The BC cone and C-slant now give a modest height improvement as well:

\[
\begin{aligned}
 y_B&\le y_C+x_C-x_B
 <-\frac7{32}+\frac{x_C}{8}-x_B\\
 &<-\frac7{32}+\frac{57}{640}+\frac{31}{60}
   =\frac{743}{1920}.                              \tag{5}
\end{aligned}
\]

## 2. The actual B square gives a uniform cone clearance

**Lemma.** If an original unit square H is disjoint in its open interior
from B and satisfies (1), then

\[
                       y_B-y_H>\frac{203}{240}.     \tag{6}
\]

This uses only B's narrow frame, its physical square, and H's incircle.
It makes no assumption on H's frame or on the sign of x_H.

Write B's canonical side as (a,b), with a>0, and put t=b/a. Since
|t|<1/12, we have |b|<1/12 and

\[
 a^2>\frac{144}{145}>\left(\frac{239}{240}\right)^2,
 \qquad
 \frac{144}{145}-\left(\frac{239}{240}\right)^2
       =\frac{2371}{1670400}>0.                     \tag{7}
\]

Set k_0=203/240. In physical coordinates of B, the squared distance
from a point z=(z_1,z_2) to its closed square is

\[
 d_B(z)^2=
 \max\{|a z_1+b z_2|-1/2,0\}^2+
 \max\{|-b z_1+a z_2|-1/2,0\}^2.                  \tag{8}
\]

The function (8) is convex. Indeed each summand is a convex
nondecreasing function of the absolute value of a linear expression;
alternatively its one-variable derivative is nondecreasing on its
three defining intervals. Every point of [-k_0,k_0]^2 is a convex
combination of its four vertices, so the maximum of (8) over that
box is bounded by its maximum at the vertices.

At each vertex, the two absolute physical coordinates, in some order,
are k_0(a+|b|) and k_0(a-|b|). Both exceed 1/2, since

\[
 k_0(a-|b|)-\frac12>
 \frac{203}{240}\left(\frac{239}{240}-\frac1{12}\right)
       -\frac12=\frac{5219}{19200}>0.
\]

Using a^2+b^2=1, (8) at a vertex is therefore exactly

\[
 2k_0^2-2a k_0+\frac12
 <2\left(\frac{203}{240}\right)^2
   -2\frac{239\cdot203}{240^2}+\frac12
 =\frac14-\frac3{800}<\frac14.                    \tag{9}
\]

If k=y_B-y_H<=k_0, the cone (1) puts c_H-c_B in this box.
Equation (9) would then put c_H at distance strictly less than 1/2
from B. H's open incircle would meet B's open interior: a point of
the closed B square at distance less than 1/2 can be moved a
sufficiently small distance into its interior while preserving that
strict distance. This contradicts the physical nonoverlap of B,H.
Hence k>k_0, proving (6), including cone-boundary cases.

Combining (5) and (6) gives the unconditional height bound

\[
                         \boxed{y_H<-\frac{881}{1920}.}        \tag{10}
\]

## 3. The whole downward-cone original lies left of the vertical axis

First suppose y_H>=y_C, and put

\[
                     X=x_C-x_H,\qquad Y=y_H-y_C\ge0.
\]

The two cone inequalities give

\[
 y_H-y_C
 \le y_B-y_C-|x_H-x_B|
 \le x_C-x_B-(x_H-x_B)=X,                         \tag{11}
\]

so X>=Y>=0. The sharper clearance (6), the BC cone, (4), and
x_B>-31/60 give

\[
 Y=(y_B-y_C)-(y_B-y_H)
 <\frac{57}{80}+\frac{31}{60}-\frac{203}{240}
 =\frac{23}{60}.                                  \tag{12}
\]

The C/H incircles require X^2+Y^2>=1. If X<=11/12, (12) would
instead give

\[
 X^2+Y^2<\left(\frac{11}{12}\right)^2
              +\left(\frac{23}{60}\right)^2
          =\frac{1777}{1800}<1.
\]

Consequently X>11/12 and

\[
 y_H\ge y_C\quad\Longrightarrow\quad
 \boxed{x_H<x_C-\frac{11}{12}<-\frac{49}{240}.}     \tag{13}
\]

If y_H<=y_C, the already proved lower-right-pocket exclusion applies
to this same original H and gives x_H<0. These two cases cover
every original H, with their common height boundary retained. Therefore

\[
                              \boxed{x_H<0.}       \tag{14}
\]

For a finite continuation, a useful complete union is

| Height case | Necessary further bounds |
|---|---|
| y_H<=y_C | x_H<0 (strengthened to x_H<-1/40 in Section 4) |
| y_H>=y_C | x_C-x_H>11/12 and x_H<-49/240 |

All strict bounds may be weakened to closed inequalities when
constructing a rational enclosure.

## 4. A uniform negative margin for H

In fact the whole caller satisfies

\[
                            \boxed{x_H<-\frac1{40}.}          \tag{15}
\]

When y_H>=y_C, (13) is stronger. It remains to consider y_H<=y_C.
Suppose, for a contradiction, that -1/40<=x_H<0, and put

\[
 p=x_C,\qquad X=x_C-x_H,\qquad Z=y_C-y_H\ge0.
\]

The whole-parent bounds and C-slant give

\[
 \frac{29}{60}<p<\frac{57}{80},\quad
 0<X\le p+\frac1{40},\quad
 0\le Z<\frac{623}{480}-\frac78p.                   \tag{16}
\]

The rightmost expression is positive on the displayed p interval.
There are two exhaustive cases.

If p>=11/20, the convex quadratic

\[
 f(p)=\left(p+\frac1{40}\right)^2+
                  \left(\frac{623}{480}-\frac78p\right)^2
\]

is bounded by its maximum at the two endpoints of
[11/20,57/80]. Their exact reserves below one are

| p | 1-f(p) |
|---|---:|
| 11/20 | 7/2880 |
| 57/80 | 4319/3686400 |

Thus X^2+Z^2<1, contradicting the C/H incircles.

If p<=11/20, the actual AB and BC links and x_A>-rho give
x_C>h_C-1/60. Consequently h_C<p+1/60<=17/30. This implies
|beta_C|<3/20. Indeed (sqrt(1-b^2)+b)/2 increases for
0<=b<=1/sqrt(2); at b=3/20 it is greater than 17/30 because

\[
 \frac{\sqrt{391}+3}{40}>\frac{17}{30}
 \quad\Longleftrightarrow\quad3\sqrt{391}>59,
 \qquad3519>3481.
\]

Equation (16) now gives X<=23/40 and Z<7/8. Write C's canonical
frame as (a,b),(-b,a), where |b|<3/20 and a>247/250. The latter
follows from a^2>391/400>(247/250)^2, with squared reserve
339/250000>0.

As in Section 2, squared distance to the closed C square is a convex
function of the displacement. Its maximum on
[0,23/40] times [0,7/8] is therefore bounded by the maximum at
the four vertices. Negating a displacement leaves that distance
unchanged, so this box covers the displacement under consideration.
At the origin the distance is zero. At the two axis vertices its
squared distance is at most (3/40)^2 or (3/8)^2, respectively:
the smaller physical coordinate is less than 1/2 and the larger
does not exceed the corresponding axis length.

At the remaining vertex put d=23/40 and z=7/8. Both physical
coordinates U=ad+bz and V=az-bd are positive. They satisfy

\[
 U\le d+\frac3{20}z=\frac{113}{160}<1,\qquad
 V\le z+\frac3{20}d=\frac{769}{800}<1.              \tag{17}
\]

Their positivity follows, for example, by replacing a below by
247/250 and |b| above by 3/20. If either coordinate is at most
1/2, (17) makes the squared distance strictly less than 1/4. If
both exceed 1/2, the exact distance formula and a^2+b^2=1 give

\[
\begin{aligned}
 (U-1/2)^2+(V-1/2)^2
 &=d^2+z^2-a(d+z)-b(z-d)+\frac12\\
 &<d^2+z^2-\frac{247}{250}(d+z)
                   +\frac3{20}(z-d)+\frac12\\
 &=\frac{4173}{20000}<\frac14.                    \tag{18}
\end{aligned}
\]

Every vertex has squared distance less than 1/4. Convexity gives
the same bound throughout the box, making H's open incircle meet
C's open interior. Both p cases are impossible, proving (15) on
the whole domain. The shared endpoint p=11/20 is retained in both
cases.

## 5. A limitation of using only A,B,C,D,H for further height routing

The stronger proposed bound y_H<-3/4 cannot be obtained from just
these five squares, their actual AB/BC links, all three main cones,
strict weak CD, the downward B/H cone, and C-slant. Here is an exact
strict-radius obstruction to that restricted implication:

| Original | Center | Frame |
|---|---|---|
| A | (-3/2,0) | aligned |
| B | (-1/2,1/3) | aligned |
| C | (1/2,-2/3) | aligned |
| D | (65/48,3/16) | theta_D=-pi/4 |
| H | (-1/2,-2/3) | aligned |

The six pairs among A,B,C,H separate by their unit horizontal or
vertical coordinate gaps. D separates horizontally from A,B,H.
For C,D the center difference is (41/48,41/48). The positive
secondary axis of D is (1/sqrt(2),1/sqrt(2)), so it gives a strict
physical separator because

\[
 \frac{41\sqrt2}{48}>\frac12+\frac1{\sqrt2}
 \quad\Longleftrightarrow\quad17\sqrt2>24,
 \qquad 578>576.
\]

The CD cone is at equality, its height difference exceeds 2/3,
and its horizontal gap 41/48 is strictly less than h_C+h_D.
The AB and BC links are actual; their cones hold. Also
y_B-y_H=1 with x_B=x_H, and

\[
 y_C+(7/8)x_C=-\frac{11}{48}<-\frac7{32}.
\]

The maximum squared corner norms of A, B, and C/H are respectively
17/4, 61/36, and 85/36, all strictly below Q. The maximum for D
is its rightward vertex, with squared norm

\[
 \left(\frac{65}{48}+\frac1{\sqrt2}\right)^2
       +\left(\frac3{16}\right)^2
 =\frac{5458}{2304}+\frac{65\sqrt2}{48}.
\]

Using sqrt(2)<10/7, its reserve below Q is strictly greater than

\[
 \frac{4487}{2304}-\frac{325}{168}
       =\frac{209}{16128}>0.
\]

Thus all five physical squares fit strictly below Q while
y_H=-2/3>-3/4. This is a limitation of that five-square argument,
not a counterexample to the full nine-square problem. Any stronger
height routing must use further information, such as E,F,G and their
physical pairs, or the ninth original I.

The proved inequalities above do not identify the location or physical
frame of I, force E above A or G above D, or imply the full guard of
the local sharp terminal. Those routing obligations remain. Every
scalar comparison used here is displayed; no optimizer or
finite-search result is a proof premise.

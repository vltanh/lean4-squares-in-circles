# Endpoint insets separate vertically

This is a complete hand lemma for the original `001/00` domain. It
uses the seven original squares A--G, with their independent physical
frames and pairwise disjoint interiors. Boundary contacts in the closed
disk of squared radius Q=1105/256 are allowed. No hypothesis about H,
I, the CD height difference, or the signs of the physical tilts is used.

Assume AB,BC,EF,FG are actual positive horizontal projection links and
CD is a positive horizontal center-cone link. Write h_P for the common
coordinate projection halfwidth of P, and g_P=1/(4h_P) for its contained
aligned-inset halfwidth. Then

\[
             |x_E-x_A|<g_A+g_E.                         \tag{1}
\]

Consequently the actual insets of A,E must separate vertically:

\[
             |y_E-y_A|\ge g_A+g_E.                    \tag{2}
\]

For D,G the [secondary-axis chapter](00100_C_SLANT_SECONDARY_AXES.md),
Section 2, proves x_G-h_G>101/432, x_D<=r-h_D, and
x_G-x_D<11/60. Thus, with S=h_D+h_G and K=3187/1728<2,
x_D-x_G<K-S<2-S<=g_D+g_G. The reverse gap 11/60 is
also smaller than g_D+g_G>=1/sqrt(2). These gap arguments use only
the two endpoint caps and actual links; they do not use the contrary
C-slant hypothesis or a G-height order. Thus both endpoint inset pairs
are vertical in the whole `001/00` domain.

## 1. Elementary bounds for A

Put r=sqrt(Q) and rho=91/60. The original center bound is |c_P|<rho.
Actual AB,BC and the contained CD insets give

\[
 x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D
                   \ge h_A+2+g_D.                       \tag{3}
\]

The horizontal span of the four originals therefore gives
2h_A+2h_B+2<=2r. Since h_B>=1/2 and r<133/64,

\[
                       h_A<37/64.                       \tag{4}
\]

Take the absolute components of a canonical side of A as alpha>=beta>=0,
and put w=tan(|theta_A|/2). Then

\[
 0\le w<1/10,\qquad
 \alpha=\frac{1-w^2}{1+w^2},\quad
 \beta=\frac{2w}{1+w^2},\quad
 h_A=\frac{1+2w-w^2}{2(1+w^2)}.                         \tag{5}
\]

Indeed h increases up to the canonical endpoint sqrt(2)-1, and
h(1/10)=119/202>37/64. In particular beta<1/5 and r beta<1/2.
The unary quarter-disk maximization proved in
[EXTRACTION.md](EXTRACTION.md), Lemma 2.1, equation (6), now gives

\[
 |x_A|\le\alpha\left(\sqrt{Q-1/4}-1/2\right)
                    <\rho\alpha.                       \tag{6}
\]

For clarity, this uses physical coordinates U,V of the same original:
(|U|+1/2)^2+(|V|+1/2)^2<=Q and
|x_A|<=alpha|U|+beta|V|. Since r beta<1/2, the maximum
has |V|=0. Also sqrt(Q-1/4)-1/2<91/60: the exact squared comparison is
1041/256<(121/60)^2, whose difference is 31/57600.

For the reverse horizontal case, use the full span from x_A to the
rightmost projection of D:
x_D+h_D-x_A>=h_A+2h_B+2>=7/2.
Since x_D+h_D<=r, this proves x_A<=r-7/2<-91/64.

## 2. Exclude the forward horizontal inset case

Suppose x_E-x_A>=g_A+g_E. Actual EFG gives

\[
 x_G-x_A\ge g_A+(g_E+h_E)+2h_F+h_G
                       \ge g_A+2+h_G.                  \tag{7}
\]

Use the physical two-square cap in [FOUNDATION.md](FOUNDATION.md),
Part B, with G as the square of weight 46, D as the square of weight
27/2, and direction reversed. It gives

\[
        46(x_G-h_G)+(27/2)(x_D-h_D)\le211/4.            \tag{8}
\]

From (3), (6), and (7), its left side is strictly greater than

\[
 \frac{119}{2}(2-\rho\alpha)+46g_A+\frac{27}{2}h_A
                              -\frac{27}{2}\frac{71}{200}. \tag{9}
\]

Here g_D-h_D>=-sqrt(2)/4>-71/200, since 71^2>5000.
Subtracting 211/4 from (9), and substituting (5), gives exactly

\[
 \frac{N(w)}{1200(1+w^2)(1+2w-w^2)},\qquad
 N(w)=1159-36682w+287980w^2+331678w^3-146339w^4.         \tag{10}
\]

The denominator is positive. The following two elementary estimates
prove N(w)>0 on the whole interval 0<=w<=1/10.

* If 0<=w<=1/25, the last two terms have nonnegative sum. The
  quadratic 1159-36682w+287980w^2 decreases on this interval and
  has value 19061/125>0 at w=1/25.
* If 1/25<=w<=1/10, then
  331678w-146339w^2>=1180373/100>11020. Therefore

  \[
  \begin{aligned}
  N(w)&\ge1159-36682w+299000w^2\\
      &=299000(w-3/50)^2+413/5-802w\\
      &\ge12/5>0.
  \end{aligned}
  \]

This contradicts (8) and excludes the entire forward horizontal case.

## 3. Exclude the reverse case and conclude

The full-span bound at the end of Section 1 and x_E>-rho give

\[
                x_A-x_E<\rho-91/64=91/960<1/2
                                      <g_A+g_E.
\]

Together with Section 2 this proves (1). The original insets are actual
subsets of their respective physical squares, so their interiors cannot
overlap. Since their horizontal interiors overlap by (1), their vertical
interiors must be disjoint, proving (2). No numerical optimization or
finite search is a proof input.

This eliminates two branches of the endpoint-inset disjunction; it does
not yet exclude the remaining upward and downward placements, the
whole Cb882 original, or all nine-square configurations.

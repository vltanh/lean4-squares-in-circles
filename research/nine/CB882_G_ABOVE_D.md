# G lies above D on the whole Cb882 original

Retain the entire [Cb882 original-nine predicate](CB882_WHOLE_DOMAIN.md),
including all nine independently oriented physical unit squares and every
original pair condition. This chapter proves

\[
                    y_G-y_D\ge g_D+g_G.                 \tag{1}
\]

Here h_P is the common horizontal and vertical projection halfwidth of
P, and g_P=1/(4h_P) is its contained aligned-inset halfwidth. Thus (1)
separates the actual contained insets vertically. All arguments also
allow original corners on the circle of squared radius Q=1105/256.
Write rho=91/60; every original center has norm strictly less than rho.

The proof excludes the full lower-G alternative. It uses no angle box
for G, no chosen C/G separating axis, and no finite search.

## 1. Whole-parent inputs

Put p=x_C. The actual AB, BC links and x_A>-rho imply
p>h_C-1/60. Section 1 of the
[geometric reduction](CB882_GEOMETRIC_REDUCTION.md) gives the sharper
upper bound for p and the one-sided D bound. Together these are

\[
 \frac{29}{60}<p<\frac{57}{80},\qquad
 h_C<p+\frac1{60},\qquad x_D-g_D<\frac{17}{16}.       \tag{2}
\]

The [complete nonpositive-D C-slant proof](00100_C_SLANT_LOWER_COMPLEMENT.md)
gives

\[
                    y_C+\frac78p<-\frac7{32}.          \tag{3}
\]

Its lower-right-pocket consequence, proved in Section 4 of the
[inner-frame chapter](00100_INNER_FRAME_AND_DOWNWARD_CONE.md), excludes
every additional original X with x_X>=0 and y_X<=y_C.

Section 2 of the [secondary-axis chapter](00100_C_SLANT_SECONDARY_AXES.md)
derives x_G-h_G>101/432 from the two physical endpoint caps and actual
links. That derivation uses neither that chapter's contrary C-slant
hypothesis nor its upper-G hypothesis. In particular,

\[
 x_G>h_G+\frac{101}{432}\ge\frac{317}{432}
       >\frac{57}{80}>p,\qquad y_G>y_C.                \tag{4}
\]

The last inequality follows from the pocket exclusion. The
[endpoint-inset theorem](00100_ENDPOINT_INSETS_ARE_VERTICAL.md) gives

\[
                    |y_G-y_D|\ge g_D+g_G.              \tag{5}
\]

All these inputs hold before selecting either vertical alternative in
(5). In particular, the completed proof of (3) includes its lower-G
complement, so its use here does not assume (1).

## 2. A clearance bound for two independently oriented squares

For any two interior-disjoint physical unit squares P,T,

\[
              |c_T-c_P|\ge1+|h_T-h_P|.                 \tag{6}
\]

Here is a direct proof, retaining both physical frames. If delta is
their relative angle, set

\[
 H=\frac{|\cos\delta|+|\sin\delta|}{2},\qquad R=\frac12+H.
\]

The physical separating-axis theorem, as in
[Foundation A.2](FOUNDATION.md), gives a separating side normal of P
or T. Along every such normal the sum of the two projection halfwidths
is R, so |c_T-c_P|>=R.

Temporarily center both squares at the origin solely to compare their
supports. In P's orthonormal frame, the absolute coordinates of each T
corner, in either order, are H and
K=||cos(delta)|-|sin(delta)||/2. Since H>=1/2 and K<=1/2,
each corner has Euclidean distance H-1/2=R-1 from P. Every point of T
is a convex combination of its corners. Taking the same combination
of closest points in P and using the triangle inequality shows that
every point of T is within R-1 of P. Interchanging P,T gives the
reverse statement.

Consequently their support values in any unit direction differ by at
most R-1. In particular |h_T-h_P|<=R-1 in the horizontal direction.
Combining this with the physical separating-axis bound proves (6).
Boundary contacts cause no change to either non-strict inequality.

## 3. Necessary bounds for the lower-G alternative

Suppose, contrary to (1), that the other alternative in (5) holds:

\[
                         y_D-y_G\ge g_D+g_G.           \tag{7}
\]

Set

\[
 h=h_G,\quad g=\frac1{4h},\quad s=y_G-y_C\ge0,\quad
 L=\frac{17}{16}-p-g,\quad
 B=\frac{15}{8}p+g-\frac{27}{32}.
\]

The CD center cone gives y_D-y_C<=x_D-p. Thus (2), (3), and (7) imply

\[
 \begin{aligned}
 0\le s&\le x_D-p-g_D-g<L,\\
 y_G&=y_C+s<-\frac7{32}-\frac78p+L=-B.
 \end{aligned}                                         \tag{8}
\]

In particular L>0. Apply (6) to the original C,G pair. By (2),

\[
 |c_G-c_C|\ge1+|h-h_C|\ge1+h-h_C
                  >\frac{59}{60}+h-p.
\]

The same pair has center distance at least one. Hence, with
R_0=max(1,59/60+h-p),

\[
 (x_G-p)^2+s^2\ge R_0^2.                               \tag{9}
\]

We now show that (8)--(9) force |c_G|>rho, in two exhaustive ranges
of the single physical halfwidth h. By (4), x_G-p is positive.

## 4. The range h<=11/20

Here g>=5/11. Using p>29/60 in (8) gives

\[
 0<L<\frac{17}{16}-\frac{29}{60}-\frac5{11}
       =\frac{329}{2640}<\frac18,
 \qquad
 B>\frac{91}{176}>\frac12.
\]

By (9) and s<L, therefore,

\[
 x_G-p>\sqrt{1-\frac1{64}}>\frac{119}{120},
 \qquad x_G>\frac{59}{40},\qquad y_G<-\frac12.
\]

The second square-root comparison follows from
63/64-(119/120)^2=7/7200>0. It follows that

\[
 |c_G|^2>\left(\frac{59}{40}\right)^2+\frac14
       =\frac{3881}{1600}
       =\rho^2+\frac{361}{2880},
\]

contradicting the universal center bound.

## 5. The range h>=11/20

Every physical unit square has g>=1/(2sqrt(2))>7/20. Consequently

\[
 L<\frac{57}{80}-p,\qquad
 B>\frac{33}{80}>\frac25,\qquad
 R_0\ge\frac{23}{15}-p.
\]

Consider the concave quadratic

\[
 F(p)=\left(\frac{23}{15}-p\right)^2
      -\left(\frac{57}{80}-p\right)^2
      -\left(\frac32-p\right)^2.
\]

Its endpoint values on the full interval in (2) are

| p | F(p) |
|---|---|
| 29/60 | 943/57600 |
| 57/80 | 193/3600 |

Thus F(p)>0 throughout that interval. Since L>0 and
57/80-p>0, (8)--(9) yield

\[
 (x_G-p)^2>
 \left(\frac{23}{15}-p\right)^2
 -\left(\frac{57}{80}-p\right)^2
 >\left(\frac32-p\right)^2.
\]

Both x_G-p and 3/2-p are positive. Hence x_G>3/2 and y_G<-2/5,
which gives the second contradiction

\[
 |c_G|^2>\frac94+\frac4{25}
       =\frac{241}{100}=\rho^2+\frac{79}{720}.
\]

The boundary h=11/20 is included in both ranges. These two
contradictions exclude (7) on the whole unchanged Cb882 original.
The exhaustive inset alternative (5) therefore proves (1). The
conclusion is a whole-parent G-order reduction; the remaining
Cb882 configurations still require exclusion.

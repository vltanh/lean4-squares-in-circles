# A left-cap exclusion and the whole Cd402 H-order

This chapter proves a left-cap exclusion on the entire normalized
001/00 caller and, as a corollary, a necessary height order on the
unchanged Cd402 original. It uses five elementary interval comparisons
and imports no archived continuation or Cb882 downward-cone bound.

Retain all nine original physical unit squares in the closed disk of
squared radius Q=1105/256, with the original actual links AB, BC, EF,
FG, the strictly weak CD link and its center cone, and the selected
other center cones. Every original X distinct from A satisfies

\[
       \boxed{x_X+g_X>-15/16},\qquad |y_A|<1/4.          \tag{L}
\]

These conclusions require no A/D tilt sign or H-order hypothesis.
For Cd402 retain its further original hypotheses, including A's
nonnegative canonical tilt, D's nonpositive canonical tilt,
y_D-y_C>2/3, x_H<=x_I, and the exact escape condition

\[
                     y_H-y_B\ge x_H-x_B.                 \tag{1}
\]

Its additional conclusion is

\[
                     \boxed{y_H-y_B\ge g_B+g_H}.         \tag{2}
\]

Here h_P is the coordinate projection halfwidth of original P and
g_P=1/(4h_P) is the halfwidth of its centered aligned inset. No original
physical square or pair is discarded from either caller.

## 1. Two squares in a narrow left cap

Put c=15/16 and rho=91/60. We use the previously proved bounds

\[
 |c_P|<\rho,\quad g_P>7/20,\quad h_P+g_P\ge1,
 \quad h_A<37/64,\quad |\beta_A|<1/5.                  \tag{3}
\]

The first three are in [Extraction, Lemma 2.1](EXTRACTION.md);
the A-frame bounds follow from Section 1 of
[the endpoint-inset proof](00100_ENDPOINT_INSETS_ARE_VERTICAL.md).
The [geometric reduction, Section 1](CB882_GEOMETRIC_REDUCTION.md)
uses no H-order hypothesis and gives

\[
 x_D-g_D<17/16,\qquad x_A+h_A<-15/16=-c.               \tag{4}
\]

The physical B/H insets must be disjoint. Their four closed
separation alternatives, together with (1), imply the union

\[
 y_H-y_B\ge g_B+g_H
 \quad\hbox{or}\quad x_B-x_H\ge g_B+g_H.              \tag{5}
\]

Indeed, the rightward horizontal alternative implies the first by
(1), and the downward vertical alternative implies the second.
Suppose the second alternative holds. Actual BC and the CD insets
then give

\[
\begin{aligned}
 x_D-g_D
 &\ge x_C+g_C
 \ge x_B+h_B+h_C+g_C\\
 &\ge x_H+g_H+(g_B+h_B)+(h_C+g_C)
 \ge x_H+g_H+2.
\end{aligned}
\]

Consequently the H-left alternative in Cd402 would imply

\[
                         x_H+g_H<-c.                   \tag{6}
\]

We prove a stronger fact in Sections 2--4: (4) is incompatible with
even the closed inequality x_H+g_H<=-c for any original H distinct
from A. Those sections use no B/H order or Cd402-specific condition.
Renaming H as an arbitrary X proves (L); applying it to (6) proves
the Cd402 conclusion (2).

## 2. Corner bounds and a sharper A height

For a centered unit square let

\[
 h\in[1/2,1/\sqrt2],\qquad k=\sqrt{1/2-h^2},
 \qquad a=h+k,\qquad b=h-k.
\]

Thus a and b are the absolute values of its canonical cosine and
sine. If its center is (-X,Y), with X>=Y>=0, the largest squared
corner norm is at least each of

\[
       (X+k)^2+(Y+h)^2,
       \qquad (X+h)^2+(Y-k)^2.                          \tag{7}
\]

For the first bound, one tilt sign has the upper-left corner
(-X-k,Y+h). The other has the corner (-X-h,Y+k), whose squared
norm exceeds the first expression by 2(X-Y)(h-k)>=0. For the
second bound, the leftmost corner has coordinates (-X-h,Y+k)
or (-X-h,Y-k). Reflections in the coordinate axes show that (7)
also applies with X=abs(x) and Y=abs(y).

For A, (4) gives X>c+h_A>=23/16. Its center bound gives Y<1,
so X>Y. We claim

\[
                            |y_A|<1/4.                  \tag{8}
\]

Write h=h_A and use a,b as above. Since b<1/5 and a>4/5,

\[
 1-a=\frac{b^2}{1+a}\le\frac b9,
 \qquad h-\frac12=\frac{b-(1-a)}2\ge\frac{4b}{9}.
\]

Therefore 1-a<=(h-1/2)/4. If Y>=1/4, the first corner bound
in (7) and the strict X>c+h would give a squared corner norm
strictly larger than (c+a)^2+(h+1/4)^2. But

\[
\begin{aligned}
 (c+a)^2+(h+1/4)^2-Q
 &=-(1-a)(2c+a+1)+(h-1/2)(h+1)\\
 &\ge\left(-\frac{31}{32}+\frac32\right)(h-1/2)
 =\frac{17}{32}(h-1/2)\ge0.
\end{aligned}
\]

This contradicts corner containment and proves (8), including the
aligned endpoint b=0.

## 3. Five bounds on H's height

Now put h=h_H, g=1/(4h), k=sqrt(1/2-h^2), and Y=abs(y_H).
Under the closed contrary hypothesis, X=abs(x_H)>=c+g>5/4.
The center bound gives
Y^2<rho^2-25/16=166/225<1, so X>Y and (7) applies.

The following five closed intervals cover all possible h. The
column Y_0 means the strict conclusion Y<Y_0.

| h interval | lower bound g_0 for g | Y_0 |
|---|---:|---:|
| [1/2,3/5] | 5/12 | 2/3 |
| [3/5,13/20] | 5/13 | 3/4 |
| [13/20,27/40] | 10/27 | 4/5 |
| [27/40,11/16] | 4/11 | 4/5 |
| [11/16,1/sqrt(2)] | 7/20 | 4/5 |

Here is complete rational arithmetic for the first four rows. Write
[l,u] for the h interval and use the stated k_0<=k. If Y>=Y_0,
the first bound in (7) is at least
(c+g_0+k_0)^2+(l+Y_0)^2. Both displayed reserves are positive.

| Row | k_0 | 1/2-u^2-k_0^2 | (c+g_0+k_0)^2+(l+Y_0)^2-Q |
|---:|---:|---:|---:|
| 1 | 37/100 | 31/10000 | 1571/90000 |
| 2 | 5/18 | 11/32400 | 360031/5475600 |
| 3 | 21/100 | 11/40000 | 1312553/14580000 |
| 4 | 33/200 | 19/160000 | 42469/4840000 |

For the fifth row, h+1/(4h) is increasing for h>=1/2. Thus
X+h>=c+11/16+4/11=175/88. Also k^2<=7/256<1/36,
with difference 1/2304. If Y>=4/5, then Y-k>19/30, and
the second corner bound in (7) contradicts

\[
 \left(\frac{175}{88}\right)^2+
 \left(\frac{19}{30}\right)^2-Q
 =\frac{274459}{6969600}>0.
\]

This proves every height bound in the table without choosing H's
tilt sign.

## 4. The original A/H physical pair cannot fit

Both x_A and x_H lie in the interval (-rho,-c-g], since
h_A>=1/2>=g. In each row of the height table, therefore,

\[
 |x_A-x_H|<D:=\rho-c-g_0,
 \qquad |y_A-y_H|<Y_0+1/4.                             \tag{9}
\]

The support comparison in
[the G-order proof, Section 2](CB882_G_ABOVE_D.md)
gives, for every disjoint pair of original unit squares,

\[
 |c_A-c_H|\ge1+|h_H-h_A|
 \ge\max\{1,1+h_H-h_A\}.
\]

If l is the lower endpoint of the row, (3) makes this lower bound
at least R_0=max(1,l+27/64). Each line of the following exact table
contradicts (9):

| Row | D | R_0 | R_0^2-D^2-(Y_0+1/4)^2 |
|---:|---:|---:|---:|
| 1 | 13/80 | 1 | 7679/57600 |
| 2 | 607/3120 | 327/320 | 39737/6230016 |
| 3 | 451/2160 | 343/320 | 210521/74649600 |
| 4 | 569/2640 | 351/320 | 6041969/111513600 |
| 5 | 11/48 | 71/64 | 69761/921600 |

All reserves are strictly positive. Shared interval endpoints are
covered by both neighboring rows; neither a tilt-sign boundary nor
an inset contact is omitted. The closed contrary hypothesis is
impossible for any original H distinct from A. This proves the
universal left-cap exclusion (L), and then the H-left alternative
in (5) is impossible, proving the whole-original conclusion (2).

There is a further useful consequence throughout the same normalized
001/00 caller. For any original X distinct from A and B, the leftward
B/X inset alternative is impossible:

\[
                        x_B-x_X<g_B+g_X.                \tag{10}
\]

Indeed, its contrary and x_B+h_B<1/16 from the geometric reduction
give x_X+g_X<=x_B-g_B<1/16-(h_B+g_B)<=-15/16,
contradicting (L). This statement retains the original orientations
and is a strict necessary inequality, not an actual projection link.

This excludes one full height alternative of Cd402. It does not
exclude the whole original or the remaining unrestricted nine-square
caller.

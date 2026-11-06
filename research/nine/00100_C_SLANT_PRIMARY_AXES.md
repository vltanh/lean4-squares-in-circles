# C-slant: a hand elimination of all primary separating axes for negative D

This chapter proves one complete part of the C-slant argument. It retains
the original `001/00` physical caller at Q=1105/256, with the normalization
y_D-y_C>=2/3 and D's canonical tilt nonpositive. It proves that, in the
contrary half-plane

\[
                         y_C+\frac78x_C\ge-\frac7{32},          \tag{1}
\]

the C/D separator must be a positive secondary axis of C or D, and a
C-owned secondary axis is possible only when C's canonical tilt is
nonpositive. No primary axis, either original owner or either sign,
is possible. The positive-C primary alternative is excluded by a
67-rectangle rational hand table, printed in full below.

The secondary-axis alternatives are proved by the
[upper-G table](00100_C_SLANT_SECONDARY_AXES.md) and the
[complete lower-G complement](00100_C_SLANT_LOWER_COMPLEMENT.md).
Together the three chapters prove C-slant for nonpositive D without
importing the archived G-order or C-slant forests. No original cell
or mask is closed here.
The new exclusions do not import the archived C-slant, G-order or
tilt-toll tables. Their nontrivial input is the physical two-square cap
proved in [the foundation](FOUNDATION.md), Part B.

## 1. Original inputs and the cap transfer

Let h_S be the coordinate support halfwidth of an original S, and let
g_S=1/(4h_S). Put

\[
 d=x_D-x_C,\quad v=y_D-y_C,\quad
 h_C\ge1/2,\quad h_D\ge1/2.
\]

The original weak-cone link gives

\[
                   d\ge v\ge2/3,\qquad d<h_C+h_D.                \tag{2}
\]

The actual original links AB, BC, EF, FG and the center bound
|c_A|<rho=91/60 give

\[
                         x_C>h_C-1/60.                         \tag{3}
\]

Apply the physical left pair cap to A,E and use the two actual chains:

\[
 46(x_C-h_C)+\frac{27}{2}(x_G-h_G)\ge\frac{27}{4}.
\]

The physical right pair cap for D,G is

\[
 46(x_D-h_D)+\frac{27}{2}(x_G-h_G)\le\frac{211}{4}.
\]

Subtracting proves the exact **cap transfer**

\[
                         d\le1-h_C+h_D.                        \tag{4}
\]

Both pair caps are valid for any two disjoint original unit squares.
No order of y_G,y_D and no selected D/G separator is assumed here.
The remaining two originals H,I keep all their physical constraints in
the caller, although this implication does not need them.

Write D's frame as

\[
 u_D=(a,-b),\quad v_D=(b,a),\quad
 a\ge b\ge0,\quad a^2+b^2=1,
 \quad h_D=(a+b)/2,\quad k_D=(a-b)/2.
\]

Write C's frame as u_C=(A,sB), v_C=(-sB,A), where
A>=B>=0, A^2+B^2=1 and s in {-1,+1}; put
h_C=(A+B)/2 and k_C=(A-B)/2. The zero-angle face belongs to
both closed sign descriptions. Every actual side-normal separation of
C,D has the same support threshold R>=1.

## 2. The negative-C primary axis is impossible

Suppose s=-1 and u_C=(A,-B) separates toward D. The shared support
threshold satisfies

\[
                         R\ge1/2+A h_D-B k_D.
\]

This follows by taking one of the two signed lower bounds for the
absolute relative sine; both original orientations are retained.
Equation (4) then gives

\[
\begin{aligned}
 R-(A d-Bv)
 &\ge1/2-A+A h_C+B(v-k_D)\\
 &=1-A+B(k_C+v-k_D)>0                           \tag{5}
\end{aligned}
\]

when B>0, because v>=2/3 and k_D<=1/2. If B=0,
R=1/2+h_D and d<h_C+h_D=1/2+h_D already rules out u_C.
Thus this entire owner/sign alternative is impossible.

## 3. The D primary axis is impossible for either C sign

Suppose u_D=(a,-b) separates toward D. Its projection is a d-bv.

If C's tilt is nonnegative, the exact threshold is
R=1/2+a h_C+b k_C. From (4), h_C>=1/2 and k_C>=0,

\[
 R-(a d-bv)
 \ge1/2-a+a(2h_C-h_D)+b(k_C+v)
 \ge b(v-k_D)>0                               \tag{6}
\]

when b>0. For b=0, the strict weak bit gives d<h_C+1/2=R.

Suppose C's tilt is nonpositive. If h_C>=h_D, (4) gives d<=1,
so a d-bv<1<=R when b>0. If b=0 and C is nonaligned then
d<=3/2-h_C<1; the fully aligned case is excluded by d<1.

In the remaining case h_C<=h_D, C's absolute angle is at most D's.
Then A>=a and R=1/2+a k_C+b h_C. Hence

\[
\begin{aligned}
 R-(a d-bv)
 &\ge1/2-a+a(A-h_D)+b(h_C+v)\\
 &\ge\frac{(1-a)^2}{2}
       +b\left(\frac{1-a}{2}+v\right)>0.        \tag{7}
\end{aligned}
\]

The only zero possibility is a=1,b=0 and then C is aligned too;
the strict weak bit excludes it. Equations (6)--(7) exhaust C's
orientation and prove the assertion.

## 4. The other signed axes

For a nonpositive original tilt, the negative primary normal is
(-a,b). Its projection is -a d+bv<=(-a+b)d<=0. The negative
secondary normal has both components nonpositive. Neither can separate.

For a positive C tilt, -u_C has both components nonpositive.
The normal -v_C=(B,-A) has projection Bd-Av<1, since
d<h_C+h_D<=sqrt(2), B<=1/sqrt(2), and Av>0.
The positive secondary normal v_C=(-B,A) cannot separate either:

\[
 v_C\cdot(d,v)\le(A-B)d<(A-B)(h_C+h_D),
\]

whereas its threshold obeys

\[
 R-(A-B)(h_C+h_D)=B^2+B a\ge0.                 \tag{8}
\]

Here R=1/2+A h_D+B k_D because C and D have opposite
tilt signs. The aligned face B=0 is included by the strict inequality
in (2).

It remains only to exclude u_C when C's tilt is strictly positive
and (1) holds. All other potential primary or signed axes have now
been excluded without using (1).

## 5. Two necessary height and span bounds for positive u_C

Assume B>0, s=+1 and u_C separates toward D. In this case

\[
 A d+Bv\ge R=1/2+A h_D+B k_D.                  \tag{9}
\]

Using (4) in (9) gives

\[
 v\ge k_C+k_D+\frac{1-A}{B}.                  \tag{10}
\]

Indeed 1/2-A+A h_C=1-A+B k_C. Using v<=d in (9) gives

\[
 d\ge g_C+\frac a2+\frac{k_C}{2h_C}b.          \tag{11}
\]

These two bounds keep the same original frame variables. No angle
or gap is replaced by an independent square.

Use half-angle parameters w=tan(gamma/2) for C's positive angle
gamma, and z=tan(delta/2) for D's absolute angle delta. They satisfy

\[
 0<w\le\sqrt2-1,\qquad0\le z\le\sqrt2-1<5/12.
\]

For a nonnegative parameter t define the following rational functions:

\[
\begin{gathered}
 a(t)=\frac{1-t^2}{1+t^2},\qquad b(t)=\frac{2t}{1+t^2},\\
 h(t)=\frac{1+2t-t^2}{2(1+t^2)},\qquad
 k(t)=\frac{1-2t-t^2}{2(1+t^2)},\qquad
 J(t)=k(t)+t=\frac{1-t^2+2t^3}{2(1+t^2)}.
\end{gathered}                                                   \tag{12}
\]

On the canonical range, h increases, k decreases, and both
g=1/(4h) and lambda=k/(2h) decrease. The function J decreases
throughout [0,5/12]:

\[
 J'(t)=\frac{t(t^3+3t-2)}{(1+t^2)^2}\le0,
\]

since t<=1/2 implies t^3+3t-2<=-3/8. In particular J(t)<=1/2.
Equations (10)--(11) are

\[
                  v\ge J(w)+k(z),\qquad
 d\ge g(w)+a(z)/2+\lambda(w)b(z).              \tag{13}
\]

## 6. One rational rule for every table rectangle

Consider a closed rectangle [l,u] times [p,q] for w,z. Every lower
endpoint in the table is below sqrt(2)-1. Set

\[
 H=h(l),\quad K=\max\{k(q),0\},\quad
 V=\max\{2/3,J(u)+K\}.
\]

If u<2/5 set G=1/(4h(u)), L=k(u)/(2h(u)). For the last
horizontal band, which contains the canonical endpoint, set instead

\[
                         G=707/2000,\qquad L=0.
\]

These are lower bounds for g(w),lambda(w):
707/2000<1/(2sqrt(2)) follows from 707^2<500000.
The deliberate weaker choice also avoids using monotonicity of h
beyond its canonical endpoint.

Define the rational numbers

\[
\begin{aligned}
 Z&=\max\{V,\ G+\min(a(p)/2+L b(p),a(q)/2+L b(q))\},\\
 \ell&=H-1/60,\qquad D_0=Z+h(p),\qquad B_0=V+K-7/32,\\
 X&=\ell+D_0,\qquad Y=\max\{B_0-(7/8)\ell,0\}.
\end{aligned}                                                   \tag{14}
\]

The endpoint minimum is valid because a(z)/2+L b(z) is a
nonnegative linear combination of cosine and sine of delta, hence
concave on the enlarged angle interval. Thus (13) gives v>=V
and d>=Z. All bounds are simultaneous necessary bounds on the
originals.

The upper-right original corner of D has coordinates
(x_C+d+h_D,y_C+v+k_D). From (1) and (3), its squared norm is at least

\[
 f(x_C):=(x_C+D_0)^2+
             \max\{B_0-(7/8)x_C,0\}^2,
 \qquad x_C>\ell.
\]

The function f increases for x>=ell. To check this directly,
ell>=29/60, D_0>=7/6, and B_0<=41/32, since V<=1 and K<=1/2.
Where the positive part is nonzero,

\[
 f'(x)/2\ge29/60+7/6-(7/8)(41/32)=677/1280>0.
\]

Where it is zero the derivative is positive immediately. Therefore

\[
                            Q\ge X^2+Y^2.                     \tag{15}
\]

This last pair X,Y consists of lower-bound expressions at ell;
they are not asserted to be the two coordinates of D's actual corner.

## 7. Complete 67-rectangle hand table

Let I_i=[5i/96,5(i+1)/96], i=0,...,7. Rows give the band for w;
columns give the band for z. The entry (m,n) means that direct
substitution in the rational expressions (12)--(14) gives
X>=m/1000 and Y>=n/1000. Every entry is thus an elementary rational
comparison with positive denominators. The last column is a lower bound
for m^2+n^2 over the displayed entries of its row.

| w band / z band | I_0 | I_1 | I_2 | I_3 | I_4 | I_5 | I_6 | I_7 | Row minimum |
|---|---|---|---|---|---|---|---|---|---:|
| I_0 | See the four subrectangles | (2027,628) | (2103,503) | (2167,373) | (2216,240) | (2253,151) | (2276,85) | (2282,25) | 4503113 |
| I_1 | (1968,696) | (2035,578) | (2103,452) | (2158,323) | (2201,190) | (2230,108) | (2242,42) | (2242,0) | 4357440 |
| I_2 | (2000,648) | (2046,529) | (2107,404) | (2156,274) | (2192,142) | (2211,70) | (2217,5) | (2212,0) | 4419904 |
| I_3 | (2024,603) | (2058,485) | (2114,360) | (2156,230) | (2182,105) | (2195,38) | (2196,0) | (2188,0) | 4460185 |
| I_4 | (2039,563) | (2070,445) | (2119,320) | (2152,190) | (2172,79) | (2180,13) | (2178,0) | (2165,0) | 4474490 |
| I_5 | (2047,530) | (2078,411) | (2119,286) | (2146,156) | (2161,59) | (2166,0) | (2159,0) | (2144,0) | 4471109 |
| I_6 | (2049,503) | (2081,384) | (2115,259) | (2138,129) | (2149,46) | (2149,0) | (2140,0) | (2121,0) | 4451410 |
| I_7 | (2046,483) | (2079,365) | (2109,240) | (2128,110) | (2135,38) | (2132,0) | (2119,0) | (2097,0) | 4397409 |

The rectangle I_0 times I_0 is replaced by its four closed halves.
Put J_0=[0,5/192], J_1=[5/192,5/96] and use the same formulas:

| w band / z band | J_0 | J_1 |
|---|---|---|
| J_0 | (1959,804) | (2007,748) |
| J_1 | (1979,780) | (2009,724) |

Their squared sums are respectively 4484097, 4587553, 4524841 and
4560257. The smallest squared sum anywhere in the complete table is
4357440, at (1968,696). Its positive reserve is

\[
              \frac{4357440}{1000000}-Q
                          =\frac{32827}{800000}>0.             \tag{16}
\]

For an explicit check of the tightest table entry, (14) at I_1 times
I_0 gives

\[
 X=\frac{3388997063}{1721783120}>\frac{1968}{1000},
 \quad Y=\frac{1198945203}{1721783120}>\frac{696}{1000}.
\]

Each other entry uses exactly the same rational rule. The table covers
the entire canonical rectangle, since sqrt(2)-1<5/12. The portions
beyond the canonical endpoint merely enlarge the bounding intervals;
they do not add physical orientation assumptions. All shared faces
are retained. There are 63 unchanged rectangles and four replacing
subrectangles, hence 67 in all.

Equations (15)--(16) contradict each other on every rectangle. This
excludes the complete positive-C primary-axis alternative under (1).

## 8. Exact outcome and assembly with the secondary-axis proof

Combining Sections 2--7 gives this complete necessary alternative in
the original contrary domain (1):

| Sign of C's canonical tilt | Remaining possible C/D axes toward D |
|---|---|
| Nonpositive | v_C=(B,A) or v_D=(b,a) |
| Nonnegative | v_D=(b,a) only |

The zero-angle boundary may appear in both rows. It loses no physical
axis. Every excluded axis was handled either by its full continuous
inequality or by the complete closed table above.

These complete secondary-axis callers, retaining the original D/G
physical pair, original corner containment and actual-chain cap
inequalities, are excluded in the two linked chapters. The lower-G
chapter supplies their acyclic assembly. Neither a C-slant conclusion
nor a G-order conclusion has been assumed in this primary-axis
reduction. The unrestricted nine-square proof and every whole-original
closure remain open.

Computer exploration suggested the reduction and the rational bands.
The delivered proof consists of the displayed physical deductions,
rational formulas and all table entries; no numerical optimizer,
external certificate or replay is a proof premise. The arithmetic has
been checked locally with exact fractions. No independent review,
Lean, Lake, CI or kernel verification is claimed.

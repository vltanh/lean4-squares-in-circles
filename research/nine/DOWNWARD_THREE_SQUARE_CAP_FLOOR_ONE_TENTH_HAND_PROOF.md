# The downward three-square transfer cap with whole floor one tenth

November 1, 2026 (America/Chicago; November 2 UTC). Reconstructed complete
hand proof of the explicitly conditional transfer theorem. Every scalar
range and coefficient identity is displayed below. No mathematical program,
sampled orientations, Lean, Lake, or CI is used. This file has no dependency
on an unarchived earlier downward-transfer manuscript.

Put

\[
 Q=\frac{1105}{256},\quad r=\frac{\sqrt{1105}}{16},\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},
 \quad T=\frac{211}{4}.
\]

## 1. The exact physical statement

Let M,A,B be pairwise interior-disjoint physical unit squares. Suppose
M and A lie in the centered disk of radius \(R\le r\), and A is
actually above M:

\[
                         y_A-y_M\ge h_A+h_M.
\tag{1}
\]

Suppose the physical A,B pair has a separating unit normal pointing
right and downward,

\[
 n=(p,-s),\quad p>0,\quad s\ge0,\quad p^2+s^2=1,
 \qquad
 n\cdot(c_B-c_A)\ge H_A(n)+H_B(n).
\tag{2}
\]

Finally suppose B lies wholly above the line y=1/10:

\[
                              y_B-h_B\ge\frac1{10}.
\tag{3}
\]

Then

\[
               a(-x_M-h_M)+b(1-x_B-h_B)\le T.
\tag{4}
\]

The inequality is strict if R<r or if s>0. No A,B coordinate projection
separation is assumed. Disk containment of B is not needed in this
three-square inequality; its stated whole floor is the condition used
for that square.

The hypothesis (1) remains an actual projection comparison. This note
does not replace it by arbitrary physical nonoverlap between M and A.

## 2. The retained support reduction

Set \(t=bs/p\ge0\). Combining k times (1) with b/p times (2), use
the three support vectors

\[
 (-a,-k),\qquad(-b,k+t),\qquad(0,-t).
\]

Multiplying (1) by k and the unnormalized (2) by b, and adding the
disk support inequalities in the first two displayed vector directions,
gives

\[
\begin{aligned}
 a(-x_M-h_M)+b(-x_B-h_B)
 \le{}&R\left(\sqrt{a^2+k^2}+\sqrt{b^2+(k+t)^2}\right)
       -\frac t{10}\\
 &-P_M-P_A-P_B,
\end{aligned}
\tag{5}
\]

where

\[
 P_M=(a+k)h_M+H_M((a,k))\ge a+k,
\]

\[
 P_B=(b+t)h_B+H_B((b,-t))\ge b+t,
\]

\[
 P_A=k h_A+H_A((b,-t))+H_A((-b,k+t)).
\]

The first two inequalities follow from
\((u+v)h+H((\pm u,\pm v))\ge u+v\) for nonnegative u,v, using
the contained aligned square of halfwidth \(g=1/(4h)\) and h+g>=1.
The expression P_A is the sum of the side lengths of the bounding
rectangle of the triangle with vertices \(0,(b,-t),(0,k)\), measured
in A's physical frame. The elementary edge-alignment minimum gives

\[
 P_A\ge\min\{E(t),N(t),D(t)\},
\]

\[
 E=b+k+t,\qquad
 N=L_1+\frac{k(b+t)}{L_1},\quad L_1=\sqrt{b^2+t^2},
\]

\[
 D=L_2+\frac{bk}{L_2},\quad L_2=\sqrt{b^2+(k+t)^2}.
\tag{6}
\]

For completeness, between successive changes in the projected extreme
vertices, a triangle's bounding-rectangle side sum is a positive
expression U cos(theta)+V sin(theta), whose second derivative is its
negative. It is concave, so a minimum occurs when a triangle edge is
parallel to a rectangle side. The three edges give exactly (6).

At t=0 one has L_2=9r and the exact identity

\[
 r\left(\sqrt{a^2+k^2}+9r\right)-(a+b+2k)=T.
\]

Consequently (5) proves (4) if all three branches satisfy

\[
 r(L_2-9r)\le m(t)-(b+k)+\frac{11}{10}t,
 \qquad m\in\{E,N,D\},\quad t\ge0.
\tag{7}
\]

The remaining sections prove all three scalar branches directly.

## 3. The E branch

The derivative of L_2 with respect to t is below one. Hence for t>0,

\[
 r(L_2-9r)<rt<\frac{21}{10}t
                 =E(t)-(b+k)+\frac{11}{10}t,
\]

where \(r<25/12<21/10\). At t=0 both sides are zero. This proves
the branch, strictly away from zero.

## 4. The D branch

Put

\[
 \mu=\frac{k}{b}=\frac{23}{24},\qquad
 z=t/b,\qquad w=\mu+z,\qquad L=\sqrt{1+w^2}.
\]

The exact normalization
\(r\sqrt{1+\mu^2}-(1+\mu)=353/384\) turns the D branch into

\[
 (r-1)L-\frac\mu L-\frac{11}{10}(w-\mu)
                                  \le\frac{353}{384}.
\tag{8}
\]

On \(\mu\le w\le21/20\), L<=29/20. Dropping the nonpositive last
term and using r<133/64 bounds the left side strictly from above by

\[
 \frac{69}{64}\frac{29}{20}-\frac{23}{24}\frac{20}{29}
 =\frac{2001}{1280}-\frac{115}{174}<\frac{353}{384}.
\]

For the last comparison it suffices to check
\(2473/3840<115/174\), or \(430302<441600\).

For w>=21/20, use \(L\le w+1/(2w)\). The expression
\((r-1)L-\mu/L\) increases in L, so the left side of (8) is
strictly smaller than

\[
 \frac{253}{240}-\frac{7w}{320}+\frac{69}{128w}
                         -\frac{2\mu w}{2w^2+1}.
\]

After multiplication by the positive denominator
\(1920w(2w^2+1)\), this last expression being at most 353/384 is
exactly

\[
 P_D(w):=84w^4-518w^3+1652w^2-259w-1035\ge0.
\tag{9}
\]

Here

\[
 P_D''(w)=1008w^2-3108w+3304>0
\]

for every real w, since its discriminant is −3662064. Also
\(P_D'(1)=1827>0\), so P_D is increasing on [1,infinity), and

\[
                     P_D(21/20)=\frac{673311}{40000}>0.
\]

This proves (9) and (8). The D branch is strict everywhere.

## 5. The N branch and its exact square identity

With \(z=t/b\), \(\mu=23/24\), and \(L=\sqrt{1+z^2}\), the
N branch is equivalent to

\[
 r\sqrt{1+(z+\mu)^2}
 \le L+\frac{\mu(1+z)}L+\frac{11}{10}z+\frac{353}{384}.
\tag{10}
\]

Define

\[
 P=24z^2+23z+47,\qquad T_1=2112z+1765,
 \qquad U=576z^2+1104z+1105,
\]

\[
 J=506880z^3+909360z^2+1398590z+829550,
\]

\[
 K=485316z^4+998565z^3+1314866z^2+575365z+829550.
\]

The right side of (10) is the positive quantity
\((80P+T_1L)/(1920L)\). Squaring the two positive sides reduces (10)
to the exact identity and inequality

\[
 (80P+T_1L)^2-27625(1+z^2)U=16(JL-K)\ge0.
\tag{11}
\]

An explicit coefficient check is J=10PT_1. The five coefficients of
\(27625(1+z^2)U-6400P^2-T_1^2(1+z^2)\), in descending order,
are

\[
 7765056,\quad15977040,\quad21037856,\quad9205840,
 \quad13272800,
\]

which are sixteen times the displayed coefficients of K. Thus (11)
is a finite displayed multiplication identity.

### 5.1. The interval 0<=z<=1/2

We have

\[
 K-J=z(485316z^3+491685z^2+405506z-823225).
\]

The cubic in parentheses increases for z>=0, and its value at 1/2 is
\(-1747545/4<0\). Consequently K<=J<=JL, strictly when z>0.
At zero equality holds.

### 5.2. The interval 1/2<=z<=2

Use \(L\ge(3+4z)/5\), obtained by taking the scalar product of
(1,z) with the unit vector (3/5,4/5). Direct multiplication gives

\[
\begin{aligned}
 F(z):=(3+4z)J-5K
 ={}&-399060z^4+165255z^3+1748110z^2\\
    &+4637145z-1659100.
\end{aligned}
\tag{12}
\]

Since z^2<=4, this is at least

\[
 165255z^3+151870z^2+4637145z-1659100>0.
\]

Indeed the final two terms alone are at least 1318945/2>0 for
z>=1/2. Hence JL>K on this interval.

### 5.3. The interval 2<=z<=3

Keep the same tangent-line bound and polynomial F from (12). Its
second derivative is

\[
 F''(z)=-4788720z^2+991530z+3496220.
\]

It is negative at z=2, with value −13675600, and decreases thereafter
because \(F'''(z)=-9577440z+991530<0\). Thus F is concave on [2,3].
Its two endpoint values are

\[
                          F(2)=9544710,
                \qquad    F(3)=123350,
\]

both positive. Concavity proves F>0 throughout this interval, and again
JL>K.

### 5.4. The half-line z>=3

Use L>=z. The polynomial in this comparison is

\[
 zJ-K=21564z^4-89205z^3+83724z^2+254185z-829550.
\]

Writing w=z−3>=0 gives the exact expansion

\[
 zJ-K=21564w^4+169563w^3+445335w^2+676906w+24670>0.
\tag{13}
\]

Thus JL>K on the entire remaining half-line. All four ranges prove
(10), strictly when t>0.

## 6. Conclusion and the retained geometric premise

All three scalar branches of (7) hold. Formula (5) therefore proves
the transfer cap (4). If R<r, the positive sum of the two disk-support
lengths makes the reduction strict. If s>0, then t>0 and every scalar
branch is strict. If s=0, the physical separator is horizontal and
A,B already have an actual x-projection comparison.

The proof supplies the conditional floor-1/10 transfer. Its geometric
hypotheses must be independently established by any caller; no unproved
routing or main-height assertion is imported here. The shoulder-to-main
comparison (1) still has to be proved in the caller. A shoulder requiring an oblique separator
from its main endpoint is not covered by silently replacing (1) with
physical nonoverlap. Nor does this note address the opposite upward
sign of the A,B separator; that sign has its own support argument.

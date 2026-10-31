# A center radius of 93/100 gives an inner arc longer than 45 degrees

Date: October 26, 2026.

**Status: accepted complete analytic strengthening after full-source reviews in
REVIEW_DIAGONAL_CHANNEL_CAP_AND_93_ARC_ROOT_2026_10_26.md and
REVIEW_DIAGONAL_CHANNEL_CAP_AND_93_ARC_BLOCK_2026_10_26.md.**
It changes only the center threshold and the last scalar comparison in the
already accepted whole-orientation proof ANNULAR_CENTER_ARC_AT_23_25.md.
No finite angle or position cover is added.

Put
\[
Q=\frac{1105}{256},\qquad r=\frac54.
\]
Let \(S\subseteq D_{\sqrt Q}\) be any actual closed unit square whose
center \(C\) satisfies
\[
|C|\ge\frac{93}{100}.
\tag{1}
\]

**Theorem.** The intersection \(S^\circ\cap\{|p|=r\}\) is one connected
open arc, contains the radial-center point \(rC/|C|\), and has angular
length strictly greater than \(\pi/4\).

There is no circle-contact, load, frame or cap premise.

## 1. Exact original arc domain

Since \(93/100>23/25\), every hypothesis of
ANNULAR_CENTER_ARC_AT_23_25.md holds. In particular the full connected
arc and radial-center-point conclusions of that proof apply unchanged.
We strengthen its length comparison.

In the own frame used there, write
\[
C=(x,y),\qquad x\ge y\ge0,\qquad
a=x+\frac12,\quad b=y+\frac12,\quad
A=a-1,\quad B=b-1.
\]
Then
\[
S=[A,a]\times[B,b],\qquad a\ge b\ge\frac12,
\qquad a^2+b^2\le Q,\qquad
k^2:=x^2+y^2\ge(93/100)^2.
\tag{2}
\]

For \(a>r\), Section 3 of the cited proof already gives both possible
arc lengths strictly greater than \(\pi/4\). Its fixed whole-domain
inequalities
\[
A^2+B^2+\sqrt2\,AB<\frac{25}{32},
\qquad \sqrt2 A+B>0
\]
are valid throughout the weaker domain \(|C|\ge23/25\); the exact
interval is
\[
[\arcsin(B/r),\ \min\{\arccos(A/r),\arcsin(\min(b/r,1))\}].
\]
Its inner-face and opposite-face-strip lengths both exceed \(\pi/4\),
with all endpoint cases included. Thus only \(a\le r\) remains.

## 2. The sole sharpened outer-face comparison

For \(a\le r\), one has \(0<A,B\le1/4\). The exact closed intersection
is the interval
\[
\left[
\max\{\arccos(a/r),\arcsin(B/r)\},
\ \min\{\arccos(A/r),\arcsin(b/r)\}
\right].
\tag{3}
\]
The two opposite-face-strip differences are at least
\(2\arcsin(2/5)>\pi/4\). The inner-inner difference is at least
\(\pi/2-2\arcsin(1/5)>\pi/4\). These are the unchanged exact
comparisons in Section 2 of the cited proof.

For the remaining outer-outer difference put
\[
L=\arcsin((x+1/2)/r)+\arcsin((y+1/2)/r)-\pi/2.
\]
At fixed \(k^2=x^2+y^2\), with \(x\ge y>0\) and \(x,y\le3/4\),
the sign of its derivative away from the diagonal is the sign of
\[
\begin{split}
&y^2\{r^2-(y+1/2)^2\}
-x^2\{r^2-(x+1/2)^2\}\\
&\quad=(x-y)\left[(x+y)(k^2-21/16)+k^2+xy\right].
\end{split}
\tag{4}
\]
All derivative terms squared in obtaining this sign are positive on
the open interval. Here \(4/5<k^2\le9/8\) and \(x+y\le3/2\),
so the bracket is greater than
\[
\frac32\left(\frac45-\frac{21}{16}\right)+\frac45
=\frac1{32}>0.
\]
Thus \(L\) is nondecreasing away from the diagonal. The diagonal
belongs to the same connected fixed-\(k\) domain. Continuity handles
\(a=r\) or \(b=r\), where a derivative can be unbounded.

The diagonal value increases with \(k\). Therefore (1) gives
\[
L\ge
2\arcsin\left(\frac{100+93\sqrt2}{250}\right)-\frac\pi2.
\tag{5}
\]
The argument is strictly greater than \(\cos(\pi/8)\).
Both quantities are positive, and their squared comparison, after
multiplication by \(250000\), is
\[
4(100+93\sqrt2)^2-62500(2+\sqrt2)
=11900\sqrt2-15808
>11900\frac75-15808=852>0.
\tag{6}
\]
Consequently the right side of (5) is greater than
\[
2\left(\frac{3\pi}{8}\right)-\frac\pi2=\frac\pi4.
\]
All four differences defining (3) now exceed \(\pi/4\). Its open
interval lies in \(S^\circ\), proving the theorem.

The full continuity, clipping, connectedness and radial-direction
claims are the same exact ones in the original accepted proof. No
square is moved, and no original containment radius is enlarged.
In particular two actual interior-disjoint units satisfying (1)
cannot both have their open inner-circle arcs routed into one
interval of angular length at most \(\pi/2\).


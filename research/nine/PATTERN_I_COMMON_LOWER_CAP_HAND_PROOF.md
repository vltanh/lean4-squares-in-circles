# Pattern I: a common lower square closes a range of separating directions

Hand proof, November 1, 2026. No mathematical scripts, Lean, or CI.

This note proves a sharp three-square cap and its actual Pattern I caller.
It closes the stated separating-normal range, not every Pattern I case.

## 1. Statement and constants

Put
\[
 Q=\frac{1105}{256},\qquad r=\frac{\sqrt{1105}}{16},\qquad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},
 \quad T=\frac{211}{4}.
\]
The identities used below are
\[
 \sqrt{a^2+k^2}=23r,\qquad \sqrt{b^2+k^2}=9r,
 \qquad32r^2-(a+b+2k)=T.                                \tag{1}
\]
Let L,A,B be physical unit squares with disjoint open interiors. L and
A lie in the centered disk of radius at most r. Write h_S for either
coordinate projection halfwidth and H_S for the centered support function.
Assume the actual vertical comparisons
\[
                 y_A-y_L\ge h_A+h_L,
 \qquad          y_B-y_L\ge h_B+h_L.                     \tag{2}
\]
Suppose a physical separating normal for A,B points right and down:
\[
 n=(p,-s),\quad p>0,\quad s\ge0,\quad p^2+s^2=1,
\]
\[
 n\cdot(c_B-c_A)\ge H_A(n)+H_B(n).                       \tag{3}
\]
If
\[
                              \frac{s}{p}\le\frac{27}{46},
                                                               \tag{4}
\]
then
\[
                 b(-x_L-h_L)+a(1-x_B-h_B)\le T.          \tag{5}
\]
This is strict whenever s>0 or the containing radius is below r.
For a genuine coordinate-exceptional pair, s=0 is impossible: (3) would
then be an actual x-separation.

For every physical square, put \(g=1/(4h)\). Its inscribed aligned
square of halfwidth g and \(h+g\ge1\) give the universal support bound
\[
        (u+v)h+H((\pm u,\pm v))\ge u+v\qquad(u,v\ge0). \tag{6}
\]

## 2. Small slopes: cancel the third center support exactly

Put \(t=as/p\), so (4) says \(0\le t\le27\). First assume
\(0\le t\le k\). Multiply the first and second comparisons in (2)
by \(k-t\) and t, respectively, and multiply (3) by \(a/p\).
The center terms combine with just two disk support vectors,
\((-b,-k)\) on L and \((-a,k)\) on A. The vector on B is zero.
Explicitly, their combined center expression is
\[
 -b x_L-a x_B+(k-t)(y_A-y_L)+t(y_B-y_L)
                  +a(x_B-x_A)-t(y_B-y_A)
 =-b x_L-k y_L-a x_A+k y_A.
\]
Consequently
\[
 \begin{aligned}
 b(-x_L-h_L)+a(-x_B-h_B)
 \le{}&r\left(\sqrt{b^2+k^2}+\sqrt{a^2+k^2}\right)
       -P_L-P_A-P_B,                                    \tag{7}
 \end{aligned}
\]
where
\[
 P_L=(b+k)h_L+H_L((-b,-k))\ge b+k,
\]
\[
 P_A=(k-t)h_A+H_A((a,-t))+H_A((-a,k)),
\]
\[
 P_B=(a+t)h_B+H_B((a,-t))\ge a+t.                       \tag{8}
\]
The displayed lower bounds follow from (6).

The quantity P_A is the sum of the side lengths of the bounding
rectangle of the triangle with vertices
\[
                         0,\quad(a,-t),\quad(0,k-t)
\]
in A's physical frame. Indeed the three vectors whose supports occur
in P_A are \((0,t-k),(a,-t),(-a,k)\), whose sum is zero. For any three
real numbers with sum zero, half
the sum of their absolute values is the range of the three corresponding
partial sums. Apply that identity in each frame coordinate.

The rectangle side-length sum has a minimum with one triangle edge
parallel to a frame axis. To verify this, partition the orientation circle
at changes of a projected extreme vertex. On each interval the sum is a
positive expression \(U\cos\theta+V\sin\theta\), whose second
derivative is its negative. There is no interior minimum; at an interval
endpoint an edge is parallel to a frame axis.

Write \(L_1=\sqrt{a^2+t^2}\) and \(L_0=\sqrt{a^2+k^2}\). The three
edge choices give
\[
 E=a+k,\qquad
 N=L_1+\frac{(k-t)(a+t)}{L_1},\qquad
 D=L_0+\frac{a(k-t)}{L_0}.                               \tag{9}
\]
All are at least \(a+k-t\). For N use \(L_1\ge a\) and
\((a+t)/L_1\ge1\). For D put \(v=k-t\in[0,k]\); then
\[
 D-a-v=(L_0-a)\left(1-\frac v{L_0}\right)>0.
\]
E has surplus t. For t>0, N is also strictly greater than the desired
bound because \(L_1>a\). Thus
\[
             P_A\ge a+k-t,
 \quad\text{strictly if }t>0.                            \tag{10}
\]
At t=k the triangle is a segment; the same formulas apply by continuity.

Insert (8)--(10) into (7), and add a. Identities (1) give (5), strictly
for positive t. If the containing radius is below r, the positive sum
of the two disk support lengths supplies strictness independently.

## 3. The remaining slopes up to 27/46

For \(k\le t\le27\), use only t times the second comparison in (2)
and \(a/p\) times (3). The disk vectors are now \((-b,-t)\) on L
and \((-a,t)\) on A; B's vector is again zero. The resulting penalties
are bounded by
\[
 (b+t)h_L+H_L((-b,-t))\ge b+t,
\]
\[
 2H_A((a,-t))\ge\sqrt{a^2+t^2},
\]
\[
 (a+t)h_B+H_B((a,-t))\ge a+t.
\]
The middle bound follows because a physical unit square contains the
radius-1/2 disk. Therefore the left side of (5) is at most
\[
 F(t):=r\sqrt{b^2+t^2}+(r-1)\sqrt{a^2+t^2}-2t-b.        \tag{11}
\]
This function is convex: both square-root terms have positive second
derivative and positive coefficients. Its maximum on [k,27] is thus
bounded by the larger endpoint value.

At the first endpoint, (1) gives
\[
                F(k)=T+a-\sqrt{a^2+k^2}<T.
\]
At the other endpoint, use the exact rational bounds
\[
 r<\frac{133}{64},\qquad
 \sqrt{b^2+27^2}=\frac{27\sqrt5}{2}<\frac{483}{16},
 \qquad\sqrt{a^2+27^2}=\sqrt{2845}<\frac{2667}{50}.
\]
Their squared checks are respectively
\(17689>17680\), \(161^2>5\cdot72^2\), and
\(2667^2>2845\cdot50^2\). Consequently
\[
 F(27)<\frac{133}{64}\frac{483}{16}
        +\frac{69}{64}\frac{2667}{50}-\frac{135}{2}
       =\frac{1350159}{25600}
       =T-\frac{241}{25600}<T.
\]
Convexity proves (5) strictly throughout this remaining interval.

## 4. The actual Pattern I caller

Use the normalized nine-square rows from
[PATTERN_I_NINE_SQUARE_CONTINUATION.md](PATTERN_I_NINE_SQUARE_CONTINUATION.md).
They give the actual comparisons
\[
 L<_yA,\quad L<_yB,\quad R<_yD,
 \qquad B<_xC<_xD,\quad L<_xM<_xR.                      \tag{12}
\]
The common-lower cap applies to L,A,B if their physical separator meets
(3)--(4). An ordinary two-square support calculation in directions
\((a,k)\) on D and \((b,-k)\) on R gives
\[
                       a(x_D-h_D)+b(x_R-h_R)\le T.       \tag{13}
\]
To verify (13), multiply their actual y-separation by k, subtract the
endpoint halfwidth terms, and apply (6). The bound is
\(r(23r+9r)-(a+b+2k)=T\), exactly (1).

But the actual horizontal comparisons in (12) imply
\[
 (x_D-h_D)-(x_B+h_B-1)\ge1+2h_C\ge2,
\]
\[
 (x_R-h_R)-(x_L+h_L)\ge2h_M\ge1.
\]
Adding (5) and (13) would therefore give
\[
                       2a+b\le2T.
\]
The constants satisfy \(2a+b=2T=211/2\), while (5) is strict for a
genuine exceptional pair satisfying (3)--(4). This is a contradiction.
Thus the entire stated separator subcase is excluded even at q=Q.

This does not claim that every physical exceptional pair has a normal
in (4). Steeper downward normals and upward normals require further
arguments. The exact eight-square obstruction has a different separating
geometry and is not contradicted by this terminal.

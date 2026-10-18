# 0011011: the whole negative core-to-negative outer edge-2 transition

## Theorem

Let edge 2 have a negative core source and negative outer target.
For either piece of the core boundary, every retained separating axis,
and every
\[
 \pi/2-.7\le\phi\le\pi/2+.7,
\]
the corrected cost is strictly greater than \(\gamma=.89765\).
Reflected reversal also gives the edge-6 partner.

This is a whole-angle theorem. It uses elementary derivative bounds,
one strongly convex scalar, and 38 fixed rational comparisons.
There is no polynomial table, minimizing search, or domain subdivision.

Set
\[
 Q=3.9156,\quad a_c=7/12,\quad
 d=\sqrt{Q/2}-1/2,\quad d_c=1/2+\sqrt2/24,\quad
 a_0=\sqrt{Q-1/4}-1/2.
\]
The source coordinates obey
\(0\le b\le d_c,\ d_c\le a\le a_c\).
The outer target obeys
\[
 A=A(B)=\sqrt{Q-(B+1/2)^2}-1/2,\qquad0\le B\le d.
\]
These bounds include the full core side and corner.
Both actual own-frame centers are \((a,+b),(A,+B)\).

The exact labels are
\[
 C_2^-(b)=.00125+hb,\quad h=1.03981,
\]
\[
 T(B)=.01670+2.42322B-.91744B^2-.95769AB.
\tag{1}
\]
Thus the corrected cost is
\[
 C=\phi-.00125-hb+T(B).
\tag{2}
\]
Writing \(s=\sin\phi,c=\cos\phi\) and \(W=(1+s+|c|)/2\),
the four separating margins are
\[
\begin{array}{c|l}
1&-b+As+Bc-W\\
2&-ac-bs+A-W\\
3&as-bc+B-W\\
4&a-Ac+Bs-W.
\end{array}
\tag{3}
\]

## 1. Global target-label bounds

Put \(r=(B+1/2)/(A+1/2)\), so \(A'=-r\), and write \(D=T'\).
Direct differentiation gives
\[
\begin{aligned}
 D&=2.42322-1.83488B-.95769A+.95769Br,\\
 D'&=-1.83488+.95769(2r+Br'),\\
 D''&=.95769\left(\frac{3Q}{(A+1/2)^3}
             +\frac{3BQ(B+1/2)}{(A+1/2)^5}\right)>1.38.
\end{aligned}
\tag{4}
\]
The last bound follows from \(A+1/2<2\) and
\(3(.95)(3.9)/8>1.38\).

Fixed radical comparisons at \(B=.6\) give
\[
 D(.6)>.6101,\qquad -.049<D'(.6)<0.
\]
The integrated tangent lower bound for (4) therefore yields
\[
 D(B)>.6101-\frac{(.049)^2}{2.76}>.609.
\tag{5}
\]
In particular \(T\) increases and \(T(B)\ge T(0)=.01670\).

Convexity of \(D\) bounds it above by its maximum endpoint value.
Both endpoints satisfy \(D(0),D(d)<1.069\); hence
\[
 .609<T'(B)<1.069\quad(0\le B\le d).
\tag{6}
\]
We also use the direct geometric bounds
\[
 .899<d<.9,\quad .5589<d_c<.559,\quad a_0<1.415,\quad
 .261<r\le1.
\tag{7}
\]

Every pair with \(\phi\ge1.47\), independently of its axis, now has
\[
 C\ge1.47-.00125-hd_c+.01670>.904>\gamma.
\tag{8}
\]
It remains only to consider
\[
 \ell:=\pi/2-.7\le\phi\le1.47<\pi/2.
\tag{9}
\]
On this range \(s>.764,c<.645\), and \(s>c>0\).

## 2. Source transverse axis

Axis 1 gives \(b\le As+Bc-W\). Substituting this upper bound for
the negatively weighted source coordinate in (2) gives
\[
 C\ge\phi-.00125+T(B)-hAs-hBc+hW.
\tag{10}
\]
Its derivative in \(B\) is \(T'(B)+hrs-hc\), which by (6)--(7)
exceeds
\[
 .609-h\{.645-.261(.764)\}>0.
\tag{11}
\]
Thus its minimum is bounded by setting \(B=0,A=a_0\), whether or
not that endpoint itself is a feasible contact.

Both axes 1 and 2 will be bounded by the scalar
\[
 F_1(\phi)=\phi+.01545+\frac h2+\frac h2\cos\phi
                    -h(a_0-.5)\sin\phi.
\tag{12}
\]
It has
\[
 F_1''=h\{(a_0-.5)\sin\phi-\tfrac12\cos\phi\}>.39
\]
throughout (9), by the left endpoint comparison.
At the one rational angle \(\phi=.9\),
\[
 F_1(.9)>1.0136,\qquad |F_1'(.9)|<.0017.
\]
Therefore integration of the curvature bound and completing a square
prove
\[
 F_1(\phi)>1.0136-\frac{(.0017)^2}{.78}>1.013>\gamma.
\tag{13}
\]
Equations (10)--(13) cover all axis-1 states.

## 3. Target primary axis

Using \(a\ge d_c\), axis 2 gives
\[
 b\le\frac{A-d_c\cos\phi-W}{\sin\phi}.
\]
The resulting lower cost has derivative
\(T'(B)+hr/\sin\phi>0\) in \(B\), so again set \(B=0\).
The scalar lower bound is
\[
 F_2(\phi)=
 \phi+.01545+\frac h2+
 h\{(d_c+.5)\cot\phi-(a_0-.5)\csc\phi\}.
\tag{14}
\]
Subtracting (12) gives
\[
 F_2-F_1
 =h\frac{\cos\phi}{\sin\phi}
   \{d_c+.5-\tfrac12\sin\phi-(a_0-.5)\cos\phi\}.
\tag{15}
\]
The fixed norm comparison
\[
 (d_c+.5)^2>\frac14+(a_0-.5)^2
\]
and Cauchy's inequality make the expression in braces strictly positive.
Thus \(F_2>F_1>\gamma\). The argument covers source points on either
core piece; it only used the uniform bound \(a\ge d_c\).

## 4. Target transverse axis

Axis 3 and \(a\le a_c\) imply
\[
 B\ge B_0(\phi)+b\cos\phi,\qquad
 B_0(\phi)=\frac12+\frac12\cos\phi-\frac1{12}\sin\phi.
\tag{16}
\]

For \(\ell\le\phi\le.95\), \(B_0\) decreases, and the fixed
comparisons give \(B_0>.7226,\cos\phi>.581\).
Since \(B\le d<.9\), (16) forces
\[
 b<\frac{.9-.7226}{.581}<.306.
\]
Using \(T(.7226)>.5579\) and (2),
\[
 C>\ell-.00125-h(.306)+.5579>1.109>\gamma.
\tag{17}
\]

For \(.95\le\phi\le1.47\), drop the nonnegative \(b\cos\phi\)
term from (16) and use \(b\le d_c\):
\[
 C\ge F_3(\phi):=\phi-.00125-hd_c+T(B_0(\phi)).
\tag{18}
\]
Here \(5/12\le B_0<d\), so all label bounds apply. From (6),
\[
 F_3'
 =1+T'(B_0)\{-\tfrac12\sin\phi-\tfrac1{12}\cos\phi\}
 >1-1.069(7/12)>0.
\]
The endpoint comparison \(F_3(.95)>.9258\) therefore closes this
whole later range.

## 5. Source primary axis

Because \(A\ge B\), \(a\le a_c\), and \(s>c\), axis 4 requires
\[
 0\le a-Ac+Bs-W
 \le a_c-\frac12+(d-\frac12)\sin\phi-(d+\frac12)\cos\phi.
\tag{19}
\]
The final expression increases on (9) and is negative at \(\phi=1.2\).
Thus every such pair has \(\phi>1.2\).

The original axis inequality also gives
\[
 B\sin\phi\ge W-a+A\cos\phi\ge1-a_c=5/12,
\]
and therefore \(B\ge5/12\). Since \(T\) increases,
\[
 C>1.2-.00125-hd_c+T(5/12)>.984>\gamma.
\tag{20}
\]
This covers every remaining lower-half axis-4 state.

## 6. Assembly and exact comparisons

Equation (8) handles every angle at least 1.47, including the full
upper half. Sections 2--5 cover all four retained axes below that
threshold, without restricting either source core piece.
Every displayed terminal bound is strictly above \(\gamma\).

The companion checker verifies 38 exact rational inequalities.
It derives its square-root brackets by integer squaring and its
sine/cosine brackets from alternating Taylor sums. The stated bound
for \(\pi\) follows from Machin's identity with rational arctangent
sums. Only the displayed fixed endpoint and curvature comparisons
are checked; the continuous variable ranges are resolved by the
proof above.

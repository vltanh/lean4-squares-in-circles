# Nine squares: a sharp orientation-stable seven-anchor theorem

**Status (2026-10-22): COMPLETE HAND PROOF of the G1 terminal inequality, including equality.**
This theorem applies to seven *independently rotated* unit squares. It
does not prove that every packing of nine squares has the required
projection-separated 4+3 pattern. That structural extraction is G2 and
remains OPEN.

The proof uses two tangent directions, a one-square support inequality,
and no generated tables, numeric optimization, or local-angle restriction.

## 1. Exact setup

Translate the containing disk center to the origin, and fix an
orthonormal coordinate frame \((e,f)\).

For a freely oriented unit square \(S\), let \(c_S=(x_S,y_S)\) be its
center and let \(u_S,v_S\) be its unit orthogonal side axes.
For \(z\in\mathbb R^2\), put
\[
 H_S(z)=\tfrac12\bigl(|z\cdot u_S|+|z\cdot v_S|\bigr).
\]
Then the projection of \(S\) onto \(z\) is the interval
\([z\cdot c_S-H_S(z),z\cdot c_S+H_S(z)]\).

Write
\[
 h_S=H_S(e)=H_S(f)=\frac12(|\cos\theta_S|+|\sin\theta_S|)
 \ge\tfrac12.
 \tag{1}
\]
The equality of the two coordinate halfwidths is special to **squares**
(not arbitrary rectangles). The angle \(\theta_S\) is measured from
the frame \(e,f\), with quarter-turn equivalence.

A group is **horizontally separated** when its horizontal projection
intervals have disjoint interiors. A group lies **above** \(y=s\)
when every one of its vertices has \(y\ge s\); it lies **below**
\(y=s\) when every vertex has \(y\le s\).

## 2. The one-square orientation penalty

**Lemma 2.1 (orientation penalty, sharp).** Let \(A>0\) and
\(0\le p\le A\). For any unit square \(S\), in any orientation,
\[
 (A+p)h_S+H_S((A,p))\ge A+p,\qquad
 (A+p)h_S+H_S((-A,p))\ge A+p.
 \tag{2}
\]
If \(p>0\), equality in either inequality holds only when \(S\)'s
sides are parallel to the coordinate frame.

*Proof.* Reversing either coordinate, or replacing an axis by its
negative, only interchanges two sign choices. By the square's
quarter-turn symmetry, let
\[
 a=|\cos\theta|,\quad b=|\sin\theta|,\qquad
 1\ge a\ge b\ge0,\quad a^2+b^2=1 .
\]
Thus \(h_S=(a+b)/2\).

Among the possible signs the **smaller** of the left-hand sides
of (2) is
\[
 E=(A+p)\frac{a+b}{2}
       +\frac{Aa+pb+|pa-Ab|}{2}.
 \tag{3}
\]
The other sign gives \(E_{\rm other}=(A+p)a+Ab\),
which is at least \(E\): in the two cases below its difference
is respectively \((A-p)b\) and \(p(a-b)\).

If \(pa\ge Ab\), (3) simplifies to
\[
 E=(A+p)a+pb.
\]
Since \(a>0\), \(pa\ge Ab\) gives \(pb\ge Ab^2/a\).
Moreover
\[
 A(1+a)-a(A+p)=A-ap\ge0,
\]
so \(Ab^2/a\ge(A+p)b^2/(1+a)=(A+p)(1-a)\).
Hence \(E\ge A+p\).

If \(pa\le Ab\), (3) simplifies to
\[
 E=Aa+(A+p)b.
\]
Here \(p\le Ab/a\); and the exact identity
\[
 a(a+b-1)-b(1-b)=(1-a)(1-b)\ge0
 \tag{4}
\]
gives \(A(a+b-1)\ge p(1-b)\). Therefore again
\(E\ge A+p\).

For \(b>0\), \(a<1\) and both arguments are strict
(the first because \(A-ap>0\); the second because
\((1-a)(1-b)>0\)). Thus equality requires \(b=0\),
meaning an axis-aligned square. Conversely, \(b=0\) gives
equality in (2). \(\square\)

This is a universal algebraic inequality on the unit circle,
not a Taylor estimate and not an interval table.

## 3. The sharp cap-row lemma

**Theorem 3.1 (rotated-square horizontal row bound).**
Let \(m\ge2\) independently rotated unit squares lie inside
the disk \(\|v\|^2\le q\). Assume their horizontal
projections have disjoint interiors and every vertex of every
square lies at or above height \(s\).
Write
\[
 A=m/2,\qquad p=s+1,\qquad 0\le p\le A.
\]
Then
\[
                 \boxed{q\ge A^2+p^2
                   =\frac{m^2}{4}+(s+1)^2.} \tag{5}
\]

If \(p>0\) and equality holds in (5), then all \(m\)
squares are axis-parallel to the chosen coordinate frame.
Their ordered horizontal center coordinates are exactly
\[
 x_i=i-\frac{m+1}{2},\qquad i=1,\ldots,m. \tag{6}
\]
The two extreme square centers have height \(s+1/2\);
all remaining centers have height at least \(s+1/2\).

*Proof.* Sort by increasing center \(x\)-coordinates
and write \(S_1,\ldots,S_m\). Projection separation yields
\[
 x_m-x_1\ge h_1+2\sum_{i=2}^{m-1}h_i+h_m
           \ge h_1+(m-2)+h_m. \tag{7}
\]
The floor condition gives \(y_1\ge s+h_1\) and
\(y_m\ge s+h_m\).

Put \(P_+=(A,p)\), \(P_-=(-A,p)\).
For every vertex \(v\) of every square in the disk,
\[
 2P_\pm\cdot v
 =\|P_\pm\|^2+\|v\|^2-\|v-P_\pm\|^2
 \le A^2+p^2+q. \tag{8}
\]
Taking the vertex maximizing each tangent linear functional
in the two extreme squares, then adding, gives
\[
\begin{aligned}
q+A^2+p^2
 &\ge A(x_m-x_1)+p(y_m+y_1)\\
 &\quad+H_m(P_+)+H_1(P_-). \tag{9}
\end{aligned}
\]

Use (7), the floor, and the one-square penalty (2) at
the two extreme squares:
\[
\begin{aligned}
\text{right side of (9)}
&\ge A(m-2)+2ps\\
&\quad+\bigl[(A+p)h_m+H_m(P_+)\bigr]
       +\bigl[(A+p)h_1+H_1(P_-)\bigr]\\
&\ge A(m-2)+2ps+2(A+p)\\
&=2A^2+2p^2, \qquad(m=2A,\ p=s+1).
\end{aligned}
\]
Cancel \(A^2+p^2\) to obtain (5).

Suppose equality and \(p>0\). All the intermediate
nonnegative slacks must vanish. Equality in Lemma 2.1
forces the two outer squares to be axis-parallel.
Equality in the middle step of (7) forces
\(h_i=1/2\) for every other square; because
\(|\cos\theta|+|\sin\theta|=1\) only at a
coordinate-aligned orientation, all squares are
axis-parallel. Every horizontal gap is exactly zero.
Equality in (8) forces the supporting vertices of
the two extreme squares to equal \(P_+\) and \(P_-\)
respectively; thus the extreme outer top corners are
\((A,p)\), \((-A,p)\), and the outer centers have height
\(s+1/2\). The contiguous horizontal projections
therefore have center coordinates (6). All other
heights are bounded below by the floor condition.
\(\square\)

**Corollary 3.2 (below a ceiling).** If the same
horizontally separated \(m\)-square group lies below
height \(s\), and \(0\le1-s\le m/2\), then
\[
 q\ge\frac{m^2}{4}+(1-s)^2. \tag{10}
\]
Equality for \(s<1\) forces horizontal axis alignment,
positions (6), extreme centers at \(s-1/2\), and
all other centers at height at most \(s-1/2\).

*Proof.* Reflect the \(y\) coordinate and apply
Theorem 3.1 with floor \(-s\). \(\square\)

## 4. Independent-rotation 4-over-3 obstruction

**Theorem 4.1 (sharp seven-anchor obstruction).**
Suppose seven independently oriented unit squares lie in a
closed disk of squared radius \(q\). Fix an arbitrary
orthonormal frame. Suppose four of the squares, denoted
\(M\), have pairwise disjoint horizontal projections;
three others, denoted \(B\), also have pairwise disjoint
horizontal projections; and *every point* of every square
in \(M\) is at least as high as *every point* of every
square in \(B\). Then
\[
                   \boxed{q\ge q_*:=1105/256.} \tag{11}
\]
No other hypotheses are imposed on the seven orientations.
Any further two squares of a nine-square packing may be
arbitrarily rotated and placed.

*Proof.* Let \(s\) be the topmost point height of all
squares in \(B\). By hypothesis every \(M\)-square
lies above the line \(y=s\), and every \(B\)-square
lies below it.

If \(s\le-1/2\), Corollary 3.2 for the three B-squares,
using the *larger* ceiling \(-1/2\), yields
\[
 q\ge (3/2)^2+(3/2)^2=9/2>1105/256 .
\]
If \(s\ge1/2\), Theorem 3.1 for the four M-squares,
using the *smaller* floor \(1/2\), yields
\[
 q\ge 2^2+(3/2)^2=25/4>1105/256 .
\]
In the remaining interval \(-1/2<s<1/2\),
both lemmas apply directly:
\[
 q\ge4+(s+1)^2,\qquad
 q\ge\frac94+(1-s)^2. \tag{12}
\]
These expressions are respectively increasing and
decreasing in the stated interval, and
\[
 4+(s+1)^2-\left(\frac94+(1-s)^2\right)
             =\frac74+4s .
\]
They intersect exactly at \(s=-7/16\), where
both equal
\[
 4+(9/16)^2=\frac94+(23/16)^2
               =\frac{1105}{256}.
\]
Thus \(q\ge q_*\) in every case. \(\square\)

**Corollary 4.2 (equality and anchor rigidity).**
Under the hypotheses of Theorem 4.1, if \(q=q_*\),
then \(s=-7/16\) and all seven squares have
sides parallel to the chosen frame.
The four M centers have the exact
horizontal coordinates \(-3/2,-1/2,1/2,3/2\),
with its two extreme centers at height \(1/16\).
The three B centers have horizontal coordinates
\(-1,0,1\), with its two extreme centers at
height \(-15/16\). The middle centers may be
staggered subject to the row ordering, disk
containment and nonoverlap constraints.

*Proof.* The two strict cases in Theorem 4.1
cannot attain equality. For \(-1/2<s<1/2\),
one of the two functions in (12) is strictly
greater than \(q_*\) unless \(s=-7/16\).
At that seam height both row bounds are
equalities. Theorem 3.1 and Corollary 3.2
force frame alignment and the exact
coordinates stated. \(\square\)

Reflection gives the reversed 3-over-4 theorem.

## 5. Consequence for the n=9 roadmap

**G1's proposed terminal inequality is now proved, not
a numerical conjecture.** It is exact, holds for independent
rotations in the seven-anchor group, and provides its own
equality classification. Its only structural hypotheses
are horizontal projection separation within each group
and complete vertical support separation between groups.

**G2 is the remaining critical mathematical obstacle.**
Nothing above proves that every 9-square packing admits
the seven-anchor pattern in some frame. Any proof of such
extraction must use the original unrestricted Packing
predicate. The known record pose lacks a central square,
and non-layered arrangements cannot simply be ruled out
by assuming the packing is a stack of rows.

No Lean source, Lean compilation or kernel verification is
claimed. The hand proof involves only one one-square
algebraic lemma and two supporting-line inequalities.

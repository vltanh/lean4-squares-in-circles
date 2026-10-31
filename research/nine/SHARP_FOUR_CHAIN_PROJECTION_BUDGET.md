# n=9: sharp four-chain projection budget with arbitrary rotations

**Status (2026-10-22): complete short analytic hand proof.**
This is an orientation-independent *quantitative stability theorem* for
**every** four-square projection-disjoint chain. It strengthens the old
four-chain total-gap bound from \(1/4\) to the geometrically sharp
**\(17/512\)**, directly at the proposed nine-square radius.
It does **not** prove the full n=9 optimum or eliminate the remaining
five-square (3,2) complement.

## 1. The elementary two-sign support penalty

Fix perpendicular coordinates \(x,y\).
For a unit square with orthonormal axes \(u,v\), let
\[
 h=\tfrac12(|u_x|+|v_x|)
   =\tfrac12(|u_y|+|v_y|),\qquad
 H(P)=\tfrac12(|P\cdot u|+|P\cdot v|).
\]

**Lemma 1.1 (symmetric horizontal orientation penalty).**
For *every* orientation and either sign of the horizontal
coordinate,
\[
 \boxed{\quad
 4h+H((2,\tfrac12))+H((2,-\tfrac12))
       \ \ge\ \tfrac92.
 \quad}\tag{1}
\]
The same holds with 2 replaced by -2.
Equality holds exactly for an axis-aligned square.

*Proof.* Put \(a=\max(|u_x|,|u_y|)\),
\(b=\min(|u_x|,|u_y|)\), so
\(a^2+b^2=1,\ a\ge b\ge0\) and \(h=(a+b)/2\).
The elementary identity \(|z+w|+|z-w|=2\max(|z|,|w|)\)
gives
\[
 H((2,\tfrac12))+H((2,-\tfrac12))
 =\max(2a,b/2)+\max(2b,a/2)
 =2a+\max(2b,a/2).
\]
Thus the left side of (1) is
\[
                 4a+2b+\max(2b,a/2). \tag{2}
\]

If \(b<a/4\), (2) equals \(9a/2+2b\).
Since \(1-a=b^2/(1+a)\) and \(b<a/4\),
\[
 \frac92(1-a)
 =\frac{9b^2}{2(1+a)}
 <\frac{9ab}{8(1+a)}<2b
\]
for \(b>0\). Hence (2)>9/2.
At \(b=0,a=1\), equality holds.

If \(b\ge a/4\), (2) equals \(4(a+b)\).
Here \((4b-a)(b-4a)\le0\), and after expansion,
\[
      4(a^2+b^2)\le17ab,\qquad ab\ge4/17.
\]
Consequently
\[
   (a+b)^2=1+2ab\ge25/17>81/64,
\]
so \(4(a+b)>9/2\). Thus equality occurs
only at \(b=0\), i.e. an axis-aligned frame.
\(\square\)

No Taylor estimate, angular interval split, or certificate table is
used: only these two **geometrically defined sign cases**.

## 2. Exact gap-and-tilt stability for four squares

Let four independently oriented unit squares
\(M_1,\ldots,M_4\) lie in a disk centered at zero
with squared radius \(q\), and suppose their
horizontal open projection intervals are pairwise
disjoint and ordered left-to-right. Let the
horizontal projection halfwidths be \(h_i\ge1/2\)
and horizontal center coordinates \(x_i\).
Define the *three genuine projection gaps*
\[
    g_i=x_{i+1}-x_i-h_i-h_{i+1}\ge0,
       \qquad g:=g_1+g_2+g_3, \tag{3}
\]
and the excess widths of the two inner squares
\[
    \varepsilon_i:=2h_i-1\ge0\qquad(i=2,3).
 \tag{4}
\]
Define the nonnegative *outer orientation penalties*
\[
 p_i:=4h_i+H_i((2,\tfrac12))+
                  H_i((2,-\tfrac12))-\tfrac92
       \ge0,\qquad i=1,4.
 \tag{5}
\]
For the left endpoint one may use \((-2,\pm1/2)\);
the sum of its support values is the same.

**Theorem 2.1 (four-chain gap and orientation budget).**
For every such chain,
\[
 \boxed{\quad
 q\ \ge\ \frac{17}{4}
        +2(g+\varepsilon_2+\varepsilon_3)
        +\frac{p_1+p_4}{2}.
 \quad}\tag{6}
\]

*Proof.* The exact projection-separation inequalities
sum to
\[
 x_4-x_1
   =h_1+2h_2+2h_3+h_4+g
   =2+h_1+h_4+\varepsilon_2+\varepsilon_3+g.
 \tag{7}
\]

For any square centered at \(c\) inside the disk and
any vector \(P\), maximization at a square vertex
and the Euclidean tangent identity give
\[
             P\cdot c+H(P)
                     \le\frac{q+|P|^2}{2}. \tag{8}
\]
Apply (8) **twice** to the left square with
\(P=(-2,\pm1/2)\), and twice to the right square
with \(P=(2,\pm1/2)\). Sum the four inequalities:
\[
 4(x_4-x_1)
 +\sum_{i\in\{1,4\}}
   \left[H_i((2,\tfrac12))+H_i((2,-\tfrac12))\right]
   \ \le\ 2q+\frac{17}{2}. \tag{9}
\]
By (7) and the definitions (5), the left
side is exactly
\[
\begin{aligned}
&8+4(\varepsilon_2+\varepsilon_3+g)\\
&\quad+\sum_{i\in\{1,4\}}
   [4h_i+H_i((2,\tfrac12))+H_i((2,-\tfrac12))]\\
&=17+4(\varepsilon_2+\varepsilon_3+g)+p_1+p_4 .
\end{aligned}
\]
Rearrange (9) to get (6). \(\square\)

**Corollary 2.2 (sharp candidate-radius reserve).**
If \(q\le Q=1105/256\), then
\[
\boxed{
g+\varepsilon_2+\varepsilon_3
      +\frac{p_1+p_4}{4}
 \ \le\ \frac{Q-17/4}{2}
 =\frac{17}{512}.
}\tag{10}
\]
In particular **the entire sum of all three
projection gaps satisfies \(g\le17/512\)**,
whereas the earlier shadow-length argument
only gave \(g<1/4\).

For each inner square, \(2h_i-1\le17/512\).
For the two outside squares, their nonnegative
orientation penalties sum to at most \(17/128\).
All bounds are exact rational consequences of
the sharp two-sign tangent identity.

## 3. How this changes the remaining (3,2) branch

The remaining coordinate-separable complement has
one four-horizontal projection chain and two vertical
stacks of sizes (3,2). By (10), the horizontal gap
between the two middle chain squares has length
**at most \(17/512\)**, and rotations of the
inner chain squares consume the *same limited reserve*.

For any vertical three-stack with pairwise
overlapping horizontal intervals, one of two
structural alternatives holds:

1. **Common inner-anchor overlap:** There is a
   middle-chain square \(M_2\) or \(M_3\) whose
   horizontal open projection overlaps **all
   three** vertical-stack squares. In a
   common-coordinate-separable packing, that
   anchor is vertically separated from all
   three; it therefore joins the triple into
   a genuine vertical chain of **four**.
2. **Gap bridge:** Two of the triple's horizontal
   intervals meet opposite inner-chain squares
   exclusively (one meets \(M_2\) but not \(M_3\),
   and another meets \(M_3\) but not \(M_2\)).
   Their overlap, and hence the common
   intersection of the triple's three horizontal
   intervals, lies inside the **middle chain
   projection gap**, of length \(\le17/512\).

*Explanation of exhaustiveness:* If not all triple
members overlap \(M_2\), and not all overlap \(M_3\),
one member misses \(M_2\) and another misses \(M_3\).
The inner-pair shadow lemma says they must then
meet \(M_3\) and \(M_2\), respectively.
Since the vertical triple's horizontal intervals
have a common open intersection (interval Helly),
that common intersection can lie only between the
right endpoint of \(M_2\) and the left endpoint of
\(M_3\). The gap is nonempty in this alternative.

This is a **two-branch structural dichotomy**, not
an enumeration of continuously many gap positions.

**Remaining mathematical obligation:** In the
common-overlap branch, identify a *disjoint
vertical triple* elsewhere or a direct signed
terminal stress. In the tiny gap-bridge branch,
prove that all five complementary squares
cannot avoid the sharp terminal bound while
retaining their physical corner containment and
actual coordinate separating axes. The estimate
\(17/512\) is a structural reserve, not a proof
that the gap-bridge branch is impossible.

## 4. Verification boundary

All arguments above are hand identities and inequalities
with arbitrary independent square orientations.
No numerical optimizer result is a premise of the
proof. This does **not** close the entire (3,2)
branch, G2.C, or unrestricted oblique-graph G2.O.
No Lean compilation, CI or independent full audit
is claimed.

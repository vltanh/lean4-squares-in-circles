# Area and second moment of physical unit squares

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/PHYSICAL_SQUARE_AREA_MOMENT_HAND_PROOF.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

**Status: complete independent mathematical review of a necessary inequality.**
The theorem applies to any subset of the same physical nonoverlapping unit
squares. It does not discharge an original cell, mask, positional root, or
roadmap gate by itself. No numerical optimization, Lean, Lake, CI, human
review, or proof-kernel verification is used or claimed here.

## 1. Statement

Let \(S_1,\ldots,S_k\) be unit squares in the Euclidean plane with pairwise
disjoint interiors, where \(k\ge1\). Their orientations are independent.
Write \(c_i\) for their centers. For every real \(2\times2\) matrix \(B\),

\[
\boxed{\quad
\sum_{i<j}\|B(c_i-c_j)\|^2
\ge \frac{k^3|\det B|}{2\pi}
 -\frac{k^2}{12}\operatorname{tr}(B^{\mathsf T}B).
\quad}
\tag{1}
\]

In particular, taking \(B=I\),

\[
\sum_{i<j}\|c_i-c_j\|^2
\ge \frac{k^3}{2\pi}-\frac{k^2}{6}
\ge \frac{k^2(21k-22)}{132}.
\tag{2}
\]

For rational \(B\), the useful entirely rational form of (1) is

\[
\boxed{\quad
\sum_{i<j}(c_i-c_j)^{\mathsf T}W(c_i-c_j)
\ge \frac{7k^3|\det B|}{44}
 -\frac{k^2\operatorname{tr}W}{12},
\qquad W=B^{\mathsf T}B.
\quad}
\tag{3}
\]

All matrix coefficients and the right side of (3) are rational. The absolute
determinant is evaluated exactly. No orientation of any square is changed.

## 2. The equal-area disk inequality

For any bounded measurable planar set \(E\) of area \(A>0\),

\[
\int_E\|x\|^2\,dx\ge\frac{A^2}{2\pi}.
\tag{4}
\]

Let \(D\) be the disk centered at zero with radius
\(r=\sqrt{A/\pi}\), so that \(|D|=|E|\). The sets \(E\setminus D\)
and \(D\setminus E\) have the same area. On the former, \(\|x\|^2\ge r^2\);
on the latter, \(\|x\|^2\le r^2\). Consequently

\[
\begin{aligned}
\int_E\|x\|^2\,dx-\int_D\|x\|^2\,dx
&=\int_{E\setminus D}(\|x\|^2-r^2)\,dx
  +\int_{D\setminus E}(r^2-\|x\|^2)\,dx\\
&\ge0.
\end{aligned}
\]

Polar integration gives
\(\int_D\|x\|^2\,dx=2\pi\int_0^r t^3dt=\pi r^4/2=A^2/(2\pi)\),
which proves (4). This argument does not require convexity or any particular
shape of \(E\).

## 3. Exact inertia of an independently oriented unit square

Let \(S_i=c_i+R_i[-1/2,1/2]^2\), where \(R_i\) is an orthogonal matrix.
The centered square has first moment zero. Its second-moment matrix is

\[
\int_{[-1/2,1/2]^2}zz^{\mathsf T}\,dz=\frac1{12}I,
\]

because \(\int_{-1/2}^{1/2}t\,dt=0\) and
\(\int_{-1/2}^{1/2}t^2dt=1/12\). Hence

\[
\int_{S_i}(x-c_i)(x-c_i)^{\mathsf T}\,dx
=R_i\left(\frac1{12}I\right)R_i^{\mathsf T}
=\frac1{12}I.
\tag{5}
\]

For any symmetric \(W\) and any point \(m\), expanding about \(c_i\) and
using the zero first moment gives

\[
\int_{S_i}(x-m)^{\mathsf T}W(x-m)\,dx
=(c_i-m)^{\mathsf T}W(c_i-m)+\frac{\operatorname{tr}W}{12}.
\tag{6}
\]

In particular, the unweighted inertia of a unit square about its center is
\(1/6\). Equations (5) and (6) are independent of \(R_i\).

## 4. Combining area, inertia, and the pair identity

Put \(S=\bigcup_iS_i\) and \(m=k^{-1}\sum_i c_i\). Each square has area
one. Distinct squares can intersect only on their boundaries, which have
area zero, so \(|S|=k\), integrals over \(S\) add, and \(m\) is the centroid
of \(S\). This includes contacts along an edge or at a vertex.

First suppose \(B\) is invertible, and set \(W=B^{\mathsf T}B\). The affine
image \(E=B(S-m)\) has area \(k|\det B|\). Change of variables and (4) give

\[
\int_S(x-m)^{\mathsf T}W(x-m)\,dx
=\frac1{|\det B|}\int_E\|y\|^2\,dy
\ge\frac{k^2|\det B|}{2\pi}.
\tag{7}
\]

Adding (6) over the squares and substituting (7),

\[
\sum_i(c_i-m)^{\mathsf T}W(c_i-m)
\ge\frac{k^2|\det B|}{2\pi}-\frac{k\operatorname{tr}W}{12}.
\tag{8}
\]

For every symmetric \(W\), direct expansion proves the pair identity

\[
\sum_{i<j}(c_i-c_j)^{\mathsf T}W(c_i-c_j)
=k\sum_i(c_i-m)^{\mathsf T}W(c_i-m).
\tag{9}
\]

Multiplying (8) by \(k\) yields (1). If \(B\) is singular, the right side
of (1) is \(-k^2\operatorname{tr}(B^{\mathsf T}B)/12\le0\), while the left
side is a sum of squares. Thus (1) also holds for every singular \(B\).

Finally, \(\pi<22/7\) gives \(1/(2\pi)>7/44\), proving (3). One completely
elementary verification of this familiar rational bound is

\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi.
\]

The equality follows by polynomial division and
\(\int_0^1(1+x^2)^{-1}dx=\pi/4\). The polynomial quotient is
\(x^6-4x^5+5x^4-4x^2+4\), with remainder \(-4\).

## 5. Rational isotropic constants

These are lower bounds on the sum over unordered center pairs of the
selected subset, not on individual pairs.

| Number of original squares \(k\) | Exact rational lower bound |
|---:|---:|
| 4 | \(248/33\) |
| 5 | \(2075/132\) |
| 6 | \(312/11\) |
| 7 | \(6125/132\) |
| 8 | \(2336/33\) |
| 9 | \(4509/44\) |

The separately proved four-planar-center bound \(8\) is stronger than the
isotropic \(k=4\) entry. A caller may use both. No unproved point-packing
optimality for five, six, or seven centers is needed for any entry here.

## 6. Matrix form for choosing useful rational weights

Define the symmetric pair matrix and its inertia correction by

\[
P=\sum_{i<j}(c_i-c_j)(c_i-c_j)^{\mathsf T},\qquad
M=P+\frac{k^2}{12}I.
\]

Equation (3) is equivalently

\[
\operatorname{tr}(B^{\mathsf T}BM)\ge\frac{7k^3|\det B|}{44}.
\tag{10}
\]

This is linear in the degree-two center moments when a rational \(B\) is
fixed. It therefore supplies exact linear rows in a common-moment lift.
The same inequality also has the diagnostic consequence

\[
\det M\ge\frac{49k^6}{7744}.
\tag{11}
\]

Indeed, \(M\) is positive definite because of its positive scalar identity
term. In (10), choose a real invertible \(B\) with
\(B^{\mathsf T}B=M^{-1}\). Then the left side is two and
\(|\det B|=1/\sqrt{\det M}\), which gives (11). The original irrational
constant analogously gives \(\det M\ge k^6/(16\pi^2)\).

For certificate construction, choose a fixed rational approximation to a
useful real \(B\), then recompute every entry of \(W\), \(\det B\), and the
right side of (3) exactly. The validity of that rational row does not rely
on the accuracy of the approximation. A numerical determinant violation
or a useful choice of \(B\) is discovery evidence only.

## 7. Original-domain scope

The premise is actual physical nonoverlap of the selected original squares.
Disjoint incircles alone do not establish the area of the square union and
cannot replace that premise. All frames, actual marked links, strict mask
bits, original corner bounds, and previously certified guards remain as
defined by the caller. A subset inequality may be installed on any parent
whose same physical squares are pairwise nonoverlapping; it introduces no
new case split. A fixed rational weighted row is unconditional on that
parent. A complete original-domain contradiction and independent exact
replay are still required before any closure count changes.

## 8. Exact row implementation and separate arithmetic check

The implementation is
[`square_area_moment_rows.py`](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/square_area_moment_rows.py).
It supplies the exact quadratic form (3) and affine consequences obtained
by upper secants on previously certified center-difference intervals.
The default family has 1,792 quadratic rows and 1,792 affine rows for
subsets of sizes five through nine and seven rational axis scalings.
Other rational matrices, including shears and reflections, use the same
unconditional theorem.

Run the independent standard-library-only coefficient check with

```
python -B -S research/nine/computer_assisted/verify_square_area_moment_rows.py
```

The [saved report](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/square_area_moment_rows_replay.json)
records 16,064 exact affine and quadratic identities across all subsets
of sizes two through nine and sixteen rational matrices. The expected
quadratic rows use a separate centroid expansion; affine projection
ranges use all rectangle vertices. The checks include zero and singular
matrices, negative determinants, nonintegral coefficients, every printed
isotropic constant and the exact polynomial identity for the pi bound.
The portable fixture is an algebra test input, not a certificate of its
original parent's physical guards. These checks close zero original
cells and zero whole masks by themselves.

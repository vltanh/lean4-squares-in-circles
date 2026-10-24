# A uniform area and completion bound for contact rings of three to six squares

**Status: complete hand proof; two separate hand audits passed.** Let \(k\)
interior-disjoint unit squares form a simple physical center/contact
ring. For \(3\le k\le6\), the area on its inner side not occupied
by the ring squares is at most

\[
                       \frac{k}{4}\cot\frac{\pi}{k}.       \tag{1}
\]

Consequently the numbers of additional interior-disjoint unit squares
that can lie inside a ring of respectively three, four, five, or six
squares are at most

\[
                              0,\quad1,\quad1,\quad2.       \tag{2}
\]

There is no containing-circle hypothesis. All frames and actual contact
points are arbitrary. The proof combines winding localization, the area
cut off from a square by a long chord, and an exact polygon inequality.

## 1. A physical contact ring and its limiting contact polygon

Let \(S_0,\ldots,S_{k-1}\) be closed unit squares with pairwise
disjoint open interiors and centers \(c_i\). Choose actual contacts

\[
                  p_i\in S_i\cap S_{i+1},                 \tag{3}
\]

with indices modulo \(k\). Assume that the loop

\[
             \Gamma=c_0p_0c_1p_1\cdots c_{k-1}p_{k-1}c_0   \tag{4}
\]

is a simple Jordan curve. Orient the indexing so that this curve has
positive winding about its bounded interior. In particular its contact
vertices are distinct. No additional physical contacts between
nonconsecutive squares are excluded by this hypothesis.

For \(0\le t\le1\), move each center vertex to

\[
       c_i(t)=(1-t)c_i+t\frac{p_{i-1}+p_i}{2},             \tag{5}
\]

keeping all contact vertices fixed. The two segments incident to
\(c_i(t)\) remain in \(S_i\). For \(t<1\), the point
\(c_i(t)\) is in the square's open interior. Each incident segment
is therefore in that open interior except at its contact endpoint.
Its two segments meet only at \(c_i(t)\): if their contact rays
were collinear, the interior vertex would lie between the two distinct
boundary endpoints. Distinct squares' open interiors are disjoint.
Thus the resulting loop \(\Gamma_t\) remains a simple Jordan
curve for every \(t<1\), with its positive orientation unchanged.

At \(t=1\) the loop is the contact polygon

\[
                   P=p_0p_1\cdots p_{k-1}p_0,             \tag{6}
\]

with edge midpoints inserted. Its edge
\([p_{i-1},p_i]\) is a chord of the single square \(S_i\).
Write

\[
                  l_i=|p_i-p_{i-1}|\le\sqrt2.            \tag{7}
\]

The limiting polygon may have boundary tangencies or retraced segments;
we do not assume it is strictly convex or even a nondegenerate Jordan
polygon. Nevertheless its winding number at every point off its edges
is either zero or one. Indeed, \(\Gamma_t\to P\) uniformly;
for a fixed point off \(P\), winding is constant for all \(t\)
sufficiently close to one, and each such Jordan curve has winding zero
or one.

Let \(G\) be the region where the winding of \(P\) equals one.
Its area is the signed polygon area

\[
                  A(P)=\frac12\sum_i\det(p_i,p_{i+1}),   \tag{8}
\]

by the usual polygon area formula, or by the signed area formula applied
to the finitely many faces of its segment arrangement. The nonnegative
winding just proved is essential here: no cancellation of oppositely
oriented regions is being used as a capacity bound.

Let \(H\) be the part of the bounded interior of \(\Gamma\)
outside the union of the closed ring squares. The homotopy (5) lies in
those squares, so it avoids every point of \(H\). Consequently

\[
                        H\subseteq G.                    \tag{9}
\]

Every additional square with open interior inside \(\Gamma\),
and interior-disjoint from the ring squares, has its entire open
interior in \(H\). This uses the elementary fact that an open
neighborhood of a point in a closed square meets that square's open
interior. Such a completion square therefore contributes its full unit
area to \(H\).

## 2. The area on either side of a long square chord

**Lemma 2.1.** A chord of a unit square with length
\(1<l\le\sqrt2\) cuts off area at least

\[
                         \frac12\sqrt{l^2-1}              \tag{10}
\]

on each side of its line.

*Proof.* Work in the square's side coordinates. If the endpoints lie on
adjacent sides, let their distances from the common corner be
\(x,y\in(0,1]\). The corner piece is a triangle of area \(xy/2\),
and \(x^2+y^2=l^2\). Since

\[
 (1-x^2)(1-y^2)\ge0,
 \qquad x^2y^2\ge x^2+y^2-1=l^2-1,                      \tag{11}
\]

that piece has the stated minimum area. It has area at most \(1/2\),
so the complementary piece has area at least \(1/2\), which is also
at least the bound (10).

If the endpoints lie on opposite sides, rotate coordinates so that they
are \((0,a)\) and \((1,b)\), with \(0\le a,b\le1\).
Then \(l^2=1+(a-b)^2\). The two areas are \((a+b)/2\) and
\(1-(a+b)/2\), each at least \(|a-b|/2\). This is exactly (10).
These cases include side endpoints and all limiting corner choices.
\(\square\)

Now take a chord \([p_{i-1},p_i]\) of the contact polygon with
\(l_i>1\). Its open chord lies in \(\operatorname{int}S_i\):
a chord lying on a boundary side could have length at most one. No other
edge of \(P\) enters \(\operatorname{int}S_i\), since every
other edge lies in a different ring square and their open interiors are
disjoint. More explicitly, an interior point of \(S_i\) cannot
belong even to the closed other square, by the open-neighborhood fact
used above.

The winding jumps by one from the right to the left of this oriented
chord. Since it takes only the values zero and one, it equals one on
the inward side. The open part of \(S_i\) on that side of the chord
is connected and meets no other polygon edge; its winding is therefore
one throughout. Hence the entire inward cut-off piece of \(S_i\)
lies in \(G\), up to its measure-zero boundary. Lemma 2.1 supplies
the area bound (10) for that piece.

The pieces furnished by different squares have disjoint interiors, and
none of them belongs to the free region \(H\). Subtracting these
occupied pieces from (9) and (8) gives

\[
 \operatorname{area}(H)
 \le A(P)-\frac12\sum_i\sqrt{\max(l_i^2-1,0)}.           \tag{12}
\]

For chords of length at most one no positive subtraction was claimed.
This avoids making any assumption about which part of a boundary-side
chord is on the inner side of the contact polygon.

## 3. An exact polygon inequality

**Lemma 3.1.** For any closed polygon with \(k\ge3\) vertices,
including a self-tangent or degenerate polygon, its signed area obeys

\[
                 A(P)\le\frac14\cot\frac\pi k
                                  \sum_i l_i^2.          \tag{13}
\]

*Proof by finite Fourier expansion.* Identify the plane with the complex
numbers, write the vertices as \(z_j\), and subtract their mean,
which changes neither area nor edge lengths. Put
\(\omega=\exp(2\pi i/k)\). The exact finite expansion is

\[
 z_j=\sum_{m=1}^{k-1}a_m\omega^{mj},
 \qquad
 a_m=\frac1k\sum_{j=0}^{k-1}z_j\omega^{-mj}.             \tag{14}
\]

The finite geometric-series identity gives
\(\sum_j\omega^{(m-n)j}=k\) when \(m=n\), and zero otherwise.
It follows that

\[
\begin{aligned}
 A(P)
  &=\frac12\operatorname{Im}\sum_j\overline{z_j}z_{j+1}
    =\frac k2\sum_{m=1}^{k-1}|a_m|^2
                             \sin\frac{2\pi m}{k},\\
 \sum_j|z_{j+1}-z_j|^2
  &=4k\sum_{m=1}^{k-1}|a_m|^2\sin^2\frac{\pi m}{k}.
\end{aligned}                                                    \tag{15}
\]

For each \(1\le m\le k-1\), the first coefficient divided by
the second is

\[
                         \frac14\cot\frac{\pi m}{k}
                         \le\frac14\cot\frac\pi k,       \tag{16}
\]

because cotangent decreases on \((0,\pi)\). The factors
\(|a_m|^2\) are nonnegative. Summing these coefficient inequalities
proves (13). This is a finite exact identity and inequality, not a
spectral approximation or numerical calculation. \(\square\)

## 4. Optimize each chord contribution for three to six sides

Set

\[
                  c_k=\frac14\cot\frac\pi k.
\]

For \(3\le k\le6\),

\[
                     0<c_k\le\frac{\sqrt3}{4}<\frac12.    \tag{17}
\]

Combining (12) and (13), and writing \(x_i=l_i^2\in[0,2]\),
gives

\[
 \operatorname{area}(H)
 \le\sum_i\left(c_kx_i-\frac12\sqrt{\max(x_i-1,0)}\right).
                                                               \tag{18}
\]

Each summand is at most \(c_k\). On \([0,1]\) it is simply
\(c_kx\le c_k\). On \([1,2]\), the function
\(c_kx-\tfrac12\sqrt{x-1}\) is convex, so its maximum on that
interval is attained at an endpoint. The two endpoint values are

\[
                            c_k,\qquad2c_k-\frac12<c_k.
\]

Thus (18) is at most \(kc_k\), which is exactly (1).

If \(q\) unit completion squares lie inside the ring, their open
interiors are disjoint subsets of \(H\), each of area one. Hence
\(q\le\operatorname{area}(H)\). The resulting exact bounds are:

| Ring size \(k\) | Maximum free area from (1) | Unit completion capacity |
| --- | --- | --- |
| \(3\) | \(\sqrt3/4<1\) | \(0\) |
| \(4\) | \(1\) | \(1\) |
| \(5\) | \(\tfrac54\cot(\pi/5)<2\) | \(1\) |
| \(6\) | \(3\sqrt3/2<3\) | \(2\) |

For the five-side comparison, the standard exact trigonometric identity
\(\cot^2(\pi/5)=1+2/\sqrt5\) gives
\(\cot(\pi/5)<8/5\): this reduces to
\(50<39\sqrt5\), whose square is \(2500<7605\).
The other strict comparisons follow from \(\sqrt3<2\).

This proves both the free-area theorem and all four completion capacities.

## 5. Scope and the remaining mixed-component obligation

The conclusion concerns squares whose open interiors lie on the inner
side of the physical Jordan ring. It supplies no bound on additional
squares in exterior pockets. In particular, a small cycle inside a
larger positive component cannot be treated as containing all physical
completion squares without a separate routing argument.

For the four-body triangle-plus-leaf class, the triangle hole is empty
by the \(k=3\) case. The exterior pocket between its touching loaded
boundary neighbors is also empty by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`. The unresolved completion
obligation is to prove that the two larger complementary regions
involving the articulation and the leaf contain at most **four** extra
unit squares in total, for every physical force-and-torque-balanced
core in the declared radius window. No separate two-per-region bound,
symmetry, common square frame, or narrow articulation-height range is
assumed here.

# An exact asymmetric two-cap piercing gate

2026-10-12 continuation. This is a **whole-continuum** necessary
condition for *two perpendicular triple caps to have disjoint labels*.
It contains no sampled parameter grid, box-cover premise, or
unproved global contact-graph reduction. It is especially useful in
the remaining all-seven-exclusive-single-side S1 branch.

## Setup

Let eight pairwise interior-disjoint unit squares lie in a disk
\(D_R\) with
\[
\sqrt2+1/2<R,\qquad R^2\le9789/2500.
\]
For one outward cap \(x\ge h\ge0\) containing **three whole**
unit squares, put
\[
X(h)=(R+h)/2,\quad B(h)=\sqrt{R^2-X(h)^2},
\quad \lambda(h)=\min\{1,\;2\sqrt2-R+h\}.
\]
The same definitions apply to the perpendicular cap \(y\ge h'\).
The half-strip \(m=(R-h)/2\) is below one because \(R<2\).

## Uniform extreme-chord coverage

For any one square in the first cap, let \(L=\cos\theta+\sin\theta\)
be its full projected width in x, \(1\le L\le\sqrt2\).
Since its horizontal projection lies in \([h,R]\), the
midpoint line \(x=X(h)\) cuts the square in an open vertical
interval of chord length \(\ell\).
As in
[HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md](HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md),
the plateau/axis-aligned chord has \(\ell\ge1\);
a sloping chord has
\[
\ell\ge\frac{2(L-m)}{L^2-1}
\ge2\sqrt2-R+h.
\]
The last inequality uses the exact monotonic decrease of the
rational function in \(L\), whose derivative numerator is
\(-2[(L-m)^2+(1-m^2)]<0\).

Thus **all three midpoint chords** have \(\ell\ge\lambda(h)\).
Ordering the three disjoint open chord intervals inside
\([-B(h),B(h)]\) shows that the **topmost actual square**
has a chord interval \((y_-,y_+)\) satisfying
\[
y_-\le B(h)-\lambda(h),\qquad
y_+\ge -B(h)+3\lambda(h).                         \tag{1}
\]

The first bound in (1) always lies **below** the other
cap's midpoint \(X(h')\). Indeed, since \(R<2\) and
\(\sqrt3<7/4\),
\[
B(h)\le\sqrt3\,R/2<7/4.
\]
Also
\[
\lambda(h)\ge\min\{1,2\sqrt2-R\}>4/5
\]
by the exact rational estimates
\(\sqrt2>7071/5000,\ R<9894/5000\).
Hence
\[
B(h)-\lambda(h)<7/4-4/5=19/20
<191/200<R/2<X(h').                             \tag{2}
\]
No restriction on how close \(h,h'\) are is needed.

## Asymmetric shared-square criterion

Suppose the three-square populations belong to two
**perpendicular** central-owned whole caps, at offsets \(h_R,h_U\).
If both strict inequalities hold,
\[
3\lambda(h_R)-B(h_R)>X(h_U),\qquad
3\lambda(h_U)-B(h_U)>X(h_R),                      \tag{3}
\]
then the populations **must share an actual square** with both
R and U whole-cap membership.

Proof: by (1)–(2), the highest right-cap midpoint chord
contains \(X(h_U)\) strictly in its vertical open interval.
Symmetrically, the rightmost upper-cap midpoint chord contains
\(X(h_R)\) strictly in its horizontal open interval. These two
actual square interiors intersect at
\((X(h_R),X(h_U))\), hence represent the same label.
No frames or contacts have been prescribed. QED.

## Necessary inequality for S1 without double-side membership

For the all-seven-single-side S1=(3+0,3+1) status, the
perpendicular triple populations are known to have **disjoint
square labels**. Therefore at least one of the following
exact continuous inequalities must hold:
\[
\boxed{
3\lambda(h_R)-B(h_R)\le X(h_U)
\quad\text{or}\quad
3\lambda(h_U)-B(h_U)\le X(h_R).
}                                                   \tag{4}
\]
This is a necessary condition for **every** S1 packing
in the proved search interval. It is not a numerical approximation
to the true feasibility region and does not claim the converse.
In particular, (4) handles asymmetric offsets and can guide further
symbolic deductions without assuming a discrete contact graph.

The rational low-offset rectangle
[HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md](HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md)
is an explicit closed subregion where both inequalities in (3)
are proved, complementing the uniform \(1/11\) threshold.
The S4 sharp equality configuration is not an S1 configuration
and remains untouched. The unrestricted lower bound
\(R_8\ge\widehat R\) is still **OPEN**.

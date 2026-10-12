# Perpendicular three-square caps also intersect in a low-offset rectangle

2026-10-12 continuation. This is a complementary **continuous rectangle
exclusion**, not a rephrasing of the one-sided \(1/11\) theorem in
[HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md](HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md).
All arithmetic below is exact rational comparison.

## Theorem (both offsets between 1/16 and 1/10)

Suppose eight pairwise interior-disjoint unit squares lie in
\(D_R\) with
\[
\sqrt2+1/2<R,\qquad R^2\le9789/2500.
\]
Let \(C\) be the unique origin-containing unit square. Suppose three
*whole* exterior squares lie beyond its right side \(x=h_R\) and
three *whole* exterior squares lie beyond its upper side \(y=h_U\),
where
\[
1/16\le h_R\le1/10,\qquad
1/16\le h_U\le1/10.
\]
Then those two triple populations **share at least one actual square**,
which has both R and U whole-square membership.

The frames of all squares are arbitrary and independent.
No contact, stress, center-radius, or grid assumption enters the proof.

## 1. A fixed low-offset range for every midpoint

For either cap offset \(h\in[1/16,1/10]\), define
\[
X=(R+h)/2,\quad m=(R-h)/2,\quad
B=\sqrt{R^2-X^2}.
\]
The prior analytic eight-square lower radius and exact upper ceiling give
\[
191/100<R<9894/5000
\]
(the upper square comparison is \(309/6250000>0\)).
Consequently
\[
789/800<X<5197/5000,\qquad
m<19163/20000<1,\qquad B<16953/10000.          \tag{1}
\]
The lower and upper midpoint bounds are, respectively,
\[
(191/100+1/16)/2=789/800,\quad
(9894/5000+1/10)/2=5197/5000.
\]
The displayed bound on \(m\) equals
\((9894/5000-1/16)/2=19163/20000\).
For \(B\), its squared expression
\((3R^2-2Rh-h^2)/4\) grows with \(R\) and decreases with \(h\ge0\),
and
\[
(16953/10000)^2-
\frac{3(9894/5000)^2-2(9894/5000)(1/16)-(1/16)^2}{4}
=47629/400000000>0.
\]

## 2. Every actual cap chord exceeds 9121/10000

For an independently rotated square, reduce its unsigned tilt to
\(0\le\theta\le\pi/4\) and put \(L=\cos\theta+\sin\theta\).
Its x projection, of width \(L\in[1,\sqrt2]\), lies in \([h,R]\).
Thus the midpoint \(x=X\) intersects its open interior.
For its vertical chord length \(\ell\), the exact formulas give
\(\ell=1/\cos\theta\ge1\) on the parallel-side plateau, or
\[
\ell\ge\frac{2(L-m)}{L^2-1}
\]
on a sloping flank. For \(m<1\), the final function decreases strictly
in \(L\): its derivative numerator is
\(-2[(L-m)^2+(1-m^2)]<0\).
Its minimum at \(L=\sqrt2\) yields
\[
\ell\ge2\sqrt2-R+h
>2(7071/5000)-9894/5000+1/16
=9121/10000=:\lambda.                           \tag{2}
\]
The strict rational inequality \(\sqrt2>7071/5000\) follows by
squaring. Plateau and axis-parallel chords also exceed \(\lambda<1\).

## 3. A fixed segment inside one square in either triple

Order the three open vertical chord intervals by their height.
Each has length \(\ell_i>\lambda\), and each lies in the disk chord
\([-B,B]\).
The topmost chord \((y_-,y_+)\) therefore satisfies
\[
y_+\ge-B+\ell_1+\ell_2+\ell_3
>-16953/10000+3(9121/10000)
=10410/10000>5197/5000,
\]
with strict final difference \(1/625>0\). Also
\[
y_-\le B-\ell_\mathrm{top}
<(16953-9121)/10000
=7832/10000<789/800,
\]
the final difference being \(4061/20000>0\).
Hence an actual square in the right cap contains openly the entire
closed vertical segment
\[
\{X_R\}\times[789/800,5197/5000].                 \tag{3}
\]
By exchanging x and y, an actual square in the upper cap contains
openly the horizontal segment
\[
[789/800,5197/5000]\times\{Y_U\},                \tag{4}
\]
where \(X_R=(R+h_R)/2\) and \(Y_U=(R+h_U)/2\).
Both slice coordinates are **strictly inside** the common fixed
interval by (1), so (3) and (4) intersect at
\((X_R,Y_U)\) within both actual open square interiors.
Therefore the two selected squares must be the same label. QED.

## Precise implication for the all-single-side S1 case

The S1=(3+0,3+1) all-seven-exclusive-single-side pattern has two
perpendicular triple populations with **no** shared label. Therefore
it cannot have *both* triple offsets in the **closed** rectangle
\[
[1/16,1/10]\times[1/16,1/10].
\]
With these sides normalized to R and U and
central square center \(p_C=(a,b)\), that is the forbidden
closed position rectangle
\[
(a,b)\in[-7/16,-2/5]\times[-7/16,-2/5].
\]
This genuinely improves the continuous classification: the previous
\(1/11\) theorem alone only forbade the complementary region in
which both offsets are \(\ge1/11\); the present box includes pairs
with both offsets strictly **below** \(1/11\).

This proves neither a global exclusion of S1 nor the unrestricted sharp
inequality \(R_8\ge\widehat R\). The valid S4 equality case
is unaffected.

# Perpendicular three-square caps: a sharper common-piercing threshold

Research continuation, 2026-10-12. This improves
[HUMAN_PERPENDICULAR_TRIPLE_FIXED_POINT.md](HUMAN_PERPENDICULAR_TRIPLE_FIXED_POINT.md)
by tightening the same elementary midpoint-slice argument. It is a *hand proof*,
not a Lean formalization. Exact rational comparisons are stated below.

## Theorem (arbitrary frames; threshold 11/120)

Let eight pairwise interior-disjoint unit squares lie in a disk of radius
\(\sqrt2+1/2<R\), \(R^2\le9789/2500\). Let \(C\) be the unique
origin-containing square. Suppose three whole exterior squares lie beyond
its right side \(x=h_R\) and three whole exterior squares lie beyond
its upper side \(y=h_U\), with
\[
h_R\ge11/120,\qquad h_U\ge11/120.
\]
Then these two three-square populations have a **common actual square**,
whose whole-square side status includes both R and U. No orientation,
contact graph, force, or center-norm assumption is used.

### Preliminary triple-cap cutoff

For three whole squares beyond \(x=h\ge0\), the sharp theorem
[HUMAN_THREE_SQUARE_CAP.md](HUMAN_THREE_SQUARE_CAP.md) gives
\(R^2\ge(h+1)^2+9/4\) for \(h\le1/3\).
For \(h\ge1/3\), apply it at the smaller cap offset \(1/3\);
this would give \(R^2\ge145/36>9789/2500\).
Thus \(h<1/3\), and
\[
h<7/24,\quad
9789/2500<2257/576=(1+7/24)^2+9/4.
\]

### 1. A common midpoint slice

For \(11/120\le h<7/24\), define
\[
X=(R+h)/2,\quad m=(R-h)/2,\quad B=\sqrt{R^2-X^2}.
\]
From \(191/100<R<1979/1000\), proved by rational squares,
\[
1<X<142/125,\qquad m<2831/3000,\qquad B<1687/1000. \tag{1}
\]
Explicitly,
\[
X>(191/100+11/120)/2=1201/1200>1,
\]
\[
X<(1979/1000+7/24)/2=1703/1500<142/125,
\]
\[
m<(1979/1000-11/120)/2=2831/3000.
\]
As \(B^2=(3R^2-2Rh-h^2)/4\) increases in \(R\) and decreases
in \(h\), the remaining estimate follows from
\[
(1687/1000)^2-
\frac{3(1979/1000)^2-2(1979/1000)(11/120)-(11/120)^2}{4}
=3247/2250000>0.
\]

### 2. Every cap square has a long actual vertical chord

Write an arbitrary square's unsigned tilt as \(0\le\theta\le\pi/4\),
\(c=\cos\theta\), \(s=\sin\theta\), \(L=c+s\in[1,\sqrt2]\),
\(cs=(L^2-1)/2\). Its horizontal projection is of width \(L\)
and is inside \([h,R]\), so the line \(x=X\) cuts it in an
open chord of length \(\ell\).

For zero tilt \(\ell=1\). For nonzero tilt, the exact square
section is \(1/c\ge1\) on the plateau and
\[
\ell=(L/2-|X-p_x|)/(cs)\ge(L-m)/(cs)
\]
on either sloping flank, since
\(|X-p_x|\le m-L/2\).

We claim \(\ell>941/1000\). In the sloping case it suffices to prove
\[
g(L):=L-(941/2000)(L^2-1)>m.
\]
The quadratic \(g\) is concave, hence its minimum on \([1,\sqrt2]\)
is at an endpoint. At \(L=1\), \(g=1>m\). At \(L=\sqrt2\),
\[
g(\sqrt2)=\sqrt2-941/2000
>7071/5000-941/2000
=9437/10000>2831/3000>m.
\]
Here \((7071/5000)^2<2\) is an exact integer comparison.
Thus the bound holds for all orientations and allowed centers.

### 3. A fixed segment must lie inside a cap square

At \(x=X\), the three square chords have mutually disjoint open
vertical intervals, each longer than \(941/1000\), all within
\([-B,B]\). For the highest chord \((y_-,y_+)\), ordering yields
\[
y_+\ge-B+\ell_1+\ell_2+\ell_3
>-1687/1000+3(941/1000)=142/125,
\]
while
\[
y_-\le B-\ell_\mathrm{top}
<(1687-941)/1000=746/1000<1.
\]
Therefore one *actual* square has in its open interior the entire
closed segment
\[
\{X\}\times[1,142/125]. \tag{2}
\]
For the perpendicular upper cap, one of its three actual squares
contains \([1,142/125]\times\{Y\}\) openly, where \(Y=(R+h_U)/2\).
Both \(X,Y\) belong to \((1,142/125)\), so the segments intersect
at a point in the open interiors of both selected squares.
As distinct packed squares have disjoint open interiors, they are
the same square. This proves the theorem. Symmetries cover every
pair of perpendicular central sides.

## Consequences for exclusive single-side S1

For S1=(3+0,3+1), the perpendicular triple populations are disjoint,
so
\[
\min(h_{\mathrm{triple},1},h_{\mathrm{triple},2})<11/120.
\]
When the triple sides are normalized as R,U and
\(p_C=(a,b)\), this becomes
\[
\min(a,b)<-49/120.
\]
This strengthens the former S1 requirement \(\min(a,b)<-2/5\).

If the small-offset triple is on the 3+1 axis, its opposite
single-square cap has \(h_\mathrm{opp}=1-h>109/120>2/5\).
Apply the arbitrary-orientation one-square envelope
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md):
for the singleton's transverse center coordinate \(z\),
\[
(|z|+1/2)^2\le R^2-(1+h_\mathrm{opp})^2
<9789/2500-(229/120)^2
=98591/360000<(21/40)^2.
\]
The last difference is \(317/180000>0\). Consequently,
\[
|z|<1/40.
\]
Neither the full small-offset S1 branch nor the unrestricted
sharp lower bound \(R_8\ge\widehat R\) is thereby proved.

## Status

Written analytic argument; rational endpoint calculations checked
independently. No Lean proof, computer interval cover, or new global
optimization claim. Preserve the S4/k=7 equality-bearing packing.

# Complete elimination of the exclusive S3 / k=3 macro-case

Research continuation, 2026-10-12. **The entire S3/k=3
outer-center subcase is impossible**, for all seven independent
exterior square orientations. This strictly supersedes the previous
small-offset, outer-ray, and far-singleton center restrictions:
those notes remain valid conditional reductions but their
S3/k=3 *parent macro-cell is now empty*.

This is **not** an unconditional proof of the eight-square
optimum: S3 with k=4,5,6,7, the other D0 statuses,
D1/D2, and the equality-bearing S4/k=7 case remain.

## Theorem

Suppose eight pairwise interior-disjoint unit squares
lie in a disk centered at the origin with squared radius
\[
R^2\le9789/2500.
\]
Let C denote their unique origin-containing square.
Assume all seven exterior squares have **exactly one**
available central-owned *whole-square* side separator,
and their populations, up to reflection/axis exchange,
are
\[
N_R=3,\quad N_L=1,\quad N_U=2,\quad N_D=1
\]
(the S3=(3+1,2+1) branch).

Then **at least four** exterior square centers have radial norm
at least one:
\[
\boxed{\text{exclusive S3}\Longrightarrow k\ge4.}
\]

No selected physical contact, common frame, stress equilibrium,
or sampled continuous minimization is used.

## 1. Retained established S3/k=3 consequences

Suppose for contradiction that exactly **k=3**
exterior centers are outer (norm at least one).

The distant whole L and D side singletons are outer,
since their opposite R triple and U pair force
their normal center distances above one.
The R triple has at least one outer center, by
the triple-cap inner-center capacity theorem.
These status groups are **disjoint actual labels**.
Thus the R triple has **exactly one outer center**
and two inner centers; both U pair centers are inner.

We may use the following separately proven, all-frame
results, **under these very hypotheses**:

* [HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md):
  the R triple's signed offset satisfies
  \(h_R>17/200\), and the two-member U offset
  \(h_U<1/5\);
* [HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md):
  the sole outer R center q has polar ray angle
  \[
  311/500<\psi<8959/10500;
  \]
* [HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md):
  the two *inner* R centers lie on strictly opposite
  sides of the horizontal origin diameter.

We will derive an entirely explicit center-distance
contradiction using these consequences and the fact
that the outer R square is **R-only**, not RU.

## 2. Two inner right-cap centers force a positive-y reserve

Denote the two distinct inner R centers by
\[
p_-=(x_-,y_-),\qquad p_+=(x_+,y_+),
\]
where \(y_-<0<y_+\). Both whole right-cap
memberships and \(h_R>17/200\) imply
\[
x_-,x_+>117/200.
\]
Both center norms are strictly less than one.
Consequently
\[
x_-,x_+<1,\quad
|x_+-x_-|<1-117/200=83/200,
\]
and
\[
y_->-\sqrt{1-(117/200)^2}
=-\sqrt{26311}/200.
\]

Distinct packed unit squares contain disjoint open
inscribed disks of radius \(1/2\), so their
center distance is at least one. Therefore
\[
(y_+-y_-)^2
\ge1-(x_+-x_-)^2
>1-(83/200)^2
=33111/40000.
\]
Since \(y_+-y_->0\),
\[
y_+>y_-+\sqrt{33111}/200
>\frac{\sqrt{33111}-\sqrt{26311}}{200}.
\]

The following exact integer square comparisons are sufficient:
\[
33111\cdot100=3311100>1819^2=3308761,
\]
\[
26311\cdot100=2631100<1623^2=2634129.
\]
Hence
\[
\boxed{y_+>\frac{1819/10-1623/10}{200}
=\frac{49}{500}.}                              \tag{1}
\]
This positive transverse reserve is **forced by the
other inner R center**; it is not inferred merely
from a center-ray sign.

We also retain
\[
117/200<x_+<1,\qquad 49/500<y_+<1.           \tag{2}
\]

## 3. The outer R center is both high enough and low enough

Let \(q=(q_x,q_y)\) denote the third, **outer**
R-square center. Its radial norm \(s\) obeys
\[
1\le s<r_0:=283/200,
\]
where the latter strict bound follows from the
exact farthest-vertex square inequality
\(s^2+s+1/2\le9789/2500\)
(the right side is exceeded at \(s=r_0\)
by \(65/40000\)).

The previously proved S3/k=3 ray restriction gives
\[
311/500<\psi=\arg q<8959/10500.
\]
Since \(\pi/6<311/500\) and \(8959/10500<\pi/3\),
we have
\[
\boxed{q_x>1/2,\qquad q_y>1/2.}                \tag{3}
\]

Also \(\psi>311/500\) and cosine decreases
on the first quadrant. The elementary alternating
cosine upper bound
\[
\cos z\le1-z^2/2+z^4/24
\]
at \(z=311/500\) gives the **exact rational margin**
\[
\frac{813}{1000}
-\left[1-\frac12(311/500)^2+\frac1{24}(311/500)^4\right]
=\frac{308048159}{1500000000000}>0.
\]
Thus
\[
q_x=s\cos\psi
<\frac{283}{200}\cdot\frac{813}{1000}
=\frac{230079}{200000}.                       \tag{4}
\]

Now use the **exclusive single-side** hypothesis:
Q is R-only, so it is **not wholly contained**
in the upper central-owned cap \(\{y\ge h_U\}\).
For any unit square, the vertical support half-width
is at most \(\sqrt2/2<177/250\).
Therefore the lowest actual vertex of Q lies
*strictly below* \(h_U\), forcing
\[
q_y<h_U+\frac{\sqrt2}{2}
<\frac15+\frac{177}{250}
=\frac{227}{250}.                              \tag{5}
\]
Here \(h_U<1/5\) was already established,
and \((177/250)^2>1/2\) is a rational square check.
This use of the **missing U separator** is essential;
a mere R-cap membership would not imply (5).

## 4. Two actual square centers are too close

Combine (2)–(5). In the x direction we have
\[
117/200<x_+<1,\qquad
1/2<q_x<230079/200000.
\]
Consequently
\[
|q_x-x_+|
<\max\left\{\frac{230079}{200000}-\frac{117}{200},
                   1-\frac12\right\}
=\frac{113079}{200000}.                        \tag{6}
\]

In the y direction,
\[
49/500<y_+<1,\qquad
1/2<q_y<227/250,
\]
so
\[
|q_y-y_+|
<\max\left\{\frac{227}{250}-\frac{49}{500},
                    1-\frac12\right\}
=\frac{81}{100}.                                \tag{7}
\]

The squared center distance of the **two different**
packed squares Q and the inner square with center p_+
is therefore
\[
\begin{aligned}
|q-p_+|^2
&<\left(\frac{113079}{200000}\right)^2
    +\left(\frac{81}{100}\right)^2\\
&=1-\frac{969139759}{40000000000}
<1.
\end{aligned}                                                   \tag{8}
\]
This contradicts the distance-at-least-one condition
from their inscribed half-unit disks.

Thus exclusive S3 with exactly k=3 outer centers
is impossible. Since all eight-square packings at
the search ceiling have \(k\ge3\), the surviving
S3 outer-center counts are precisely a **necessary**
subset
\[
\boxed{k\in\{4,5,6,7\}.}
\]
This does **not** assert existence of those remaining
outer-count cases. QED.

## Scope and follow-up

The argument uses one exact sine/cosine direction
constraint, two inner squares in a **whole** R
cap, and the **failure** of the outer R square to
belong wholly to the perpendicular U cap. It is
orientation-independent. It does not infer that
a positive-y center puts its entire square in
the upper origin quadrant.

It eliminates the **entire S3/k=3 macro-cell**
rather than merely its earlier narrow offset
or center-ray sectors. The previous S3/k=3
research notes become historical conditional
lemmas; they are not proofs of actual surviving
configurations.

The full S3 branch with k=4..7, S1, S2, S4,
D0 corner-only, D1 and D2, and the global sharp
radius \(R_8\ge\widehat R\) remain **OPEN**.
The known S4/k=7 exact candidate equality
packing is deliberately preserved.

[verify_s3_k3_global_exclusion.py](verify_s3_k3_global_exclusion.py)
audits all displayed strict rational margins;
the **written all-frame proof** establishes the
continuous result, not a sampled classifier or
external PASS premise.

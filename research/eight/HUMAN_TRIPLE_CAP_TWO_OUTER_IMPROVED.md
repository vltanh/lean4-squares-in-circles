# Two outer centers in a three-square cap already at offset 13/100

Research continuation, 2026-10-12. This strengthens the \(h\ge7/50\)
theorem in [HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md](HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md).
The proof uses exact midpoint chords with one additional top-frame split.
It is a written arbitrary-orientation theorem, not a Lean formalization.

## Main theorem

Let three pairwise interior-disjoint unit squares of **arbitrary**
independent orientations lie wholly in
\[
D_R\cap\{x\ge h\},\qquad R^2\le9789/2500,\qquad h\ge13/100.
\]
Then the squares with the **highest** and **lowest** vertical chords at
\(X=(R+h)/2\) both have center norm **strictly greater than one**.
They are distinct labels. No contact, selected separator, stress,
or packing of the rest of the disk is assumed.

The condition is on *whole-square cap membership*, not merely
a center coordinate sign.

## 1. Exact rational midpoint estimates

The bound \(R^2\le9789/2500\) implies
\[
R<9894/5000
\]
since \((9894/5000)^2-9789/2500=309/6250000>0\).
Define
\[
X=(R+h)/2,\quad m=(R-h)/2,\quad B=\sqrt{R^2-X^2}.
\]
A triple of complete unit squares implies \(R>h\), so \(X\)
is inside the projection strip \([h,R]\).
Our assumptions yield
\[
m<(9894/5000-13/100)/2=2311/2500<1,
\qquad B<3349/2000.                         \tag{1}
\]
For the second bound, \(B^2=(3R^2-2Rh-h^2)/4\) is
increasing in \(R\) and decreasing in \(h\ge0\) when \(h<R\).
The exact endpoint square gap is
\[
(3349/2000)^2-
\frac{3(9894/5000)^2-2(9894/5000)(13/100)-(13/100)^2}{4}
=6017/100000000>0.
\]

## 2. All three actual vertical chords exceed 9796/10000

For one square, modulo symmetries let its unsigned tilt be
\(0\le\theta\le\pi/4\). Write
\[
c=\cos\theta,\quad s=\sin\theta,\quad
L=c+s\in[1,\sqrt2],\quad cs=(L^2-1)/2.
\]
Its horizontal projection of width \(L\) lies inside \([h,R]\),
so its open vertical section at \(x=X\) has positive length \(\ell\).
The exact section formula is \(\ell=1/c\ge1\) on the
parallel-side plateau (including the axis-parallel limit), or
\[
\ell=\frac{L/2-|X-p_x|}{cs}
\ge\frac{2(L-m)}{L^2-1}                      \tag{2}
\]
on a sloping flank. The final function strictly decreases
on \(1<L\le\sqrt2\), since its derivative numerator is
\(-2[(L-m)^2+(1-m^2)]<0\) by \(m<1\). Therefore
\[
\ell\ge2(\sqrt2-m)=2\sqrt2-R+h
>2(7071/5000)-9894/5000+13/100
=9796/10000=:\lambda.                       \tag{3}
\]
Here \(\sqrt2>7071/5000\) follows by squaring.
This reserve holds for every frame and center position.

## 3. Extreme-chord center bounds

Order the three disjoint open vertical chord intervals at \(x=X\).
Write \(S\) for the topmost square, \(L\) for its projection width,
\(\ell_S\) for its chord length, and \(p=(p_x,p_y)\) for its center.
The lower endpoint of its chord is at least
\(-B+\ell_{\rm bottom}+\ell_{\rm middle}\).
Its upper chord endpoint cannot exceed the top of the square's
full vertical projection \(p_y+L/2\). Thus, from (1)–(3),
\[
p_x\ge h+L/2\ge13/100+L/2,\qquad
p_y>-3349/2000+2\lambda+\ell_S-L/2.       \tag{4}
\]
We prove \(|p|>1\) in two **exhaustive** ranges of \(L\).

### Case I: \(1\le L\le69/50\)

The top chord has \(\ell_S\ge1\).
This is immediate on a plateau or for zero tilt. On a
sloping flank, (2) is at least one provided
\[
(L-1)^2\le2(1-m).
\]
Indeed, \((L-1)^2\le(19/50)^2=361/2500\),
while \(m<2311/2500\) gives
\(2(1-m)>378/2500>361/2500\).

Consequently (4) gives
\[
p_x+p_y>
13/100-3349/2000+2(9796/10000)+1
=14147/10000>\sqrt2,                    \tag{5}
\]
where \((14147/10000)^2-2
=137609/100000000>0\).
Cauchy--Schwarz implies \(|p|^2\ge(p_x+p_y)^2/2>1\).

### Case II: \(69/50<L\le\sqrt2\)

Using \(\ell_S>\lambda\) in (4), set
\[
K=3\lambda-3349/2000=12643/10000.
\]
Then
\[
p_x\ge13/100+L/2>0,\qquad p_y>K-L/2>0.
\]
For the last inequality, \(L\le\sqrt2<3/2\), and
\(K-3/4>0\). Hence
\[
|p|^2>
F(L):=(13/100+L/2)^2+(K-L/2)^2.
\]
The exact derivative is
\[
F'(L)=13/100+L-K>0
\quad\text{for }L\ge69/50.
\]
Therefore
\[
|p|^2>F(69/50)
=(82/100)^2+(5743/10000)^2
=100222049/100000000>1.                 \tag{6}
\]

Both cases show the center of the **topmost** chord square has
norm \(>1\). Reflection \(y\mapsto-y\) gives the same result
for the **bottommost** chord square. Their chord intervals are
distinct, so the two outer centers correspond to different
squares. QED.

## Exact consequences for the n=8 status queue

Let \(k\) be the number of exterior squares with center norm at
least one. In the all-seven-single-side cases, different cap
populations are different square labels. Therefore:

* S1=(3+0,3+1): if either triple side offset is \(\ge13/100\),
  the two disjoint triple populations plus the 3+1 opposite singleton
  give \(k\ge4\). Hence S1/k=3 requires **both** triple offsets
  \(<13/100\), in addition to the sharper shared-cap constraint
  \(\min(h_{\mathrm{triple},1},h_{\mathrm{triple},2})<1/11\).
* S2=(3+0,2+2): if its triple offset is \(\ge13/100\), then
  \(k\ge4\); when additionally the 2+2 central coordinate
  satisfies \(|t|\le1/10\), the opposite-cap center count yields
  \(k\ge5\).
* S3=(3+1,2+1): if its triple offset is \(\ge13/100\), then
  \(k\ge4\). Thus S3/k=3 requires a triple offset below \(13/100\)
  and (independently) its 2-member side offset below \(2/5\).
* Saturated Type A (3+1,3+1) with its unique shared RU member:
  if both triple offsets are \(\ge13/100\), the two triple
  populations provide at least three **distinct** outer centers
  (two from each triple, at most one overlapping at RU), and
  their two opposite singletons are also outer. Hence \(k\ge5\).

These are strengthened *joint outer-center/continuous-position*
necessary conditions, not a decrease in the purely symbolic
twelve-status count. The source \(7/50\) theorem remains true
and is subsumed at offsets \(\ge7/50\). The global sharp lower
bound \(R_8\ge\widehat R\) and the equality-preserving S4 branch
remain open and intact.

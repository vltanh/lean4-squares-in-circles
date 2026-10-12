# Perpendicular three-square caps: a sharper common-piercing threshold

Research continuation, 2026-10-12. This improves
[HUMAN_PERPENDICULAR_TRIPLE_FIXED_POINT.md](HUMAN_PERPENDICULAR_TRIPLE_FIXED_POINT.md)
by tightening its elementary midpoint-slice argument. Written **hand proof**,
not a Lean formalization. Each numeric inequality is an exact rational comparison.

## Theorem (arbitrary square frames; threshold 1/11)

Let eight pairwise interior-disjoint unit squares lie in a disk of radius
\(\sqrt2+1/2<R\), \(R^2\le9789/2500\).
Let \(C\) be the unique origin-containing square. Suppose three whole
exterior squares lie beyond its right side \(x=h_R\) and three whole
exterior squares lie beyond its upper side \(y=h_U\), with
\[
h_R\ge1/11,\qquad h_U\ge1/11.
\]
Then the two triple populations **share an actual square label**, with
both R and U whole-square side membership. There is no assumption about
the square frames, physical contacts, force equilibrium, or center norms.

### Preliminary triple-cap cutoff

The sharp arbitrary-frame theorem in
[HUMAN_THREE_SQUARE_CAP.md](HUMAN_THREE_SQUARE_CAP.md)
gives \(R^2\ge(h+1)^2+9/4\) for three whole squares in a cap of
offset \(0\le h\le1/3\). If \(h\ge1/3\), the same three squares
belong to the smaller-offset cap at \(h=1/3\), implying
\(R^2\ge145/36>9789/2500\), impossible.
Thus \(h<1/3\). More precisely,
\[
h<5813/20000
\]
since \((1+5813/20000)^2+9/4-9789/2500
=70969/400000000>0\).
We shall also use
\[
191/100<R<9894/5000,
\]
from \(R>\sqrt2+1/2\), \(\sqrt2>141/100\),
and \((9894/5000)^2-9789/2500=309/6250000>0\).

### 1. A rational common midpoint strip

For \(1/11\le h<5813/20000\), put
\[
X=(R+h)/2,\qquad m=(R-h)/2,\qquad
B=\sqrt{R^2-X^2}.
\]
Then
\[
1<X<45389/40000,\qquad m<1,\qquad
B<16867/10000.                                     \tag{1}
\]
For the first inequality,
\[
X>(191/100+1/11)/2=2201/2200>1
\]
and
\[
X<(9894/5000+5813/20000)/2=45389/40000.
\]
Also \(m<(9894/5000-1/11)/2<1\).
Finally \(B^2=(3R^2-2Rh-h^2)/4\) increases in \(R\) and decreases
in \(h\ge0\). Therefore
\[
(16867/10000)^2-
\frac{3(9894/5000)^2-2(9894/5000)(1/11)-(1/11)^2}{4}
=2799701/12100000000>0,
\]
proving the last inequality in (1).

### 2. Sharp-form uniform midpoint chord reserve

For any whole square in the cap, reduce its unsigned tilt modulo a
quarter-turn to \(0\le\theta\le\pi/4\), and put
\(c=\cos\theta\), \(s=\sin\theta\),
\(L=c+s\in[1,\sqrt2]\), \(cs=(L^2-1)/2\).
Its horizontal projection of length \(L\) is contained in \([h,R]\).
The line \(x=X\) consequently has an open chord through the square,
of length \(\ell\).
At zero tilt \(\ell=1\), and at nonzero tilt
the exact vertical-chord formula is \(\ell=1/c\ge1\)
on the parallel-side plateau, or
\[
\ell=\frac{L/2-|X-p_x|}{cs}\ge
\frac{L-m}{cs}
=\frac{2(L-m)}{L^2-1}
\]
on a sloping flank (since \(|X-p_x|\le m-L/2\)).

For \(1<L\le\sqrt2\), the final rational function is
**strictly decreasing in \(L\)**. Its derivative has numerator
\[
-2\big((L-m)^2+(1-m^2)\big)<0,
\]
because \(m<1\). Therefore
\[
\ell\ge2(\sqrt2-m)=2\sqrt2-R+h
>2(7071/5000)-9894/5000+1/11
=6466/6875>9405/10000.                            \tag{2}
\]
For the penultimate inequality, \((7071/5000)^2<2\);
the last exact difference is \(1/110000>0\).
The plateau and axis-parallel cases satisfy (2) as well.
Thus all three cap squares have actual open vertical chords
longer than \(9405/10000\), independently of all orientations.

### 3. One actual square contains a fixed segment

Order these three disjoint chord intervals from bottom to top.
All lie inside the disk chord \([-B,B]\).
If \((y_-,y_+)\) denotes the topmost interval, then (1)–(2) give
\[
y_+\ge -B+\ell_1+\ell_2+\ell_3
>-16867/10000+3(9405/10000)
=11348/10000>45389/40000,
\]
where the last margin is \(3/40000>0\). Also
\[
y_-\le B-\ell_\mathrm{top}
<(16867-9405)/10000=7462/10000<1.
\]
Thus **one actual square contains, in its open interior, the full
closed segment**
\[
\{X\}\times[1,45389/40000].                         \tag{3}
\]

Applying the same argument with \(x,y\) swapped to the perpendicular
upper triple yields one actual square containing
\([1,45389/40000]\times\{Y\}\), \(Y=(R+h_U)/2\).
By (1), \(1<X,Y<45389/40000\), so the two open-interior segments
cross at \((X,Y)\). Interior disjointness forces the selected squares
to be the **same label**, and that label lies wholly beyond both
central sides. Reflections and right-angle rotations treat every
pair of adjacent central sides. QED.

## Consequences: S1 central displacement and transverse lane

For all-seven-exclusive-single-side type S1=(3+0,3+1), the two
perpendicular triple populations have **no common square**. Hence
\[
\min(h_{\mathrm{triple},1},h_{\mathrm{triple},2})<1/11.
\]
Normalize those triples as right/upper with central center \(p_C=(a,b)\),
so \(h_R=1/2+a\), \(h_U=1/2+b\). Then
\[
\boxed{\min(a,b)<-9/22}.
\]
This improves the original \(1/10\) threshold and the intermediate
\(11/120\) threshold; it applies regardless of the outer-center count.

If that small-offset triple is on the 3+1 axis, the opposite singleton's
whole cap offset is \(h_\mathrm{opp}=1-h>10/11\).
The arbitrary-frame cap-center envelope
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md)
gives, for its transverse center coordinate \(z\),
\[
(|z|+1/2)^2\le R^2-(1+h_\mathrm{opp})^2
<9789/2500-(21/11)^2<(25/48)^2.
\]
The exact final difference is \(51481/174240000>0\), so
\[
\boxed{|z|<1/48}.
\]
No such transverse-center bound is inferred when the
small-offset triple is instead on the 3+0 axis.

## Status and scope

This is a full-domain analytic proof conditional only on the cited
existing hand lemmas. The entire small-offset S1 branch is **not**
eliminated; nor is the unrestricted inequality \(R_8\ge\widehat R\)
established. No Lean proof, generated case classifier, or sampled
minimum is used as a premise. The S4 seven-outer equality case remains
valid and must not be discarded.

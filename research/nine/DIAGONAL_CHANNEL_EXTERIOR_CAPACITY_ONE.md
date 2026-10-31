# Every actual diagonal channel has exterior capacity at most one above radius two

Date: October 26, 2026.

**Status: accepted complete whole-channel analytic theorem after full-source,
arithmetic and physical-scope reviews in
REVIEW_DIAGONAL_CHANNEL_CAP_AND_93_ARC_ROOT_2026_10_26.md and
REVIEW_DIAGONAL_CHANNEL_CAP_AND_93_ARC_BLOCK_2026_10_26.md.** The proof uses no
alternating-three-load turn restriction and no coefficient certificate.
The entire five-load diagonal corollary is included in both reviews.

## 1. Original channel scope

Let all actual unit squares be interior-disjoint in the same disk, with
\[
2\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The entire selected positive component is a simple cycle with at least
three loaded bodies. Let \(X,V,Y\) be one of its original channels,
where \(V\) is a true unloaded degree-two diagonal transmitter.

Keep the original strict point-normal and compatible diagonal-avoidance
conventions. They force the two actual vertices of \(V\) to meet
relative interiors of sides of \(X,Y\). The channel direction is
therefore an actual side axis of both endpoints. Both physical circle
masks, every individual nonnegative corner weight and all other
original forces and means are retained.

Use the proper endpoint and actual channel-cap conclusions of
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md and
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. Reflect and relabel once to write
\[
\begin{gathered}
X=[-a,1-a]\times[b-1,b],\qquad
Y=[c-1,c]\times[d-1,d],\\
a+c=A:=2+\sqrt2,\qquad
a^2+b^2=c^2+d^2=R^2,\\
a,c>\frac12,\qquad b,d\ge\frac12.
\end{gathered}
\tag{2}
\]
The nonnegative center heights in the cited channel theorem give the
last weak inequalities; equality is deliberately retained for a
physical radial endpoint. The strict opposite horizontal center
signs give \(a,c>1/2\). The farthest endpoint corners are the actual
circle points
\[
z_X=(-a,b),\qquad z_Y=(c,d).
\]

The unchanged applications and transmitter center are
\[
P_X=(1-a,h),\qquad P_Y=(c-1,h),\qquad
c_V=\left(\frac{c-a}{2},h\right),
\tag{3}
\]
where the full original mean restrictions are
\[
h>0,\qquad b-1<h<b,\qquad d-1<h<d.
\tag{4}
\]
No transverse application is reset.

**Theorem.** The whole actual exterior \(X-V-Y\) pocket has capacity
at most one additional physical unit square.

Its proof applies to every radius and actual endpoint mask in (1).
It uses the proper unique-corner concurrence only at the endpoint
identified in Section 2, where that physical mask is proved.

## 2. A uniform original height bound

Every endpoint in (2) gives
\[
a,c\le\sqrt{R^2-\frac14}
\le\frac{\sqrt{1041}}{16}<\frac{81}{40}.
\]
Since \(A>17/5\),
\[
\boxed{\frac{11}{8}<a,c<\frac{81}{40}.}
\tag{5}
\]
The last radical comparison follows by squaring.

Relabel \(X,Y\) so that \(a\le c\). Thus \(a\le A/2\) and \(b\ge d\).
By (1),
\[
b^2=R^2-a^2\ge4-\frac{A^2}{4}
=\frac52-\sqrt2>1.
\tag{6}
\]
Therefore \(a,b>1/2\), and \(X\) has exactly one physical circle
corner \(z_X=(-a,b)\). This remains true even if \(Y\) is physically
radial.

The original degree-two proper-concurrence theorem puts \(q_X\)
inside this physical-unique square on the positive ray through \(z_X\).
Its channel line is \(y=h\), so
\[
q_X=\frac hb(-a,b).
\]
The actual right supporting face of \(X\) consequently gives
\[
-\frac{ah}{b}\le1-a,\qquad
\boxed{h\ge b\left(1-\frac1a\right).}
\tag{7}
\]
This is an inequality for the original mean \(h\). It is not asserted
for a radial concurrence outside its body.

We prove
\[
\boxed{h>\frac{43}{100}.}
\tag{8}
\]
There are two continuous scalar intervals, with no sampled parameter
subdivision.

### 2.1. The whole interval \(11/8\le a\le3/2\)

Since the other corner height satisfies \(d\ge1/2\),
\[
b^2=R^2-a^2=c^2+d^2-a^2
\ge A^2-2Aa+\frac14.
\]
Hence the square of the right side of (7) is at least
\[
G(a)=\left(A^2-2Aa+\frac14\right)\frac{(a-1)^2}{a^2}.
\]
Its derivative is
\[
G'(a)=\frac{2(a-1)}{a^3}
\left(A^2+\frac14-Aa(a+1)\right).
\tag{9}
\]
The expression in parentheses strictly decreases with \(a\).
Thus the derivative can only change sign from positive to negative,
and the minimum on the full interval is at an endpoint.

At the left endpoint,
\[
G(11/8)=\frac{9(3+5\sqrt2)}{484}
>\frac{45}{242}>
\frac{1849}{10000},
\]
where the last exact reserve is \(1271/1210000\).
At the other endpoint,
\[
G(3/2)=\frac{\sqrt2+1/4}{9}
>\frac{659}{3564}>
\frac{1849}{10000}.
\]
Here \(\sqrt2>140/99\), and the last exact reserve is
\(41/8910000>0\). The radical comparison has squared reserve
\(2-(140/99)^2=2/9801>0\).

### 2.2. The whole interval \(3/2\le a\le A/2\)

Now (1) gives \(b^2\ge4-a^2\), so the square in (7) is at least
\[
F(a)=(4-a^2)\frac{(a-1)^2}{a^2}.
\]
Its derivative is
\[
F'(a)=\frac{2(a-1)}{a^3}(4-a^3).
\tag{10}
\]
Again the only possible interior critical point is a maximum.
The two endpoint values satisfy
\[
F(3/2)=\frac7{36}
=\frac{1849}{10000}+\frac{859}{90000},
\]
\[
F(A/2)=\frac{23}{2}-8\sqrt2
>\frac{13}{70}
=\frac{1849}{10000}+\frac{57}{70000}.
\]
The strict comparison uses \(\sqrt2<99/70\), whose squared reserve
is \((99/70)^2-2=1/4900>0\).
Both intervals give (8), since every quantity in (7) is positive.

By the actual whole-pocket cap theorem, every extra \(E\) in this
pocket lies wholly in \(\{y\ge h\}\). Its vertical halfwidth is at
least one half. Thus
\[
|c_E|\ge(c_E)_y\ge h+\frac12>\frac{93}{100}.
\tag{11}
\]
ANNULAR_CENTER_ARC_AT_93_100.md now gives a connected open arc longer
than \(\pi/4\) on the circle of radius \(r=5/4\), lying inside
\(E^\circ\) and containing its radial center direction.

## 3. The entire free endpoint interval is shorter than a right angle

Put
\[
x=a-1,\qquad y=c-1,\qquad x+y=\sqrt2.
\tag{12}
\]
By (5), \(0<x,y<41/40<r\), and \(a,c>r\). Define principal angles
\[
\lambda_a=\arccos(x/r),\qquad
\lambda_c=\arccos(y/r),
\]
\[
\mu_b=\arcsin(\min(b/r,1)),\qquad
\mu_d=\arcsin(\min(d/r,1)).
\tag{13}
\]

On the upper \(r\)-semicircle, \(X\) has its actual gap-facing arc
endpoint at
\[
\phi_L=\pi-\min(\lambda_a,\mu_b),
\]
and \(Y\) has its actual gap-facing endpoint at
\[
\phi_R=\min(\lambda_c,\mu_d).
\tag{14}
\]
Indeed the outer horizontal faces \(x=-a\), \(x=c\) lie beyond this
inner circle. At \(X\)'s gap-facing end the only possible active
faces are its right face or its top face; at \(Y\)'s end they are
its left face or its top face. The lower faces cut the opposite
ends of the respective arcs. Formula (14) includes top faces beyond
the inner circle through the clipping in (13).

We prove all four comparisons
\[
\lambda_a+\lambda_c>\pi/2,\quad
\mu_b+\mu_d>\pi/2,\quad
\lambda_a+\mu_d>\pi/2,\quad
\mu_b+\lambda_c>\pi/2.
\tag{15}
\]
They imply
\[
\boxed{\phi_L-\phi_R
=\pi-\min(\lambda_a,\mu_b)-\min(\lambda_c,\mu_d)<\pi/2.}
\tag{16}
\]

### 3.1. Both vertical-face angles

Equations (12) and (5) give
\[
x^2+y^2<\frac{41}{40}(x+y)
=\frac{41}{40}\sqrt2
<\frac{41}{28}<\frac{25}{16}=r^2,
\tag{17}
\]
using \(\sqrt2<10/7\); the final reserve is \(11/112>0\).
For positive \(x,y<r\), (17) is exactly the first comparison in
(15).

### 3.2. Both horizontal-face angles

If \(b\ge r\) or \(d\ge r\), one clipped angle is \(\pi/2\) and
the other is positive. Otherwise it suffices to show
\(b^2+d^2>r^2\).

Put \(L=\sqrt{R^2-1/4}\). The full domain of \(a,c\) is contained
in \([A-L,L]\), with \(a+c=A\). Convexity of their squared sum gives
\[
\begin{split}
b^2+d^2
&=2R^2-a^2-c^2\\
&\ge2R^2-\{L^2+(A-L)^2\}\\
&=2AL-A^2+\frac12\\
&\ge A\sqrt{15}-A^2+\frac12\\
&>2-\frac{\sqrt2}{4}
>\frac{13}{8}>\frac{25}{16}.
\end{split}
\tag{18}
\]
Here \(R\ge2\), \(\sqrt{15}>15/4\), and \(\sqrt2<3/2\) were used.
All are strict fixed radical comparisons; \(13/8-25/16=1/16\).
This proves the second inequality in (15).

### 3.3. Each mixed pair of faces

We show \(d>x=a-1\). If \(x<1/2\), this follows from \(d\ge1/2\).
For \(1/2\le x\le41/40\), the convex polynomial
\[
J(x)=x^2+(1+\sqrt2-x)^2
\]
has maximum at an endpoint. Its endpoint values satisfy
\[
J(1/2)=\frac52+\sqrt2<4,
\]
\[
J(41/40)=\frac{2441}{800}-\frac{\sqrt2}{20}
<\frac{2441}{800}<4.
\]
Since \(c=1+\sqrt2-x\) and \(R^2\ge4\), this gives
\[
d^2=R^2-c^2>x^2,\qquad d>x.
\tag{19}
\]
If \(d\ge r\), the relevant mixed angle comparison is immediate.
If \(d<r\), monotonicity gives
\[
\lambda_a+\mu_d
=\arccos(x/r)+\arcsin(d/r)>\pi/2.
\]
Reflection proves \(b>y=c-1\) and the other mixed comparison.
All of (15), hence (16), are now established.

## 4. Full actual pocket routing into that one interval

The physical exterior pocket is the bounded side of the unchanged
occupied crosscut
\[
z_X-P_X-P_Y-z_Y
\tag{20}
\]
and its outward outer-circle arc. All of this Jordan boundary lies
above the original height \(h>0\). Both applications are in the
strict side interiors, so the two selected upper circle corners
in (2) lie strictly above \(h\). The proper channel and physical
cyclic-order theorem identifies this upper arc as the actual exterior
one. Another physical circle corner or a zero-weight contact may
subdivide the pocket and cannot enlarge it.

Both endpoint units meet the inner circle in connected closed arcs;
their upper-semicircle restrictions are also intervals. This follows
directly from their axis-parallel rectangles in (2), and also from
the whole boundary-arc theorem ANNULAR_CENTER_ARC_AT_23_25.md.
Each full connected endpoint arc contains its radial center direction
in its relative interior. Its upper-semicircle restriction contains
that direction, possibly at angle zero or pi when the endpoint center
height is zero. Indeed the endpoint center radius is greater
than \(R-1/\sqrt2>5/4\) and less than \(91/60\), so its radial
\(r\)-circle point is strictly inside its radius-one-half incircle.

The left endpoint radial point has first coordinate strictly below
\(1-a\), and the right endpoint radial point has first coordinate
strictly above \(c-1\). Because cosine decreases on the upper
semicircle, every intersection of the middle segment \(P_XP_Y\)
with that semicircle lies between the two endpoint center directions.
The other two segments of (20) lie inside the corresponding closed
endpoint units.

Now take any inner-circle point of \(E^\circ\), for a pocket extra
\(E\). It is strictly above \(h\) and avoids both closed endpoint
units. If it were below the right endpoint's center angle and
outside its closed arc, the upper-circle path toward angle zero
would avoid both endpoint arcs and the middle segment, as well as
the outer-circle arc since \(R>r\). The positive horizontal ray
then escapes to infinity below height \(h\), contradicting membership
in the bounded pocket. The reflected path toward angle \(\pi\)
excludes an angle above the left endpoint center. Endpoint center
angles equal to zero or \(\pi\) cause no exceptional case.

Thus every such point lies between the two endpoint center directions.
Avoiding the two connected closed endpoint intervals confines it to
the single actual gap
\[
\phi_R<\phi<\phi_L.
\tag{21}
\]
The bounds (14) therefore apply to every open inner-circle arc of
every actual pocket extra. There is no center-sector assumption.

The original compact-interior routing convention carries the same
argument through any weak junction and every allowed original mean
endpoint. No new application or orientation is chosen.

## 5. Capacity and the whole five-load diagonal exit

If two actual extras occupied this pocket, (11) and
ANNULAR_CENTER_ARC_AT_93_100.md would supply two disjoint open
inner-circle arcs, each of length greater than \(\pi/4\).
They would both lie in the single interval (21), whose length is
strictly below \(\pi/2\) by (16). This is impossible. The whole
channel pocket has capacity at most one, proving the theorem.

For the original five-load bare cycle
\[
V-S_1-S_2-S_3-S_4-S_5-V,
\]
SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md already gives central
capacity at most one and places all other extras in this sole
actual channel cap. The same-nine theorem
NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md gives \(R>2\),
so the radius premise (1) is present for that full nine-square
completion. The new diagonal cap bound allows at most one additional
extra there. At most two extras are possible altogether, contradicting
the three original physical extras.

**Consequently the entire five-load bare-C6 diagonal-transmitter
family is excluded**, including every physical endpoint mask, every
zero individual radial weight and all other three loaded-body masks.

Together with the already accepted radial side-channel exit, the
only five-load width/mask row still requiring completion is a
width-one transmitter with both channel endpoints physically unique.
The complete original five-load gate is not closed by this source.

The general diagonal cap theorem applies to other entire positive
simple cycles under the stated actual premises, but their other
central and exterior allocations must be counted separately.
No finite coefficient packet, numerical angle test, new force choice,
Lean compilation or CI enters the proof.


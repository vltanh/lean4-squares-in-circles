# All genuinely shared adjacent-root C4/S-S cores have one exact geometry

Date: October 26, 2026.

**Status: complete hand rigidity argument, pending independent review.**
This is a necessary geometry theorem for an entire actual feature family
of the original M6.B4L2.C4.ADJACENT.LCD.SS gate. It is not a core
exclusion: the unique geometry has the positive stress exhibited in
ADJACENT_C4_TWO_S_LEAVES_POSITIVE_CORE_CONTROL.md.

Work in the common selected certificate and radius window
\[
79/40\le R\le\sqrt{1105}/16.
\]
The actual positive component has cycle \(A-B-C-D-A\), one genuine
S leaf at each of \(A,B\), and loaded vertices \(C,D\). The roots
are the actual unloaded degree-three vertices; \(C,D\) are the
actual loaded degree-two vertices. Retain the full nine-square packing
and all three arbitrary completion units.

Assume all four actual cycle intersections are positive-length shared
sides. Their aggregate force applications may be anywhere on their
actual intersections, including endpoints. No application is chosen
or made a midpoint.

**Theorem.** Up to a rigid orthogonal change of coordinates fixing the
circle center, the six actual units have exactly the geometry
\[
\begin{aligned}
A=[-1,0]\times[-b,1-b],\qquad&
B=[0,1]\times[-b,1-b],\\
D=[-1,0]\times[1-b,2-b],\qquad&
C=[0,1]\times[1-b,2-b],
\end{aligned}
\tag{1}
\]
where
\[
b=\frac{22-\sqrt{313}}{24},\qquad
d=\frac{2\sqrt{313}-11}{24},\qquad
R^2=\frac{1565+52\sqrt{313}}{576}.
\tag{2}
\]
The genuine S leaves are
\[
L_\pm=(\pm1,-b)+[0,1]e_\pm+[-1/2,1/2]Je_\pm,
\qquad e_\pm=(\pm1,-b)/d.
\tag{3}
\]
The four shared-side means are not determined by this geometry theorem.
It uses only the original force equations, not an imposed torque or
mean relation.

## 1. The full shared-edge direction cover

Throughout the original radius window,
\[
\frac9{10}<d:=\sqrt{R^2-1/4}-1<\frac{61}{60}.
\tag{4}
\]
Section 2 below derives the stronger strict bound `d>1` directly
from the actual shared-root force equations. No separate lower-window
exclusion is required for this feature family.
The original S-leaf theorem supplies the true radial singleton
application \(d e\) at each leaf root and the entire radial rectangle
\(d e+[0,1]e+[-1/2,1/2]Je\). No force is deleted to obtain it.

A positive-length shared side makes the two units' side frames agree,
up to exchanging and reversing their axes. The cycle is connected, so
all four units share one aligned frame. Each actual shared edge has
one of its two coordinate axes as its normal. Along that axis the two
center coordinates differ by exactly one; along the other axis their
difference is strictly less than one, because the intersection length
is positive.

There are only the following complete possibilities for the cycle's
four axis labels.

### 1.1. An odd number on either axis is impossible

If three edges have horizontal normals and one has a vertical normal,
the sum of the three signed horizontal center increments is an odd
integer, of absolute value at least one. The remaining increment has
absolute value strictly less than one and cannot make the sum zero.
Interchanging axes excludes the complementary odd count.

### 1.2. Four parallel normals are impossible at the actual loaded pair

Suppose all four normals are horizontal. The full degree-two equations
at \(C,D\) make their nonzero circle forces horizontal. For an aligned
contained unit, all physical circle corners have the same strict sign
of their vertical coordinate unless its center has vertical coordinate
zero. Indeed the farthest corner height has the sign of the center,
with an additional absolute height \(1/2\). Thus a nonzero positive
circle resultant with zero vertical component forces that center
coordinate to be zero.

The actual physical square is then horizontal radial S, with center
one of \((d+1/2,0)\) and \((-d-1/2,0)\). Two distinct such units
either coincide or have center separation \(2d+1>14/5>\sqrt2\).
They cannot be the physically touching pair \(C,D\). The vertical
case is identical after rotation.

This argument allows either individual circle coefficient to be zero:
the only input is the true nonzero resultant and the signs of all
possible physical circle corners.

### 1.3. Two labels of each kind must alternate

Suppose instead that the horizontal edges are consecutive, say \(AB\)
and \(BC\). If their signed horizontal increments agree, then
\(|c_{C,x}-c_{A,x}|=2\), whereas the other two, vertically normal
edges have horizontal increments of absolute value less than one.
This is impossible. Hence the two horizontal increments cancel and
\(c_{C,x}=c_{A,x}\). The same argument for the consecutive vertical
edges gives \(c_{C,y}=c_{A,y}\), contradicting distinct interiors.

Thus the axis labels alternate. Their two signed increments on each
axis must be opposite, by the same strict tangential-increment
argument. Reflections now put \(AB\) to the right, \(BC\) upward,
\(CD\) to the left and \(DA\) downward. This is a derived full
normal pattern, not a restriction to a displayed representative pose.

## 2. Keep all sliding coordinates and the true leaf applications

There are real parameters \(x,y,a,b_1\) such that the four complete
physical units are
\[
\begin{aligned}
A&=[x-1,x]\times[a,a+1],&
B&=[x,x+1]\times[b_1,b_1+1],\\
D&=[y-1,y]\times[a+1,a+2],&
C&=[y,y+1]\times[b_1+1,b_1+2].
\end{aligned}
\tag{5}
\]
The positive shared lengths impose further strict interval-overlap
conditions, all retained. None is replaced by a full-side coincidence.

Write \(\mu,\nu,\alpha,\beta>0\) for the actual magnitudes on
\(AB,DC,AD,BC\), respectively. The complete root balances give
the actual root-to-leaf vectors
\[
F_{L_A}=(-\mu,-\alpha),\qquad
F_{L_B}=(\mu,-\beta).
\tag{6}
\]
Each has two strict coordinate signs. Consequently it strictly exposes
the indicated outer lower root vertex. The genuine radial S-leaf
applications are exactly
\[
p_A=(x-1,a),\qquad p_B=(x+1,b_1),\qquad
|p_A|=|p_B|=d.
\tag{7}
\]
Their radial positive directions give
\[
-1<x<1,\qquad -d<a<0,\qquad -d<b_1<0.
\tag{8}
\]
Subtracting the squared equalities in (7) yields
\[
a^2-b_1^2=4x.
\tag{9}
\]

There is also a direct full-window consequence. Both negative heights
in (8) are strict, so (7) gives `|x-1|<d` and `|x+1|<d`.
Since `-1<x<1`, these two horizontal lengths sum to two. Hence

\[
                         2<2d,\qquad d>1,
                    \qquad R^2>17/4.
\tag{9a}
\]

This derives the required upper-radius restriction before any later
use of `d-1>=0`, including the formerly separate equality endpoint.

## 3. The two upper physical masks are necessarily unique

The actual degree-two balances at \(D,C\) are
\[
F_D=(-\nu,\alpha),\qquad F_C=(\nu,\beta).
\tag{10}
\]
Each is nonzero and points strictly upward.

The center heights of the two upper units are \(a+3/2\) and
\(b_1+3/2\), positive by (4),(8). For an aligned square whose
center height is positive, its physical circle corners can be two
only if its center abscissa is zero, in which case they are its two
upper corners. Such a vertical radial S unit has bottom height \(d\).
For \(D\), this would give \(a+1=d\), hence \(a=d-1\ge0\),
contrary to (8). The same contradiction holds for \(C\).

This explicitly excludes the two-corner physical mask, rather than
assuming equal or positive weights at both of its corners. A four-corner
mask would require the unit center to be \(O\) and \(R^2=1/2\),
outside (4). Thus both upper units have a unique physical circle
corner, whose coordinate signs must agree with (10). Those actual
corners are therefore
\[
z_D=(y-1,a+2),\qquad z_C=(y+1,b_1+2),
\tag{11}
\]
with \(-1<y<1\) and both heights positive. In particular
\[
(y-1)^2+(a+2)^2
 =(y+1)^2+(b_1+2)^2=R^2.
\tag{12}
\]
Subtracting gives
\[
(a-b_1)(a+b_1+4)=4y.
\tag{13}
\]

## 4. Original force ratios eliminate the entire sliding family

Put
\[
u=(a+b_1)/2,\qquad v=(a-b_1)/2.
\]
Equations (9),(13) become
\[
a=u+v,\quad b_1=u-v,\quad x=uv,\quad y=v(u+2).
\tag{14}
\]
The actual radial leaf vectors (6),(7) give
\[
\frac{\alpha}{\beta}
 =\frac{a(1+x)}{b_1(1-x)}.
\tag{15}
\]
The actual unique-corner forces (10),(11) give independently
\[
\frac{\alpha}{\beta}
 =\frac{(a+2)(1+y)}{(b_1+2)(1-y)}.
\tag{16}
\]
All divisions in (15),(16) are justified by (8),(11) and positivity;
no individual physical weight endpoint has been removed.

Cross multiplication and substitution of (14) yield the exact identity
\[
\begin{aligned}
0={}&a(1+x)(b_1+2)(1-y)
      -b_1(1-x)(a+2)(1+y)\\
 ={}&4v(1+v^2)\bigl(2-(u+1)^2\bigr).
\end{aligned}
\tag{17}
\]
Here \(-2<u<0\), since both \(a,b_1\) lie in \((-d,0)\)
and \(d<2\). Therefore \((u+1)^2<1\), so the last factor
in (17) is strictly positive. It follows that \(v=0\).

Hence \(a=b_1\), \(x=y=0\). The four whole units in (5)
form the solid rectangle (1), with \(b=-a=-b_1>0\).
This uses all four actual nonleaf magnitudes at the same time; it
does not impose symmetry of forces, roots, frames, or means in advance.

## 5. The radius and both genuine leaves are then fixed

The two physical radius equations now read
\[
d^2=1+b^2,\qquad R^2=1+(2-b)^2,
\qquad R^2=(d+1)^2+1/4.
\tag{18}
\]
Consequently
\[
2d+4b=11/4.
\tag{19}
\]
Because \(d\ge1\), (19) gives \(0<b\le3/16\). Substituting
\(d=11/8-2b\) in the first equation of (18) gives
\[
192b^2-352b+57=0.
\tag{20}
\]
Of its two roots \((22\pm\sqrt{313})/24\), only the negative-sign
root lies in \((0,3/16]\). Equations (18),(19) then give exactly
(2). The original leaf formula and the actual applications (7) give
the whole leaf rectangles (3), with their fixed radial frames.

The exact comparisons \(1/6<b<3/16\) and
\(17/4<R^2<1105/256\) are independently expanded in the positive
control source. The endpoint \(R^2=17/4\) cannot occur in this
genuinely shared four-edge family.

## 6. Meaning for the original gate and the completion problem

The theorem covers every actual positive-length shared-side choice on
all four cycle edges, including every allowed shared mean endpoint,
both physical masks initially permitted at \(C,D\), and all sliding
coordinates. It introduces no new case ID or computational certificate.
The entire lower radius interval and its equality endpoint are already
excluded by the actual root-force argument (9a).

The positive control source verifies a legitimate positive stress on
this unique geometry, with actual means in all four side interiors.
Thus the rigidity theorem is not an exclusion of the six-body core.
To exclude the all-shared feature from a nine-square packing, one still
has to bound the capacity of the complement of the six whole units
(1),(3) by two. All three completion squares remain unrestricted until
that physical theorem is established.

Other original owner patterns in M6.B4L2.C4.ADJACENT.LCD.SS are not
claimed to be shared or to have geometry (1). The original gate
remains open. No roadmap update, finite orientation table, force
deletion, post-certificate normal change, Lean compilation, CI, or
git operation is part of this result.

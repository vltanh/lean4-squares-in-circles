# The rigid adjacent-root C4/S-S core has completion capacity two

Date: October 26, 2026.

**Status: complete hand completion proof and feature-family join,
pending independent review.**
All three arbitrary physical completion squares are retained. The
capacity argument uses no force equations at those squares and no
shared orientation or separating-axis assumption.

The two reusable geometric ingredients are the accepted forty-degree
boundary-center separation in CENTERED_INNER_ARC.md and the new
central-clearance/cap theorem in
CENTRAL_CLEARANCE_CENTERED_ARC_AND_TWO_POINT_CAP.md.
The whole-unit pocket routing is proved below.

## 1. Exact physical core and the theorem

Put
\[
b=\frac{22-\sqrt{313}}{24},\qquad
d=\frac{2\sqrt{313}-11}{24},\qquad
R^2=\frac{1565+52\sqrt{313}}{576}.
\tag{1}
\]
The identities and estimates are
\[
d^2=1+b^2,\qquad
R^2=1+(2-b)^2=(d+1)^2+\frac14,
\tag{2}
\]
\[
\frac7{40}<b<\frac3{16},\qquad
1<d<\frac{61}{60},\qquad
\frac{17}{4}<R^2<\frac{1105}{256},\qquad R<\frac{25}{12}.
\tag{3}
\]
For the strengthened lower bound on \(b\), use
\(\sqrt{313}<89/5\); the remaining comparisons are also expanded
in ADJACENT_C4_TWO_S_LEAVES_POSITIVE_CORE_CONTROL.md.

The four actual aligned units form the solid rectangle
\[
K=[-1,1]\times[-b,2-b],
\tag{4}
\]
with lower row \(A,B\) and upper row \(D,C\), respectively from
left to right. Write
\[
p_\pm=(\pm1,-b),\qquad e_\pm=p_\pm/d.
\]
The two actual radial S leaves are
\[
L_\pm=p_\pm+[0,1]e_\pm+[-1/2,1/2]Je_\pm.
\tag{5}
\]
They meet \(K\) precisely at the respective points \(p_\pm\).
The two upper rectangle corners
\[
z_D=(-1,2-b),\qquad z_C=(1,2-b)
\tag{6}
\]
and the two outer corners of each leaf lie on the actual circle.
These six units are contained and pairwise interior-disjoint, as
verified in the positive-control source.

**Theorem 1.1.** At most two additional independently oriented physical
unit squares can be added to (4),(5) in the same disk. Consequently
this six-unit core cannot occur in a nine-unit packing.

The theorem is purely physical. Its application to the whole
all-shared feature family follows in Section 6 from
ADJACENT_C4_ALL_SHARED_SS_RIGIDITY.md. The positive six-body stress
itself is not contradicted; the obstruction is its three-square
completion.

## 2. The two side-pocket boundary centers have gap less than eighty degrees

Consider the right leaf. Write
\[
e=(1,-b)/d,\qquad f=(b,1)/d.
\]
Its center direction is \(-\arctan b\). The center of the upper
right unit \(C\) is \((1/2,3/2-b)\), with direction
\(\arctan(3-2b)\). Their minor center-angle gap is
\[
\beta=\arctan(3-2b)+\arctan b\in(0,\pi/2).
\tag{7}
\]
The complete interval (3) gives
\[
\cot\beta=\frac{1-3b+2b^2}{3-b}>\frac{13}{72}.
\tag{8}
\]
Indeed the derivative of the fraction in (8) is
\[
\frac{-8+12b-2b^2}{(3-b)^2}<0,
\]
and its value at \(b=3/16\) is \(13/72\).

Here is an exact angular comparison, without a decimal-angle premise.
Put \(\eta=\arctan(13/72)\in(0,\pi/6)\). The triple-angle
formula gives
\[
\tan(3\eta)=\frac{199979}{336744}>\frac1{\sqrt3},
\]
because
\[
3\cdot199979^2-336744^2=6578279787>0.
\tag{9}
\]
As \(3\eta\in(0,\pi/2)\), this implies
\(\eta>\pi/18\). Thus (8) implies
\[
\beta<\frac{4\pi}{9}.
\tag{10}
\]

Any two distinct physical circle-touching units have center-angle
separation strictly greater than \(2\pi/9\), by
CENTERED_INNER_ARC.md. Hence no third physical circle-touching
unit can have its center direction strictly between those of the
right leaf and \(C\) on this minor arc. The same statement holds
for the reflected left pair \(L_-,D\).

The center/circle-corner order theorem in
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Section 2, ensures the
corresponding open arc between their chosen circle corners also
cannot contain a circle corner of a third physical unit. This
includes both physical corners of each S leaf and permits zero
individual circle weights; the assertion is entirely geometric.

## 3. Dilation empties each whole side pocket

The right leaf's outer upper and lower corners are
\[
z_R^+=(d+1)e+\frac12f,\qquad
z_R^-=(d+1)e-\frac12f.
\tag{11}
\]
Their abscissas are greater than one. Their heights satisfy
\[
(z_R^+)_y=-b+\frac{1/2-b}{d}>-b,\qquad
(z_R^-)_y=-b-\frac{1/2+b}{d}<-b.
\tag{12}
\]
The right side pocket \(\Omega_R\) is bounded by the following
simple crosscut and the corresponding circle arc:
\[
z_C\longrightarrow p_+\longrightarrow z_R^+.
\tag{13}
\]
The first segment is the actual right edge of \(K\), and the
second lies in the actual leaf by convexity. The open circle arc
from \(z_R^+\) to \(z_C\) is the upper right arc. The whole pocket
lies in \(x\ge1\). Portions of the right leaf may lie inside this
pocket; they remain physical obstacles.

Every extra square's open interior avoids both closed obstacles and
therefore avoids the crosscut (13). If it lies in \(\Omega_R\),
it is initially strictly circle-clear, by the angular exclusion in
Section 2. The circle endpoints cannot be shared with another
contained unit.

Suppose one or more extras occupied this pocket. Move all such extras
simultaneously, preserving their orientations, by the center dilation
\[
c_j(s)=p_++s(c_j-p_+),\qquad s\ge1.
\tag{14}
\]
This preserves their separation from the entire solid rectangle \(K\),
not merely from one of its constituent squares. To check it, take
any original unit separator \(n\) from \(K\) to extra \(j\).
Because \(p_+\in K\),
\[
n\cdot p_+\le h_K(n)\le n\cdot c_j-H_j(n),
\qquad
n\cdot(c_j-p_+)\ge H_j(n)\ge\frac12.
\tag{15}
\]
The separation therefore improves under (14). Exactly the same
argument applies to the full right leaf, since \(p_+\in L_+\).
Every mutual separator among the moving squares is also preserved:
their center differences are multiplied by \(s\), while the two
support halfwidths are unchanged.

As long as the moving squares stay in the disk, their connected
interiors cannot cross the boundary crosscut, which lies in the
unchanged obstacles. They remain in \(\Omega_R\) and cannot meet
any fixed extra on its other side. The left leaf is on that other
side, since it lies in \(x<0\). Thus all actual physical units
remain separated throughout this motion.

Equation (15) shows every \(c_j-p_+\) is nonzero. A first outer
circle contact therefore occurs at a finite \(s_*>1\), with all
packing constraints still valid by continuity. Its new circle corner
must lie strictly on the open arc from \(z_R^+\) to \(z_C\):
the endpoints belong to the two unchanged boundary units, and the
moving interior stays in this pocket. This contradicts Section 2.
Hence \(\Omega_R\) contains no additional unit.

Reflection proves that the entire left side pocket is empty as well.
This argument uses simultaneous dilation only inside an actual
isolated complementary pocket; it does not move one extra through
uncontrolled completion units elsewhere in the disk.

## 4. All surviving extras are wholly below the rectangle

For completeness, the full physical routing has no omitted side wrap.
The six circle points consisting of (6) and the two corners of each
leaf are in their coordinate-determined circular order. Between
successive points, the outer complementary regions are:

1. the north cap between \(z_D,z_C\), with lower boundary the top
   edge of the solid rectangle;
2. the right pocket bounded by (13);
3. the cap outside the right leaf's outer face;
4. the lower region between the two leaves' outer lower corners;
5. the cap outside the left leaf's outer face;
6. the reflected left side pocket.

These are the whole free-region components, allowing subdivision by
occupied portions of the obstacles. One can obtain their separating
crosscuts directly from the top, side and bottom edges of \(K\),
the two segments from each \(p_\pm\) to its leaf's outer corners,
and each leaf's outer face. Every such crosscut lies in the actual
closed obstacles. The rectangle has no internal free region, and
each leaf meets it only at \(p_\pm\); the three-obstacle contact
graph is a tree, so there is no additional bounded hole. A connected
extra interior cannot cross any of these barriers.

Equivalently, the barrier graph has the four rectangle vertices and
the four outer leaf corners, hence eight vertices. Its four rectangle
edges, four root-to-leaf-corner segments and two leaf outer faces give
ten edges. It is connected and plane, with exactly three bounded
faces: the rectangle and two triangles already filled by the actual
obstacles. Adding the six actual circle arcs gives sixteen edges and
nine faces inside the circle. Removing the three filled faces leaves
exactly the six regions listed above. The remaining occupied leaf
portions may subdivide those regions but cannot create an additional
routing class.

The north cap has vertical width
\[
R-(2-b)<\frac{25}{12}-2+\frac3{16}=\frac{13}{48}<1.
\tag{16}
\]
Each leaf outer cap has width in its own radial direction
\[
R-(d+1)<\frac{25}{12}-2=\frac1{12}<1.
\tag{17}
\]
Every unit square has projection width at least one in every direction,
so none can occupy one of these three caps. The two side pockets were
excluded in Section 3.

The lower region's inner boundary runs from the left lower leaf corner
to \(p_-\), along \([p_-,p_+]\), and then to the right lower leaf
corner. By (12), every point of this boundary has height at most
\(-b\); the corresponding bottom circle arc has still smaller
height. Its entire bounded region is therefore in \(y\le-b\).
Taking closures of each surviving extra interior proves the genuine
whole-unit screen
\[
                         S_{\rm extra}\subset\{y\le-b\}.
\tag{18}
\]
This is stronger than a statement about center heights. It includes
every unit that might otherwise wrap obliquely around a lower
rectangle corner.

## 5. The two actual leaves occupy the outer cap-cover points

Reflect the vertical coordinate in (18), writing \(Y=-y\).
Then every whole extra lies in \(Y\ge b>1/6\).
The two fixed outer points required by Corollary 3 of
CENTRAL_CLEARANCE_CENTERED_ARC_AND_TWO_POINT_CAP.md are
\[
Q_\pm=\left(\pm\frac{11}{12},\frac23\right)
\]
in this reflected frame, or
\((\pm11/12,-2/3)\) in the original frame.

We verify their actual physical occupation, rather than placing
auxiliary obstacles. For \(Q=(11/12,-2/3)\), its own coordinates
in the right leaf frame are
\[
e\cdot Q=\frac{11/12+(2/3)b}{d},\qquad
f\cdot Q=\frac{(11/12)b-2/3}{d}.
\tag{19}
\]
The first coordinate exceeds \(d\), because
\[
\frac{11}{12}+\frac23b-d^2
 =-\frac1{12}+\frac23b-b^2>0.
\tag{20}
\]
The last expression vanishes at \(b=1/6\) and strictly increases
through the interval \(1/6<b<3/16\). The same coordinate is below
\(d+1\): its absolute value is at most
\[
|Q|=\frac{\sqrt{185}}{12}<\frac76<d+1.
\]

The second coordinate in (19) is negative. Its absolute value is
strictly below \(1/2\), since
\[
\left(\frac23-\frac{11}{12}b\right)^2<\frac{d^2}{4}
\quad\Longleftrightarrow\quad
85b^2-176b+28<0.
\tag{21}
\]
The polynomial on the right is decreasing for \(7/40<b<3/16\),
and its value at \(7/40\) is \(-63/320<0\). All quantities squared
in (21) are positive. Thus \(Q\) lies in the open interior of the
actual right leaf. Reflection puts the other point in the actual
left leaf.

The cap corollary now applies to the same actual extras. Every extra
whose center has nonnegative abscissa must contain
\[
P_+=\left(\frac13,-\frac{13}{12}\right)
\]
in its open interior, because its alternative outer cover point is
already occupied by the right leaf. Hence at most one such extra
exists. Every extra whose center has nonpositive abscissa similarly
contains \(P_-=(-1/3,-13/12)\), so there is at most one.
A center on the axis satisfies both statements and supplies no
additional class.

There are therefore at most two arbitrary extras. This proves
Theorem 1.1, retaining every completion unit's independent orientation,
contact features and possible zero stress.

## 6. Complete original feature-family join and limits

ADJACENT_C4_ALL_SHARED_SS_RIGIDITY.md proves that every actual
four-edge genuinely shared-side member of
M6.B4L2.C4.ADJACENT.LCD.SS has exactly the physical geometry
(1)--(5). It keeps all root forces, actual positive degrees, sliding
coordinates, initial physical circle masks and shared mean endpoints.
The present theorem excludes its entire nine-square completion,
including the exact positive six-body control. Thus the whole
all-four-shared feature family is now excluded upon independent review.

The axis-pattern cover in that rigidity source has a further direct
application to the corresponding two-loaded C4 family with a genuine
D leaf. It uses only the common frames and the actual loaded
degree-two pair \(C,D\) to force alternating horizontal/vertical
cycle normals. At either adjacent root, its two actual cycle forces
then have nonzero components on both perpendicular axes. Their sum
cannot balance a genuine D-leaf force, whose radial normal is an
actual root side axis. Thus the all-four-shared feature of
M6.B4L2.C4.ADJACENT.LCD.SD is already excluded by the true root
force equation. No force at the other root is omitted.

These are whole physical feature-family exits within the same original
IDs. The original gates also contain nonshared owner patterns, which
are not asserted to have this geometry and remain separate obligations.
No parent ID or coarse cell is declared closed solely by this result,
and no new checklist ID is introduced.

The central-clearance theorem and its two-obstacle cap corollary have
broader independent scope. Another original family may inherit the
same capacity-two conclusion once it proves an actual whole-unit
screen into a cap of depth \(1/6\) and physical occupation of the
two corresponding rational outer points. Those implications are not
assumed automatically here. No angle grid, computational coefficient
packet, Lean compilation, CI, or git operation is used in this proof.


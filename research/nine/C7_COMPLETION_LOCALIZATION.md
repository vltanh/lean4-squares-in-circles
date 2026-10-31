# Every completion square of a boundary seven-cycle lies inside the ring

**Status: complete hand geometric reduction, separately audited.** Let seven
interior-disjoint unit squares lie in the disk of radius

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\]

all touch the circle, and have the complete physical touching graph
\(C_7\). Any further unit squares in the same packing lie on the inner
side of the ring. No completion square can occupy an exterior pocket.
For a positive physical seven-cycle, every completion square is in fact
contained in the closed convex polygon of concurrence points constructed
in `C7_FORCE_POLYGON.md`.

This is a localization theorem, not the still-missing assertion that at
most one completion square fits. It does not assume regularity, common
orientations, or that a completion square contains the origin.

## 1. The elementary simultaneous dilation lemma

Let \(A,B\) be two fixed convex bodies with a common point \(p\),
and let \(T_1,\ldots,T_k\) be finitely many interior-disjoint unit
squares, each interior-disjoint from \(A\) and \(B\). Write
\(c_j\) for the center of \(T_j\), and \(H_j(a)\) for its support
halfwidth in a unit direction \(a\). Keep each square's frame fixed and
move its center to

\[
c_j(s)=p+s(c_j-p),\qquad s\ge1.                       \tag{1}
\]

This preserves all pairwise square separations and all separations from
\(A,B\). The separations from \(A,B\) are strict when \(s>1\).

Indeed, choose a separating unit normal \(a\) directed from \(A\)
to \(T_j\). Since \(p\in A\),

\[
a\cdot p\le h_A(a)\le a\cdot c_j-H_j(a),
\qquad a\cdot(c_j-p)\ge H_j(a)\ge\frac12.             \tag{2}
\]

Here \(h_A\) is the full support function of \(A\). The gap in the
same separating inequality increases under (1) by
\((s-1)a\cdot(c_j-p)>0\). The identical argument applies to \(B\).
For a separator \(n\) directed from \(T_j\) to \(T_l\),

\[
n\cdot(c_l-c_j)\ge H_j(n)+H_l(n)>0.
\]

Its left side is multiplied by \(s\), while its right side is unchanged.
Thus every such separation is preserved. All directions and support
halfwidths used here are those of the original physical squares; no
common frame is required.

The same lemma applies with just one fixed obstacle and any point
\(p\) in it. The two-body form is enough for the construction below.

## 2. An embedded ring and seven exterior cells

Number the ring squares \(S_0,\ldots,S_6\) in their circular center
order. Their only physical neighbors are consecutive squares. Choose
one contact point

\[
p_i\in S_i\cap S_{i+1}
\]

for each edge. At square \(S_i\), the points \(p_{i-1}\) and
\(p_i\) are distinct: otherwise three circle-touching squares would
share a point, contrary to `CYCLIC_GLOBAL_CONTINUATION.md`, Section 7.
Join the center \(C_i\) to these two contact points by segments.

Except for their boundary endpoints, these segments are in the open
square. Distinct square interiors are disjoint, nonconsecutive ring
squares do not touch, and the two segments from one center have distinct
rays. Consequently

\[
\Gamma=C_0p_0C_1p_1\cdots C_6p_6C_0                \tag{3}
\]

is a simple Jordan curve contained in the union of the ring squares.
It winds once positively around the origin: each consecutive link has
its angular image in the union of the two adjacent square shadows, an
arc of length less than \(2\pi/3<\pi\), and changes angle by the
positive consecutive center gap. These gaps sum to \(2\pi\). These
shadow and contact-order facts are proved in
`CIRCLE_CONTACT_ANGULAR_ORDER.md`.

Choose one circle corner \(z_i\) of each square and add the spoke
\([C_i,z_i]\). Its open segment lies inside \(S_i\) and meets
\(\Gamma\) only at \(C_i\): a second ray from the center can meet
this ray away from the center only if its contact endpoint is the same
boundary point, whereas a circle point cannot belong to two packing
squares. The latter fact follows directly from strict inward radial
containment at a circle corner. The seven spokes are mutually disjoint.
Their circle endpoints are distinct.

Every spoke lies on the exterior side of \(\Gamma\), since its
endpoint is on the outer circle and it cannot cross \(\Gamma\).
Cutting this annulus along the seven disjoint spokes gives seven open
cells. A cell between successive spokes has boundary consisting of

* the two spokes in \(S_i,S_{i+1}\);
* the ring link \(C_i p_i C_{i+1}\), also in those two squares; and
* the intervening outer-circle arc.

The order of the circle endpoints agrees with the ring order by Jordan
separation, or by cutting the annulus along one spoke and reading the
remaining disjoint crosscuts in the resulting disk. Thus these are
exactly the adjacent pairs \(S_i,S_{i+1}\).

No other ring-square interior enters such a cell. Its center is outside
the cell. To enter, its connected open interior would have to cross a
spoke or ring-link segment inside one of the two boundary bodies, the
shared point \(p_i\), or the outer circle. The first option violates
interior disjointness, the second violates the no-triple-circle-body
junction theorem, and the third violates disk containment. A chosen
spoke endpoint cannot be shared either.

A square may have a second circle corner. That can further subdivide an
exterior cell, but the relevant additional barrier is still part of one
of its two boundary bodies. No separate cap assumption is needed.

In particular, every connected component of the open disk minus
\(S_i\cup S_{i+1}\) that meets this cell is confined to the cell:
all of its other boundary paths are in those two obstacles. Any extra
square whose open interior is outside \(\Gamma\) lies in one such
cell, because it cannot cross any spoke or ring-link segment.

## 3. Every exterior cell is empty of additional unit squares

Suppose an exterior cell contains one or more completion squares. Take
all the completion squares in that cell. Fix its two boundary bodies
\(A=S_i\), \(B=S_{i+1}\), and the contact point \(p=p_i\).
Apply (1) simultaneously to the centers of these completion squares.
Leave all other squares fixed.

For \(s>1\), the moving squares are strictly separated from \(A\)
and \(B\), by Section 1. While all their corners remain in the disk,
continuity confines them to the same component of the disk minus
\(A\cup B\), and hence to the same exterior cell. They therefore
cannot meet any other ring square or any completion square in a different
cell or on the inner side of \(\Gamma\). Mutual nonoverlap within
the moving group is preserved by the same lemma.

Initially every completion square is strictly circle-clear, because
there are already seven physical circle-touching squares and the
universal bound is seven. Every vector \(c_j-p\) is nonzero by (2),
so the moving centers are unbounded as \(s\to\infty\). By continuity
there is a first finite \(s_*>1\) at which some moving square reaches
the containing circle; all moving squares remain in the disk up to and
including \(s_*\). All packing separations persist at this first
contact, including by continuity at the endpoint.

The original seven ring squares still touch the circle. At least one
additional square now touches it too. This contradicts the seven-body
circle-contact bound in `CYCLIC_GLOBAL_CONTINUATION.md`.

Therefore every exterior cell contains no completion square. Every
completion square has its open interior on the inner side of
\(\Gamma\), and its whole closed square in the closure of that
inner region. \(\square\)

## 4. Positive cycles localize further to the convex concurrence polygon

For a positive physical boundary cycle, let \(P\) be the convex
polygon \(q_0q_1\cdots q_6\) from `C7_FORCE_POLYGON.md`.
Its edge \([q_i,q_{i+1}]\) passes through \(p_i\), with the two
edge pieces contained in \(S_i\) and \(S_{i+1}\), respectively.
Choose these stress application points as the contact points in (3).
Moving each \(q_i\) linearly to \(C_i\) inside \(S_i\), keeping
all \(p_i\) fixed, gives a homotopy from the polygon boundary to
\(\Gamma\) entirely within the union of the ring squares.

The open interior of a completion square is disjoint even from the
closed ring squares: an open neighborhood of a point of a ring square
always meets that square's interior. Thus, for every point \(x\) in
the completion square's open interior, this homotopy avoids \(x\).
By Section 3, \(\Gamma\) has winding number one about \(x\).
So the boundary of \(P\) also has winding number one about \(x\).
Since \(P\) is a simple convex polygon, \(x\) lies in its open
interior. Taking closures proves

\[
                       \boxed{T\subseteq P}.
\]

This holds for every completion square, with arbitrary independent frame.
The remaining C7 completion problem is therefore precisely whether two
interior-disjoint unit squares can lie in this convex polygon while
avoiding the seven actual boundary squares. That capacity theorem is
still open here; neither polygon area nor regularity is assumed.

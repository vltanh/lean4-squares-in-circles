# Independent review: distinct all-both-vertex unloaded triangle

Reviewed November 1, 2026. The reviewer did not contribute to the theorem under
review. Source:
[`../../DISTINCT_ALL_VERTEX_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md`](../../DISTINCT_ALL_VERTEX_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md).

**Verdict:** the stated theorem is valid as a hand argument on its exact
original physical domain. It proves \(R>9/4\), uniformly over all positive
original internal weights, all permitted strict original internal normals,
all original exit means, and all repeated outside-terminal identities. No
gap was found in the finite geometry classification, torque restriction, or
force-weighted support argument.

This review covers the no-common-physical-point, all-three-original-pair-
applications-are-vertices-of-both-squares theorem. It does not independently
review the separately linked common-junction theorem or declare the full
direct-triangle family closed.

## 1. Geometric classification

If any two original pair applications coincide, that point belongs to all
three actual core squares. Thus the no-common-point premise really does force
three distinct applications; there is no omitted repeated-point branch.

Each core square contains its two applications as vertices, so every side of
the application triangle has length either \(1\) or \(\sqrt2\). The strict
triangle inequality follows from \(\sqrt2<2\), hence collinearity is excluded
without a genericity assumption.

If two sides are diagonals, at their common endpoint each corresponding
square has an open tangent quadrant of angle \(\pi/2\), centered on the
direction of its diagonal. The angle between those diagonals is at most
\(\pi/3\), by the cosine rule and the third-side upper bound \(\sqrt2\).
Their open quadrants overlap, so sufficiently short rays in that overlap
lie in both square interiors. This excludes both the two-diagonal and the
three-diagonal possibilities.

If exactly one side is a diagonal, the two other lengths are \(1\), so the
third application is one of the other two vertices of the square with that
diagonal. It is already in the other two squares, giving a forbidden actual
common point. This conclusion does not depend on which side of the diagonal
contains the third application.

With no diagonal, the application triangle is equilateral of side one.
Every core square is erected on one of its sides. An inward choice contains
the third application strictly in its interior: the base coordinate is
\(1/2\) and the altitude is \(\sqrt3/2\in(0,1)\). Since that point belongs to
another actual square, nearby interior points of that square overlap the
first. Thus all three squares must be outward. At each resulting pair
contact the actual intersections are singleton vertices, so invoking the
original strict singleton-normal convention is legitimate. No original
shared-side mean is silently changed to obtain this configuration.

## 2. Full torque restriction

In the stated square chart, the original internal force vectors are
\((r,-a)\) at \((1/2,0)\) and \((-s,-b)\) at \((-1/2,0)\), with all four
components strictly positive in magnitude. These signs follow from strict
exposure of the two bottom vertices, not from a symmetry assumption on weights.

Complete unloaded translation gives the sole exit \(E=(T_0,V)=(s-r,a+b)\).
Its original application maximizes \(E\) on the square. For \(T_0>0\), the
actual point is \((1/2,1)\) and the complete moment equation gives \(T_0=b\).
For \(T_0<0\), the actual point is \((-1/2,1)\) and the same equation gives
\(T_0=-a\). In both cases \(|T_0|<a+b=V\). If \(T_0=0\), the original
top-side mean is retained, and its horizontal coordinate cancels from the
subsequent support estimate. Therefore the exit direction is strictly within
\(\pi/4\) of the outward vertical. The proof uses each body's full original
force and torque lists, with no unretained positive cut.

## 3. Actual outside points and common-center averaging

The unit-step assertion is valid for an arbitrary outside frame. At a minimum
support point in unit direction \(e\), each nonzero component of \(e\) in the
neighbor's orthonormal square coordinates starts at the corresponding
minimizing endpoint. Adding that component moves inward by at most one.
A zero component leaves the original segment coordinate unchanged. Hence
\(w=q+e\) is an actual point of the unchanged outside square even for an
endpoint or interior original support mean.

About the common equilateral centroid \(H\), the source correctly obtains

\[
 e\cdot(w-H)=1+\left(1+\frac{\sqrt3}{6}\right)\cos t
                  +\frac12\sin t,\qquad 0\le t\le\frac\pi4.
\]

The last two terms form a positive strictly concave function on this closed
interval, so their minimum occurs at an endpoint. The two exact endpoint
comparisons with \(5/4\) are valid; the second reduces to
\(\sqrt3>19/12\). Thus all three original exits produce points satisfying
\(e_i\cdot(w_i-H)>9/4\).

Finally \(\sum_i z_i e_i=0\) is exactly the sum of the three original unloaded
translations. Multiplying each disk support inequality by its original
positive exit magnitude cancels the same translation \(H-O\). This yields
\(R\sum_i z_i>(9/4)\sum_i z_i\), and hence \(R>9/4\). The argument permits
the \(w_i\) to lie in the same actual outside square and never assumes distinct
terminals, balanced exterior degrees, or altered exterior reactions.

## 4. Adoption boundary

This justifies marking the complete stated geometric feature as independently
reviewed. A no-common-point direct triangle still requires treatment when
at least one original pair application is not a vertex of both squares.
Original coarse/fine/exterior counts cannot change from this feature review
alone without a theorem joining the full original caller domain.

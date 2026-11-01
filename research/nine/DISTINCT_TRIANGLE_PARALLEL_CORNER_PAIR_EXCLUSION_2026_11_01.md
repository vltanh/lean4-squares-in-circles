# Distinct-contact unloaded triangle: every parallel-frame corner pair forces R squared greater than nine halves

November 1, 2026. PR #11 continuation. **Evidence at construction: H; independent review requested.**

## 1. Exact scope

Keep the same original physical force-and-torque certificate on three actual selected-circle-unloaded unit squares A,B,C forming a positive direct triangle, each with full original positive degree three and one original positive outside exit. Keep the other six actual squares, all original applications, normals, means, loads and zero coefficients. The outside terminals may repeat and have arbitrary frames and degrees.

Suppose the actual core squares have no common point and at least two of their frames are parallel modulo quarter turns. This manuscript treats the complete feature where the chosen parallel pair intersects only at a point. The separate positive-length shared-side feature has its exhaustive classification in [DISTINCT_SHARED_SIDE_TRIANGLE_COMPLETE_NOTCH_CHART_AND_TORQUE_EXCLUSION_2026_11_01.md](DISTINCT_SHARED_SIDE_TRIANGLE_COMPLETE_NOTCH_CHART_AND_TORQUE_EXCLUSION_2026_11_01.md).

Then the original disk must satisfy

    R^2 > 9/2 > 1105/256.

Only the chosen two core frames are parallel. The third core and every outside square may have different frames.

## 2. Exact physical corner-notch chart

Two parallel unit squares with disjoint interiors and a point-only intersection meet diagonally at one corner. Normalize the actual parallel pair as

    A=[0,1] x [0,1],
    B=[-1,0] x [-1,0],
    A intersect B={P},        P=(0,0).

C cannot have the same frame: three pairwise-intersecting axis-aligned rectangles have a common point by the interval intersection property in each coordinate. Therefore C is nonparallel, and both its intersections with A and B are singletons. Denote them by p and q.

The segment [p,q] lies in C and cannot pass through P. It must cross the two coordinate axes through either the Southeast or Northwest notch between A and B. Reflect across the diagonal if needed to take the Southeast notch. The nonoverlap condition then forces

    p=(x,0),        0<x<=1,
    q=(0,-y),       0<y<=1.                       (1)

For example, as the segment travels from p toward q it moves in both negative coordinate directions. If p had positive height and positive horizontal coordinate, its initial segment would enter A's open interior; if p lay on the positive vertical axis, the segment would be in the Northwest notch instead. Thus p lies on A's bottom side. The reflected argument at q forces B's right side. The excluded zero coordinates would be the common point P.

Because C is nonparallel, choose unit directions

    u=(c,h),       v=(h,-c),
    c,h>0,         c^2+h^2=1,

and let L be its leftmost vertex, so

    C=L+[0,1]u+[0,1]v.

The rising upper-left edge of C is L+[0,1]u.

Every actual support at p or q must lie on that edge. If p is in A's bottom-side interior, the direction from A to C is South, and its minimizing support on C is the uppermost vertex L+u. If p=(1,0), its original strict normal from A toward C is Southeast. For any such vector n=(alpha,-beta), alpha,beta>0, one has n dot v=alpha h+beta c>0, so every minimizing support lies on the displayed edge. The same reasoning at q uses East for B's right-side interior and Southeast for the bottom-right corner (0,-1).

Thus both p and q are on one actual unit edge whose horizontal and vertical extents are c<1 and h<1. In (1) neither x nor y can equal 1. Both contacts are consequently strict side-interior contacts on A and B, and their forced C vertices are

    q=L=(0,-h),
    p=L+u=(c,0),       c,h>0, c^2+h^2=1.          (2)

This proves the entire physical chart. In particular it excludes unaccounted alternatives in which an outer A/B corner is placed in a side of C. All angular endpoints would have C parallel, already incompatible with the no-common-point premise.

## 3. Original translations force two opposite outside support corners

Let the original AB magnitude be t>0. By the retained strict singleton convention, the original A-to-B normal at the diagonal corner P is

    (-r,-k),       r,k>0,      r^2+k^2=1.

No normal is reselected. From (2), the original A-to-C normal is South and the original B-to-C normal is East. Let their positive original magnitudes be a,b.

The complete A translation forces its sole outside vector to be

    E_A=(tr,tk+a),

with both components strictly positive. Hence its unchanged original application is the actual corner (1,1). The complete B translation forces its sole outside vector to be

    E_B=(-tr-b,-tk),

with both components strictly negative. Hence its unchanged original application is (-1,-1).

All original moment equations remain retained; the contradiction does not need to weaken or replace them. Write the outside unit normals as

    e_A=(alpha,beta),
    e_B=(-gamma,-delta),

where all four components are positive and alpha^2+beta^2=gamma^2+delta^2=1.

## 4. Actual outside points have squared separation greater than 18

At each original outside contact q, the point q minimizes the outward normal e on the actual outside neighbor. The unit-square support fact therefore puts q+e in that very neighbor: in its own side coordinates, adding each component of e moves inward by at most one. This holds for every outside support owner and original mean.

Consequently the unchanged original disk contains the two actual points

    w_A=(1+alpha,1+beta),
    w_B=(-1-gamma,-1-delta).

Their squared separation is

    |w_A-w_B|^2
      =8+4(alpha+beta+gamma+delta)
          +(alpha+gamma)^2+(beta+delta)^2
      >8+8+2=18.

The strict inequality follows from alpha+beta>1, gamma+delta>1 and

    (alpha+gamma)^2+(beta+delta)^2
      =2+2(alpha gamma+beta delta)>2.

The original disk diameter now gives 4R^2>=|w_A-w_B|^2>18. Thus R^2>9/2, proving the theorem. No distinctness of the actual outside terminals is needed.

## 5. Coverage and remaining boundary

The proof covers the entire no-common-point direct-triangle feature with a parallel-frame pair meeting at a singleton corner. Combined with a completed shared-side family exclusion and the complete common-junction exclusion, it removes every direct triangle having any parallel pair of core frames.

The other original positive edges, the third original full star, all six remaining actual squares and the full original circle data remain present. The theorem is a geometric feature exclusion, not an automatic closure of any original coarse parent. All-pairwise-nonparallel singleton contact systems remain to be analyzed.

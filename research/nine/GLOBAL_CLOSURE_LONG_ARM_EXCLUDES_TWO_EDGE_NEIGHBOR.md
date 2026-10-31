# A long pendant arm excludes a two-edge arm at any touching root

Date: October 26, 2026.

**Status: accepted complete theorem after full-source root review in REVIEW_LONG_ARM_GEOMETRY_AND_TWO_EDGE_ROOT_2026_10_26.md and separate review in REVIEW_LONG_ARM_TWO_EDGE_NEIGHBOR_ROOTED_BLOCKS_2026_10_26.md.** No original gate is changed here.

## 1. Original geometric and force scope

Keep all nine physical unit squares in the original circle, with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, r=R-sqrt(2).

Suppose the distinct physical roots A,B touch. A has a genuine pendant
path A--U--V--L of three positive bridges; B has a genuine pendant path
B--T--M of two positive bridges. The two path body sets are disjoint.
U,V,T are genuinely unloaded of exact positive degree two, and L,M are
genuine radial S/D leaves. Retain all other forces and physical squares,
including any circle force at A. There is no force or degree assumption
on either root beyond the displayed actual branches and physical AB
contact. In particular, the argument applies when A,B are distinct
vertices of a sole positive triangle with arbitrary additional branches
at its third root.

The theorem is that this entire physical layout is impossible.

Use `ROOTED_TRIANGLE_LENGTH_THREE_ARM_GEOMETRY.md`, independently reviewed
in `REVIEW_LENGTH_THREE_ARM_GEOMETRY_GLOBAL_2026_10_26.md`. Its complete
original-width and critical-P cases give

    d=1+epsilon,  0<epsilon<1/60,  rho=1-epsilon=2-d,
    L=S(e),
    A subset {e dot x<=-rho},
    U=[-rho,epsilon] times an actual length-one transverse interval
      containing zero.                                      (1)

In particular U contains O. The source also proves the stronger full
aligned chart for A, but only its supporting half-plane is needed here.
Rotate e to the positive horizontal direction.

## 2. A negative two-edge root application forces an interior-origin body

Let v be M's actual radial direction. The unchanged degree-two equation
at T makes it a normal transmitter of width w in {1,sqrt(2)}. Its
applications are r_M v at M and (r_M-w)v at B, where r_M is r for D
and d for S. Every original side mean and endpoint is retained.

If M is D, its parent T has the D inner vertex r v in a relative side
interior. Indeed an off-origin vertex/vertex physical point contact
cannot have the selected radial normal; this is the unchanged strict
point-normal convention from the radial leaf reduction. Thus T is
side-aligned to v, with longitudinal interval [r-1,r] and a transverse
interval containing zero strictly. Since 0<r<1, O belongs to the open
interior of T. This includes the entire D/side case; the D/diagonal
vertex/vertex alternative is already excluded by the same convention.

If M is S and w=sqrt(2), the two actual applications are the opposite
vertices (d-sqrt(2))v and d v of T. Because 0<d<sqrt(2), O lies strictly
between them on T's diagonal, and therefore in its open interior.

Either alternative contradicts physical disjointness with U, which
contains O. A square containing O has interior points arbitrarily near
O, while a square with O in its open interior contains a neighborhood
of O. Thus they would have overlapping interiors. This argument keeps
the whole original T and does not delete its branch forces.

The only remaining two-edge branch is therefore S/side, with

    M=S(v),  w=1,  p_BT=epsilon v,
    B subset {v dot x<=epsilon},  epsilon v in B.           (2)

## 3. Its root B must share the origin side line of U

For any unit square with radial outward support p=epsilon v and
0<epsilon<1, the entire inward segment [p-v,p] lies in that square.
This follows directly in its own coordinates: at a side support it is
the perpendicular unit segment, and at a vertex support the inward
coordinates of v are nonnegative and at most one. Hence O belongs to B.

Moreover, O cannot be a vertex of B. If a unit square has O as a vertex,
write it as [0,1]u+[0,1]w for orthonormal inward axes. Any nonzero
positive radial outward support p=t n satisfies |p|>=1: on a non-origin
vertex this is immediate; a relative side-interior radial outward
support must lie on one of the two opposite sides, giving an own
coordinate equal to one. The two sides through O have outward axes
pointing outside this quadrant and cannot contain a point t n for t>0.
Thus the small positive radius epsilon<1 in (2) excludes an origin
vertex. This covers side-axis endpoints as well.

Since U and B are distinct physical squares containing O, neither can
contain it in its open interior. Consequently O is in a relative side
interior of each. In U the longitudinal interval [-rho,epsilon] contains
zero strictly, so the side through O is horizontal. Their two tangent
half-planes must be opposite; otherwise their open interiors overlap
arbitrarily close to O. Thus B is also side-aligned to the horizontal
axis and has a horizontal side through O.

Reflect vertically if necessary to put B below that side. It then has
the exact form

    B=[a,a+1] times [-1,0],  with a<0<a+1.                 (3)

The reflected upper-half-plane case has identical conclusions.

## 4. Full radial feature cover of B and the final contradictions

At the actual application p=epsilon v, its norm is below one. Therefore
p cannot lie on the far horizontal side y=-1 of (3). A relative interior
of the origin side y=0 has outward normal (0,1); no point epsilon(0,1)
with epsilon>0 lies on that side. At an endpoint of the origin side,
p has y=0, so radiality itself makes v horizontal. At a relative
interior of a vertical side, its outward normal is horizontal as well.
These cases exhaust all actual side/vertex supports and their endpoints.
Consequently

    v=e or v=-e.                                         (4)

If v=e, the two genuine radial S leaves L and M are the same physical
square S(e), contrary to their distinct bodies and interior disjointness.

If v=-e, equation (2) is the left support of B at x=-epsilon. Thus every
point of B satisfies x>=-epsilon. Every point of A satisfies x<=-rho by
(1), and rho=1-epsilon>epsilon. The two roots are strictly separated
by the positive horizontal gap rho-epsilon=1-2epsilon>29/30. They cannot
physically touch, contrary to the original AB edge.

Both alternatives are impossible. This proves the whole theorem.

## 5. Exact application and limits

In a sole-triangle component after the already proved outside-fork and
multiple-path-at-one-root reductions, every nontrivial arm is an original
simple pendant path whose internal bodies are genuinely unloaded. The
theorem therefore excludes every remaining arrangement with a length-three
arm and a length-two arm at different triangle roots, including the full
distributions (3,2) and (3,2,1). It also applies before any restriction on
other root forces, provided the two displayed paths have the stated
genuine internal degrees and loads.

No common triangle moment, concurrence sign, boundary load at A, or
external-resultant noncollinearity was needed. A possible original root
circle force was never discarded. The remaining length-three/direct-leaf
distributions are separate obligations. This source alone makes no whole
coarse-cell, final radius or equality claim.

No numerical pose sampling, Lean compilation, CI or remote action is used.

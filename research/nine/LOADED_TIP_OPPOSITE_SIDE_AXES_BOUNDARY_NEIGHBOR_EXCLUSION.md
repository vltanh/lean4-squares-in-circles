# Opposite original tip axes cannot feed a physical-boundary neighbor

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free boundary theorem and all-mask loaded-tip corollary, submitted for independent review.** The radius interval is the entire closed range R^2>=13/4, with no upper bound. No U3, W2, T2, boundary-path order or completion-square allocation is needed.

The inward-support box used in earlier mask arguments is printed in full here at this broader radius and mean scope. Every physical circle corner, individual zero coefficient and original shared-side mean remains.

## 1. A whole radial inner side has no inward boundary neighbor

Let V and W be actual closed unit squares contained in the same unchanged disk D_R, where

    R^2>=13/4.                                      (1)

In an actual orthonormal circle-centered frame suppose

    V=[D,D+1] x [-1/2,1/2],
    D=sqrt(R^2-1/4)-1.                              (2)

Thus the two physical outer V corners are (D+1,+/-1/2).

Suppose W contains an actual point

    M=(D,t), -1/2<=t<=1/2,

and its whole actual square satisfies

    W subset {x<=D}.                                (3)

Then every point of W lies strictly inside D_R. In particular W cannot physically touch the containing circle.

### Complete support-point reach proof

M is an actual maximum-horizontal support point of W. In either tangent direction, the horizontal-support point of a unit square has vertical reach at most one.

At a unique support vertex, the two inward unit edge vectors have nonpositive horizontal components. Their vertical components have opposite signs or one is zero because the vectors are orthogonal. At most one edge therefore contributes to either vertical direction, and its component has magnitude at most one. Any point of the square is a combination of the two edges with coefficients in [0,1].

At a side-interior or side-endpoint support point, the support side has length one, while its perpendicular inward edge has zero vertical component. The same one-sided reach bound follows, including both actual endpoints and every point of that side.

The horizontal inward span of any unit square is at most sqrt(2). Consequently the entire actual W satisfies

    D-sqrt(2)<=x<=D,
    |y|<=3/2.                                       (4)

By (1),

    D>=sqrt(3)-1>5/7>1/sqrt(2).

The first strict rational comparison follows from
3-(12/7)^2=3/49>0, and the second from25/49-1/2=1/98>0.
Therefore D-sqrt(2)>-D, so |x|<=D in (4).

It follows that every actual point of W satisfies

    |z|^2<=D^2+9/4
             <D^2+2D+5/4
              =(D+1)^2+1/4=R^2.                   (5)

The strict reserve is2D-1>0. This proves the whole-square conclusion. It covers every W frame and every possible W physical mask simultaneously.

No force, circle coefficient, degree or normal selection is used in this geometric theorem.

## 2. Complete all-mask corollary for a genuine loaded tip

Keep actual interior-disjoint contained unit squares and their original physical stress in the same radius range(1). Suppose V is positively circle-loaded and its entire positive pair neighborhood is exactly U,W. The actual W physically touches the containing circle; U and W retain arbitrary true degrees, loads, other forces and contact means.

Let n be an own side axis of the actual V. Suppose the original directed normals are

    n_UV=n,
    n_VW=-n.                                        (6)

These are assumptions about the original selected normals. No normal is reselected.

Let mu,omega>0 be the original pair magnitudes. The full true V2 equation gives its complete outward circle resultant

    F_V=mu*n-omega*n_VW=(mu+omega)n.                 (7)

Choose an actual perpendicular axis k=Jn. If V's k-center coordinate were nonzero, every physical farthest corner would have a nonzero k-component of the same sign. Any nonnegative combination with positive total circle load would have a k-component of that sign, contradicting F_V.k=0.

Thus its k-center coordinate is exactly zero. If its n-center coordinate were also zero, its squared containing-circle radius would be1/2, contrary to(1). If that coordinate were negative, every physical farthest corner would have negative n-component, contrary to F_V.n>0. Therefore the n-center coordinate is positive.

The entire physical V mask is consequently exactly the two actual outer corners in(2). Both are retained. Equation(7) constrains their complete weighted sum; it does not remove a corner whose individual coefficient may initially have been zero. No unique-circle formula is applied to this physical-two mask.

The original normal n_VW=-n puts all W in the inward half-plane n.z<=D. Its unchanged original application or full side mean M belongs to both actual units and lies on the whole actual V minimum-n side. It therefore has precisely the form required in(3), with t in the full closed interval[-1/2,1/2].

The force-free theorem now puts the entire actual W strictly inside the circle, contradicting its physical boundary contact.

**Corollary.** A genuine positively loaded V2 with physical-boundary neighbor W cannot have the two original directed own-axis normals(6), anywhere in R^2>=13/4.

The conclusion includes actual singleton, side-interior and positive shared VW features and every full original mean endpoint. It requires no original application distinctness, no fixed-tip selector, no equation at W, and no condition on a third unit T.

## 3. Literal sole-UT use and broader caller boundary

In the current original D02 singleton sole-UT interface, the unchanged UV normal n is V-side-owned at a strict U vertex. If its original V-owned VW normal is -n, the genuine loaded V2 and physical-boundary W satisfy every hypothesis of Section2. The original same-nine radius R>2 is stronger than(1), so that whole return category is excluded.

The true original U3,V2,W3,T2, full rim and chord02, positive load set{0,1,3,4,5}, all original means and all nine actual units remain. The local contradiction does not use a smaller component or a completion allocation.

The other V-owned axis -Jn is outside(6). The common-W-side, different-W-side and free-return categories retain their own complete proof obligations. This source by itself grants no original D02 row or coarse-parent credit.

The force-free theorem also applies directly to any actual radial unit and any whole inward neighbor satisfying(2)--(3), regardless of a graph or stress. A caller must establish those exact physical placements rather than infer them merely from a resultant direction.

## 4. Exact operative inputs

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete true V2 equation, original directed support conventions, full actual means and all physical circle coefficients |
| D02_ENTIRE_INCOMING_HUB_AXIS_AND_SHARED_TERMINAL_EXCLUSION.md | 0b0e8b90ff7535e6e80f429e10ff7535190c2a74220022d1a9ad3676a8595c7f | Literal current original singleton sole-UT entry only |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original graph, load mask, true degrees and all three extras in the optional original caller |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Original R>2 only on the same retained nine units; the local theorem independently assumes(1) |

Every new geometric and physical-mask step is printed above. Independent full-source review is required before adoption. No pose sample, numerical exclusion certificate, changed original normal, shortened shared mean, omitted force, fake W2, Lean compilation, CI, workflow, remote write or ledger mutation is used.


# Root full-source review: one-root triangle forests and off-origin bridges

Date: October 26, 2026.

## 1. Every bridge forest attached at one triangle root

**Verdict: accept the full selected-certificate theorem in
GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md.** Its separate
full-source review is
REVIEW_ONE_ROOT_TRIANGLE_FORESTS_ROOTED_BLOCKS_2026_10_26.md.

I checked the original full graph, the additional support selection, every
fork and path case, and the critical-radius root equation. The theorem
concerns a compatible stress chosen with minimum positive scalar support
on the unchanged common radius/Phi-minimizer pose. It is not a conclusion
about every earlier stress representation.

The exact articulation source proves the complete branch reweighting
equations. Its positive private branch masses and zero individual branch
moments justify the extra collinearity refinement: three collinear branch
resultants at an unloaded articulation span at most two dimensions after
adjoining their scalar masses, so a nonnegative reweighting removes a
positive atom. The named at-most-five-body exclusions apply at the same
canonical pose after an exact loaded-body split. Thus every outside
nonleaf is unloaded, its degree is at most three, and the triangle root
has at most two bridge branches. These claims do not discard old forces
without constructing the new complete stress first.

The two untouched triangle tips keep genuine positive degree two and are
loaded. Their intact end-triangle equations give the nonzero resultant,
strict positive pressure and strict support bound used throughout. The
root is circle-clear, but its other branch forces are retained. The
all-bridge central localization is local: it needs the body's genuine
zero load and its incident bridge edges, not a tree premise for the whole
component. The bound on a farthest fork's terminal-arm length follows
before any two-arm classification is used.

I checked the four exhaustive terminal-arm pairs against their source
hypotheses. The direct/direct, D/direct-with-channel, S/direct-with-channel,
and channel/channel cases use only the force-free portions at the root.
The inequalities on the three other side distances in the S case are
strict on 0<epsilon<1/60. At positive epsilon each resulting rectangle
contains the open disk D_epsilon. At d<1 the applicable cases contain the
origin in their interior. The d=1 tangent cases retain weak containment
and are handled separately; no continuity argument supplies their forces.

Away from d=1, a farthest fork puts the triangle root outside the central
disk. Every incoming root bridge then uses its unique nearest point. An
outgoing root bridge has support greater than one and can lead only to
a genuine S leaf. If that leaf exists, its inward unit segment forces
the nearest point to be epsilon times its direction. The other incoming
branch is collinear, contradicting the proved minimum-support property.
Without an outgoing leaf there can be only one bridge at the triangle
root, and its actual nearest radius meets the complete outer-triangle
theorem's threshold. The source keeps that theorem's exact root degree.

At d=1, the argument proving that outside nonleaves and then the triangle
root contain the origin uses their actual available neighbors. A body
avoiding zero would need an outward support above one. No outside
unloaded body or genuine S/D leaf can be its outer neighbor, and the
remaining possibility of the triangle root gives the same complete
collinearity or outer-triangle contradiction. Separators between actual
origin-containing bodies pass through zero; bridge radiality then makes
the actual application zero, irrespective of a shared-side mean.

The critical root with only origin forces violates the strict triangle
support bound in its inward normal cone. With one direct S leaf, the
displayed full equation M=-alpha*u-beta*n is the actual original root
equation. I checked every remaining root feature: the excluded axis
normals, the origin, the screened leaf midpoint, the far vertex, the
remaining v vertex and the +v side. The proper concurrence has negative
v coordinate, while the remaining two vertex applications would concur
at v. The support-equality side case forces the original radial S(v),
and its midpoint screen excludes the other boundary tip. The parallel
case is separately covered by the genuine tip-force nonparallel lemma
and the duplicate radial-square exclusion. No arbitrary branch is
replaced by a fictitious leaf or transmitter.

Finally, with no outside fork the graph has at most two genuine paths.
The original center bound excludes length at least four. A length-three
path gives a unique nearest radius greater than59/60; the other path's
direct-leaf, negative-application and epsilon-application alternatives
are all excluded without changing their means. The remaining lengths
1 and2 are exactly the cited complete attachment families, including
the newly reviewed two-channel attachment. This is an exhaustive graph
join, not a collection of representative poses.

The theorem does not cover forests attached at distinct triangle roots,
other cyclic blocks or chorded triangle blocks. In particular it does
not by itself close C1.3.b4, C1.3.b5 or C1.3.b6. No original label is
added or ticked by this review.

## 2. Uniform off-origin unloaded all-bridge bodies

**Verdict: accept the full local theorem in
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md.** Its separate complete
independent review passed in
REVIEW_OFF_ORIGIN_BRIDGE_TRANSMITTERS_ROOTED_BLOCKS_2026_10_26.md.

The component is allowed to have arbitrary cyclic neighbors. I checked
the all-bridge localization and both directions of the force argument.
If U avoids zero, each incoming bridge uses its unique nearest point,
whereas every outgoing radial direction has strictly positive dot
product with that nearest-point direction. Its zero-load balance thus
requires both kinds of edge. An outgoing radial support of an
origin-avoiding square has radius greater than one, and its contained
neighbor bounds that radius by d.

In own axes, two center coordinates outside [-1/2,1/2] would force every
outgoing support beyond sqrt(2), impossible. With only the first center
coordinate outside that interval, the incoming direction is horizontal.
Each nonzero outgoing height has absolute value below11/60. Opposite
sign heights would be the two actual vertical endpoints, separated by
one, contradicting that bound. Transverse equilibrium then excludes the
only possible nonzero sign. All outgoing applications are therefore the
same horizontal side foot and differ from the incoming foot by exactly
one. This also retains side endpoints b=+/-1/2 and every original mean.

Every outward neighbor has center x>3/2 and norm<91/60. The complete
rectangular cap has squared diameter bound

    (91/60-3/2)^2 + 4((91/60)^2-9/4) = 29/144 < 1.

Thus two such neighbors would violate the unit incircle separation. The
inward unit segment at each incoming neighbor's radial support contains
zero because 0<rho<=d-1<1/60. No load or leaf geometry is imposed on the
outer neighbor. Finally the complete articulation scaling argument
removes a third collinear branch only under the explicitly stated
minimum-support selection, leaving exactly one incoming neighbor.

The consequence at R^2<=17/4 requires no support-minimization premise:
an origin-avoiding unloaded all-bridge body would need 1<t<=d<=1. At
higher radius, the side-transmitter conclusion and the prohibition on
adjacent off-origin unloaded all-bridge bodies retain their stated
selected-certificate scope. This is a local result, not a closure of
an entire coarse cyclic cell.

No compilation, CI, numerical search or new coefficient certificate was
used in either review. The older full prerequisite-chain audit remains
separate.

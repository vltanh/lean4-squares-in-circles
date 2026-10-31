# Full independent review: intact root bridging to a genuine leaf root

Date: October 26, 2026.

Reviewer: rooted-blocks agent, independently of the author and root review.

**Verdict: ACCEPT the complete local theorem and the complete stated
all-triangle block-tree exclusion. No correction is required.**

Reviewed source:
`GLOBAL_CLOSURE_INTACT_ROOT_BRIDGE_TO_LEAF_ROOT_EXCLUSION.md`.
SHA-256 of the complete source read:

    9de9c732b4b8f5214c2f71ef391840b979b75e668bca14955c422640eb25fd0f

This review checks the original positive bridge HA, the genuine leaf L
at its actual root A, and the full remaining graph. In particular it
does not treat A as a degree-two transmitter or delete any of A's
possible cyclic or bridge forces.

## 1. Inputs and their actual scopes

I read the complete source and reread the full relevant accepted sources
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`,
`ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md`, and
`GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md`.
I also read the shorter companion
`GLOBAL_CLOSURE_INTACT_ROOT_TWO_EDGE_ARM_BLOCK_TREE_EXCLUSION.md` to
check that the new theorem genuinely removes its degree-two premise at
the outer root rather than silently importing that premise.

The intact-petal theorem applies to the two actual degree-two loaded
tips and leaves all other H forces present. It gives O in int H, a
genuine common own side of height P<39/40, and strict transverse port
straddling. One port has transverse magnitude at most 1/2, so the
boundary-unit distance floor gives

    P^2 > 889/14400 > 1/25.

The last strict reserve is 313/14400. Hence 1/5<P<39/40, and every
actual vertex of H has norm greater than 1/40 because its longitudinal
coordinate is P or P-1. This is a vertex bound, not a claim that H
contains the disk of radius 1/40.

Every genuine leaf is loaded by its true degree-one force equation.
The radial bridge and S/D leaf forms therefore apply without any
degree restriction at its parent. A D leaf puts O in its parent, and
an S leaf with d<=1 also puts O in its parent. Since O lies openly in
H, any distinct parent containing O even on its boundary is impossible.
This justifies the reduction to a genuine S leaf with d=1+epsilon>1
and the actual point epsilon v in A.

## 2. The genuine HA bridge and its complete nearest-point geometry

The bridge law is a cut-moment identity for the full original graph;
it does not need a local degree-two equation. Since O is in int H,
the actual H-to-A support is p=rho e with rho>0. The unchanged point
epsilon v in A then gives

    0<rho<=epsilon(e.v)<=epsilon.

The strict vertex margin makes p a relative interior point of an H
side. Thus e is an actual own side axis. Its opposite height is 1-rho.
Neither of these faces can be the intact petal's actual common face:
their heights are respectively below 1/5 and above 39/40. The petal
face is perpendicular, with the other two side heights P and 1-P.
Both exceed epsilon. These three strict margins prove exactly the
source's implication

    x in D_epsilon and x not in int H  =>  e.x>=rho,

including every disk boundary point and equality on the e side.

The support inequalities show that p is A's unique nearest point to
O. The S-root classification in Section 2 is exhaustive:

- If the leaf direction is an A side axis, A has its full slider
  form [epsilon,d]v+[l,l+1]Jv with -1<=l<=0. Its nearest point is
  epsilon v, even at either slider endpoint. Therefore rho=epsilon,
  v=e, and A owns the same axis.
- Otherwise d v is a strict supporting vertex. In its outward own
  axes A has intervals [d a-1,d a] and [d b-1,d b], where a,b>0 and
  a^2+b^2=1. Since A avoids O, at least one lower endpoint is strictly
  positive. Both cannot be nonnegative with one positive, since that
  would force d^2>2, whereas d^2<(61/60)^2<2. Consequently exactly
  one lower endpoint is positive and the other interval contains
  zero strictly. The nearest point lies in the corresponding side
  interior, so uniqueness identifies that axis with e.

After a transverse reflection the strict-vertex case is therefore

    A=[rho,rho+1] x [u_0-1,u_0],
    (rho+1)^2+u_0^2=d^2,
    0<rho<epsilon,  0<u_0<1/5.

The arithmetic u_0^2<121/3600<1/25 has reserve 23/3600. No load or
other force equation at A is used in this classification. The axial
slider and the nonaxial orientation endpoints are all retained.

## 3. Whole small-disk exclusion for every other leaf parent

In the strict-vertex alternative the exact radius identity gives

    rho^2+u_0^2=epsilon^2+2(epsilon-rho)>epsilon^2.

For a disk point outside int H, x_1>=rho. Its other A inequalities
are strict: x_1<rho+1 and x_2>u_0-1, while x_2>=u_0 would violate
the displayed norm identity. If x_1>rho it is in int A. If x_1=rho
it belongs to the relative interiors of both actual shared sides.
The two units then cover a full neighborhood on the opposite sides
of their common support line.

The conclusion about a third square is valid even when it contains
the point only on a vertex or an edge. Every neighborhood of a point
of a full-dimensional square contains points of that square's open
interior. In the shared-side case these cannot all remain on one
line, and in the interior case there is an immediate open overlap.
Thus a distinct square disjoint in open interiors from both H and A
cannot meet D_epsilon at all.

In the axial alternative the three other H margins are strict and
its remaining height equals epsilon. Hence all of D_epsilon except
the single point epsilon e is in int H. A third genuine S-leaf root
would have to contain epsilon e and use the same direction e. The
radial S formula then identifies its actual leaf with exactly the
already present unit L, including its position and orientation.
Distinct physical bodies cannot occupy that
same open square; the true degree-one body L already has its unique
positive neighbor A. It cannot acquire another root.

These arguments prove the full local statement that every genuine
leaf root in the component is H or A. They do not only exclude leaves
in one selected branch. They also show why epsilon=0 is absent: it
was excluded by the original leaf and origin-interior geometry before
the small-disk argument.

## 4. Complete block-cut-tree join with arbitrary outer degree

I checked the graph argument with A allowed to be cyclic and to have
arbitrary additional branches at the outset.

Root the full block-cut tree at H. Each terminal triangle has two
private vertices with their true positive degree two. An unloaded
one would transmit a positive-width channel between the other two
physically touching vertices, so both private tips are genuinely
loaded. Its intact-root origin theorem makes its root H. Each
terminal bridge has a genuine leaf endpoint, whose parent is H or A
by the already proved whole-component local statement.

Suppose a triangle block lies away from H. A terminal descendant is
either a triangle or a bridge. The triangle would have its root away
from H, impossible. The bridge cannot have parent H because that
would return to the ancestral root in a tree. Nor can it have parent
A: its unique tree route from H to A would then pass through the
chosen triangle, whereas the original HA bridge already provides
that complete route. This uses the actual bridge HA and does not
identify or move A.

Thus every triangle meets H directly. The same descendant argument
excludes any extra block at a private tip; it cannot lead to A because
HA is a distinct bridge. The private tips therefore really do have
degree two in the unchanged graph. All triangles are intact petals
at H, with no attachment removed to make them intact.

There are at least two such petals and the original radial bridge HA
still has norm rho<=epsilon. Section 3 of the accepted common-root
source excludes exactly that local combination, for arbitrary other
forces at H. Its use requires neither stress-support minimization nor
the final pressure sum from that source's separate forest assembly.

This proves the stated entire all-triangle block-tree family and all
declared direct-connector applications. A far endpoint without a
genuine leaf, a root having only its own direct S leaf, a graph with
no intact petal, and a nontriangle cyclic block remain outside scope.
No whole coarse cell is silently marked closed.

## 5. Verification boundary

The review preserves the physical pose, all original positive forces,
every actual mean and selected normal, all zero-weight contacts, and
the full original component and nine-body completion. It contains no
numerical search as proof, no changed normal selection, no fictitious
degree-two root, and no deletion of A's possible original circle
force or other branches. No Lean, CI, remote action, or shared-ledger
change was performed.

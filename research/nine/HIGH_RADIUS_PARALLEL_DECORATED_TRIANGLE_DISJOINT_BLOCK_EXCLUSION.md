# A parallel decorated triangle excludes every disjoint cyclic block in the parallel-hub frame

Date: October 28, 2026. Author: two_blocks.

**Status: complete proposed uniform implication, submitted for full root
and separate independent review. No coarse or fine closure is claimed.**

Keep all nine actual interior-disjoint unit squares, their original
circle and compatible selected positive certificate, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Every positive force, true degree, selected normal, actual application,
shared-side mean, physical circle mask, individual zero weight,
zero-stress contact and completion square remains unchanged.

## 1. A disk-avoiding block is incompatible with exterior boundary access from a closed-origin unit

Let Q be a maximal cyclic block of the original positive graph. Suppose
every actual unit of Q avoids the closed disk D_epsilon. Suppose an
actual unit E outside Q contains O closed, and E has an original
positive path to a physical boundary unit T such that every vertex of
the path lies outside Q. Then these data are impossible.

This is a precise boundary-path extension of Section 2 of
`C2_35_TWO_BRIDGES_AND_C2_36_ONE_BRIDGE_ORIGINAL_ATTACHMENT_REDUCTION.md`.
Its full radial-edge, cut-moment and port-order proofs have exactly the
same premises here. We spell out the extension and the needed geometry.

First, every actual Q edge has nonzero origin moment. If a contact were
radial, write its nonzero application as p=t e, with t>0 and n=e at
its inner unit U. The contained-neighbor support bound gives t<=d.
In an actual own interval of U missing zero, reflected as [a,a+1]
with a>0, the component of e=p/t is positive. Because p is the
maximum-e support, that component of p equals a+1. Hence t>1
and a<=t-1<=epsilon. If both own intervals missed zero, t>sqrt(2)>d.
If just one did, (a,0) would be an actual point of U in D_epsilon.
Both alternatives contradict the stated avoidance. The case p=O
already contradicts it. This keeps every actual radial side mean.

Each connected component outside maximal Q attaches to Q at at most
one vertex. Its complete origin-torque sum shows that its total
external moment at that vertex is zero; internal pair moments cancel
at their unchanged common points, and every circle atom has zero
origin moment. Thus Q's original nonzero edge moments form a
circulation at all its vertices. Orient each edge in its positive
moment direction. A finite positive circulation contains a directed
simple cycle C.

Sections 1--3 of
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`
apply to C. All its actual units and its two cycle neighbors avoid
D_epsilon, and its incoming and outgoing original moments have the
required opposite signs at each body. The actual cycle winds positively
about O. In one sufficiently close compatible physical embedding it
is a simple Jordan cycle with that winding. No degree-two equation
was assigned to any vertex, and no additional positive force was dropped.

The segment from O to the real center c_E is disjoint from the closed
cycle units. Every nonzero point of that segment is interior to E;
O itself is excluded from the cycle units. Compactness gives positive
clearance, also when O is on the boundary of E. Consequently c_E is
inside the same Jordan cycle. The actual positive path from E to T
has no cycle vertex and cannot cross C in this compatible embedding.
It therefore puts T inside C as well. This contradicts the protected
exterior-face access of every physical boundary vertex.

The path may have any length and T need not be a genuine leaf. A
direct original edge to a physical boundary body is sufficient. No
path is invented and no physical contact is independently rerouted.

## 2. The high-radius parallel A pair forces the actual hub to contain O

Now let H,A,B be an actual positive triangle. Require that A has
exactly its two triangle edges and one genuine radial S leaf L_A,
and B has true positive degree two, with neighbors A,H. H has
arbitrary true degree and all its original external forces. Suppose

    d=1+epsilon>1,
    A's two triangle force lines are parallel,
    the actual frames of A and H are parallel.

No origin premise at H is imposed. Each triangle body's complete
external origin moment is zero, as in the original block callers.

B is positively circle-loaded: an unloaded true degree-two body would
separate its two actually touching neighbors by a positive width.
The two parallel A normals have the same outward sign, because
opposed normals would likewise separate its touching neighbors.
A's full three-force equation makes both normals opposite its real
leaf direction e. If A were tilted relative to e, both applications
would be its unique opposite vertex. Its actual torque would make
that vertex radial, forcing equal components of e in its own frame.
That vertex then has norm sqrt(2)-d<R-sqrt(2), impossible for the
actual AB point in physical boundary B. This is the complete
parallel-root calculation in Section 1 of the pinned 9036 source.

Therefore A is aligned with its real leaf. Rotate e east. The exact
unchanged geometry and torque are

    A=[epsilon,d] x I, length(I)=1, 0 in I,
    P_AB=(epsilon,y), P_AH=(epsilon,z),
    mu*y+nu*z=0, mu,nu>0.

The true leaf application is (d,0); no other application is set to a
midpoint. The boundary-point bound and the full high-radius interval
give r=R-sqrt(2)>129/200. Since epsilon<1/60, the nonzero B mean
has |y|>16/25. Reflect the complete configuration vertically to take
y>0. The torque then gives z<0, and the original interval I gives

    y>16/25, 0<-z<9/25, y-z<=1.

All these inequalities include every original mean endpoint. The
exact comparison is

    (129/200)^2-(1/60)^2-(16/25)^2=2213/360000>0.

The actual B lies in x<=epsilon and touches that wall at P_AB.
Every point of B has y-coordinate greater than 1/2. Here is the
whole physical frame proof, without an H equation.

If B is aligned, its horizontal interval is [epsilon-1,epsilon].
Since it is a physical boundary square, its far vertical corner
has absolute height greater than sqrt(13)/2>3/2. Its actual
vertical interval contains 0<y<=1, so the far height is positive.
Its lower height is consequently greater than 1/2.

If B is oblique, P_AB is its unique rightmost vertex. Write its
inward unit axes as (-c,s),(-s,-c), with c,s>0 and c^2+s^2=1.
The squared norms of P_AB and its two adjacent corners are at
most 1+1/3600, 4+1/3600 and 2+1/3600 respectively, all below
R^2>17/4. Thus its only physical circle corner is the opposite
corner W. Its horizontal magnitude is at most sqrt(2), giving
|W_y|>3/2. But W_y=y+s-c>-1, so W_y>3/2. The actual lowest
height of B is W_y-s>1/2. This treats every physical circle mask
before any particular positive weight is used.

The actual H is parallel to A, lies across its west support and
contains P_AH. Hence

    H=[epsilon-1,epsilon] x [t,t+1].

Because H contains z<0 and physically touches B above height 1/2,

    -1/2<t<0, t+1>1/2.

Since 0<epsilon<1, both own coordinates of O are strictly between
H's endpoints. Thus **O belongs to int H**, derived from the actual
parallel interface. No assumption on H's additional forces or any
leaf at H was required.

## 3. The entire closed small disk is protected by the actual H and A

Every premise of the uniform theorem
`ROOTED_PARALLEL_DECORATED_TRIANGLE_THIRD_NEAR_UNIT_EXCLUSION.md`
is now established. Its Sections 2--5 use exactly the actual A3/B2,
the parallel A pair, the parallel H frame and the origin-interior
H just proved. The force, degree and frame of a further unit are
unrestricted there.

For precision, those sections give a geometric disk cover before
the final contradiction with the third unit. The complete actual
BH owner cover puts B above the top line of H and gives
|c_B,x|>=1/2-epsilon. If the lower margin of H were no greater
than epsilon, that whole B would lie beyond height 1-epsilon>59/60.
The force-free far-wall theorem would give |c_B,x|<3/20, a
contradiction. Thus t<-epsilon, while t+1>1/2 and
1-epsilon>epsilon already hold.

It follows in our reflected chart that

    D_epsilon minus {p_0} is a subset of int H,
    p_0=(epsilon,0).

The two unchanged A wall means strictly straddle zero. Therefore
p_0 is in the relative interiors of both the left A side and the
right H side. These actual two squares occupy opposite local
half-planes, so H union A contains a full neighborhood of p_0.

Consequently **every distinct actual square outside H,A avoids
closed D_epsilon**. A disk point different from p_0 would lie
in int H. At p_0, interior points of any third square would approach
the filled neighborhood and enter int H or int A. Both possibilities
violate the original packing. This includes exact disk tangency.

The cited complete BH proof retains the selected fixed-tip convention,
the separate variable-side-mean branch, every physical B mask and all
H forces. Only its proved local conclusions are used here; no
terminal-four-block hypothesis is imported.

## 4. Every disjoint cyclic block is excluded

Suppose Q is any maximal cyclic block vertex-disjoint from the
triangle H,A,B in the same original positive component. The genuine
leaf L_A cannot be a cyclic-block vertex either. Section 3 makes
every actual unit of Q avoid closed D_epsilon.

Section 2 gives O in int H. The original single edge H--B is a
positive path entirely outside Q to the actual physical boundary
unit B. Section 1 therefore excludes Q.

This conclusion is independent of the block size, root orbit, chord
set, load mask and degrees. In particular it removes the whole
parallel-A/parallel-H geometric interface of the disjoint
C2.35.b2 triangle/five-block family. It does not close that structural
family, since nonparallel A pairs and oblique H frames have not been
excluded here. The shared-root five-block and six-block cases are
outside this last corollary because Q then contains H.

## 5. Exact inputs and review boundary

| Source | SHA256 | Operative scope |
| --- | --- | --- |
| C2_35_TWO_BRIDGES_AND_C2_36_ONE_BRIDGE_ORIGINAL_ATTACHMENT_REDUCTION.md | 28810d74517a6f6a4a4e5b2972c5359bdf41559957bd7e33bcb5fb4b358685d5 | Section 2 full radial-edge, block-circulation and closed-origin transfer; boundary access is explicitly extended to an actual outside path here. |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Sections 1--3 full degree-free support/port-order and winding proof. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Compatible selected embedding and protected exterior access of physical boundary vertices. |
| ROOTED_C3_334_PRIVATE_ADJACENT_LEAF_TWO_LOAD_C4_EXCLUSION.md | 9036a1a8c2b1c7e0f713eef3e0dc3bacbecb42d588332120cf9e04c27ffa98c5 | Section 1 only: complete true A3 genuine-S parallel-pair alignment; arbitrary actual nonleaf neighbors. |
| ROOTED_PARALLEL_DECORATED_TRIANGLE_THIRD_NEAR_UNIT_EXCLUSION.md | 989eae4dd32e7c48617b3e908b149daf847ed1292f484e48eb1e87fb75561426 | Complete local original B mask/owner cover and exact disk-tangent protection, once O in int H is proved. |

The present proof preserves the inherited common-selection and earlier
analytic prerequisite scopes. It uses no numerical pose, force deletion,
replacement mean, finite graph table, Lean execution, compilation, CI,
remote change or shared-ledger mutation. No new whole fine identifier
or coarse cell is earned by this geometric subdomain exclusion.

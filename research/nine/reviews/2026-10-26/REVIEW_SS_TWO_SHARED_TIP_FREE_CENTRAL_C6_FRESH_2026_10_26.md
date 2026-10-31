# Fresh independent full review: two shared tip ports and a free central diamond edge

Date: October 26, 2026.

Reviewer: c6_five, independently of source author fan_review.

**Verdict: PASS unchanged.**

| Frozen source | SHA256 |
| --- | --- |
| SS_HUB_TIP_TWO_SHARED_TIP_PORTS_FREE_CENTRAL_EXCLUSION.md | ecf6da01608b625eb3b357613856cb7df035930a8dba618663aca302922aa1f6 |

I read all nine sections and independently checked both reusable
geometric lemmas, the full original port/leaf cover, the genuine H4
force projection, and the final exact shared-perimeter join.
No repair is requested.

I did not propose or edit either new geometric lemma before this
review. I received the frozen source and its request to inspect the
side-interior corner alternatives and both tilt signs, then read
the complete source and its exact owner-direction and final
shared-perimeter inputs.

## 1. Complete missing-quadrant lemma

The radius-free three-unit L is precisely the southwest, southeast
and northeast unit quadrants. I checked every possible location of
an actual contact with its southwest member S.

Contacts in the relative interiors of S's left and bottom faces
place the entire fourth square west of x=-1 or south of y=-1,
respectively, and cannot reach N. The right-side interior is already
filled on both local sides by S and E. A top-side interior contact
places the whole fourth square in y>=0.

At either left corner, the separate side-interior alternative in T
is essential and is handled correctly. The unique inward normal of
that T face has nonpositive horizontal component because it is a
common supporting normal at S's left corner. The distance along the
unit side from an interior point to either endpoint is strictly less
than one. Its possible horizontal increase is therefore strictly
less than one, and the inward normal span cannot increase x.
Starting at x=-1, the entire T has max x<0 and cannot touch N.
No endpoint is silently classified as a side-interior point.

For the remaining T-vertex alternatives, a right-angle sector
avoiding an open coordinate quadrant lies entirely in one of its
two complementary coordinate half-planes. I checked this on the
whole angular interval: avoiding the southeast quadrant permits
starting angles from zero to pi, and each resulting right-angle
sector is either north or west. The rotated bottom-left and
top-left versions give the source's exact half-plane cover.
At the bottom-right corner S and E fill the northern half-plane.
At the three-square junction the sole available ninety-degree
sector is northwest; side-interior or interior incidence there
cannot fit.

Consequently every possible T is wholly in y>=0 and contacts S at
height zero. In the tilted case its unique lowest vertex has
abscissa in [-1,0]. The edge from that vertex toward its rightmost
vertex has both a positive horizontal component and a vertical
increment strictly between zero and one. If max x>0, an interior
part of that edge lies in the open unit northeast quadrant; an
arbitrarily small motion into T gives overlap with N. The aligned
case gives the same contradiction directly from its [0,1] vertical
interval. Finally contact with N forces max x=0.

Thus the asserted whole-square screen, both support equalities, and
all side/corner contact types are proved without force or radius
assumptions.

## 2. Continuous containment rigidity, both tilt signs

I independently reconstructed both vertex lists in source (7) from
the unique lowest vertex and two upward inward orthonormal axes.
After labeling their positive magnitudes c>=s>0, the lists cover
both signs of tilt and include c=s. The horizontal translation is
fixed by max x=0, not selected by a symmetry assumption.

For case I the actual top corner's squared excess over
1+(t+1)^2 is

\[
             2cs-s^2+2t(c+s-1)>0.
\]

Every sign follows from s>0, c>=s and t>=0. In case II the actual
left corner's squared excess is

\[
             2cs-s^2-2t(1-c)
       \ge s^2\left(1-\frac{2t}{1+c}\right)>0.
\]

Here the first comparison uses c>=s and 1-c=s^2/(1+c);
the strict final comparison uses
2t<1+1/sqrt(2)<=1+c. Both excess identities were checked by
direct expansion using c^2+s^2=1. Therefore every tilted frame has
an actual corner outside the containing disk. The aligned frame is
uniquely fixed by the two support equalities.

The lemma is valid on its entire continuous orientation interval,
including the forty-five-degree wall; it has no sampled-angle
premise.

## 3. Whole shared-port direction and slider cover

The real shared HB and BK contacts make H,B,K coframed. The two
actual B normals have only the stated alternatives:

- Opposite normals put H,K across opposite B sides, separated by a
  positive gap, so they cannot touch.
- Equal normals put them in the same unit column. Disjointness and
  contact force their longitudinal displacement to be exactly one,
  giving a full shared HK side.
- Perpendicular normals give the displayed two-slider chart.

For perpendicular normals, the exact projection intervals require
eta>=0 and zeta<=0 for HK contact. Both strict inequalities give
interior overlap. Exactly one equality gives a positive-length side.
Thus a physical free singleton forces eta=zeta=0. This derives the
whole exact L; it does not impose any actual mean at the L's junction.

The actual selected HK normal at the diagonal singleton is strictly
northeast. Applying the radius-free lemma to the real fourth body C
gives its full northwest support screen. All actual HC applications
are on H's top face or its endpoints, so every real H-to-C normal
has nonnegative vertical component.

## 4. Actual leaf applications and full H4 equation

The accepted lower-radius common-neighbor exit covers the complete
original d<1 hub-tip layout. For d>=1, the two true inward S-root
segments and their shared separation line give |h|<=delta.

The unshortened B3 equation forces its leaf direction strictly
southeast. Its actual support is therefore the lower-right B
vertex (h+1,q), with q<0. At d=1 the support inequality gives h=0
and the leaf norm would give q=0, so the equality radius is explicitly
excluded. On d>1 the full bound q^2<=4delta<1/15 follows.

I freshly read the exact arbitrary-degree owner-direction theorem.
Its physical premises are satisfied at H: actual H-owned HB, the
near-origin genuine root B, and the real common boundary neighbor K.
It therefore gives e_H dot e_x<0 without assigning degree three to
H or discarding HC.

This leaves exactly the upper-left vertex, lower-left vertex, or
aligned leftward side for the H leaf. The upper-left vertex would
give 4h=2q+1, incompatible with 4h<1/15 and 2q+1>7/15.
For the aligned leftward case, the leaf and HB have zero vertical
force, HK has strictly positive vertical force, and HC has
nonnegative vertical force. The full H4 vertical sum is strictly
positive. This handles the entire aligned leaf side, including its
actual mean endpoints.

Only the lower-left leaf remains. Equal norms of its support and
the B leaf support force h=0. No H3 or K2 equation enters this step.

## 5. Physical K and exact disk level

With h=0 and t=q+1>11/15, the obtained K rectangle has unique
farthest corner (1,t+1). Its genuine positive circle load requires
that corner to have norm R, giving R^2=1+(t+1)^2 without a
prior mask assumption or a shortened K force equation.

Combining this equality with d^2=1+q^2 and the defining
R^2=(d+1)^2+1/4 gives exactly
4q=2d-11/4. Hence q=d/2-11/16<-43/240 and
0<t<197/240. The source's containment condition follows from

\[
 2t<197/120<17/10<1+1/\sqrt2.
\]

The first rational comparison has reserve 7/120, and
1/sqrt(2)>7/10 follows by squaring positive quantities.
The actual C now satisfies every containment-rigidity premise,
so it must be the aligned missing square [-1,0] x [t,t+1].
Both possible physical C masks and every original C contact owner
were retained until this physical conclusion.

## 6. Exact final feature join

The derived geometry makes all four real perimeter intersections
HB, BK, KC, CH full shared sides. The original positive perimeter
forces and their actual means have not been moved or replaced.
The original central HK magnitude remains positive.

I freshly read the complete pinned shared-perimeter exclusion.
Its full H4/K3 argument covers this obtained geometry, retains the
actual central force, and uses the existing compatible common-frame
diagonal avoidance. Its conclusion applies directly here; no new
normal choice is made in the present source. The original physical
three completion units remain unrestricted throughout.

This closes exactly the whole HB/BK-shared, HK-free feature in the
original S/S hub-tip gate. It does not claim that other perimeter
owner patterns are shared, nor that the entire original gate is
closed.

## 7. Dependency record and verification limits

All five dependency hashes match the frozen source's table:

| Dependency | SHA256 |
| --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 |
| SS_HUB_TIP_DIAMOND_SHARED_PERIMETER_EXCLUSION.md | d7e7cafe4b9dd636bbbef1e0857e3dda1605404a382c27623ca26d3f707dc4b2 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |

The complete source passes unchanged. The proof and this review use
no pose grid, numerical exclusion packet, selected side mean, deleted
force, reduced higher degree, new gate ID, ledger edit, Lean invocation,
CI workflow or remote mutation.

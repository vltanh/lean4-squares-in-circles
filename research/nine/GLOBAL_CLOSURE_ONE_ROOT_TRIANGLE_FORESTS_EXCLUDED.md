# One triangle cannot carry an arbitrary bridge forest through one root

Date: October 26, 2026.
**Status: accepted complete hand theorem after full-source root review in
REVIEW_ONE_ROOT_FORESTS_AND_OFF_ORIGIN_BRIDGES_ROOT_2026_10_26.md and
separate independent review in
REVIEW_ONE_ROOT_TRIANGLE_FORESTS_ROOTED_BLOCKS_2026_10_26.md.**
This source uses the additional proved minimal-support stress selection
of GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. It is a theorem
about that common selected certificate on the unchanged canonical pose,
not a claim that every earlier stress representation is minimal.
No original gate, coarse-cell tick or shared ledger is changed here.

## 1. Full graph scope and the additional selection

Work with all nine actual squares at the common radius/Phi-minimizer
pose, in 79/40<=R<=sqrt(1105)/16. Keep the previously selected physical
normals, their strict point-contact conventions, all physical circle
masks, every mean, and all zero-stress physical contacts. Among compatible
normalized planar stresses on that same pose, choose one with the fewest
positive original scalar atoms, as in the articulation source.

**Theorem.** This selected positive component cannot have exactly one
cyclic block, a triangle A--B--C--A, with every bridge tree attached
to the triangle at the same vertex A. The forest may have arbitrary
branching and all its actual bodies and loads are retained. The result
includes all such seven-, eight- and nine-body attachment families.

The triangle tips B,C have their genuine positive degree two. They are
loaded, because an unloaded degree-two transmitter separates its two
neighbors, whereas those neighbors physically touch. Consequently A is
physically circle-clear, by the no-three-mutually-touching-boundary-units
theorem. Put M=F_B+F_C. The accepted whole end-triangle theorems give

    M != 0,                 c_A.M>0,
    h_A(M/|M|)<d,           d=sqrt(R^2-1/4)-1.             (1)

Their exact sources are BOWTIE_CELL_CLOSED.md, Section 2, and
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md. They allow every extra force
at A and retain both actual tips; no petal is replaced by a square.

Write epsilon=max(d-1,0), and delta=max(R-2,0). Throughout the window,

    9/10<d<61/60, epsilon<1/60, delta<1/12,
    |c_S|<91/60 for every contained unit S.                 (2)

The articulation source supplies two further facts at exactly this
unchanged canonical pose:

* Every loaded body incident only to bridges is a genuine leaf. This
  uses its exact stress split and the established complete exclusions
  on at most five bodies; the named assemblies are given there.
* At an unloaded articulation there are at most three branches.
  In particular A has at most two bridge branches, in addition to
  its intact triangle branch. Every outside branching vertex has
  degree at most three.

We will also use the following immediate refinement of the same linear
argument: **three branches at an unloaded articulation cannot have
collinear resultant vectors.** Indeed their vectors (f_j,a_j), with
a_j>0, then span at most two dimensions. A nonzero dependence and the
nonnegative branch scaling of that source remove a positive branch
while preserving the full normalized stress, contradicting the chosen
minimum. This is a proved change-of-stress contradiction, never an
equilibrium equation obtained by dropping an old force.

Every outside nonleaf is therefore truly unloaded and has only bridge
edges. Every outside leaf has its actual radial S or D geometry.

## 2. Local all-bridge geometry, with no whole-tree premise

### 2.1. Every unloaded all-bridge body meets the central disk

Let U be truly unloaded and incident only to bridges. If it did not
meet D_delta, the radial bridge central-endpoint theorem would make it
the outer body at every incident edge. A zero application is impossible.
Every application would equal U's unique nearest point to the origin,
and all its positive pair-force directions would agree. They could
not balance without a circle load. Thus U meets D_delta and

    |c_U|<19/24.                                          (3)

This is the local proof of TREE_BODY_LOCALIZATION.md, Theorem F1.1.
Its use here does not assume that the full component is a tree: only
the genuine zero load and all-bridge incidence of U were used.

### 2.2. Outward radial support of a square avoiding the origin

If a unit square S avoids the origin and p=t e, t>0, is an actual
outward radial support point, then t>1. In S's own axes some center
coordinate has magnitude greater than 1/2. Reverse it to be greater
than 1/2. Every point of S has positive coordinate on this axis, so
radial support at p uses its far face, whose coordinate exceeds one.
This proves t>1, exactly as in TREE_BODY_LOCALIZATION.md, Lemma F1.3.

Any inward bridge at a square avoiding zero uses its unique nearest
point. All such incoming forces are therefore parallel with the same
sign. A positive-radius outward bridge from such a square cannot lead
to an unloaded all-bridge body: that neighbor would have nearest-point
radius greater than one, contrary to (3) and its D_delta intersection.

### 2.3. No terminal arm of an outside fork has length three or more

Let H be an outside branching vertex and follow a branch from it to a
genuine leaf L with only degree-two vertices in between. All intermediate
vertices are truly unloaded. The original transmitter law gives a common
radial force line and widths in {1,sqrt(2)}, without changing a mean.

If the arm has at least three edges, there are at least two intermediate
widths. With e the actual leaf direction and r_L=d or R-sqrt(2), the
unchanged H application is

    p_H=(r_L-W)e,        W>=2,       r_L<=d.

Since H lies in e.x<=r_L-W, its center has
c_H.e<=d-2-1/2<-89/60. This contradicts (3). Thus every such terminal
arm has length one or two.

## 3. Two terminal arms place a disk inside their root

Suppose H has two distinct terminal arms, each of length one or two.
Each intermediate body, when present, is its original truly unloaded
degree-two transmitter. Then

    D_epsilon subset H.                                   (4)

If d<1, the origin is in the open interior of H. If d>1, (4) already
puts the origin in its open interior. At d=1 only the weak containment
of the origin is needed below. No force equation at H is used in this
lemma, so its other branch remains arbitrary.

Here is the complete arm cover.

* **Two direct leaves.** The full central-disk lemma is
  TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1.
  It proves the asserted strict containment for d!=1 and retains the
  entire origin-vertex exception when d=1.
* **A direct D leaf and a two-edge arm.** The geometric part of
  TRIANGLE_THREE_BRIDGES_MIXED_ARMS_D_EXCLUSION.md, Section 1, forces
  d>1, a side-normal S arm, and, up to a rigid frame,

      H=[d-2,d-1] times [r-1,r],     r=R-sqrt(2).

  The horizontal near-side distance is epsilon, and the other three
  side distances exceed epsilon. This proves (4). That cited section
  precedes every triangle force equation and uses only the two actual
  arm geometries.
* **A direct S leaf and a two-edge arm.** The geometric part of
  TRIANGLE_THREE_BRIDGES_MIXED_ARMS_S_EXCLUSION.md, Section 1, excludes
  d<1 and forces a side-normal S arm. For d>1 its complete root is

      H=[epsilon-1,epsilon] times [2sqrt(epsilon)-1,2sqrt(epsilon)]

  after reflection. Each of the three other side distances is greater
  than epsilon: 2sqrt(epsilon)>epsilon and
  1-2sqrt(epsilon)>epsilon on 0<epsilon<1/60. Thus (4) holds.
  At d=1 the unchanged arm application is zero, so 0 belongs to H.
  No tip equation from that source is imported into this lemma.
* **Two two-edge arms.** Section 1 of
  GLOBAL_CLOSURE_TWO_LEAF_ARMS_END_TRIANGLE_EXCLUSION.md proves their
  entire force-free classification. It forces d>=1, two side-normal
  S arms, and H=[epsilon-1,epsilon]^2 in the two actual orthogonal
  arm directions, including the full epsilon=0 endpoint. This gives
  (4) directly.

These four alternatives include every S/D leaf, both transmitter widths,
every original side slider and every endpoint mean.

## 4. Any outside fork is impossible away from d=1

Suppose the attached bridge forest has an outside branching vertex.
Root its trees at A and choose a branching vertex H farthest from A.
It has one parent and two terminal arms: the degree-three conclusion
in Section 1 excludes further children. Section 2.3 bounds both arm
lengths by two, so Section 3 applies.

For d!=1, H contains the origin in its open interior, and hence A
avoids zero. When d>1, A is moreover disjoint from the open disk
D_epsilon, because that disk is contained in H's interior. This
last assertion follows from (4) even when H touches the closed disk
on one or two sides.

Classify an actual bridge directed outward from A. Its radial application
is p=t n for a real signed t. A zero value would put zero in A and
is impossible. If t<0, A is the outer body and the application is
its unique nearest point. All such bridge forces agree in direction.
If t>0, Section 2.2 gives t>1. Its outer neighbor cannot be an unloaded
all-bridge body, by Section 2.2. It must be a direct S leaf, with
t=d>1; the D radius is below one.

If such a direct S leaf occurs in direction e, the actual unit inward
segment in A contains (d-1)e=epsilon e. Since A avoids the open disk
D_epsilon, this is its unique nearest point. Consequently every incoming
bridge at A points along -e. A second outward S leaf would have another
nearest point epsilon e', forcing e'=e and repeating the same physical
leaf. Thus there is at most one outward bridge. The branch containing
H is not that leaf, so an incoming bridge also occurs. The two tree
resultants and M are collinear by the full A force equation, contrary
to the minimal-support refinement in Section 1.

If no outward bridge occurs, all tree resultants at A have the same
incoming direction. Two tree branches would again make all three
branch resultants collinear. Thus there is exactly one bridge at A.
Its application, directed from the forest into A, is rho e with

    rho>=epsilon when d>1,       rho>0 when d<1.

A has its exact degree three, B,C their exact degree two, and
A subset {e.x>=rho}. The full theorem
OUTER_BRIDGED_TRIANGLE_EXCLUSION.md applies with
rho>=max(d-1,0). It allows arbitrary cycles or branching on the other
side of that bridge and excludes this entire end triangle.

Therefore the outside-fork alternative is impossible at every d!=1.

## 5. The full critical radius, without a tree-force substitution

Now d=1 and R^2=17/4. We first establish two facts directly in the
original component; no complete tree theorem is applied to it.

### 5.1. Every outside nonleaf contains zero

If an outside unloaded U avoided zero, all its incoming bridge forces
would agree. Its unloaded force balance therefore requires an outgoing
radial support. Section 2.2 puts that support at radius greater than
one. Its outer neighbor cannot be an unloaded all-bridge body, or an
S/D leaf whose radius is at most one. It must consequently be A.

Then A has nearest-point radius greater than one and avoids zero.
Every outward radial bridge of A would likewise have radius greater
than one, but its neighbor could be neither an outside unloaded body
nor an S/D leaf. Thus all A bridges are incoming and parallel. Two
are excluded by minimal support; one is excluded by the outer bridged
triangle theorem, now with threshold zero. This contradiction proves
that every outside nonleaf contains zero.

The same argument at A shows that, whenever there is an outside
nonleaf, A also contains zero. If A avoided zero, none of its bridges
could be outgoing, so the preceding parallel or single-bridge
contradictions apply. Its origin point is on its boundary because
another physical square contains zero.

### 5.2. The root receives only actual origin forces, with at most one leaf

Every A bridge to an outside nonleaf has actual application zero:
the separating line of two squares containing zero passes through
zero, and radiality makes its normal-parallel application zero.
All such outward directions belong to A's normal cone at zero.

There are at most two tree branches at A. If an outside fork exists,
at least one branch starts with an outside nonleaf. At most one other
branch can be a direct leaf. It cannot be D, because a D leaf would
put zero in the open interior of A. Thus the only possible direct
leaf is S.

If both actual tree forces are applied at zero (or there is just one
such force), their negative sum M lies in A's inward normal cone at
zero. At a side-interior origin this gives h_A(M/|M|)=1. At an
origin vertex, write A=[0,1]u+[0,1]v; the unit vector M/|M| has two
nonnegative own components, so its support is their sum, at least
one. Both cases contradict the strict end-triangle bound (1).

### 5.3. One direct S leaf and one original origin force

For completeness the remaining critical implication is proved with
its actual full root equation. It also explains why the earlier
mixed-arm critical argument legitimately applies to an arbitrary
branch at the same original origin port.

If zero is in an A side interior, the only outward radial support
of norm one is the foot on its opposite side. The S leaf is in
that direction e, and the origin force points along -e. Thus M is
parallel to e. The positive pressure c_A.M>0 makes M point along e,
but h_A(e)=1 contradicts (1).

Otherwise write A=[0,1]u+[0,1]v, with its genuine S leaf S(u) at
the unit support u. Let beta n be the other tree force at zero.
The actual full equation is

    M=-alpha u-beta n,     alpha,beta>0,
    n.u<=0, n.v<=0.                                      (5)

If n.v=0, n=-u. The pressure in (1) makes M a positive multiple
of u, contradicting its support bound at height one. Hence n.v<0
and M.v>0.

When the two root triangle normals are nonparallel, their actual
concurrence is q=-t M/|M|, t>0, and every port is proper, by
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md. In particular q.v<0.
An A-owned u-axis normal would put its port on the line of v-coordinate
q.v<0, outside A. An A-owned -v normal has negative dot product
with M, contrary to the physical triangle nonobtuse-normal lemma.

The origin cannot belong to a boundary tip. The vertex u is the
inner-face midpoint of the actual leaf S(u), so any different
neighbor containing it is physically circle-clear by the complete
radial-inner-face neighbor screen. A strictly exposed port at u+v
has support n.u+n.v>1=d and cannot have a contained neighbor.
Thus only the vertex v and an A-owned +v side port remain.

A +v side port has support height one. Sharp support equality makes
its neighbor exactly the radial unit S(v). A second boundary tip
at v would then be a boundary neighbor of S(v)'s inner-face midpoint,
impossible by that same screen. Two nonparallel vertex-v ports
would have concurrence v, contradicting q.v<0.

If the root normals are parallel, they agree because the tips touch.
A strict vertex direction gives both applications at the same vertex.
The two genuine proper tip concurrences then lie on that same normal
line; their connecting BC line is parallel as well, contradicting
the nonparallel tip-force lemma. Distinct positive radial tip directions
exclude coincident tip concurrences. The only remaining axis with
positive v component is +v, whose height-one equality makes both tips
the same S(v), again impossible.

This exhausts the critical root interface. It is precisely the
whole geometric argument of
TRIANGLE_THREE_BRIDGES_MIXED_ARMS_S_EXCLUSION.md, Sections 5--6,
with (5) explicitly supplying its required origin force. The force
comes from the unchanged actual branch, and no internal branch
equation or positive force has been removed.

Together Sections 5.1--5.3 exclude every outside fork at d=1 too.

## 6. With no outside fork, only the already complete arm families remain

If no outside vertex branches, every bridge branch of A is one
simple path ending at its genuine leaf. There are at most two such
paths. All their internal bodies are truly unloaded.

A path of four or more edges is geometrically impossible: its root
application has coordinate at most d-3<-119/60 along the leaf
direction, giving c_A.e<-149/60, contrary to |c_A|<91/60.

With one path, the complete length-one, length-two and length-three
attachments are excluded respectively by

* ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md;
* TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md;
* TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md.

With two paths, neither has length three. Indeed such a path puts
the unique nearest point of A at radius greater than 59/60. A direct
leaf on the other path would make A meet D_epsilon, impossible.
A second path of length at least two has either a negative signed
root application, or the sole nonnegative S/side alternative of
radius epsilon. The latter is too near zero. In the former case
uniqueness of A's nearest point forces both leaf directions to agree.
Two actual S leaves in one direction coincide, two D leaves coincide,
and an S and D on one ray overlap. All are physically impossible.

Thus both path lengths are one or two. Their full original families are

| Lengths | Complete whole-attachment source |
| --- | --- |
| 1,1 | ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md |
| 1,2 | TRIANGLE_THREE_BRIDGES_MIXED_ARMS_EXCLUSION.md |
| 2,2 | GLOBAL_CLOSURE_TWO_LEAF_ARMS_END_TRIANGLE_EXCLUSION.md |

Every source retains the root's true positive degree. The direct-leaf
and mixed sources retain all physical completion squares at the
critical radius. The final row is the complete seven-body two-arm
theorem, accepted after full-source root and separate independent
reviews in REVIEW_TWO_ARMS_AND_D_WALL_ROOT_2026_10_26.md and
REVIEW_TWO_LEAF_ARMS_END_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md.
With no bridge at all the triangle is already excluded
by CYCLIC_BLOCK_INVENTORY.md, Section 6.

The fork and no-fork alternatives exhaust every finite bridge forest
attached only at A, proving the stated selected-certificate theorem.

## 7. Exact inheritance and remaining scope

The only new selection is minimizing the number of positive scalar
atoms among stresses on the same fixed physical pose with the same
preselected normal system. Branch scaling proves every use of its
minimality. It preserves the radius/Phi-minimizer, all surviving normals,
every surviving aggregate mean and the nine physical squares. No later
argument combines equations from two different stresses.

The theorem removes all single-triangle-root forests at once for that
selected certificate. It does not eliminate a bridge forest attached
at two or three different triangle vertices, a component with another
cyclic block, or a chorded triangle block. It therefore does not alone
close C1.3.b4, C1.3.b5 or C1.3.b6, and supplies no sharp nine-square
or equality conclusion. Its original canonical-pose premise must
remain attached to every later use.

No pose sampling, numerical optimization, scalar certificate, Lean
compilation or CI is used.

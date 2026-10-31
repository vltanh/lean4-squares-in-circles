# A single cyclic block cannot carry five original bridges

Date: October 27, 2026.

**Status: accepted complete hand whole-forest theorem after full-source
root and separate independent reviews in
REVIEW_ONE_CYCLIC_BLOCK_FIVE_BRIDGES_ROOT_2026_10_27.md and
REVIEW_ONE_CYCLIC_BLOCK_FIVE_BRIDGES_ROOTED_BLOCKS_2026_10_27.md.** Its new whole coarse-cell
application is C1.4.b5, with every actual four-body cyclic block and
every five-edge bridge forest retained. No shared ledger or fine
count is changed.

Keep the same original nine physical unit squares, common compatible
selected radius/Phi-minimizer pose and minimum-positive-scalar-support
certificate, with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),       1/2<r<7/10,       9/10<d<61/60.

The positive component has exactly one cyclic block and exactly five
bridge blocks. No equation internal to the cyclic block is replaced
by a leaf, triangle or smaller-block equation. All actual forces,
positive degrees, masks, individual zero weights, original normals
and shared-side means remain.

**Theorem.** This original positive component is impossible in the
same nine-square packing.

For C1.4.b5 the block has four bodies, and all nine original physical
units are positive bodies because 4+5=9. The same proof also applies
to the already excluded single-triangle/five-bridge profile; it uses
no internal graph type of the cyclic block.

## 1. Every outside nonleaf and every genuine leaf root is an actual near unit

All bodies outside the cyclic block are incident only to bridges.
The accepted exact splitting theorem
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md excludes a loaded
all-bridge nonleaf in the common selected nine-square certificate.
Its exact nonnegative split preserves the actual pose, normals,
means and circle atoms; one may use either the stipulated minimum
positive scalar support or its accepted same-nine small-core
consequence. Thus every outside nonleaf is truly unloaded, and
every outside leaf is a genuine positive radial S/D leaf.

Every such unloaded nonleaf meets D_epsilon. If it contains O,
this is immediate. If it avoids O, the complete theorem
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md gives its actual
side-transmitter chart with inner application rho e, where
0<rho<=d-1. That unchanged point belongs to D_epsilon. In
particular at d<=1 every outside nonleaf contains O closed.
No fictitious terminal geometry is assigned to its cyclic neighbor.

Every genuine leaf root also meets D_epsilon by its actual radial
inward unit segment. At d<=1 it contains O closed; a D leaf root
always contains O openly. These statements allow arbitrary actual
degree and other forces at a cyclic leaf root.

Let I be the number of outside nonleaves, L the number of genuine
leaves, and q the number of distinct cyclic-block bodies with at
least one genuine direct leaf. The five bridges add precisely
five outside bodies, so

    I+L=5.

The I outside nonleaves and q cyclic direct-leaf roots are distinct
actual near units. The accepted force-free capacity theorem
FOUR_NEAR_ORIGIN_UNITS_NINE_CAPACITY_EXCLUSION.md therefore gives

    I+q<=3.                                          (1)

The actual support-minimal articulation bound gives two further
degree facts. An outside nonleaf has at most three incident
branches, and hence degree two or three. A cyclic body has at
most two attached bridge branches: deleting it leaves one connected
remainder of its biconnected block and one component per attached
branch. Thus three attached branches would already give four
articulation branches. An unloaded three-branch articulation
cannot have its three actual branch forces collinear, by the
same full branch reweighting theorem.

In particular any genuine leaf root has at most two genuine
leaves. Also

    I+q>=2.                                          (2)

If I=0 and q<=1, five direct leaves would be attached to one
cyclic body, violating its two-branch bound. If I=1 and q=0,
all four leaves would be attached to that sole outside nonleaf,
violating its degree-three bound. These exhaust I+q<=1.

## 2. Exact rooted-tree and physical tools

Each outside bridge tree attaches to the cyclic block at one body;
two attachments would create another route and destroy the bridge
property. Orient its edges away from the block. An outside nonleaf
has one parent and one or two children. A vertex with two children
is called a fork here. This is only a description of its actual
degree three; all three positive forces remain.

If a fork is farthest from the block, each child branch is a
simple terminal arm ending in a genuine leaf, with true unloaded
degree-two transmitters in between. At any such transmitter the
two actual widths are one and sqrt(2), with actual radial means
kept. For a terminal arm of length ell and leaf direction e,
the application's radial coordinate at its root is

    x=r_L-W,
    r_L in {r,d},       W=sum of the ell-1 actual widths,
    root subset {z:e.z<=x}.                           (3)

Here r_L<=d and every width is at least one. If an outside
nonleaf rooted an arm of length at least three, then
x<=d-2<-epsilon. This contradicts that root's actual point
in D_epsilon. Hence every child arm of a farthest fork has
length one or two. A simple pendant path from the cyclic
block has length at most three, by applying the same fact
at its first outside body.

We use the following complete physical results at d=1,
equivalently R^2=17/4. Their scope is independent of graph,
load and other-square orientations; it is also explicitly
exported in ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md,
Section 4.

* THREE_VERTEX_ORIGIN_CAPACITY.md: three distinct actual
  unit squares with O as a vertex allow at most eight
  physical unit squares in total.
* P_ALL_COMPLETION.md: the two actual radial S squares
  S(e),S(-e), together with any two actual aligned units
  in the intervening opposite unit-width strips whose
  transverse intervals contain zero, allow at most eight.
  Both original transverse endpoint sliders are included.
* The force-free physical conclusion of Sections 3--4 of
  TREE02_POINT_CONTACT_COMPLETION.md: two actual vertex-
  origin units meeting only at O, together with four
  distinct physical radial S squares on their four own
  side rays, allow at most eight. Once these six original
  bodies are supplied, none of the four outer bodies is
  required to have positive graph degree one.

Here S(e) at d=1 is the unique actual radial unit

    S(e)={t e+s Je:1<=t<=2, -1/2<=s<=1/2}.

We will supply every one of these bodies before invoking a
capacity result. The sharp contained-unit half-plane bound
from END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1,
says that a unit beyond e.z>=t has t<=d; at equality it is
the unique radial S(e). This bound is purely physical and
permits an arbitrary cyclic or bridge-attached neighbor.

## 3. Every noncritical forest has exactly two possible leaf counts

Suppose d!=1. If any body supports two genuine leaves, the
full geometric lemma in
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md,
Section 1, gives O in its open interior for d<1, or the
whole closed D_epsilon in its open interior for d>1.
Equation (2) supplies a distinct other actual near unit.
That unit contains O when d<1 and meets D_epsilon when
d>1. In either case the physical squares overlap.

Therefore every genuine leaf has a distinct root in this
noncritical domain. All those roots belong to the I+q
near units, so L<=I+q<=3. Since I=5-L and I<=3, L>=2.
There are exactly two numerical possibilities:

    (a) L=3, I=2, q=1;
    (b) L=2, I=3, q=0.                              (4)

For (a), three distinct leaf roots and only two outside
nonleaves force q>=1, so (1) gives q=1. In either row
there are exactly two distinct outside genuine leaf roots.
The q=1 row has one further genuine direct leaf at a cyclic
body C. Thus there are exactly three known near units.

For later reference, if t is the number of attached outside
tree components and F the number of outside forks, the
actual rooted forest satisfies

    L=t+F.                                          (5)

This is the elementary child-count identity: each tree
starts with one terminal branch, and each fork adds one
additional leaf. No positive edge or force is contracted.

## 4. The entire strict low-radius domain d<1

All actual outside nonleaves and cyclic direct-leaf roots
contain O. A D root would contain it openly and overlap
another such unit, so every leaf is S.

There can be no outside fork. A farthest fork has two
terminal arms. They cannot both be direct leaves, since
Section 3 proved all leaf roots distinct. At least one
arm has length at least two, and (3) puts its actual
support at x<=d-1<0. This is impossible at a root
containing O.

The outside forest is consequently a union of simple
paths. Each of its two distinct outside genuine leaf
roots has true degree two. A diagonal S transmitter
contains O openly, since O lies strictly between its
opposite vertices d e and (d-sqrt(2))e. An aligned
side transmitter is

    [d-1,d] times [b,b+1],       b<=0<=b+1.

Its longitudinal interval contains zero strictly. If the
transverse slider is interior it again contains O openly.
Any of these open containments overlaps another near unit.
Thus both outside genuine roots have O in a relative
side interior. Their local occupied half-planes must be
opposite, and their union contains a full neighborhood
of O. No third actual square can contain O.

But each row of (4) has a third distinct actual near unit,
which contains O at d<1. This excludes the full low-radius
domain, including every transverse endpoint of the true
degree-two roots.

## 5. The entire strict high-radius domain d>1

Each row of (4) has three actual near units. If any leaf
were D, its root and the other two actual near units
would violate D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md.
That uniform theorem imposes no degree or force premise
on the two other units. Hence every leaf is S.

A true degree-two genuine leaf root cannot be diagonal.
In its own axes its four origin-side margins are
d/sqrt(2) and 1-d/sqrt(2), each twice. Both exceed epsilon:
the first exceeds 1/2, and the second exceeds 23/84 by
d<61/60 and sqrt(2)>7/5. Thus D_epsilon would lie
strictly inside this root and overlap another near unit.
Every actual terminal transmitter of degree two is
therefore S/side. Its inward port is epsilon e, and its
parent body contains O by the actual inward unit segment.

### 5.1. Row (a): two outside nonleaves and three leaves

Both outside nonleaves U,V are distinct genuine single-
leaf roots. If they lie in separate outside trees, both
are exact length-two arms with cyclic parents A,B.
The additional direct leaf is at C. The parent points
just proved put O in A and B. The four-near-unit theorem
would be contradicted unless A=B=C, since U,V,C are
already three distinct near units. But A=B=C would
attach two arms and a direct leaf at the same cyclic
body, violating its two-branch bound. This case is closed.

If U,V belong to one outside tree, they are adjacent.
After naming, U has its parent at the cyclic block,
one genuine direct leaf and the short arm U--V--L.
It keeps its full three original forces. The force-free
mixed-root geometry in Section 1 of each of
TRIANGLE_THREE_BRIDGES_MIXED_ARMS_D_EXCLUSION.md and
TRIANGLE_THREE_BRIDGES_MIXED_ARMS_S_EXCLUSION.md gives
the complete high-radius charts

    [epsilon-1,epsilon] times [r-1,r]       (direct D),
    [epsilon-1,epsilon] times
      [2sqrt(epsilon)-1,2sqrt(epsilon)]     (direct S),

after rotation and reflection in the actual arm direction.
Only the second type remains here, but the geometric
statement includes both without any cyclic-root equation.
In either chart D_epsilon is inside the root and its
only boundary point on that disk is the arm point
epsilon e. The distinct genuine root C must supply
its actual epsilon e_C outside int U, so e_C=e.
Its genuine radial S leaf would then be the same physical
S leaf as the terminal of U's arm, contrary to the
distinct original bodies. This excludes row (a).

### 5.2. Row (b) with two outside trees

Here I=3,L=2 and q=0. If t=2, (5) gives F=0, so
the two original trees are simple paths. Their positive
internal-body counts are one and two. The shorter path
is a true length-two arm. Its side S transmitter has
an actual inward epsilon point, so its cyclic parent
contains O as proved above. That parent is a fourth
near unit, distinct from all three outside nonleaves.
The uniform four-near capacity excludes this case.

### 5.3. Row (b) with one outside tree

If t=1, (5) gives exactly one fork W. Let k be the
number of outside bodies on the stem from the block
through W, and let ell_1<=ell_2 be its two terminal
arm lengths. The internal count I=3 gives

    k+ell_1+ell_2=5.

Two direct child leaves are excluded because their roots
would agree. The complete remaining possibilities are

    (k,ell_1,ell_2)=(1,1,3), (1,2,2), (2,1,2).

The length-three child arm in the first case contradicts
Section 2's near-root support bound.

In the second case both arms are S/side and their actual
W applications are epsilon e_1 and epsilon e_2. Their
directions are distinct, since otherwise their two real
radial S leaves would coincide. A unit with two distinct
outward radial supports of norm epsilon<1/60 must use
two adjacent own-side axes: a strict vertex of that norm
has its two adjacent vertices farther than 1-epsilon,
its opposite vertex still farther, its two adjacent
side distances strictly below epsilon and its other
side distances greater than 1-epsilon. It supplies no
second radial support of the same norm. Opposite side
faces would require 2epsilon=1. Thus the actual W is

    W=[epsilon-1,epsilon]^2

in its two actual arm axes. Its unchanged zero-load
three-force equation makes the parent normal strictly
negative in both axes. The parent application is the
unique opposite vertex, with radial norm

    sqrt(2)(1-epsilon)>59sqrt(2)/60>61/60>d.

This violates the sharp contained-neighbor support bound.
The original parent is not assumed loaded or a leaf.

In the final case W has a direct leaf and one short
arm, and its parent Z is another actual outside nonleaf.
Use the full mixed-root chart from Section 5.1. Since
Z meets D_epsilon and avoids int W, it contains the
unique possible point epsilon e on W's small disk.
That point lies in the relative interior of the actual
arm side of W. The unchanged WZ support therefore has
normal e: both bodies contain this point, and the
original separating support must support W there.
The actual W-to-arm force is also a positive multiple
of e. But its genuine direct leaf has a nonzero transverse
component in either mixed chart. W's full three-force
equation, with no circle load, cannot balance that
transverse component. This closes the last high-radius
case and hence the entire d>1 forest.

## 6. Critical local fork facts at d=1

It remains d=1. All actual near units contain O. Any
two-leaf root is either origin-interior, immediately
overlapping another near unit by (2), or has O as a
vertex and its two genuine leaves are the actual S
squares on its two own side rays. Keep the original
closed-origin alternatives for every other body.

Choose an outside fork farthest from the block. Section 2
makes its child-arm lengths one or two. We exclude all
three possibilities below with the original three forces.

### 6.1. Two length-two child arms

The fork W contains O. Each length-two child-arm port
has coordinate r_L-w<=0, while its actual W support
must be nonnegative. Thus both arms are S/side with
actual root point O. Their directions e_1,e_2 differ,
since their genuine S leaves are distinct physical units.

W cannot have O in a side interior, whose only outward
normal there would make e_1=e_2. It has O as a vertex.
The two side transmitters U,V also contain O. If both
have O as a vertex, the three-origin-vertex capacity
already excludes nine squares. Otherwise exactly one
has O in a side interior; an interior origin would
overlap W. Its half-plane and the other two right-angle
sectors fill the full turn. The three actual frames
therefore agree, with W and the other vertex square
partitioning the opposite half-plane into two quadrants.

Both arm normals are now actual axes of W. They are
distinct, and opposite normals cannot support the same
W vertex, so they are perpendicular. In these axes
W=[-1,0]^2 and its two arm forces point east and north.
Its full third force points strictly southwest. The
actual parent port is (-1,-1), with radial norm sqrt(2),
contradicting the sharp bound d=1. This handles every
critical side-mean or vertex endpoint of the two arms.

### 6.2. One direct leaf and one length-two child arm

Let the fork be W and the side transmitter on its short
arm be V. As above, the arm is S/side with actual WV
point O. W's direct leaf cannot be D, which would make
O interior and preclude this support. It is S.

If O is in a relative side interior of W, its only
radial outward support of norm one is the opposite side
foot. Hence its direct leaf force and the arm force
are opposite parallel. The full third force is parallel
too, contradicting the actual unloaded three-branch
noncollinearity from minimum support.

Otherwise W=[0,1]u+[0,1]v with its direct leaf S(u).
Write e for its actual arm normal and n for its actual
parent normal. The unchanged equation is

    alpha u+beta e+gamma n=0,
    alpha,beta,gamma>0,
    e.u<=0,       e.v<=0.                            (6)

If e.v=0, all three forces are collinear. Thus e.v<0,
so n.v>0. A negative n.u would expose v, which is
radial only for n=v; a positive n.u would expose
u+v of norm sqrt(2)>d. The full radial support law
therefore forces n=v. Equation (6) now gives e.u<0
as well. The W origin quadrant lies strictly inside
the half-plane opposite the arm direction.

The actual V cannot have O as a vertex: WV would
then be point-only, since W's normal e exposes only
O, but e is V's side axis and would not strictly
expose its vertex, contrary to the retained selected
point-normal convention. Thus V has an origin-side
interior. Its half-plane and W's strict quadrant
leave two gaps each narrower than pi/2. No third
actual square can contain O.

There must be such a third actual near unit in the
present five-bridge forest. If the only near units
were W,V, then I=2,q=0 and L=3. The third genuine
leaf could not attach to W, whose true degree is
already three. It would have to attach to V, turning
V into a deeper fork and contradicting the chosen
farthest fork. Hence this child-arm type is excluded.

### 6.3. Two genuine direct child leaves

Let the fork be W and its actual parent K. Its root
geometry gives W=[0,1]u+[0,1]v, with two actual leaves
S(u),S(v). Its full unloaded three-force equation
makes the original parent normal strictly negative
in both own axes. The real WK application is therefore
O, so K contains O closed and W meets K only at O.

There is no third actual square containing O. If K
has an origin-side interior, W's strict quadrant and
K's half-plane leave two gaps narrower than pi/2.
If K has O as a vertex, the two complementary gaps
between their point-only quadrants are both positive
and less than pi. A third origin unit could only
have O as a vertex, and the three-vertex capacity
would contradict nine. An interior origin in K
already overlaps W. This proves the claimed isolation
with all physical endpoint cases retained.

Consequently all known near units belong to {W,K}.
If K is cyclic, there can be no other outside nonleaf
and no other cyclic direct-leaf root. The remaining
two of the five bridges must therefore be two genuine
direct leaves at K, in addition to its W branch.
That violates K's two-branch bound.

If K is outside, it is the only other outside nonleaf,
and no cyclic body has a direct leaf. The actual graph
then has exactly three genuine leaves: two at W and
one at K. K has true degree three, with its third
edge leading to a cyclic body A.

If K has an origin-side interior, its sole norm-one
radial support is its opposite side foot. Its genuine
leaf force and WK force are opposite parallel, so
its full third force is parallel too, forbidden by
the three-branch selection. Otherwise K has O as a
vertex. Write K=[0,1]w+[0,1]z with its genuine leaf
S(w). Since WK is point-only, its original outward
K normal n_W strictly exposes O on K. Both its own
components are strictly negative. The full equation

    alpha w+beta n_W+gamma n_A=0

therefore gives n_A.z>0. The same radial support
cover as in Section 6.2 forces n_A=z and actual
KA point z: a negative w component would expose
the nonradial vertex z, while a positive one would
expose w+z at forbidden radius sqrt(2). The sharp
support equality consequently makes the actual
cyclic A the physical square S(z).

Now W,K are the two actual vertex-origin units
meeting only at O, and the four actual distinct
outer units are S(u),S(v),S(w),A=S(z). Their four
side rays are distinct, since a common ray would
give W,K a nontrivial common segment. The complete
physical point-contact capacity in Section 2 allows
at most two additional units, for total at most eight.
It does not require A to be a genuine leaf. This
excludes the last farthest-fork case.

All possible outside forks at the critical radius
are now excluded.

## 7. Critical forests without outside forks

The remaining forest is a union of simple pendant
paths. They have length at most three by Section 2.
A length-three path A--U--V--L is impossible at
d=1 by an exact physical P skeleton.

Indeed U,V both contain O. A D or diagonal S root
V would contain O openly and overlap U. Thus V is
S/side with real UV point O and real leaf point e.
The true unloaded U transmits in the same direction,
so its other actual application is -w e, with
w in {1,sqrt(2)}. Its cyclic neighbor A lies beyond
the radial support of height w. The sharp bound
w<=d=1 forces w=1 and makes A the physical S(-e).
The unchanged U,V are the two aligned intervening
unit squares with arbitrary transverse sliders
containing zero. Together with the actual L=S(e)
and A=S(-e), they meet the full P_ALL_COMPLETION.md
hypotheses, including both slider endpoints. All
other original units remain, so nine is impossible.

Every remaining path has length one or two. Let a
be the number of length-two arms and l the number
of genuine direct leaves at cyclic roots. Then

    2a+l=5,       I=a,       I+q<=3.                 (7)

The complete possibilities are as follows.

### 7.1. Two short arms and one direct leaf

Here a=2,l=1. The true arm transmitters U,V and the
cyclic direct-leaf root C already give three distinct
origin-containing units. Each arm is S/side: any
D or diagonal S root would contain O openly and
overlap another near unit. Its actual inward port
is O, so each cyclic parent A,B also contains O.
The four-near capacity forces A=B=C. But then that
one cyclic body has two arms and a direct leaf,
contradicting its two-branch bound.

### 7.2. One short arm and three direct leaves

Here a=1,l=3. By (7) and the two-branch bound,
the three direct leaves have exactly two cyclic
roots: two at Q and one at C. Let U be the actual
arm transmitter and P its cyclic parent. The
three units U,Q,C contain O. The arm is again
S/side with inward point O, so P also contains O.
The four-near capacity forces P to equal Q or C.
P=Q would give three attached branches at Q, so
P=C.

The double-leaf root Q has O as a vertex, since
an interior origin would overlap U. Both its
actual leaves are S on its two own side rays.
C also has O on its boundary and its direct
leaf is S. If C has an origin-side interior,
its sole norm-one radial support is the side
foot opposite the actual arm normal e. Thus
the actual U leaf S(e), the actual C leaf
S(-e), and the aligned intervening C,U are a
full physical P skeleton. Its capacity is eight.

Suppose instead C has O as a vertex. If U is
also a vertex-origin unit, Q,C,U contradict
the three-vertex capacity. Otherwise U has
an origin-side interior. Its half-plane and
the Q,C right-angle sectors exactly fill a
turn. Q,C therefore partition the opposite
half-plane into two aligned quadrants. One
of Q's two actual S leaves points opposite
the genuine leaf direction e of U. Q,U
are aligned intervening units, with Q's
transverse slider at an allowed endpoint.
They and S(e),S(-e) again form the actual
P skeleton. This completes every endpoint.

### 7.3. Five direct leaves

Here a=0,l=5. The two-branch bound and q<=3
force exactly three cyclic leaf roots with
multiplicities 2,2,1. Let the double roots
be Q_1,Q_2 and the single root C. They all
contain O. Both double roots have O as a
vertex and have actual S leaves on both
own side rays; an interior origin would
overlap another root.

If C has O as a vertex, the three-vertex
capacity excludes the nine units. If it
has O in a side interior, its half-plane
and the two right-angle sectors must fill
the whole turn. Q_1,Q_2 are then adjacent
aligned quadrants sharing one side ray.
Both genuine double roots would have the
same physical radial S leaf on that ray,
contrary to the distinct original leaves.
An interior origin in C already overlaps
either double root. All alternatives are
therefore excluded.

Equations (7) and Sections 7.1--7.3 exhaust
the critical forest after the proved fork
and length-three-path exclusions.

## 8. Exact whole-cell consequence and unchanged scope

The d<1, d>1 and d=1 proofs cover every
original leaf type, outside degree, branch
shape, transmitter width and actual mean
of a single cyclic block with five bridge
blocks. The finite counting uses the true
original trees and the selected branch
bound; it never erases a bridge to fit an
earlier exact graph theorem.

Every physical capacity result is applied
only after its original squares are
identified. In particular a cyclic body
is used as a radial S square only when
the sharp actual half-plane equality
forces that occupied geometry; no leaf
force or degree-one equation is assigned
to it. All private circle systems and
all cyclic-block forces remain.

For an actual four-body cyclic block,
this proves the entire original coarse
cell C1.4.b5, including every C4, diamond
and K4-type original possibility without
relying on a smaller-type deletion. The
common compatible selected-pose and
minimum-support hypotheses, and the
accepted small-core scope if that version
of the all-bridge load exclusion is used,
remain in force. All nine original units
are retained.

No numerical pose, Lean compilation, CI,
normal reselection, coefficient packet,
remote action or shared-ledger mutation
is used. Its complete source and exact
coarse-cell implication have their full
root and separate independent reviews.

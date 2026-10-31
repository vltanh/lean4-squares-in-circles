# A uniform marked-cycle angular budget: body count plus long-run count is at most eight

Date: October 30, 2026 UTC.

**Status: complete proposed hand theorem and broad cycle reductions,
awaiting independent review. No original graph, ledger or roadmap flag
is changed here.**

The theorem uses actual square support geometry and a compatible
physical cycle embedding. Translational force balance supplies its
common-normal runs in the stress caller. No torque equation, loaded
concurrence, convex force polygon, or change of stress selection is
used. Marked endpoint bodies can have additional positive chords or
attachments, all retained in their full true degrees.

## 1. Geometric statement and full-force caller

Work with actual interior-disjoint unit squares in a disk centered at O,
with radius

    79/40 <= R <= sqrt(Q), Q=1105/256.

Let C be a simple cycle of m distinct actual bodies in one physical
contact graph. Assume this graph has a **compatible physical embedding**:
its edges are routed from the actual body centers through actual contact
points, with arbitrarily small noncrossing changes in contact-junction
disks and center-to-contact tubes that respect the geometric order of
the incident square sectors. This is stronger than abstract planarity.
It is the construction in `PLANAR_STRESS_CORE.md`, Lemma 4.1, and in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Section 5.

Mark at least two vertices of C. Every marked body physically touches
the containing circle. For each marked-to-marked run in cycle order,
assume there is one signed unit direction supporting all its successive
actual contacts from the earlier body toward the later body. A direct
edge has no unmarked internal body and automatically has such a normal.

Let k_j count runs with exactly j unmarked internal bodies. The theorem
will first show that j can only be 0,1,2. A run with two internal bodies
is called a long run; write ell=k_2.

**Theorem 1 (marked-cycle angular budget).** Under these geometric
hypotheses,

    m+ell <=8.                                            (1)

In particular:

- No such cycle has nine or more bodies.
- An eight-body such cycle has no long run.
- A seven-body such cycle has at most one long run.

The same packing may contain any additional actual squares. All their
physical restrictions remain; the theorem does not move or discard any
body, contact, circle corner, or actual application mean.

**Full-force caller.** In a retained physical contact/circle stress,
suppose each unmarked cycle vertex is unloaded and has true positive
degree two in the whole retained graph. Then its two actual contact
forces are equal and opposite. The common supporting normal therefore
propagates through the entire run, supplying the geometric premise.
The marked vertices may have arbitrary true degrees, extra positive
chords or attachments, and arbitrary circle weights including zero.
Their physical circle contact is the only endpoint condition used in
the geometric proof.

This is a single-certificate statement. Degrees, circle loads, normals,
contact points and the compatible embedding all refer to that same
actual retained graph. A merely degree-two vertex of the displayed
cycle cannot replace a genuinely unloaded true-degree-two body.

## 2. Center bounds and exact supported-run gaps

Put M=91/60. For every actual contained square with center c and side
axes u,v, its farthest actual corner has squared norm

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Since

    M^2+M+1/2-Q=31/57600>0,

we have

    |c|<M.                                                (2)

Distinct actual square centers have distance at least one, by the
disjoint open incircles of radius 1/2.

For a run from marked A to marked B with common signed normal n, let
h_S(n) be the actual support halfwidth of a body S. Every unit has
h_S(n)>=1/2. Tight actual support contacts telescope to

    n.(c_B-c_A)=h_A(n)+h_B(n)
                 +sum_(unmarked S in the run) 2*h_S(n).
                                                               (3)

Thus a run with j internal bodies gives

    |c_B-c_A|>=j+1.                                      (4)

If j>=3, this contradicts the center diameter 2M<4. Hence every run
has j in {0,1,2}, and counting its initial marked body and its internal
bodies gives

    m=k_0+2*k_1+3*k_2.                                  (5)

Equation (3) uses only actual support widths. A one-body transmitter
may have arbitrary orientation; no width in {1,sqrt(2)} is assumed.
The actual contact applications need not be collinear. Additional
forces at the marked endpoints have not been omitted from any balance.

## 3. The physical embedding gives the actual marked-center order

### 3.1 Boundary centers have angular separation greater than forty degrees

The complete geometric lemma `CENTERED_INNER_ARC.md` applies on the
whole radius interval here. Every physical circle-touching unit
contains, in its open interior, the entire closed radius-5/4 arc whose
angular interval is centered on its center direction and has halfwidth
pi/9. Two such intervals cannot overlap, since their shared point would
belong to both open square interiors.

Consequently every two distinct marked center directions have minor
angular separation strictly greater than

    2*pi/9 = 40 degrees.                                 (6)

This is a physical boundary statement, so it includes a marked square
with zero selected circle load or a zero-weight physical circle corner.
The cited source proves the whole closed-arc inclusion, rather than
only two angular endpoint inequalities.

### 3.2 Disjoint actual square arcs preserve center order to circle-corner order

A point of the containing circle belongs to at most one physical unit.
One short proof is to use the two orthonormal inward side directions
u,v at a circle corner z. Containment of z+u and z+v gives
z.u,z.v<=-1/2. Hence z-epsilon*z lies in the open square for all
sufficiently small epsilon>0. If two squares shared z, those nearby
radial points would lie in both open interiors, a contradiction.

Choose one actual circle corner z_i on each marked body, and put

    rho=5/4, n_i=c_i/|c_i|, P_i=rho*n_i.

Section 3.1 puts P_i in its actual square's open interior. A physical
boundary center has radius

    r_i>=R-1/sqrt(2)>5/4=rho,                            (7)

where R>=79/40 and 1/sqrt(2)<29/40. Since every circle corner is a
farthest actual corner of its square, its radial projection is

    z_i.n_i=r_i+(|c_i.u_i|+|c_i.v_i|)/(2*r_i)
           >=r_i+1/2>7/4>rho.                          (8)

The segment P_i to z_i lies in that actual square, and except at z_i
lies in its open interior. Every point of the segment after P_i has
projection on n_i strictly greater than rho, hence norm greater than
rho. Every point before z_i has norm strictly below R by strict
convexity of the disk. Thus this is a proper arc of the annulus between
the radius-rho circle and the containing circle. These arcs are pairwise
disjoint, by physical interior disjointness and unique ownership of
their outer circle endpoints.

Use the elementary annular-order fact: disjoint arcs joining marked
points of a Jordan curve to an enclosing circle preserve their cyclic
order, up to reversing both orientations. To verify it, cut the annulus
along one arc. The remaining arcs in the resulting disk connect two
boundary intervals; reversed endpoint orders would force an intersection
by Jordan separation. Closing the cut recovers the cyclic assertion.

Apply this fact first to the two concentric circles and the actual
segments P_i to z_i. The center directions are exactly the directions
of P_i, so the chosen physical circle corners have the same cyclic
order as the marked centers. No corner-angle estimate is needed.

### 3.3 The actual spokes can be retained in the compatible embedding

For each marked body, join its center to the chosen actual circle
corner. The open segment lies in that original square's open interior.
These spokes are pairwise disjoint. Each meets the initial
center-to-contact drawing only at its own body center: two distinct
rays from that center cannot cross, and an actual contact point on
the same ray would have to be the same boundary point, which is
impossible at the uniquely owned circle corner.

All actual contact junctions lie strictly inside the containing disk.
Choose the finitely many local junction disks and strand tubes small
enough to avoid the spokes. Near each marked center, the spoke has a
direction distinct from the incident contact rays, so those rays can
be separated without using its angular sector. The compatible full
graph embedding can therefore preserve all the marked circle spokes.
Extra positive edges at marked bodies remain in that embedding.

The selected simple cycle is a Jordan curve Gamma strictly inside the
containing circle. Each marked spoke meets Gamma only at its own center
and reaches the containing circle. Its open part must lie in the
exterior of Gamma: it cannot pass from the bounded to the unbounded
component without crossing Gamma.

Apply the same annular-order fact to these exterior spokes. It follows
from this application and Section 3.2 that the marked body order
along C is their actual center angular order, up to reversal. Orient
C to agree with that circular order, and let gamma_i be the successive
positive center angular gaps. Then

    sum_i gamma_i=2*pi.                                  (9)

Each gamma_i is at least the minor angular separation of its two
endpoint centers. It need not itself be a minor angle. No assertion
that the origin lies inside Gamma or a force polygon is required.
The case of two marks has the same conclusion with the two complementary
angular gaps; each is at least their common minor angle.

## 4. Two support-gap estimates: eighty degrees and one hundred sixty degrees

The following elementary estimates use only the center bound (2).

### 4.1 A one-body run has endpoint minor angle greater than eighty degrees

First,

    cos(4*pi/9)=sin(pi/18)>1/6.                         (10)

Indeed sin(pi/18) lies in (0,1/2), where 3*s-4*s^3 is strictly
increasing; its value at the actual sine is sin(pi/6)=1/2,
whereas its value at 1/6 is 13/27<1/2.

Suppose two centers of radial distances r,s<M had minor angle
theta<=4*pi/9. By (10),

    |c_B-c_A|^2
      =r^2+s^2-2*r*s*cos(theta)
      <r^2+s^2-(1/3)*r*s
      <=(5/3)*M^2
      =41405/10800 <4.                                 (11)

For the non-strict intermediate maximum, the quadratic is convex in
each variable separately on [0,M]^2. Its maximum is at a rectangle
corner, where its values are 0,M^2,M^2,(5/3)*M^2. The exact reserve
in the last comparison is 359/2160.

A run with one internal body has endpoint distance at least two by
(4), contradicting (11). Thus its minor endpoint angle, and hence
its actual consecutive marked gap, exceeds

    4*pi/9 =80 degrees.                                 (12)

### 4.2 A two-body run has endpoint minor angle greater than one hundred sixty degrees

The exact comparison

    cos(pi/9)<19/20                                     (13)

follows because 4*x^3-3*x is strictly increasing for x>1/2,
its value at cos(pi/9) is 1/2, and its value at 19/20 is
1159/2000>1/2.

If theta<=8*pi/9, then
cos(theta)>=-cos(pi/9)>-19/20. Therefore

    |c_B-c_A|^2
      <r^2+s^2+(19/10)*r*s
      <(39/10)*M^2
      =107653/12000<9.                                 (14)

The exact reserve is 347/12000. A two-body run has endpoint distance
at least three by (4), so its minor endpoint angle and its actual
consecutive marked gap exceed

    8*pi/9 =160 degrees.                                (15)

The estimates include every actual endpoint orientation, all possible
circle masks, and all actual contact means. They are consequences of
the support gaps, not approximations to a presumed force polygon.

## 5. One angular sum proves the whole family

For a run with zero, one, or two unmarked internal bodies, Sections
3--4 give respectively

    gamma_i > (2*pi/9), (4*pi/9), or (8*pi/9).

Summing these strict inequalities and using (5),(9),

    2*pi > (2*pi/9)*(k_0+2*k_1+4*k_2)
         = (2*pi/9)*(m+k_2).

Thus m+k_2<9. Both terms are integers, proving

    m+ell=m+k_2<=8.

This proves Theorem 1 simultaneously for every number of marked
boundary bodies and every cyclic placement of its allowable runs.
No mask table or separate nine-cycle polynomial is needed.

## 6. Complete simple-component corollary and broader branch consequences

### 6.1 Every compatible simple positive component has at most eight bodies

Take one retained physical translational stress with the compatible
embedding above. Suppose an entire positive component is a simple cycle.
Mark its positive-circle-weight bodies. All other cycle bodies are
genuinely unloaded and have full true positive degree two, so the
common-normal premise holds.

For completeness, a positive component has at least two distinct
positive-circle-weight bodies. Dot each body force equation with its
center and sum over the component. Actual tight contact support gives

    2*sum_(circle atoms) lambda*c.z
       =sum_(positive pairs i,j) mu*(h_i(n)+h_j(n))>0.

Thus some circle atom has positive weight. Summing the force equations
without center factors gives sum lambda*z=0. This cannot be supported
on only one boundary body: its center c has radius

    |c|>=R-1/sqrt(2)>5/4>1/sqrt(2),

and each of its corners z satisfies c.z>=|c|*(|c|-1/sqrt(2))>0.
Taking the dot product with c would contradict sum lambda*z=0.
There are therefore at least two marked bodies, as required.

Theorem 1 applies and gives the complete conclusion:

**Every such entire simple positive-cycle component has m<=8. If m=8,
none of its load-to-load runs has two unloaded internal bodies.**

In particular all nine-body simple positive cycles are excluded,
simultaneously over every load count, load mask, physical circle mask,
actual normal choice and actual application mean within this compatible
single-certificate scope.

### 6.2 Chords and attachments at marked boundary bodies are permitted

Theorem 1 did not require the whole positive component to be the cycle.
It also excludes a nine-body cycle in a larger or chorded positive graph
whenever its unmarked bodies are genuinely unloaded of full degree two
and its marked bodies physically touch the circle. All extra positive
edges at marked bodies are retained. These endpoint degrees never enter
the support or angle arguments.

One useful equivalent application is to mark every physical boundary
vertex on a displayed positive cycle. If every remaining circle-clear
cycle vertex has full true positive degree two, Theorem 1 applies.
There cannot be zero or one marks in this application: following the
opposite forces through a whole unloaded cycle, or through its one
mark-to-itself run, would telescope strictly positive support gaps to
zero center displacement. Thus its marked set has at least two members.

Consequently, in this compatible physical scope, every nine-body cycle
must contain a circle-clear body with an additional positive edge beyond
its two cycle edges. This identifies an explicit surviving branch
obligation rather than treating all chorded nine-body blocks as simple
cycles.

### 6.3 Four-load callers and the retained smaller frontier

For an eight-body simple cycle with four positive-circle-load bodies,
the run counts sum to four. Theorem 1 excludes every placement of the
families (2,2,0,0) and (2,1,1,0). The only remaining four-load count
family on eight bodies is (1,1,1,1).

Every nine-body four-load cycle is excluded, including both
(2,2,1,0) and (2,1,1,1). This is a special case of the all-load-count
nine-cycle theorem, not an additional independent closure.

The seven-body record orbit with cyclic counts (2,0,1,0) satisfies
m+ell=8 and is retained. The theorem does not exclude all eight-body
cycles, all seven-body blocks, or all chorded nine-body blocks. It adds
no automatic original coarse-row credit.

## 7. Selection and verification boundary

The proof can be used directly on a single certificate furnished by
`PLANAR_STRESS_CORE.md`: its actual tight normals, translational
balances, circle weights and compatible physical contact drawing are
joint. It also applies to a selected physical force-and-torque
certificate with the compatible drawing of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`. These are alternative inputs;
they are not asserted to be the same selection.

In either case, the full true degrees and unloaded predicates must be
read after the chosen selection, uncrossing and any thinning. An old
degree pattern cannot be transferred to a new stress without a caller
proof. The angular budget itself uses neither angular stationarity
nor any unproved joint force-polygon domain.

All displayed numerical comparisons are exact rational or elementary
trigonometric inequalities. The cyclic-order proof uses actual
spoke-preserving routing and Jordan separation. No Lean compilation,
CI, numerical pose search, new finite computational certificate,
original ledger mutation or remote write is claimed here.

### Operative source scope

- `CENTERED_INNER_ARC.md`: the complete physical closed-arc theorem and
  its strict forty-degree center separation, on the full radius window.
- `PLANAR_STRESS_CORE.md`, Sections 4--5, or
  `PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Sections 5--6: an alternative
  compatible physical drawing for a caller's same chosen graph.

| Source | SHA256 |
| --- | --- |
| `CENTERED_INNER_ARC.md` | `fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5` |
| `PLANAR_STRESS_CORE.md` (alternative drawing input) | `0cbdd5d2c6236e0a1407776963f71d64df4b822d20380a91cc1eabb14f2bbf26` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` (alternative drawing input) | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |

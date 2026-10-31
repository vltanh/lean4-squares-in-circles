# Two distinct long-channel endpoint pairs force physical capacity eight

Date: October 30, 2026 UTC.

**Status: complete proposed hand theorem and family reductions, awaiting
independent review. No original closure, graph, ledger or roadmap flag is
changed here.**

The principal theorem uses actual support contacts. Translational force
balance supplies its common-normal path premise in the stress corollary.
Every actual square, including an unstressed ninth square, is retained.
Torque equations, a plane body graph and a new stress selection are
unnecessary.

## 1. Statement and exact scope

Let a finite family of actual unit squares have pairwise disjoint open
interiors and lie in a disk centered at O with squared radius at most

    Q=1105/256.

A **common-normal four-square path** consists of four distinct actual
bodies A,U,V,B, with three actual successive contact points and one
signed unit direction d that supports each consecutive pair from its
earlier body toward its later body. Thus every consecutive contact has
the same signed normal d, and its center gap equals the sum of the two
actual support halfwidths in d.

**Theorem 1 (geometric two-path capacity).** If the packing contains two
vertex-disjoint common-normal four-square paths, the entire packing has
at most eight actual squares. This statement requires no stress, force
balance, torque balance or prescribed contact-point weights.

For the graph consequence, retain one physical contact/circle stress on
the same actual packing, with one
positive force, an actual common support normal and an actual contact
application point for each positive body pair. Parallel atoms at a side
contact may be aggregated to their original weighted mean. Translational
force balance holds on every body. A body is **unloaded** when its total
selected circle weight is zero. Its **true positive degree** counts all
its positive body-pair neighbors in this same retained stress. No torque
equation is assumed.

A **long channel** is a path of four distinct bodies

    A -- U -- V -- B

whose two internal bodies U,V are unloaded and have true positive
degree two. Its endpoint pair is the unordered pair {A,B}. The endpoint
degrees, circle weights, physical circle contacts and square orientations
are otherwise unrestricted.

**Corollary 1.1 (physical two-channel capacity).** If two long channels have
different endpoint pairs, the entire actual packing contains at most
eight squares. In particular, in an actual nine-square packing there is
at most one distinct endpoint pair supporting a long channel, even when
the channels belong to different positive components.

Multiple channels with the same endpoint pair are not excluded by this
statement. The result strengthens the existing endpoint matching theorem
to a single possible distinct long pair in the nine-body physical scope.

The result is uniform in the size and shape of the remaining graph. Its
proof first makes two disjoint long channels cross, then identifies the
crossing as their common middle contact. Their four internal squares form
a nearly centered two-by-two block. The completion-capacity theorem for
that block excludes every ninth square, irrespective of its stress.
For the geometric theorem, the common normal and vertex-disjointness
are hypotheses; Sections 2.2 and 2.3 supply the latter for the stress
corollary. All support and geometric arguments below apply to either
scope.

## 2. Center, transmission and endpoint facts

Put

    M=91/60, L=89/60.

For any contained square with center c and orthonormal side axes u,v,
the farthest actual corner has squared norm

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Since

    M^2+M+1/2-Q=31/57600>0,

every actual center satisfies |c|<M. Any two distinct actual centers
have distance at least one, because their open radius-1/2 incircles
have disjoint interiors.

### 2.1 A long channel transmits one common supporting normal

For Theorem 1, take the common supporting normal already given in each
geometric path. For Corollary 1.1, obtain that normal as follows.
Force balance at an unloaded true-degree-two body makes its two positive
forces equal in magnitude and opposite in direction. Propagating this
through U and V gives a signed common unit normal d from A toward B.
Let w_U(d),w_V(d) be their actual support widths, each at least one.
Contact support equalities telescope to

    d.(c_B-c_A)=h_A(d)+h_B(d)+w_U(d)+w_V(d).              (1)

Here h is the actual square support halfwidth, always at least 1/2.
Consequently

    d.(c_B-c_A)>=2+h_A+h_B>=3.                          (2)

Write the three actual application means, in path order, as p_0,p_1,p_2.
In the geometric statement these are the given actual contact points;
no weighted-mean premise is needed.
Because the two incident means lie on opposite support faces of each
internal body,

    d.(p_1-p_0)=w_U(d), d.(p_2-p_1)=w_V(d).             (3)

Only their projections are asserted. The means need not lie on one
force line, and the internal frames need not have d as a side normal.

The endpoint projections and halfwidths obey

    c_A.d < -L, c_B.d > L,
    h_A+h_B < 2M-2=31/30,
    1/2 <= h_A,h_B < 8/15.                              (4)

These conclusions retain the original means, including side endpoints
and any zero-load physical circle contacts. No transverse center
alignment is asserted.

### 2.2 Long-channel endpoints are retained bodies

An endpoint cannot itself be unloaded of true degree two. For example,
suppose A were such a body and let T be its neighbor other than U.
The neighbor cannot be V, since V already has the two distinct true
neighbors U and B. If T differs from B, the path T-A-U-V-B has three
unloaded true-degree-two internal bodies. Its support projection is at
least four, contradicting the center diameter bound 2M<4.

If T=B, the same directed support calculation around the closed path
B-A-U-V-B gives zero center displacement and a strictly positive sum
of contact gaps, also impossible. Thus A is retained: it has a positive
circle weight or true degree different from two. The same holds for B.

This argument is also the reason that an omitted external force cannot
be silently discarded to create a new long channel.

### 2.3 Different long endpoint pairs give eight distinct bodies

By (2), each long pair has center distance at least three. The complete
physical endpoint matching theorem in
`LONG_CHANNEL_ENDPOINT_MATCHING.md` says that one actual square cannot
have two distinct actual partners at center distance at least three.
Different long endpoint pairs therefore have four distinct endpoints.

An endpoint of one channel cannot be an internal body of the other,
because Section 2.2 makes endpoints retained whereas internal bodies
are unloaded of true degree two. If the channels shared an internal
body, its two true neighbors would force the other internal body to
be the same one: its other neighbor is retained and cannot serve as
the second internal body. The two endpoint pairs would then agree.
Thus two channels with different endpoint pairs use eight distinct
actual squares.

## 3. Four endpoint directions alternate, with protected access to a circle

### 3.1 Exact angular separations

Every endpoint of either long pair has radial distance between L and M,
by (4). Let theta be the minor angle between two endpoint-center vectors.

For a long pair, theta>5*pi/6. Indeed, if theta<=5*pi/6, then
cos(theta)>=-sqrt(3)/2>-7/8, and

    |c_B-c_A|^2 < (15/4)*M^2
                 =8281/960 <9,

contrary to (2). The exact reserve in the last comparison is 359/960.

For any two distinct endpoints among the four, theta>pi/6. Otherwise,
using cos(theta)>=sqrt(3)/2>4/5 and their radial coordinates r,s,

    |c_i-c_j|^2
      =(r-s)^2+2*r*s*(1-cos(theta))
      <(M-L)^2+(2/5)*M^2
      =8291/9000 <1,

contrary to actual center separation. The reserve here is 709/9000.

The two pairs alternate in circular order. To prove this explicitly,
suppose they did not. After choosing orientation and labels, their
order would be A,C,D,B, with C,D in one A-to-B arc. Both A-to-B arcs
have length less than 7*pi/6, because the minor A,B separation exceeds
5*pi/6. The gaps A-to-C and D-to-B each exceed pi/6. The intervening
C-to-D gap is therefore less than 5*pi/6, contradicting the long-pair
separation of C,D.

### 3.2 Actual outward rays and their cyclic order

Use the complete force-free lemma
`NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md`.
For the endpoint A of a channel oriented by d, the entire ray

    c_A-t*d, t>=0,

is disjoint from every other actual closed square; similarly the ray
from B in direction +d is protected. This only needs (4), not circle
contact or positive circle weight.

For clarity, the numerical angular control is also explicit. Write an
endpoint center in its outward coordinates as (X,Y). Then

    X>L, |Y|^2<M^2-L^2=1/10, |Y|<1/3,
    |Y|/X <20/89<1/4<tan(pi/12).

Along the outward ray, its polar direction moves monotonically toward
the outward axis and by less than pi/12 from its starting direction.
The four endpoint-center directions are pairwise separated by more
than pi/6. Therefore their whole outward spokes lie in four disjoint
angular neighborhoods, and the circle exits retain the alternating
cyclic order established above.

Take an auxiliary circle centered at O with radius 3. Since sqrt(Q)<3,
every physical square lies strictly inside this circle. Continue each
of the four protected rays up to its unique exit from the auxiliary
circle. They are pairwise disjoint. This choice avoids any additional
premise about which physical square meets the containing circle.

## 4. Actual center-and-mean paths must cross at four squares

For a channel A-U-V-B use the following polygonal route:

    c_A, p_0, c_U, p_1, c_V, p_2, c_B.                   (5)

This route is contained in its four actual squares. Every point other
than one of the three application means lies in the open interior of
one of these squares. This follows because the segment from a square's
center to any boundary point lies in the open square except at that
boundary endpoint.

The route is simple. In direction d, each segment in (5) is strictly
increasing: the endpoint increments are h_A,h_B>0, and the two halves
inside either internal square each have increment half its positive
support width. Append the two outward spokes from Section 3.2. When
traversed from the A-side
circle exit to the B-side circle exit, the entire route is strictly
increasing in d. It is therefore a simple proper arc of the auxiliary
closed disk, with its interior in the open disk.

Make the same construction for the second channel. Two proper disk
arcs whose four boundary endpoints alternate must intersect. One way
to see this is to join the first arc to either boundary arc between
its ends and apply the Jordan curve theorem; the other arc's two
ends lie on opposite sides of the resulting crosscut.

No intersection can involve a protected spoke and a physical part of
the other route, since that spoke misses every other closed square.
The four spokes also miss one another by their disjoint angular
neighborhoods. Hence some intersection point p lies on both polygonal
physical routes (5).

The two routes use eight distinct squares by the geometric premise, or
by Section 2.3 for the stress corollary. The interior of one actual
square cannot meet any other actual closed square: if
it did, interior points of the latter arbitrarily near the intersection
would contradict disjoint open interiors. Consequently p cannot be a
non-mean point of either route. It is an actual application mean of
each channel, and belongs to the four distinct squares incident to
those two contacts.

Four interior-disjoint unit squares containing one point must all have
that point as a vertex. Each contributes a local interior angle at
least pi/2; four of them fill the full angle exactly. Their quadrants
are consecutive, so all four frames agree up to quarter turns and
their union is exactly an aligned two-by-two block centered at p.

The center-and-mean route is essential here. A straight force line can
lie along a square boundary when the means are corners; its arbitrary
intersection need not be the required four-square contact.

## 5. The four-square crossing is both channels' middle contact

First establish a screen for every four-square junction in the whole
physical packing, regardless of stress. In the common frame of its
two-by-two block, write the junction as p=(p_x,p_y). A farthest corner
of that block has squared norm

    |p|^2+2+2*(|p_x|+|p_y|) >= |p|^2+2+2*|p|.

If |p|>=19/20, this would be at least

    1921/400 > Q,
    1921/400-Q=3111/6400>0.

Thus every actual four-square junction has |p|<19/20.

For any long channel, its two outer application means instead satisfy,
using (4),

    p_0.d=c_A.d+h_A < -L+8/15=-19/20,
    p_2.d=c_B.d-h_B >  L-8/15= 19/20.                  (6)

Both have norm greater than 19/20 and cannot be four-square junctions.
The intersection in Section 4 is therefore the middle application p_1
of each channel. Its four incident squares are precisely the four
internal transmitters, not any of the four endpoints.

## 6. The two channel directions force a nearly central junction

Use the common orthonormal side frame of the four internal squares at
the junction. For either channel direction n, its two internal widths
are now equal, since their actual frames agree. Write

    m=|n_x|+|n_y|.

The support identity (1) and center bound give

    1+2*m <= h_A+h_B+2*m <2*M=91/30,
    m<61/60.                                            (7)

### 6.1 Each direction is close to one common side axis

Let a=max(|n_x|,|n_y|), b=min(|n_x|,|n_y|). Then

    a>=b>=0, a^2+b^2=1, a+b=m<61/60.

Since b<=1/sqrt(2)<4/5, squaring gives

    a>=1-b/2,

because 1-b^2-(1-b/2)^2=b*(1-5*b/4)>=0. Hence

    1+b/2<=a+b<61/60,
    b<1/30,
    a=sqrt(1-b^2)>899/900.                              (8)

The last bound uses 1-b^2>899/900 and sqrt(t)>=t for 0<=t<=1.
There is a unique nearer side axis, since a>b.

### 6.2 The two directions are close to different side axes

Suppose instead that both directions were close to the same common
side axis f. Reverse each channel as needed so that n.f=a>0, and use
its positive-side endpoint center c. By (4),

    c.n>L, |c|<M,
    |c.n_perp|<sqrt(M^2-L^2)<1/3.

Changing from the n frame to the common side frame and applying (8)
therefore gives

    c.f>=a*(c.n)-b*|c.n_perp|>a*L-b/3
       >(899/900)*(89/60)-(1/30)*(1/3)
       =79411/54000 >22/15.                            (9)

The reserve in the last inequality is 211/54000. The two endpoints are
distinct by vertex-disjointness. But any two centers in the same cap
c.f>22/15, |c|<M have squared distance less than

    (M-22/15)^2+4*(M^2-(22/15)^2)
      =719/1200<1,                                    (10)

contradicting actual center separation. Thus one channel direction is
close to each of the two common side axes.

### 6.3 Their support projections locate the actual junction

Let p be the shared middle contact, and consider either channel with
normal n and common internal width m. Equation (3) and endpoint
support give

    c_A.n=p.n-m-h_A,
    c_B.n=p.n+m+h_B.                                   (11)

Since m>=1 and h_A,h_B>=1/2, the strict center bound implies

    -1/60=-M+3/2 < p.n < M-3/2=1/60.                   (12)

Put P=max(|p_x|,|p_y|) in the common side frame. If P=0 the desired
bound is immediate. Otherwise choose the channel whose normal is
close to the coordinate axis where the maximum occurs. Equations
(8),(12) yield

    1/60>|p.n| >= (a-b)*P > (869/900)*P.

Consequently

    |p_x|,|p_y| <= P <15/869<1/30.                      (13)

Apply the force-free theorem
`FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_WITH_ONE_FIFTEENTH_MARGIN_2026_10_30.md`,
Section 4, with own-frame coordinate threshold 1/30. Such a block
permits at most four other actual unit squares, with arbitrary
orientations. Its proof uses the block's radius-1/2 center exclusion
and places every additional center in one of four caps, each of center
diameter less than one. The total packing therefore has at most eight
actual squares. This proves Theorem 1 and Corollary 1.1.

This last step is a completion argument on the entire original packing.
It does not discard a ninth square because it is unloaded, unstressed,
outside the chosen positive component, or absent from the eight-body
crossing configuration.

## 7. Separate selected-plane alternative, with its exact extra premise

There is also a graph-selection version that does not need a ninth
body. It must use a compatible physical embedding, not abstract
planarity of the body graph.

Assume that the retained physical body graph admits the following
specific embedding construction: start with the actual center-to-mean
strands, then choose arbitrarily small disks about contact junctions
and tubes along those strands; within them route the selected edges
without crossings, respecting the geometric cyclic order of the
incident square sectors. This is exactly the local construction of
Section 5 of `PHYSICAL_BODY_GRAPH_UNCROSSING.md`, after its physical
uncrossing selection has removed simultaneous opposite pairs.

**Theorem 2 (compatible plane selection).** Under this additional
embedding premise, the retained stress has at most one distinct long
endpoint pair, regardless of the number of actual squares.

To prove it, suppose two such pairs existed. Sections 2 and 3 give
eight distinct bodies and four pairwise disjoint protected spokes with
alternating circle exits. Each protected spoke misses the unperturbed
physical drawing except at its own endpoint center. Indeed it misses
all other physical squares; inside its own square, distinct rays from
the center meet only at that center. No actual application mean can
lie on the protected ray, since such a mean also belongs to a second
square.

Choose the finitely many junction disks small enough to avoid the
spokes. Choose the center-to-mean tubes to avoid the spokes away from
their endpoint centers. Near an endpoint center, the protected ray
has a direction different from every incident strand, so the strand
routings can stay in their other angular sectors. The two selected
graph paths can consequently be drawn disjointly while preserving
all four spokes. They lie inside the auxiliary radius-3 disk, and
their spoke extensions give disjoint proper arcs with alternating
boundary endpoints. The crosscut theorem in Section 4 contradicts
this. Theorem 2 follows.

Theorem 1 is independent of this additional selection premise. A
caller using Theorem 2 must name the particular physical selected
certificate and verify that all other needed hypotheses hold on
that same selection. Neither theorem identifies an older merely
translational planar certificate with a torque-balanced certificate,
and neither resolves the remaining common-selection audit by itself.

## 8. Simultaneous consequences for simple four-load cycles

Suppose a full positive component is a simple cycle with exactly four
circle-loaded vertices. List its four load-to-load runs in cyclic
order, and let k_i count the unloaded internal bodies in each run.
These bodies have true positive degree two in the whole retained
stress. The transmission bound gives k_i in {0,1,2}.

Every run with k_i=2 is a long channel. Different runs have different
endpoint pairs. Corollary 1.1 therefore gives, in an actual nine-body
packing,

    at most one of the four counts k_i can equal 2.       (14)

This closes all physical four-load cycle realizations containing two
long runs, simultaneously over their load masks, endpoint degrees,
actual means and any remaining physical squares. In particular:

- On an eight-body four-load cycle, the full run family (2,2,0,0),
  with every cyclic placement, is excluded. The placements in which
  the two long runs share a loaded endpoint were already excluded
  by endpoint matching; the present theorem also excludes the
  disjoint-endpoint placements.
- On a nine-body four-load cycle, the full run family (2,2,1,0),
  with every cyclic placement, is excluded by the same argument.

The entire four-load cycle frontier is not closed. Among eight-body
cycles the count families (2,1,1,0) and (1,1,1,1) remain beyond this
theorem; among nine-body cycles, (2,1,1,1) remains. The seven-body
record orbit with cyclic counts (2,0,1,0) has only one long run and
is preserved.

The principal graph-size-independent conclusion is the stronger
global version of this run bound: in an actual nine-square physical
force-balanced stress there can be only one distinct long endpoint
pair anywhere in the full graph, across all blocks and components.
No particular coarse-row identifier is automatically credited by this
manuscript.

## 9. Sharpness and verification boundary

An actual ninth square is essential when using Theorem 1 as an exclusion.
Eight axis-aligned squares with four centers (+-1/2,+-1/2) and four centers
(+-3/2,0),(0,+-3/2) fit in squared radius 17/4. Two disjoint width-one
channels can pass through the common junction of the central four
squares. Their two opposite middle pairs cross at that junction; an
arbitrary physical stress need not have the compatible body embedding
required by Theorem 2. The capacity theorem allows these eight bodies.

All of Theorem 1 uses only actual support contacts, and force balance
supplies those common supporting normals for the stress corollary.
The theorem permits continuously tilted internal squares. Their
frame agreement is proved only at the actual four-square junction,
and the quantitative argument in Section 6 then locates that junction.
No discrete width classification or torque equation is inserted into
a translational caller.

The exact rational comparisons displayed above were checked directly
with rational arithmetic. The topological argument, physical incidence
classification, and completion proof are hand arguments. No Lean
compilation, CI run, numerical pose search, new finite certificate,
original ledger mutation, or remote publication is asserted here.

### Frozen dependency pins

The literal source versions used for this assembly are:

| Source | SHA256 |
| --- | --- |
| `LONG_CHANNEL_ENDPOINT_MATCHING.md` (Corollary 1.1 only) | `38fa41694cc24fcbe7ac13bc64481323117bcf9d283832a9ec95049cc265cf59` |
| `NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md` | `82ff38f0d73045652c517a10f70f86d93bc0d55d540f3b67c99b04896cc049de` |
| `FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_WITH_ONE_FIFTEENTH_MARGIN_2026_10_30.md` | `df237a44886f100d3fa901981c6c747b0dfa827d61ef4c1f046b476df1c1ada4` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` (Theorem 2 only) | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |

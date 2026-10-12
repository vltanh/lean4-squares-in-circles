# A connected actual-contact representative exists below radius two

## Theorem: a global normalization without a contact-pattern hypothesis

Let N>=2 unit squares have pairwise disjoint open interiors and lie in
a closed disk D_R centered at zero with R<2. Assume one square C contains
zero in its open interior. This C is unique, since no other square can
contain zero even in its closed set.

Then the packing may be changed **without increasing R**, and by a finite
sequence of continuous rigid-body component rotations and one optional
translation of the initially isolated central square, so that

1. every square remains inside D_R and interiors remain disjoint;
2. every actual square-square contacting pair in the original packing
   remains an actual contacting pair at the end;
3. the entire **actual-contact graph is connected**.

In fact each stage adds at least one contacting pair and loses none.
Consequently, among radius minimizers of eight unit squares with
R_8<2, **every minimizer maximizing the number of actual contacting
pairs has connected actual-contact graph**. Existence of such a maximizer
follows from compactness of the minimizing packing set and the fact that
the contact count belongs to {0,...,28}.

There is no premise about a candidate ring, separator choices,
orientations, physical stresses, or whether any particular exterior
square meets the containing circle.

**Scope warning.** This representative generally differs from the
one *minimizing* actual contacts. The leaf, actual-bridge and actual
degree-two rigidity lemmas proved for the minimum-contact representative
cannot automatically be used on this maximum-contact representative.
Connectedness alone is not the missing sharp R_8>=R_hat inequality.

## 1. Every exterior unit square crosses the unit circle openly

**Radial-band lemma.** Let S be a unit square that omits zero in its
closed set and lies in D_R with R<2. Then S contains points of
norm strictly below one and strictly above one. Therefore the
unit circle Γ_1={x:|x|=1} meets the **open interior** of S in a
nonempty relatively open arc.

**Proof.** Write p for S's center and e,f for its own orthonormal
frame, and put r=|p|. Its closed inradius-1/2 disk is contained
in S. Because zero is not in S, r>1/2. The exact largest vertex
norm formula gives

    max_(x in S)|x|^2
       =r^2+|p dot e|+|p dot f|+1/2
       >=r^2+r+1/2
       >1/4+1/2+1/2=5/4>1.                     (1)

Thus S has an interior point of norm >1, by moving slightly
inward from a farthest vertex.

Since S is compact and omits zero, it has a nearest point
z to zero at positive distance d=|z|. The minimizing property
over the convex square gives

    z dot(x-z)>=0  for every x in S.

This follows by differentiating |z+t(x-z)|^2 at t=0+
along the segment inside S. Put u=z/d. Then

    min_(x in S) u dot x=d.                       (2)

The projection width of a unit square along any unit
direction is |u dot e|+|u dot f|>=1. Therefore (2) yields

    max_(x in S)u dot x >=d+1.

Disk containment bounds every such projection by R<2,
so d+1<=R<2 and hence d<1. Again by approximation
from the interior, S has an interior point of norm <1.

Its open interior is convex and contains points of norms
below and above one. The segment joining these two points
lies in the open interior and crosses Γ_1. An open disk
around the crossing point is contained in int(S), and
its intersection with Γ_1 is a nonempty open circular arc.
This proves the radial-band lemma. QED.

## 2. Rotating a component merges it with another exterior component

The *actual-contact graph* has one vertex for each square
and an edge whenever the corresponding **closed** squares
have a common point.

Let J be any connected component of that graph containing an
exterior square S, meaning S does not contain zero.
Suppose another component K contains another exterior
square T. These are compact disjoint finite unions of squares,
so all pairs across components have positive distances.

Pick points

    z in int(S) intersection Γ_1,
    w in int(T) intersection Γ_1,                       (3)

which exist by section 1. Let φ be an angle with
Rot(φ) z=w. Under the rigid rotation Rot(φ) applied
**simultaneously to every square in J**, the two squares
Rot(φ) S and T would have overlapping open interiors:
the point w is interior to both.

Move the whole component J continuously through angles
from 0 toward φ, leaving all other components fixed.
Rigid rotation about zero preserves the containing disk
exactly, because the disk is rotationally invariant.
All internal contacts and all internal pairwise
nonoverlaps of J are preserved exactly.

At angle zero every cross-component pair is separated
as a **closed-set** pair. At angle φ an overlap with T
would occur. Therefore there is a first angle along the
path when a square of moving J touches a square outside J.
Compactness and continuity make the first-contact time
well defined. At that first time open interiors remain
disjoint: a strict interior overlap would hold for
slightly earlier angles, contrary to first contact.

At least one **new** actual contact has appeared;
none of the existing contacts has been lost. The
number of actual-contact connected components has
decreased by at least one. If a third component is
met earlier than K, this is still a valid merge.

Repeat whenever at least two graph components contain
exterior squares. A finite number of steps suffices,
because there are at most N components and each stage
strictly reduces that number. At termination all exterior
squares belong to a **single** actual-contact component J.

No assumption about the graph's internal cycle structure
was used, and J may contain C or omit it.

## 3. Attach the central square if it remains isolated

There is only one square that is not exterior, namely C.
If the completed component J from section 2 does not contain
C, then C is an **isolated** vertex. We now move C alone
until it has a first contact with any member of J.

First keep its frame fixed and move its center radially
toward zero, from its initial center p_C to t*p_C,
as t decreases from 1 to 0. The farthest squared vertex
norm is exactly

    t^2 |p_C|^2
     +t(|p_C dot e_C|+|p_C dot f_C|)+1/2.            (4)

This is nondecreasing as a function of t>=0;
hence the inward translation never violates disk
containment. C remains the open central square
throughout, because its original local center
coordinates have absolute values below 1/2 and
scaling t can only decrease them.

If C makes a first closed-set contact with another
square along the path, stop: all other squares are
already in J, so the entire graph is now connected,
and no prior contact was broken.

If no contact occurs, C reaches center zero still
isolated. Choose any exterior square T in J, with
center p_T=r*u, r>0 and |u|=1. Disjointness of C
and T's open inscribed radius-1/2 disks implies
r>=1. In fact r>1 because C is still isolated.

The inscribed disk of T lies inside D_R, so
r+1/2<=R and r-1<=R-3/2<1/2.
Move C's center from zero along

    p_C(t)=t*u,       0<=t<=r-1.                    (5)

Every vertex of the moving square has norm at most

    t+1/sqrt(2)
       <=r-1+1/sqrt(2)
       <=R-3/2+1/sqrt(2)<R,                        (6)

so disk containment is preserved. Also t<1/2
keeps zero in the open interior of C regardless
of its frame orientation.

At t=r-1 the two centers are one unit apart, so
their closed inscribed radius-1/2 disks have a
common point, which lies in both **closed** squares.
Thus a contact must occur by that time. Stop at
the first such contact, which preserves all
interior nonoverlap and every old actual contact.
This joins C to J, giving a connected actual graph.

## 4. Optimizing the contact-count representative

The procedure of sections 2--3 applies to any initial
packing with C containing zero and R<2, without any
minimality assumption. It strictly increases the
number of actual-contact pairs whenever the graph
is disconnected.

An attained eight-square radius minimizer exists by
the compactness proof in BALANCED_SEPARATOR_REDUCTION.md.
The analytic central-square theorem in
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md applies to the
radius range of that minimizer, since the exact
construction gives R_8<2. Among all such minimizers
choose one attaining the **largest** integer
number of actual touching pairs; a largest value
exists because that integer belongs to {0,...,28}.

If this packing were disconnected, the procedure
would yield another packing in the **same disk**
with strictly more actual-contact pairs. It
cannot have enclosing radius less than R_8,
by definition of the minimum, so it remains an
optimal-radius packing, contradicting maximality
of the contact count.

Therefore every maximum-contact radius-minimizing
representative has **connected** actual-contact graph.
The proof is exact, includes multiple simultaneous
contacts and arbitrary square orientations, and
requires no selected support-force graph.

## 5. Remaining sharp problem

Connectedness removes global isolated vertices and
independent actual-contact clusters from a
maximum-contact representative. It does **not**
show its graph equals the seven-outer contact ring
with two central spokes, that its central square
has actual degree two, or that its contact axes
produce the five-corner projected inequalities.
The maximum-contact representative may have
additional zero-stress contacts absent from a
minimum-contact representative.

Hence the project still requires a **sharp global
geometric inequality** for all connected
eight-square contact graphs at radius
R<=R_hat, including the candidate's full
seven-outer cycle as an equality case.
This note establishes a useful global normal
form but does not claim R_8>=R_hat.

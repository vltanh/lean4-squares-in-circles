# Four genuine leaves cannot be distributed with at most two at each root

Date: October 27, 2026.

**Status: complete uniform hand physical theorem and original selected-
component corollary, submitted for full root and separate independent
review.** No shared metadata or coarse count is changed.

Keep all nine original physical unit squares, their disjoint open
interiors, and the same compatible selected physical certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,       9/10<d<61/60,
    epsilon=max(d-1,0)<1/60.

Suppose four distinct original bodies are genuine positive leaves.
Their actual roots need not have any prescribed degree, load or
additional neighbor. Assume that no root is the root of more than
two of these four leaves. Every original force, moment, normal,
actual side mean, physical circle mask and individual zero weight
is retained.

**Physical theorem.** This entire situation is impossible.

**Selected-component corollary.** In the minimum-positive-original-
scalar-atom certificate, a connected positive component has at most
three genuine leaves. In particular every attachment of four direct
pendant leaves to a four-body cyclic block is excluded, for every
original root multiplicity, leaf type, load mask and contact owner.
This is the entire four-direct-leaf forest of C1.4.b4; other four-
bridge forests are not closed by this source alone.

The physical theorem is a completion argument. Its only graph use is
the genuine-leaf geometry already available in the common selected
certificate. The corollary additionally uses the exact articulation
branch bound in GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md,
Section 5. No smaller stress is substituted into an original root
equation.

## 1. Actual roots are near the origin, and a double root is central

A genuine radial D leaf has an actual root containing O in its open
interior. A genuine radial S leaf in direction e has its actual
root support point d e. The radial inward unit segment

    [d-1,d] e

belongs to that root. Thus every genuine leaf root contains O when
d<=1 and meets the closed disk D_epsilon when d>1. These statements
include all aligned side means and all strictly exposed vertex
owners. The original genuine leaves themselves stay outside a fixed
positive-radius disk about O, so none is one of these near roots.

We use the purely physical central-disk lemma proved in Section 1
of TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md. For an actual
root U of two distinct genuine leaves it says:

* if d<1, O belongs to int(U);
* if d>1, the closed disk D_epsilon is contained in int(U);
* if d=1, either O belongs to int(U), or O is a vertex of U and
  its two leaves are the two genuine radial S squares in U's own
  outgoing side directions from O.

That source proves these alternatives from the complete D/S radial
support geometry before using any triangle. They do not require a
boundary neighbor, a true root degree, or a root force equation.

Whenever a closed point of another actual square lies in int(U),
the two physical interiors overlap: interior points of the other
unit approach every one of its closed points. We use this basic
closed-point observation also at the exact origin endpoints.

## 2. Four different roots and all noncritical radii

Let q be the number of distinct actual roots of the four leaves.
The multiplicity hypothesis gives q>=2.

If q=4, all four roots meet D_epsilon, including epsilon=0 at and
below d=1. The accepted physical theorem
FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md applies because epsilon<1/60.
It gives at most eight squares in total, contrary to the original
nine. Every other original body is included in that capacity count.

Otherwise q is two or three, so one actual root U has two of the
four leaves. There is a distinct genuine leaf root V. For d<1,
Section 1 gives O in int(U) and O in V, a physical overlap. For
d>1, it gives D_epsilon subset int(U), whereas V meets that same
closed disk, again a physical overlap.

Consequently the only remaining radius and root counts are

    d=1,       R^2=17/4,       q in {2,3}.             (1)

At this radius every root contains O closed. None can contain O
openly, since another root is present. In particular every genuine
leaf is S, and the actual double root U is an origin-vertex unit
with its two radial side-direction leaves.

## 3. Three roots at the critical radius

For completeness we give the full physical join, equivalently the
critical argument of THREE_GENUINE_LEAF_ROOTS_LOW_RADIUS_EXCLUSION.md.
There are three distinct roots containing O on their boundaries.
A unit's inward angular sector at such a point has angle pi/2 if
the point is a vertex, and angle pi if it is in a side interior.
Those three open sectors are disjoint.

If all three roots have O as a vertex, the physical theorem in
THREE_VERTEX_ORIGIN_CAPACITY.md gives total capacity at most eight.
It assumes no stresses or common orientation for the extra units.

Otherwise exactly one root T has O in a relative side interior.
The other two, including the double root U, have O as a vertex.
Their sectors have angles pi, pi/2, pi/2 and therefore exactly
tile the full turn. This forces the two vertex-root frames to be
aligned with T's side through O.

The genuine S direction of a side-interior root at d=1 is its
inward normal from that side. Indeed a tilted S support at d e
would put O in the open interior in the root's two inward own
coordinates; and an aligned root has longitudinal interval [0,1].
Rotate and reflect so that

    T=[-1,0] times [h-1,h],       0<h<1,
    U=[0,1] times [0,1].                              (2)

The actual leaf of T is S(-e_x). Since U is a double root, both
S(e_x) and S(e_y) are actual original leaves. In particular the
four original physical units

    T, U, S(-e_x), S(e_x)

are exactly a P_ALL_COMPLETION.md skeleton. Its left middle slider
is h-1/2 in (-1/2,1/2), and its right slider is the allowed endpoint
1/2. The full closed-slider physical theorem gives total capacity
at most eight. The third root and every remaining original square
are kept as completion bodies. This excludes all q=3 alternatives.

## 4. Two double roots at the critical radius

Now q=2. Both actual roots U,V have exactly two of the four chosen
leaves. By Section 1 they are origin-vertex units, and their four
leaves are the radial S squares in their four outgoing side-ray
directions.

Those four directions are distinct. If two were equal, their
actual radial S squares would be the same occupied unit, contrary
to the four distinct original leaves. The closed tangent cones of
U and V have disjoint interiors. Two such right-angle cones can
share a nonzero ray only along a common boundary ray; the four
distinct boundary directions exclude this. Hence

    U intersect V = {O}.                              (3)

The two complementary angular gaps between their right-angle cones
therefore have positive openings g,h with

    g+h=pi,       0<g<=pi/2<=h<pi,                    (4)

after exchanging the gaps. The six original units U,V and their
four leaves are already physically present.

We now use only the force-free completion argument of
TREE02_POINT_CONTACT_COMPLETION.md, Sections 3--4. Its preceding
Section 2 derives four terminal leaves from a special strict
point-contact certificate; that derivation is not needed here,
because the four distinct genuine leaves are explicit original
hypotheses. No stress edge between U and V is assumed.

Here are all the geometric steps of that application. Every center
has norm at most 3/2 at (1). The vertex-quadrant lemma in
THREE_VERTEX_ORIGIN_CAPACITY.md, Section 2, says that another center
in the closed occupied quadrant of U or V could only be the point
(3/2)e on one of its side rays. Each such point is already the
center of its actual S(e) leaf. Distinct actual centers have
distance at least one, so no additional center occurs there.
Every additional center consequently lies strictly inside one of
the two gaps in (4).

Each gap boundary ray is physically screened from radius zero to
one by an actual central side, and from one to two by its actual
S leaf. The outer-face screen in RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1, excludes every point of an additional square at radial
projection at least two. Corollary P1.2 then puts the entire closed
additional square in the closed gap wedge containing its center.
This is a physical barrier conclusion for the full unit; no
coordinate separating axis or center-only routing is assumed.

The two distinct radial leaves bounding the smaller gap obey the
exact separation bound of that source, Lemma P5.1:

    g>=beta:=2 arctan(1/2),
    h=pi-g<=pi-beta=2 arctan(2).                       (5)

If g<pi/2, its acute screened wedge contains no additional square
by Theorem P3.1, while the other wedge contains at most two by
Theorem P4.1. If g=pi/2, both wedges are right angles and each
contains at most its unique origin-vertex unit by Theorem P3.1.
Thus at most two further physical squares accompany the fixed six
in every continuous angle case, including the exact right-angle
endpoint. The total is at most eight, proving the physical theorem.

## 5. Exact minimum-support component corollary

Now suppose one connected positive component of the original
minimum-atom certificate has at least four genuine leaves. A root
with at least three genuine leaf neighbors cannot be the center
of an isolated three-leaf star, since this component has at least
four leaves. Deleting that root therefore leaves its three leaf
singleton components and at least one further component. Its
number k of articulation branches is at least four.

This contradicts the actual selected-certificate inequality

    k+ell<=3

from GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, Section 5,
where ell is the number of positive circle atoms at that same
root. In fact the genuine root is physically clear, but ell>=0
already suffices. The inequality is on whole branches and is
proved with the original scalar atoms and unchanged surviving
means; we do not replace it by a bound on the root's pair degree.

Consequently every root in this component has at most two genuine
leaf neighbors. Choose any four of its distinct genuine leaves.
They satisfy the physical theorem, which is impossible. This
proves the at-most-three-leaves conclusion for the original
selected component.

For a four-body cyclic block with four direct pendant bridges,
the four outer bodies are precisely four genuine positive leaves.
They lie in the same positive component, regardless of how their
roots repeat on the block. Hence the corollary closes every such
original C1.4.b4 attachment. The proof never assigns the block
vertices a reduced force equation and never discards another
physical unit, physical mask, zero circle weight, or actual mean.

No other four-bridge forest or entire C1.4.b4 coarse cell is claimed
closed here. No Lean compilation or CI is claimed.

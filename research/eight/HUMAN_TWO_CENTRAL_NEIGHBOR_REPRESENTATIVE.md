# Two actual central neighbors can always be arranged at the n=8 radius ceiling

## Theorem: a global two-spoke representative, not a two-force classification

Let eight pairwise interior-disjoint unit squares fit in a
disk D_R centered at zero, where

    sqrt(2) < R,       R^2<=98/25.

By HUMAN_GLOBAL_GEOMETRY_CLOSURE.md there is
exactly one square C containing zero in its
open interior. Keep the **other seven squares
fixed**, and keep C's side-frame orientation
fixed, but allow its center to translate.

**Theorem.** There is a translation of C which
keeps all eight squares inside D_R with
pairwise disjoint open interiors, and for
which C has actual contacts with **at least
two distinct** members of the other seven.

All actual contacts between the fixed seven
squares are unchanged. No extra assumption
on their frames, contact graph, stress,
winding cycle, or candidate pattern is used.

If C was initially isolated, the move adds
two or more actual contacts without losing
any existing contact, and any physical stress
supported entirely on the fixed seven
squares remains valid with zero multipliers
assigned to the new contacts.

**Important.** The two central contact normals
are not asserted to be opposite, radial,
or both positively stressed. Thus the theorem
does not imply the minimum-contact
degree-two transmitter theorem, a common
frame, or R_8>=R_hat.

## 1. The exact polygonal center feasibility set

Write the central unit square with center zero
and its original orthonormal frame as S_0.
For a center p it becomes

    C(p)=p+S_0.

Let S_1,...,S_7 be the seven fixed squares.
The circle containment region for p is

    K_R={p : every vertex of C(p) belongs to D_R}.

It is a compact convex intersection of four
closed disks; R>sqrt(2) implies it has a
nonempty interior.

For each j let

    P_j=S_j-S_0={x-y:x in S_j,y in S_0}.             (1)

This is a closed convex polygon, the Minkowski
sum of two unit squares (a parallelogram,
rectangle, or octagon depending on their
relative frames). The *open interiors* of
C(p) and S_j overlap if and only if

    p belongs to int(P_j).                          (2)

For completeness: an overlap of interiors
gives p=x-y with x,y both interior,
so p is in the interior of P_j.
Conversely, the interior of the Minkowski
sum of two full-dimensional convex polygons
is the sum of their interiors; this follows
by moving any decomposition slightly toward
their respective interior points and then
using the convexity of each polygon. Equally,
it follows directly from the separating-axis
description of their difference polygon.

Hence the complete set of allowable central
square center positions, with all seven fixed, is

    F=K_R minus union_(j=1)^7 int(P_j).           (3)

It is closed inside compact K_R, and thus compact.
Its boundary consists of pieces of the polygon
edges of P_j and possibly of the circle
containment boundary of K_R.

## 2. Circle containment can never be the active boundary

Every p in F gives an eight-square packing
in the disk of squared radius <=98/25.
The other seven squares are held fixed and
all omit zero even in their **closed** sets:
the original central square contains zero
in its open interior, and no other closed
square can contain zero without creating
interior overlap.

By the **analytic** central-square theorem,
every packing obtained at p has some unique
square containing zero in its open interior.
None of the fixed S_j can do so, so
necessarily

    0 belongs to int(C(p)),    for every p in F.    (4)

Every vertex z of a unit square containing
zero in its open interior satisfies
|z|<sqrt(2), since all points of that square
are strictly within its diameter sqrt(2)
of the interior point zero. Since R>sqrt(2),

    every vertex of C(p) has norm <R.               (5)

Thus **F is disjoint from the boundary of K_R**.
Because F is compact, it even has positive
distance from that boundary. In particular
every connected component of the interior
of F is a bounded polygonal open region
whose boundary consists solely of pieces
of the seven fixed convex polygon boundaries
partial P_j. No moving-square circle
contact can close off a free-placement
component.

## 3. If central degree is at most one, a free center region exists

If the original C already has at least
two distinct actual neighbors, the theorem
is immediate by taking its original center.

Suppose it has no actual neighbors.
The center has positive separation from
all seven closed squares, and has strict
circle slack by (5). Thus its center lies
in the open interior of F.

Suppose instead it has exactly one actual
neighbor S_j. Choose any valid unit
separating normal n of this touching
pair, directed from S_j toward C.
A small translation of C by epsilon*n
makes that pair **strictly separated**
because its support projection gap
increases by epsilon. Every other pair
C,S_i has positive closed-set distance,
and C has strict circle slack.
For sufficiently small epsilon>0 they
remain separated and contained.

Therefore F has a nonempty open interior
in either case. Fix one of its nonempty
connected open components Omega.
Its closure K=cl(Omega) is compact and
lies strictly inside K_R by section 2.

## 4. A convex-hull corner must touch two forbidden polygons

We use one elementary planar-geometry fact.

**Convex-obstacle corner lemma.** Let
Omega be a nonempty **bounded** connected
open region obtained by removing interiors
of finitely many closed convex polygons
from a planar open domain. Suppose
cl(Omega) stays a positive distance
from the domain boundary. Then some
point z of cl(Omega) belongs to the
boundaries of at least two **different**
removed polygons.

**Hand proof.** The region has a polygonal
boundary, consisting of finitely many line
segments whose support lines come from
the obstacle edges. Its compact convex hull

    H=conv(cl(Omega))

is therefore a nondegenerate convex
polygon. Choose a vertex z of H.
It belongs to cl(Omega) (every extreme
point of a convex hull of a compact
set belongs to the set), and the region
lies locally inside the strict convex
corner of H at z, whose interior angular
aperture is less than pi.

The point z cannot lie away from every
obstacle boundary, since cl(Omega) has
no contact with the domain boundary:
a small open disk around z would then
lie in Omega, contradicting that z
is an extreme vertex of H.

Suppose exactly one obstacle P_j has
z on its boundary. All other obstacles
have positive distance from z, and the
domain boundary has positive distance
too. Shrink a disk B_epsilon(z) to avoid
them. In that disk the available
points are precisely those outside
the **interior** of P_j.

Since P_j is convex, it has a
supporting line through z and is
contained on one side of that line.
The opposite open half-disk is
therefore free of P_j. It is connected
and meets Omega arbitrarily close
to z; the locally available exterior
of one convex polygon is connected
near any edge or vertex. Hence this
entire open half-disk belongs to the
same component Omega.

But an open half-disk centered at z
has directions covering an angular
aperture pi, and cannot lie in the
strict corner of H at z with aperture
less than pi. Contradiction. Therefore
at least **two distinct obstacles**
have z on their boundaries. QED.

Apply the lemma with the domain
int(K_R) and obstacles P_1,...,P_7
of section 1. The required positive
distance from the domain boundary
holds by (5). We obtain p_star in
cl(Omega) subset F belonging to

    partial(P_i) intersect partial(P_j),
        i !=j.                                        (6)

Because p_star belongs to F, the
translated square C(p_star) fits
D_R and overlaps no open square interior.
Since p_star belongs to both
boundaries (6), C(p_star) actually
touches **both distinct** squares
S_i,S_j (the boundary of their
Minkowski difference corresponds
exactly to closed-set contact).
This proves the theorem.

## 5. Application to the eight-square minimizer

The exact five-corner construction gives
R_8<2 and the analytical lower bound
gives R_8>sqrt(2)+1/2>sqrt(2), so
the theorem applies to *every*
eight-square radius minimizer. Holding
its seven exterior squares fixed, we
can select a same-radius representative
in which the central square has
at least **two actual neighbors**.

This can be combined with the
connectedness normalization in
HUMAN_CONNECTED_MAX_CONTACT_REPRESENTATIVE.md,
but the central adjustment may create
additional contacts and is not
necessarily compatible with selecting
the globally **fewest actual contacts**.
In particular it does not show that
the two neighbors are opposite
side contacts or bear equal positive
stress.

The exact sharp-family construction
of ANALYTIC_SHARP_FOUR_CENTRAL_CONTACTS.md
has even four actual central neighbors.
Thus two contacts are a lower-bound
representative normalization, not
an equality classification and
certainly not a claimed global
five-corner structural reduction.

The unrestricted inequality
R_8>=R_hat remains OPEN.


## 6. Joint connected, two-central-spoke, stress-preserving representative

**Corollary (one consistent representative).** For the
attained eight-square radius minimum R_8 there is
a packing P_star of the same radius satisfying
**all three** structural properties:

1. Its full actual-contact graph is **connected**.
2. Its unique central square has actual contacts
   with **at least two distinct** exterior squares.
3. It carries a normalized physical stress whose
   nonzero contact forces, nonzero circle multipliers,
   and original square positions on the
   minimum-actual-contact representative's
   unique nontrivial component J are **unchanged**.

**Proof.** Begin with a radius-minimizing
packing P_min chosen with the fewest actual
contacting pairs. HUMAN_CONTACT_COMPONENTS.md
gives one nontrivial actual component J,
the others isolated; J necessarily contains
an exterior square.

Apply the **core-preserving exterior rotation**
procedure of HUMAN_CONNECTED_MAX_CONTACT_REPRESENTATIVE.md,
section 6. It leaves every member of J
fixed, rotates only components formed by
originally isolated exterior labels, and
attaches all exterior labels into one
connected actual-contact component
containing J.

If the central square C originally belonged
to J, then it already had at least two
actual neighbors: it is strictly inside
the containing circle and the
minimum-contact one-leaf theorem prohibits
central actual degree one. All squares
are now connected and the core has not
moved, so the claim follows.

Otherwise C was originally an isolated
vertex, and remains isolated after the
exterior rotations. Keep all seven
exterior squares in their newly connected
configuration **fixed**. Apply the
two-central-neighbor theorem of sections
1--5 to translate C, with its frame
unchanged, to a feasible location
contacting at least two distinct
members of that exterior component.
The resulting actual graph is connected.

Every originally isolated label,
including C in the second case, had
zero contact and circle multipliers in
the chosen normalized physical stress.
All squares in J have literally
unchanged positions, frames, and
contacting partners, so retaining the
old nonzero multipliers and giving all
new contact pairs weight zero preserves
the force and moment equilibrium
equations and their normalization,
as established in the core-preserving
saturation theorem. This proves
all three properties in one packing. QED.

This joint representative is **not**
asserted to minimize the number of
actual contact pairs. Neither the
new central two contacts nor any
newly attached zero-weight edges may
be inserted into the minimum-contact
opposite-normal rigidity theorem.

The sharp lower-bound problem remains:
even this joint representative does
not yet force the coherent five-corner
separator chain or any alternative
radius obstruction valid for all
possible square orientations.

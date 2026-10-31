# The full five-spoke exterior-hexagon fan has no nine-square completion

Date: October 26, 2026.

**Status: accepted complete whole original graph/load-family theorem
after the full reviews REVIEW_FAN_COMPLETE_ROOT_2026_10_26.md and
REVIEW_CHORDED_HEXAGON_FAN_COMPLETE_GLOBAL_2026_10_26.md.**
This source itself changes no original gate.

Keep the actual selected positive fan

    H B_i (1<=i<=5),
    B_1 B_2, B_2 B_3, B_3 B_4, B_4 B_5.

The complete original exterior-hexagon graph/load cover forces all five
B_i to be positively circle-loaded, and makes H physically circle-clear.
Its true degree is five. B_1,B_5 have true degree two; B_2,B_3,B_4 keep
true degree three. Keep the complete nine-square packing, every original
positive force and common mean, every physical one- or two-circle-corner
mask and every individual zero corner weight.

Work first in

    2<=R<=sqrt(1105)/16.                                 (1)

The already established nine-square radius-two exclusion handles the
lower part of the original radius window 79/40<=R. No new radius-two
certificate is asserted here, and that inherited global premise is not
retired by this source.

**Theorem.** The entire positive fan with its original forced load set
12345 has no nine-square completion. All endpoint owners, all three
internal hub normals and all their actual positive magnitudes are included.

## 1. Complete physical order and whole force equations

Let p_i be the unchanged H--B_i applications, n_i the unchanged unit
normals directed H to B_i, and mu_i>0 their magnitudes. Let F_i be the
complete actual circle resultant on B_i. The full equations give

    sum_i mu_i n_i=0,
    sum_i mu_i det(p_i-c,n_i)=0 for every fixed c,
    sum_i F_i=0.                                        (2)

The second identity uses the full hub force and torque equations;
translation of the moment center does not remove any force. The third
identity sums all six original body equations.

Every nonconsecutive pair B_i,B_j is physically closed-disjoint. An
additional physical contact would close a cycle in the existing physical
boundary path, contrary to the physical boundary path-forest theorem.
In particular B_1 and B_5 are closed-disjoint and p_1!=p_5. At any H
point at most two of the B_i can occur, and if two occur they are
consecutive on the path. Three would already make a physical boundary
triangle. These are physical consequences, not inferences from missing
positive graph edges.

The actual outer face is H,B_1,...,B_5,H. The physical embedding and its
compatible arbitrarily small junction routings put the hub spokes in
this cyclic order. Every internal application lies on one of the two
closed H boundary arcs from p_1 to p_5, the arc followed by the path.
The complementary arc will be called the outer H arc. Coincident
applications at an endpoint are assigned their unchanged physical
sector order.

The actual normals have the same weak angular order. At distinct H
points this is the monotone normal order of a convex square. On an H
side the normal is its axis, and at a vertex it lies in its closed
outward normal quadrant. At a coincident point, the normal directed
into each B_i belongs to that body's inward tangent sector: for a square
vertex this is the quadrant of its two inward side directions; for a
side-interior application it is the inward axis in its tangent
half-plane. The sectors of different physical bodies have disjoint
interiors. Their directions therefore have their same physical order.
The retained strict convention at free point contacts supplies strict
interior directions there; shared-side endpoints retain weak directions.
Thus coincidences cannot reverse the normal order. No normal is chosen
again.

In particular, if the path follows an arc from one H side to a vertex,
all its normal directions lie in that arc's ordered normal interval.
This includes a hub-owned force whose actual mean is an H vertex:
a different sector on the other side of that vertex belongs to the
other boundary arc, and cannot be inserted into this normal interval.

The circle-resultant directions are also in the strict order B_1,...,B_5.
The physical boundary angular-order theorem and the complete pi/12
corner/resultant-to-center bound give this: the relevant open intervals
are disjoint since the boundary center separation is greater than pi/5.
Every F_i is nonzero. Every consecutive resultant gap, including the
closing gap from B_5 to B_1, is strictly less than pi. Otherwise all five
directions lie in one closed semicircle; in the equality case the other
three distinct directions are in its interior. Their positive sum
cannot be zero, contradicting (2).

Finally the true endpoint degree-two theorem gives

    q_i=t_i F_i=p_i+ell_i n_i,
    t_i>0, ell_i>=0,                 i=1,5.              (3)

This is the complete proper-concurrence lemma in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. It covers physical
radial masks and every circle-weight split; q_i need not be inside B_i.
No such equation is imposed on any internal B_i.

## 2. A disk-exclusion lemma for the actual hub pocket

Put r=R-sqrt(2). Every point x of every boundary unit B_i satisfies

    |x|>=r>=2-sqrt(2)>1/4.                              (4)

This follows from its diameter and any one of its actual circle corners.

Here is the geometric lemma used in all remaining owner cases.

**Hub-pocket lemma.** Suppose a nonzero vector v satisfies

    v.x>0 on the whole outer H arc from p_1 to p_5,
    v.F_1>0, v.F_5>0,                                  (5)

and that the same whole outer H arc has distance strictly greater than
1/4 from O. Then every whole unit in the actual exterior pocket through
H has distance strictly greater than 1/4 from O.

### 2.1. An actual occupied Jordan boundary misses the quarter disk

For geometry only, replace a side-contact application p_i by the extreme
a_i of its actual H--B_i intersection facing the outer H arc. Keep p_i
unchanged in every equation. If the intersection is a point, a_i=p_i.
A positive-length intersection lies on its one actual H side, so the
arc from a_1 to a_5 is a subarc of the stated outer arc. The endpoints
remain distinct because B_1,B_5 are physically disjoint.

Choose the actual circle corner z_i of B_i facing the closing circle
gap. Join a_i to z_i by a simple path through the open interior of B_i,
except at its endpoints. Two straight segments through a suitable
interior point suffice. Each such path meets the closed H only at a_i;
the two paths are disjoint because B_1,B_5 are closed-disjoint. Together
with the outer H subarc they form a simple occupied crosscut. Join it
to the corresponding closing circle arc from z_5 to z_1.

This is an actual Jordan boundary. Its H part misses the closed disk
D_(1/4) by hypothesis; its endpoint-body parts do so by (4); and its
circle part does so by (1). No assertion about a concurrence lying in a
physical unit is used for this separation.

The actual hub pocket is the side between this crosscut and the closing
circle arc, in the original outer-face order. All its free components
are confined to this Jordan region. Choosing contact extremes includes
the full original side-contact intervals. Further zero-weight contacts
can subdivide its free parts but cannot enlarge the region through the
occupied crosscut. This is the same occupied-crosscut routing used in
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Sections 3--4.

### 2.2. A separate homotopy computes winding at O

For every x in B_i and every physical circle corner z of B_i,

    z.x >= R^2-R sqrt(2)>0.

Summing the actual nonnegative corner weights gives F_i.x>0 throughout
B_i. Also F_i.q_i=t_i|F_i|^2>0. Consequently each original endpoint
path can be homotoped, avoiding O, to a path through q_i. This remains
valid if q_i is outside B_i: the entire convex hull of B_i and q_i
lies in the strict half-plane F_i.x>0.

Move its circle endpoint z_i along that body's own angular interval to

    z'_i=R F_i/|F_i|.

This interval lies in the same strict F_i half-plane. Its endpoints and
all intervening directions avoid O. The disjoint physical corner/
resultant intervals preserve the original closing-arc lift, so this
deformation introduces no extra turn around the circle. The endpoint
path can now be replaced by a_i--q_i--z'_i within the same half-plane,
and the circle arc deforms continuously with its two endpoints.

The resulting loop consists of the unchanged outer H subarc, the two
paths a_i--q_i--z'_i, and the closing resultant circle arc. All its
points lie in v.x>0. Indeed the H part satisfies (5); q_i and z'_i are
positive multiples of F_i; and every line segment between these
points stays in that half-plane. The closing resultant gap is less
than pi by Section 1. Since both endpoint directions lie in v.x>0,
this is exactly their minor arc in that half-plane. Hence the limiting
loop has winding zero about O, and so does the actual Jordan boundary.

Only this auxiliary winding computation uses a homotopy, and it needs
to avoid O, not the whole quarter disk. The actual Jordan boundary
itself already misses that whole disk by Section 2.1. Winding is
constant on the connected D_(1/4), so its winding is zero everywhere
on the disk. Thus the whole closed quarter disk lies outside the
bounded pocket. The actual compact boundary has a strict distance
margin from D_(1/4); increasing the disk radius slightly preserves
both separation and winding zero. Therefore every unit confined to
the pocket has distance strictly greater than 1/4. This proves the
hub-pocket lemma with all weak contact subdivisions retained.

## 3. One hub-axis endpoint and one oblique endpoint

Reverse the complete path if necessary to make n_1 an H side axis.
Rotate so n_1=N=(0,1), keeping the true circle origin at O=0. Write

    H=[L,L+1] times [h-1,h],
    p_1=(p,h), L<=p<=L+1.

The other actual normal is not an H axis. Its application p_5 is
therefore an H vertex, and its two normal components at that vertex
are strict. Reflect the horizontal coordinate, together with all
physical data, so p_5 is one of the two left vertices.

### 3.1. The actual path takes the long hub arc

If p_5=(L,h), its normal is (-a,b), a,b>0, and p>L because the two
endpoint bodies are disjoint. The short arc from p_1 leftwards to p_5
has only normals with nonnegative y-component; the two endpoint
components are strictly positive. Full hub force balance excludes it.

If p_5=(L,h-1), its normal is (-a,-b), a,b>0. The short arc goes from
p_1 along the top and then down the left side. Its ordered normal
interval is from N through W to this strict southwest normal. Every
x-component is nonpositive and the last is strictly negative. Full
hub force balance again excludes it. Section 1's normal order covers
all possible coincident applications at either endpoint; it does not
silently omit a corner-valued side mean.

Thus in both cases the actual path follows the long clockwise arc,
through the right and bottom sides. Its physical circle path has that
same orientation. The general boundary-contact moment lemma in
`FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Section 1, gives a strictly
negative origin moment for the directed first boundary edge. The true
B_1 torque equation therefore gives

    det(p_1,N)=p<0.                                     (6)

The endpoint concurrences (3) now have strictly negative x-components:

    (q_1)_x=p<0,
    (q_5)_x=L-ell_5 a<0.                               (7)

In particular both actual endpoint resultants lie in the strict left
half-plane. Every point of the outer H arc also has x<=p<0. Thus
(5) holds with v=(-1,0).

### 3.2. The entire outer H arc misses D_(1/4)

For the top-left endpoint, this arc is the horizontal segment from
(p,h) to (L,h). Since L<p<0, its distance from O is minimized at p_1
and is at least r by (4).

For the bottom-left endpoint, the outer arc consists of the top
segment from p_1 to (L,h), followed by the vertical segment to p_5.
The top segment again has norm at least |p_1|>=r.

If zero is outside the vertical interval [h-1,h], the closest point
on the vertical segment is an endpoint. At its top, the norm is at
least |p_1|; at its bottom it is |p_5|. Both are at least r.

Suppose instead 0 belongs to [h-1,h]. If |L|<=1/4, then L<=p<0 gives
|p|<=1/4 too. Both actual boundary-contact radii yield

    h >= sqrt(r^2-1/16)>1/2,
    1-h >= sqrt(r^2-1/16)>1/2,

which is impossible. The strict comparison follows from

    (2-sqrt(2))^2-1/16>1/4:
    sqrt(2)<91/64, since 2*64^2=8192<8281=91^2.

Therefore |L|>1/4 whenever the vertical segment crosses the horizontal
axis. Its whole norm is then greater than 1/4. In every case the whole
outer H arc has a strict quarter-disk margin. The hub-pocket lemma
applies and treats this entire mixed-owner family, including every
physical mask or side-mean value at either endpoint.

## 4. Both endpoint hub normals are oblique

Both actual endpoint applications are H vertices. They are distinct
because B_1,B_5 are physically disjoint. Therefore they are adjacent
vertices or opposite vertices. These are the complete two possibilities;
no metric theorem for a shorter boundary path is imported.

We use one consequence of the full five-load balance. Normalize all
actual positive circle-corner weights to have total one. Their weighted
sum is zero by (2). Every such corner z has distance at most
3/sqrt(2) from c_H: use its actual H contact, the unit-square diameter,
and H's half-diagonal. Hence

    R^2+|c_H|^2=sum_z lambda_z |z-c_H|^2<=9/2,
    |c_H|<=1/sqrt(2).                                  (8)

All five whole-body circle loads are retained in this identity.

### 4.1. Adjacent endpoint vertices

Rotate so these are

    p_1=(x-1/2,h), p_5=(x+1/2,h),
    c_H=(x,h-1/2).

Both endpoint normals have strictly positive y-component. The short
top-side path would put all hub normals in the closed upper half-plane,
with positive endpoint components, contrary to (2). Thus the outer H
arc is exactly this top side, and the actual boundary path goes the
other way around H.

By (8), |x|<=1/sqrt(2)<1. The smaller of |x-1/2|,|x+1/2| is therefore
at most 1/2. Since both actual ports belong to boundary units, (4) gives

    h^2>=r^2-1/4 >= (2-sqrt(2))^2-1/4 > (3/10)^2.       (9)

For the final strict comparison use sqrt(2)<283/200, since
2*200^2=80000<80089=283^2; then
23/4-4sqrt(2)>23/4-283/50=9/100.

The negative sign h<-3/10 is incompatible with (8): it would give
h-1/2<-4/5, whereas 1/sqrt(2)<4/5. Thus h>3/10. The entire outer H
arc is in y>3/10. Equations (3) and the positive endpoint normal
components put both q_1,q_5, and hence both F_1,F_5, in y>0. The
hub-pocket lemma applies with v=(0,1).

### 4.2. Opposite vertices: group coincident hub ports before taking torque

Put sigma=1/sqrt(2), rotate the opposite-vertex chord horizontally,
and reflect vertically if necessary so the actual path follows the
lower H arc. Write

    p_1=(x-sigma,h), p_5=(x+sigma,h), c_H=(x,h).

The other H vertices are (x,h-sigma) and (x,h+sigma). By (8),
|x|<=sigma. Equality would force h=0 and one actual boundary-contact
port to equal O, contradicting (4). Therefore

    X=sigma-x>0, Y=sigma+x>0,
    p_1=(-X,h), p_5=(Y,h).                              (10)

Do not assume that an internal actual application differs from p_1
or p_5. Group all unchanged positive hub forces at p_1 into G_1 and
all such forces at p_5 into G_5. Every other hub application lies on
the intervening lower arc. For each such point P and actual outward
normal n, the elementary diamond-side calculation gives

    det(P-p_1,n)<=0, det(P-p_5,n)>=0.                    (11)

For example the lower-left side has
P=p_1+s(sigma,-sigma), n=(-sigma,-sigma), and the two determinants
are -s and 1-s. The lower-right side gives the same weak signs. At
the bottom vertex its full outward normal cone has n_y<=-|n_x|,
which gives (11). Every actual shared-side mean remains included.

Take the full hub torque about p_5. The p_5 group contributes zero;
the p_1 group contributes -2sigma (G_1)_y; and every other contribution
is nonnegative by (11). Thus (G_1)_y>=0. Torque about p_1 similarly
gives (G_5)_y>=0.

Within the left-vertex group the physical normal order along the lower
arc starts at n_1. On the left vertex's normal interval [3pi/4,5pi/4],
the y-component is decreasing. Hence n_1 has at least the y-component
of every other normal in that group. The positive weighted group sum
having nonnegative y-component implies (n_1)_y>=0. At the right vertex
the interval [7pi/4,9pi/4] has increasing y-component and n_5 is last.
The same argument gives (n_5)_y>=0.

Consequently the two true endpoint normals have the form

    n_1=(-b_1,a_1), n_5=(b_5,a_5),
    b_i>0, 0<=a_i<=b_i.                                (12)

Every force at a coincident endpoint was included in its original group;
no multiplier was split, discarded, or treated as a new endpoint force.

### 4.3. The opposite-vertex outer arc and endpoint rays

The lower H arc goes counterclockwise from p_1 to p_5. The actual
circle path has that orientation as well. Its first boundary-edge
moment is strictly positive. The genuine B_1 torque equation gives

    det(p_1,n_1)=b_1 h-a_1 X>0,

so h>0. Equations (3),(10),(12) put q_1 in the strict upper-left
quadrant and q_5 in the strict upper-right quadrant. Both F_1,F_5
therefore lie in y>0. The entire outer H arc, through the upper
vertex (x,h+sigma), lies in y>=h>0.

Its two sides also have an exact distance margin. The upper-left side
has outward unit normal (-1,1)/sqrt(2) and support

    (X+h)/sqrt(2) >= |p_1|/sqrt(2)
                   >= r/sqrt(2) >= sqrt(2)-1 > 1/4.

The upper-right side gives (Y+h)/sqrt(2) with the same lower bound.
Every point of either side has norm at least its positive support.
Thus the whole outer H arc misses D_(1/4) strictly, and the hub-pocket
lemma applies with v=(0,1). This includes all tip-owned, genuinely
free, physical radial, shared-neighbor and coincident-port cases.

## 5. The remaining both-axis family and the complete original join

If both n_1,n_5 are H side axes, the complete theorem
`CHORDED_HEXAGON_FAN_HUB_OWNED_ENDPOINTS_EXCLUSION.md` applies. Its
internal three hub normals are unrestricted. Its equal and opposite
endpoint-axis cases are fully excluded; its adjacent-axis case puts
the whole actual hub pocket beyond distance 2/5 from O and obtains
the same eight-unit arc contradiction used below. Every corner-valued
endpoint mean and all physical masks are covered there.

If exactly one endpoint normal is an H axis, Section 3 applies. If
neither is, Section 4 applies, with adjacent and opposite H vertices
exhausting the distinct possibilities. This is the complete owner
cover for the original full fan. It changes no original selected
normal and imposes no load deletion or additional force equation.

For each remaining case from Sections 3--4, every whole extra in the
actual hub pocket has distance greater than 1/4 by Section 2. The full
triangulated fan has zero central unit capacity by
`CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`. Its four directly touching
boundary pairs have empty exterior unit pockets by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`. Consequently all three
actual completion units must be in the one exterior pocket through H.
For completeness, extend the actual plane fan to the containing circle
by an occupied access path through each B_i to a circle corner. These
five paths have disjoint open interiors and their circle order is the
path order. The resulting face cover consists exactly of the four
original triangular faces, the four boundary-pair circle pockets, and
the closing pocket whose inner boundary passes through H. An extra's
connected open interior avoids every occupied path and lies on one
of these face sides. Changing the access path within its actual B_i
does not change that label, because the homotopy avoids the extra's
open interior. At a weak junction first fix a compact inner square of
the extra and use sufficiently small compatible routing neighborhoods;
closure gives the whole extra on that face side. This covers every
bounded free component and subdivision by zero-weight physical
contacts. No chord is deleted to make the assignment.

Thus these three units, and the five original boundary units by (4),
are eight actual interior-disjoint units at distance greater than 1/4
from O. The complete all-orientation inner-circle theorem in
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`, Section 1, gives each an
open-interior radius-5/4 arc of angular length greater than pi/4.
The eight arcs are pairwise disjoint, but their total measure exceeds
2pi. This is impossible.

The entire original exterior-hexagon fan with chords {02,03,04} and
forced load set 12345 is therefore excluded throughout the declared
nine-square radius window, using the inherited radius-two exit below
(1). All five boundary loads, all nine positive fan edges and all
three physical completion squares have been retained throughout.

This closes exactly that complete graph/load family. The other seven
positive-chord exterior-hexagon graph types, their remaining load
orbits, the non-hexagonal six-body embeddings, the coarse C1.6.b0
cell, and the unrestricted nine-square theorem are separate obligations.
The source is not a permission to delete their forces or reuse a
degree-two equation at a higher-degree body. No sampled pose,
numerical optimization, Lean compilation, CI, remote action or shared-
ledger mutation is used as a premise or performed by this source.

# Full-window partially unloaded hub pockets and four complete RR-mask exclusions

Date: October 31, 2026 UTC.

**Status: complete proposed hand implications, for full root review.**
The first implication extends the existing partially unloaded hub-path
pocket theorem to the entire original radius window and permits the
weak path supports produced by exact RR promotion. The second uses the
new arbitrary-graph promotion theorem to exclude four whole physical
RR masks at once. All nine actual units and every original positive
chord are retained. No entire original graph/load row is declared closed.

Throughout put

    R_* = 79/40, Q=1105/256, R_*<=R<=sqrt(Q).

An RR transmitter means an original unloaded true-degree-two **side**
transmitter whose two actual endpoint units have physical two-corner
circle masks. The original ports are strict side-interior ports of the
transmitter. Positive endpoint circle loads alone do not imply RR.

## 1. A full-window extension of the existing partially unloaded theorem

Retain all the complete component, endpoint, and order hypotheses of
`SINGLE_HUB_BOUNDARY_ENDPOINTS_PARTIALLY_UNLOADED_PATH_POCKET.md`,
Section 1. Explicitly, the entire positive component is

    H, B_1,...,B_k, k>=3;
    every B_i--B_(i+1), H--B_1, H--B_k;
    any subset of the internal spokes H--B_i.

Its actual exterior cycle is H,B_1,...,B_k,H, with protected physical
circle spokes on its exterior side. H is unloaded and physically
circle-clear. The endpoints B_1,B_k are positively loaded, have their
true positive degree two, and are physically closed-disjoint. Their
other actual neighbors B_2,B_(k-1) are physically circle-touching.
There are at least three positively loaded bodies in the component.
Internal path bodies may have zero circle load, and their degrees,
physical masks, forces, and full means are unrestricted by the theorem.
Every actual hub spoke remains; no external positive force is omitted.

Keep the original compatible weak circular order of the hub normals,
including coincident applications and shared-side endpoint means.
Path-edge normals may be any unchanged genuine common supporting
normals, including a side axis which becomes a weak vertex normal
after promotion. In particular the present theorem does not ask for a
fresh globally strict certificate at the promoted packing.

**Theorem A.** Every whole additional actual unit in the closing
exterior pocket through H between B_k and B_1 has distance strictly
greater than 1/4 from the unchanged circle origin, on the full window
R_*<=R<=sqrt(Q).

The proof is the complete endpoint-normal and winding proof of the
cited partially unloaded theorem, with the following explicit metric
upgrade and weak-support check. They account for every place where
its displayed statement used R>=2 or an original selected path normal.

### 1.1. The replacement radius bound

Write r=R-sqrt(2). Since 99^2>2*70^2,

    sqrt(2)<99/70,
    r>79/40-99/70=157/280,
    r^2>24649/78400>24500/78400=5/16.          (1)

In particular

    r>1/2>1/4,
    r/sqrt(2)>1/4,
    sqrt(r^2-1/4)>1/4,
    sqrt(r^2-1/16)>1/2.                     (2)

Every point of an actual boundary endpoint still has norm at least r:
subtract its unit-square diameter from any actual circle corner. The
support bound p_j dot n_j<=R-1 is unchanged, because its entire
outward neighboring unit has directional width at least one. The upper
window also gives

    R-1<3/2, R-1<sqrt(2).                   (3)

For example R<5/2 gives the first inequality, and
Q<(1+sqrt(2))^2 gives the second. These were the only upper-radius
comparisons in the endpoint-normal proof.

Here is its whole metric cover, retaining the same actual normal
cases and the same strict half-plane directions for the two endpoint
resultants.

| Actual endpoint normals of H | Complete arc estimate on the full window |
| --- | --- |
| Equal H axes | The unchanged full-force/port-order and two endpoint moment signs contradict each other; no metric estimate is needed. |
| Adjacent H axes | The surviving outer two-side arc has projection at least r/sqrt(2)>1/4 on its inward bisector. |
| Opposite H axes | The outer arc's horizontal pieces have norm at least r. If its left vertical piece crosses y=0 and its support had absolute value at most1/4, both actual port radii would require h and1-h at least sqrt(r^2-1/16)>1/2. This is impossible. The other vertical positions have their nearest endpoint already at radius at least r. |
| One H axis, one oblique H normal | The unchanged force/order argument makes the outer arc a left horizontal segment, or that segment plus a left vertical segment. The horizontal part has norm at least r; the vertical part has exactly the preceding opposite-axis estimate. |
| Two oblique normals at adjacent H vertices | In the original chart p_1=(x-1/2,h), p_k=(x+1/2,h), endpoint moments give h>0. Width and (3) give abs(x)<1. One port has absolute horizontal coordinate at most1/2, so h^2>=r^2-1/4>1/16. The whole outer arc is its horizontal side at height h>1/4. |
| Two oblique normals at opposite H vertices | The unchanged grouped full-hub torques and width bound put both ports on opposite sides of the vertical axis and at positive height. The actual two-side outer roof has positive supports at least abs(p_j)/sqrt(2)>=r/sqrt(2)>1/4. All coincident-force groups remain. |

For clarity, the adjacent-oblique width step uses the actual moment
inequalities

    b(x-1/2)+a h>0, d(x+1/2)-c h<0,
    n_1=(-a,b), n_k=(c,d), a,b,c,d>0.

If x>=1, put X=x+1/2>=3/2. Then h>Xd/c and

    p_k dot n_k=Xc+hd>X/c>=3/2>R-1,

contradicting the actual support bound. Reflection excludes x<=-1.
If h<=0, the two strict moment inequalities would require x>1/2 and
x<-1/2 simultaneously. Thus the smaller full-window value h>1/4,
rather than the older unnecessary value h>3/10, is sufficient.

For opposite oblique vertices, the full original proof groups every
force at each endpoint before taking moments. It yields

    p_1=(x-sigma,h), p_k=(x+sigma,h), sigma=1/sqrt(2),
    n_1=(-b_1,a_1), n_k=(b_k,a_k), 0<=a_j<=b_j.

If x>=sigma, the last endpoint moment and unit normalization give
p_k dot n_k>=sqrt(2)>R-1; reflection excludes x<=-sigma.
The first endpoint moment then gives h>0. With X=sigma-x>0 and
Y=sigma+x>0 the roof supports are (X+h)/sqrt(2) and
(Y+h)/sqrt(2), at least the respective port radii divided by sqrt(2).
This verifies that no hidden fan-center estimate or R>=2 bound is used.

Every remaining sign and direction calculation in the cited source
uses only the full hub force and torque, the genuine endpoint torque
signs, proper concurrence, and actual port order. Those inputs hold
throughout the present window as checked next. Thus the table is a
complete extension of its endpoint-normal cover, not a replacement of
that cover by endpoint distances alone.

### 1.2. Weak path supports and the complete endpoint equations

For every actual hub spoke keep magnitude mu_i>0, original normal n_i,
and original full mean p_i. Let F_i be the actual circle resultant,
with F_i=0 at an unloaded internal body. The whole component gives

    sum mu_i*n_i=0,
    sum mu_i*det(p_i-c,n_i)=0 for every fixed c,
    sum F_i=0.                                         (4)

For a path edge B_i to B_(i+1), keep its actual magnitude gamma_i>0,
normal g_i, and actual mean t_i. The true endpoint equations remain

    mu_1 det(p_1,n_1)=gamma_1 det(t_1,g_1),
    mu_k det(p_k,n_k)=-gamma_(k-1) det(t_(k-1),g_(k-1)). (5)

`FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Lemma 1.1, takes **any**
common supporting normal of two actual boundary units, and every
actual point of their intersection. Its proof uses only their
support inequalities, circle-corner angular order, and the unit-width
bound 1-R<=t dot g<=R-1. It does not require the normal to be strict
in a vertex cone. Hence its strictly signed boundary-edge moments
apply to (5), including a newly weak axis at a promoted port. Its
entire radius window is R_*<=R<=sqrt(Q).

Likewise the endpoint proper-concurrence lemma is
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Its literal
premises are positive endpoint circle load, the actual two positive
pair forces, and at least one physically boundary neighbor. The
neighbor's circle load may be zero. It gives

    q_j=tau_j*F_j=p_j+ell_j*n_j,
    tau_j>0, ell_j>=0, j=1,k.                         (6)

Its proof covers both physical circle masks and a coincident pair of
applications. For distinct applications it checks the closed normal
cones of the actual rectangle. In the unique-corner case it excludes
outer concurrence by the unshareable circle corner and unit width;
the potential weak horizontal side-normal endpoint is explicitly
included in that width exclusion. In the two-corner case it retains
abs(q_y)=1/2 and closed side endpoints. Concurrence outside a radial
unit is permitted when the stated inequalities (6) hold. Parallel
force lines are excluded using the actual physically boundary
neighbor and its unit-width obstruction. None of those steps chooses
another normal or requires a strict path vertex cone. Thus (6) applies
to the original forces after promotion as well. No concurrence is
imposed on an internal higher-degree or unloaded path unit.

The hub-spoke normal order and every spoke application remain those
of the original compatible certificate. Promoted weak normals occur
only on path edges. They do not change a hub normal, a positive
magnitude, the true endpoint degrees, or the grouped hub moments.

### 1.3. Zero internal loads, closing order, and the occupied pocket

The protected-circle-order proof in
`GENERAL_BOUNDARY_CHORD_OUTER_CYCLE_ORDER_EXCLUSION.md`, Sections 2--4,
is force-free on the present full window. The positive F_i have
distinct directions in the circular order of their physical boundary
subsequence. The two loaded path endpoints are consecutive across
the closing gap in that subsequence. At least three positive
resultants occur and their sum is zero by (4). A closing gap at
least pi would put all these directions in a closed semicircle,
with at least one strictly inside it, contradicting that sum. Thus
the actual closing resultant gap is strictly less than pi. Zero
internal F_i are kept in the cancellation and do not create a turn
in the closing arc. Extra physical zero-weight circle corners merely
subdivide the other side of the actual ordered path.

The complete endpoint-normal proof now gives a vector v!=0 with

    v dot p>0 on the whole actual outer H arc,
    v dot F_1>0, v dot F_k>0,
    dist(O, outer H arc)>1/4.                           (7)

Use the gap-facing extreme of each actual H endpoint intersection
only to construct the occupied barrier; keep p_j in (4)--(6).
Join each extreme to a gap-facing actual circle corner through its
endpoint's interior. The endpoints are closed-disjoint and H is
circle-clear. These two paths, the intervening outer H subarc, and
the closing circle arc form the actual occupied Jordan boundary of
the pocket. Its endpoint-body parts have radius at least r>1/4;
its H part satisfies (7); its circle part has radius R>1/4.

For the winding computation, every x in B_j and each of its physical
circle corners z satisfy z dot x>=R^2-R*sqrt(2)>0. Thus the whole
endpoint and its q_j lie in F_j dot x>0. Homotope its barrier path
there, avoiding O, to one through q_j and the circle point in the
F_j direction. The actual ordered circle intervals preserve the
closing-arc lift. By (6),(7) and the closing gap less than pi, the
resulting loop lies entirely in v dot x>0 and has winding zero about O.
The original actual boundary consequently has winding zero about O.
It already misses the connected closed quarter disk, so that entire
disk has winding zero. Its compact boundary has a strict margin,
and every whole unit in the pocket has distance greater than1/4.

As in the primary source, a whole extra is assigned by its connected
open interior, which avoids every closed occupied unit. Weak junctions
are handled by retaining a compact inner square before making small
compatible physical routings and then taking closures. The auxiliary
homotopy through q_j is used only for winding about O; it is not a
motion of an extra or a claim that q_j belongs to a radial endpoint.
This proves Theorem A on the full window with every stated weak support.

## 2. Promotion preserves the equations and the actual exterior embedding

Apply
`RADIAL_RADIAL_SIDE_CHANNEL_FULL_CAP_PROMOTION_WITH_ARBITRARY_POSITIVE_GRAPH_2026_10_31.md`
to any chosen original RR transmitters. Its sequential promotion
keeps all nine actual units, promotes each chosen transmitter to its
exact physical circle cap, and fixes every unchosen unit. Arbitrary
positive chords and higher-degree neighbors are included.

Each moving transmitter has exactly two positive pair forces. Its
two actual applications remain the same fixed endpoint inner vertices;
the same opposite forces act on their same line. They remain common
supporting normals at every intermediate position and at the cap.
Therefore all actual force and origin-moment equations remain true,
including the moving transmitter's zero force and zero moment.
Retain its zero circle load at the final cap. No positive load is
assigned merely because a physical circle corner has appeared.

This observation is not a new stress extraction or a transfer of a
secondary minimum. It just checks the original equations at a known
feasible new packing. Theorem A needs exactly those equations and
the actual supports, so the final weak side normals are sufficient.

The original positive center/contact embedding retains its exterior
cycle during the motion. The two moving center-to-port segments stay
inside the moving transmitter's interior apart from their two fixed,
distinct ports. Every other strand stays in its unchanged actual unit.
At these original strict side/vertex RR ports a third unit cannot fit:
the complement of the side half-plane and strict vertex sector has
two sectors each narrower than a square's right angle. Thus their
positive-edge junctions are unambiguous, and the existing small
routings at every other junction can be retained. The strands never
cross another open body as the promotion proceeds. At the final cap
the two ports are distinct adjacent inner vertices; the two rays from
the center are still distinct. Extra physical contacts may subdivide
free regions but do not delete an original strand or swap its sides.

The same argument applies successively to several selected RR units.
A selected transmitter is originally physically circle-clear and
cannot be another selected transmitter's original radial endpoint.
Thus every unprocessed local triple is unchanged. Previously promoted
weak ports are irrelevant to the next purely geometric cap motion.
At the end every new physical circle corner has an occupied access
spoke through its own unit, disjoint from the original positive
strands except at its own center. The actual rim and all its original
chords, forces, applications, and full means are therefore retained.

## 3. Four exact original RR-mask callers

Keep the six positive rim edges 01,12,23,34,45,50. The following
table specifies four complete physical-mask implications on the
original load rows. Every RR condition refers to the original
packing and its original selected side transmitter, before promotion.

| Original positive chords and positive loads | Required original RR units and their radial endpoints | H and actual boundary path after promotion | Actual hub neighbors |
| --- | --- | --- | --- |
| D03.L024: chord03, loads0,2,4 | Both1 between0,2 and5 between0,4 | H=3; path2,1,0,5,4 | 2,0,4; true degree3 |
| D03.L0124: chord03, loads0,1,2,4 | 5 between0,4 | H=3; path2,1,0,5,4 | 2,0,4; true degree3 |
| D0203.L1235: chords02,03, loads1,2,3,5 | 4 between3,5 | H=0; path1,2,3,4,5 | 1,2,3,5; true degree4 |
| D0204.L1245: chords02,04, loads1,2,4,5 | 3 between2,4 | H=0; path1,2,3,4,5 | 1,2,4,5; true degree4 |

In the first row the original radial mask is required at0,2,4.
In the second it is required only at0,4. In the third it is required
at3,5, and in the fourth at2,4. No radiality is imposed on another
loaded body. Every individual zero circle-corner weight is retained.

The chosen units have true positive degree two and zero circle load
in these original rows. Every original neighbor listed for H remains
in its full star. In the first two rows the genuine loaded endpoints
are2,4, both true2; the loaded internal body0 remains true3. In the
third row the endpoints are1,5, both true2, while the loaded internal
bodies2,3 retain true3. In the fourth the endpoints again are1,5,
both true2, and the loaded internal bodies2,4 retain true3.

After the specified promotions all five path units physically touch
the circle. H stays physically circle-clear: if it touched the circle
as well, the original physical rim would be a forbidden six-boundary
cycle, by `CIRCLE_CONTACT_ANGULAR_ORDER.md`, Section5. The two path
endpoints are closed-disjoint, since an additional physical contact
between them would close a five-boundary cycle on their existing
five-unit path. Each endpoint's actual other path neighbor is now
physically boundary, including any promoted neighbor with zero load.

The original positive component contains respectively three, four,
four, and four nonzero circle resultants. All other ones remain zero.
The full original component sum is unchanged. Section2 gives its
actual exterior cycle and protected boundary order. Consequently
every premise of Theorem A, including the two true endpoint stars,
is supplied for every row in the table. No chord endpoint is made
into a degree-two tip, and no positive chord is removed.

## 4. Full face allocation and the common eight-unit contradiction

After promotion the entire actual bounded face list is still

| Original chords | Actual bounded faces | Reason every face has zero unit capacity |
| --- | --- | --- |
| 03 | 0123,0345 | Each quadrilateral has three of the five physical boundary path units. |
| 02,03 | 012,023,0345 | The first two are contact triangles; the quadrilateral has physical boundary3,4,5. |
| 02,04 | 012,045,0234 | The first two are contact triangles; the quadrilateral has physical boundary2,3,4. |

Triangles are empty by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Theorem1.1. Each displayed
quadrilateral is empty by `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`.
That theorem is completely force-free, requires only three actual
physical boundary units and R^2!=5/2, and retains arbitrary outside
forces, original means, and weak junctions. Its radius premise holds
throughout the current window. Thus zero load at a promoted unit
does not weaken any of these central-face exclusions.

The four exterior pockets at consecutive path pairs are empty by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Theorem4.1. Its hypotheses
are physical contact and physical circle contact of the pair. It uses
no positive circle load, no selected-normal strictness, and no degree
assumption. It retains all other actual units during its pocket
dilation. Hence the weak path ports produced by promotion are included.

This list and the closing H pocket exhaust the three original
completion units. To see the complete allocation, extend the actual
plane graph by an occupied path from each of its five boundary units
to one actual circle corner. Those ordered access paths have disjoint
open interiors. The disk is cut into exactly the original bounded
faces, the four direct boundary-pair pockets, and the closing pocket
through H. An extra's connected open interior avoids all these closed
occupied strands and lies on one of their face sides. At a weak
junction fix a compact inner square of the extra before choosing the
arbitrarily small compatible routing; closure gives the entire unit
on that side. Additional zero-stress contacts can subdivide a side
but cannot merge sides through an occupied strand. No chord has been
deleted to produce this allocation.

All three actual completion units must therefore lie in the closing
H pocket. Theorem A gives each distance strictly greater than1/4.
The five actual boundary path units have distance at least
R-sqrt(2)>1/4 by (1). These are eight distinct actual unit squares,
with their independent original frames or exact promoted frames,
inside the same disk of radius at most sqrt(Q).

The complete force-free inner-arc theorem
`UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md`,
Theorems A and B, gives each such unit an open-interior arc of length
strictly greater than pi/4 on the radius-5/4 circle. Its stated
clearance threshold at this radius is exactly 5/4-1=1/4. This radius
is in its complete allowed interval because that source proves

    r_-<157/128<5/4<13/10<r_+.

Thus the actual strict distance bounds above supply the premises
directly, without a further endpoint-mask or half-plane inference.
The eight open arcs
are pairwise disjoint because the actual unit interiors are disjoint.
Their total length would exceed2pi. This contradiction excludes
every entire RR mask listed in Section3.

The proof uses the full original radius interval. It does not invoke
the radius-two measure certificate or a computed arithmetic table.
Every original hub degree, load, force, mean, chord, and all three
actual completion units were retained in the original packing and
in the promoted packing used for the contradiction.

## 5. Additional arbitrary-graph physical boundary obstructions

The same promotion theorem has a useful completely force-free graph
corollary. Take **all** original physical boundary units, including
zero-load units outside the positive component. Add any chosen
original RR transmitters by simultaneous sequential promotion. Keep
every old physical contact between the unchanged boundary units and
the two original endpoint contacts of each promoted transmitter.
This is a subgraph of the resulting actual physical boundary graph.

By `CIRCLE_CONTACT_ANGULAR_ORDER.md`, Sections3--5, the latter has
maximum degree two and is a path forest unless it is one seven-cycle.
Therefore each of the following original RR features is impossible:

1. A selected transmitter has a radial endpoint which already touches
   two **other** original physical boundary units. Promotion would
   give that unchanged endpoint three distinct boundary neighbors.
2. The retained boundary contacts and chosen RR paths create a cycle
   of length at most six after promotion. Such a physical boundary
   cycle is forbidden, even if some of its circle loads are zero.
3. They create a seven-cycle while there is another original or
   promoted physical boundary unit outside it. A boundary cycle must
   be the complete seven-cycle containing every actual boundary unit.

For example in the representative D03.L0134, RR2 alone would give
boundary3 the boundary neighbors0,2,4, and RR5 alone would give
boundary0 the boundary neighbors1,3,5. This is a literal illustration
of item1; it is not new whole-row credit, since that original row
already has a separate boundary-chord exclusion.

These graph obstructions are separate from the cap theorem's count
b+r<=7 and from the four pocket-capacity exclusions above. They use
actual physical contacts rather than treating a missing positive
edge as physical separation.

## 6. Exact adoption boundary

The new exports are the full-window quarter-pocket implication with
weak promoted path supports, the original nine-unit exclusions of
the four explicitly stated RR masks, and the arbitrary-graph
physical-boundary obstructions in Section5. Graph-preserving
dihedral images act on every unit, force, mean, and mask together.

None of the four original graph/load rows is closed by its RR mask
alone. The other side-channel endpoint masks, any diagonal channels,
and all other original physical features remain separate obligations.
No original fine/coarse flag, proof-gate count, unrestricted n=9 claim,
or formal verification status is changed by this source itself.

No numerical pose, script-based certificate, sampled orientation,
force truncation, normal reselection, Lean/Lake invocation, CI,
workflow dispatch, remote write, or shared-ledger mutation is used.

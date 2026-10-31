# A physical minimizer stress can be chosen with a planar body graph

**Status: complete hand construction, independently audited.**
The physical contact certificate of `PHYSICAL_CONTACT_STRESS.md` can
be chosen so that its positive body-pair graph has a plane embedding.
Every physical circle-touching vertex of that graph is incident to
the exterior face, whether or not its circle multiplier is positive.
The normalized certificate still has at most \(3n\) positive scalar
atoms before aggregation, hence at most \(27\) for nine squares.

This is an **existence statement about a selected certificate**. It
does not assert that every physical stress, or the complete physical
touching graph, is planar. The construction selects certain free
vertex/vertex normals before obtaining the equilibrium certificate,
then exactly replaces crossing forces at four-square junctions.

## 1. The local geometry at a shared contact point

Let finitely many closed unit squares have disjoint open interiors.
At a point \(p\) of a square, its inward tangent sector has angle
\(\pi/2\) if \(p\) is a vertex and angle \(\pi\) if \(p\)
is in the relative interior of a side. Distinct incident squares
have disjoint open tangent sectors. Thus at most four squares can
meet at one point.

If four meet at \(p\), all four sectors have angle \(\pi/2\),
and they exactly fill a full turn. Their side frames therefore agree,
and their union is an aligned \(2\times2\) block centered at
\(p\). In its orthonormal frame \(u,v\), name the squares
\(\mathrm{SW},\mathrm{SE},\mathrm{NE},\mathrm{NW}\) according
to their quadrant at \(p\).

Each adjacent pair shares a full unit side with endpoint \(p\).
Each opposite pair has only the point \(p\) in common. A drawing
whose vertices follow these four sectors can cross at \(p\) only
if it uses both opposite pairs:

\[
 \mathrm{SW}\!\text{--}\!\mathrm{NE},
 \qquad
 \mathrm{NW}\!\text{--}\!\mathrm{SE}.
 \tag{1}
\]

For three or fewer incident squares, every local body-pair graph can
be drawn without crossings in their cyclic sector order. For four,
the cyclic adjacent edges together with at most one of the two
diagonals also have such a drawing.

## 2. Choose compatible free normals before taking multipliers

At a point-only vertex/vertex contact, the physical local feasible
branch permits any unit common normal that strictly exposes the
common vertex in both squares. These normals form a nonempty open
angular interval; see `PHYSICAL_CONTACT_STRESS.md`, Section 2.2.

At each four-square junction, choose positive numbers

\[
                 a,b>0,\qquad a^2+b^2=1,
 \tag{2}
\]

and prescribe the two opposite-pair normals to be

\[
 \begin{aligned}
 n_+&=a u+b v
       &&\text{from SW to NE},\\
 n_-&=a u-b v
       &&\text{from NW to SE}.
 \end{aligned}
 \tag{3}
\]

Both choices strictly expose the two corresponding vertices, because
\(a,b>0\). Their matching absolute coefficients will be used in
the force identity below.

At any nonzero junction \(p\), one can additionally require

\[
                  \det(p,n_+)\ne0,
                  \det(p,n_-)\ne0.
 \tag{4}
\]

Each equality forbids at most finitely many parameters in the open
quarter-circle (2). At other point-only contacts, a nonradial normal
can be chosen in the same way when \(p\ne0\). When \(p=0\),
every normal has zero origin moment; no nonradial assertion is made
there, and the subsequent uncrossing works unchanged.

If desired, also avoid the two incident squares' diagonal directions
at every point-only contact. These are again finitely many forbidden
directions. In (3) this only adds \(a\ne b\), because all four
frames agree. This optional choice is compatible with (4).

These choices are made **before** using the physical feasible branch
and its multiplier theorem. They are legitimate fixed normals of
that branch; no equilibrium normal is changed after the multipliers
have been obtained. An opposite pair has just one common point, so
choices at different four-square junctions do not conflict.

Use these normals together with the usual vertex/side and two-endpoint
side-contact branches. The physical minimizer theorem gives
nonnegative contact multipliers and normalized nonnegative circle
multipliers, satisfying force and torque balance at every body.

## 3. An exact uncrossing identity at one four-square junction

Suppose the two opposite edges at \(p\) have positive multipliers
\(\mu,\nu\), in the orientations (3). Put

\[
                             t=\min(\mu,\nu)>0.
 \tag{5}
\]

Subtract \(t\) from each opposite multiplier. Replace those
subtracted contributions by four adjacent-pair forces, all applied
at the same physical point \(p\):

| Oriented adjacent pair | Unit normal | Added multiplier |
| --- | --- | --- |
| SW to SE | \(u\) | \(ta\) |
| NW to NE | \(u\) | \(ta\) |
| SW to NW | \(v\) | \(tb\) |
| SE to NE | \(v\) | \(tb\) |

The common amount \(t\) of the two original opposite forces gives
the following total force on each body:

\[
 \begin{array}{c|c}
 \mathrm{SW}&t(a u+b v)\\
 \mathrm{NE}&-t(a u+b v)\\
 \mathrm{NW}&t(a u-b v)\\
 \mathrm{SE}&t(-a u+b v).
 \end{array}
 \tag{6}
\]

The four adjacent forces in the table reproduce exactly the same
four totals. Every replaced and every added contribution acts at
\(p\). Therefore its torque about each body's center, as well as
its torque about the origin, is also preserved exactly. Equivalently,
the corresponding physical contact-gradient vectors satisfy an exact
nonnegative linear identity.

All new forces are legitimate physical atoms. Adjacent squares in the
\(2\times2\) block share a whole unit side, and \(p\) is one
endpoint of that side. The two-endpoint side-contact branch already
includes the physical gradient at this endpoint. Thus the replacement
uses actual active rows of the original feasible branch, not invented
forces or nonphysical application points.

Every new multiplier is nonnegative, every old multiplier remains
nonnegative, and at least one opposite multiplier becomes zero by
(5). Circle multipliers are unchanged, so their normalization is
unchanged. This eliminates the crossing at this junction.

Perform the same operation independently at every four-square
junction with two positive opposite pairs. No operation can create a
new opposite-pair crossing at another junction: each newly added
pair has a positive-length side intersection, whereas an opposite
pair at any four-square junction has only that one point in common.
There are finitely many junctions. After these replacements no
four-square junction carries both positive opposite edges.

## 4. Restore sparsity and aggregate body pairs

The uncrossing may temporarily increase the number of positive
endpoint atoms, but the \(3n\)-atom bound can be restored without
reintroducing a crossing.

Keep only the atom types currently carrying positive coefficients.
They give a nonnegative representation of the same objective-gradient
balance. Every contact and circle gradient is orthogonal to the
infinitesimal simultaneous rotation of all bodies. In the
\(3n+1\) position/angle/radius variables, they therefore lie in a
linear subspace of dimension at most \(3n\). The same elementary
conic thinning used in `PHYSICAL_CONTACT_STRESS.md` yields a
representation using at most \(3n\) of these surviving atoms.
The radius coordinate still gives

\[
                         \sum_{i,k}\lambda_{i,k}=1.
 \tag{7}
\]

This thinning only deletes atom types; it does not add a previously
removed opposite edge. All force, torque, positivity, and normalization
conditions persist. Remaining point-only normals retain their strict
exposure and any finite avoidances chosen in Section 2.

For each positive body pair, aggregate its surviving atoms as usual.
At a side contact their normals agree, so replace them by their total
magnitude acting at their weighted mean point of the actual common
segment. At a point-only contact there is a single prescribed normal
and a single application point. Aggregation does not change which
body pairs are positive and cannot add an opposite pair at a junction.
The scalar-atom count asserted here is the count **before** this
aggregation, exactly as in the original physical certificate theorem.

## 5. Construct a plane embedding of the selected body graph

Give each positive body-pair edge an initial drawing from one center
to its aggregate application point and then to the other center.
Except for the contact endpoint, each half-edge is in its own square's
open interior. Consequently two such drawn edges can meet away from
their incident body centers only at a common contact application
point.

Around the finitely many such junctions choose small pairwise
disjoint disks, avoiding all square centers and other junctions.
At a junction, the incident square sectors occur in their geometric
cyclic order. The selected local body-pair graph has at most three
vertices, or has four cyclic vertices with at most one diagonal,
by Sections 1--3. Each of these graphs has a noncrossing drawing
with its vertices in that sector order on the boundary of a disk.
For four vertices, draw the cyclic adjacent edges near the boundary
and the sole possible diagonal through the interior.

Use these local drawings to replace the initial strands inside each
junction disk. When one square contributes several strands at the
same junction, order them within its contiguous sector according to
this local drawing and run them as separate parallel strands along
its center-to-junction tube. They meet only at the square's center.
Tubes for distinct contact points of the same square have distinct
directions from that center; they can be made disjoint except at
the center. Tubes in different square interiors are disjoint.

These replacements give a plane drawing of the positive body-pair
graph. Unlike a drawing of an arbitrary contact stress, no unresolved
opposite-pair crossing remains.

## 6. All circle-touching positive vertices lie on the exterior face

A point of the containing circle cannot belong to two packing
squares. For completeness, if \(z\) is a circle corner of a unit
square and \(w_1,w_2\) are its two orthonormal inward side
directions, containment of \(z+w_j\) gives

\[
                      z\cdot w_j\le-\frac12.
\]

Thus the short radial segment \(z-\varepsilon z\) lies in its
open square. Two squares sharing \(z\) would overlap along that
segment.

For every physical circle-touching square that is a vertex of the
positive graph, choose one circle corner \(z_i\), and consider
the spoke from its center \(C_i\) to \(z_i\). Its open segment
is in its square's open interior. It meets the initial center/contact
drawing only at \(C_i\): two rays from the center cannot intersect
away from that center, and a contact endpoint on the same ray would
have to equal the circle corner itself, which cannot be shared.
The spokes of distinct squares are disjoint.

All contact junctions lie strictly inside the containing disk, and
none lies on a spoke. In Section 5 choose the junction disks and
the parallel tube perturbations small enough to avoid all spokes
away from their incident centers. Then the completed plane drawing
still has these pairwise disjoint spokes to the containing circle.

The graph drawing lies strictly inside the containing disk; its
contact points are not circle points, and its segments and sufficiently
small perturbations remain inside. A chosen circle corner therefore
lies in the unbounded face of the graph. Its spoke shows that its
body vertex is incident to that same exterior face. This conclusion
uses physical circle contact alone, with no positivity requirement
on that body's circle multiplier.

**Theorem 6.1 (planar selected physical certificate).** Every
minimizing packing of \(n\) unit squares admits a normalized
nonnegative physical contact/circle certificate satisfying force and
torque balance, with at most \(3n\) positive scalar atoms before
aggregation, such that its positive body-pair graph has a plane
embedding with all physical circle-touching vertices on the exterior
face.

Each connected positive component inherits this plane embedding and
the body balances. Its total circle weight is positive by the existing
component lemma, so division by that weight normalizes its certificate.
If a separate \(3m\)-atom bound is needed on its \(m\) bodies, the
same conic thinning can be applied within that component. It may delete
edges or split the positive graph, but preserves the inherited planar
and exterior-face properties.

The theorem requires no special bound on \(R\) beyond the containing
disk and the existence of the physical minimizer certificate.

## 7. Two elementary consequences and their scope

First, for a connected selected component with \(m\ge3\) vertices,
let \(e\) be its number of distinct positive body pairs and let
\(b\) be the number of its physical circle-touching vertices. If
the exterior face boundary walk has length \(L\), then \(L\ge b\).
Every bounded face of a simple plane graph has degree at least three,
so Euler's formula and face-degree counting give

\[
                 e\le3m-3-L\le3m-3-b.
 \tag{8}
\]

Bridges are counted twice in the exterior boundary walk, as usual;
the inequality does not assume a biconnected graph.

Second, if the optional diagonal avoidance of Section 2 was imposed,
a surviving positive point-only vertex/vertex contact cannot be
incident to an unloaded vertex of positive degree two. Indeed, the
two-force transmission lemma makes its two forces opposite and
collinear. A strict vertex contact then forces transmission along a
diagonal of that square, contradicting the chosen normal. This
consequence concerns point-only contacts; it does not exclude a
diagonal transmitter whose endpoint is against the relative interior
of another square's side.

The planar certificate is a new global necessary condition. It does
not itself close the remaining mixed cyclic completion classes or
the unrestricted nine-square radius theorem. In particular, no bound
is transferred from a planar selected graph to every possible
physical body graph.

# Every touching return pair of an unloaded three-force square lies strictly behind its third support

Date: October 28, 2026 UTC. Author: frontier_audit continuation.

**Status: complete proposed radius-free full-domain theorem and
selection-free unloaded-diamond corollary, submitted for full root
and separate independent review. No original fine/coarse checkbox
or historical source is changed.**

The two returned normals need not be owned, perpendicular, parallel
or fixed at a generic choice. The proof includes all original
side means, side endpoints, free normals and every support owner
at the returned units.

## 1. Exact physical and full-force theorem

Let U,Q,V,W be distinct actual closed unit squares with pairwise
disjoint open interiors. U is unloaded and its entire positive
pair neighborhood is exactly Q,V,W. Retain every original
separating unit normal, positive magnitude and application or
shared-side mean. Assume the actual V and W physically touch;
their contact need not carry positive force.

All equations, loads, masks and true degrees at Q,V,W are
arbitrary. No containing-circle or radius premise is required.
Additional zero-weight physical contacts remain permitted.

Let n0 be the actual U-to-Q normal and p0 its unchanged actual
application. Then

    n0.z < n0.p0     for every actual z in V union W.       (1)

Thus both whole closed returned units are strictly on U's side
of its actual third support. Since Q lies in the opposite
closed half-plane n0.z>=n0.p0, Q is closed-disjoint from both
V and W. More generally neither return can touch any actual
set entirely in that opposite closed half-plane.

The proof uses only U's full original force and torque, the
actual V--W contact, their unit geometry and their original
U supports. It never changes a normal or a side mean.

## 2. Complete physical support tools

### 2.1. Strict unit reach at any actual support point

Suppose P is any actual minimum-n support point of a unit
square K. For a unit direction e with n.e<0,

    max_(z in K) e.(z-P)<1.                              (2)

At a vertex, choose the two inward orthonormal own axes.
Their n components are nonnegative. They cannot both have
positive e components, since that would force n.e>=0.
The sole possible positive component is strictly below one;
equality one would make e an inward axis and again give
n.e>=0. At a side-interior point only the actual tangent
interval can contribute positively. Its length is at most
one and its projected unit component is strictly below one.
Side endpoints are included in the vertex case.

In particular a neighbor with actual minimum-support point
(1,1) and strict Northeast inward normal lies entirely in
x>0,y>0. A neighbor at (1,0) with strict Southeast inward
normal lies entirely in x>0,y<1. These whole-unit statements
include side-owned normals and arbitrary actual means on
the neighboring square.

At a minimum-East support point (1,p), the corresponding
weak perpendicular bound is

    x>=1, p-1<=y<=p+1                                  (3)

on the whole neighbor. To verify the y bounds, the inward
vertex axes have nonnegative x components, so at most one
has positive y component and at most one negative component,
each of magnitude at most one. At a side-interior point
use the unchanged tangent interval of length one.

### 2.2. Physical triangles with one U-owned side axis

If V,W touch and the actual U-to-V normal is an own axis
of U, its dot product with the actual U-to-W normal is
nonnegative. For completeness, normalize the first axis
to East and U=[0,1]^2. If the other normal had negative
x component, its actual U application would lie on x=0.
Formula (2), applied to W in the East direction, would
put the whole W in x<1. But V lies in x>=1, contradicting
their actual contact.

This uses no force equation and no normal-selection rule.

### 2.3. Opposite strict U vertices cannot provide touching returns

Normalize U=[0,1]^2. If one return has strict Northeast
normal at (1,1) and the other strict Southwest normal at
(0,0), (2) gives

    V subset {x>0,y>0}, W subset {x<1,y<1}.

Any common point would be in int U. A point of another
closed unit in int U is impossible: every neighborhood
of that point also contains open-interior points of that
other unit, producing an interior overlap. The other
opposite-corner pair follows by reflection.

Two opposite U-owned axes also cannot give touching
returns: their outward half-planes are separated by
U's positive width one.

### 2.4. The full perpendicular-axis case

If both return normals are perpendicular own axes of U,
the complete radius-free theorem

UNLOADED_THREE_FORCE_PERPENDICULAR_TRIANGLE_STRICT_SUPPORT_SEPARATION.md

applies directly. Its exact frozen SHA256 is

6630675274998befc40e87bfe67e15f0bdf0d74b7b814f82ccbc42b71dea4b24.

It uses the full actual three-force equation to force the
third corner, and the exact relation between the two
unchanged means. Its strict relay covers every parallel
and nonparallel return frame, including equality orientations,
and is applied in both physical directions. Its conclusion
is exactly (1) for both returned units.

No higher-degree extension or conditional original-family
table is needed for this invocation.

## 3. Both original return normals are U-owned axes

If the axes are opposite, Section 2.3 already contradicts
the actual V--W contact.

If they are equal, rotate so both are East. Full positive
U force balance makes n0 West. Its original application
lies on x=0, while every point of either return lies in
x>=1. This gives (1) strictly for every possible original
third application and both returned means.

The only other pair of own axes is perpendicular, covered
in full by Section 2.4. These exhaust both-owned returns.

## 4. Exactly one original return normal is a U-owned axis

Rotate the actual U chart to [0,1]^2 with V East, at its
unchanged application P_V=(1,p), 0<=p<=1. By Section 2.2,
the other nonaxis normal has positive x component. Reflect
vertically if necessary so W has strict Southeast normal
and original U application P_W=(1,0).

Write the actual force vectors on U as

    F_V=(m,0), F_W=(s,-w), m,s,w>0.

These are force components, including their original
positive magnitudes. Full U force balance makes the third
force (-(m+s),w). Its unit normal is therefore strict
Northwest and its original application is p0=(0,1).

Full torque about p0 gives

    m*(1-p)+s-w=0,
    w=s+m*(1-p)<=m+s.                                 (4)

Set E=m+s and define H(x,y)=E*x-w*y. The desired strict
separation is H(z)>H(p0)=-w.

For every point of W, Section 2.1 gives x>0,y<1.
Hence

    H(z)+w=E*x+w*(1-y)>0.                              (5)

For V, its actual East support and full transverse mean
bound (3) give

    H(z)+w>=E-w*p.                                    (6)

This is strictly positive for every p in [0,1]. If p<1,
w<=E gives E-w*p>=E*(1-p)>0. If p=1, (4) gives
E-w=m>0. Both original mean endpoints are included.

Thus (1) holds on both whole returned units. The reflection
used above covers the strict Northeast alternative without
changing any physical square, application or force.

## 5. Neither original return normal is a U-owned axis

Each original normal then strictly exposes one actual U
vertex; its original application on U is that vertex.
No condition on its owner or mean on the returned unit
is inferred.

Opposite U vertices are excluded by Section 2.3. Thus the
two applications are identical or adjacent.

### 5.1. The same U vertex

Normalize their common vertex to (1,1). Both return force
vectors have strictly positive x and y components. Their
positive sum has the same property, so the third normal
is strict Southwest and its original support is p0=(0,0).

Both returned units lie entirely in x>0,y>0 by (2).
Their projections on the positive sum of the return
forces are strictly positive, whereas the level at p0
is zero. This is exactly (1).

### 5.2. Adjacent U vertices: the parallel third-normal endpoint

Normalize the applications and actual force vectors as

    P_V=(1,1), F_V=(f,t), f,t>0,
    P_W=(1,0), F_W=(s,-w), s,w>0.                      (7)

If w=t, the full third force is West. Its application
has x=0. Each returned unit has x>0 by (2), so (1)
again holds strictly, independently of the third side mean.

If w<t, reflect the whole coordinates vertically and
interchange the two return names. The new lower-return
vertical magnitude exceeds the new upper one. Since
the theorem treats both units symmetrically and makes
no degree or load assumption on either, it therefore
suffices to prove the case w>t.

### 5.3. Adjacent U vertices: the complete strict third-normal case

Now the third normal is strict Northwest, so its actual
application is p0=(0,1). Full torque about p0 gives

    t+s-w=0, w=t+s.                                   (8)

Divide all force vectors by E=f+s>0. Define

    kappa=s/E, omega=w/E.

Then

    0<kappa<1, omega>kappa,
    h=(1,-kappa),
    g=(kappa,-omega),
    F_V/E=h-g=(1-kappa,omega-kappa).                   (9)

The desired separation is

    h.z>h.p0=-kappa.                                  (10)

For W, its actual strict Southeast support at (1,0)
puts the whole unit in x>0,y<1. Consequently

    h.z+kappa=x+kappa*(1-y)>0,

which proves (10) for W.

It remains to prove (10) for the entire actual V,
including when V owns its contact normal and (1,1)
is an arbitrary actual V side mean. No vertex-frame
assumption at V will be made.

Suppose some actual X in V violated (10), so
h.X<=-kappa. Put P=(1,1), the unchanged U/V application.
The actual original V support is

    (h-g).(Y-P)>=0  for every actual Y in V.           (11)

Choose any actual Z in V intersect W. The original
U/W support makes g.Z>=g.(1,0)=kappa, while
g.P=kappa-omega. Thus

    g.(Z-P)>=omega.
    h.(X-P)<=-1.                                     (12)

Applying (11) at X and Z respectively gives

    g.(X-P)<=h.(X-P)<=-1,
    h.(Z-P)>=g.(Z-P)>=omega.

Subtracting shows that the same actual vector Z-X
has both lower projection bounds

    g.(Z-X)>=1+omega,
    h.(Z-X)>=1+omega.                                 (13)

But X and Z lie in one unchanged unit square V.
Its diameter is sqrt(2), so Cauchy gives

    1+omega<=sqrt(2)*min(|g|,|h|).                    (14)

This is impossible on the whole domain (9).

If omega>=1, then |h|=sqrt(1+kappa^2)<sqrt(2), and

    sqrt(2)*|h|<2<=1+omega.

If omega<=1, then kappa<omega gives
|g|=sqrt(kappa^2+omega^2)<sqrt(2)*omega, and

    sqrt(2)*|g|<2*omega<=1+omega.

The common endpoint omega=1 is included in both strict
estimates. These two inequalities require no subdivision
of any physical angle, no orientation ordering and no
chosen normal on V. They exclude even equality in (10).

This proves strict separation on V and completes every
adjacent-vertex feature.

## 6. Exhaustiveness, higher degrees and the exact selection-free corollary

Every unit-normal support feature of U is either an own
axis, with its original complete side mean, or a strict
vertex cone, with its uniquely exposed U vertex.
Sections 3--5 cover both axes, exactly one axis and
neither axis. Same, adjacent and opposite vertex
pairs are all accounted for. All changes of coordinates
are rigid rotations, translations or reflections of
the same physical data; no original normal is reselected.

This proves the entire theorem in Section 1 without a
generic-normal or fixed-star determinant premise.

**Selection-free unloaded-diamond corollary.** An unloaded
actual unit whose entire positive neighborhood consists
of exactly three distinct units cannot have two physical
contact edges among those three neighbors.

Indeed any two such edges on three vertices share a
vertex. Choose one of them as V--W and name the remaining
neighbor Q. The other physical edge joins Q to V or W,
contradicting the whole closed separation in (1). The
edges among the neighbors need not have positive force.
All neighbor degrees and loads are arbitrary.

This is a radius-free statement for every original
normal and mean satisfying the full U equilibrium.
It strengthens the logical premise needed by the
existing NO_UNLOADED_DIAMOND_HUB.md consequence.
That historical source and all its existing pins are
preserved; this manuscript does not silently repin a
caller or alter any prelisting.

There is also a precise conditional full higher-degree
extension. Keep every original force at an unloaded U,
select two positive forces to physically touching V,W,
and let R0 be the sum of every other original force.
Require an actual maximum-R0 support point p0 of U
such that the sum of those other original moments
about p0 is zero. Then R0 is nonzero: otherwise the
two selected positive normals would be opposite,
contrary to their touching units and U's positive
width. Full U force gives R0+F_V+F_W=0; full torque
gives the same two-return torque about p0 used above.

All proofs of Sections 3--5 use only that aggregate
vector, its genuine U support point and these full
equations. They therefore give

    R0.z<R0.p0  for every actual z in V union W.       (15)

A sufficient special case is that all other original
applications coincide at the same actual U support
point p0: their positive normal sum supports U there,
and their moments about p0 vanish individually.

No actual third neighboring unit is automatically
placed beyond an aggregate support line. A physical
separation corollary needs that neighbor's own
supporting half-plane or another proved containment.
Neither the supporting-point premise nor the
aggregate-moment premise is automatic at H4.

## 7. Literal broad interfaces and limits

Every true-three-force row in the earlier perpendicular
source now has the strict conclusion for its entire
original normal/owner domain, without the perpendicular
condition:

| Original family | Actual unloaded U; actual third neighbor Q | Actual touching return pair |
| --- | --- | --- |
| M6.B5L.HOUSE.LOWER.LTDC.S | A3; B3 | T2,D3 via TD |
| M6.B5L.HOUSE.ROOF.LAC.S | D3; C2 | T3,A3 via TA |
| M6.B5L.HOUSE.ROOF.LABC.S | D3; C2 | T3,A3 via TA |
| M6.B5L.HOUSE.HUB.LTC.S | D3; C2 | A4,T2 via AT |
| M6.B5L.HOUSE.HUB.LTCB.S | D3; C2 | A4,T2 via AT |
| M6.B5L.FAN.ENDPOINT.L234.S | Root 1 of degree three; its genuine leaf L | J4,loaded 2 of degree three via J2 |

The roof-root callers U=T, Q=L, pair A,D are also
unconditional in their original owner domains: AD is
an actual edge and T retains its full genuine third
leaf force. The lower-TDC.D star is another literal
example, now in the closed D-family proof.

For both four-spoke no-chord pentagon load families,
use the unchanged actual unloaded end U=3 with
third neighbor Q=4 and return pair H,2. The actual
edge H2 supplies the triangle. The theorem uses
only U's genuine degree-three equation; H retains
all four original forces and 2 its loaded degree
three. It puts both whole H and 2 strictly on U's
side of the original 3-to-4 support.

For load L124 the other end 0 is also unloaded of
degree three, so the additional literal caller
U=0, Q=4, pair H,1 applies. In L0124, unit 0 is
loaded, and that additional invocation is unavailable.

These are complete whole-interface conclusions,
not full original-family exclusions. None implies
a nonexistent A--C contact in a house or removes
a loaded endpoint's circle force. A contradiction
still requires an actual contact across the proved
line or another exact physical obstruction.

## 8. Exact mathematical sources and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNLOADED_THREE_FORCE_PERPENDICULAR_TRIANGLE_STRICT_SUPPORT_SEPARATION.md | 6630675274998befc40e87bfe67e15f0bdf0d74b7b814f82ccbc42b71dea4b24 | Only the complete full true-three-force perpendicular-axis case; its conditional higher-degree/table conclusions are not used to prove the general theorem |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Physical support-span and owned-axis triangle proofs, restated in Section 2 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original S-house/fan graph labels, loads and true degrees |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal original H4_D0 pentagon graph, unloaded ends and full positive degrees |

All new inequalities and geometric cases are proved
above. The theorem has no radius window, no graph
size beyond its actual local star, no load or degree
hypothesis at the returns, and no assumption about
the location of any completing square. Every
original unit, normal, side mean and endpoint stays
fixed.

No numerical pose search, angle mesh, scalar
exclusion certificate, force deletion, selected
normal modification, Lean compilation, CI,
workflow, ledger edit or remote write is used.


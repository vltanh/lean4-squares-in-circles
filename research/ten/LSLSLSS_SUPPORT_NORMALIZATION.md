# Seven central support forms for LSLSLSS

**Status:** reviewed exact necessary-form reduction; root and independent
mathematical reviews passed on 2026-10-30, including the reused R-VE exclusion.
This is a finite ownership split inside the existing fixed whole-case
ID, not a new progress denominator or a whole-case exclusion.

Consider the positive cycle `A–U–V–B–T–C–S–A`, where A, B, C are loaded,
U,V form an SS path, and S,T are single side transmitters. Its fixed
signature is `C20-M07-L03-B02-T01 LSLSLSS`. Assume
`79/40≤R≤3/sqrt(2)` and use the selected physical stress.

Let P_A,P_B be the contacts on C, and let n_A,n_B be their outward unit
normals, pointing along the two S paths toward A and B. The exact path
distance theorem gives

```text
Q_A=P_A+n_A ∈ A,          Q_B=P_B+n_B ∈ B,
dist(A,B)=2.                                             (1)
```

The following reductions retain arbitrary endpoint orientations,
arbitrary positive stress weights, and all allowable circle-load splits.

## 1. Three universal central exclusions

**Parallel directions.** If `n_A=n_B`, both P contacts lie on one
support face of C, whose diameter is at most 1. Hence
`dist(A,B)≤|Q_A−Q_B|=|P_A−P_B|≤1`, contradicting (1).
If `n_A=−n_B`, the endpoints are separated along that direction by C's
projection width plus 2, at least 3. This also contradicts (1).

**Coincident contacts.** If `P_A=P_B=P`, the two normals lie in one
normal cone of C, of angular width at most pi/2. Therefore
`dist(A,B)≤|n_A−n_B|≤sqrt(2)<2`. The contacts are distinct.

**Outer side-normal supports.** A unit square supported at Q with inward
unit normal n contains `Q+n`; this is the unit-normal-step lemma of
[SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md).
Thus the endpoint reached from a side-normal C contact P contains
`P+2n`.

If C has a unique circle vertex `(X,Y)` in its own axes, choose the axes
so `X,Y>1/2` and

```text
C=[X−1,X]×[Y−1,Y],       X²+Y²=R².
```

A right-side or top-side S path would put a point of an endpoint square
at x-coordinate `X+2>5/2` or y-coordinate `Y+2>5/2`, respectively.
Since `R<5/2`, this is impossible. The only side-normal supports are
the inner left and bottom sides.

If C has two circle vertices, its own axes put it in radial-side form

```text
C=[L,L+1]×[−1/2,1/2],
R²=(L+1)²+1/4,       L=sqrt(R²−1/4)−1>9/10.
```

The right side again cannot start an S path. The top and bottom sides
would give an endpoint point at height ±5/2. Thus the only side-normal
support is the inner side `x=L`.

## 2. The support alphabet and circle multiplicity

Call a selected contact E if its normal is a side normal of C; its
application point may be anywhere on that support side, including an
endpoint. Call it V otherwise; then the support is a vertex and the
normal is strictly inside that vertex's normal cone. This convention
assigns every boundary normal to E and avoids losing shared-side
endpoint forces.

A square in the present radius window has at most two circle vertices.
If there are two they are adjacent and its center is normal to their
side. Three circle vertices would force the square's circumcenter to
be the disk center and R=1/sqrt(2). Two opposite circle vertices with
the other two inside imply the same circumcenter situation. A circle
vertex cannot be shared with another square, by the reviewed circle
contact lemma. Hence neither P contact is a circle vertex.

For one circle vertex put

```text
Z=(X,Y),       I=(X−1,Y−1),
J=(X−1,Y),     K=(X,Y−1),       X,Y>1/2.
```

The possible V contacts are I,J,K. Their outward force signs are
respectively `(−,−)`, `(−,+)`, and `(+,−)`, with both entries strict.
The possible E directions are left and down. Force balance requires
their positive weighted sum to equal `−lambda(X,Y)`, `lambda>0`.

Up to exchanging C's two axes and interchanging A,B, exactly the five
unique-circle rows below survive these sign conditions and the distinct
contact requirement. The two radial-side rows in Section 4 finish the
central split. These are necessary forms. The radial R-VE row is excluded
below by an existing clearance lemma. The entire U-VE-I row is now excluded
by [INCIDENT_SIDE_SOURCE_SS_EXCLUSION.md](INCIDENT_SIDE_SOURCE_SS_EXCLUSION.md),
which also permits extra contacts at the endpoint bodies. Other rows still
need completion or exclusion arguments.

The further shared exclusions now remove all U-VE-N and U-VV-O forms:
[nonincident vertex/side theorem](NONINCIDENT_SIDE_SOURCE_EXCLUSION.md)
and [opposite-vertex theorem](OPPOSITE_VERTEX_SOURCE_EXCLUSION.md). Both
allow arbitrary far-endpoint contacts and any two transmission widths at
least one. The remaining LSLSLSS central families are U-EE, U-VV-A, and
radial R-VV with mixed or two-vertex SS endpoint support. The historical
seven-row table below remains the exhaustive starting classification.

## 3. The five unique-circle rows and their exact identities

All forces displayed here are outgoing from C. Their total torque about
Z is zero, since the positive circle force is applied at Z.

| Row | Contacts | Outgoing forces | Necessary identities |
| --- | --- | --- | --- |
| U-EE | `(X−1,eta Y)`, `(eta X,Y−1)` | `(−lambda X,0)`, `(0,−lambda Y)` | `0<eta≤1`; both points belong to their displayed sides |
| U-VE-I | I and `(X−1+t,Y−1)` | `(−u,−v)`, `(0,−z)` | `0<t≤1`, `u=lambda X`, `v+z=lambda Y`, `t z=lambda(Y−X)`, `u−v=(1−t)z≥0` |
| U-VE-N | J and `(X−1+t,Y−1)` | `(−u,v)`, `(0,−z)` | `0<t<1`, `u=lambda X`, `z=lambda Y/t`, `v=(1−t)z` |
| U-VV-A | I and K | `(−u,−v)`, `(w,−z)` | `v=lambda X`, `z=lambda(Y−X)>0`, `u=v+w` |
| U-VV-O | J and K | `(−u,v)`, `(w,−z)` | `w=v>0`, `u=w+lambda X`, `z=v+lambda Y` |

Every lower-case force component in the table is strictly positive.
Thus U-VE-I and U-VV-A imply `Y>X`.

For U-EE, the torque equation is `X y=Y x`, giving the common parameter
eta. Since at least one of X,Y exceeds 1 in the radius window, membership
in the corresponding inner side gives eta>0. Side membership gives
eta≤1. This includes all boundary application points.

For U-VE-I, the I force contributes torque `v−u` about Z, and the E
force contributes `(1−t)z`. Force balance gives the displayed identities.
Coincidence with I excludes t=0; t=1 remains allowed.

For U-VE-N, the J force contributes `−v` and the E force contributes
`(1−t)z`. Since `z−v=lambda Y>0` and v>0, necessarily `0<t<1`.

For U-VV-A the two torques are `v−u` and w, yielding `u−w=v`.
For U-VV-O they are `−v` and w, yielding w=v. Combining with force
balance gives the last two rows.

Exhaustiveness is short: two E directions must be left and down, since
parallel directions are excluded. One V and one E can use I with either
inner side, or J with the bottom side, or its axis exchange. The remaining
incident pair J/left has nonnegative total vertical force, and K/bottom
has nonnegative total horizontal force. Two distinct V contacts are
either adjacent along an inner side, or the opposite pair J,K.

## 4. The two radial-side rows

Use the radial-side coordinates of Section 1. The two geometric circle
vertices are `(L+1,±1/2)`, with coefficients `lambda_+,lambda_-≥0`
and positive total. Define

```text
F=(lambda_++lambda_-)(L+1)>0,
G=(lambda_+−lambda_-)/2,
|G|≤F/[2(L+1)].
```

Only the inner vertices `P_+=(L,1/2)` and `P_-=(L,−1/2)` can be V.
Only the inner side can be E. Two E directions would be parallel; two
contacts at one vertex were already excluded. Reflection in the horizontal
axis leaves precisely these rows:

| Row | Contacts | Outgoing forces | Necessary identities |
| --- | --- | --- | --- |
| R-VE | `P_+`, `(L,h)` | `(−u,v)`, `(−w,0)` | `u,w,v>0`, `−1/2≤h<0`, `u+w=F`, `G=−v`, `L v+u/2+h w=0` |
| R-VV | `P_+`, `P_-` | `(−u,v)`, `(−w,−z)` | `u,v,w,z>0`, `u+w=F`, `z−v=G`, `(u−w)/2=L G` |

For R-VE, torque about the disk center immediately forces h<0.
Membership in the inner side gives h≥−1/2. In particular
`w≥u+2Lv>u`; the boundary h=−1/2 is retained. For R-VV, force and
torque give the displayed equations directly. Neither row assumes the
two circle coefficients equal or strictly positive individually.

**R-VE is impossible.** The existence of the SS path alone implies
`R²≥17/4`: the reviewed cap theorem at midpoint offset 1 has nonnegative
height numerator `sqrt(R²−4)−1/2`. Thus the present radial C has
`1≤L<17/16`. The inner-side S endpoint contains `(L−1,h)`, whose norm
is below 9/16. Every point of its unit square then has norm less than
`9/16+sqrt(2)<2<R`, contradicting that endpoint's positive circle load.
This is exactly the horizontal-S clearance argument already proved in
[SS_PATH_RADIAL_SIDE_SIDE_EXCLUSION.md](SS_PATH_RADIAL_SIDE_SIDE_EXCLUSION.md)
and [SS_PATH_PARALLEL_EXCLUSION.md](SS_PATH_PARALLEL_EXCLUSION.md), reused
with the SS radius lower bound. Therefore a surviving radial C must be
R-VV. Its E/E SS-endpoint subcase is now also excluded in
[RADIAL_CENTRAL_SS_SIDE_ENDPOINTS.md](RADIAL_CENTRAL_SS_SIDE_ENDPOINTS.md);
the mixed and V/V SS supports remain open. More generally, wherever an SS path exists, this same argument
forbids a radial-side loaded body from having a side-normal single-S
path to another loaded body.

## 5. SS endpoint restrictions remain independent of the central row

Put the SS direction horizontally and its endpoint support lines at
`x=−b` and `x=a`, where `a+b=2`. The endpoints have E or V support in
the same sense as above, independently of whether their geometric circle
feature is a unique vertex or an outer side with two circle vertices.
All four labeled E/V pairs and all circle-load splits must be retained
unless a further argument excludes them.

The width-two cap theorem gives

```text
15/16<a,b<17/16,
|y_A|+|y_B|<125/288,
horizontal square widths <19/16.
```

When both SS supports are V, the exact lemma
[DOUBLE_SIDE_ENDPOINT_CHIRALITY.md](DOUBLE_SIDE_ENDPOINT_CHIRALITY.md)
forces their common-height contact vertices to have the same vertical
sign relative to their own centers. This geometric restriction is
available for every width-two path in any remaining signature; it does
not depend on the present three-loaded component.

## 6. Which old local arguments transfer

The support facts and force/torque identities from C09–C17 remain valid
whenever their stated circle multiplicity and support hypotheses hold.
The following conclusions do not transfer automatically:

* Separating the projections of A and B only proves that they cannot
  touch. Here their required distance is 2, so that separation is
  compatible with the component.
* A proof based on direct A–B force transmission or on a direct loaded
  neighbor cannot replace that edge by an SS path without redoing the
  application-point and torque argument.
* A unique-circle endpoint calculation cannot discard radial-side
  endpoints. The numerical seven-body candidate uses positive splits
  between both circle vertices at both SS ends.

The shared completion criterion in
[FINITE_CENTER_COVER_CAPACITY.md](FINITE_CENTER_COVER_CAPACITY.md) can be
applied after uniform center regions are derived from any combination
of these necessary forms. The goal is a finite family of capacity
certificates valid over all orientations and transmitter slides in each
family. No such complete family is claimed by this normalization note.

## Radial circle-multiplicity refinement, 2026-10-31

The reviewed [radial transmission-angle theorem](RADIAL_SOURCE_TRANSMISSION_ANGLE.md)
excludes radial central C whenever either SS endpoint is also radial-side.
Thus the remaining R-VV family has unique circle vertices at both SS
endpoints, with mixed or two-vertex SS supports; E/E remains excluded by
the earlier radial-central theorem. This refinement changes no whole-case
status.

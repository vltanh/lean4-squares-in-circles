# The entire five-body fan positive component is excluded

**Status: complete hand graph-family assembly; root and separate independent
full assembly audits passed.** Work in the declared window
\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\tag{1}
\]
for the selected physical positive certificate of a nine-unit-square
packing. All actual zero-stress contacts and all four squares outside
the five-body component remain part of the physical packing.

**Theorem.** The selected positive body graph cannot be the fan over a
four-vertex path:
\[
                 Hu_i\ (1\le i\le4),\qquad
                 u_1u_2,\ u_2u_3,\ u_3u_4.
\tag{2}
\]
This excludes the whole fan graph, for every positive-circle-load mask,
physical one-/two-circle-corner mask, side owner, free point normal and
actual shared-side application mean. It needs no secondary minimizer
and no completion-square motion or independent pocket assumption.

## 1. The full graph and load cover

`FIVE_BODY_BICONNECTED_REDUCTION.md`, Section4.3, gives the complete
initial load cover. The endpoints u_1,u_4 are positive degree-two
triangle tips and are loaded. H is unloaded and physically clear.
The only initial possibilities are both endpoints plus one inner
path body, or all four path bodies loaded.

`NO_UNLOADED_DIAMOND_HUB.md`, Section6, excludes both three-load
possibilities. For example the exact positive degree-three body u_2
has neighbors H,u_1,u_3, and its neighbor H touches both of the other
neighbors. The radius-free selected-star theorem forces u_2 to be
loaded. It likewise forces u_3 to be loaded. Thus the entire remaining
graph has
\[
                    H\text{ unloaded and physically clear},
              \qquad u_1,u_2,u_3,u_4\text{ loaded}.
\tag{3}
\]
Only u_1,u_4 have positive degree two. The two inner path bodies
retain exact positive degree three throughout the arguments below.

Summing the five actual body force equations gives zero total circle
resultant of these four path bodies. Each resultant is a nonnegative
combination of its physical circle corners with positive total weight.
Individual corner weights may vanish. Physical circle contacts of
other squares, when their stress weights are zero, are not discarded.

## 2. One permitted certificate for the whole endpoint cover

Use the existing simultaneous strict/nonradial point-normal convention,
the matched four-junction choices, physical uncrossing and the already
compatible `GENERAL_FIXED_TIP_NORMAL_SELECTION.md`. All relevant
ordered physical tips are prelisted before extracting multipliers.
There is no change of a point normal after a certificate is obtained.

The fixed-tip selection applies to a physical unique-corner degree-two
endpoint when both of its actual pair intersections are singleton
points. Its coincident radial-D exception cannot occur with the
endpoint's physical boundary neighbor: the inner radial-D point has
norm exactly R-sqrt(2), whereas a point shared by two boundary units
has strictly larger norm. The selection does not freeze a shared mean.
Those shared alternatives are treated explicitly below.

All the endpoint-family exclusions use this same permitted certificate.
The subsequent force, torque and metric arguments introduce no new
normal choices. In particular the physically radial two-corner free
endpoint is handled directly, including its individual zero-weight
limits, rather than being relabeled as a physical unique-corner tip.

## 3. The two endpoint normals cannot have equal ownership status

Call an endpoint H-owned when its actual normal is a side axis of H.
A shared H/tip side is included. The two complete results are:

* `FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md`: at least one endpoint
  must be H-owned. The family in which **neither** is H-owned
  is impossible. Its full cover includes two tip-owned singletons,
  unique free endpoints opposite actual shared boundary sides, and
  physical radial free endpoints. The exact degree-two endpoint and
  full hub equations retain every inner mean and degree-three force.
* `FAN_HUB_OWNED_ENDPOINT_EXCLUSION.md`: the family in which **both**
  are H-owned is impossible. Equal, opposite and perpendicular H axes
  are exhausted, including all actual endpoint means. The last case
  contradicts the whole-path resultant angle using only the two genuine
  endpoint equations.

Consequently a remaining fan would have exactly one H-owned endpoint.
Reverse the path if necessary so it is Hu_1. This is an actual graph
symmetry preserving the endpoint and inner degree roles.

The complete common domain is recorded in
`FAN_ENDPOINT_OWNER_REDUCTION.md`. For geometric coordinates one may
write
\[
 H=[0,1]^2,\qquad P=(p,1),\quad n_1=e_y,\quad0<p\le1,
 \qquad Q=(0,0),\quad n_4=(-a,-b),\quad a,b>0.
\tag{4}
\]
The true circle origin is separately retained in those coordinates.
The first contact may be an entire shared side, with P any actual
mean. The second contact is a single H vertex. The strict point-only
convention makes it either tip-side-interior owned or free in both
vertex cones; no side-axis endpoint of a free cone is silently added.

## 4. The three complete mixed families are all excluded

### 4.1. The other endpoint is tip-owned

If Q lies in the relative interior of a u_4 side,
`FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md` excludes the entire family.
It retains both physical circle masks at each endpoint and the
whole Hu_1 side-mean interval, including p=1 and its coincident
inner-port cases. The actual long hub arc and endpoint moments give
the center quadrants. A general width bound at u_1 and the exact
tip-owned angle/radius bound at u_4 make the unit height separation
strictly insufficient over the full coupled angular domain.

### 4.2. The other endpoint is free with one physical circle corner

If Q is a free u_4 vertex and u_4 has exactly one physical circle
corner, the fixed-tip selection removes a singleton u_3u_4 contact.
The remaining positive-length shared u_3u_4 side, with every actual
mean, is excluded by
`FAN_UNIQUE_FREE_SHARED_ENDPOINT_EXCLUSION.md` after reversing labels.

That proof keeps the full circle-mask transition of the internal
shared neighbor. The physical shared-side offset is exact, the full
hub force and torque bound the opposite actual H-side parameter, and
the complete circle equations force that H-owned application P to
have norm less than11/20. Since P belongs to its loaded boundary tip,
its norm must be at least R-sqrt(2)>11/20. Both possible opposite
H-owned sides are covered. No equation is imposed on the internal
neighbor as if it had degree two.

### 4.3. The other endpoint is free with two physical circle corners

The last possible physical mask is radial S, with two circle corners.
`FAN_HUB_OWNED_RADIAL_FREE_ENDPOINT_EXCLUSION.md` excludes the entire
family. Its local routing uses only the radial endpoint's degree-two
equations and the actual contact triangle: its two contacts lie at
the distinct radial inner vertices. It then retains the actual
Hu_1 side mean, obtains the genuine clockwise port and center order,
and uses the exact radial endpoint height in the complete angular
comparison. Both circle weights and either zero individual endpoint
remain included.

Every side feature of the non-H-owned endpoint belongs to exactly one
of these three physical alternatives. Thus they exhaust (4), and each
gives a contradiction.

## 5. Whole fan closure and exact parent scope

Section1 covers every positive load mask of the fan graph. Sections3--4
cover every actual endpoint owner, mean and physical corner mask under
the same permitted certificate. Their contradictions are at the core
level: the four arbitrary additional squares were never removed,
translated, assigned fixed orientations or assumed to occupy separate
pockets. No secondary minimizer is used.

Therefore the **entire five-body fan graph is excluded** in (1).
Together with `FIVE_CYCLE_POSITIVE_COMPONENT_EXCLUSION.md` and the
complete graph reduction, the only remaining graph family inside
C1.5.b0 is the house, with its full end-triple, middle-triple and
four-load domains still requiring their own whole exits. The fan's
degree-four hub is not replaced by the house's degree-three hub by
silently deleting a spoke.

This assembly does not close C1.5.b0, any larger coarse graph cell,
or the whole nine-square theorem. Those obligations remain separately
recorded. The result here is a complete graph-family exclusion, not
a numerical pose search, a partial radius interval, a Lean build or
a CI outcome.

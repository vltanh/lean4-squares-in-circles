# Independent review of closed small stress graph classes

The `n8_lessons` research agent independently reviewed
`FOUR_PATH_ANGULAR_CLASSIFICATION.md` and
`CLOSED_STRESS_GRAPH_FAMILIES.md`, and `LEAF_NEIGHBOR_UNLOADED.md`.
This review checks their mathematical
arguments given the stated independently certified universal lower bound
`q>9/2`; it does not recheck that separate certificate.

**Conclusion: pass for the explicitly stated graph classes.**

For the four-vertex full-angle stress path with unloaded internal vertices,
center balance makes all three selected normals and all aggregate edge weights
equal along the path. Every edge has a parallel owner, so a nonparallel body
owns neither incident edge and has a unique smooth support vertex in that
direction. I checked the internal angular derivative and both endpoint
calculations. A singly loaded nonparallel endpoint contributes `beta*h'`
from its corner and the same amount from its separator. A doubly loaded
endpoint on a frame axis gives the stated strict nonzero angular derivative;
the sign follows from `rho>1/2`. Thus every remaining nonparallel frame is
diagonal, and adjacent diagonal frames are impossible.

The endpoint projection formulas follow from force balance and the farthest
corner signs. Summing the three exact contacts counts twice every body's
support width. I checked the three endpoint-type equations, the all-parallel
value `q=17/4`, and each exact radical comparison excluding a diagonal frame
under `U`. This classification uses angular stationarity and unloaded
internals; the additional leaf lemma below supplies that missing hypothesis
when it is applied to an arbitrary four-path.

The spanning-star enclosing disk bound uses actual shared points and the
unit-square diameter. The four-cycle estimate uses the quadrilateral midpoint
identity, the adjacent center bound `sqrt(2)`, and unit separation of opposite
centers. It gives squared enclosing radius `(9+2sqrt(14))/4<17/4` as stated.
The graph classification on four vertices is exhaustive: degree three gives
a spanning star, while a connected maximum-degree-two graph is a path or
cycle. Additional physical contacts are included in this classification.

The new leaf-neighbor lemma also passes independently. Its endpoint frame
classification is local and does not assume the neighbor unloaded. For a
diagonal leaf, the unique support corner is an actual shared point. For a
parallel leaf owning the separator, angular stationarity forces the convex
average of the neighbor support vertices to give the radial midpoint of the
leaf's contact face. Central symmetry puts that averaged point on the
neighbor's near face; the note correctly avoids assuming each support atom
itself is a physical contact point. The half-plane/diameter estimate then
excludes a circle point on the neighbor. If the neighbor owns the separator,
both frames are parallel; actual contact bounds their transverse center
offset by one, and the stated corner-norm estimate is strictly below `q`.
I checked both exact formulas for `q-r^2` and their strict rational margins.

Consequently every full-angle positive stress leaf has a circle-unloaded
neighbor. The two internal vertices of a four-path are therefore unloaded,
so the earlier angular classification now excludes every full-angle
four-vertex path. Together with stars, four-cycles, and the earlier smaller
core exclusions, this proves `5<=k<=11` for a retained connected full-angle
core. The separate fixed-frame certificate retains its weaker size bound;
discarding angular equations would invalidate this leaf-neighbor argument.
Larger cores and the sharp global eleven-square bound remain open.

Reviewed source hashes are recorded below.

- `FOUR_PATH_ANGULAR_CLASSIFICATION.md`:
  `23ca045832994edda5465d56bae8a4747490800af6e524108d15849e540bde17`.
- `CLOSED_STRESS_GRAPH_FAMILIES.md`:
  `52bf6e6e28e34c2cf2370b44713b5d26a1fcda300922cd78b580992d50814111`.
- `LEAF_NEIGHBOR_UNLOADED.md`:
  `303ed6525cb094213a95bcc673ac53f0fab5869a2a3d593f95210414f8284725`.

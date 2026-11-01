# A.2: exact square-pose propagation excludes 886 of the fixed 7,915 roots

**Unrestricted optimality and the full equality classification remain OPEN.**
The same positional cover and zero-based root IDs are retained. The certificates
in this continuation exclude **886 entire closed-Q roots**, including all 81
previous exclusions: **805 additional roots, 7,029 OPEN**. This is not a
percentage of proof effort. No remaining root is asserted feasible or easy.

The new constraints use the squares' actual corner-containment and
separating-axis geometry, not just distances between centers. All orientation
intervals are covered continuously, with closed endpoints. There is no angular
sampling assumption, fixed-Q-minus-epsilon extrapolation, or chosen stress.

The following is the hand derivation of the finite certificate's implication.
The complete integer tables are reconstructed by the supplied source and their
propagation rows are attached in `square_pose_certificate.json`. A separate
implementation reconstructs every compatibility edge and replays every row.
This is a computer-assisted result with an explicit mathematical soundness
proof, **not yet the requested complete compact hand proof of optimality**.
No separate human review, Lean, Lake or CI is claimed.

## 1. Inputs and the unchanged global cover

Use Q=1105/256. The previous manuscript
`HEXAGON_ROOT_COVER_AND_FIRST_EXCLUSIONS.md` proves that every physical packing
at q<=Q has, after a common Euclidean symmetry and relabeling, a representative
in one of 7,915 canonical nine-cell subsets of the nineteen-hexagon cover.
The centers satisfy |c|<91/60 and pair distances at least one.

For each of the two meshes below, subdivide the same hexagons into closed
triangles as in that source. An integer point (X,Y) denotes the physical point

    (49/(200m)) (X, sqrt(3)Y).

Retain a triangle whenever its exact minimum squared norm is at most
(91/60)^2. The equality case is retained; the only discarded triangles cannot
contain any physical center. This gives 2,652 triangles for m=6 and 4,638 for
m=8. The earlier global cover itself is not subdivided or renumbered in the
progress ledger: these are internal certificate domains.

## 2. A complete rational orientation cover

A square's frame can be quarter-turned without changing the physical square.
Consequently its first axis may be represented by

    u(t)=((1-t^2)/(1+t^2), 2t/(1+t^2)),     0<=t<=1,
    v(t)=(-u_y(t),u_x(t)).

Indeed, choose the first axis in the closed first quadrant and put
`t=u_y/(1+u_x)`. The denominator is at least one. The parametrization and its
inverse follow by elementary algebra using u_x^2+u_y^2=1.

Cover [0,1] by the twelve CLOSED intervals [j/12,(j+1)/12], j=0,...,11.
Every actual square orientation is represented, including both ends of every
interval. This is a cover of continuous angles, not twelve tested angles.
Quarter-turning this frame is not a physical movement of an individual square.

The component a(t) decreases and b(t) increases on [0,1]. The two component
ranges on each interval are therefore determined by its rational endpoints.
All endpoint vectors have rational coordinates.

## 3. Exact outward arithmetic and unary pruning

Let D=2^20. Replace each rational endpoint coordinate by its floor/ceiling at
scale D. For triangle y-coordinates use the rational enclosure

    1732050807/10^9 < sqrt(3) < 1732050808/10^9.

Both inequalities are verified by squaring positive rationals. Take the minimum
and maximum of the two products when the coordinate is negative. Thus each
physical triangle vertex has a rational enclosing rectangle with integer
coordinates divided by D. Its three vertex rectangles enclose the triangle's
convex hull. Let B_T be their common coordinate bounding rectangle.

A state is a retained triangle T together with one of the twelve orientation
intervals. The following are the only unary deletions.

**Corner test.** For signs s,t in {-1,+1}, the doubled actual corner is

    (2x+s a-t b, 2y+s b+t a).

Interval arithmetic on B_T and the axis component intervals encloses this
corner. The minimum of z^2 over an interval [l,h] is
`max(0,l,-h)^2`. Remove a state only if some doubled-corner rectangle has

    64 [min X^2 + min Y^2] > 1105 D^2,                       (1)

where X,Y are scaled integer coordinates. The strict comparison means every
q<=Q containment equality survives.

**Farthest-corner test.** With a true unit frame,

    max_corner |corner|^2 = |c|^2 + 1/2 + |c.u| + |c.v|.     (2)

Minimize |c|^2 over T exactly: either the origin is in T, or the minimum lies
at the clipped perpendicular projection onto one of its three edges. In the
integer X,Y coordinates the metric is X^2+3Y^2, so this minimum is rational.
Round the result down at scale D^2. Obtain independent lower bounds on the
two absolute projections from interval products on B_T and the axis intervals.
Remove a state only when the resulting lower bound in (2) is strictly above Q.
Using independent lower bounds weakens the test but cannot discard a real pose.

After these tests the two covers contain:

| Mesh m | Position triangles | Continuous angle intervals | Retained pose states | Selected cores |
|---:|---:|---:|---:|---:|
| 6 | 2,652 | 12 | 29,542 | 35 |
| 8 | 4,638 | 12 | 51,572 | 48 |

The two meshes are separate complete covers. A core uses one specified mesh;
there is no assumption that mesh 8 refines mesh 6 or that a proof transfers
between them automatically.

## 4. Exact necessary pair compatibility

### 4.1 Center distances

For triangles T,U, the largest squared distance occurs at a vertex pair:
maximize the convex squared distance first in one triangle and then the other.
For integer fine coordinates define

    delta((X,Y),(X',Y')) = (X-X')^2 + 3(Y-Y')^2.

Since physical squared distance is 2401/(40000m^2) times delta, a pair can be
retained only if

    2401 max_vertex_pairs delta >= 40000m^2.                (3)

Equality is retained.

### 4.2 Lower bound on the required separation width

Suppose the two frame angles belong to closed intervals I,J contained in
[0,pi/2]. A separating axis of either square requires

    2|n.(c_j-c_i)| >= 1+cos(delta)+|sin(delta)|,             (4)

where delta is the difference of the frame angles. The complete finite-axis
separation argument is in `UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md`.
It includes touching, parallel and corner-contact cases.

The function g(delta)=cos(delta)+|sin(delta)| is concave separately on
[-pi/2,0] and [0,pi/2]. Its minimum over the possible angle-difference interval
therefore occurs at a difference endpoint, or at zero if that is included.
The two difference endpoints come from opposite endpoints of I and J. At
rational endpoint frames (a,b),(A,B), the corresponding value is exactly

    aA+bB+|aB-bA|.

If I,J overlap, also include g(0)=1. Let g_IJ be the minimum of these exact
rational candidates. Set

    H_IJ = floor(D^2(1+g_IJ)).                              (5)

The producer also checks the other two endpoint combinations; concavity makes
this equivalent. The independent implementation uses only the two difference
endpoints and the optional zero. Both yield the same entire threshold table.

### 4.3 Upper bound on an available separator projection

The interval axis components put each possible u-axis in a rectangle and
each v-axis in its quarter-turned rectangle. Take the four vertices of each
rectangle, eight candidate coefficient vectors in total. For a coefficient
vector d in integer scale D and position triangle T, compute

    L_d(T) = min over the three vertex rectangles of d.p,
    U_d(T) = max over the three vertex rectangles of d.p,

in integer scale D^2. These are exact extrema of linear functions on rational
rectangles. They bound the projection of every point in T.

For a frame interval I define

    P_I(T,U) = max_d { U_d(U)-L_d(T), U_d(T)-L_d(U) }.        (6)

For fixed points, the projection is linear in the axis coefficients. Hence
its maximum over their rectangle occurs at a coefficient vertex. Combining
this with the vertex-rectangle bounds proves that (6) is an upper bound on
D^2|n.(c_j-c_i)| for every u- or v-axis n of a square in interval I.

Consequently retain a compatibility edge between states (T,I),(U,J) only if
both (3) and

    2 max(P_I(T,U), P_J(T,U)) >= H_IJ                       (7)

hold and the coarse cells differ. If physical squares realize the two states,
some actual axis satisfies (4), so (3) and (7) necessarily hold. An edge is
ONLY a necessary condition: it does not prove that any actual pair exists.

### 4.4 No floating-point or overflow premise

All scalar endpoints and norms use Fraction or unbounded integers. The vector
operations use int64 only after verifying every scaled vertex coordinate has
absolute value <=3D and every axis coefficient <=D. Projection magnitudes
are bounded by 6D^2 and projection differences by 12D^2. Even the conservative
corner calculation is bounded by 8192D^2<2^63. The fine-coordinate distance
products are also far below 2^63 for m=6 and 8. Thus these operations are
ordinary exact integer arithmetic, not unchecked machine-overflow arithmetic.

The independent graph builder constructs the mesh by horizontal lattice
triangles rather than six fans. It computes projection bounds by interval
midpoints/radii rather than endpoint sign selection. It reconstructs every
edge; the two complete graph hashes agree. It imports no new producer code.

## 5. A short soundness proof for propagation tables

Let a core specify a set C of occupied coarse cells. For each c in C initialize
D_c to all retained pose states belonging to c. An actual physical packing of
these squares selects one state in each D_c, and every selected pair is
compatible by Sections 1-4.

A propagation row chooses a source cell s and replaces every other domain by

    D_c <- {v in D_c : there exists w in D_s with edge(v,w)}. (8)

Inductively the actual state in c cannot be removed: its actual partner in s
has survived and supplies the required edge. Therefore, if a finite sequence
of rows makes any domain empty, no physical packing of that occupied-cell
pattern exists at ANY q<=Q.

This proves the interpretation of each certificate. The producer computes
(8) by a union of neighbor bitsets. The independent verifier checks it
candidate-by-candidate against the source domain, rechecking every reported
before/after count. It requires a real empty domain at the end. No timeout,
failed numerical search, or fixed positive radius gap is accepted as a proof.

### Example: a five-cell core closes in five propagation rows

For mask 143, the occupied cell IDs are 0,1,2,3,7 (the unchanged lexicographic
IDs in the hex-cover source). Using m=6, the full integer propagation table is:

| Source cell used | Remaining in cell 0 | Cell 1 | Cell 2 | Cell 3 | Cell 7 |
|---|---:|---:|---:|---:|---:|
| Initial domains | 535 | 1,340 | 581 | 1,356 | 560 |
| 0 | 535 | 783 | 581 | 835 | 560 |
| 7 | 535 | 783 | 581 | 292 | 560 |
| 2 | 535 | 237 | 581 | 292 | 560 |
| 1 | 158 | 237 | 191 | 292 | 560 |
| 0 | 158 | 237 | 191 | **0** | 560 |

Every entry is computed from the explicit integer tests (1)-(7), not from
sampling. The last entry proves the entire continuous five-square core
impossible, and hence excludes every nine-square root containing a physical
symmetry image of it.

For comparison, the previous center-only graph has a compatible five-state
assignment with triangle IDs 9,73,239,303,993 for these cells. This is a discrete
relaxation witness, NOT an actual square packing or a proof that the continuous
center-only problem is feasible. It shows that this exclusion is strictly
stronger than that earlier finite center-distance test.

## 6. The full certificate and transfer to the fixed root table

There are 83 selected cores: one uses 5 cells, six use 7 cells, seventeen use
8 cells and fifty-nine use 9 cells. They have 2,059 propagation rows in total.
The explicit masks and mesh choices are in `square_pose_core_list.json`.
The full rows and exact graph fingerprints are in `square_pose_certificate.json`.

For every one of the original 7,915 canonical roots, check whether it contains
a dihedral image of a proved core. When it does, record the family, core and
symmetry that exclude it. Otherwise record OPEN. The result is 886 excluded
roots, including all original 81, and 7,029 open roots. All IDs, masks and cell
lists are compared with the original manifest and left unchanged.

The fine angle grids need NOT be invariant under a sixty-degree rotation.
Transfer uses a common Euclidean isometry of the actual physical packing:
rotate/reflect a hypothetical packing containing the image back into the
proved core. Its arbitrary orientations are still covered by Section 2.
No unproved isomorphism of the finite pose graph is used.

The selected core set is not claimed to exhaust everything the relaxation
could prove. In particular, OPEN means only that these certificates do not
exclude the root. It does not mean that a discrete graph solution or an
actual physical packing was found.

## 7. Equality, boundary and corrupted-certificate controls

For each mesh the exact verifier locates the known oblique attaining packing
in the pose cover under all twelve dihedral symmetries. Every actual square's
unit frame and corner inequalities are rechecked in Q(sqrt(3)); all 432
selected pair edges survive. Canonical equality root 7820, mask 177242, remains
OPEN in the updated root manifest.

For each mesh it also checks 25 genuinely touching pairs, with t=0,1/24,...,1,
including every orientation-interval endpoint. These pairs have a shared side;
none may be removed by the weak-contact compatibility test. The verifier tests
all containing triangle/angle unary states, including shared mesh boundaries.

Deliberate corruptions must fail: removing the terminal propagation row,
changing a survivor count, naming a nonexistent source cell, marking the
known equality root excluded, omitting a global root, or changing a root mask.
These are regression controls, not replacements for the soundness proof.

## 8. Reproduction and remaining mathematics

From `research/nine/computer_assisted/`:

```sh
python make_hex_cover.py
python make_square_pose_certificate.py
python verify_square_pose_certificate.py --negative-controls
```

The producer and independent graph builder require NumPy for bounded integer
array operations. There is no general SMT solver, floating optimizer, Lean,
Lake or CI dependency. Full manifests/certificates are deterministic generated
artifacts included in the continuation archive; the repository has the complete
source, core list, hand derivation and actual execution reports.

**A.2 remains active.** The next obligations are the 7,029 original physical
root predicates still marked OPEN. They retain all continuous positions,
independent orientations and original separators. The two meshes above are
useful finite relaxations, not a guarantee that further uniform refinement
will prove sharpness. In particular, roots approaching the attaining family
will need a sharp all-q<Q inequality. A.3 globally, B.2/B.3 and the complete
hand/table manuscript C remain OPEN. No new roadmap or gate IDs are introduced.

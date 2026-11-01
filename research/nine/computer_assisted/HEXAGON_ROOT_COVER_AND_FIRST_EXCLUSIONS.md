# Unrestricted n=9: a complete 7,915-root cover and 81 exact exclusions

**Scope.** This is a proved finite positional cover of ALL nine-square packings
with squared containing radius q <= Q = 1105/256, followed by five exact
center-pattern exclusions. It is NOT the unrestricted optimality theorem.
The cover has **7,915 canonical roots: 81 EXCLUDED and 7,834 OPEN**.
Every OPEN root retains all nine independent frames, all 36 original corner
constraints and all 36 original pair-separation disjunctions.

This does not assume rows, common separating directions, a contact graph,
positive stresses, or a generic position. The two-direction draft is not used.
The cover is small enough to generate, inspect, and independently replay;
no assertion is made that each remaining continuous root is easy to solve.
A.1b's explicit exhaustive-cover obligation and A.1c's boundary accounting
are supplied below. A.2 has begun. A.3 globally, equality B and manuscript C
remain open. No separate human reviewer or Lean/CI verification is claimed.

## 1. Two elementary necessary inequalities

For a contained unit square with center c and orthonormal axes u,v, its largest
squared corner norm is

    |c|^2 + 1/2 + |c.u| + |c.v| >= |c|^2 + 1/2 + |c|.

Put rho=91/60. Direct rational arithmetic gives

    rho^2 + rho + 1/2 - Q = 31/57600 > 0.

The right side is increasing in |c|>=0. Hence every physical center satisfies

    |c| < rho.                                                   (1)

Each square contains the open disk of radius 1/2 about its center. If two
centers had distance <1, their midpoint would belong to both of these open
disks. Therefore disjoint square interiors imply

    |c_i-c_j| >= 1.                                              (2)

Only (1)-(2) are used in the five exclusions. They are necessary, NOT
sufficient, for packing squares. A compatible center pattern is never called
a feasible square packing.

## 2. Nineteen closed hexagons cover the entire center disk

Let s=49/100 and define the triangular lattice

    L(q,r) = (s/2)*(3q, sqrt(3)*(q+2r)),       q,r integers.

In coordinates p=(s/2)*(X,sqrt(3)*Y), let H be the closed hexagon

    |Y| <= 1,       |X+Y| <= 2,       |X-Y| <= 2.                 (3)

Its vertices are (X,Y)=(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1).
Each has physical norm s. Convexity gives |p|<=s throughout H and

    diam(H) <= 2s = 49/50 < 1,
    1 - (2s)^2 = 99/2500 > 0.                                   (4)

Write H(q,r)=L(q,r)+H.

### Cover of the plane

For any point p, a nearest lattice point L exists: the lattice is discrete
and squared lattice norms tend to infinity. Compare its distance with those
of the six neighbors having axial offsets

    (0,+/-1), (+/-1,0), (1,-1), (-1,1).

The six comparisons |p-L|^2<=|p-L-d|^2 reduce exactly to (3) for p-L.
Thus every plane point lies in a closed H(q,r). Ties are retained.

### Only nineteen lattice cells can be needed

Retain the cells with

    max(|q|,|r|,|q+r|) <= 2.                                    (5)

There are nineteen. Outside (5), one of |q|,|r|,|q+r| is at least 3.
Since

    q^2+qr+r^2 = (q^2+r^2+(q+r)^2)/2,

and the other two signed components sum to the negative of the largest one,
this integer quadratic form is at least 27/4 and therefore at least 7.
Consequently an outside lattice center has norm at least s*sqrt(21).
A point in its hexagon has norm at least s*(sqrt(21)-1). But

    21s^2 - (rho+s)^2 = 18277/18000 > 0,                          (6)

so this lower bound is larger than rho. No center satisfying (1) needs an
outside cell. This proves the nineteen-cell cover, including every boundary.

By (2) and (4), two different physical centers cannot belong to the same
closed cell. For each of the nine centers choose any containing cell. The
chosen cells are automatically distinct, even at shared cell boundaries.

## 3. Exact symmetry reduction, with no orientation restriction

The cell IDs are lexicographic in (q,r):

| q | r values, in order | Cell IDs |
|---:|---|---|
| -2 | 0,1,2 | 0,1,2 |
| -1 | -1,0,1,2 | 3,4,5,6 |
| 0 | -2,-1,0,1,2 | 7,8,9,10,11 |
| 1 | -2,-1,0,1 | 12,13,14,15 |
| 2 | -2,-1,0 | 16,17,18 |

Before symmetry there are binomial(19,9)=92,378 nine-cell subsets.
Rotation through 60 degrees and reflection across the physical x-axis act by

    R(q,r)=(-r,q+r),       J(q,r)=(q,-q-r).                       (7)

These are actual Euclidean symmetries of the disk and of all the squares,
not individual-square rotations. They give twelve cell permutations. Under
a reflection, reverse one frame axis when needed; the physical square is
unchanged and still has a positive orthonormal frame representation.

Represent a subset C by mask(C)=sum_{i in C} 2^i. Its canonical representative
is the smallest mask in its twelve-element orbit. The exact orbit table is:

| Orbit size | Number of canonical roots | Original subsets covered |
|---:|---:|---:|
| 2 | 6 | 12 |
| 3 | 12 | 36 |
| 4 | 2 | 8 |
| 6 | 403 | 2,418 |
| 12 | 7,492 | 89,904 |
| Total | **7,915** | **92,378** |

The producer enumerates unvisited orbits. The separate verifier enumerates
all complementary ten-subsets and canonicalizes each one. A third count
uses the cycle-length polynomial product(1+z^length) for each permutation:
its coefficient of z^9 counts fixed nine-subsets. The fixed-subset counts
are 92,378 for the identity, 0,20,126,20,0 for the other rotations, and
266,546,266,546,266,546 for the reflections. Their sum divided by twelve is
7,915. This checks the table without relying on the producer's enumeration.

**Cover theorem.** Every physical nine-square packing at q<=Q, after one
common rotation/reflection and a relabeling, has its i-th center in the i-th
cell of one of these 7,915 canonical subsets. All nine square orientations
remain arbitrary. The proof is Sections 1-3, not numerical sampling.

The cells are closed, so this is an overlapping cover rather than a claimed
disjoint partition. Overlaps cause no missing or invalid cases. A boundary
center may use any containing cell; no two physical centers can collide in
that assignment. All tangent and parallel physical configurations remain.

## 4. Operational root predicates

`emit_hex_root.py` appends exactly one root to the existing unrestricted
emitter. It uses nine independent frames and NO square-0-horizontal gauge.
That gauge must not be imposed on an already fixed positional root without
a new proof that the root is preserved.

For a center (x,y) assigned to cell (q,r), introduce the single shared
positive constant k with k^2=3. The six closed cell inequalities are

    +/-[200y - 49k(q+2r)] <= 49k,
    +/-[200kx + 200y - 49k(4q+2r)] <= 98k,
    +/-[200kx - 200y - 49k(2q-2r)] <= 98k.                       (8)

They follow by multiplying (3), translated by L(q,r), by the positive 49k.
No denominator can vanish and there is no sign choice hidden in (8).
Strict-Q mode retains the original strict corner bounds; closed-Q mode
retains the original weak corner bounds. All pair separations stay weak.

Each generated root has 37 real declarations (including the uniquely fixed
k), 137 assertions, all 36 original pair disjunctions, and 54 added cell
inequalities. Its polynomials still have degree at most two. A solution of
a root is a genuine solution of the original physical formula. Conversely,
every original packing has a representative in some root by the cover
 theorem. The root cover therefore reduces the problem, but does not solve
its continuous separator constraints.

## 5. A finite exact graph relaxation and its proof certificate

Subdivide each hexagon into six triangles from its center to neighboring
vertices. Divide each side into m=6 equal parts. This gives 6m^2=216 closed
small triangles per cell, 4,104 in total, without gaps.

Use integer fine coordinates for which a point (X,Y) represents

    (s/(2m))*(X,sqrt(3)*Y).

Squared physical distances are s^2/(4m^2) times

    D((X,Y),(U,V))=(X-U)^2+3(Y-V)^2.                              (9)

The minimum of X^2+3Y^2 over a closed triangle is obtained at the origin
when it is contained, or at the perpendicular projection onto one of the
three edges, clipped to that edge. All resulting values are rational.
Discard a triangle ONLY when its minimum exceeds

    4m^2*rho^2/s^2 = 3312400/2401.                              (10)

The equality case is retained. Exactly 1,452 triangles are discarded and
2,652 retained. The verifier constructs the mesh independently from
horizontal elementary triangles in the integer lattice X=Y mod 2, rather
than from the producer's six fans. Both construct exactly the same cover.

For retained triangles T,U in distinct coarse cells, keep a compatibility
edge whenever at least one vertex pair satisfies

    2401 D(vertex(T),vertex(U)) >= 1440000.                     (11)

This is a sound necessary test. For fixed y, |x-y|^2 is convex in x;
maximize first over T's vertices and then over U's vertices. Therefore the
maximum over T x U occurs at a vertex pair. If two actual centers in T,U
have separation at least 1, (11) must hold. Equality edges are retained.

It follows that centers occupying a set of coarse cells require a clique
choosing one retained triangle from every occupied cell. Failure to find
such a clique by EXHAUSTIVE finite enumeration proves the center pattern
impossible. Existence of a clique proves neither point nor square feasibility:
each edge can use a different pair of triangle vertices.

### Replay format and soundness

A proof node selects one unassigned coarse cell and branches over EVERY
triangle still available to it. After selecting triangle v, each remaining
cell domain is intersected with the compatibility neighbors of v. A terminal
is valid only if some remaining domain is empty. A state with no remaining
cells is a feasible discrete assignment, never a contradiction.

The certificate records all children. The verifier rejects a missing or
duplicate child, a forward/cyclic reference, a false empty-domain claim, and
unreplayed nodes. Child indices are smaller than their parent, so induction
on proof node index proves every accepted node has no compatible completion.
Together with (9)-(11), each accepted root excludes an entire continuous
center pattern. This is the mathematical implication of the certificate.

The producer uses bounded int64 operations for speed. The separate verifier
uses Python unbounded integers and Fraction only, and recomputes adjacency
rather than trusting a producer-supplied graph. There are no floating-point
proof comparisons and no general solver answer is used as evidence.

## 6. Five verified patterns exclude 81 canonical roots

A mask denotes the cells listed in Section 3. The five proved cores are:

| Core mask | Occupied cells | Newly excluded roots, in table order |
|---:|---|---:|
| 447 | 0,1,2,3,4,5,7,8 | 7 |
| 507 | 0,1,3,4,5,6,7,8 | 10 |
| 2255 | 0,1,2,3,6,7,11 | 36 |
| 4303 | 0,1,2,3,6,7,12 | 27 |
| 5559 | 0,1,2,4,5,7,8,10,12 | 1 |
| Total | Any symmetry image of these cores | **81** |

For each canonical nine-cell root, test whether it contains a dihedral image
of a listed core. If so, apply the core's center theorem to those actual
squares and exclude the whole root. Otherwise mark it OPEN. Each excluded
root records its specific core and symmetry. The last column is disjoint
incremental coverage, not the sum of overlapping individual orbit sizes.

The five core proofs have 6,416 proof nodes and 73,487 contextual visits.
All were replayed successfully. There are now **7,834 OPEN canonical roots**.
This count describes this fixed exhaustive cover, not a percentage of the
mathematical effort and not 7,834 known feasible configurations. No later
subdivision is silently included in this count.

## 7. Equality and negative controls

The known physical oblique witness has centers

    (x/2,1/16), x=-3,-1,1,3;
    (x,-15/16), x=-1,0,1;
    (+/-11/20,19/16),

with first axes (1,0) for the first seven and (99/101,20/101) for the last
two. The verifier independently checks its frames, all original corners,
and all original pair separations using rational arithmetic.

Its selected cell IDs are 1,5,14,17,3,8,12,6,15. Its canonical mask is
177242, root ID **7820** (zero-based), which remains OPEN.

The emitted-text tests use exact arithmetic in Q(sqrt(3)). All twelve
rotation/reflection controls pass closed-Q root formulas; strict-Q rejects
exactly the four attaining corner constraints. In total 24 emitted models,
114 closed cell vertices, and 19 outside-cell controls pass. The baseline
unrestricted emitter was transcribed into the working container and checked
against Git blob SHA 9139677c644b3d66f9e3db986f12a54b4321ec17 before testing.

The independent cover verifier rejects deliberate removal of a global root,
marking an unproved root excluded, omission of a proof child, and declaring
the nonempty root already contradictory. It also checks all three displayed
rational margins (1),(4),(6). These tests are regression controls; the cover
and certificate soundness arguments are the proofs, not sample counting.

## 8. Reproduction and exact remaining obligation

Run in this directory:

```sh
python make_hex_cover.py
python verify_hex_cover.py --negative-controls
python test_hex_root_emitter.py
python emit_hex_root.py --root 7820 --radius closed --output /tmp/n9-equality-root.smt2
python emit_hex_root.py --root 7820 --radius strict --output /tmp/n9-strict-root.smt2
```

Only the producer needs NumPy. The certificate verifier needs the Python
standard library only. Generated outputs are deterministic:

- `hex_root_manifest.json`: every canonical root and its exact current status.
- `hex_exclusion_certificate.json`: the full five-core decision forest.
- `hex_generation_report.json`, `hex_verification_report.json`,
  `hex_emitter_test_report.json`: actual execution reports.

The repository source and reports regenerate the manifest and certificate;
the continuation archive also contains the exact generated copies, pinned by
the SHA-256 values in the reports. The source proof above and two separate
implementations were written in this continuation. This is not a separate
human review or a kernel-checked proof.

**Next actual mathematical task: A.2.** Prove orientation-sensitive terminal
inequalities or exact certificate cores that exclude groups of the 7,834
remaining root predicates. Center separation alone is a relaxation and is
not claimed to be sufficient for sharp optimality. Retain all root labels
and closure evidence; do not replace this finite cover by a fresh vague
roadmap. Near-equality roots, including 7820, require a sharp all-q<Q
argument rather than a fixed positive numerical gap. Full equality B and
the final hand/table presentation C are still OPEN.

## Methodological reference

Center-tiling constraints in rigorous square-in-circle searches were used by
T. Montanher, A. Neumaier, M. C. Markot, F. Domes and H. Schichl,
“Rigorous packing of unit squares into a circle,” Journal of Global
Optimization 73 (2019), 547-565, DOI: 10.1007/s10898-018-0711-5.
The nineteen-cell constants, orbit table and five certificates above are
derived and checked here; no n=9 conclusion is imported from that paper.

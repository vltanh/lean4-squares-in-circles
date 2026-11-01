# A.2 — disk-support contraction: 3,100 additional fixed-root exclusions

**Global n=9 optimality, complete equality classification and the final full
hand/table proof remain OPEN.** The original 7,915 canonical root IDs are
unchanged. This continuation adds **3,100 exclusions** to the previous 886:
**3,986 EXCLUDED, 3,929 OPEN**. These are counts in one fixed exhaustive cover,
not a percentage of proof effort and not a claim that open roots are feasible.

The new certificate has **176 selected cores and 4,182 propagation rows**.
The verifier also replays all 83 previous square-pose cores. A particularly
useful four-cell obstruction excludes 2,023 canonical roots, including 1,351
that were previously open, using a four-row propagation table.

The mathematical improvement is a containment contraction, not merely more
sampled poses: an exact support formula bounds every possible center of a
contained square over each entire closed orientation interval. Two independent
geometric implementations reconstruct the resulting rational polygons and every
compatibility edge. See `disk_support_verification_report.json` for execution
status, complete counts and fingerprints. No separate human review, Lean,
Lake or CI verification is claimed.

## 1. Exact support of the admissible-center region

Put

    Q=1105/256, R=sqrt(Q), rho=sqrt(Q-1/4)-1/2=sqrt(1041)/16-1/2.

For a square with a fixed orthonormal frame u,v, its allowed centers c satisfy

    (|c.u|+1/2)^2+(|c.v|+1/2)^2 <= Q.                         (1)

This is exactly the farthest-corner condition, not a relaxation. All four
corners lie in the disk iff (1) holds; convexity then contains the whole square.
Let K denote this closed center region. For a nonzero vector n write

    a=max(|n.u|,|n.v|), b=min(|n.u|,|n.v|), ell=|n|.

Thus a>=b>=0 and a^2+b^2=ell^2. Its support function is exactly

             { rho*a,                    if 2R*b <= ell,
    h_K(n) = {                                                   (2)
             { R*ell-(a+b)/2,            if 2R*b >= ell.

The formulas agree at the boundary, which is included in both cases.

### Proof of (2)

By the sign and coordinate-interchange symmetries of (1), maximizing n.c
reduces to maximizing a*x+b*y over x,y>=0 with

    (x+1/2)^2+(y+1/2)^2<=R^2.

Set X=x+1/2 and Y=y+1/2. The unconstrained maximum over the disk is at
(X,Y)=R(a,b)/ell. If 2Rb>=ell, both coordinates are at least 1/2, so this
point is feasible and gives the second expression in (2).

Otherwise the constraint Y>=1/2 is active. For Y>=1/2, the objective before
subtracting (a+b)/2 is a*sqrt(R^2-Y^2)+b*Y. It is nonincreasing from Y=1/2:
its derivative is b-aY/sqrt(R^2-Y^2), which decreases with Y, and its value
at 1/2 is nonpositive precisely when 2Rb<=ell. Thus Y=1/2 and
X=sqrt(R^2-1/4), giving rho*a. This point is feasible. At 2Rb=ell, direct
substitution makes both expressions equal. This proves the exact formula.

For example, in an aligned frame,

    |c_x| <= sqrt(1041)/16-1/2,
    c_x+c_y <= sqrt(2210)/16-1.

These are genuine joint four-corner restrictions. They are not inferred from
one selected tangent corner or from a stress certificate.

## 2. Maximization over a whole orientation interval

Use the same complete frame parametrization as the earlier pose certificate:

    u(t)=((1-t^2)/(1+t^2),2t/(1+t^2)), v(t)=(-u_y,u_x), 0<=t<=1.

Quarter-turning the frame does not move the physical square, so every square
has such a representation. The intervals [j/k,(j+1)/k] are CLOSED, with k=12
or 24. No intermediate angle is omitted.

Fix n and let delta in [0,pi/4] be its angular distance from the nearest frame
axis. Dividing (2) by ell gives

              { rho*cos(delta),                      if 2R*sin(delta)<=1,
    f(delta)={
              { R-(cos(delta)+sin(delta))/2,          otherwise.

Both pieces are nonincreasing on [0,pi/4], and they agree at their join.
Consequently the maximum of h_K(n) over an orientation interval occurs at
an endpoint, or at an alignment of n with a square axis inside the interval.
The intermediate diagonal alignment is a minimum, not an omitted maximum.

Every endpoint frame is rational. Alignment inside the interval is checked
by two determinant signs after quarter-turning n into the first quadrant.
For an alignment, the support is rho*ell. This finite candidate rule is an
EXACT maximization over the entire continuous orientation interval.

At an endpoint the branch condition has the rational form

    1105*b^2 <= 64*ell^2.                                    (3)

Thus no numerical angle comparison is needed.

## 3. Rational outer halfplanes for every state

Let D=2^20 and take the following fixed set of 48 integer normal directions:

    N={(p,q) in Z^2: |p|,|q|<=4 and gcd(|p|,|q|)=1}.

For every orientation interval I and n in N, compute an integer B_I(n) with

    B_I(n)/D >= max_{theta in I} h_{K_theta}(n).               (4)

The maximization is the finite candidate rule of Section 2. Square roots
are enclosed by integer square roots, with outward rounding. For example,
the first branch in (2) is bounded above at a rational endpoint by

    ceil(D*sqrt(1041*a^2/256)) - floor(D*a/2).

The second branch is bounded above by

    ceil(D*sqrt(1105*ell^2/256)) - floor(D*(a+b)/2).

At alignment the corresponding upper integer is

    ceil(D*sqrt(1041*ell^2/256)) - floor(D*ell/2).

The last floor is obtained by an integer square root as well. For any
nonnegative rational z, floor(sqrt(z)) is isqrt(floor(z)); comparison of its
square with z gives the exact ceiling. All denominators are positive.

The implementation additionally takes the minimum with the older valid bound

    ceil(D*R*ell) - floor(D*min_{theta in I} h_square_theta(n)). (5)

This minimum cannot invalidate (4). The square support minimum in (5) is
attained at an endpoint or an axis alignment: between sign changes it is a
positive concave sine/cosine expression. Both complete halfplane arguments
are retained; there is no assumption that rounding preserves an unproved
ordering between the two integer bounds.

For a state whose center lies in a position triangle T and whose frame is in
I, every actual center therefore satisfies all 48 closed inequalities

    n.c <= B_I(n)/D.                                        (6)

### Exact rational polygon construction

As in the original pose model, enclose sqrt(3) between

    1732050807/10^9 < sqrt(3) < 1732050808/10^9,

verified by squaring. Each vertex of T then has a rational outward rectangle
at scale D. Let T+ be the convex hull of those vertex rectangles. It contains
T, including its boundary. Define

    P(T,I)=T+ intersect {c: all inequalities (6) hold}.        (7)

Every physical center in state (T,I) lies in P(T,I). An empty P therefore
excludes that entire state, uniformly for every q<=Q. A nonempty P is retained,
including when it is only a line segment or a point.

The producer clips the initial convex polygon successively by halfplanes.
The independent implementation instead derives the initial supporting lines,
enumerates pairwise line intersections, and retains every feasible one.
The equivalence follows from bounded polytope geometry: a nonempty bounded
intersection of finitely many closed planar halfplanes has a vertex; at a
vertex two independent active lines meet. This remains true for a segment
or a singleton. Conversely every retained feasible intersection belongs to
the intersection. Their convex hull is precisely that intersection.

Line intersections are checked using integer numerators and a positive
integer determinant, without floating arithmetic. The two implementations
agree on every resulting polygon enclosure and every removed state.

## 4. Stronger pair compatibility, same complete physical interpretation

Round each vertex of a nonempty P(T,I) outward to a rational rectangle at
scale D. The convex hull of these rectangles still contains P(T,I). It need
not itself satisfy (6); this extra outward enlargement is deliberately safe.

For any candidate axis-coefficient vector d, compute the smallest and largest
values of d.c over these rectangles. The axis coefficients range over the
same outward rectangles used by the original pose graph. Linear extrema in
the coefficients occur at their rectangle vertices, so eight coefficient
vectors suffice for the u- and v-axes of one orientation interval.

Apply the original exact necessary separating-axis test with these contracted
position enclosures. Retain an edge only when the new test allows a separator
AND the previous graph retained that edge. Every actual pair still has its
actual separator represented, so no actual pair can be removed incorrectly.
The complete lower support-width bound and its endpoint/alignment proof are
unchanged from `SQUARE_POSE_CERTIFICATES.md` Sections 4.2-4.3.

The graph retains the original pose-state IDs. Removed states have empty
neighborhoods and are removed from their cell domains. No positional root is
renumbered or replaced, and no global frame gauge is imposed on a fixed root.

### Arithmetic bounds

All polygon calculations use unbounded Python integers and Fraction.
Every outward position coordinate is checked to have absolute value at most
3D, and each axis coefficient has absolute value at most D. Hence a projection
has magnitude at most 6D^2, a projection difference at most 12D^2, and its
double at most 24D^2<2^63. The midpoint/radius implementation obeys the same
bounds. NumPy int64 operations used to construct the graph are therefore
ordinary exact integer operations, not unchecked floating or overflow tests.

The previous corner and center-distance bounds are unchanged. The two old
geometry builders have only had their allowed angle-bin argument extended
from 12 to {12,24}; their k=12 outputs retain the previous graph fingerprints.
Their existing formulas already cover general rational interval endpoints.
No numerical optimizer or general solver result is a premise.

## 5. Propagation soundness and the four-cell theorem

For an occupied cell c, let D_c be its full retained state domain. A physical
packing chooses one state from each D_c, with every chosen pair compatible.
Using another occupied cell s, the certified operation is

    D_c <- {v in D_c: some w in D_s is compatible with v}.    (8)

Its actual state cannot be deleted: its actual partner in s supplies the
required edge and has survived the earlier operations. Induction proves that
an empty domain after finitely many operations contradicts the physical
packing. This is the same inference rule as before; the geometric domains
are now stronger.

### Four-cell theorem

Use the unchanged coarse-cell IDs 1,2,6,11, or any common dihedral image of
them. Their axial coordinates are (-2,1),(-2,2),(-1,2),(0,2), respectively.
For s=49/100, each cell is the closed side-s regular hexagon centered at

| Cell | Hexagon center |
|---:|---|
| 1 | (-3s,0) |
| 2 | (-3s,s*sqrt(3)) |
| 6 | (-3s/2,3s*sqrt(3)/2) |
| 11 | (0,2s*sqrt(3)) |

**Four interior-disjoint unit squares in the disk q<=Q cannot have one center
in each of these four cells.** Their frames are independent and arbitrary.
The hypothesis is the stated four cells, not an assertion that four squares
cannot fit anywhere in the disk.

For mesh m=6 and k=12, the complete propagation certificate is:

| Source cell | Remaining in cell 1 | Cell 2 | Cell 6 | Cell 11 |
|---|---:|---:|---:|---:|
| Initial | 1,240 | 476 | 1,211 | 485 |
| 2 | 629 | 476 | 650 | 485 |
| 11 | 629 | 476 | 91 | 485 |
| 6 | 629 | 56 | 91 | 77 |
| 2 | **0** | 56 | 91 | 77 |

Every entry is reproduced from (3)-(8), the explicit finite triangle mesh and
closed orientation intervals. The last row proves the theorem. The counts
alone are not a proof without the stated domains, exact edge inequalities and
full replay of their integer tables. The supplied generator and separate
verifier reconstruct those tables; the four rows summarize their deductions.

The core mask is 2118. Checking its twelve physical symmetry images against
the unchanged canonical root table excludes exactly **2,023 roots**. Of these,
672 were already excluded and **1,351 are additional exclusions**. Square
orientations need not transform between identical finite angle grids: rotate
or reflect the actual hypothetical packing back into the proved core, then
use its complete orientation cover. No graph-symmetry assumption is made.

## 6. All selected certificates and stable root accounting

The explicit core list has:

| Position mesh m | Closed angle intervals k | Selected cores |
|---:|---:|---:|
| 6 | 12 | 3 |
| 8 | 12 | 7 |
| 6 | 24 | 166 |
| Total | | **176** |

There are 4,182 propagation rows. The selected cores range from four to nine
occupied cells. Redundant certificates were removed by comparing their exact
transfers to the fixed root set. This does not assert that the method or its
candidate search has exhausted every possible further exclusion.

Every root keeps its original ID, mask and cell list. A previously excluded
root retains a reference to its previous square-pose proof. A newly excluded
root names a new family, core and physical symmetry. A root with neither
proof is OPEN; a failed search, a time limit and numerical evidence cannot
change its status. This gives 3,986 excluded and 3,929 open roots.

The new independent verifier rechecks the original complete root enumeration,
all 83 prior square-pose cores, every new contracted geometry and compatibility
graph, all 4,182 new propagation rows, and every root transfer. The old and
new source models are reconstructed, not loaded from a trusted cached graph.
A.3 is nevertheless OPEN globally because 3,929 physical roots still lack
contradictions.

## 7. Equality, degenerate contacts and mutation controls

For each geometry family, the known oblique equality packing is located in
the new state cover under all twelve actual dihedral symmetries. Its original
unit-frame and corner inequalities are rechecked exactly in Q(sqrt(3)). Every
containing unary triangle/angle state remains and all 432 selected pair
edges survive. Canonical equality root 7820, mask 177242, remains OPEN.

The verifier also checks side-touching pairs at every angle-interval endpoint
and midpoint: 25 controls for each k=12 family and 49 for k=24. Each control
is a genuinely physical pair, not just compatible graph states. Additional
exact rational single-square tests use attaining corner configurations rotated
to every endpoint/midpoint and check all support halfplanes for each applicable
closed orientation interval.

Corruption controls include a missing terminal row, a changed domain count,
an inconsistent core mask, a false equality-root exclusion, an omitted root,
a changed root mask and altered support-domain or support-semantics fields.
The verifier must reject them. These are regression tests; Sections 1-6 give
the universal mathematical implication and do not infer it from sampling.

## 8. Reproduction and exact remaining task

From `research/nine/computer_assisted/`:

```sh
python make_hex_cover.py
python make_square_pose_certificate.py
python make_disk_support_certificate.py
python verify_disk_support_certificate.py --negative-controls
```

The continuation archive includes all generated inputs and outputs, so the
first two generators are unnecessary when those copies are already present.
The final verification uses no producer graph cache. Python and NumPy are
required; no new solver dependency or Lean compilation is needed.

The repository contains the full source, the explicit selected core list,
this proof, and the execution summary. The archive additionally contains the
full new certificate, the unchanged-ID updated root manifest, and the full
verification report. SHA-256 fingerprints in the report pin these artifacts.

**A.2 remains active.** The 3,929 open physical root predicates still retain
all continuous centers, independent orientations and original pair separators.
The current exclusions hold even at q=Q, so they cannot exclude roots that
contain attaining packings. Those roots require a sharp argument for q<Q,
not endless attempts to prove their closed-Q domains empty. Full equality
classification B.2/B.3 and the final global hand/table manuscript C remain
open. No new roadmap or gate IDs are introduced.

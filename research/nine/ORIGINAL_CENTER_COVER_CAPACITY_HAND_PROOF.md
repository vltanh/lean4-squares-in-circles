# A complete center-cover capacity theorem for the unchanged originals

November 3, 2026. This is a finite geometric terminal for a whole original
parent. It uses intervals already proved for all nine centers, then excludes
the entire possible center region of one named original. A cover with an
unproved terminal proves no parent exclusion.

## 1. Two orientation-independent physical facts

Every physical unit square contains its concentric open radius-1/2 disk.
Consequently distinct originals with disjoint open interiors have center
distance at least one. This includes physical contacts and all original
orientations.

Every original contained in the disk of squared radius Q=1105/256 also has
center norm strictly below rho=91/60. To prove this directly, take its own
orthonormal sides u,v and center c. The largest squared corner norm is

    ||c||^2+1/2+|c dot u|+|c dot v|
        >= ||c||^2+1/2+||c||.

If ||c||>=rho, monotonicity on nonnegative arguments would give a corner
squared norm at least

    rho^2+rho+1/2 = Q+31/57600 > Q,

which contradicts containment. Thus the strict center-radius conclusion
is valid even when the original corners have closed-Q bounds.

## 2. The quantified cover criterion

Let the same whole original caller imply

    x_j in [a_j,b_j], y_j in [c_j,d_j]   for every original j.

Fix a target original i. Its root rectangle is exactly

    B_i=[a_i,b_i] times [c_i,d_i].

Take a finite tree whose root is B_i and whose every internal node splits
one of its two coordinate intervals at its rational midpoint. Retain both
closed children, including their shared face. Suppose every terminal
rectangle B=[p,q] times [r,s] has one of these two certificates.

**A distinct original is necessarily too close.** There is an original
j different from i such that

    U=max((p-b_j)^2,(q-a_j)^2)
        +max((r-d_j)^2,(s-c_j)^2) < 1.               (1)

For every target center in B and every permitted center of j, the two
coordinate differences lie in [p-b_j,q-a_j] and [r-d_j,s-c_j]. A convex
square function attains its maximum over an interval at an endpoint.
Therefore their squared center distance is at most U<1. This contradicts
the original incircle separation, regardless of the actual position of j
within its whole-parent rectangle. No independently chosen pose of j is
used. The original frame of j remains unchanged and unrestricted.

**The target lies outside its center disk.** Let m([a,b]) be zero if
0 belongs to [a,b], and min(a^2,b^2) otherwise. Suppose

    L=m([p,q])+m([r,s]) >= rho^2.                    (2)

Every center in B then has norm at least rho, contradicting Section 1.
The weak comparison in (2) is justified by that strictly bounded physical
center radius. No positive reserve is required at this particular face.

These two tests cover all physical original orientations. They can use
different neighbor originals in different terminal rectangles. The same
original neighbor may witness many rectangles.

## 3. Why the entire parent is excluded

Assume a physical configuration satisfies the original parent and all its
already proved center intervals. Its target center belongs to B_i. At each
internal node it belongs to at least one of the two closed children. Because
the tree is finite it reaches a terminal rectangle. Equation (1) or (2)
then gives a physical contradiction. Thus the whole original parent is
impossible.

This reasoning does not infer a physical configuration from a feasible
linear relaxation. It excludes every actual target center after its bounds
have been proved on the whole caller. The finite rectangle tree is a real
geometric partition and its internal splits must be reported as such.
It does not change the immutable original-parent ID or the mask cover.

All other eight original squares, their frames, all physical pairs and
corners, original marked cone comparisons, and exact actual/weak bits
remain in the caller. The derived boxes may depend on all of those inputs.
The terminal itself needs only the two physical facts in Section 1.

## 4. Exact replay and source binding

`computer_assisted/verify_original_center_cover.py` implements the two
displayed rational tests and the complete finite-union induction. It
imports no numerical producer. The checker requires:

- the exact SHA-256 of the whole-parent bound record;
- equality of every supplied original center interval with that record;
- equality of the root rectangle with the target's full proved rectangle;
- exactly both children at every split, using the same axis and midpoint;
- unique terminal paths, with no terminal above another terminal;
- every strict incircle comparison and every center-disk comparison;
- zero pending rectangles and the exact node, terminal and depth counts.

The center-cover checker verifies the terminal and its scope. A separate
independent replay must establish the preceding whole-parent bound
induction; a hash alone is not an arithmetic proof. Their composition is
acyclic: proved bounds first, then a finite full-region exclusion.

The first current application, `positive-3da90694b58b6ef7`, has 61 terminal
rectangles, 60 internal rectangle splits, depth 12 and no pending region.
Its witnesses are F (24 rectangles), C (6), D (10), G (10), H (9), and
the center-disk bound (2). The least positive table reserve is
141600887/274877906944. This application is credited only with the
separately replayed original-parent induction and the bound certificate.
Other applications retain their own exact complete tables.

The theorem and arithmetic replay do not claim human or proof-kernel
verification. No Lean compilation, Lake, or CI is involved. A whole-mask
closure still requires all remaining original parents or a theorem
subsuming their entire domains.

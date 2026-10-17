# Gate 3B.2 / M5: complete exact exclusion of LOW

## Status and theorem

The LOW child from GATE3B_M5_SURPLUS_CIRCLE_SPLIT.md is now excluded,
INCLUDING LOW-REST. The exclusion no longer assumes any oblique chain.
This is a **computer-assisted exact finite proof**, with a hand-proved
geometric cover and an independent rational verifier. It has NOT yet been
compressed into the preferred short pen-and-paper geometric proof.
HIGH, the entire M5 gate, unrestricted optimality, and equality remain OPEN.

**Reference theorem.** Eight interior-disjoint unit squares, five in one
frame and three in the frame at 45 degrees, cannot be contained in a disk
of radius

    Rbar = 198869/100000 = 1.98869.

The proof permits all centers, tangencies, and valid separator alternatives.
After rotating the LOW reference problem by 45 degrees its five diagonal
squares become the five standard squares, so this theorem applies.

**LOW corollary.** Every actual M5 packing with E<=3/1000 must have

    q > (200/201)^2 Rbar^2
      = 39548879161/10100250000
      > 9789/2500.

The exact last margin is 340261/10100250000. Thus the entire LOW child,
not only the old LOW-CHAIN subfamily, is impossible at the research ceiling.
The proof does not show that a competitive M5 packing must be LOW.

## 1. A finite grid cover derived from the actual geometry

Rotate the five parallel squares to the standard frame. Label them 0--4;
label the three 45-degree squares 5--7. All centers p_i=(x_i,y_i) satisfy
|p_i|<3/2: every square contains its centered radius-1/2 disk, so containment
in Rbar<2 gives |p_i|+1/2<=Rbar<2.

Partition each coordinate into the three HALF-OPEN intervals

    [-3/2,-1/2), [-1/2,1/2), [1/2,3/2).

Two parallel squares whose centers lie in the same product cell have
both coordinate differences strictly less than one, hence overlapping
open interiors. Therefore the five standard centers occupy five DISTINCT
cells of a 3-by-3 grid. There are binomial(9,5)=126 masks.

Common signed coordinate permutations preserve the disk and both frame
classes. Modulo these eight symmetries there are exactly 23 masks.
Burnside's count is (126+2+6+2+4*12)/8=23: the 90/270-degree rotations
fix two masks each, the half-turn fixes six, and each reflection fixes
twelve. The verifier independently enumerates the 126 masks and checks
that the 23 displayed certificate roots cover them exactly by orbits.

### Boundaries and forced within-strip separators

Normalize a mask by a common symmetry and relabel its five centers.
For the subsequent convex subproblems CLOSE the assigned cell intervals.
Do not silently reassign boundary centers to a different half-open cell.

If two source centers shared a grid row, their y difference was strictly
less than one. Their actual standard-square nonoverlap therefore forced
horizontal separation at least one, with direction set by their columns.
Likewise a shared source column forces vertical separation. Retain these
non-strict forced separators after closing the cells. Reflection or axis
exchange preserves the original strict within-strip span, so these
implications remain sound in every canonical mask, including cut ties.

This gives an exhaustive one-way cover by closed cell constraints PLUS
the derived within-row/column separators. Closed cells alone would not
justify those extra inequalities; the source assignment is essential.

Sort the three minority centers by x, weakly. For masks invariant under
x reflection, choose sum of minority x coordinates nonnegative. For masks
invariant under y reflection, choose the leftmost minority center's y
nonnegative. The x choice can be made first, then sort, then the y choice;
the latter preserves the first choice. No nonexistent symmetry is used.

## 2. Rational necessary inequalities, never an inner approximation

Put

    s2 = 707106781/500000000,
    0<s2<sqrt(2),
    2-s2^2 = 263818039/250000000000000000 >0.

For a rational unit direction n=(a,b), actual disk containment gives

    a x_i+b y_i <= Rbar-(|a|+|b|)/2             (standard),
    a x_i+b y_i <= Rbar-s2*max(|a|,|b|)/2      (diagonal).

The second inequality WEAKENS the true diagonal support by rounding
sqrt(2) DOWN. It cannot remove an actual packing. The normals used in the
generated proof are exact Pythagorean directions

    ((32^2-k^2)/(32^2+k^2), 64k/(32^2+k^2)), 0<=k<=32,

and their quarter turns. The independent verifier instead checks each
used direction's squared norm equals one and reconstructs its support
inequality directly. These are exact necessary circle-support inequalities,
not four coarse strips and not a claim that the tangent polygon is a disk.
Excluding this OUTER relaxation suffices to exclude the actual disk.

For d=p_j-p_i, the complete weakened pair alternatives are:

* standard/standard: one of +dx,-dx,+dy,-dy is at least 1;
* diagonal/diagonal, with minority x sorted: dx+dy or dx-dy is at least s2;
* mixed: one of +dx,-dx,+dy,-dy is at least (1+s2)/2, OR one of
  +dx+dy,+dx-dy,-dx+dy,-dx-dy is at least 1+s2/2.

These follow from the actual SAT axes. The sorted diagonal pair uses
|dx|+|dy| with dx>=0, so the two alternatives are complete even at a tie.
All support thresholds round in the safe downward direction. Thus every
actual packing supplies a feasible point in one root's finite disjunction
of these rational linear systems.

The LOW reference ceiling is safely covered because

    Rbar^2 - 395485389/100000000 = 340261/10000000000 >0.

## 3. Exact terminal contradiction

Write an active linear inequality as A_r dot p<=b_r, where p has sixteen
coordinates and every coordinate lies in [-3/2,3/2]. A leaf stores
nonnegative INTEGER weights alpha_r, not all zero. Put

    v=sum_r alpha_r A_r,     B=sum_r alpha_r b_r.

The independent verifier proves, in Fraction arithmetic,

    B+(3/2) sum_j |v_j| < 0.                         (F)

But the weighted inequalities would give v dot p<=B, whereas the center
box gives v dot p>=-(3/2)sum_j |v_j|. This is a contradiction. Exact force
balance is not assumed: (F) explicitly accounts for any rounding residual
in the numerical discovery weights. A positive floating solver margin
is NEVER a terminal proof condition.

Each branch node selects an unordered square pair and has one child for
EVERY corresponding SAT alternative above. It retains the same centers
and all ancestor constraints. A reused leaf is valid only if every pair
inequality in its weighted proof was actually selected on that path.
The independent checker enforces this and rejects omitted alternatives,
repeated branch pairs, invalid row labels, and graph cycles.

## 4. Executed complete certificate

All 23 roots were generated and independently replayed. The complete
certificate contains:

    79,167 distinct proof nodes;
    37,952 exact weighted-contradiction leaves;
    41,215 branching nodes;
    319,575 node visits accounting for reused leaves;
    maximum branch depth 14.

Every root, every branch child, and every used geometric inequality was
checked. The checker uses only Python's standard library, Fraction
arithmetic, JSON and gzip. It does not import the generator, NumPy,
SciPy, an optimizer, or an interval/LP solver. It reconstructs inequalities
from geometric tags rather than trusting a stored numerical matrix.
The generator's 'complete' flags and solver statuses are not proof inputs.

The full replay reported:

    ALL 23 ROOTS AND ALL 126 GRID MASKS VERIFIED BY EXACT RATIONAL ARITHMETIC.
    No exact 3+5 two-frame packing fits R <= 198869/100000.

Mutation controls rejected an omitted branch child, altered theorem
radius, and zeroed contradiction multipliers. An additional exact rational
POSITIVE eight-square packing at R=2 was checked against all 28 true pair
conditions and all true vertices. It satisfies the model at R=2 and traces
a valid SAT path; the old leaf ceases to be a contradiction at that larger
radius. Thus the model is not incorrectly claiming a radius-two exclusion.

The certificate archive, independent verifier, generator, positive control,
manifest and execution logs are delivered together with this continuation.
Repository code and the manifest record the proof contract and provenance.
The numerical discovery experiments are not premises in this theorem.

## 5. Remaining proof-standard and global obligations

This closes the mathematical LOW exclusion by an exact finite certificate.
It does NOT yet meet the preferred short analytic exposition for this child;
compressing the 23 cases into reusable geometric inequalities remains a
separate hand-proof conversion task. Do not describe the certificate as a
Lean proof, or a full paper-only proof without its data.

The unrestricted M5 gate remains active on HIGH: E>3/1000, all original
orientations, all true square pair disjunctions, and actual circle geometry.
M6, M7, M8, unrestricted optimality and global equality have not been
advanced. No Lean compilation or CI was invoked.

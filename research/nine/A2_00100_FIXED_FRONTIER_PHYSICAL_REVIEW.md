# Physical interpretation of the fixed original-nine frontier

November 2, 2026, America/Chicago. Internal mathematical and source review;
no human or proof-kernel verification. No Lean, Lake, or CI.

This review concerns the complete finite cover recovered from the immutable
version-13 positive and negative forests, and the version-14 implications
used to discharge entire recorded frontier cells. It does not assert that
the remaining frontier is empty or that either `001/00` or `100/00` is closed.
The original 32-mask and 7,915-root ledgers are separate.

## 1. The caller is the original strict mask

Use the exact nine-original predicate in
`A2_COVERAGE_AND_CLOSURE_CONTRACT.md`, Sections 2–3. In the selected frame
the main originals are A,B,C,D; the short originals are E,F,G; and H,I are
the two remaining physical squares. Every original keeps its own frame,
four corner constraints, and physical separation from every other original.
AB, BC, EF, FG have actual projection separation; CD has its original
center-cone comparison and the strict inequality `x_D-x_C<h_C+h_D`.
Every corner has squared norm strictly less than `Q=1105/256`.

The accepted complete low-gap theorem excludes `|y_D-y_C|<=2/3`.
On its complement reflect the whole coordinate frame vertically, if needed,
to obtain `y_D-y_C>2/3`. Sort only the interchangeable extras so that
`x_H<=x_I`. Neither operation drops a physical original or a constraint.
Represent each unchanged square by a quarter-turn-equivalent side frame

    u_i=(alpha_i,beta_i),  v_i=(-beta_i,alpha_i),
    alpha_i>0,  |beta_i|<=alpha_i,
    alpha_i^2+beta_i^2=1,  t_i=beta_i/alpha_i in [-1,1].

The two closed root boxes have `t_D in [-1,0]` and `t_D in [0,1]`;
all other slopes lie in `[-1,1]`. Both retain the common zero face.
Every center coordinate lies in `[-rho,rho]`, `rho=91/60`: an original's
largest squared corner norm is at least `|c|^2+|c|+1/2`, and
`rho^2+rho+1/2-Q=31/57600>0`.

These two boxes therefore cover the entire normalized strict caller.
The larger closed numerical relaxations used below are only necessary
conditions. Their feasible equality controls are never asserted impossible
without the retained strict caller and a valid analytic terminal.

## 2. Meaning of a finite path

A path is a finite conjunction of the root conditions, closed rational
angle and center cuts, and the indicated original-pair or analytic escape
inequalities. All nine physical squares remain conjuncts of this domain,
even when a particular contradiction needs only a subset of its constraints.
The numerical producer's stored floating boxes do not define the domain:
the exact checker reconstructs it from the path.

Binary cuts retain both closed children. A physical inset branch retains
all four signed coordinate separations. A physical separating-axis branch
retains both original owners, both axes of each owner, and both signs.
An analytic escape branch uses the complete complement union of its stated
hand theorem, including equality. Where predecessor complements are added,
the point chooses its first satisfied escape inequality; the closed
complements of earlier inequalities still contain that point.

Consequently this is a finite cover, generally with shared faces, rather
than a disjoint partition into poses. The separate independent path/trie
review checks the complete child sets, root prefixes, guarded invocations,
and agreement with each historical leaf's version-specific path decoder.
It rejects a missing child, duplicate terminal, or terminal which is an
ancestor of another terminal. A proof leaf and an unresolved cell have
different statuses even though both terminate a path.

## 3. Necessary rows for the same original variables

The following are the mathematical meanings of the regenerated rows. They
are not conclusions drawn from a floating optimization result.

| Row family | Justification |
|---|---|
| Original frame intervals and folded width | `alpha=1/sqrt(1+t^2)`, `beta=t/sqrt(1+t^2)`, `h=(alpha+|beta|)/2`; monotonicity on the closed signed intervals |
| Coordinate inset | The square of halfwidth `g=1/[2(alpha+|beta|)]` is contained in the same original |
| Four original corners | For every retained rational direction `w`, `w.c+H_i(w)<=sqrt(Q)|w|`; each corner is treated with its actual signed frame coefficients |
| Marked links | The five original cone comparisons and exact actual-link lower spans; the original weak CD upper bound is relaxed only as a necessary numerical row |
| Nonconsecutive marked pairs | Two cone steps give horizontal span at least `sqrt(2)>=h_i+h_j`, so the omitted explicit SAT branches for these pairs are unnecessary |
| Owned physical separation | The separating-axis theorem for the two original squares, with all eight signed owner choices |
| Frame products and normal/center products | Four McCormick inequalities for the actual products on their stated intervals; product variables can be assigned their actual values |
| Circle support in additional directions | Cauchy–Schwarz for the unchanged corner, with an outward rational bound on `sqrt(Q*|w|^2)` |
| Center separation | Each original contains an open disk of radius `1/2`, hence distinct original centers have distance at least one |
| Disk/inset and disk/diamond rows | The complete containment and convex-secant arguments in `DISK_INSET_AND_DIAMOND_SEPARATION_HAND_PROOF.md` |
| Pair caps and signed caps | The accepted physical two-original cap and its stated folded/signed toll refinements; signed uses retain the proved upward original separator |
| Derived orders, strips and overlaps | The accepted C-slant, G/D, F/B, F/C, E/A, endpoint-edge, upper-inset, unique-leftmost and extra-strip theorems, with their original strict-caller hypotheses |

The physical support required by an owned axis is exactly

    [1+cos(theta_j-theta_i)+|sin(theta_j-theta_i)|]/2.

The cosine is nonnegative because both canonical angles lie in
`[-pi/4,pi/4]`. Keeping the two signs of the determinant yields the two
linear product rows used by the verifier. The same original alpha/beta
variables appear in every corner, chain, cap and chosen pair condition;
they are not replaced by independent orientation choices in different rows.

All original pairs also retain the necessary center-distance and inset
conditions, including the two extras. A proof may ignore a valid necessary
row, which weakens its relaxation. It may not remove a physical condition
from the stated original domain or omit an eligible separator child.

## 4. Interval propagation and exact arithmetic

Bounds propagated from a linear inequality use the minimum possible
contribution of its other variables before solving for the selected
coordinate. Original chain and inset inequalities propagate in both
directions. If all but one of the four inset-separation alternatives are
impossible on a closed rectangle, the remaining alternative is forced.
The small positive comparison allowance in that option test retains extra
possibilities; it cannot discard a feasible equality case.

For the circle envelope, write `k=sqrt(1/2-h^2)`. In the quadrant of a
center an original corner has outward offsets either `(h,k)` or `(k,h)`.
If `l` is a lower bound for the absolute first center coordinate and
`h^-`, `k^-` are lower bounds for the corresponding offsets, the absolute
second coordinate is at most

    max(sqrt(Q-(l+h^-)^2)-k^-,
        sqrt(Q-(l+k^-)^2)-h^-).

The center-disk bound supplies an additional upper bound. All square roots
in the checker are enclosed by integer comparisons on the grid `2^-48`.
The first radicand being negative is already impossible by the original
coordinate projection; the second is weaker since `h^->=k^-`. Empty
propagated intervals are therefore legitimate exact contradictions.

For every Farkas leaf the regenerated rows have the form `a_j.z<=b_j`.
The delivered multipliers are positive integers divided by `2^40`.
Their residual coefficient vector need not vanish exactly. If `|z_k|<=M_k`,
the checked quantity is

    reserve = -sum(lambda_j*b_j)
              -sum(M_k*|sum(lambda_j*a_jk)|) > 0.

The bounds are `rho` for center coordinates, one for original frame/inset
variables, `2*rho` for normal-times-center-difference variables, and one
for frame products. Actual original values satisfy these bounds. The
positive reserve contradicts their simultaneous row inequalities.
The discovery solver, its tolerance, and its claimed reserve play no role
in this implication.

## 5. Analytic escape unions and the version-14 additions

The inherited escape unions invoke these complete hand inputs:

- The near-horizontal B,X,D row, asymmetric B,X,D row, and positive-D
  total-variation row, with their exact horizontal and height guards.
- The right-lower exclusion `not(x_X>=0 and y_X<=y_C)`.
- The inward-endpoint A,H,I,D row at total variation `11/30`, guarded by
  the original A and D tilt signs.
- Alternative four-cone chains with actual outer links and unchanged E,F,G.
  Their whole-mask conclusion is a strict-radius theorem; no closed-Q
  exclusion is inferred for alternative endpoints.
- The F-side variation barrier and four cardinal cap-column inequalities.

The version-14 mathematical delta is limited to two already proved inputs.
The correlated-corner row terminal uses tangent bounds `1/30` or `1/50`;
these conservatively imply the sine bounds required in
`ALL_SIGN_CORRELATED_CORNER_ROW_HAND_STRENGTHENING.md`. Its allowed total
variations are respectively `11/30` and `9/20`. The seven-original guard
includes A,D,E,F,G,H,I and does not impose an unwarranted B/C angle bound.

The original-center column union follows from unit center distances. For
an ordered chain of `m` centers with total transverse variation at most
`w<1`, its longitudinal span is at least `m-2+sqrt(1-w^2)`. To see this,
use convexity of `1-sqrt(1-u^2)` and sum the adjacent unit-distance bounds.
Taking `w=3/5` gives the seven-child triple union and twelve-child
four-center union: every order escape, the span bound, and every signed
variation escape are retained. Thus these additions neither assume a
numerically observed order nor lose a boundary face.

Historical leaves are dispatched to their immutable historical verifier.
Their indices are never reinterpreted using the version-14 row list.
The reviewed version-13 sources and forests match the preserved archive
byte for byte. New leaves have explicit version tags and independently
replayed rational certificates.

## 6. Scope of acceptance

The complete physical caller maps into the two root boxes and every
necessary-row or analytic-escape construction above. Combined with the
independent finite-coverage audit and successful source-bound exact leaf
replays, this justifies adopting the 231 recorded paths as the fixed
remaining original-nine cover. It does not justify excluding an open path.

A recorded cell is counted as newly closed only when its entire path
domain is contradicted, either directly or by a complete internal proof
whose children all close. Unfinished internal searches leave that same
cell OPEN and do not enlarge the fixed register. The actual arithmetic
counts, frozen files, replay results and unresolved IDs are supplied by
the accompanying register and manifest; they must be read together with
this review. The full masks remain OPEN until every remaining cell closes.

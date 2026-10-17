# Independent review: the whole positive outer edge 3

**PASS.** The manuscript
`WRONG_0011011_EDGE3_POSITIVE_OUTER_PAIR_HAND_PROOF.md` proves the
complete outer/outer edge-3 positive/positive row of word `0011011`:

\[
 \phi+R(b)-J(B)>.89777>.89765,
 \qquad 0\le b,B\le d,
 \qquad |\phi-\pi/2|\le.7,
\]

under any of the four retained signed SAT inequalities. Reflected
reversal supplies the stated edge-5 row. All four axes, both angle
halves, and inactive and endpoint pieces are included.

The exact source and target coefficients match the shared rational
table's role-3 `O+` and role-4 `O+` entries. No correction was needed.
The companion `audit_wrong_0011011_positive_outer_edge3.py` binds the
reviewed manuscript, checker, arithmetic report, label table and two
imported manuscripts by SHA-256. It also works after these files are
placed together in the repository's `research/eight` directory.

## 1. Signed geometry and the two imported facts

I independently substituted both positive signs into the general SAT
formulas. Every axis in equation (11) has the correct signs. The lower
and upper quarter contact equations in the manuscript are their direct
algebraic consequences.

The derivative identities imply that the source label is strictly
increasing and concave, with a negative third derivative. The target
label is strictly increasing, and its first derivative is convex.
The two source chords therefore have the required lower-bound direction.
The target tangent bounds through its concave portion have the required
upper-bound direction, including their upward rational rounding.

The imports are correctly scoped:

- The global affine target bound \(J(B)<.108+.73B\) is a statement
  about the entire outer arc at the same \(Q\), independent of SAT or
  the source square. Its proof in the negative-core/positive-outer note
  uses strong concavity through \(.5\), then the convex target
  derivative and its endpoint values.
- The late zero-source contact and its derivative bound in Section 3.2
  of the positive-core/positive-outer note depend only on the target
  circle and on the vanishing source transverse coordinate. The source
  primary coordinate does not occur in that axis. Thus the facts transfer
  to the present outer source. The changes from the earlier source label
  are explicitly absorbed by \(R'(0)>1.0424\) and
  \(R(0)>-.01450\); the inherited \(.9025\) cost becomes
  \(.90249\), still more than sufficient.

The positive-core import was independently audited earlier. The
negative-core import has its own independent audit. Their whole-pair
conclusions are not used circularly here; only the stated target-only
scalar facts enter this proof.

## 2. Lower axis 1 and its complete boundary cover

For least-source contact, the target-coordinate derivative of the source
coordinate is positive. I rederived all three derivatives of that contact
and the expression for the third derivative of its cost. The source's
first two curvature terms are negative, and the remaining two are bounded
above by
\(r'\{1.061(2.15)-3(1.89442)\}<0\).
Therefore the contact cost has a concave first derivative.

At alignment that derivative starts positive. A concave derivative
which starts positive cannot subsequently cross from negative back to
positive. Thus the cost minimum is at one of the two stated endpoints.
The source-zero inactive portion decreases up to the same first endpoint.

For early angles and source coordinate at most \(.35\), the SAT
multiplier \(.98\) cancels the source coordinate in its lower chord.
The target-circle support calculation gives exactly equation (16).
The radical identity used for its concavity has the stated sign; the
single uniform sine comparison is sufficient for all four rows.
Each of the eight endpoints therefore controls its whole interval.

The target-coordinate derivative bound in equation (17) is concave in
each of its two variables. Its four endpoint corners consequently
control a full rectangle. This applies both to the large-target
continuation and to all four source-cut rectangles. The source-cut
parametrization and its increasing derivative were independently
rederived. Each remaining contact has only the listed endpoints:
the source cut, the source diagonal, or the target diagonal.

For the later lower angles, the inherited zero contact is the first
active endpoint. Its derivative is positive, and the same concave-
derivative argument reduces the cost to that endpoint or the target
diagonal. The upper bound on the source coordinate at the latter
explicitly excludes a missing source-diagonal exit.

Both complete diagonal curves are handled correctly. The source-
diagonal parametrization has increasing target coordinate and positive
\(f'\); its target speed and curvature bounds force strict cost
concavity. Its terminal angle is uniquely between \(1.014\) and
\(1.015\). Along the target diagonal the source coordinate decreases
from \(d\) to \(1-d>.1\); the source-curvature and speed bounds
again force strict cost concavity. The resulting endpoints are exactly
those already checked.

## 3. Lower axis 2

The source projection increases with its transverse coordinate. The
displayed implicit contact is therefore the least feasible source.
Its first angular derivative is negative and its second derivative
is negative; since \(R'>0\) and \(R''<0\), the contact cost is
strictly concave in angle. At each fixed target, all feasible contact
angles form an interval, and all four possible endpoint types are listed.

The fixed lower-angle support follows by subtracting the stated
positive SAT multiplier, then using \(a\ge d\) and the full target
circle. I rederived the factors of \(\sin\phi\) and the constant
term in equation (30). The zero-source target curve has the claimed
positive speed, so its cost decreases to alignment. The source-diagonal
target curve has positive speed as well. The lower bound on \(J'/r\)
is justified by its initial value and the positive derivative of its
numerator, giving the claimed monotone continuation to the double
diagonal. No endpoint is omitted by the source-zero inactive pieces.

## 4. Upper axes 1 and 2

The direct label bound covers every angle at least \(1.676\), leaving
only the overlapping strip \(0\le x\le.11\).

For upper axis 1, the source-zero target is unique and lies between
\(B_1\) and \(d\). All active source coordinates are below \(.101\).
The target-coordinate second derivative is strictly negative, so only
the zero-source and target-diagonal endpoints remain. The explicit
speed bounds make both endpoint costs increase from alignment.

For upper axis 2, the projection increases throughout the source arc.
The source coordinate \(.101\) is already feasible for every target,
so every least active source is below it. This validates the improved
denominator and radial-derivative bounds used in equation (35). The
resulting target-coordinate curvature is negative, again leaving only
the same two endpoints.

At the target diagonal, the source coordinate decreases with angle.
In its implicit second derivative, the cross term is positive and the
only negative term is bounded by the stated \(.585(.11)(1.02)^2\).
Thus both source coordinate and contact cost are concave. The active
piece ends at the unique zero angle between \(.107\) and \(.108\).
For the source-zero curve, the independently rederived identity
\(B''=Um/V-Qv^2/V^3\) has the correct minus sign and gives the
required lower bound. The target curvature then makes its cost concave.
Both endpoint costs are covered, and beyond the zero angle the entire
source-zero region has its minimum at the target diagonal and increases.

## 5. Axes 3 and 4

The common outer center-norm bound follows from the circle equation and
the concavity of \(a+b\). It gives the small target cap used in axis 3.
After inserting the target tangent, the two source-coordinate derivative
bounds are positive on their entire intervals, so the relaxed source
minimum really is at zero. The scalar second derivative increases and
has the stated positive lower bound; its one-point square completion
proves the whole lower half. The upper half is covered directly by the
same cap and the late-angle bound.

For lower axis 4, the necessary margin increases with angle and is still
negative at \(1.2\). Its subsequent target cap increases, so its two
endpoint substitutions cover the complete remaining interval. The
upper-axis cap follows from \(a,A\le a_0\) with the correct positive
\(\sec x+\tan x\) factor. Its direct bound and the late-angle
estimate cover the full upper half.

## 6. Exact replay and independent arithmetic

The author checker was copied to an isolated temporary directory. Its
fresh **147-comparison** JSON output is byte-identical to the frozen
report, and every recorded strict comparison passes.

A separately written Python rational calculation passed **47** additional
comparisons. It uses independent binary square-root brackets and
trigonometric sums. It reconstructs all four target tangents, all eight
support endpoint values and all sixteen contact-derivative rectangle
corners; evaluates the two closest diagonal endpoints from the actual
circle equations; and checks the chord, curvature, speed and final
strictness reserves. No author interval implementation is imported.

This completes the independent review of the final positive outer row.

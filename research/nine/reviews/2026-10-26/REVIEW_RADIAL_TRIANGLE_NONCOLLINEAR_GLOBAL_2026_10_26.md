# Independent review: radial external resultants of a physical triangle

Date: October 26, 2026.
Reviewer: global_closure, independent of the source author.

**Decision: ACCEPT the complete local theorem at its stated scope.**

Source reviewed in full:
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md`.
Source SHA-256 at review:
`6c4827c11e4587b968f46fbe3b271b11f63d88276311b8474a82a135435f3b65`.

I also reread the full purely geometric proper-port proof in
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 2, and the complete
`RADIAL_TRIANGLE_CONCURRENCE.md` theorem that receives this new input.
Their use requires only actual positive triangle contacts and actual
means, not a circle-load or degree-two premise at a root.

## 1. Exact equation and parallel cases

The directed-force identities are consistent with outward forces at all
three bodies. If an external resultant vanishes, the two outward cycle
forces there are opposite. The two neighboring squares would then lie
beyond opposite support faces with a positive projection gap; they cannot
touch. This proves all three resultants nonzero.

If the three external resultants are collinear and one cycle pair is
parallel, that pair has the same outward sign. Its resultant determines
the common axis, and the full force differences make every edge axial.
The three same-outward-sign requirements on an odd three-cycle are
inconsistent. Consequently the assumed collinear case has three genuine
nonparallel concurrences.

## 2. Zero origin moments and nonnegative proper lengths

Taking the full equation about each concurrence gives
`det(q_i,F_i)=0`, since the entire external system has zero origin
moment. This permits either sign or zero; the source assumes none of the
strict signs from the nonzero-cycle-moment theorem.

Every concurrence therefore belongs to the same line through the
original origin. The two proper-port lengths on each edge are
nonnegative, and their sum gives the stated nonnegative multiple of that
edge force between the concurrences. If any concurrence pair differs,
the corresponding edge is axial, and all three directed edges become
axial by the force differences. The preceding odd-cycle contradiction
excludes this. Thus all concurrences coincide. Each sum of two
nonnegative proper lengths is then zero, so both lengths vanish. All
three actual contact applications equal the same point q.

This argument includes side endpoints and all actual shared-side means;
it neither replaces a mean nor assumes strict proper lengths.

## 3. The final angular contradiction is strict

Two nonparallel normals at q make q a vertex of each square. Their
positive sum is strictly inside its outward normal cone, even when an
individual selected normal lies on a cone boundary. Hence each of the
two inward side rays has strictly positive scalar product with its own
external resultant. Its closed right-angle tangent cone lies strictly
inside the corresponding open half-plane, apart from its vertex.

Three nonzero collinear resultants with zero sum include two having the
same sign. The associated two closed right-angle angular intervals lie
strictly inside one open semicircle. Each has positive margin from both
semicircle endpoints. They cannot have disjoint interiors: their total
angular length would be pi in an available interval of strictly smaller
length. An interior angular intersection gives actual overlap near q.
This completes the contradiction without assuming any nonzero cycle
moment.

## 4. Scope and inheritance

The theorem retains every actual circle atom and bridge contribution in
each F_i, and requires zero origin moment only for the full external
system. It therefore legitimately supplies noncollinearity when a
bridge-attached cyclic root is itself loaded. The application to positive
radial concurrence still requires the separate hypothesis H nonzero;
the source states this limitation explicitly. No minimum-support,
radius, canonical-pose, new-normal or circle-mask premise is introduced.

No correction or missing case was found. No Lean compilation, CI,
numerical pose sampling, ledger change or global closure claim was used
in this review.

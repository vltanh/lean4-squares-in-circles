# ONE bridge to the unrestricted eight-square sharp radius

**Single current research objective, 2026-10-13.**
This supersedes the sprawling case-first strategy as the **primary
proof program**. Historical S1–S4, D0/D1/D2 and physical-stress
case notes remain available but are **not separate first priorities**.

## The established endpoints

The exact full eight-square construction in
[ANALYTIC_EXACT_CONSTRUCTION.md](ANALYTIC_EXACT_CONSTRUCTION.md)
proves
\[
\boxed{R_8\le\widehat R\approx1.97877086534.}
\]

The analytical five-corner theorem
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md)
and the full-domain certificate
[FIVE_CORNER_OPTIMALITY.md](FIVE_CORNER_OPTIMALITY.md)
prove a **sharp conditional** lower bound.
The stronger *actual-square* formulation
[HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md](HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md)
already covers **seven genuine unit squares** when
seven directed true support inequalities are present
and two distinguished square frames A,E are aligned.
All the other five square frames are unrestricted.
Under these hypotheses alone,
\[
R\ge\widehat R
\]
is proved, and equality reconstructs the relevant
five-corner frame alignment/contact sliders.

**What is missing is the topological extraction of those
seven directed inequalities plus the two common end frames.**

## THE SINGLE PROPOSED BRIDGE (UNPROVED)

> **Candidate minimizer-level bridge B (UNPROVED).**
> Every attained **global radius-minimizing**
> eight-unit-square packing with \(R\le\widehat R\)
> admits seven distinct square labels
> A,B,T,D,E,H,G and true orthonormal directions
> (a,b),(e,f) satisfying the exact seven
> **directed whole-square support inequalities (1)**
> of HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md,
> **with A,E possessing the same side frame (a,b)**.
>
> No positive-stress-only or center-distance
> replacement is permitted for a specified
> genuine whole-square separator.

Proving B would establish \(R_8\ge\widehat R\)
immediately by the existing conditional theorem;
the exact construction supplies the matching
upper bound. **B may be false.** Its failure at an
attained minimizer would require a genuinely
orientation-independent sharp force/support
inequality as an *alternative research target*,
not an unproved escape clause in B itself.

The key mathematical challenge is to justify
**common end-frame alignment and directed
support ownership**, not merely abstract
adjacency of a seven-center cycle.
No contact graph enumeration or marker count
currently establishes these two properties.

### Minimize-first quantifiers are essential

A new full-domain exact obstruction
[NO_NEAR_SHARP_CONTACT_OR_FRAME_RIGIDITY.md](NO_NEAR_SHARP_CONTACT_OR_FRAME_RIGIDITY.md)
proves **for every \(R>\widehat R\)** there
exist full eight-square packings inside radius
R with **no actual contacts and no two
parallel frames**. An explicit *rational*
witness below \(R^2\le9789/2500\) is checked
in
[verify_generic_no_contact_eight_square_packing.py](verify_generic_no_contact_eight_square_packing.py)
with all 32 vertices, all 28 real SAT owner axes
and exact positive reserves.

Therefore **any purported extraction theorem
for every packing with \(R^2\le9789/2500\)
that requires an exact contact or aligned pair
is false**. This includes an overbroad reading
of the sharp seven-square separator theorem:
that theorem's common A/E frame must be
*proved from minimum-radius stationarity*,
not taken for granted from the radius ceiling.
The witness does **not** refute the projected
five-corner inequalities or any **minimizer-only**
claim.

If a packing with radius strictly below
\(\widehat R\) existed, compactness of center
positions and square-frame angles inside its
disk would give a genuine **attained global
minimizer with still smaller radius**.
Thus restricting the missing bridge to actual
minimizers is a sound logical reduction.
At such a minimizer normalized physical
stress and actual contacts exist; their
known four-root classification is a tool,
not the final theorem.

## The one computational falsification test

**Do not optimize a local cap or a partially
filled seven-square model and infer global conclusions.**

Instead, run a complete eight-square
center/frame optimization with **all 32 true
vertices and all 28 genuine pairwise SAT
disjunctions**, in a small neighborhood of
the exact candidate, *and* from independent
starting configurations. For every putative
new radius/contact topology, separately
solve the actual force/torque multiplier
equations and check which of the **seven
directed true-square support inequalities**
of the existing sharp theorem can possibly
hold.

There are only two reportable outcomes:

* **A complete, strict counterexample to
  the proposed bridge:** a certified
  stationary full eight-square competitor
  under the candidate bound **without**
  the extractable directed/aligned-end
  pattern, with exact actual vertices,
  SAT constraints and physical stress.
  If it has radius below \(\widehat R\),
  it would also disprove the conjectured
  optimum; do not disguise that.
* **A complete proof of the bridge:** an
  all-frame geometric theorem extracting
  the directed separators and A/E alignment
  from *every actual global minimizer*
  below \(\widehat R\), or a universal
  sharp force inequality covering the
  unextractable alternative.

A local optimizer's failure to find a
lower radius, a negative residual, or
a near-constant optimal frame **does not
count** as a proof or a counterexample.
The attempted seven-square SLSQP probe
with freely rotated endpoints has not
yielded a certified counterexample;
its negative constraint residuals make
its below-candidate trial values unusable.

## Only one success criterion

**Stop adding new S1/S2/S3/S4 branch lemmas,
small cap thresholds, and graph-template
counts unless a result directly proves or
falsifies the single bridge above.**

The next output must be one of:

1. a rigorous minimizer-level **directed
   support/frame extraction lemma**
   reducing a substantial *entire global
   stress class* to the seven-separator
   theorem, or
2. a complete actual-square **counterexample**
   demonstrating that the proposed bridge
   itself is too strong and must be
   replaced by an orientation-free dual
   lower bound.

The equality-bearing full seven-outer
actual-contact ring must remain admitted.
The unrestricted \(R_8\ge\widehat R\),
global equality classification, and
Lean 4 formalization are **OPEN**.
There is no reason to mark PR #9 non-draft.

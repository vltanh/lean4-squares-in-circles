# ONE bridge to the unrestricted eight-square sharp radius

## CURRENT mathematical breakthrough: true SAT-local sharpness with all seven frames free

**The candidate's seven-square ring is now proved
LOCALLY SHARP under full genuine SAT nonoverlap,
without any parallel-frame or prescribed fixed-axis
separator hypothesis.**

[HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md](HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md)
proves that some open neighborhood of the exact seven
outer-square reference configuration has the following
property: **every** set of seven genuine unit squares
inside that neighborhood, with completely independent
orientations, *all actual open interiors disjoint* and
contained in \(D_R\), satisfies \(R\ge\widehat R\).

The proof uses the NEW
[HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md](HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md).
For every common tilted-frame parameter t near the
exact sharp root, it chooses a true positive
seven-directed-edge/five-circle adaptive algebraic
dual from the stationary five-corner scalar family,
and completes the center squares:
\[
R^2\ge q_*+\mu_H(t)F(q_*,y(t),t)+
 (1/200)\sum_{\text{seven frames}}
 |\sin(\text{orientation defect})|
\]
under the **fixed seven directed** separator hypotheses.
The global-in-family theorem gives \(F\ge0\).

The stronger TRUE-SAT theorem then removes those
fixed-direction hypotheses **locally**:
at the exact candidate **all 11 wrong pair SAT
side axes** have projected gap less than \(-1/20\),
so actual nonoverlap forces one of just
**32** correct signed owner assignments.
A true physical force/circle dual on all
32 assignments has **strict first-order
mismatch coefficient reserve \(>1/40\)**
on the five relative-orientation tree edges
AB,TB,DT,ED,HG, proven by the
[exact interval auditor](verify_sat_seven_local_dual.py).
Positive disk-vertex quadratic terms
absorb position/angle mixed Taylor errors,
giving an exact nonlinear local bound with
angular penalty \(>1/80\) times total relative
angle defect after reducing the neighborhood.
**No physical square is rotated in this argument.**

Because any full eight-square packing contains its
seven named exterior squares, this proves **LOCAL
sharpness of the full eight-square construction**,
for all independently oriented frames, with
its legitimate T/G slider freedoms.

### The one remaining GLOBAL bridge

The finite local result does **NOT** prove
unrestricted \(R_8\ge\widehat R\).
The next and ONLY global theorem needed by
this approach is a **capture statement**:

> Every hypothetical complete eight-square packing
> with \(R<\widehat R\) can, by an exhaustive sound
> geometric pose-cover proof and symmetry reduction,
> be reduced to the open seven-square candidate
> neighborhood just proved sharp—or must satisfy
> another exact globally sharp obstruction.

Equivalently, it would suffice to establish:
**every attained global minimizer of radius
\(R<\widehat R\) lies (up to label symmetries
and rigid disk symmetries) in the candidate's
local pose neighborhood.**
The local theorem would then immediately contradict
the smaller radius. **THIS CAPTURE THEOREM IS OPEN**.

The revised 11SquaresOptimal manuscript obtains its
global capture using a fixed marker ownership cover,
compulsory convex regions and certified
interval/SAT pruning. Our disk geometry needs a
new **circular-geometry** pose/ownership capture,
not its rectangular wall arguments copied verbatim.

**Stop rule:** Do not attempt further tiny
cap-constant improvements or new conditional
contact graphs. The only current globally decisive
deliverable is a sound complete capture of
strictly better eight-square configurations
into the local true-SAT neighborhood (or an
orientation-independent alternative sharp bound).
The equality-bearing full seven-outer actual
contact ring is explicitly included locally.

Unrestricted sharpness, global equality classification,
and Lean 4 formalization remain **OPEN**.

---



## New preferred bridge after reading 11SquaresOptimal: pay for independent frame angles

**The existing exact-end-frame bridge B below is now a
STRONGER BACKUP conjecture, not the preferred next
proof test.** The new technical target is an
**orientation-robust seven-directed-separator theorem**,
which may work even if A,E have different true frames.

[**ELEVEN_SQUARE_METHOD_TRANSFER.md**](ELEVEN_SQUARE_METHOD_TRANSFER.md)
extracts the technique from
https://github.com/Queuingtheorydotcom/11SquaresOptimal,
especially its revised manuscript's
"mixed support inequality with independent angles":
a true pair separator can give
\[
g_{ij}\ge\frac{\eta_{ij}}2
             |\theta_i-\theta_j|,\quad
\eta_{ij}>0.
\]
A positive weighted sum of true supports may
then "pay" to compare its scalar value with
the common-angle family, via an abstract
spanning-tree contraction of angle variables.
**No physical packing is rotated** and no exact
minimizer-level frame parallelism is assumed.

A concrete full-continuum **local transfer is PROVED**
in [HUMAN_LOCAL_ANGLE_MISMATCH_BACKBONE.md](HUMAN_LOCAL_ANGLE_MISMATCH_BACKBONE.md):
for the genuine candidate's directed SAT pairs
AB, TB, DT, ED and HG, independently moving
each relevant true square center by <=1/50
and its frame by <=1/50 radians still
**forces the correct true SAT owner family**
and yields the uniform mismatch reserve
\[
\boxed{g_{ij}\ge\tfrac7{100}
                   |\theta_i-\theta_j|.}
\]
All five exact base transverse displacements
are rational with absolute values <=23/30.
The arithmetic is independently checked in
[verify_eight_angle_mismatch_backbone.py](verify_eight_angle_mismatch_backbone.py).
The edge graph joins all **five standard
chain frame variables** A--B--T--D--E,
and separately the **tilted pair** H--G;
the candidate's *relative* tilt remains free.

**One immediate decisive computation, BEFORE
more full case enumeration:** construct an
explicit **positive weighted seven-square
support functional** equal at common
standard-cluster angles to the existing
sharp five-corner scalar certificate.
Determine whether its angle-cluster
derivative bounds are dominated by
the five **positive true-square mismatch
penalties** above. A certificate
\[
|\partial_{\text{cluster}} S|
\le\beta_{ij}
\le\lambda_{ij}\eta_{ij}/2
\]
throughout a rational candidate neighborhood
would prove a **local orientation-robust
conditional sharp lower bound** without
requiring any pair of frames to be parallel.

**Global gap still present:** one must
extract the required genuine seven
directed SAT owner families and a
sufficient pose/capture neighborhood
from every hypothetical better
eight-square minimizer, *or* prove
a different universal sharp bound
for uncaptured alternatives. The
eleven-square manuscript gets
capture from **12-markers in a
SQUARE container**; its wall-based
ownership proof is not valid
verbatim for our circle.
Do not mistake a local positive
angle penalty for a global
five-corner reduction.

**No new global sharp radius proof,
equality classification, or Lean
formalization is claimed.**

---


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

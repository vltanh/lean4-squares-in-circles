# n=8 proof tracker

## Current orientation (2026-10-11)

### CURRENT proof architecture: four stress roots; k7 two-spoke m=7 excluded

[STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md](STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md)
now leads the research. It abandons
further minor cap-cutoff tuning in
favor of actual contact geometry,
positive mechanical stress and the
*unrestricted global radius*.

The exact
[HUMAN_GLOBAL_STRESS_ROOTS.md](HUMAN_GLOBAL_STRESS_ROOTS.md)
reduces every attained minimizer to:
(A) the **full seven-outer actual-contact
ring**, genuinely realized at equality;
(B2) central positive stress degree two;
(B3) central positive stress degree >=3;
or (X) an exterior positive-moment
cycle of 5..7 squares containing a
**noncentral, strictly circle-free
inner-center witness**.

Within k=7/B2 and **outer actual paths**,
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
proves that the entire positive stress
graph is a single cycle
C-S1-...-Sm-C, m=3..7, with no
positive outer tails; its angular
order is consecutive among all seven
outer square centers. Exact graph
enumeration returns 35 labeled
supports before applying further geometry.

**Major completed macro-case exclusion:**
[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md)
proves opposite supporting contacts
across C force the neighbor-center
angle **>\(\pi/2+1/13\)**.
[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md)
then proves **m=7 is impossible** in
this k7/B2 actual-path root, since
the six actual successive outer
contacts require missing angle
**<\(\pi/2+3/250\)**.
The exact incompatibility margin is
\(211/3250>0\).
Only **m=3,4,5,6** remain in this
particular root, 28 labeled graph
supports before continuous pruning.

The candidate's real **full outer
actual-contact seven-cycle** belongs
to separate root A, and is not rejected.
Outer spectators, zero-weight actual
contacts and all square frames remain
part of the global model.

This is a genuine *structural proof
step*, not just a smaller real-valued
cap parameter. **It does not yet
establish \(R_8\ge\widehat R\)** or
classify all equality cases.
Lean formalization has not begun.


### CURRENT computer-assisted proof frontier: 79/250 (2026-10-12)

**Supersedes the older 37/100, 1/3, and 8/25
cutoffs elsewhere in this historical tracker.**

[HUMAN_CAP_ENVELOPE_79_250.md](HUMAN_CAP_ENVELOPE_79_250.md)
is a new **genuine full-frame hand theorem**:
at \(q\le9789/2500\), every whole unit square
beyond offset \(h\ge79/250\) satisfies the
sharp aligned-cap envelope
\((h+1)^2+(|p_\perp|+1/2)^2\le q\).
It is proved by actual vertices, strict
concavity and a **63-coefficient exact rational
Bernstein certificate**, establishing the
needed height bound noncircularly.
[computer_cap_bernstein_discover.py](computer_cap_bernstein_discover.py)
records the reproducible exact coefficient
discovery workflow; optional scripts
audit arithmetic, never substitute for the
mathematical hand proof.

[HUMAN_MIXED_HIGH_CAP_79_250.md](HUMAN_MIXED_HIGH_CAP_79_250.md)
then proves **full-frame impossibility**
of same-weak-sign mixed inner/outer cap
pairs at \(h\ge79/250\):
their coupled squared center distance
is \(<999361/1000000<1\).

**Latest necessary exclusive S2/k4 cells:**
A: \(79/250\le h_U<97/200\), opposite signs;
B: \(7/24<h_U<79/250\), opposite signs;
C: \(7/24<h_U<79/250\), weak same signs,
forced near-U outer **whole-quadrant owner**
and a nonzero actual frame-tilt defect.
No cell is yet completely eliminated.
The remaining same-sign offset interval
has width \(73/3000\).

**Counterexample guard:** the aligned one-square
envelope is **false at h=3/10** under
the same disk ceiling; an actual rational
rotated square and its four true vertices are
given in
[RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md](RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md).
This does *not* disprove a future **mixed
two-square** SAT obstruction at h>=7/24.

**Next substantive step:** prove (or falsify
with genuine SAT-verified geometry) the
proposed sharp mixed same-sign two-square
cap bound down to h=7/24, not another
tiny one-square threshold update.
Then couple opposite-sign cells with
the far-D pair and R triple; continue
S1 tiny-offset, higher-k, corner-only,
D1/D2 and true S4/k7 equality-preserving
five-corner global proof.

The unrestricted \(R_8\ge\widehat R\),
full equality classification and
Lean 4 proof remain **OPEN**.


### CURRENT computer-to-hand roadmap (2026-10-12)

Start from the authoritative
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md).
It documents an **actual** reproducible
mixed-center two-square cap optimization
using every true vertex and signed SAT
separator, then converts its candidate
near-axis pattern into a completely
independent **written analytic theorem**.

The new
[HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md)
extends the sharp arbitrary-frame single-square
cap envelope to offset \(h\ge37/100\)
under the established n=8 disk ceiling
\(R^2\le9789/2500\), via four rational
polynomial positivity certificates.
The derived
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md)
**excludes all mixed inner/outer same-weak-sign
two-square caps at \(h\ge37/100\)**,
with true center squared-distance upper
bound \(1989/2000<1\).

The current exhaustive **exclusive S2/k4**
geometric three-cell queue is now
A: \(37/100\le h_U<97/200\), opposite
near-U transverse signs;
B: \(7/24<h_U<37/100\), opposite signs;
C: \(7/24<h_U<37/100\), weak same signs
with compulsory quadrant and frame constraints.
The **entire** former C strip
\(37/100\le h_U<2/5\) is eliminated.
The conjectured stronger standalone
mixed-cap radius bound
\(R^2\ge(1+h)^2+9/4\) down to \(h=7/24\)
is **not yet proved**. Numerical local
solver values are NOT proof certificates.

Priorities in the new roadmap: finish
C using exact SAT-owner frame reductions,
then the opposite-sign A/B cases;
then tiny-offset S1/k3, higher k,
D0 corner-only/D1/D2, and the
**equality-preserving S4/k7** global
radius lower bound.

The unrestricted theorem \(R_8\ge\widehat R\),
global equality classification and Lean 4
formalization remain OPEN. Preserve the
genuine exact S4/k7 equality packing.


### Latest October 12 small-cap research frontier

The main unrestricted target is still
\[
R_8\ge\widehat R.
\]
Neither all status cases nor all equality
configurations have been classified. No
production Lean proof has been constructed.

**New mathematical hand results:**

* The previous S3/k3 local angular argument is
  extracted and strengthened in
  [HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md](HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md).
  It forbids three R whole-cap members
  (two inner, one R-only outer) at
  \(h_R>17/200\) alongside two distinct
  U-inner whole-cap members whenever
  \(h_U\ge1/16\), for *all* frames.
* Consequently **exclusive S1/k3** normalized
  as R=3,L=1,U=3,D=0 must satisfy the
  **uniform strict** tiny-offset bound
  \(0<h_{30}<1/16\).
* [HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md](HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md)
  proves the far L singleton must have actual
  transverse center
  \(-3/20<y_L<-1/75\). This is a
  genuine additional signed-position
  exclusion, but does **not** finish S1/k3.
* For **exclusive S2/k4 cell C**, the
  mixed near-U outer square is forced
  into an **actual whole open origin
  quadrant** with x-boundary clearance
  \(>1/50\), by
  [HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md](HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md).
* The *blanket* same-sign two-square
  whole-cap impossibility shortcut is
  **false**. The genuine exact rational
  rotated pair in
  [RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
  has positive center x values, a shared
  cap offset \(>7/24\), and true
  square separation/disk-vertex margins
  below the search ceiling. Its centers
  are **both outer**; it is *not* an
  S2/k4 mixed-center realization.

**Remaining exclusive D0/S=7 k queue:**
S1 k=3..6; S2 k=4..6 with at least one
near-2+2 outer center; S3 k=4..7;
S4 k=4..7 including exact k=7 equality.
D0 corner-only, D1/D2 and full exterior
contact-graph cases also remain open.
The three-cell S2/k4 A/B/C geometry is
not yet excluded.

All new rational-margin scripts are
checks of **arithmetic**, not global
mathematical certificates or Lean proofs.
Preserve the genuine sharp S4/k7 equality
construction in every proposed global
obstruction.


### Most recent further S2/k4 mixed-pair case split

The exclusive S2/k4 parent macro-cell remains OPEN,
but [HUMAN_S2_K4_THREE_CELL_QUEUE.md](HUMAN_S2_K4_THREE_CELL_QUEUE.md)
now gives an exact three-cell *continuous* remainder:

- \(0<h_R<13/100\),
  \(7/24<h_{\rm near}<97/200\);
  the far 2+2 members are outer, R has one
  outer/two inner, and near U has one
  outer/one inner square.
- At \(h_{\rm near}\ge2/5\), the near inner
  and outer centers **must have opposite**
  transverse signs, by an all-frame analytic
  mixed-cap center-distance contradiction.
- For \(7/24<h_{\rm near}<2/5\), an
  opposite-sign pair remains, or a **weak
  same-sign** pair with inner \(|x|<1/4\),
  outer \(|x|>7/10\), and at least one
  actual frame deviation \(>1/2600\) radians.
- In all three cases their center-ray gap is
  \(>3/4\) radian, and their **actual**
  horizontal chords on \(y=(R+h_{\rm near})/2\)
  are disjoint and each have length >=1.
  Do **not** infer disjoint whole horizontal
  projections for arbitrary rotated squares.

These are strict necessary conditions, not
claims that all three continuous cells
are impossible or realizable.
They do **not** modify the older complete
S2/k3, S3/k3, S4/k3, or S2-near-both-inner
exclusions, nor the actual S4/k7
sharp equality construction.

The unconditional reverse radius inequality
\(R_8\ge\widehat R\), equality classification,
and Lean handoff remain OPEN.


### Latest completed subcases (2026-10-12 research continuation)

Two additional **full analytic macro/subbranch closures** now
supersede some historical 'remaining S2/S3' statements below:

1. [HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md)
   proves that **exclusive S3=(3+1,2+1) with exactly k=3
   exterior outer centers is impossible**, all frames and
   central offsets. It uses an inner-R-pair positive center-y
   reserve and the sole R-outer's failure to have a U
   whole-square side separator to force center distance <1.
2. [HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
   proves that **exclusive S2=(3+0,2+2) with both nearer
   2+2 cap centers inner is impossible**, for every k.
   The proof combines strict outer-ray ordering with a
   four-rational-endpoint hand convexity argument and
   center separation <1.

The current **exclusive all-seven-one-side D0/S=7**
outer-center counts not yet globally excluded are:
S1 k=3..6; S2 k=4..6 (with at least one near-2+2
outer center); S3 k=4..7; S4 k=4..7
(including the actual S4/k=7 sharp equality packing).
Other D0 corner-only, D1, D2 and contact graph cases
still require sharp continuous inequalities.

No complete proof of \(R_8\ge\widehat R\),
unrestricted equality classification, production
Lean 4 proof or Lean handoff has been established.
The PR must remain a research-only draft.


### October 12 latest exact continuous pruning

See HAND_PROOF_CLOSURE_LEDGER.md and
PATTERN_REJECTION_MATRIX.md for precise hypotheses.

* **Exclusive S2, both nearer 2+2 cap centers inner:**
  the only remaining outer-center count is **k=4**,
  with right triple offset \(0<h_R<1/20\);
  the U inner and D outer cap-center transverse
  x pairs each have opposite strict signs,
  with absolute coordinate lower bounds
  \(9/25\) and \(29/100\). This is not a
  complete S2/k=4 exclusion.
* **Exclusive S3/k=3:** the two offsets must satisfy
  \(17/200<h_R<13/100\) and
  \(17/200<h_U<1/5\).
  The entire **negative** outer R-center polar
  ray sector is now impossible; the sole possible
  R outer ray satisfies
  \(311/500<\psi<8959/10500\).
  Its distant D singleton center must satisfy
  \(-13/40<x_D<0\), \(y_D<0\).
  The positive-ray case remains open.
* The earlier **entire S2/k=3 and S4/k=3**
  exclusions remain proven.
* The rational eight-center S2 relaxation example
  is known to violate the *existing* outer-angle
  theorem; it proves only insufficiency of its
  explicitly enumerated weaker center constraints,
  and is not evidence of an actual packing.

The conditional sharp five-corner optimum, exact
construction, analytic cap lemmas and local
exclusions do **not** yet establish
\(R_8\ge\widehat R\). No n=8 production
Lean theorem or unrestricted equality
classification has been completed.
The exact sharp S4/k=7 equality construction must
continue to be preserved.


### October 12 continuation: verified status of the global case queue

The original checklist and early narrative below preserve historical
planning. The active summary is the closure ledger and the end of
SINGLE_SIDE_SEVEN_BRANCHES.md. In particular, the new
[HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md)
hand proof **completely excludes** the exclusive-one-side
S2/k=3 and S4/k=3 macro-cells. It works by an exact six-square
inner/outer center-ray contradiction (arbitrary square frames)
and retains the real candidate's S4/k=7 equality cycle.

The remaining all-single-side D0/S=7 subcases are
S1 k=3..6, S2 k=4..6, S3 k=3..7, S4 k=4..7.
Other D0 cases with corner-only exceptions, D1 with a double-side
square, and D2 with two adjacent doubles are **still open**
after their precise cap and angle restrictions.
This enumeration is necessary-status bookkeeping, **not** a list
of independent solved or even realizable geometric patterns.

The analytic sharp five-corner construction and its conditional
family optimum are proved; the **unrestricted reverse bound
\(R_8\ge\widehat R\) remains open**.
There is no production Lean n=8 theorem, no Lean handoff,
and no equality classification of all minimizers.
None should be claimed from the remaining local-cap eliminations.


The checklist below is the original planning document and predates most of
the research on this branch. See [PEN_AND_PAPER_ROADMAP.md](PEN_AND_PAPER_ROADMAP.md)
for the current evidence, the precise global gap, and the analytic work plan.
The exact construction and the sharp conditional five-corner optimum now
have complete analytical proofs. The unrestricted sharp lower bound is
not yet proved.
The current continuation writes mathematics only; no Lean proof is attempted.

### Completed analytical work in this continuation

- [x] Give an explicit rational eight-square packing, with complete
      containment and pair-separation proofs.
- [x] Extend every least-family-radius stationary configuration to
      eight full squares, with three independently variable positions,
      using only the defining equations and analytical bounds.
- [x] Prove the full fixed-tilt position convexity and exact domain of the
      five-corner defect.
- [x] Give an analytic least-stationary-root characterization of the
      conditional family optimum, including global endpoint exclusions.
- [x] Prove feasible-branch position monotonicity and the stationary
      coordinate inequalities needed for the construction's column order.
- [x] Prove the sharper stationary order $1/2<v<u<1$ and give an
      analytic whole-family enclosure $R>79/40$, $\tan t<1/5$ below
      the rational construction ceiling, using concave support functions.
- [x] Prove that the stationary polynomial system has exactly one admissible
      solution in the explicit radius strip, and that it gives the global
      family optimum. The envelope argument covers critical points with
      positive defect as well as feasible critical points.
- [x] Prove compactness, exact center supports, balanced stresses, and
      complete normal angle stationarity for arbitrary minimizers.
- [x] Prove the exceptional-corner bound and the outward disk-cap capacity.
- [x] Prove the sharp two-square disk-cap inequality
      $R^2\ge(h+1)^2+1$ for $2/3\le h\le1$, including arbitrary
      orientations and the complete equality cases.
- [x] Prove analytically that every eight-square packing with
      $q\le98/25$ has a unique square containing the disk center in its
      open interior, using total angular measure on two circles.
- [x] Prove the unconditional analytical bound $R_8>\sqrt2+1/2$,
      using an auxiliary circle chosen from the central square's depth.
- [x] Exclude four-square straight separator chains below radius two.
- [x] Derive the orientation of strictly interior two-contact squares.
- [x] Derive a four-square common frame from two such squares sharing their
      two actual neighbors.
- [x] Under this explicit twin hypothesis, identify the central twin, fill
      the bounded gap without affecting any other square, exclude the two
      upper central-corner exceptions, and obtain the outer two-unit spans
      without assuming the frames of the remaining squares.
- [x] Prove radial leaf geometry and exclude nontrivial actual-contact tree
      components in a minimum-contact minimizer.
- [x] Prove force and moment equilibrium at actual common contact points;
      constrain positive-stress bridges and tree components.
- [x] Prove nearest-point angular order for the contact moments of every
      exterior square, and positive winding for every directed exterior
      moment cycle, including degenerate contacts and higher-degree branches.
- [x] Prove that a four-square exterior cycle around the central unit is
      exactly a parallel cross, and that such a cross has room for at most
      two additional units below radius two. Exterior moment cycles in
      an eight-square minimizer therefore have at least five vertices.
- [x] Exclude every nontrivial stress-tree component under the explicit
      hypothesis $\sqrt2+1/2<R<2$; the new analytical lower bound now
      places $R_8$ in this interval without a certificate premise.
- [x] Replace the symmetric four-type seven-walk enumeration by an exact
      elementary formula.

### Remaining proof obligations

- [ ] Force a sufficient contact pattern or a sharp alternative inequality
      for an arbitrary radius-minimizing eight-square packing.
- [x] Select the exact sharp family root uniquely by an analytical theorem;
      a tiny numerical root box is unnecessary for its definition or proof.
- [x] Prove the eight-square construction at the exact selected least
      family root without the existing interval margin checks.
- [ ] Combine these results into the unconditional equality $R_8=R_*$.

The exact construction now proves $R_8\le\widehat R$, where $\widehat R$
is the analytically selected least five-corner radius. The earlier rational
construction also remains a standalone explicit upper bound. The
conditional family results and contact-pattern implications do not yet
establish the unrestricted lower bound. See the roadmap for exact statements
and links to every new proof.

## Original checklist (historical)

The sections below preserve the earlier plan; their unchecked boxes are
not the current completion record.

## Scope

This branch tracks research toward a human-readable proof for eight unit squares
in a circle.

- [x] Keep research artifacts under `research/eight/**`.
- [x] Do not change production Lean, public theorem statements, CI, metadata,
      or other research subtrees in this planning PR.
- [x] Reuse generic n=6/n=7 machinery where it genuinely applies.
- [ ] Do not promote a numerical candidate to a theorem statement until its
      exact contact equations and construction have been derived.
- [ ] Keep the substantive proof analytical: no interval-box cover, generated
      classification table, sampled minimum, or external PASS result as the
      reason a continuous case is true.

## Working objective

The project has two logically separate tasks:

1. reconstruct the best n=8 candidate exactly and prove it is a packing;
2. prove no packing can use a smaller radius, ideally with an equality/contact
   classification strong enough to explain the candidate.

The hard research question is expected to be the global structural reduction,
not the pairwise separation algebra.

## Reusable machinery from n=7

### Generic pair normalization and separating axes

These pieces should be treated as infrastructure, not reproved case by case.

- [ ] Generalize/reuse the canonical relative-state model for two rotated unit
      squares.
- [ ] Reuse the four separating axes of the two square frames.
- [ ] Reuse support sums in terms of:
      - relative phase;
      - center displacement in the first frame;
      - pair width
        `(1 + |cos d| + |sin d|)/2`.
- [ ] Reuse the reverse-pair/reflected-frame reduction.
- [ ] Make the generic pair lemma independent of the n=7 label definition
      where practical.

Relevant n=7 architecture:

```text
CanonicalPair
  -> canonical_has_separator
PairModel
  -> relativePhase
  -> centerDX / centerDY
  -> pairWidth
  -> pairSupport
  -> pair_support_axis_values
```

### Continuous-gap / leftmost-minimum method

- [ ] Identify whether the n=8 candidate supplies a natural critical angular
      gap or a small finite set of critical gap types.
- [ ] If so, prove the critical-gap inequalities first.
- [ ] Reuse the n=7 pattern:
      ```text
      endpoint/critical gap
        -> positivity near one end
        -> assume a first nonpositive point
        -> choose leftmost minimum
        -> cardinal-phase cases
        -> smooth stationary case
      ```
- [ ] Reuse the smooth sinusoid/stationary-corner machinery rather than
      subdividing a continuous angle interval.

### Convex state-region reductions

- [ ] When an active label/support branch produces a convex polygonal state
      region, reduce affine support expressions to its vertices.
- [ ] Keep finite cases only when they are geometric vertices, sign walls,
      contact types, or separating directions.

## Reusable machinery from n=6

### Weighted separator combinations

- [ ] Search for small cycles/paths of genuine separating inequalities whose
      weighted sum cancels nuisance center coordinates.
- [ ] Derive weights from the candidate contact geometry, not by numerical fit.
- [ ] Keep all weights nonnegative when they are used as dual multipliers.
- [ ] Explain every resulting support force geometrically.

This is a leading candidate for the final n=8 closure because the optimum may
not have the equal-gap rigidity available for n=7.

### Support-force cones

- [ ] Keep two-dimensional force vectors intact before scalar expansion.
- [ ] Prove force vectors lie in a simple cone.
- [ ] Derive one disk-support inequality valid on that cone.
- [ ] Use completed squares / Cauchy--Schwarz after the cone is visible.
- [ ] Avoid replacing a clean vector inequality with a large polynomial unless
      there is no simpler route.

### Whole-domain analytic reduction

For any remaining 2--4 parameter defect:

- [ ] derive its true domain from geometry;
- [ ] prove monotonicity in one variable where possible;
- [ ] prove concavity/convexity in another;
- [ ] split only at genuine sign walls or active-contact transitions;
- [ ] reduce to finitely many endpoints forced by those arguments;
- [ ] use exact Taylor/algebra only at those forced endpoints.

## Gate 1 — exact candidate reconstruction

Do not begin a full lower-bound formalization before this gate is understood.

- [ ] Recover a high-precision candidate configuration from a reliable source or
      independent numerical reconstruction.
- [ ] Determine its symmetry group.
- [ ] Identify every square-square contact.
- [ ] Identify every active circle contact.
- [ ] Identify which square orientations are equal by symmetry.
- [ ] Count the true degrees of freedom after quotienting translation/rotation.
- [ ] Write the minimal contact equation system.
- [ ] Eliminate auxiliary coordinates enough to obtain an exact algebraic
      characterization of the candidate radius.
- [ ] Determine whether the radius satisfies a manageable polynomial.
- [ ] Prove the selected algebraic root is the geometrically relevant one.
- [ ] Record exact or algebraic coordinates/orientations suitable for Lean.

Deliverable:

```text
research/eight/CANDIDATE.md
```

with an exact contact graph and equations, not only decimal coordinates.

## Gate 2 — construction

- [ ] Define the exact candidate configuration.
- [ ] Prove every object is a unit square.
- [ ] Prove pairwise disjoint interiors from the contact graph / separating
      axes.
- [ ] Prove containment in the candidate circle.
- [ ] Prove at least one vertex/contact reaches the boundary, so the stated
      radius is exact for the construction.
- [ ] Package a proposed Lean construction theorem.

Deliverable:

```text
research/eight/CONSTRUCTION_PROOF.md
```

## Gate 3 — choose the global structural invariant

Test several routes before committing to one.

### Route A — marker / angular budget

- [ ] Define candidate-derived marker(s) for an exterior square.
- [ ] Determine whether one marker type is enough or whether the tilted and
      near-axis states need different marker branches.
- [ ] Prove a pairwise marker-gap inequality from canonical separation.
- [ ] See whether the full circle budget forces the candidate cyclic pattern.
- [ ] If gaps have different types, derive a mixed budget such as
      `m*alpha + k*beta = 2*pi` at equality.
- [ ] Reject this route if the resulting gap theorem is too weak to force the
      contact graph.

### Route B — contact/separator graph

- [ ] Use four-axis pair reduction to associate each relevant pair with a
      geometric separating/contact type.
- [ ] Prove every sufficiently small packing has enough active/near-active
      separators to force a small list of planar contact graphs.
- [ ] Eliminate graphs conceptually using degree, cyclic order, support budget,
      or disk geometry rather than exhaustive graph enumeration.
- [ ] Show the surviving graph is the candidate graph.

### Route C — large near-axis scaffold

- [ ] Test whether a sufficiently small n=8 packing must contain a large
      subsystem of squares with nearly common orientation.
- [ ] If yes, rigidify that subsystem using n=5/n=6 style polygon/tangent
      arguments.
- [ ] Treat the remaining tilted squares as defects/insertions constrained by
      the scaffold.
- [ ] Determine whether this reduces the problem to one or two tilt parameters.

### Decision gate

- [ ] Select the route with the shortest conceptual global argument.
- [ ] Document why the discarded routes fail or are weaker.

Deliverable:

```text
research/eight/STRUCTURAL_REDUCTION.md
```

## Gate 4 — n=8 state and label model

Only after the candidate/contact structure is understood:

- [ ] Choose sorted local state coordinates for an exterior square.
- [ ] Write the exact containment region at the candidate radius.
- [ ] Derive support/marker branches from actual candidate contacts.
- [ ] Define a label as the minimum of those geometrically meaningful branches,
      if a single label is useful.
- [ ] Prove branch-transition loci exactly.
- [ ] Identify capped/convex regions and their true vertices.
- [ ] Avoid introducing branches solely because a numerical estimate changes
      quality there.

Deliverable:

```text
research/eight/STATE_MODEL.md
```

## Gate 5 — critical pair inequalities

For every pair type required by the structural reduction:

- [ ] state the exact support inequality;
- [ ] reduce disjointness to one of the four separating axes;
- [ ] exploit sign/active-label symmetry;
- [ ] use disk support, weighted separators, or force cones;
- [ ] use monotonicity/concavity on the full continuous sector;
- [ ] record equality/contact conditions, not merely nonnegativity;
- [ ] avoid Bernstein/coefficient-vector positivity unless it is only final
      transparent bookkeeping after a human sign argument.

Maintain a table:

| Pair/contact type | Separator axis | Active branches | Human inequality | Equality |
| --- | --- | --- | --- | --- |
| TBD | | | | |

Deliverable:

```text
research/eight/PAIR_INEQUALITIES.md
```

## Gate 6 — global lower bound

- [ ] Assemble the pair inequalities into the chosen structural invariant.
- [ ] Prove every packing below the candidate radius contradicts either:
      - the angular budget;
      - the forced contact/separator graph;
      - or a weighted global support inequality.
- [ ] Keep the lower-bound endpoint independent of numerical search artifacts.
- [ ] State clearly which portions are strict below the candidate radius and
      which extend to equality.

Deliverable:

```text
research/eight/LOWER_BOUND_PROOF.md
```

## Gate 7 — equality and uniqueness / classification

Do not assume uniqueness in advance.

- [ ] Determine numerically/geometrically whether the optimum appears isolated
      or has continuous degrees of freedom.
- [ ] Classify zeros/equality cases of every support inequality used above.
- [ ] Recover the contact cycle/graph at equality.
- [ ] Reconstruct centers and orientations from contacts.
- [ ] Identify any continuous family of optimal packings.
- [ ] Formulate the correct congruence/classification statement.

Deliverable:

```text
research/eight/EQUALITY_PROOF.md
```

## Gate 8 — Lean handoff

Research code remains separate until the mathematics stabilizes.

- [ ] Implement generic reusable lemmas under `research/eight/lean/**`.
- [ ] Give exact theorem interfaces matching eventual production needs.
- [ ] No `sorry`, `admit`, external success premise, or generated finite
      classifier in the final research proof path.
- [ ] Add dependency checks excluding any exploratory certificate machinery.
- [ ] Compile locally before proposing production integration.
- [ ] Only after the proof stabilizes, hand off production integration as a
      separate change.

## Immediate next tasks

1. [ ] Reconstruct the candidate and contact graph.
2. [ ] Decide whether the two-square canonical/support model can be factored
       into a generic reusable research module without n=7 labels.
3. [ ] Test the candidate contact graph against:
       - marker-gap budget;
       - weighted separator cycles;
       - near-axis scaffold rigidity.
4. [ ] Derive the first exact structural lemma before writing large Lean files.

## Human-proof standard

A successful n=8 proof should read schematically as

```text
candidate contact geometry
  -> generic separating-axis reductions
  -> small number of candidate-derived state/contact types
  -> global structural theorem
  -> whole-domain support/monotonicity/concavity
  -> forced equality graph
  -> candidate radius and classification
```

not as

```text
many angle boxes
  -> generated rows / sampled minima
  -> acceptance by exhaustive computation.
```


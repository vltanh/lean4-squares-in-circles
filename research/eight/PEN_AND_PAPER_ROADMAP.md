# A pen-and-paper route to the eight-square theorem

Orientation date: 2026-10-10. Starting PR head:
`09e7c0eb5978874f8aaf4c71e646025c6be73607` (26 research commits).

The target is the least radius of a disk containing eight unit squares with
pairwise disjoint open interiors. Write `R8` for that infimum and `R*` for the
existing exact candidate, numerically `1.978770865339763...`.

## 1. Evidence at the starting PR head

The original checklist in PROOF_TRACKER.md predates most of the PR. Its empty
boxes do not mean that candidate reconstruction still needs to start over.
The current evidence is:

| Result | Location | What its proof currently uses |
| --- | --- | --- |
| Five projected inequalities imply an exact scalar feasibility condition | FIVE_CORNER_REDUCTION.md, section 1 | A complete analytic argument using disk support and monotonicity |
| An exact algebraic stationary candidate exists | FIVE_CORNER_REDUCTION.md; EXACT_CONFIGURATION_AND_FREEDOM.md | A rational contraction certificate in a small root box |
| Eight squares fit at R*, with at least three independent sliders | EXACT_CONFIGURATION_AND_FREEDOM.md | Symbolic contact identities plus interval checks of strict margins |
| R* is optimal for the specified five-corner chain | FIVE_CORNER_OPTIMALITY.md | Interval verification of convexity and exclusion of the complement |
| Every eight-square packing has squared radius greater than 19/5 | GLOBAL_LOWER_BOUND.md | A complete-domain pair-marker certificate and a circle budget |
| At squared radius at most 98/25, a unique central square contains the closed radius-1/12 disk in its open interior | CENTRAL_CORE_CERTIFICATE.md | Another complete-domain pair-marker certificate |
| The other seven squares have ring gaps between 7/8 and 29/28 | SHARP_MARKER_RING.md | A pair-marker certificate, then elementary cyclic arithmetic |
| A state potential telescopes around a seven-cycle | SEVEN_CYCLE_POTENTIAL.md | An analytic abstract lemma; the needed sharp pair bounds are unproved |

The numerical values and the executed certificate results above are reports
of the existing PR. They are not new independent replays or new analytic
proofs. In particular, the current unrestricted sharp lower bound is OPEN.

### New analytical results in this continuation

These results have written proofs. They do not invoke a box cover or upgrade
the earlier certificate-only premises.

| New result | Proof |
| --- | --- |
| Eight explicitly specified rational squares fit in radius $\sqrt{9789}/50 = 1.9787875\ldots$ | [ANALYTIC_RATIONAL_CONSTRUCTION.md](ANALYTIC_RATIONAL_CONSTRUCTION.md): seven exact farthest-vertex comparisons and a complete separating-line argument for all 28 pairs |
| Eight squares fit at the exact least five-corner radius $\widehat R$, with three independent sliders | [ANALYTIC_EXACT_CONSTRUCTION.md](ANALYTIC_EXACT_CONSTRUCTION.md): the stationary order and the whole-family enclosure in HUMAN_FAMILY_ENCLOSURE.md give all containment and 28 pair checks analytically |
| At every fixed tilt the five-corner defect is strictly convex in its position variable on the complete radical domain | [HUMAN_FIVE_CORNER.md](HUMAN_FIVE_CORNER.md), Lemmas 1–2 |
| A global $F_{tt}+4F>91/45$ inequality gives a convex transformed fixed-position tilt defect | HUMAN_FIVE_CORNER.md, Lemma 3 |
| The family optimum is attained at an interior stationary point and is exactly the least admissible q in a nine-variable polynomial system | HUMAN_FIVE_CORNER.md, Lemmas 4–8; the exact zero-tilt optimum is $\sqrt{2257}/24$ and nonzero tilt improves it |
| Feasible position minima move monotonically with tilt; simultaneous stationary points satisfy $u,v<1$, hence $r>U$ and $w>V$ | HUMAN_FIVE_CORNER.md, Lemmas 9–11; the additional corner bounds $k_1>1$, $k_2>1/2$ hold on the whole relevant radical domain |
| The stationary polynomial system has a unique admissible solution in $(79/40)^2\le q\le9789/2500$, and this solution is the global family optimum | [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md): every critical point of the minimized tilt envelope has positive second derivative, even when its defect is positive |
| Relative to any selected square, at most one neighbor per corner lacks every separator on the selected square's axes | [HUMAN_STRUCTURAL_LEMMAS.md](HUMAN_STRUCTURAL_LEMMAS.md); in an eight-square packing at least three neighbors admit such axes |
| Every eight-square packing with $q\le98/25$ has a unique square containing the disk center in its open interior | [HUMAN_GLOBAL_GEOMETRY_CLOSURE.md](HUMAN_GLOBAL_GEOMETRY_CLOSURE.md): the one-square inequality $3L_1+L_{5/4}\ge\pi$ and its exact equality cases force the conclusion by angular capacity |
| A disk of radius two cut by $x\ge1/2$ contains at most two unit squares | [HUMAN_CAPACITY_BOUND.md](HUMAN_CAPACITY_BOUND.md); this bounds outward central sides and includes an exact counterexample to applying the same bound to inward sides |
| A radius minimizer exists and has a nonzero balanced separator stress with exact disk-admissible center supports | [BALANCED_SEPARATOR_REDUCTION.md](BALANCED_SEPARATOR_REDUCTION.md) |
| Normal contact multipliers satisfy center balance and the complete angle stationarity equations, including rotation of the selected normal | [HUMAN_ROTATIONAL_STRESS.md](HUMAN_ROTATIONAL_STRESS.md) |
| A straight chain of k unit squares needs radius at least $\sqrt{k^2+1}/2$ | [HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md), section 7; four-square chains are impossible below radius two |
| A strictly interior square with two actual contacts in a contact-minimal minimizer aligns its side with its two opposite separators | HUMAN_CYCLE_ANALYSIS.md, section 8 |
| Two strictly interior degree-two squares sharing the same two neighbors force all four square frames to be parallel | HUMAN_CYCLE_ANALYSIS.md, section 9; the common neighbors are exactly distance one apart |
| Every nontrivial actual-contact component in a minimum-contact minimizer contains a cycle | [HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md); every actual leaf is radial, all leaves share a central neighbor, and there are at most two |
| Contact forces can be applied at actual common points, with exact force and moment equilibrium | [HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md); every positive-stress bridge is radial, and a stress-tree component must meet a square containing the disk center |
| If $\sqrt2+1/2<R<2$, every nontrivial physical stress component has a cycle carrying a nonzero moment circulation | HUMAN_CONTACT_EQUILIBRIUM.md, sections 7–8; the lower endpoint is an explicit hypothesis, not a new analytic lower bound for eight squares |
| Stress leaves have two exact radial forms; three-vertex stress trees have only four possible radii | [HUMAN_STRESS_TREE_ENDS.md](HUMAN_STRESS_TREE_ENDS.md); this classification is analytic for $R>\sqrt2$ |
| The minimum weight of a closed seven-step walk on four symmetric types is exactly $\min(\tau+4m,L)$ | HUMAN_CYCLE_ANALYSIS.md, section 2; the continuous geometric pair bounds required to apply it remain open |

The sharp conditional family radius is now specified by a **unique
admissible stationary solution in an explicit strip**, with a complete
analytical proof of global optimality. The earlier tiny root box is not
needed for this exact definition. The common-frame theorem derives
orientation from a stated actual-contact pattern; it does not yet force
that pattern in every optimal packing.

## 2. Proof standard for this continuation

The present request is pen and paper, with no Lean proof yet. New positive
claims need displayed hypotheses and human-checkable reasoning. Exploratory
algebra may help discover identities; a sampled minimum, fitted label,
interval-box cover, or external PASS result will not close a continuous
argument in this continuation. Earlier computational results remain useful
evidence, explicitly labeled as such.

All new files and edits stay under `research/eight/`. Research commits include
`[skip ci]`. A candidate-radius theorem, a conditional theorem, and a theorem
about arbitrary packings must remain visibly distinct.

## 3. The actual missing implication

The existing conditional chain is

    (P2-P1).y >= 2,
    (P2-P3).x >= 3,
    (P3-P4).y >= 2,
    f dot (P4-P5) >= 1+sin(t),
    e dot (P1-P5) >= 2+cos(t),

where the five points lie in the packing disk, `0 <= t <= pi/4`,
`e=(cos(t),sin(t))`, and `f=(-sin(t),cos(t))`.

To use it globally one must prove that a hypothetical packing of radius
less than R* yields these inequalities, or prove a different sharp
inequality that covers all its alternatives. The seven-marker count
`(2,2,2,1)` does not imply that six square orientations agree or that the
horizontal projected span is 3. Neither assertion may be inserted as a
normalization.

The most useful target is an inequality or a reduction for an actual
minimizer. It is unnecessarily strong to demand that every packing below a
coarse ceiling already have the candidate's literal contact graph. Any use
of minimizers must first justify attainment and allowed deformations.

## 4. Work packages and their completion criteria

### A. Replace the conditional optimization certificate

Exploit the geometry of the five disk points before expanding the existing
nested radicals. For fixed tilt the problem is convex in the points and
radius. Derive its support dual with nonnegative multipliers, then allow the
multipliers to depend on the tilt. A fixed candidate stress is insufficient:
NEGATIVE_RESULTS.md records the failed frozen-stress experiment.

An alternative is to eliminate the tilt analytically from the scalar
condition and prove whole-interval convexity or monotonicity of the remaining
one-variable function. Split only where a genuine domain endpoint, a support
branch, or a stationary equation changes. The goal is a theorem covering all
`0 <= t <= pi/4` and the complete feasible ordinate interval, including
radicand-zero endpoints. Local Hessian positivity is insufficient.

**Completion criterion:** a human proof that the projected chain has minimum
R*, an exact root selection, and equality conditions for its five points.
This is valuable even before the global structural theorem is found.

### B. Establish an analytic structural starting point

Audit the central-square, central-core, and marker-ring reductions separately.
The numerical coefficients of the current markers do not provide a human
reason for their full-domain pair bounds. Either replace these bounds by
geometric support inequalities or use an independent structural route that
does not need them.

Start with compactness and fixed-orientation separating-axis geometry. Keep
the actual central square, all four possible separating axes per pair, and
all non-neighbor disjointness constraints. A supporting inequality may discard
constraints to give a necessary condition, but a construction or equivalence
argument must restore every omitted constraint.

**Completion criterion:** a rigorously justified small collection of geometric
possibilities for a minimizer, with no numerical mesh or assumed parallelism.

### C. Couple neighboring exterior squares to the central obstacle

The leading global task is a three-square inequality involving the central
square and two consecutive exterior squares, or a balanced sum of such
inequalities around the seven-cycle. Retain exterior-axis separators where
they occur. Seek a nonnegative weighted combination that cancels center
coordinates and leaves disk-support terms, as in the six-square method.

The odd length seven may matter: cheap alternating state transitions need not
close after seven steps. A state-potential argument is legitimate only after
its continuous pair bounds, the precise type domains, and all sharp equality
states are proved. Arbitrary numerical type cuts or a successful finite-state
fit do not establish that argument.

**Completion criterion:** either the five-corner obstruction is forced, or an
alternative sharp cyclic/support inequality covers every surviving case.

### D. Prove the construction and handle equality

Replace the remaining strict-margin interval checks by a small explicit
rational neighborhood with displayed elementary inequalities, or by direct
identities and monotonicity from the exact root specification. Preserve the
known sliders. Equality for the five-corner obstruction can be rigid while
some of the eight squares still move.

**Completion criterion:** an analytic construction at R* and a correct
description of the equality freedom actually proved. A maximal
classification is a further theorem; it must not delay a valid radius bound
or be inferred from one displayed three-parameter family.

### E. Assemble the unrestricted theorem, then prepare a later handoff

Combine the analytic structural statement with the sharp support inequality
and construction. Check the endpoint separately from the strict subcandidate
contradiction. Only after this mathematical dependency chain is closed should
Lean theorem interfaces or formal proof files be written.

**Completion criterion:** an unconditional theorem `R8 = R*` whose proof
contains no unproved structural assumption and no certificate-only premise.

## 5. Reductions already known to fail

Do not restart these as if they were available lemmas:

* Dropping the central square: seven exterior squares can fit below R*.
* Independently pushing every exterior square to circle contact: it can create
  overlap, even while preserving the core and ring necessary conditions.
* Requiring each central/exterior pair to separate on a central-square axis:
  an exact two-square counterexample uses only an exterior-square axis.
* Seeking a universal pair gap of `2*pi/7` from a single quarter-window state
  label: the exact two-pair obstruction already rules this out.
* Inferring a rigid eight-square equality configuration: the candidate has
  at least three independently variable positions.

The corresponding exact examples are in NEGATIVE_RESULTS.md,
RADIALIZATION_OBSTRUCTION.md, CENTRAL_PORT_NEGATIVE.md,
UNIFORM_HEPTAGON_MARKER_OBSTRUCTION.md, and
EXACT_CONFIGURATION_AND_FREEDOM.md.

## 6. Concrete remaining roadmap

### Priority 1: force a sufficient contact pattern in a minimizer

Central-square existence in the full relevant radius range is now proved
analytically by HUMAN_GLOBAL_GEOMETRY_CLOSURE.md. It uses two auxiliary
circles and total angular measure, including disconnected intersections.
This removes the marker-certificate dependency from central existence;
the central core, individual marker gaps, and quadrant counts remain
separate stronger assertions.

Use a radius minimizer with the fewest actual contacting pairs. Its radius
is below two by the rational construction. Attainment, the allowed local
deformations, exact center support, normal multipliers, and the interior
two-contact lemmas are now available analytically.

A nontrivial actual-contact component must contain a cycle. Positive-stress
components obey further restrictions: a bridge has a radial force line
meeting the actual contact segment, and a tree component must contain a
square through the disk center. These are exact graph reductions. They
allow actual contacts carrying zero stress, so the two graphs cannot be
identified.

The physical stress theorem excludes all tree components when
$\sqrt2+1/2<R<2$. Using the old bound $R_8^2>19/5$ puts the eight-square
minimum in this interval, but that use retains its computational premise.
An entirely analytic proof must establish a sufficient lower bound or
cover the remaining smaller-radius possibilities separately.

A useful target is the following specific intermediate statement:

> Some minimizer has two squares strictly inside the circle, each with
> actual contact degree two, and both have the same two neighbors.

This statement is still **open**. If proved, it would now force a
four-square parallel arrangement without any orientation assumption. In the
candidate these squares are C,T between B,D. One would then need to force
the continuations through A,E,H,G, with the projected lengths needed for
the five-corner chain. A theorem that directly gives the chain, or a sharp
inequality for the alternatives, would be equally sufficient.

Keep actual contacts, positive-weight stress edges, and available
separators distinct. A stress graph may omit real contacts; choosing one
exterior-owned separator does not prove that no central-owned separator
exists. Neither the cap bound nor the exceptional-corner bound alone
classifies the whole graph.

### Priority 2: identify the least family root analytically

**Completed.** Write $\widehat R$ for the sharp projected five-corner
radius. HUMAN_FAMILY_CLOSURE.md proves that the defining stationary
polynomial system has exactly one admissible solution in

$$
(79/40)^2\le q\le9789/2500.
$$

This solution exists, gives $q=\widehat R^2$, and is the global conditional
optimum. The proof first encloses every feasible chain analytically. It
then proves positive Hessian determinant at every critical point of the
minimized tilt envelope in the remaining strip, without assuming
nonpositive defect. Therefore each radius has at most one interior tilt
minimum. Strict radius monotonicity gives the unique stationary root.
This closes the former gap between separate coordinate convexity and
global optimization. A tiny numerical isolating box is unnecessary.

### Priority 3: construct eight squares at the selected exact optimum

**Completed.** ANALYTIC_EXACT_CONSTRUCTION.md extends every selected
least-family-radius stationary point to eight squares. The proof uses
$1/2<v<u<1$, $R>79/40$, and $\tan t<1/5$, all now established
analytically. It checks every farthest vertex and all 28 pairs, and supplies
three independent closed slider intervals with positive residual margins.
The resulting unconditional upper bound is $R_8\le\widehat R$.

This construction does not depend on identifying a tiny numerical root
box. The equality $R_8=\widehat R$ still needs the unrestricted lower
bound. The exact radius appearing in that target is now uniquely selected
by the analytical theorem in Priority 2.

### Priority 4: assemble the sharp theorem

Combine the unrestricted reduction, the sharp conditional obstruction, and
the exact construction. The required conclusion remains $R_8=R_*$. The present
notes do not yet justify it. Only after these mathematical steps close should
work on a Lean proof begin.

## 7. Reporting rule

New lemmas are committed as they become reviewable. A failed proposed
inequality is recorded only when there is a precise counterexample or a
useful mathematical obstruction. The seven-cycle route remains available,
but its continuous pair inequalities and equality states still need proof;
the exact four-type walk formula alone does not supply them.

No completion of the unrestricted n=8 proof is claimed by this roadmap.


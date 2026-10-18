# Small-step roadmap for the unrestricted eight-square proof

Starting head for this reorientation: `bd095cb3f2e8380233691bc396d7580df2529037`.
All statements concern unit squares with pairwise disjoint open interiors.
No Lean proof is part of this continuation.

## 1. Fix the target before further reductions

Let q_dagger be the unique positive-radical solution of the stationary
system in HUMAN_FIVE_CORNER.md, equations (27)--(30), in the interval

    (79/40)^2 <= q <= 9789/2500,

with `0<s<c` and the sign conditions stated there. HUMAN_FAMILY_CLOSURE.md
proves existence, uniqueness and global optimality for the projected
five-corner family. Put `R_dagger=sqrt(q_dagger)`.
ANALYTIC_EXACT_CONSTRUCTION.md proves `R8<=R_dagger`.

The remaining target is `R8>=R_dagger`. The decimal candidate and its
previous tiny isolating box are not assumptions in this target.

The earlier notes already supply an attained radius minimizer, the
analytical bound `sqrt(2)+1/2<R8<2`, and a unique square C containing zero
in its open interior. They supply normal physical contact stresses and
exclude exterior directed moment cycles of lengths three and four.
These are inputs, not the unrestricted sharp theorem.

## 2. Reduce disconnected possibilities first

| ID | Exact next assertion | Dependencies / proof test | Status |
| --- | --- | --- | --- |
| G1 | Every nontrivial actual-contact component of a contact-minimal minimizer is a local minimum of its own containing radius R8. | If it admitted a nearby smaller-radius packing, slightly expand its centers to separate every pair in that component. Preserve its positive distances from all other components. | To prove |
| G2 | Such a component admits its own normalized physical contact stress. | The strict-direction and finite-separation proof of HUMAN_CONTACT_EQUILIBRIUM.md is local; check its normalization and all inactive constraints. | To prove |
| G3 | Any nontrivial physical stress component omitting C contains at least five squares. | Nonzero moment circulation, exterior winding, and cross occupancy. | Ready to assemble |
| G4 | No nontrivial physical stress component containing C has two or three vertices. | Use that C is strictly inside the disk. With only two incident positive forces, its normals must be opposite. Check contact impossibility between the two resulting opposite neighbors. | To prove |
| G5 | Every normalized physical stress has exactly one nontrivial component. | G3 and G4: two components would require at least 5+4 squares. Isolated zero-stress vertices must be retained. | To prove |
| G6 | All actual contacts belong to one connected component, possibly with isolated squares outside it. | Apply G1--G5 to independently supported stresses on the actual components. Do not confuse this with absence of isolated squares. | To prove |

## 3. Turn angular order into quantitative restrictions

The existing winding theorem is qualitative. The next tests must retain the
actual contact points, the central square and the unused squares.

| ID | Exact next assertion or decision | Completion criterion | Status |
| --- | --- | --- | --- |
| A1 | Bound the angular advance of one exterior square from its incoming contact to its outgoing contact. | A displayed sharp bound in terms of R and genuine support data; all vertex/edge cases included. | Open |
| A2 | Translate A1 into a lower bound on the length of a directed exterior cycle. | A complete angle sum, not a count of circle contacts or sampled marker gaps. | Open |
| A3 | Separate cycles avoiding C from cycles passing through C. | Specify the contact path through C and the exact constraints it inherits from force and moment balance. No assertion that a selected stress avoids C. | Open |
| A4 | Account for every square not on the selected cycle. | A containment or separation inequality for each such square. Replacing the eight-square problem by a seven-square exterior ring is invalid. | Open |
| A5 | Decide whether the surviving cases force the twin pattern or require a different sharp inequality. | Prove the pattern, or retain and bound each alternative. The pattern is not a normalization. | Open |

A1--A5 are proof obligations, not a claim that the cycle route necessarily
succeeds. In particular, an upper bound at radius two that is too weak at
R_dagger is not a sharp closure.

## 4. Complete the geometry if the twin pattern is obtained

The hypothesis here is that two strictly interior actual-degree-two squares
share their two neighbors. HUMAN_CYCLE_ANALYSIS.md proves their four frames
parallel. HUMAN_SCAFFOLD_CLOSURE.md proves that one twin is C, that their
convex hull excludes the other squares, and that a vertical domino is a
valid radius-preserving normal form.

| ID | Remaining conditional obligation | Exact output needed | Status |
| --- | --- | --- | --- |
| T1 | Place at least one remaining center in each lower outer column. | Produce squares below B and D with horizontal offsets satisfying the proved 7/8 projection lemma. | Open |
| T2 | Select the first four disk points consistently. | Obtain `(P2-P1).y>=2`, `(P2-P3).x>=3`, `(P3-P4).y>=2` using the same P2 and P3. | Follows once T1 is proved |
| T3 | Control the last two squares jointly, retaining all their mutual separators. | Produce one frame e,f and one disk point P5 with `f.(P4-P5)>=1+sin(t)` and `e.(P1-P5)>=2+cos(t)`. | Open |
| T4 | Normalize the resulting angle without losing inequalities. | Prove `0<=t<=pi/4` after a permitted relabeling/reflection; do not assume shared orientations in T3. | Open |

T1 does not follow merely from an individual side capacity. T3 is not
supplied by finding separate support points for its two inequalities: the
same point P5 is required.

## 5. Final assembly and audit

1. Apply the conditional family lower bound only after all five projected
   inequalities have been obtained for arbitrary minimizers, or after an
   alternative equally strong bound has covered the missing cases.
2. Combine `R8>=R_dagger` with the exact construction to get equality.
3. Audit the dependency graph for any unproved twin, degree, orientation,
   circle-contact, connectedness, or marker assumption.
4. Keep the known three construction sliders. A radius theorem does not
   automatically classify every equality packing.

Each completed lemma will be committed with `[skip ci]`. A failed target
will be replaced by its exact obstruction, not silently assumed. At this
starting head, steps 1--2 of the final assembly are not completed.

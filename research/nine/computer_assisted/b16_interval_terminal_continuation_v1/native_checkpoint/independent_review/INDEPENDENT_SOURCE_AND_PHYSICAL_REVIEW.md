# Independent review of the B16 exact interval continuation

## Conclusion and scope

The prepared continuation is sound at its declared regional scope. It replaces
exactly 14 previously OPEN, zero-round leaves in the retained 45-node tree by
existing exact interval terminals. The other 31 node payloads are byte-identical.
All initial states, parent links, branch choices, completed bound rounds, child
lists and complete covers are preserved. The result has 16 excluded leaves and
14 OPEN leaves, so even this restricted region remains OPEN.

The region is the merged closed I21/I22 part of original
`negative-16a2fc93c8d133f0`, mask `001/00`. Its independently replayed restriction
has SHA256 `142b74254b59e00267298ea59fa27bef68b392a220f9509aa4a88221f514d5cc`.
It retains original I's center in

\[
x_I\in[-163627/2097152,\;2457813/4194304],\qquad
y_I\in[-91/120,\;91/120].
\]

The parent declaration covers exactly grid quarters `[2,1]` and `[2,2]` of the
fixed four-by-four partition. The raw path retains the original angle,
F-height and F/H escape predicates; the interval restriction is supplied by
the explicit parent declaration. An unchanged path alone would not prove
whole-original scope. The actual whole-domain verifier returns false for this
restriction schema, and the completed report explicitly retains
`entire_registered_original_domain_retained=false`.

This review gives no whole-original or mask credit. The separate accepted
proofs of the other fourteen I quarters are neither changed nor replaced.

## Physical terminal rules

The screen and completed checker use the same already accepted physical
adapter and exact geometry. No mathematical row or terminal rule is added.
The geometry source hash is
`ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993`.
The accepted-center wrapper hash is
`5e18bec014381a657dde410a1a457ed1f8d7ae02d16e95de3b3d6040ff6cd0c0`.

For leaves **2, 3, 6, 8, 10, 12, 20, 22, 35, 37, 39, 41 and 44**, the unchanged
center propagator derives an empty original-coordinate interval. Its updates
intersect existing certified boxes with necessary center inequalities from
the original links and cones, contained physical insets, the selected proxy
alternative, and the outward-rounded circle/center envelopes. Every update
preserves any physical configuration satisfying that leaf's original
hypotheses. The terminal requires a strict lower-endpoint excess, not equality,
so no shared closed face is dropped. The checker recomputes the propagator
from the full inherited state and accepts only its exact terminal label.

For leaf **43**, the same necessary propagation and its inherited pair interval
give the following incompatible bounds on `y_I-y_F`:

\[
y_I-y_F\ge
-14586234245506722041/34587645138205409280,
\qquad
y_I-y_F\le -640855/1048576.
\]

The first rational is strictly larger than the second. The unchanged adapter
independently intersects the physical and inherited pair boxes, checks the
first empty axis, and requires the exact pair `[5,8]`, axis `1`, lower and upper
literals. The independent byte audit separately checks the positive exact gap.

All nine original squares, 36 corners, 36 pairs, the five marked cones, actual
AB/BC/EF/FG links, strict weak CD link and shared closed faces remain inherited
from the unchanged accepted original and parent proof.

## Constructor and full-cover review

The constructor hashes the source screen and prior manifest, then hashes every
old node before use. Each changed node must have no children, no bound rounds,
and identical node initial, record initial and record final states. The allowed
record change is exactly: change the two status fields, add the independently
validated terminal literal, and remove the former final-state field. It does
not substitute a stronger state, omit an earlier restriction or discard a
partially completed round.

The constructor supports ancestor status updates, but there are **none in this
actual result**. All 31 unaffected payloads, including every parent and the two
earlier exact-reserve leaves, are byte-identical. The independent comparison
reconstructs the entire permitted manifest delta and rejects any additional
change. A complete traversal visits all 45 nodes once, checks all child choice
lists and parent/depth links, and recovers exactly seven four-way proxy unions
and eight two-way closed-angle unions. No sibling is omitted after an OPEN
branch is encountered.

The unchanged bounded-memory tree checker freshly reconstructs each child from
its certified parent and checks literal initial-state equality before the
unchanged record core processes any bound round or terminal. The terminal
screen is discovery/preparation evidence; it is not substituted for those
checks in the completed full replay.

## Completed evidence and review limits

Root's full fresh gate completed in session **16960 with observed exit 0**, as
reported by root. Its report SHA256 is
`03754a15723bc8e9fc67a685a980ccaa50d034487ca94b827849d1acc31be451`.
It freshly replays the original/merged-parent ancestry, all 45 node records,
all 21 retained bound rounds, 2,324 deductions and 7,865 printed rows, including
the 14 new exact terminals. Its saved log is retained unchanged.

This independent review read the complete screen, constructor, physical
early-terminal dispatch, record-core terminal path and lazy cover reader. Its
separate byte/domain/cover audit completed in session **2743, observed exit 0**,
rehashing all **293** source identities in the completed report. It also checks
the exact old/new node bytes, report counters, domain restriction and complete
cover topology. It does not duplicate the full weighted arithmetic run.

The constructor's manifest and attachment retain their historical
`FRESH_COMPLETE_REPLAY_PENDING` fields because those exact preparation bytes
were the inputs to the completed gate. The new publication README and exact
report record the completed result without rewriting the proof inputs.

No numerical search, active tree, Git/index, ledger, Lean, Lake or CI was
started or changed by this review.

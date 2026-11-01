# n=9 — published proof progress

**A.2 remains active. Global optimality, complete equality classification and
the full hand/table manuscript remain OPEN.** No Lean, Lake or CI was run.

[Canonical roadmap](DEEP_GATED_ROADMAP.md) · [same gate registry](gates/ACTIVE_ROADMAP.json)

## Publication recovered; fixed case count retained

The previously local coupled-separator checkpoint is now published in
`d9461466b5495bd92f8f0244f8b7a7c003ae8d05`, on top of the sharp-neighborhood
publication `d05959c9f4a3347b5725fb2f761b765717593234`. The original 7,915
canonical root IDs are unchanged: **5,838 EXCLUDED, 2,077 OPEN**.
This publishes the earlier 1,852 additions to the 3,986-exclusion baseline;
it is not 1,852 newly discovered exclusions in this publication session.
The coupled proof uses 247 cores, 401 nodes, 77 exhaustive binary splits and
8,777 propagation rows, with all 83 square-pose and 176 disk-support prior
cores retained. See [proof and reproduction](computer_assisted/COUPLED_SEPARATOR_CERTIFICATES.md)
and [pinned full-replay summary](computer_assisted/coupled_separator_verification_summary.json).

The complete producers, selected core lists, separate verifiers, hand derivations
and verification summaries are committed. The larger generated forests, root
manifests and full rational appendix remain deterministic outputs, pinned by
hashes and included in the conversation archives. They are not silently claimed
to be checked into GitHub. Source-only reproduction regenerates them.

## New continuation: a strictly wider sharp terminal

The former seven-square terminal is in
[SHARP_NEIGHBORHOOD_THEOREM.md](computer_assisted/SHARP_NEIGHBORHOOD_THEOREM.md).
Its extension and original-coordinate guard interface are published in
`cd1ab86a45d602ced0e133790c90d70cd0307d5c`:
[WIDE_SLIDE_SHARP_TERMINAL.md](computer_assisted/WIDE_SLIDE_SHARP_TERMINAL.md).

Keep horizontal deviations and anchor-height deviations within 1/8, independent
frame tilts within 1/64, and normalize ONE common frame using M0. Inner middle-row
height deviations now range over **[-1/8,11/16]**, and the bottom-middle deviation
over **[-19/32,1/8]**. The same exact conclusion holds:

    q - 1105/256 >= V/256 + (1/2) sum_anchors w_i |deviation_i|^2,
    w_0=w_3=23/64, w_4=w_6=9/64.

The proof recenters each row before telescoping. A seven-row signed table has
minimum reserve 675/1048576. Its separate arithmetic checker re-expands the two
physical polynomial identities, checks all 14 endpoint layers and all 126 full
six-tilt layers, and rejects eight corruptions. Sixty-four physical rational
equality controls pass, 52 outside the old vertical neighborhood.

For q<=Q, the lower bound on the bottom-middle deviation is automatic from
|c|<91/60, with exact slack 7/480. The local equality slide ranges are characterized
including their algebraic lower circle endpoint. This is not a full nine-square
equality classification or a global extraction theorem.

`emit_sharp_terminal.py` expresses every chart guard in the original coordinates,
including an optional reflection and selected seven labels. It introduces no
independent real variables and preserves all original corners/pairs and any fixed
hex-cell root. Its 120 exact physical-witness emitted-model controls pass.
The guards are sufficient terminal hypotheses, NOT a claimed global cover.

## Gate status — same IDs and goals

| Gate | Current evidence |
|---|---|
| A.0 / A.1a | Original physical-model source available; final independent human audit remains |
| A.1b / A.1c | Same exhaustive closed positional cover; all IDs and boundaries retained |
| A.2 | **OPEN: 5,838 excluded, 2,077 open. Wider sharp terminal available conditionally.** |
| A.3 | Global completion OPEN; prior complete partial-certificate replay supplied |
| B.1 | Same closed equality-domain cover; attaining root 7820 remains OPEN |
| B.2 / B.3 | Global equality classification OPEN; the widened seven-square chart is classified locally |
| C.1 / C.2 | Local three-cell and sharp-table arguments supplied; global manuscript/audit OPEN |

## Exact next obligation

For each surviving physical domain, prove a complete contradiction or prove
ALL hypotheses of a valid sharp terminal in one common frame. Appending guards
to a model is not proof that its unguarded domain satisfies them. No original
root is removed from the counter merely because it contains an attaining pose
or some subdomain in the sharp neighborhood. Closed-Q pruning and sharp q<Q
terminals must be joined by an exhaustive caller.

Additional exploratory searches in this session found no new accepted original
root exclusions. The count therefore remains 5,838 / 2,077. A compatible finite
graph assignment is only a relaxation witness, not a physical square packing.
No separate human reviewer, global solver UNSAT, Lean, Lake or CI is claimed.

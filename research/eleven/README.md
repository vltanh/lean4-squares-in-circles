# Eleven squares in a circle

This research branch begins the unrestricted eleven-square problem. Every
square may rotate independently and boundaries may touch. The sharp lower
bound and complete equality classification are **open**. No Lean is written
in this phase.

Start with [the deep gated roadmap](DEEP_GATED_ROADMAP.md). It is the current
status authority; [the progress ledger](PROGRESS_LEDGER.md) records completed
checkpoints. [Lessons from n=8](N8_METHOD_AND_SOURCES.md) explains the proof
discipline and pinned sources behind the roadmap.

The first closed construction gate is an [exact feasible upper bound](EXACT_UPPER_BOUND.md)
of q11 <= 49013/10000. Its rational witness certifies all 44 vertices and all
55 pair separators; run `python3 check_rational_witness.py` in this directory.
This bound is close to the published layout but is not asserted to be sharp.

The stronger [exact contact-family construction](CANDIDATE_CONTACT_SYSTEM.md)
now gives q11<=q_c, where q_c is a locally isolated root near
4.901206412408145 (radius about 2.2138668461). It includes a nonempty sliding
interval. Run `python3 isolate_contact_root.py` to replay its rational interval
certificate; [independent review](CONTACT_ROOT_REVIEW.md) records its scope.
Existence and feasibility are proved; optimality remains open.

The [finite separator cover](FINITE_SEPARATOR_COVER.md) proves an exhaustive
8^55-cell polynomial encoding, compact attainment and a conditional stress
identity. A useful reduced terminal classification remains open.

[Coordinate rank cases](COORDINATE_RANK_CASES.md) closes the first conditional
finite classes: rank extraction, a forbidden corner, and the sharp
double-four-chain exclusion. Its 1105 residual masks are explicit; this
branch requires a common separating coordinate frame.

The intended result is an exact least disk radius together with all attaining
packings under the repository's rotation-and-relabeling congruence. Reflected
families must be included explicitly when they are not rotation-congruent.
An approximate published packing is an upper-bound lead, not an optimality
theorem or a complete equality model.

All work here is research. The public definitions, existing theorems, and
registry statements are outside this PR's current scope.

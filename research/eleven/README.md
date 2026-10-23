# Eleven squares in a circle

This research branch begins the unrestricted eleven-square problem. Every
square may rotate independently and boundaries may touch. The sharp lower
bound and complete equality classification are **open**. No Lean is written
in this phase.

Start with [the deep gated roadmap](DEEP_GATED_ROADMAP.md). It is the current
status authority; [the progress ledger](PROGRESS_LEDGER.md) records completed
checkpoints. [Lessons from n=8](N8_METHOD_AND_SOURCES.md) explains the proof
discipline and pinned sources behind the roadmap.

The [unconditional lower bound](arc_budget/UNIVERSAL_LOWER_BOUND.md) now
proves q11>9/2. Five weighted circles and a complete exact pose cover prove
this for unrestricted orientations. The current rigorous radius window is
9/2<q11<=q_c.

The first closed construction gate is an [exact feasible upper bound](EXACT_UPPER_BOUND.md)
of q11 <= 49013/10000. Its rational witness certifies all 44 vertices and all
55 pair separators; run `python3 check_rational_witness.py` in this directory.
This bound is close to the published layout but is not asserted to be sharp.

The stronger [exact contact-family construction](CANDIDATE_CONTACT_SYSTEM.md)
now gives q11<=q_c, where q_c is a locally isolated root near
4.901206412408145 (radius about 2.2138668461). It includes a nonempty sliding
interval. Run `python3 isolate_contact_root.py` to replay its rational interval
certificate; [independent review](CONTACT_ROOT_REVIEW.md) records its scope.
Existence and feasibility are proved. The [positive stress](FIXED_ORIENTATION_STRESS.md)
proves sharpness for the fixed candidate frames and fourteen specified
separators. The [local theorem](LOCAL_OPTIMALITY.md) proves unrestricted
local optimality and complete local equality, allowing every square to
rotate independently. [Independent review](CANDIDATE_STRESS_REVIEW.md)
checks both results. The [full grouped-angle terminal](FULL_GROUP_ANGLE_CLASS.md)
now proves sharpness and the slider equality family for arbitrary centers
and both group angles throughout their full closed first-quadrant square,
under the fourteen prescribed separators. Global capture into this class
remains open.

The [finite separator cover](FINITE_SEPARATOR_COVER.md) proves an exhaustive
8^55-cell polynomial encoding, compact attainment and a conditional stress
identity. The [unrestricted radial extraction](CORE_RING_TWO_CASES.md)
now gives two core/ring count cases: (3,8) and (4,7), with a genuine cyclic ring and all
core squares strictly inside the disk. Sharp bounds for these cases remain
open.

The **entire common-coordinate branch is excluded** at q<=49013/10000:
[shrinking](COORDINATE_SHRINKING_REDUCTION.md) reduces it to axis-aligned
squares, and [six exact cases](AXIS_ALIGNED_EXCLUSION.md) exclude all of them
with 32 nodes and 19 contradiction leaves. An independent implementation
replays the certificate. All 1105 old rank masks are therefore closed in
this window.

[Minimizer stress extraction](SPARSE_MINIMIZER_STRESS.md) now provides an
attained positive contact stress on a connected component of 4 to 11
squares, with bounded multipliers. [Small graph exclusions](CLOSED_STRESS_GRAPH_FAMILIES.md)
strengthen the full-angle component to 5 through 11 squares: spanning contact
stars, four-cycles, and four-paths are impossible. A full-angle stress leaf
always has a strictly circle-unloaded neighbor. The fixed-frame and
full-angle certificates retain separate scope and sparsity bounds; all
omitted squares remain physical completions.

[The finite case ledger](TERMINAL_CASES.md) now identifies the oblique branch
as the global frontier. The [exact oblique witness](NO_COMMON_SEPARATING_FRAME.md)
remains a concrete example; the new exclusion proves every feasible packing
in the candidate window is oblique in this sense.

[Verification and artifact manifest](VERIFICATION.md) records replay commands,
independent reviews and the boundary between these results and future Lean
verification.

The intended result is an exact least disk radius together with all attaining
packings under the repository's rotation-and-relabeling congruence. Reflected
families must be included explicitly when they are not rotation-congruent.
An approximate published packing is an upper-bound lead, not an optimality
theorem or a complete equality model.

All work here is research. The public definitions, existing theorems, and
registry statements are outside this PR's current scope.

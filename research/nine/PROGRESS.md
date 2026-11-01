# n=9 — current hand-proof progress

**Active gate: A.2. The unrestricted lower bound, global equality classification,
and complete hand/table manuscript remain OPEN.** The current instruction is
hand proof, with tables permitted; external mathematical scripts may only test
potential directions. No mathematical script, Lean, Lake, or CI was run in this
continuation.

[Canonical roadmap](DEEP_GATED_ROADMAP.md) · [same gate registry](gates/ACTIVE_ROADMAP.json)
· [current handoff](HANDOFF_A2_2026_11_01.md)

## New broad hand results — November 1, 2026

### The entire two-direction-separable class is proved

[TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md](TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md)
proves q>=1105/256 for every nine-square packing for which two fixed projection
directions separate every pair. The directions may be skew and the square
frames independent. In particular, the entire parallel-square class is closed.

The missing extraction is now supplied: Greene's explicitly cited poset theorem
forces disjoint projection chains of lengths four and three in one of the two
directions, unless both orders have height at most three. In the latter branch,
the actual rank-pair bijection supplies a genuine skew 3-by-3 grid. Two derived
triangle support minima and four elementary inequalities give q>=9/2.
This does not infer a geometric grid from a Greene partition.

The existing physical 4+3-chain theorem completes the chain branch. Equality
forces perpendicular covering directions and seven aligned squares; the new
source supplies an explicit necessary-and-sufficient parameter domain for
**this entire cover class**. It is not unrestricted equality classification.
The old conditional-draft warning is superseded for this theorem, while its
global coverage warning remains necessary.

### The two-square directional cap is now exact and sharp

[TWO_SQUARE_SHARP_CAP_HAND_PROOF.md](TWO_SQUARE_SHARP_CAP_HAND_PROOF.md)
defines rho=(sqrt(1041)-8)/16, d=rho-1/2, k=sqrt(d^2+1/4), and H=rho*d/k.
Every Q-contained square with e.c>=H contains the same point k*e; if e.c>H,
the point is in its interior. Thus any two physical squares satisfy

    min(e.c_1,e.c_2)<=H<109/80<137/100.

The proof is a scalar factorization and two explicit intervals, with a
constructive equality pair and its uniqueness. It replaces the earlier
large cap certificate with a stronger complete hand theorem. Consequences
include a center-segment bound, a disjoint marker-arc budget, and unique
exposure of every actual boundary-square center with projection gap >1/400.

### Two strips replace the small coordinate boxes

[TWO_STRIP_SEVEN_SQUARE_HAND_PROOF_2026_11_01.md](TWO_STRIP_SEVEN_SQUARE_HAND_PROOF_2026_11_01.md)
removes every horizontal coordinate guard and every separate anchor-height
guard from the seven-square sharp terminal. Four centers in -1/16<=y<=3/4
and three in y<=-13/16 suffice, with relative frame tilts at most 1/64 in
the frame of the leftmost middle square. Containment forces the needed
separator axes. The retained displacement squares need no box bounds.

The same exact sharp inequality and seven-square equality family follow.
All fourteen sign-table entries are printed together with one integer
expression permitting direct hand verification. No scripted table generation
or verification was used in this continuation.

### A global strict-counterexample reduction incorporates the cap

[BOUNDARY_NORMALIZATION_WITH_SHARP_CAP_HAND_PROOF.md](BOUNDARY_NORMALIZATION_WITH_SHARP_CAP_HAND_PROOF.md)
gives a self-contained proof that a subcritical packing exists iff nine
pairwise closed-disjoint units fit the Q-disk. A common center expansion
can place a corner on the Q-circle. One common isometry gives the selected
square the exact one-parameter form

    u=(a,b), v=(-b,a), a>=b>0, a^2+b^2=1, 2sqrt(Q)b>=1,
    c=(sqrt(Q)-(a+b)/2,(a-b)/2).

The new cap then forces all eight other centers to have x<H. This reduction
is global: it does not preserve an individual positional root. The resulting
domain is not proved empty.

## Fixed positional accounting — unchanged

| Evidence | Excluded roots | Open roots |
|---|---:|---:|
| Published reproducible baseline | 5,838 | 2,077 |
| Earlier archive-only reported checkpoint | 6,150 | 1,765 |

There are still exactly **7,915 original canonical roots**. The second row
includes 312 earlier locally verified exclusions whose complete new source,
certificate and manifest are not published on this branch. This continuation
does not claim to recover or replay those artifacts. Their archive, digests
and publication boundary remain in the handoff.

The new hand theorems prove broad geometric families. They do not by themselves
exclude every assignment of an original positional root, so the canonical
counter remains **5,838 excluded / 2,077 open**. The attaining root 7820 stays
open under closed-Q pruning. No completion percentage is asserted.

The earlier coupled baseline was published in d946146, retaining all 83
square-pose and 176 disk-support cores and adding 247 coupled cores. Its
producers, verifiers and pinned summaries remain in the branch. The larger
generated forests and manifests are reproducible outputs; they are not
silently claimed to be GitHub blobs.

## What remains at A.2

A hypothetical q<Q packing must avoid every proved sharp terminal. It has no
pair of disjoint parallel projection chains of lengths four and three, admits
no two-direction separation cover, and cannot meet the two-strip terminal.
The original physical constraints and the new universal cap still apply.

The exact remaining obligation is to exclude **all** such configurations,
or force one of the proved terminals. The normalized boundary domain is an
equivalent way to pose this global obligation, with all eight remaining
orientations and every original pair retained. No universal extraction,
global contradiction, or full-root transfer is claimed.

Independent agents and the integrating agent checked the new derivations by
hand. This is not an independent human review or a kernel verification.
A.3 global replay, B.2/B.3 unrestricted equality, and C.1/C.2 complete
manuscript/audit remain open. No new roadmap gate IDs are introduced.

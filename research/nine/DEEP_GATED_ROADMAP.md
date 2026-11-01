# n=9 — canonical proof roadmap (v3, A.2 disk-support update)

**The unrestricted sharp theorem and complete equality classification are OPEN.**
Target: nine independently oriented, interior-disjoint unit squares in a disk
have squared radius at least **1105/256**, and classify every attaining packing.

**Active: A.2.** A complete positional root cover is now available: **7,915
canonical roots, 3,986 EXCLUDED, 3,929 OPEN**. See the
[containment theorem and exact tables](computer_assisted/DISK_SUPPORT_CERTIFICATES.md)
and [independent replay summary](computer_assisted/disk_support_verification_summary.json).
This adds 3,100 exclusions while retaining every previous exclusion and root ID.
This count is for a fixed explicit cover, not a completion percentage or a
claim that the remaining roots are uniformly easy.

## Three theorem deliverables — unchanged

| Deliverable | Status | Acceptance test |
|---|---|---|
| A. Global bound | **OPEN** | Exclude every physical packing at every q<1105/256 |
| B. Equality | **OPEN** | Explicit necessary-and-sufficient families of all q=1105/256 packings |
| C. Hand/table proof | **OPEN** | Complete human-checkable manuscript for A and B |

The same gate IDs and mathematical goals are retained. Experiments, software
setup and method choices are not theorem closures. No historical case counters
are restored. Source proofs and separate exact implementations are available;
no separate human reviewer or kernel verification is claimed.

## A — prove the lower bound

**A.0 — Faithful model [SOURCE AVAILABLE; audit required].** The original
unrestricted emitter has nine independent frames, all 36 original corners,
and all 36 weak pair separations. Its geometric equivalence source proof and
attaining witness are in `computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md`.
A full independent source audit remains part of final acceptance.

**A.1 — Global coverage [EXPLICIT COVER AVAILABLE; exclusions incomplete].**
The nineteen-hexagon theorem covers every physical q<=Q packing without row,
common-direction, contact-graph or stress premises. Each root is the original
physical formula plus nine closed cell assignments. The root models retain
all continuous orientations and separator alternatives. No claim is made that
7,915 root models automatically form 7,915 easy solver jobs.

- **A.1a — sound representation [SOURCE AVAILABLE].** The original formula
  still contains every pose, corner and weak pair separation. The root emitter
  adds six exact quadratic cell inequalities per square and one positive
  algebraic constant sqrt(3), with no extra frame gauge.
- **A.1b — exhaustive explicit cover [PROVED SOURCE + EXACT ENUMERATION].**
  Every center lies inside radius 91/60 and different centers are at least
  one apart. Nineteen closed hexagons of diameter 49/50 cover that disk, so
  the centers occupy nine distinct cells. The 92,378 subsets reduce to 7,915
  canonical subsets under twelve actual disk symmetries. Producer, separate
  enumeration and Burnside counts agree. Each root has a deterministic ID
  and an explicit emitted physical predicate.
- **A.1c — boundary accounting [PROVED FOR THIS COVER].** Closed hex cells,
  arbitrary tie assignment and diameter strictly below one cover shared
  cell boundaries. All original weak contacts and independent orientations
  remain. Fine triangles are discarded only by a strict exact impossibility
  bound; equality compatibility edges are retained. The argument also works
  at q=Q and does not discard singular or repeated-normal configurations.

**A.2 — Close the finite obligations [OPEN / ACTIVE].** The disk-support
certificates add 3,100 exclusions, giving 3,986 excluded and 3,929 OPEN roots.
An exact support formula for the center region of a contained square produces
necessary halfplanes over whole closed orientation intervals. Contracting each
state's positional polygon gives stronger square-owned separator bounds. The
176 new cores have 4,182 propagation rows. The earlier 886 exclusions and their
proof references are preserved; the same original physical root IDs remain.
Any further subdivision must cover every child and retain its root linkage.
No angle sampling, generic position or fixed positive radius gap is used.

**A.3 — Independent global replay [OPEN].** The verifier reconstructs the old
physical pose graphs, replays all 83 prior square-pose cores, independently
rebuilds the contracted polygons and every compatibility edge, and checks all
4,182 new rows and all root transfers. The polygon implementations use distinct
methods: clipping versus feasible supporting-line intersections. Every proof
comparison is integer/rational, with explicit bounds on array arithmetic.
This is complete replay of the present partial certificate, not global closure:
3,929 physical roots still lack contradictions. Final A.3 needs all-q<Q
exclusion of every remaining root, including arbitrarily near equality.

A closes only when the complete physical argument is proved and audited.
Combine it with the known exact q=Q witness to obtain sharp optimality.

### Method choices, not extra gate trees

Primary: exact direct physical certificates. Structural/contact lemmas are
optional tools, but a stress-based caller must establish one globally valid
selection and all of its hypotheses. Switching methods is not theorem progress.
The two-direction summary remains a draft and is not used by the hex cover.
No separate mandatory direct-versus-stress proof trees are introduced.

## B — characterize all equality packings

**B.1 — Complete equality-domain cover [ROOT COVER SUPPLIED].** The same
nineteen-cell theorem and closed-Q root emitter cover every physical equality
packing. The 3,986 current exclusions hold even at q=Q. The known oblique witness
survives in root 7820. This supplies a starting equality cover, not a list of
all equality normal forms.

**B.2 — Necessary normal forms and parameters [OPEN].** Derive every equality
structure up to common Euclidean isometry and relabeling, with exact ranges
for all translations, tilts, slides, endpoints and degeneracies. Do not assume
that the special seven-row equality core is globally necessary.

**B.3 — Constructive converse [OPEN].** Prove that every listed parameter
value satisfies all original corner and pair conditions and that no physical
equality packing is absent. B closes only with necessity and sufficiency.

## C — write the final hand proof with tables

**C.1 — Human reconstruction [OPEN].** The hex-cover proof, exact center-support
theorem, complete interval-containment derivation and finite core tables are
written. The four-cell theorem has a four-row summary with explicit integer
rules for reconstructing each entry. The complete manuscript still requires
all remaining root exclusions and B's equality classification. Large replayable
finite tables are not by themselves the requested final compact hand proof.

**C.2 — Audit [OPEN].** Independently check the full mathematical manuscript,
all exact table comparisons and every boundary implication. The present
separate arithmetic implementation is not a separate human reviewer.
Lean, Lake and CI remain deferred.

## Current evidence and reproduction

Run from `research/nine/computer_assisted/`:

```sh
python make_hex_cover.py
python make_square_pose_certificate.py
python make_disk_support_certificate.py
python verify_disk_support_certificate.py --negative-controls
python emit_hex_root.py --root 7820 --radius strict --output /tmp/n9-root.smt2
```

The producer and independent graph builder use NumPy only for exact
bounded-integer operations; polygon and support arithmetic uses Python int
and Fraction. The final verifier reconstructs its graphs, without trusted caches.
The complete generated certificate, root manifest and full replay report
accompany the continuation archive. Their hashes are pinned in the committed
summary. The source and core list reproduce all results.

The canonical status is `gates/ACTIVE_ROADMAP.json`. The new finite cover does
not imply all 3,929 unresolved roots can be solved by uniform pose refinement.
Closed-Q pruning cannot empty domains containing equality packings. Those
roots need sharp q<Q inequalities, not a fixed numerical gap.
A.2 remains the active gate; all existing gate IDs and goals are unchanged.

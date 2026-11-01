# n=9 — canonical proof roadmap (v3, finite-cover update)

**The unrestricted sharp theorem and complete equality classification are OPEN.**
Target: nine independently oriented, interior-disjoint unit squares in a disk
have squared radius at least **1105/256**, and classify every attaining packing.

**Active: A.2.** A complete positional root cover is now available: **7,915
canonical roots, 81 EXCLUDED, 7,834 OPEN**. See the
[hand cover proof and exact exclusions](computer_assisted/HEXAGON_ROOT_COVER_AND_FIRST_EXCLUSIONS.md)
and [separate verifier report](computer_assisted/hex_verification_report.json).
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

**A.2 — Close the finite obligations [OPEN / ACTIVE].** Five integer/rational
center-pattern certificates exclude 81 entire roots. The remaining 7,834
roots are explicitly OPEN, not sampled feasible. Seek groupwise inequalities
or exact certificates using the full square geometry, rather than repeatedly
refining center-distance bounds alone. Any new subdivision must record all
children and maintain its link to the fixed root manifest. A root closes only
when its complete q<Q domain has a sound exact contradiction.

**A.3 — Independent global replay [OPEN].** A separate standard-library checker
replays the current five-core forest and verifies its transfers to 81 roots.
That is partial replay, not acceptance of the global theorem. Final A.3 requires
proofs for every remaining root, all coverage implications and an all-q<Q
argument arbitrarily close to Q, without trusted floating tolerances.

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
packing. The 81 center exclusions hold even at q=Q. The known oblique witness
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

**C.1 — Human reconstruction [OPEN].** The hex-cover proof and finite orbit
and core tables are written. The full manuscript still needs all remaining
root exclusions and B's complete equality proof. A large exact graph decision
forest is computational evidence with a proved replay interpretation, not by
itself the requested compact final hand argument.

**C.2 — Audit [OPEN].** Independently check the full mathematical manuscript,
all exact table comparisons and every boundary implication. The present
separate arithmetic implementation is not a separate human reviewer.
Lean, Lake and CI remain deferred.

## Current evidence and reproduction

Run from `research/nine/computer_assisted/`:

```sh
python make_hex_cover.py
python verify_hex_cover.py --negative-controls
python test_hex_root_emitter.py
python emit_hex_root.py --root 7820 --radius strict --output /tmp/n9-root.smt2
```

The producer uses NumPy only for exact bounded-integer acceleration. The
separate certificate verifier needs only Python's standard library. The
manifest and certificate are deterministic generated artifacts; their hashes
are pinned in the saved reports and copies accompany the continuation archive.

The canonical status is `gates/ACTIVE_ROADMAP.json`. The new finite cover does
not imply all 7,834 unresolved roots can be solved by the first center-only
screen. That specific mathematical task is now visible under A.2.

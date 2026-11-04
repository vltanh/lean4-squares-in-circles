# Eleven-square research handoff — 23 October 2026

## Resume here

Repository: `vltanh/lean4-squares-in-circles`.
Draft PR: <https://github.com/vltanh/lean4-squares-in-circles/pull/13>.
Branch: `research/eleven-gated-hand`; base: `main` at
`4bea747b3efa13c869b956cb28435efaf21526fa` when this work began.
The last earlier checkpoint was
`ca6aa425a0f15b5523ddd173e60dd8ee73f64bce`; the commit containing this
handoff adds the remaining reviewed artifacts and saved pending work.

The user requested a hand proof before Lean, a deep gated roadmap, finite
case classification, frequent commits, and use of the GitHub connector.
The final instruction was to commit the current work as a future-session
handoff. No Lean was written or run. All PR changes are research artifacts
under `research/eleven/`; existing public theorems are untouched.

**The unrestricted sharp proof is not complete.** The rigorous window is

```
9/2 < q11 <= qc ≈ 4.901206412408145,
sqrt(qc) ≈ 2.2138668461332864.
```

Here q is squared radius. Do not substitute the repository's n=11 radius
placeholder for the research constant. `DEEP_GATED_ROADMAP.md` is the gate
authority, `TERMINAL_CASES.md` is the current case ledger, and
`PROGRESS_LEDGER.md` preserves checkpoint history. Earlier radial counts
in named historical notes are superseded by `CORE_RING_TWO_CASES.md`.

## Closed results

1. **Physical model and compact attainment.** The exact all-orientation
   separator encoding covers all 55 pairs, including weak contacts,
   multiple valid owners and ties. It gives an exhaustive raw `8^55`
   closed-cell cover; that syntactic count is not a solved sharp inventory.
2. **Exact candidate construction.** `CANDIDATE_CONTACT_SYSTEM.md` defines
   qc by an isolated algebraic contact root. A rational contraction proof
   gives existence and uniqueness in its box, and complete corner/pair
   checks prove an exact feasible slider family. The simpler rational
   witness at U=49013/10000 remains useful for coarse reductions.
3. **Entire common-coordinate class excluded.** Shrinking reduces it to
   axis-aligned squares. Six cases, 32 nodes and 19 contradiction leaves
   exclude every packing at q<=U, including all 1,105 old rank masks.
   The leaves have three hand motifs and independent exact replay.
4. **Sharp candidate contact class.** Arbitrary centers and both group
   angles throughout `[0,pi/2]^2` satisfy q>=qc under fourteen prescribed
   signed separators and three orientation groups. All 507 closed angle
   rectangles are solved; equality is the exact slider family.
5. **Unrestricted local sharpness.** Every square may move and rotate
   independently, and physical separator owners may switch. The explicit
   normalized terminal N<=10^-7 forces q>=qc and exactly slider equality,
   uniformly through both endpoints. See `UNRESTRICTED_NEIGHBORHOOD.md`.
6. **Unconditional coarse lower bound.** Five weighted circles and an exact
   2,385-node pose cover prove q11>9/2, with separate arithmetic replay.
7. **Only two radial cases.** At core threshold 41/40, the counts are (3,8)
   and (4,7). Core squares are strictly inside the containing circle;
   ring arcs on radius 27/20 are connected, longer than 7/10, and cyclically
   ordered. All eleven squares and all physical constraints remain.
8. **Four-core shell.** In the four-core case every other center is
   strictly beyond 6/5. The stronger 18-circle certificate has 20,405 nodes
   and 9,187 accepted bounds; supplied replay, separate arithmetic replay,
   and mathematical/source audit all pass. The older 11/10 shell is retained.
9. **Actual minimizer stress.** A connected full-angle positive component
   has 5–11 bodies, at most 3k support-vertex atoms, and at least two
   circle-loaded bodies. Spanning contact stars and all four-body components
   are excluded. A leaf's neighbor is strictly circle-unloaded. A separately
   extracted frozen-frame component retains the weaker 4–11 size bound
   and its distinct sparsity count. Every omitted body remains a physical
   completion; never discard it.
10. **Four-core subcase and moment.** An exact two-by-two block centered
    within 1/50 of the disk center cannot have seven completions. The
    marker proof has 1,445 independently replayed leaves. Four separated
    centers satisfy `sum |pi|^2 >= 2+4|centroid|^2`; physical equality is an
    exact two-by-two block. General four cores need not be a block.
11. **Coarse angular classifications.** The split-core gap theorem on
    radius 27/20 gives 49 cyclic occupancy cases: 16 for (3,8), 33 for (4,7).
    The three-core interleaving cover has 17 dihedral classes from 165 words.
    These are necessary geometric covers. No sharp row exclusion follows
    merely from enumeration.

All closed claims above have written soundness arguments and independent
reviews. Exact arithmetic certificates are not Lean kernel verification.

## The unresolved proof frontier

Both radial cases still require a whole-domain sharp argument, then global
equality exhaustion. The solved fourteen-separator class and the explicit
local neighborhood are terminals available for capture; neither is assumed
to contain arbitrary packings or minimizers.

For **four cores/seven rings**, combine the strict radius-6/5 shell with
core geometry and actual physical ring separation. The promising lead is
to bound ring capacities of complementary angular gaps. Pending exact
common-point certificates strengthen pair spans, but no universal
capacity-at-most-six theorem has been proved. Retain raw split components
on the radius-5/4 circle; they cannot be joined by the radius-27/20 lemma.

For **three cores/eight rings**, `THREE_CORE_INTERLEAVINGS.json` exposes all
17 coarse words. The candidate uses `00000001` and `00000101`, because its
sliding core becomes visible during part of the interval. All 17 words still
need sharp inequalities or valid reductions. Even the zero-active word
remains open. A numerical search found radius-squared near 5.069 there,
which is discovery evidence only. A weighted-circle relaxation with all
three cores inside radius 27/20 was being considered; no certificate was
completed.

The next useful steps are:

1. Independently audit the saved `pending/` manuscripts and sector code.
2. Close an actual coupled core/ring class, preserving every completion
   square and all 55 pair constraints. Do not accumulate conditional
   candidate variations in place of the missing geometric capture.
3. Prove every remaining minimizer enters a solved terminal or is excluded.
4. Assemble q>=qc and recover all equality packings on original centers,
   including reflected copies and the complete slider interval.
5. Complete an independent full hand audit before any Lean translation.

## Saved pending work and failed shortcuts

`pending/README.md` lists the unpromoted artifacts and their replay commands.
Their supplied exact runs passed; independent mathematical review remains.
The ring-sector manuscripts use two circles and must not be conflated:

| Test circle | Single-ring width | Pair-span bound | Marker radius |
| --- | --- | --- | --- |
| 5/4 | at least 63/100 | strictly above 27/20 | 3/2 |
| 27/20 | above 7/10 from main theorem | strictly above 36/25 | 57/40 |

The pair bounds require ring-center radius at least 11/10, available in
the four-core case from the stronger proved shell. The saved localization
draft would place every stress leaf neighbor inside radius 6/5, linking
such neighbors to the four radial cores. It does not bound all unloaded
bodies or the number of leaves sharing one neighbor.

Keep these negative controls in mind:

- The stronger common-coordinate statement q>=5 is false. The committed
  exact axis-aligned counterexample has q<4.91; exclusion is only at U.
- Four radial cores can occur below q=5; that alone does not contradict U.
- At radius 5/4, an axis-aligned core centered at `(0.65,0)` can have two
  circle components with an outer square at `(1.65,0)` in their internal
  gap. Their farthest outer corner has squared norm 4.8725<U. Never fill
  that gap without another theorem.
- The weaker pair-span 13/10 did not force capacity at most six. The saved
  rational `FOUR_CORE_GAP_COUNTEREXAMPLE.json` has two gaps accommodating
  counts 4+3 under that weaker bound. The 27/20 bound defeats this example
  but has no exhaustive four-core proof yet.
- Three cores all invisible at radius 27/20 cannot be excluded just using
  the known three-square optimum: its squared radius 425/256 is smaller.
- The full contact body graph need not be planar: four-way junctions can
  give K4. A pending five-body argument addresses one restricted case.

## Reproduction and artifact integrity

`VERIFICATION.md` lists the standard-library Python replay commands for
closed results. Use ordinary Python, not `python -O`. Most checks reject
optimized mode because their proof comparisons use assertions. Run only
checks relevant to changed dependencies; repeating unchanged certificates
does not supply a missing geometric theorem.

The latest additions are:

```sh
python3 research/eleven/arc_budget/check_wide_shell.py
python3 research/eleven/arc_budget/replay_wide_shell.py
python3 research/eleven/check_core_gap_inventory.py
```

The first shell replay rounds certified elementary bounds down to a fixed
rational grid; the second uses a separately implemented stronger unrounded
bound. The inventory replay uses multisets and explicit dihedral index
permutations, independently of the original enumerators. `MANIFEST.json`
binds all saved proof/data/checker inputs, including pending files, by
SHA-256; those hashes assert identity, not proof closure.

GitHub changes were made through the connector using tree/commit/ref
operations with an expected-head lease. Fetch the live PR branch before
resuming; do not rely on cached SHAs or overwrite a concurrent update.
No credential values are needed in the handoff. The n=8 predecessor audit
and pinned sources are in `N8_METHOD_AND_SOURCES.md`.

All durable resume inputs are in this PR. Scratch directories from the
research session are not required to replay its committed certificates.

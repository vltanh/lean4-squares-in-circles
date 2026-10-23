# n=9 — quadrant/block continuation progress and exact evidence

**Date:** 2026-10-23 UTC. **Read base:** `59d0c95092a01a575a3fc078ab5c6db54107d4fc` on PR #11.
**Global status:** unrestricted T9 and full equality necessity remain OPEN. **P.ALL and Y.ALL were not closed in this continuation.** The new work supplies a general quadrant capacity theorem, cyclic necessary-load rules, a finite coarse cyclic partition and one selected-component exclusion. It must not be described as a finished proof.

This log continues PROGRESS_LEDGER.md and ORIGIN_POCKET_PROGRESS.md without rewriting their historical claims. The current deep roadmap and CYCLIC_CELL_LEDGER.md distinguish proved coverage from unproved sharp physical capacity.

## 1. UTC commit milestones (GitHub-reported)

| UTC, 2026-10-23 | Commit | Deliverable | Exact gate impact |
|---|---|---|---|
| 16:20:02 | [c02fa61](https://github.com/vltanh/lean4-squares-in-circles/commit/c02fa61b49e08dc2feb92f6bebb3a974eaae97aa) | QUADRANT_UNAVOIDABLE_POINT.md | [x] QCAP.1–3: all-angle quadrant unavoidable point/capacity one and every-frame axis-crossing necessary count; P/Y routing still open |
| 16:24:24 | [b3bac6e](https://github.com/vltanh/lean4-squares-in-circles/commit/b3bac6e1ce6012a0e93df0e3d6c7e8731464aebb) | CYCLIC_BLOCK_INVENTORY.md | [x] coarse 58-cell coverage, loaded-endblock rule and loaded-clique exclusion; [x] C1.3.b0 only |
| 16:26:41 | [fed5a88](https://github.com/vltanh/lean4-squares-in-circles/commit/fed5a8882ba4d002c5299cefae1139221da98f12) | check_quadrant_blocks.py | Exact reproducible finite regression source; no universal proof claim |
| 16:27:18.851687–16:27:19.137192, actual execution | source fed5a88; report [338c566](https://github.com/vltanh/lean4-squares-in-circles/commit/338c5660d21ab46a4cc7b897ac7d05b4f4a889a1) | QUADRANT_BLOCK_EXACT_CHECK.json | PASS, Python 3.13.5, exit 0; source bytes matched to committed Git blob before execution |
| Before deep-roadmap update | [b5e868e](https://github.com/vltanh/lean4-squares-in-circles/commit/b5e868e6ffcbb13aba5ea2b6830e8d145d75d275) | CYCLIC_CELL_LEDGER.md | All 58 cells individually recorded, one checked, 57 unchecked; no extra sharp closure |
| 16:43:42 | [9c75dae](https://github.com/vltanh/lean4-squares-in-circles/commit/9c75dae8d5584e7a370065099620686415455f8f) | DEEP_GATED_ROADMAP.md | Deep checked/unchecked G0–G8 contracts reconciled to new proof scope |

No Lean compilation, CI, independent full audit or unrestricted optimality is claimed. The new mathematical arguments are hand proofs pending independent review.

## 2. QCAP: what was proved and what was not

**Theorem proved:** every arbitrarily oriented unit square wholly inside the first quadrant of D_(17/4) contains (1,1). It contains that point in its open interior if tilted; in the aligned boundary case, (1,1)-epsilon*(1,1) is interior for all sufficiently small positive epsilon. Thus two physically disjoint squares cannot fit wholly in that quadrant. No terminal obstacle squares are required.

The analytic proof uses exact own-frame coordinates t,z and proves four inequalities placing (1,1) inside the square. Its nontrivial factorization is

    a^2(1+2b)^2-(1+b)^2 = 2b(1+b)(1-2b^2) >= 0,

for a>=b>=0 and a^2+b^2=1. The aligned boundary perturbation is essential; merely claiming that two closed squares share a point would not contradict disjoint open interiors.

**Unrestricted necessary consequence at q<=17/4:** in every perpendicular frame at least five squares of any hypothetical nine-square packing have open interiors meeting at least one of the two coordinate lines.

**Not proved:** that P or Y extra squares can all be assigned to disjoint quadrant cells. Some may cross the intended boundaries. QCAP is a genuine all-orientation tool but does not close either parent capacity theorem.

## 3. CYCLIC: precise finite scope

The block-cut identity

    n = 1 + b + sum(k_i-1) <= 9

gives exactly 21 cyclic block-size profiles and 58 bridge-count cells. This is a proved complete coarse partition for the **selected connected cyclic positive body component**. Each cell retains all actual graphs, loads, contact normals, continuous square poses and 9-n other physical squares.

**Necessary force rules proved:**
- an unloaded positive appendage attached through only one external body cannot balance;
- each endblock has a loaded nonarticulation body;
- in the explicit window R>=79/40, all loaded bodies cannot pairwise physically touch, since their centroid and normalized circle-force balance would imply R^2<=625/162<(79/40)^2.

**One complete cell closed:** C1.3.b0, an isolated selected triangle component, has a pairwise touching loaded subset and is excluded. The argument does not close triangles with bridge attachments or a larger component containing a clique.

**Sharp frontier remains:** 57 cyclic cells are unchecked. This inventory is not the desired small geometric terminal classification. It exposes a finite coverage obligation but does not make the remaining inequalities routine or supply a completion percentage. A common sharp invariant covering many cells is preferred to a large graph/angle enumeration.

## 4. Exact executed regression provenance

Committed source: `research/nine/check_quadrant_blocks.py`, commit `fed5a8882ba4d002c5299cefae1139221da98f12`.

- Git blob SHA-1: `fdb7d5ef123b8018601c3661b5451c4346672ba5`.
- SHA-256: `d7fe0378cf8d1accea9f971daa97e06056900780469d0593cdfbc0186b4938b7`.
- Pinned run: 2026-10-23 16:27:18.851687–16:27:19.137192 UTC.
- Python 3.13.5; exit status 0.
- Report: [QUADRANT_BLOCK_EXACT_CHECK.json](QUADRANT_BLOCK_EXACT_CHECK.json).

```sh
python check_quadrant_blocks.py \
  --source-commit fed5a8882ba4d002c5299cefae1139221da98f12 \
  --output QUADRANT_BLOCK_EXACT_CHECK.json
```

**Passed finite checks:**
- 104 exact rational identity checks;
- 2,254 admissible rational quadrant-square samples, including 2,082 tilted strict-point examples and 33 aligned boundary examples;
- 1,772 finite connected cyclic graph checks, exercising all 58 cells through all small simple graphs, deterministic larger samples and one abstract witness per cell;
- exact center-relaxation and angular negative controls below.

**Evidence limit:** samples do not establish the all-angle theorem; its symbolic proof does. Graph tests do not prove physical realizability or sharp capacity. These are reproducible regressions, not a universal n=9 certificate, independent mathematical audit or Lean verification.

## 5. A stronger exact false-relaxation witness for P

The four actual aligned path squares have inner sliders

    tau1=-193/1000, tau2=186/1000.

The following FIVE additional candidate centers satisfy all of the common center/inscribed-disk necessary conditions:

    ( 887/1000, 1204/1000),
    (-128/1000, 1353/1000),
    (-1094/1000,1003/1000),
    (-552/1000,-1212/1000),
    ( 555/1000,-1189/1000).

They lie strictly within the center disk of radius 3/2, have pairwise distances strictly greater than one, and their open radius-1/2 disks have strict clearance from every one of the four actual path rectangles. The exact minimum squared slacks checked are:

    9/4-|c|^2:                        2723/200000,
    dist(c,root_rectangle)^2-1/4:    3009/1000000,
    |c_i-c_j|^2-1:                   26213/500000.

**This is NOT a physical unit-square packing.** No orientations realizing the five full squares with correct corner containment/nonoverlap are claimed. It proves that any proof using only these center/inscribed-disk inequalities cannot exclude P+five. A valid full-family P argument must use actual square supports or stronger physical information.

## 6. A proposed 45-degree center-angle rule is false

The two axis-aligned unit squares centered at (5/4,1/2) and (5/4,-1/2) have disjoint open interiors, fit squared radius 65/16<17/4 and have center-direction angle with cosine 21/29. Since 2*21^2>29^2, the angle is strictly below pi/4.

Thus a universal pi/4 angular spacing rule for extra square centers is false, even in this radius range and with noncentral centers. This control must remain separate from the true pi/6 annular separation used in THREE_VERTEX_ORIGIN_CAPACITY.md.

## 7. Current ticked scope and next genuine completion test

- [x] New all-angle quadrant capacity and every-frame axis-intersection necessary count.
- [x] Coarse cyclic block partition, with proof of exhaustiveness.
- [x] Loaded endblock and loaded-clique necessary restrictions.
- [x] C1.3.b0 excluded in the explicit radius window.
- [x] Exact negative controls and source-pinned finite regressions committed.
- [ ] P.ALL entire two-slider physical completion theorem.
- [ ] Y.ALL entire two-parameter fan physical completion theorem.
- [ ] 57 remaining cyclic cells uniformly sharply bounded, or a global invariant bypassing them.
- [ ] Explicit lower-window dependency, unrestricted assembly, all equality packings, independent audit, Lean and integration.

**Completion criterion:** the next claimed closure must be a full P/Y family, a whole cyclic cell or a theorem covering multiple cells, with all physical completion squares retained. Another numerical range check or count of new lemma names does not close those parents. The unrestricted proof was not finished in this continuation.
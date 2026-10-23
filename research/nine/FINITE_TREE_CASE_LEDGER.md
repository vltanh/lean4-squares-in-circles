# n=9 — finite tree-case ledger and timestamped closure record

**Checkpoint:** 2026-10-23. **Global theorem remains OPEN.**
The tree branch now has a **proved finite exhaustive geometric partition**, not an unbounded list of increasingly small offset/angle intervals. Two of its six full nine-square completion cases are closed by new hand arguments. Independent audit and Lean verification remain outstanding.

## 1. Where this finite branch sits in the global proof

At an unrestricted minimizing packing in the explicitly declared radius window 79/40<=R<=sqrt(1105)/16, choose the physical torque-balanced certificate with the prior nonradial choice at off-origin point-only vertex/vertex contacts.

There is a logically exhaustive outer split:

1. The selected positive body-pair graph has a connected **tree component**. Select one such component and apply TREE.F1/F2 below.
2. Every connected positive component has a **cycle**. This separate branch is OPEN; it is not covered by the six tree cases.

Selecting one tree component does not discard the other squares: every case includes **all nine physical squares**, including other components and zero-stress bodies, in its completion condition. The lower-radius window is a declared dependency, not silently established here.

## 2. Completed finite reductions

- [x] **TREE.F1 — every tree body localized.** All unloaded bodies are among the <=4 central circle-clear bodies; every loaded body has radial S/D geometry even at degree two; every unloaded body avoiding zero is one side-normal transmitter leading to one S terminal, with incoming neighbors containing zero.
  Source: [TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md).
- [x] **TREE.F2.I — origin-interior roots excluded.** Ordinary stars are already excluded; subdivided-star roots are handled exhaustively by whether a short radial support contact is on a side or at a vertex.
- [x] **TREE.F2.R — ALL nonexceptional tree radii excluded.** The side/vertex origin-incidence alternatives both force A=sqrt(R^2-1/4)-1=1. Therefore every positive tree in the window has **R^2=17/4**, not merely the two-loaded trees.
- [x] **TREE.F2.C — complete finite case enumeration.** At that radius all unloaded bodies have zero on a side or vertex, all loaded bodies are radial S terminals, and 2s+v<=4, s+v>=2. These integer inequalities give **exactly six** disjoint incidence profiles.
  Source for all F2 items: [TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md).

## 3. The six cases — no missing geometric profile inside the tree branch

Here s counts unloaded component bodies with zero in a side's relative interior, and v those with zero at a vertex. It does not count unstressed physical bodies outside the selected component.

| ID | (s,v) | Full geometric family, including continuous freedom | Nine-square completion gate |
|---|---|---|---|
| TREE.20 | (2,0) | Opposed side-origin squares; the two-loaded four-square path with both inner sliders strictly between -1/2 and 1/2 | [ ] OPEN; only the flat row was previously excluded |
| TREE.11 | (1,1) | One side-origin and one vertex-origin body, arbitrary compatible relative angle/side offset | [ ] OPEN |
| TREE.12 | (1,2) | A side body and two vertex bodies fill the full angle at zero | [x] **CLOSED hand** — forces four cardinal loaded squares; at most eight total physical squares |
| TREE.02 | (0,2) | Two vertex-origin bodies with arbitrary disjoint right-angle cones | [ ] OPEN |
| TREE.03 | (0,3) | Three vertex-origin bodies with all compatible angular gaps and loads | [ ] OPEN |
| TREE.04 | (0,4) | Four right-angle bodies fill the full angle and form a central solid 2x2 block | [x] **CLOSED hand** — at most eight total physical squares |

**Boundary handling:** slider endpoints |tau|=1/2 change the origin incidence from a side interior to a vertex and therefore move into the appropriate vertex row. They are not omitted. Cases allow oblique-only separators of the additional physical squares.

**Two completed capacity proofs:** [TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md).
The cardinal-cage theorem does not assume that free squares share its frame: it first restricts their centers by inscribed-disk distances, then excludes the remaining diagonal pockets using the full square support inequality. The central-block proof also allows arbitrary rotations.

## 4. Exact progress provenance (UTC, GitHub-reported)

| UTC | Commit | Gate and change | What was actually closed |
|---|---|---|---|
| 2026-10-23 12:56:07 | [4f8144d](https://github.com/vltanh/lean4-squares-in-circles/commit/4f8144db1ff9d6b1ac0388aa1cb9413c5120e997) | TREE_BODY_LOCALIZATION.md | **Every** positive-tree body, not one sampled topology |
| 2026-10-23 12:58:52 | [4007bfc](https://github.com/vltanh/lean4-squares-in-circles/commit/4007bfcc108d42977202d0bb4cb329ea58c56593) | TREE_RADIUS_QUANTIZATION.md | All tree radii except 17/4; exhaustive six incidence cases at the remaining radius |
| 2026-10-23 13:05:27 | [5acabe7](https://github.com/vltanh/lean4-squares-in-circles/commit/5acabe75e3e0b729c6a6279555cffdb6e4fdce05) | TREE_FINITE_COMPLETIONS.md | **Entire** TREE.12 and TREE.04 completion families, including oblique free squares |

All three are hand mathematical manuscripts. No optimizer, orientation grid, or enumeration of sample poses is a proof premise. Regression checks and explicit physical counterexamples are recorded separately, and cannot be promoted to general certificates.

## 5. Next exact completion targets

**TREE.20:** exclude five additional physical squares for every two-loaded staggered four-square path at R^2=17/4; the flat row is only one subcase. A center-distance relaxation alone is too weak.

**TREE.11 / TREE.02 / TREE.03:** derive one capacity or support inequality covering each **whole** origin-incidence family, with all positive loaded S terminals and all unstressed-square completions. Do not subdivide arbitrary angular ranges into a new infinite sequence of purported gates.

**CYCLIC:** derive a separate human-sized exhaustive structural cover or a uniform sharp inequality. The radial bridge law does not make nonbridge edges radial. No solved tree count is evidence that the cyclic branch is solved.

**Stop condition for the tree parent:** it closes only after all six completion rows are [x], with the universal tree-radius/case-cover lemmas audited. Four rows remain open at this checkpoint. Unrestricted G4 additionally needs the cyclic branch, the explicit lower-window dependency, and global assembly.

## 6. No false completion metric

It is valid to say **two of six exhaustive tree-completion cases are closed at hand level**. It is NOT valid to infer that one third of the entire unrestricted theorem is proved: the four remaining cases have continuous parameters and the cyclic branch is still open. This ledger records a genuine finite partition and whole-case exclusions, not a completion percentage.
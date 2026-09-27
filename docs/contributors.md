# Contributors

[Back to the README](../README.md)

AI models wrote the mathematics and the Lean code. The repository owner
directed the work, reviewed it, and made the decisions about scope and naming.
Times are rough commit times, in US Central time (UTC−5).

## 22 September 2026

* **Around 12:00 — three squares by enumeration.** ChatGPT 6 Pro wrote a
  certificate proof of the three-square optimum: separating axes, 48 branches
  and 53 rational certificates. Claude Opus 5 High-Max compiled it and
  arranged the repository. It is kept on the `legacy` branch.
* **15:00 to 16:15 — three, four and five squares by occupied arcs.**
  The occupied-arc idea came from Claude Opus 5 Max. ChatGPT 6 Pro used it
  first on five squares, where it succeeded, and was then asked to generalize
  it down to three and four squares; it wrote one framework for all three
  cases ([PR #2](https://github.com/vltanh/lean4-squares-in-circles/pull/2)).
  Claude Opus 5.5 Max compiled it and made it the main proof.
* **16:45 to 19:50 — uniqueness.** ChatGPT 6 Pro wrote the uniqueness proofs
  for three, four and five squares
  ([PR #3](https://github.com/vltanh/lean4-squares-in-circles/pull/3)), and
  Claude Opus 5.5 Max compiled them.
* **Around 21:15 — one and two squares.** Claude Opus 5.5 Max added both
  cases and reorganized the library by `n`.
* **Around 23:30 — simplification.** Claude Opus 5.5 Max reviewed the whole
  library, removed duplicated arguments and shared the common lemmas across
  cases.

## 23 September 2026

* **16:15 to 21:40 — seven squares.** ChatGPT 6 Pro wrote an analytic proof
  of the seven-square optimum, with its family of optimal packings, without
  compiling it
  ([PR #4](https://github.com/vltanh/lean4-squares-in-circles/pull/4)).
  Claude Opus 5.5 Max compiled it and added it to the library.
* **21:50 to 22:25 — uniqueness for seven squares.** ChatGPT 6 Pro wrote the
  classification of the optimal seven-square packings, up to the heights of
  the middle squares, without compiling it
  ([PR #5](https://github.com/vltanh/lean4-squares-in-circles/pull/5)).
  Claude Opus 5.5 Max compiled it and added it to the library.

## 26 September 2026

* **12:00 to 13:10 — seven squares simplified, and one framework.** Claude
  Opus 5.5, at Max or Extra High effort (which one was not recorded) and
  running five agents in parallel, proved the pair analysis of seven
  squares once, for closed containment, simplified its foundation and its
  reconstruction, and shared a regular-polygon lemma across the cases. It then
  put every case into one framework, `Optimum`.
* **Around 16:00 — every case simplified.** Claude Opus 5.5 simplified the
  foundation and the cases of one and two squares, unified the arc proofs of
  three to five squares, simplified seven squares further, and derived every
  lower bound from uniqueness, once for all cases. Over the day the library
  went from 14,570 lines of Lean in 99 files to 9,820 in 61.
* **17:40 to 19:50 — the statement and the textbook.** Claude Opus 5.5 stated
  the optimal packings by congruence to model packings, and rewrote the proof
  pages as an illustrated textbook, with 171 figures computed from the
  geometry of the proofs.
* **From 23:30 — the Palomar registry.** Claude Opus 5.5 moved the library to
  Lean and mathlib v4.35.0-rc3 and prepared it for the
  [Palomar](https://palomar-registry.org/) registry: the statement gathered in
  `Geometry.lean`, `Challenge.lean`, `comparator.json`, `formalization.yaml`
  and the checks that run them.

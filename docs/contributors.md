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

## 26 to 30 September 2026

* **Six squares.** ChatGPT's latest model at the time, in the chat on the
  ChatGPT website, and Claude Opus 5.5 Max, in the Claude chat, proved the
  six-square optimum together, with numerical certificates
  ([PR #6](https://github.com/vltanh/lean4-squares-in-circles/pull/6)).
  Claude wrote its normalization, which puts every packing near the optimum
  into a standard frame. ChatGPT 6 Pro then turned the certificates into an
  analytical proof and wrote the whole proof in Lean, without compiling it
  ([PR #7](https://github.com/vltanh/lean4-squares-in-circles/pull/7)).

## 30 September 2026

* **From 17:55 — six squares compiled.** Claude Opus 5.5, in Claude Code,
  compiled the analytical proof: 968 errors in 197 of its 284 modules, nearly
  all from changes in Lean and mathlib, and two wrong constants in scalar
  bounds, whose corrected values still close the proofs. It then added the
  case to the library.
* **18:25 to 20:40 — seven squares without Bernstein certificates.**
  ChatGPT 6 Pro wrote human-readable proofs for the eight Bernstein
  certificates of seven squares and for five other numerical steps, in
  mathematics and in Lean, without compiling them
  ([PR #8](https://github.com/vltanh/lean4-squares-in-circles/pull/8)).
* **From 20:50 — the certificates replaced.** Claude Opus 5.5, in Claude
  Code, compiled these proofs and put those of the eight certificates into the
  library, together with three of the other steps: the marker envelope, the
  initial boundary ratio and the bounds on side labels. The other two, longer
  than the computations they replace, were left out. It then rewrote the
  affected parts of the textbook.

## 1 October 2026

* **Around 05:10 — six squares rewritten.** Claude Opus 5.5, in Claude Code,
  rewrote the proof of six squares as one analytic argument in the style of
  the other cases: 262 files and about 33,800 lines of Lean became 44 files
  and about 19,600, and the proof no longer uses seven squares.
* **From 07:45 — one style for all seven cases.** Claude Opus 5.5, in Claude
  Code, went over the seven cases for consistency, simplicity and sharing.
  From three squares on, every case has the same files: its construction,
  what a square that avoids the disk centre holds, what becomes of the square
  that contains it, and uniqueness, with the long middle parts of six and
  seven squares in folders. The tools that six and seven squares had each
  built for themselves are now one copy in `Common/`: one-variable calculus and
  trigonometric bounds, squares in a rotated frame, the separating axes of two
  turned squares, congruence and the diagonal reflection, the chart of a
  square in a disk and the supports of a square. Tuned constants went: the
  marker arc of seven squares has half-width 1/2 instead of 801/1600, five
  squares use the exact cosine of π/5, three squares lose 1/12, 1/24 and
  9/20, four squares the bound 5/6, and the octagon that kept the radial sweep
  of five squares disjoint gave way to centres within distance 1 of the disk
  centre.
* **Around 11:00 — the last Bernstein certificates.** Claude Opus 5.5, in
  Claude Code, replaced the two Bernstein certificates that remained in six
  squares, for the transverse bounds of the wing W, by keeping the leading
  terms of each polynomial, and the polynomial of degree 11 behind Lemma H.18
  of seven squares by a square in the target height plus an affine part that
  is positive at both ends of its range, one end by Taylor bounds and the
  other by concavity and one value.
* **Around 12:20 — no long fractions.** Claude Opus 5.5, in Claude Code,
  removed every fraction with four or more digits from the proofs of three
  and five squares, seven squares and their appendices, mostly by better
  arguments: the small turns of the forward axis are bounded at the
  transition state, where the force lies between the normals of the circle and
  of the tie line; the transition profile is tested at the diagonal corner,
  where X/Z = 12/13 exactly; elsewhere the leading terms suffice, or concavity
  and one value. Brackets of irrational constants are written as short
  decimals, in the proofs and in the Lean.
* **Around 14:20 — the constants of six and seven squares.** Claude Opus 5.5,
  in Claude Code, went on to the Lean of six squares, where some 600 lines
  carried long fractions: the brackets of the model constants and the ceiling
  `Q0 = 2.85118` are decimals with as few digits as their uses need, tuned
  weights became simple ones (41/20 and 3/8, 8/15, 1/5, 1/6 and 1/10, 12/5 and
  13/6), and several estimates were reargued, among them the curvature of the
  chord term by its convexity, the vertex case of the diagonal estimate by
  concave pieces, and the west stress along the axis of W with exact lengths.
  In seven squares the last tuned constants went: an axial label gives
  `a + u < 1 + 2π/15` straight from the remainder, and the turn profile is at
  least `z/40`.
* **From 14:35 — the chapter of six squares.** Claude Opus 5.5, in Claude
  Code, wrote six squares into the textbook as Chapter 9, between five and
  seven squares, with Appendices B to E for its estimates (the normalization,
  the separators, the wings, and the tails and the stress of the model) and 69
  figures computed from the geometry of the proof. The book now reads as if six
  squares had come first: seven squares became Chapter 10, with its appendices
  after those of six squares and its separating-axis lemma taken from
  Chapter 9; the one-variable estimates of both cases share Appendix A; and the
  chapter files and the figures are sorted by chapter.

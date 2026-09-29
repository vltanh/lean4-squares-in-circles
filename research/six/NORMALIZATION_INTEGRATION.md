# Supplied normalization proof: completed integration record

## Scope and source versions

The supplied normalization manuscript is incorporated in
[NORMALIZATION_PROOF.md](NORMALIZATION_PROOF.md), with the corrected theorem
assembly and interfaces in [HAND_PROOF.md](HAND_PROOF.md). The manuscript
replaces the historical §2.3; it does not independently reprove the existing
Appendix A or downstream A2 calculations.

The integration base was `4d9754c79c90df8b103e7b218dc316bec58dc43e`.
The twelve Python source files used for the fresh execution recorded here were
read at `c7385e9a6c875af289617d1ee1075f8336810002`. Each local file's Git blob
SHA was checked against the fetched repository blob before execution. The
source files were not changed during this recording stage.

The repository manuscript is an edited integration of the submission, not a
byte-for-byte archival copy of the uploaded manuscript. The uploaded inputs
are identified by SHA-256:

| Input | SHA-256 |
|---|---|
| `NORMALIZATION_PROOF.md` | `1ec9d66d0d1363102124cd7dda3670c70dcf743fc4ad38a692cdf6fb0b967c6f` |
| `normalization_cert.zip` | `28a8310b02a850e842d26986230b06658138f90979449ea1d0b654e38e3e4a8f` |

The old downstream manuscript and roadmap are preserved byte-for-byte in
HAND_PROOF_PRE_NORMALIZATION.md and LEAN_ROADMAP_PRE_NORMALIZATION.md.
Their old normalization sketches and status paragraphs are superseded by the
current source hierarchy. No original downstream calculation was silently
removed when introducing the new normalization source.

## Dependency changes implemented

1. **N23 precedes sectors.** Proposition A / Lemma A proves the stronger central
   box directly from the genuine Seven marker gaps. N16 then follows. No A2
   classification, fixed pin, affine-marker assumption, or sector theorem is
   used to establish the strong box.
2. **Charts precede pin labels.** Lemma B proves N17, axial markers N20, and
   exclusion of the secondary central separators. Lemma C supplies the five
   open pins and the bijective assignment of labels to exterior squares.
3. **Windows precede the final normalization.** D1–D4 establish separator
   alternatives, direction windows, and W/D order. The single diagonal
   normalization puts phi_D at most 5*pi/4. No horizontal reflection is used.
4. **Piercing supplies the remaining geometry.** K4 proves one helper per
   cardinal side and the cardinal moving pins; Lemma G covers the own-primary
   moving pin. K3 supplies N25.
5. **N26 is conditional.** Both members of an opposite pair must admit their
   cardinal separators. The retained uses are P26-1 (E/W cardinal) and P16
   (N/S cardinal). No unconditional opposite-pair assertion is introduced.
6. **N27 has a complete Appendix A interface.** The strong central box,
   W/D ordering, chart bounds, and one-helper-per-side theorem are established
   before applying the retained west-cardinal D exclusion. Appendix A is not
   used circularly to obtain the strong box or the pins.

These interfaces are listed explicitly in HAND_PROOF.md and in the updated
LEAN_ROADMAP.md. The supplied statement remains a hand proof with named scalar
obligations and the stated external Appendix A dependency.

## Fresh local execution

Python: **3.13.5**. Backend: **independent exact-dyadic intervals with 96-bit
units**, implemented in rational_arb_compat.py. This was **not** a
python-flint/Arb run. The runtime did not have the flint module installed.
No GitHub runner or Lean build was used.

Run from `research/six/normalization_cert`:

```sh
python test_replay.py
python replay_rational.py --log RATIONAL_REPLAY_LOG.md
python sharpness.py --backend rational --log SHARPNESS_LOG.md
```

All three processes completed with **exit status 0**.

| Executed check | Result |
|---|---|
| Scalar inequalities S1–S54, including sublabels | 78 / 78 passed |
| Direct certificate groups | 23 / 23 certified |
| Direct boxes evaluated | 176,000 |
| Unresolved boxes in the direct certificate groups | 0 |
| Algebraic-identity numerical sanity checks | 4 / 4 passed |
| Positive/negative sharpness controls | 14 / 14 behaved as expected |
| Arithmetic, coverage, and failure-handling regression tests | 9 / 9 passed |

The A2 cone group contains the 36 central-coordinate boxes of the supplied
staircase cover. Its conditional CE/OWN exclusions retain the strict
hypothesis **cx > c0**. The boundary cx = c0 is not excluded: the regression
suite checks the feasible axis-parallel east-square witness with marker zero.

Execution records:

- [RATIONAL_REPLAY_LOG.md](normalization_cert/RATIONAL_REPLAY_LOG.md): every
  direct group, unresolved count, scalar result, and source SHA-256 hash.
- [SHARPNESS_LOG.md](normalization_cert/SHARPNESS_LOG.md): all 14 controls,
  including observed non-certifications and unresolved counts.
- [UNIT_TEST_LOG.txt](normalization_cert/UNIT_TEST_LOG.txt): actual regression
  test output.
- [REPLAY_MANIFEST.json](normalization_cert/REPLAY_MANIFEST.json): pinned source
  commit, all twelve Git blob and SHA-256 hashes, input/output hashes,
  process exit statuses, and explicit execution-scope flags.

The supplied author's Arb log is not the local execution log. Its times and
box counts must not be substituted for these recorded results. The separate
native command remains `python run_all.py --log ARB_REPLAY_LOG.md`; no native
Arb success is claimed here.

## Implementation changes and interpretation

Relative to the supplied programs, the repository version adds explicit backend
identification, source hashing, inventory counts, nonzero failure exits,
traversal validation, float-endpoint enlargement, and the independent rational
backend. The runner passes the theorem margins as exact rational balls. These
are implementation and reproducibility changes, not new geometric premises.

The displayed sampled minima are diagnostics, not certified lower bounds.
Acceptance uses only interval comparisons. In particular, do not propagate the
submission's blanket numerical remark that all unlisted margins are at least
0.02: the local diagnostic values include S20 near 0.009626 and S49b near
0.010527. Their strict positivity checks pass; the larger blanket margin is
not needed by the hand proof.

Likewise, an expected failure in a sharpness control is not itself a certified
counterexample or a sharp-optimality proof. The four numerical near-zero
identity checks are sanity checks only; I1–I4 are justified algebraically.

## Completion boundary

The normalization manuscript, its dependency interface, and its independent
local arithmetic replay are integrated and recorded. There is no longer a
missing normalization-search task in the roadmap.

This does not constitute a Lean kernel proof of N16–N27 or of the unrestricted
six-square theorem, and it is not a new independent audit of every retained
A1/A2 inequality. N27 retains the supplied Appendix A dependency. Formalization
must prove the scalar statements and geometry in the documented order, then
build and audit the final theorem's dependencies. The PR remains a draft;
no merge or public theorem declaration was changed by this integration.

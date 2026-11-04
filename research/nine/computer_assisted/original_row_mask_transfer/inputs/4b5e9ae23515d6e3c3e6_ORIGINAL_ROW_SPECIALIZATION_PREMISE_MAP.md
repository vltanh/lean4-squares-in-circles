## Appendix A. Literal premise and dependency mapping for Section 2

The source for this appendix is the unchanged accepted
`opposite_tilt_theorem/HAND_PROOF.md`, SHA-256
`db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a`.
Its Section 1 states a seven-square geometric theorem; its final paragraph
announces a separate original-001 consequence proved only in Section 7.
The present specialization uses the geometric theorem through Section 6.

### A.1. Original-label map

| Source theorem label | Unchanged caller label | Premise retained |
|---|---|---|
| A | A | Original physical unit square; canonical signed angle is the left endpoint angle |
| H, row index 1 | B | Original physical unit square; angle independent of the other row frames |
| I, row index 2 | C | Original physical unit square; angle independent of the other row frames |
| D | D | Original physical unit square; canonical signed angle is the right endpoint angle |
| E | E | Original left short-chain square |
| F | F | Original middle short-chain square |
| G | G | Original right short-chain square |

This is substitution into a seven-square theorem, not a permutation of the
existing nine-square certificate or its bit fields. The caller's original
H,I are still present and constrained. None of its labels, angles, selected
bits, or pair facts is rewritten.

### A.2. Every required pair premise

Here `actual` means horizontal gap at least the sum of the two physical
horizontal halfwidths; a main bit of one means the original strict reverse
inequality. Physical disjointness is a separate premise and includes contact.

| Exact caller pair | Original center cone retained? | Actual projection required by this specialization? | Role |
|---|---|---|---|
| AB | Yes | No; either original bit value is permitted | Proves weak row order; physical separation supplies one actual owned separator in source equation (6) |
| BC | Yes | No; either original bit value is permitted | Same row-order and physical-separator role |
| CD | Yes | No; either original bit value is permitted | Same row-order and physical-separator role |
| EF | Yes | **Yes**, the short-chain bit must be zero | Gives \(x_F-x_E\ge h_E+h_F\) in source equation (15) |
| FG | Yes | **Yes**, the short-chain bit must be zero | Gives \(x_G-x_F\ge h_F+h_G\) in source equation (15) |
| AE | Not a selected cone pair | No | Physical left-endpoint weighted cap, source equation (4) with direction −x |
| DG | Not a selected cone pair | No | Physical right-endpoint weighted cap, source equation (4) with direction +x |
| Every other original pair | All original facts retained | No new projection premise | All 36 physical pair constraints remain in the caller |

For the closed-Q contradiction, **at least one** of the three exact original
pairs AB, BC, CD must have its strict weak bit. Its identity comes from the
unchanged main mask and is not chosen by physical-separator ownership. No
particular one of these three bits is needed. For strict radius alone no
main bit assumption is used.

The endpoint-angle premise is the physical canonical sign condition
\(\theta_A\theta_D\le0\). The proof first treats \(\theta_A\ge0\),
\(\theta_D\le0\); common vertical reflection of all centers and frames
treats the other orientation. That reflection preserves the five cone
comparisons, horizontal supports, actual/strict weak bits, corner norms, and
all pair separations. Zero endpoint angles and the canonical endpoint
angles are retained. No same-sign case is inferred from this reflection.

### A.3. Literal source-to-lemma dependency check

| Source location | Mathematical input actually used | Why it remains valid after the substitution |
|---|---|---|
| Section 1, geometric statement (1)–(2) | Seven distinct physical squares; weak four-row order; opposite endpoint signs; variation bound; actual EFG | The table in A.1 preserves distinctness and the two endpoint labels; A.2 supplies the only two required actual projection links |
| Section 2, physical cap (4) | Universal endpoint toll, sharp small-angle toll, and unrestricted physical pair-cap equality classification | These are physical two-square inequalities for AE and DG; neither has an AB or BC actual-link premise |
| Section 2, pair support (5) and owner inequality (6) | Physical separation of each adjacent row pair, positive row gap, and height gap at most 23/100 | The pairs are now exactly AB, BC, CD. Each has both possible original owners and both axes retained; actual horizontal projection is not assumed |
| Sections 3–4, scalar inequality (7) | Four independent canonical angles with opposite endpoint signs, all eight owner patterns, all three choices of maximal owner slope | The scalar table is indexed by row indices 0,1,2,3 and owner indices, with no original bit or center-cone input. Relabeling its two internal indices changes no polynomial or certified box |
| Section 5, row inequality (14) | Sum the three physical owner inequalities and use total variation | The same sum is along the unchanged main row AB, BC, CD |
| Section 5, cap sum (15) | Pair caps on AE/DG and actual EF/FG | Precisely the explicit two actual short links in A.2; strict radius makes the cap sum strict |
| Section 6, equality | Zero maximal owner slope; actual row separation then follows from aligned physical owners; endpoint tolls vanish | This is a conclusion, not an added actual-main premise. It aligns the original A,B,C,D and forces their three original horizontal gaps to equal one |
| Section 7, equation (16) | Actual AB and BC plus the CD cone-inset inequality in a different AHID-row attachment | **Not used.** Its separate argument for recovering the two omitted B,C frames is unnecessary: those frames are already the internal row frames here |

The inherited physical texts are exactly
`UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md`,
`SHARP_SMALL_MAIN_ENDPOINT_TILT_TOLL.md`, and
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
inside the unchanged theorem packet. Its original manifest, all 101 immutable
inputs, scalar replay, and root review are retained by hash in the companion
dependency audit. This audit checks bytes and the literal dependency map;
it does not claim a second polynomial replay.

### A.4. Strict and equality faces

At \(q<Q\), source equation (15) is strict and contradicts the lower bound
\(2a+b\), with \(a=46\), \(b=27/2\). At \(q=Q\), the nonnegative
surplus forces maximal owned slope zero. Physical row projection then gives
each gap at least the adjacent support sum. The cap equality forces all
row halfwidths to 1/2 and the sum of its gaps to three. Thus each gap is
exactly one. A retained strict weak main bit demands that same gap be
strictly less than one, which is impossible.

No height ordering is assumed. Absolute increments and all eight signed
height sums include zero increments and equality at 23/100. If adjacent
main x coordinates coincide, their center cone also gives equal y
coordinates, contradicting the unit center-distance bound; the theorem's
weaker order formulation already safely includes this face. Same-sign
escape domains keep their zero-angle overlap. No closed overlap is discarded
as an independent exclusion merely because another theorem applies there.

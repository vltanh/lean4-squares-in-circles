# Nine complete original cells from shared center capacity

November 3, 2026. This checkpoint closes **nine further unchanged original
cells** of the certified `001/00` cover. It advances that cover from
**174 CLOSED / 57 OPEN** to **183 CLOSED / 48 OPEN**. The original-nine mask
ledger remains **8 CLOSED / 24 OPEN**. The current mask, its reversal,
A.2, the unrestricted lower bound and the global equality classification
remain OPEN. No Lean, Lake or CI was run.

The new proofs combine the same original frame identities, physical
pair inequalities and three-square capacity bounds. Four parents end
directly in exact positive contradictions. Two end in complete covers
of the ninth original's possible center. Three use a fixed `8 x 8`
center cover and one complete rectangular induction for its remainder.
Every accepted proof excludes its entire original parent.

## 1. Exact caller and unchanged coverage

The caller is the strict original-nine predicate `D_001/00^lt` in the
[coverage and closure contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md), at
every `q < Q = 1105/256`. The original squares A through I retain their
independent physical orthonormal frames, all 36 corners, all 36 physical
pair nonoverlap conditions, the marked cone comparisons and their exact
bits. In particular, the original CD weak bit remains strict.

The accepted low-gap theorem and common vertical reflection give
`y_D-y_C > 2/3`. Only the two extra originals are relabelled, so
`x_H <= x_I`. Each original center has norm strictly below `91/60`.
All other conditions of each immutable original path remain premises.
The proofs use necessary inequalities of those same physical originals;
they never replace the originals by freely chosen frames or new squares.

The [fixed register](gates/A2_00100_FIXED_FRONTIER.json) retains the same
231 IDs and full ancestor paths. The portable checkpoint freezes the
preceding 174-CLOSED register so each new ID can be checked to have been
OPEN before this continuation. Its path hash is independently recomputed.
The accepted whole-mask cover is unchanged, including its shared closed
faces, orientation endpoints and physical-contact boundaries.

## 2. Complete new original-cell proofs

The deduction counts below count a proved scalar coordinate, frame or
pair-difference bound once. For a fixed-grid proof, the new count includes
both its whole-parent induction and its one covering-rectangle induction.
Printed rows count all checked rows used in these deductions and in the
terminal positive sums. A terminal domain is a complete region on which
a final contradiction is proved; these are internal proof regions, not
new original cells or masks.

| Family and unchanged original ID | Prior deductions | New exact deductions | Printed rows checked | Complete terminal domains | Final argument |
|---|---:|---:|---:|---:|---|
| A `positive-8f760b2d708ad21d` | 34 | 358 | 373 | 1 | Original C/I center distance below one |
| A `positive-3da90694b58b6ef7` | 33 | 548 | 1,573 | 61 | Complete I-center rectangle cover |
| D `positive-3b5d35fda8ec4119` | 30 | 862 | 1,196 | 11 | Complete I-center rectangle cover |
| B `negative-a3ab8823d7fe0fa6` | 55 | 150 | 209 | 1 | Seven-row rotated-capacity contradiction |
| B `negative-ab8b276e0338d7f0` | 34 | 138 | 190 | 1 | Original H/I center distance below one |
| C `negative-493c2b626cdbf986` | 32 | 316 | 552 | 1 | Exact physical-frame and altitude-capacity contradiction |
| B `negative-f92d74e712afa6be` | 31 | 762 | 1,468 | 63 | 62 fixed tiles and one complete lower rectangle |
| B `negative-b8e4f47ec1258e16` | 38 | 853 | 1,469 | 63 | 62 fixed tiles and one original D-frame contradiction |
| B `negative-1de449e714cf90dd` | 39 | 846 | 1,558 | 59 | 58 fixed tiles and one complete covering rectangle |
| **Total** | **326** | **4,833** | **8,588** | **261** | **Nine whole original parents** |

The first six proofs contain no new split in their bound inductions.
Their two complete center covers have 61 and 11 leaves, with 60 and 10
binary rectangle splits respectively. The last three use three fixed
`8 x 8` covers, accounting for all 192 tiles. Their covering-rectangle
inductions introduce no further split. No partial cover is credited.

## 3. Shared physical inequalities

### A point of one original against another original's incircle

For two physical originals with disjoint open interiors, every point of
one square has distance at least `1/2` from the other's center. The claim
also holds on square boundaries by continuity. Write a point of original
`i` as `c_i + (s u_i + t v_i)/2`, with `s,t` in `[-1,1]`, and let
`d = c_j-c_i = (x,y)`. With the same original frame components
`u_i=(alpha_i,beta_i)` and `v_i=(-beta_i,alpha_i)`, the consequence is

```text
x^2 + y^2 - alpha_i(s x+t y) - beta_i(s y-t x)
    + (s^2+t^2-1)/4 >= 0.
```

On already proved displacement and frame intervals, upper square
secants and lower product planes turn this into exact rational linear
rows. Each plane uses the old proved state of the complete parent.
The [point/incircle hand proof](ORIGINAL_POINT_INCIRCLE_FRAME_COUPLING_HAND_PROOF.md)
derives the implication and the row signs. The independent replay
reconstructs every used row from its original indices and rational
parameters, without importing the discovery generator.

### The original frame equation supplies an inset perspective

For one original put `z=|beta|`, `alpha^2+z^2=1`,
`0<=z<=alpha`, `g=1/(2(alpha+z))`, and `t=z/alpha`. Then

```text
2g/alpha = (1+t^2)/(1+t) = t-1+2/(1+t).
```

This function is convex on `[0,1]`. Its rational tangents and chords
give lower and upper affine bounds on `2g` in the same original `alpha`
and `z`. In particular, `2g<=alpha`. Reciprocal chords for `g` and
lower chords of the physical unit-circle arc give companion exact rows.
The [frame-perspective hand proof](ORIGINAL_FRAME_PERSPECTIVE_AND_DIRECTIONAL_SUPPORT_HAND_PROOF.md)
retains aligned and diagonal equality endpoints.

### Support variation strengthens physical pair distance

For any common unit direction `n`, two physical original unit squares
satisfy

```text
|c_j-c_i| >= 1 + |h_i(n)-h_j(n)|.
```

The same hand proof derives this from their centered-square Hausdorff
distance and a genuine physical separating axis. Lower signed support
forms for one original, upper absolute-value chords for the other and
square secants for the displacement give exact affine consequences.
The [coordinate support-height proof](ORIGINAL_SUPPORT_HEIGHT_PAIR_HAND_PROOF.md)
also records the folded coordinate specialization. Neither implication
requires the two original frames to agree.

### Three actual originals have a sharpened strip capacity

For three original unit squares with longitudinally ordered centers,
transverse width `W<=7/10`, endpoint longitudinal gap `V` and transverse
endpoint difference `Delta`, the
[sharp strip theorem](THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.md)
gives

```text
V + (13/50) Delta^2 >= min(2, 2 sqrt(2)-2W)
                       >= min(2, 280/99-2W).
```

The hand proof supplies the geometric middle-square argument and exact
scalar checks. The older, weaker `5/14` rows remain valid where retained
by an immutable earlier producer. The certificate's physical row name
determines which coefficient is independently reconstructed.

The [altitude-capacity proof](THREE_ORIGINAL_ALTITUDE_CAPACITY_HAND_PROOF.md)
uses the same strip theorem after proving that the middle center projects
between the two endpoint centers. Exact dot-product and determinant
bounds establish every such guard. A proved endpoint-distance lower
bound controls the actual altitude. These guards are derived from the
old complete-parent state before any new inequality is used.

## 4. How a finite center cover excludes a whole original parent

Fix an original, here I, and its entire proved center rectangle. Divide
that rectangle into closed rational rectangles whose union is exact.
For a leaf rectangle `R` and another original's proved center box `B_j`,
compute the largest squared distance between any point of `R` and any
point of `B_j`. If it is strictly below one, the two original open
incircles must overlap for every possible placement in that leaf.
Alternatively, a leaf whose minimum squared distance from the origin is
at least `(91/60)^2` contradicts the strict original-center radius bound.

All leaf comparisons are exact rational comparisons. All midpoint
children include their common face. A complete binary trie checks that
every child is present and that no duplicate, missing or ancestor leaf
has replaced another region. The
[center-cover hand proof](ORIGINAL_CENTER_COVER_CAPACITY_HAND_PROOF.md)
explains the full-parent implication.

For `positive-3da90694b58b6ef7`, 61 rectangles account for the entire
I-center box. F, C, D, G and H witness 24, 6, 10, 10 and 9 overlap leaves;
two remaining leaves lie outside the center disk. The least positive
leaf reserve is `141600887/274877906944`.

For `positive-3b5d35fda8ec4119`, 11 rectangles suffice. H witnesses one,
G six and F three; the final leaf lies outside the center disk. The least
positive leaf reserve is `1808911487579729/63331869759897600`.

Those covers are useful only after their preceding whole-parent bound
inductions have been independently proved. Both inductions and both
complete covers passed fresh replay; a numerical collection of boxes
would not establish either closure.

## 5. Three fixed-grid proofs and one finished B routing

The [three-B hand assembly](A2_00100_THREE_B_FIXED_CENTER_COVER_CLOSURE.md)
gives the full exact caller, rectangle endpoints and final contradictions.
Each original I-center box is divided into all 64 products of its closed
equal eighths. One exact static proof is attempted per tile. The proof
then handles the entire remaining rectangle at once, retaining the same
frozen grid.

| Original | Static tiles proved | Tiles covered by one rectangle | Whole-parent new deductions | Rectangle deductions | Rectangle terminal |
|---|---:|---|---:|---:|---|
| `negative-f92d74e712afa6be` | 62 | `0,8` | 224 | 538 | Nineteen-row positive contradiction |
| `negative-b8e4f47ec1258e16` | 62 | `0,8` | 521 | 332 | Empty original D-frame intersection |
| `negative-1de449e714cf90dd` | 58 | `0,1,2,8,9,10` | 527 | 319 | Thirty-row positive contradiction |

The last covering rectangle includes three previously proved tiles as
well as all three unresolved ones. This harmless overlap is checked
explicitly; every original tile is accounted for. The two rectangle
bound rounds in the b8e proof contain 124 and 208 deductions. Its final
frame contradiction occurs before the producer replaces its preceding
saved state; the independent checker reconstructs the contradictory
intersection itself and never promotes that saved preceding state.

The f92 and 1de original paths differ only in the existing alternatives
`y_F<=1/2` and `y_F>=1/2`. Both have negative D tilt, nonpositive A tilt,
F/H routing child 6 and F/I routing child 5. Their two complete proofs
therefore close this entire existing routing across all F heights,
including `y_F=1/2`. This is an actual shared routing closure within the
fixed cover; it does not by itself close a mask.

## 6. Short exact terminal checks

Several terminal tables have concise geometric readings.

For `positive-8f760b2d708ad21d`, the full-parent induction gives
`|x_I-x_C|<11/100` and `|y_I-y_C|<97/100`. Consequently their squared
center distance is below `953/1000<1`, contradicting their open
incircles. Its stored three-row positive terminal supplies the same
strict contradiction directly.

For `negative-ab8b276e0338d7f0`, the proved H/I difference bounds give

```text
|x_I-x_H| <= 1/1048576,
|y_I-y_H| <= 977503/1048576.
```

Their squared-distance upper bound is
`477756057505/549755813888 < 1`, with positive reserve
`71999756383/549755813888`. The two stored terminal rows also cancel
with equal positive weights. The unchanged ordered path additionally
forces the exact common abscissa `x_H=x_I=0`.

For the b8e covering rectangle, its same original D satisfies
`alpha_D<=500885/524288` and `g_D>=423149/1048576>2/5`.
The original unit-frame identity forces `|t_D|>17/55`, since

```text
3025 * 524288^2 - 3314 * 500885^2 = 70182897950 > 0.
```

Monotonicity of the same original inset on the folded slope interval
then gives
`g_D^2<=1657/10368<4/25`, contradicting `g_D>2/5`.
The final difference `4/25-1657/10368` is exactly `47/259200`.
All bounds used here are consequences of that complete covering
rectangle; none is assumed for a smaller unrecorded region.

## 7. Independent acceptance and remaining scope

The portable
[manifest](computer_assisted/a2_00100_original_center_capacity_manifest.json)
binds the frozen original register, original geometry, discovery sources,
certificate bytes, exact rational tables, independent checkers and
reports. After extracting the archive into a fresh directory, run:

```sh
python original_center_capacity_checkpoint/verify_all.py
```

The archive SHA-256 is
`98deacea890cad968e8a2b83bc6efb2454dc14057717d072a4753674916aba6b`.
Verification uses Python's standard library. Discovery uses
numerical optimization only to propose rational combinations; acceptance
reconstructs the used physical rows and recomputes every nonnegative
weighted sum with exact rational arithmetic.

For each bound round the verifier uses one already proved old state.
All proposed deductions are checked there and installed simultaneously.
It independently checks the subsequent physical frame inversion and
state intersection. A later tightened bound cannot justify an earlier
row. Final rows are reconstructed from the proved state, with all
residual coefficients paid using valid absolute variable bounds.

Fresh root replay checked the six direct/center-cover parents and all
three fixed-grid parents. The portable replay repeats these checks after
relocating the source bindings. The
[root integration review](computer_assisted/a2_00100_original_center_capacity_root_review.json)
records nine fresh extracted parent replays, all 315 immutable file
checks, the unchanged 231 paths and the exact nine status changes.
Damaged-control checks reject missing
tiles or center leaves, shifted shared faces, negative multipliers,
altered physical rows, invalid induction bounds and missing union faces.
These are arithmetic, source-identity and complete-coverage checks;
no human or proof-kernel verification is claimed.

| Same early branch family | OPEN before this checkpoint | Newly CLOSED | Still OPEN |
|---|---:|---:|---:|
| A: positive D, nonpositive A, inward-row escapes | 14 | 2 | 12 |
| B: negative D, nonpositive A, F-height branches | 27 | 5 | 22 |
| C: negative D, nonnegative A, alternate-chain escapes | 10 | 1 | 9 |
| D: positive D, nonnegative A, alternate-chain escapes | 6 | 1 | 5 |
| **Total** | **57** | **9** | **48** |

The same 7,915 positional roots and all 15 roadmap IDs remain unchanged.
There are no new positional-root exclusions or roadmap closures. The
closed masks remain `000/00`, `000/01`, `000/10`, `000/11`, `010/00`,
`010/01`, `010/10` and `010/11`. Apply whole-witness reversal to `100/00`
only after all remaining original cells of `001/00` have complete proofs.

Ongoing bounded trials on the other original IDs are separate research.
Their partial grids, numerical points and unfinished rectangle inductions
leave their original parents OPEN. This checkpoint makes no claim to
finish the current mask or the other 23 open masks.

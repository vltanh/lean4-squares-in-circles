# A.2: fixed coverage and whole-domain closure contract

November 1, 2026, America/Chicago. Replaces the expanding research queue, not the mathematical sources. Baseline: `ea4ff8bad97a58e2b8633ab69f549acb5352e573`.

**A.2 is OPEN. The November 2 continuation closes the full `000/01`,
`000/10`, `010/01`, and `010/10` domains even at Q, and now closes
`000/11` and `010/11` for strict radius. There are 24 fixed masks still open.** The existing exhaustive covers are retained. The missing result is closure of their continuous domains, not another list of conditional subcases.

## 1. Two different ledgers must not be conflated

The original positional cover has 7,915 stable root IDs. The published `computer_assisted/coupled_separator_verification_summary.json` reports 5,838 **closed-Q exclusions** and 2,077 OPEN roots. This historical result is preserved, not rerun here. Its generated manifest SHA-256 is `bc2f1dcc4e16b413beb960616793bdb84c20ae51c7fa29617245eb2cb0db9990`. No missing per-root records are reconstructed from counts.

A closed-Q exclusion asserts that an entire root is impossible even at q=Q. A sharp lower-bound proof asserts only that its q<Q part is impossible. These are different claims. Root 7820 contains an attaining packing, so it cannot be closed by a closed-Q exclusion. It can eventually have its strict-radius obligation discharged while its equality domain remains nonempty. **Do not demand that the historical closed-Q OPEN count reach zero.**

The hand-proof work queue uses the 32 already introduced marked-chain masks. They are exact domains of nine physical squares with a chosen chain witness, not 32 finite sets of poses. The accepted complete source proofs treat `000/00`, `000/01`, `000/10`,
`000/11`, `010/00`, `010/01`, `010/10`, and `010/11`; the other 24 remain OPEN. This is not a percentage of effort, nor a replacement for the 7,915 root IDs or the 15 roadmap IDs.

## 2. The unchanged unrestricted physical predicate

Put Q=1105/256. A labeled physical configuration P consists of nine centers c_i in R^2 and nine independent orthonormal side frames (u_i,v_i), for 0<=i<=8. Let

    S_i = c_i + { (a u_i + b v_i)/2 : -1 <= a,b <= 1 }.

Write Physical_le(P) when:

- every frame is orthonormal;
- each of the 36 corners c_i+(epsilon u_i+tau v_i)/2 has squared norm at most Q;
- the open interiors of S_i and S_j are disjoint for all 36 pairs i<j.

Physical_lt(P) uses strict corner bounds instead. Convexity of the disk makes the four-corner condition equivalent to whole-square containment. A packing fits some squared radius q<Q exactly when Physical_lt(P) holds. Weak physical contacts remain allowed in both predicates.

No row layout, common square orientation, separator owner, marker occupancy, stress graph, small-tilt assumption, or positive clearance is part of this predicate. In particular both squares not selected for a chain remain physical squares, with all their corner and pair constraints.

For the positional route, a root R_r adds exactly its nine closed hex-cell memberships to this same predicate. The canonical cell set and its stable ID are those of `computer_assisted/HEXAGON_ROOT_COVER_AND_FIRST_EXCLUSIONS.md`. A source formula or a count is not a new root-exclusion certificate.

## 3. Exact witness and mask domains

A witness W consists of an orthonormal coordinate frame (e,f) and a permutation pi of all nine labels. Coordinates below are projections of the original centers onto this frame; they do not move a center out of a fixed positional root. Set

    x_i = e dot c_{pi(i)},     y_i = f dot c_{pi(i)},
    h_i = (|e dot u_{pi(i)}| + |e dot v_{pi(i)}|)/2,
    g_i = 1/(4h_i).

Then 1/2<=h_i<=1/sqrt(2), the y-halfwidth is also h_i, and the centered aligned square of halfwidth g_i is contained in S_{pi(i)}.

Require a center-cone four-chain on labels 0,1,2,3 and a disjoint center-cone three-chain on labels 4,5,6. Explicitly, for each of the five edges

    E = ((0,1),(1,2),(2,3),(4,5),(5,6)),

require

    x_j-x_i >= |y_j-y_i|.

Distinct physical squares have distinct centers, so each designated x-gap is positive. The inset argument gives x_j-x_i>=g_i+g_j. Labels 7 and 8 have no extra chain restriction and retain all their physical constraints.

For each edge define its bit by the exhaustive, disjoint alternatives

    0: x_j-x_i >= h_i+h_j;       actual projection separation;
    1: x_j-x_i <  h_i+h_j;       weak cone comparison.

Projection equality is assigned to bit 0. Center-cone equality is retained. For a mask m=abc/de, define D_m^lt(P,W) to mean Physical_lt(P), the five cone comparisons, and exactly these five bit predicates. Define D_m^le analogously with Physical_le.

This freezes the meaning of every mask. A later condition such as a floor bound, a separator owner, an orientation interval, or a marker placement may be proved from D_m or used in an exhaustive internal proof split. It may not silently be added to D_m's hypotheses.

The 32 predicates are disjoint for a fixed witness. Their projections onto physical packings can overlap because a packing can admit many witnesses. No disjoint partition of physical packings is claimed or needed.

## 4. Coverage and assembly, with all quantifiers visible

**Existing extraction input.** Sections 1-3 of `CENTER_CONE_ROTATION_AND_ADJACENT_FIRST_BIRTH_HAND_PROOF.md` prove that every Physical_le configuration has such a center-cone 4+3 witness. Its source dependencies are the height-four bound and the cited finite-poset extraction. This contract uses that source theorem; it does not claim a new independent audit of its entire dependency chain.

**Coverage proposition.** Subject to that extraction theorem,

    Physical_lt(P)  iff  there exist W and m in {0,1}^3 x {0,1}^2
                         such that D_m^lt(P,W).

For the forward implication, choose the extracted witness and assign each edge its unique bit using the comparison with h_i+h_j. There are precisely three plus two binary choices. For the reverse implication, Physical_lt is an explicit conjunct of D_m^lt. The same statement holds with le in place of lt. This proves coverage without numerical sampling, a new pose enumeration, or an assumption about which masks are physically realizable.

**Assembly proposition.** If, for every one of the fixed masks m, there is a complete proof of

    for every P,W, not D_m^lt(P,W),

then there is no strict counterexample and the unrestricted lower bound follows. Conversely, an unrestricted no-strict-counterexample theorem discharges all these predicates because each contains Physical_lt.

A universal terminal-extraction proof may bypass individual rows: it is enough to prove that every hypothetical strict counterexample admits a witness satisfying a proved sharp terminal. Such a global proof must actually establish that existential claim, including the terminal's hypotheses. The ledger must not force unnecessary case-by-case work after a valid global theorem exists.

The diagonal event-frame reduction is optional evidence for a caller, not an additional mandatory gate tree. Its at-most-36 angles depend on the unknown centers. The first-birth grid premises may not be applied to an arbitrary event frame or to persistent height four without a separate implication.

## 5. The entire fixed table

Here C means closed for q<Q by an existing sharp hand theorem; X means excluded even at q=Q; O means OPEN over the full predicate of Section 3.

| Four-chain bits | Three-chain 00 | Three-chain 01 | Three-chain 10 | Three-chain 11 |
|---|---|---|---|---|
| 000 | C | X | X | C |
| 001 | O | O | O | O |
| 010 | X | X | X | C |
| 011 | O | O | O | O |
| 100 | O | O | O | O |
| 101 | O | O | O | O |
| 110 | O | O | O | O |
| 111 | O | O | O | O |

The machine-readable rows are in `gates/A2_MASK_FRONTIER.json`. There are no hidden mandatory owner, angle, occupancy, or slope rows beneath this table.

The 000/00 C source is `PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`, Theorem 2. Actual 4+3 chains are explicit in D_000/00. The remaining two physical squares need no additional hypothesis.

The 010/00 X source is `COMPLETED_MIDDLE_LINK_SHARP_TERMINAL_HAND_PROOF.md`, Sections 1-3. For its two internal main squares B,C, write eta_S=h_S+g_S-1>=0. The actual outer links and weak middle cone link give

    x_D-x_A-h_A-h_D >= 2+eta_B+eta_C > 2.

The strict inequality follows because a weak pair cannot have both frames aligned. The actual three-chain has adjusted endpoint span at least 1. The two physical weighted endpoint caps give an upper bound 211/2 on 46 times the first span plus (27/2) times the second, whereas these lower bounds exceed 211/2. This is a complete whole-mask exclusion. It requires no bound on exceptional pairs elsewhere.

The `000/00` and `010/00` results are inherited. The November 2 complete
proof of `000/01` and its reversal `000/10` is
`A2_000_01_WHOLE_DOMAIN_HAND_TABLE_PROOF.md`, with fresh exact replay and
independent review recorded in `A2_000_01_VERIFIED_CLOSURE_2026_11_02.md`.
It excludes both full domains at closed Q. The subsequent complete
`010/01` and `010/10` proof is `A2_010_01_WHOLE_DOMAIN_ASSEMBLY.md`,
with six new independently replayed covers and the complete physical
audit recorded in `A2_010_01_VERIFIED_CLOSURE_2026_11_02.md`. Those two
domains are also excluded at closed Q. The complete strict-radius
`000/11` proof is `A2_000_11_WHOLE_DOMAIN_ASSEMBLY.md`, with exact
replays and independent physical/assembly reviews recorded in
`A2_000_11_VERIFIED_CLOSURE_2026_11_02.md`. Its final contradiction uses
the normalized D>2; its closed-Q status is unclassified. Conditional
endpoint and capacity theorems do not change another O without a complete
caller. The complete strict-radius `010/11` proof is
`A2_010_11_WHOLE_DOMAIN_ASSEMBLY.md`, with its complete exact replays and
physical assembly review recorded in
`A2_010_11_VERIFIED_CLOSURE_2026_11_02.md`. Its closed-Q status also remains
unclassified. This reconciles the contract with that already accepted
closure; the newer weak-outer subdomain result changes no table entry.

## 6. Exact proof sharing by reversal

The map

    (e,f) -> (-e,-f),
    (0,1,2,3;4,5,6;7,8) -> (3,2,1,0;6,5,4;7,8)

preserves the physical configuration and converts a witness of mask abc/de into one of mask cba/ed. All relevant halfwidths and inequalities are unchanged. This is an involution and preserves every original pair and corner condition. Thus complete closure of either full domain proves closure of its reversed partner.

In particular `000/01` and `000/10` have equivalent closure obligations,
as do `010/01` and `010/10`. The complete November 2 proofs close both
pairs by this exact reversal. The
published denominator remains 32. Reversing only one chosen chain without the corresponding coordinate change is not this argument.

## 7. The single next proof target

**Active target: the whole `001/00` strict-radius domain, with exact
reversal `100/00`.** Its long chain has two actual links followed by one
strictly weak outer cone link, and its disjoint short chain is actual.
The two other original squares remain unrestricted.

The complete signed hand/table assembly in
`WEAK_OUTER_LOW_GAP_HAND_TABLE_ASSEMBLY.md` proves that the weak pair's
absolute transverse gap exceeds 2/3 even at closed Q. That complete
subdomain exclusion leaves the larger-gap original-nine complement
open and closes no whole mask. The original mask definition in Section 3
is unchanged. Parallel searches may address another fixed full mask or
a universal terminal extraction without adding mandatory gates. No bound
on another exceptional pair, endpoint owner, inner height, tilt or outsider
placement may be assumed without proof.

The November 3 [fixed-cover checkpoint](A2_00100_FIXED_FRONTIER_HAND_TABLE_CHECKPOINT.md)
establishes the exhaustive cover of this full predicate. Its baseline has
11,278 proved leaves and 231 fixed unresolved original cells. The original
53 substitutions and [99 further complete cell proofs](A2_00100_PHYSICAL_PAIR_CLOSURE_CHECKPOINT.md)
plus [seven bound-plus-pair proofs](A2_00100_BOUND_PAIR_CONTINUATION.md)
and [nine distance/frame proofs](A2_00100_ORDERED_DISTANCE_AND_FRAME_CONTINUATION.md),
followed by [three shared-capacity proofs](A2_00100_SHARED_CAPACITY_WHOLE_CELL_CLOSURE.md)
and [three rotated-capacity/frame proofs](A2_00100_ROTATED_CAPACITY_AND_FRAME_CLOSURE.md),
then [nine original-center capacity proofs](A2_00100_ORIGINAL_CENTER_CAPACITY_CLOSURE.md),
[two further complete center covers](A2_00100_TWO_MORE_FIXED_CENTER_COVER_CLOSURES.md),
[six shared-center remainder proofs](A2_00100_SHARED_CENTER_REMAINDER_CLOSURE.md),
the [complete inward-child-5 proof](A2_00100_A_INWARD_CHILD5_WHOLE_PARENT_CLOSURE.md),
the [complete C60b H-center proof](A2_00100_C60B_FIXED_H_COVER_CLOSURE.md),
[four shared whole-original proofs](A2_00100_FOUR_ORIGINAL_SHARED_CLOSURE.md),
the [complete D a497 rational-square cover](A2_00100_D_A497_FIXED_CENTER_PSD_CLOSURE.md),
[two complete B quadratic covers](A2_00100_TWO_B_FIXED_CENTER_PSD_CLOSURES.md),
the [complete B5d7 cover](A2_00100_B5D7_FIXED_CENTER_PSD_CLOSURE.md),
the [complete B265 bound/quadratic cover](A2_00100_B265_FIXED_CENTER_BOUND_PSD_CLOSURE.md),
the [complete A2d5 and B79 covers](A2_00100_A2D5_B79_FIXED_CENTER_CLOSURES.md),
the [complete B054 cover](A2_00100_B054_FIXED_CENTER_BOUND_CLOSURE.md),
the [complete B347 cover](A2_00100_B347_FIXED_CENTER_BOUND_CLOSURE.md),
the [complete C573 cover](A2_00100_C573_FIXED_CENTER_BOUND_CLOSURE.md),
the [complete B61 cover](A2_00100_B61_FIXED_CENTER_BOUND_PSD_CLOSURE.md),
the [complete C618 cover](A2_00100_C618_PROVED_STATE_H_COVER_CLOSURE.md),
the [complete B4ce cover](A2_00100_B4CE_FIXED_CENTER_BOUND_PSD_CLOSURE.md),
the [complete C2f9 cover](A2_00100_C2F9_FIXED_CENTER_BOUND_CLOSURE.md),
the [complete C953 cover](A2_00100_C953_COMPLETE_FIXED_CENTER_OWNED_SLOPE_CLOSURE.md),
the [complete Bd090 cover](A2_00100_BD090_FIXED_CENTER_BOUND_PSD_CLOSURE.md),
the [complete B1a0 cover](A2_00100_B1A0_FIXED_CENTER_BOUND_CLOSURE.md),
and the [complete A8b cover](A2_00100_A8B_FIXED_CENTER_AND_SLOPE_COVER_CLOSURE.md),
now exclude 215 of those cells and leave 16 OPEN. The
[stable register](gates/A2_00100_FIXED_FRONTIER.json) retains every original
path and its physical caller. Shared closed faces are allowed. This
coverage-qualified count is separate from all 32 mask statuses.

Under the operative frontier-first directive, a cell checkpoint must name
each complete original cell it discharges and supply its full hand/table
proof, exact replay when used, and the complete parent-to-terminal cover.
An unfinished internal subtree leaves that same original cell OPEN.
A whole-mask or roadmap closure still requires the entire fixed domain,
an entire stable original root, or a valid global terminal extraction.
No incomplete target becomes a list of new mandatory gates.

## 8. A closing proof must assemble, not merely split

A finite internal table is legitimate if the parent implies the union of its child domains, including all equality faces, and every child is proved impossible or is routed to an already proved sharp terminal with all its hypotheses derived. Overlap is harmless. Missing complement cases are not.

For a proof that reuses other proof nodes, give an explicit finite acyclic dependency graph or a finite node numbering that strictly decreases along every dependency. Induction then justifies assembly. A conditional statement D_m and H implies contradiction leaves D_m and not H untouched and earns no whole-row closure.

The accepted mathematical proof must cover every q<Q, arbitrarily close to Q. An exclusion only for q<=Q-epsilon, with fixed epsilon>0, does not close a row. A numerical failure to find a packing does not close a row. A smaller subsystem may be used only when its exclusion is actually proved; missing ninth-square constraints may not be assumed.

A change of physical coordinates, expansion of centers, or relabeling used in a root-specific proof must have a valid root-transfer argument. The global strict-counterexample normalization need not preserve a particular hex root. Merely evaluating projections in a different witness frame, as in Section 3, does not move the original configuration.

## 9. Progress invariant and its limitation

Let U be the subset of the fixed 32 masks with no accepted complete strict-radius proof. At the reset |U|=30; after the six complete November 2 closures |U|=24. The subsequent weak-outer gap improvement leaves |U|=24. A mathematical closure update removes one or more specified elements of U; a new conditional lemma, a narrower angle range, a child split, a source recovery, or a documentation change removes none. Incorrect proofs must be retracted even if that increases |U|.

This is a monotone accounting rule for valid accepted closures, **not a theorem that proof discovery terminates**. A finite list can contain very hard continuous statements. Compactness, an integer counter, and a finite mask set do not establish tractability or a uniform finite subdivision bound. No claim of uniformly easy leaves or a completion percentage is made.

A full-root strict proof may also be accepted with its stable root ID and complete domain proof; it is recorded separately from closed-Q exclusions. The finite root-cover route remains available, and the user has authorized computer-assisted discovery and independent
exact replay, followed by a complete hand/table proof. No Lean, Lake,
or CI is authorized.

## 10. Repository policy after this reset

`PROGRESS.md`, `DEEP_GATED_ROADMAP.md`, and `gates/ACTIVE_ROADMAP.json` now describe this one closure queue. The 15 roadmap IDs and 7,915 positional root IDs are unchanged. The old growing checkpoint descriptions remain in Git history and their source manuscripts remain in the repository; they are a library, not simultaneous active proof branches.

No fresh conditional-lemma campaign is an accepted next deliverable. Necessary lemmas may be developed inside the selected whole-domain proof, and a broad lemma may close several fixed rows at once. Administrative corrections and explicit obstruction reports remain possible but must report zero mathematical closures.

This reset also corrects the stale registry, which still described 31 untreated masks and several now-published sources as unarchived leads. Its historical metadata is preserved by the pinned pre-reset commit rather than copied into another expanding active ledger.

No mathematical program, Lean, Lake, or CI was run for this reset. The new coverage/assembly and reversal arguments are hand deductions from the explicitly cited inputs. No new independent human, agent, or kernel review is claimed. Unrestricted equality and the final manuscript remain separate open deliverables.

## November 3: complete geometry and strict-boundary inputs

The [accepted geometry checkpoint](WEAK_OUTER_GEOMETRY_AND_STRICT_BOUNDARY_CHECKPOINT.md)
adds the complete strict C-slant theorem, its exclusion of any other original
in `x>=0,y<=y_C`, the all-tilts upward-normal reduction, actual vertical
C/G separation, and the global-angle near-horizontal replacement-row exclusion.
The latter resolves its closed-Q equality face using the original strict
weak bit; no positive reserve is invented for a feasible closed relaxation.

The C-slant certificate covers all eight roots with **96,045 exact leaves,
189,342 nodes, and zero frontier**. Two complete exact replays passed, and
six damaged controls were rejected. Its source-bound inventory is
`computer_assisted/weak_outer_hand_C_slant_manifest.json`.
The replacement-row theorem has a complete independent mathematical review
and exact scalar checks. A conditional deep-B left-lower exclusion is also
accepted, without asserting that B must be deep.

The exact `v=1` aligned control demonstrates that a positive-reserve-only
cover of the closed weak-bit relaxation cannot finish the strict problem.
The new analytic row terminal excludes a neighborhood of that control.
The remaining original-nine placement alternatives are still unproved.
**No whole-mask, positional-root, or roadmap-gate count changes.**



# Execution recovery checkpoint — 4 November 2026

## Status and scope

The execution environment became unavailable during the active computer-assisted proof work. At 13:28:54 UTC, even a read-only working-directory request returned:

> No usable execution environment is available. Wait for an environment to become available before using this tool.

GitHub remained available. The PR head was independently read as `37d008a6103e3045b9d1aeeb3f12a3289b7cd714`, with tree `02b32907dc9fe5c60148edd5729cf6fef033b795`. This additive recovery checkpoint preserves the last observed work state and restart instructions. It introduces **no proof acceptance and no ledger change**.

Local report paths and hashes below are observations recorded before the outage, including the component owners' final handoffs. Their bytes could not be rehashed while this note was written. The [machine-readable recovery index](computer_assisted/execution_recovery_2026_11_04_1328.json) is an index of those observations, not a replacement for any certificate, source review or exact replay. Local work not already committed remains dependent on recovering the workspace.

## Published proof state

| Fixed accounting | Closed | Open |
|---|---:|---:|
| Same 231 current-mask original cells | 219 | 12 |
| Same 32 original-nine masks | 8 | 24 |
| Same 7,915 positional roots | 5,838 historical closed-Q exclusions | 2,077 |

The remaining original families are A1, B6, C3 and D2. The 15 roadmap IDs remain unchanged. `001/00`, its reversal `100/00`, A.2, the unrestricted lower bound and global equality remain OPEN.

The two latest published proof commits are:

- `9d735dd0eefac0b51e8826de5a52dbf1ab461d7b`: [complete Dc71 original-cell exclusion](A2_00100_DC71_COMPLETE_ORIGINAL_CLOSURE.md). All sixteen I rectangles and 254 terminal domains are covered. This is the one new original-cell closure that raised the register from 218 to 219.
- `37d008a6103e3045b9d1aeeb3f12a3289b7cd714`: [complete D6c5 I23 checkpoint](A2_00100_D6C5_I23_COMPLETE_H_COVER_CHECKPOINT.md), including the corrected complete energy appendices. D6c5 has fifteen of sixteen I rectangles excluded; I22 remains OPEN. This checkpoint adds no original or mask credit.

Both published ledger files were fetched at the exact parent commit and agree with these counts. This recovery commit leaves them untouched.

## Last completed exact components awaiting further assembly

The following rows concern restricted components. They overlap through ancestry and must not be added as independent original-cell counts.

| Work | Last confirmed exact result | Remaining obligation |
|---|---|---|
| D6c5 I22, all 64 D-quarter BOUND3 records | 24 terminal components, 40 OPEN3; 948 frozen inputs; report `d2cdfd63…` | Continue the surviving states and attach every complete sibling union |
| D6c5 I22 H01, eight D-quarter BOUND6 records | 4 terminals, 4 OPEN6; 835 inputs; report `b0db8098…` | These are descendants of the preceding 64-member batch |
| D6c5 I22 H01, four surviving BOUND9 records | 1 terminal, 3 OPEN9; 847 inputs; report `e20464cd…` | The three normal OPEN9 records entered the reviewed 9→12 queue |
| D821, twenty H BOUND6 records | 5 terminals, 15 OPEN6; 464 inputs; report `878c7c4a…` | Priority I-quarter descendants still require exact replay and assembly |
| C744, 178 completed D-quarter BOUND3 records | 108 terminals, 70 OPEN3; 1,075 inputs; report `2704f128…` | One positive-D guard attachment and 69 continuations remain |
| C744, two separately failed initial-frame numerical domains | Both exact elementary frame exclusions pass; 732 inputs; report `893ed220…` | Complete-sibling attachment source review remains pending; failure logs are retained |
| B16a, thirteen D components | 5 terminal components, 8 OPEN9; 586 inputs; report `4c4e5aa2…` | Remaining original-frame covers |
| B16a, first two F4 declarations | 4 terminals, 4 OPEN3; 627 inputs; report `9ee67c71…` | Neither entire F4 parent is closed |
| Cd402, recovered whole-original eight-round state | All 477 deductions and 1,577 printed rows replayed; 208 inputs; report `8aedce8a…` | The whole original is still OPEN |
| Cb882, combined compact H census | 32 terminal H members and 32 OPEN H members; census `05b8886f…` | No new complete I parent |

The latest selected exact D6c5 states therefore account for the same 64 D leaves as 29 terminals and 35 OPEN states: 32 other OPEN3 leaves and three H01 OPEN9 leaves. This substitutes descendants on unchanged domains and does not add geometric leaves or close I22. C744's separately retained seventieth OPEN3 member is I20 / Hx0 / Hy0 / I-quarter1 / D-quarter0; its positive-D guard attachment remains pending.

Full paths, SHA256 bindings and the relevant accounting are in the recovery index. Every whole-original and whole-mask conclusion still requires the accepted complete physical hand/table assembly.

### B580 I11 saved-evidence recovery

B's saved-evidence assessment composes all eight H rectangles of I11: two affine terminals, five ordinary bound terminals and the twelve-leaf HI1103 F/I-angle cover. It checked 366 source inputs. The composition has 22 distinct bound records, 41 local rounds, 5,646 deductions and 10,657 printed rows, including 319 terminal rows. Its energy census contains 83 triple-energy occurrences and one four-center occurrence.

The assessment hash is `41397a9d4d1b8c2c59c74a9f0de96b43390bc084815bf354a2d2114035178930`. The hand and table are saved locally, but root review and a portable publication packet are still pending. This recovery record does not promote that assessment into a published accepted checkpoint and adds no original or mask credit.

## Jobs whose current state is unknown

Session IDs are historical handles, not evidence that a process is still running. Check the actual process, logs and final records before resuming or restarting.

| Owner / session | Finite job | Last confirmed observation |
|---|---|---|
| Root / `48543` | D6c5 other 32 D3→6 members, two workers | 19 members observed: 13 candidate terminals and 6 normal OPEN6 states |
| Root / `90383` | D6c5 H01 three D9→12 members, one worker | Launched with reviewed exact and numerical continuation sources; later completion unknown |
| A / `45772` | C744 69 D3→6 members, two workers | 16 observed records: 8 candidate terminals, 7 normal OPEN6 and 1 early HiGHS `kNotset` stop |
| B / `36117` | B16a F40 BOUND3 screen, one worker | 33 of 40 members observed; the prepared F3→6 worker was not launched |
| Global / `49725` | D821 two complete I4 declarations: immutable-context preparation | Completion unconfirmed; eight discovery records contain 4 candidate terminals and 4 OPEN3 states |

The C744 early-stop record contains four written complete rounds and no final footer. Preserve it and its log. It is not a completed OPEN6 parent and receives no completed-state credit.

Two source-save operations were unresolved when access disappeared:

- A's `verify_C744_original_fixed_and_recursive_cover.py` was being written and syntax-checked. Its existence, bytes, hash and review status are unconfirmed. Treat it as preparatory if it appears.
- B's `run_b16a_I22_F_survivors_continue6.py` save orchestration was terminated after the outage. File persistence is unconfirmed; no continuation process was launched.

The D821 3→6 exact component and complete-four gate passed B's independent source review `26fcc6df…`; root's full source/hand review is still pending. C744's complete-sibling extension `75c2b0b9…` also awaits Global's review. Neither pending review may be silently inferred from the completed underlying component replays.

## Other mask work

The first full-nine `011/00` PSD experiment completed all ten accepted closed domains and produced ten OPEN results, with zero numerical or exact exclusions. Its model retains all nine original frames and all 36 physical pair unions; selector integrality and rank one are explicit relaxations. The frozen model has 384 inputs, 45,352 necessary rows, 2,204 variables and a 55-by-55 PSD matrix.

Saved solution diagnostics point to fractional separating-owner selectors and covariance as substantial relaxation gaps. That is a discovery observation, not a proof. The authorized next screen is a complete 80-branch cover: all ten domains times all eight B/F owner alternatives. Each branch fixes one B/F selector to one and the other seven to zero, retaining all other pair unions and all 38 strict-slack rows. The intended first-pass limit is one worker, 30 seconds and 3,000 iterations per branch, sharing the same immutable model. Source and complete-union review are required before launch. The screen had not been launched.

Cd402's new exact whole-eight state should first be screened with the accepted opposite-tilt AHID and small-angle sharp guards. Use its proved orders if available when choosing the complete necessary complement; do not import current-mask order hypotheses into another mask.

## Recovery order

1. Restore execution access. Inspect available disk, actual processes, pending writes, logs and normal completion footers. Do not assume an interrupted tool or an existing session finished.
2. Fetch the current PR branch and inspect local status. Preserve local changes. Reconcile this additive recovery commit with the local `session-complete-masks-20261103` checkout; do not stage the obsolete untracked B265 archive.
3. Recheck the immutable manifests and the last accepted report hashes. Preserve every failed or partial scientific attempt. Resume only unfinished work in fresh output paths; never overwrite an accepted source or raw certificate.
4. Finish the D6c5 I22 continuations, independent exact replays, complete sibling covers and whole-original assembly. Continue to the other unchanged original parents.
5. Review and package B580 I11; finish C744's terminal attachments, B16a's I21/I22 and D821's priority I-quarter replays.
6. Screen Cd402's exact whole state, then choose a complete further cover. Finish source review of the finite `011/00` B/F screen before running it.
7. Continue with the other masks. Commit accepted complete checkpoints frequently, while retaining the fixed denominators and every explicit unresolved parent.

Use the reviewed manifest-only interned freezer `ec08d1e3…` and strict component runner `6a6b527f…`. Freeze only declared immutable inputs and completed output snapshots. Do not bind a mutable aggregate progress file or treat an early numerical stop as a normal completed parent. Ancestry manifests and source bindings must remain independently copied.

Disk was last observed near 2 GB free. The owned redundant-transfer cleanup `recover_owned_archive_transfer_prefixes_v3.py` may have been launched; its completion is unconfirmed. Inspect its process, `REDUNDANT_OWNED_ARCHIVE_TRANSFER_PREFIX_RECOVERY_V3.log` and durable journal before any retry. It is restricted to inactive owned transfer copies that exactly match byte prefixes of retained canonical archives. Retain the canonical archives, proof inputs, scientific failures and all foreign-workspace files.

The `001/00` work retains the same nine physical originals, 36 corners, 36 pairs, five marked cones, actual AB/BC/EF/FG and strictly weak CD for `q<Q=1105/256`, together with every shared closed face, contact and orientation endpoint. Work on other masks retains each mask's own exact bits; in `011/00`, both BC and CD are strictly weak. Its proof must not import `001/00` actual-BC or height/order hypotheses. No Lean, Lake or CI is authorized. The PR remains draft and unmerged.

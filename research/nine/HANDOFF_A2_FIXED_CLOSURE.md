# Current A.2 handoff: close the fixed full domain 000/01

**Updated computational handoff:** The user authorized computer-assisted proof discovery first. Produce a genuine exact certificate over all moving physical squares for `000/01` (or a canonical original root), independently replay it, and only then write the hand/table proof. `computer_assisted/emit_fixed_mask.py` generates the full target; `test_emit_fixed_mask.py` supplies positive/negative exact controls. The 58-leaf fixed-seven no-eighth certificate and its independent checker are a successful *pipeline* test only, not a nine-square closure. The current runtime lacks an exact nonlinear SMT solver; a solver's unsupported `unsat` answer would not itself be an accepted certificate. No new gate IDs or full-domain closures.

**Global status: OPEN. Latest attempt: OPEN / BLOCKED. New full-domain closures: zero.**

Read `A2_COVERAGE_AND_CLOSURE_CONTRACT.md` and then `A2_000_01_ATTEMPT.md`. The proof sources remain a library, not separate active owner/sign/threshold campaigns. No mandatory subgates were added by the latest attempt.

## Exact target, unchanged

Prove `D_000/01^lt` empty, retaining all nine physical squares and all 36 pair constraints. Its selected four-chain is actual and center-cone; its selected three-chain has first link actual and second weak center-cone. The two other units and all cross-pair separator types remain arbitrary.

`D_000/10^lt` follows by reversing both chains and both coordinate basis vectors. A broader actual-four-chain theorem would also handle `000/11`. None is asserted easy or proved.

## What the latest attempt establishes and where it stops

The uniform routing argument in the attempt record derives, after vertical reflection, that all three selected outsiders lie above both inner main centers; both main heights are below 7/20. The central outsider has the derived whole-floor bound `y_P-h_P>min(y_1,y_2)+869/1860`. This does not give a lower bound on both main heights, so it does not establish the previous bounded-inner caller.

The physical endpoint caps leave the exact identity

    (27/2)*delta_R = 46*W + (27/2)*(eta_P+s+t) + K_L+K_R,

with W,s,t,eta_P nonnegative and K_L,K_R strictly positive at q<Q. The definitions and derivation are printed in the attempt record. No proof yet makes the two remaining physical units contradict this identity or forces another sharp terminal on the entire domain.

The same record supplies an exact seven-unit packing at squared radius 273/64<Q with the required selected mask. All 21 pairs are checked by hand. Its span reserves W,s,t,eta_P vanish; the outer tilt deficit pays positive cap slacks exactly. Thus neither the seven-square shortcut nor a presumed improvement of a loose inset step can close this argument. The selected seven already have two coordinate-exceptional pairs, so the one-exception theorem is not an automatic caller.

This counterexample does not contain the eighth or ninth square. It proves only that information beyond the selected seven is needed; it does not prove that both additional squares are individually indispensable. The explored eight-square shortcut remains unproved and undisproved. Do not treat failed numerical searches as exclusions, or import the older different-mask eight-square example without a new valid witness.

## Acceptance boundary

A closure commit must contain a complete full-domain argument. Extra floor, owner, height, or orientation hypotheses must be derived or have their entire complement treated inside that proof. An unfinished attempt stays OPEN/BLOCKED rather than becoming another mandatory case tree. A global extraction is a valid shortcut only when its actual coverage and all terminal premises are proved.

## Immutable accounting and preserved evidence

The original 7,915 root IDs and 15 roadmap IDs are unchanged. Historical published closed-Q exclusions remain 5,838, with 2,077 OPEN; nothing was rerun or regenerated. The same 32 hand-mask rows have two inherited complete strict-radius proofs (`000/00` and `010/00`) and 30 OPEN domains. These are not completion percentages.

Root 7820 contains equality and must remain nonempty at q=Q. A future q<Q discharge is distinct from a closed-Q exclusion. The pre-reset catalogue is preserved at `ea4ff8bad97a58e2b8633ab69f549acb5352e573`; the fixed-domain reset is `3b68416cfa087d56d737d5af0548ba106117fcc6`.

## Method and review boundary

Hand proof; exact tables allowed; no Lean, Lake, CI, or mathematical proof enumeration. The latest attempt used bounded numerical optimizations and a sampled rotation probe only to test possible directions. No numerical result certifies an exclusion. The accepted construction, routing, and algebraic identities are hand-derived. No new independent second-agent, human, or kernel review is claimed.

The fixed frontier controls accounting, not difficulty. Its decreasing unresolved-row count is not a termination theorem. A.2, unrestricted equality, and the complete final manuscript remain OPEN.

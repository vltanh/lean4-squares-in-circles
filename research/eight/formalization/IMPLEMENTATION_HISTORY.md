# Implementation milestones for the uncompiled n=8 draft

The new implementation is delivered in [PR #10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), stacked on the mathematical source branch `research/eight-proof`. The transferred source snapshot is PR #9 commit `a21c91f54039e805a637e983bc612bd130f39ee7`.

These timestamps are the actual UTC committer dates returned by GitHub's Git commit API. The accompanying [IMPLEMENTATION_COMMITS.json](IMPLEMENTATION_COMMITS.json) preserves both author and committer dates, tree identifiers, and parent links. They record source-writing milestones, not successful proof checking.

| Commit time | Commit | Source milestone |
|---|---|---|
| 2026-10-18 02:23:55 UTC | [c3b1283c10bf](https://github.com/vltanh/lean4-squares-in-circles/commit/c3b1283c10bff2dec65f97f1d5e5357c8bd0a164) | Transfer n=8 formalization roadmap and draft shared geometry model |
| 2026-10-18 02:37:20 UTC | [587731b65fcb](https://github.com/vltanh/lean4-squares-in-circles/commit/587731b65fcba4eba9ae928e3978fa4bdf000ec4) | Draft signed SAT, arithmetic semantics, radius transfer, and mismatch lemmas |
| 2026-10-18 03:13:22 UTC | [55809af8c715](https://github.com/vltanh/lean4-squares-in-circles/commit/55809af8c715c6ce372d67eba07e2c2069bd27fa) | Draft geometric reductions, stationary selection, and complete owner-dual application |
| 2026-10-18 03:54:10 UTC | [0858b29e5e05](https://github.com/vltanh/lean4-squares-in-circles/commit/0858b29e5e05196bcbb11845de23e693958f3197) | Add exact closed-cover and polynomial Lean source data for n=8 |
| 2026-10-18 03:59:24 UTC | [02d9a502110a](https://github.com/vltanh/lean4-squares-in-circles/commit/02d9a502110af157e14f9b645287c37a6a472f1d) | Complete uncompiled n=8 lower bound and five-parameter equality source |

The first commit carries the transferred roadmap and the shared actual-square model. The later milestones add the signed-axis semantics, geometric reductions, exact stationary selection, finite arithmetic data, candidate capture, unrestricted lower bound, and full equality-family source. All commit messages carry `[skip ci]` in accordance with the requested source-only delivery.

Subsequent statement-layer and documentation commits remain visible in [the PR commit history](https://github.com/vltanh/lean4-squares-in-circles/pull/10/commits). The source status is maintained in [STATUS.md](STATUS.md); the full route and finite-domain requirements are in [ROADMAP.md](ROADMAP.md).

## Preserved earlier history

The prior mathematical development and its 650-commit timestamp export remain in the inherited [PROGRESS_HISTORY.md](../PROGRESS_HISTORY.md) and [PRE_SQUASH_COMMITS.json](../PRE_SQUASH_COMMITS.json). This implementation log adds new milestones without replacing or rewriting that history.

## Execution scope

The requested deliverable is an uncompiled Lean source draft. Lean, lake, CI, historical checker replays, proof audits, and axiom/comparator checks were not invoked. Source generators construct the literal rational data and proof scripts; that construction does not establish that Lean accepts them. In particular, the `RealBox.certify 96` and other ordinary `by decide` bodies remain unevaluated until the later verification pass.


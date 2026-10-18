# n=8 Lean draft status

This is the source implementation pass requested on 2026-10-18 UTC.
No Lean invocation, build, CI run, or audit is authorized in this pass.

| Stage | Source ownership | Status |
|---|---|---|
| F0 | `Eight/Model.lean`, `Eight/SeparatingAxis.lean` | draft in progress |
| F1 | `Eight/Arithmetic/`, `Eight/Generated/` | draft in progress |
| F2 | `Eight/ExactFamily/` | draft in progress |
| F3 | `Eight/CentralCore.lean` | draft in progress |
| F4 | `Eight/BoundaryReduction.lean`, `Eight/RadiusTransfer.lean` | draft in progress |
| F5 | `Eight/Frames.lean` | draft in progress |
| F6 | `Eight/QuarterWords.lean` | draft in progress |
| F7–F8 | `Eight/Candidate/` | draft in progress |
| F9 | `Eight/Terminal.lean` | draft in progress |
| F10 | `Eight/Theorem.lean` | pending assembly |
| F11 | `Eight/Equality.lean` | draft in progress |
| F12 | public import; later checking and audit | verification deferred by user |

The mathematical sources and all finite table domains are inherited from
[the transferred roadmap](ROADMAP.md). The equality target has five independent
parameters; it does not assert a unique isolated optimal pose.

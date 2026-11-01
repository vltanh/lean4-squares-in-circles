# n=9 — sharp nine-unit-square packing

**Goal OPEN:** prove all nine arbitrarily oriented unit squares inside a disk satisfy R²>=1105/256, then classify every equality packing.

[Current proof status](PROGRESS.md) · [one proof-first roadmap](DEEP_GATED_ROADMAP.md) · [implemented direct model and sharp row-profile certificate](computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md).

The unrestricted quadratic emitter, complete source equivalence argument, exact geometry controls and a proper continuous-row-family certificate are now available. A separately implemented exact checker verifies the row identity; this does not prove that every packing has that row structure. No separate human review or global SMT result is claimed.

**Active task: D.3.c** — broader certified coverage of unrestricted relative orientations, or a documented limitation/pivot of the direct approach. No legacy progress fractions. Computer-assisted proof first, hand/table simplification later. No Lean/Lake/CI.

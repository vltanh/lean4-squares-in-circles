# Exact caches and sparse dual conversion for proof discovery

These changes reduce repeated numerical-discovery work. Every geometric row, rational bound, complete cover and final certificate still passes the unchanged independent physical verifier.

## Coupled-energy cache

The pure coupled-energy generator recomputed identical coordinate projections and vertex energies many times. Bounded caches now reuse those values, and a two-entry cache reuses a complete result for identical pair intervals, diagonal intervals and directions. The wrapper returns a fresh row list and deep-copies mutable guard records. No caller can mutate a cached result.

The packet retains the exact reference generator and two complete pair-interval inputs. Replay compares every row, its order and every guard field: 5,220 rows and 336 guard records. It also mutates returned containers and checks that the cached source remains unchanged. The initial discovery benchmark measured generation at 1.70 s to 1.24 s and 1.81 s to 1.17 s; an identical repeated interval state took 0.015–0.039 s. Timings depend on workload and host load.

## Sparse dual conversion

The former converter applied Python rounding to every entry of a dense LP dual vector. On finite float64 vectors whose scaling cannot overflow, nonnegative entries cannot produce a positive multiplier, so the new converter visits only negative entries. It then applies exactly the same `int(round(-float(v) * SCALE))` with `SCALE = 2**40` and keeps the same positive values and ascending indices. Other input types, nonfinite values and potentially overflowing values use the original function.

The fixture reconstructs dense vectors from 197 saved sparse multiplier lists, containing 6,778 nonzero weights. It does not contain the original unrounded solver vectors. Separate controls check 42 signed half-grid boundaries and adjacent floating-point values, plus five nonfinite/overflow error cases. The recorded initial benchmark for this conversion was 3.65 s to 0.08 s. This is a timing for one operation, not the complete proof search.

## Replay

```sh
python -B verify_packet.py
```

NumPy is required only for the dual-conversion comparison. The independent physical certificate checker remains standard-library-only and imports neither optimization. New original-cell credit: 0. New mask credit: 0. No Lean, Lake, compilation or CI is used.

# Faster assembly of identical exact area-moment rows

The numerical proof search was rebuilding the same pair/matrix secants for every subset of five through nine originals. A profile of a real Bf14 state attributed 15.5 of 27.0 profiled seconds in row collection to this generator. The optimization computes each pair/matrix contribution once, then sums those exact rational contributions for each original subset. A bounded cache also reuses identical interval states.

No inequality, geometric premise, subset, matrix, coefficient, right-hand side, row name, or row order changes. The independent checker remains unchanged and does not install this numerical-discovery optimization. Any subsequent certificate must still pass the usual independent physical replay.

On two saved Bf14 interval states, all 3,072 rows per state matched exactly. Unprofiled generation times in the recorded run were 4.54 s → 0.69 s and 4.30 s → 0.57 s; a repeated interval state took about 0.0002 s. These are generator timings, not a claim that the whole search is seven times faster.

## Reproduce literal parity

```sh
python -B -S check_parity.py /tmp/area-moment-parity.json
```

The packet includes the byte-identical reference generator and the complete pair-interval inputs needed for this comparison. The original node hashes identify provenance; their full physical ancestry is not needed to check equality of the two pure generators. The input file makes no new geometric-domain claim.

`fast_exact_area_moments.install(module)` installs the optimized generator in a numerical process after its frozen reference module is loaded. The caller must bind this optimizer source in its discovery manifest. Previously running processes and frozen source files are not edited.

## Exact assembly identity

For each matrix B and original pair i < j, precompute the two coordinate coefficients and constant obtained from the same two interval secants in the reference implementation. The row for subset S is the sum of these pair contributions over i < j in S, followed by the unchanged lower bound for |S| and B. Associativity of rational addition gives the identical reduced fractions. Enumeration retains the reference order: subset size, matrix, then lexicographic subset; coefficients retain original-column order.

The cache key contains every original pair interval, the complete ordered matrix list and the subset-size list. Pair contributions have a separate bounded cache keyed by all pair intervals and the exact matrix. All returned row tuples and fractions are immutable, and each caller receives its own outer list.

This is a discovery-performance change. New original-cell credit: 0. New mask credit: 0. No Lean, Lake, compilation or CI is used.

# B continuation readiness after exact source restoration

The new discovery wrapper adds the accepted exact area-moment assembly
optimization to the previously reviewed accepted-center runtime. It introduces
no new inequality, variable, row name, row ordering, physical premise, or
independent checker rule. Its atomic driver differs from the accepted driver
only in the imported runtime module.

The actual loaded reference generator has SHA256
`d4d4b7a9bda2595693ea10e15821eedfb5681b9f1be32381179b20512d2700d1`,
identical to the reference in the published optimization packet. The optimized
helper has SHA256
`9afb26cad3032731902679f67a3ff166d44ba5d2a5684cf31f832da767edd071`.
Root's published review requires complete36-pair inputs, immutable rational
intervals, stable finite count/matrix sequences and unchanged helper functions.
The new wrapper enforces those conditions before invoking the cached generator.

For each matrix and pair, the optimizer precomputes precisely the coordinate
coefficients and constant in the reference secant calculation. Summing the
same rational contributions over each original subset gives the same row.
The subset, matrix and coefficient enumeration order is preserved. Cache keys
include all pair intervals and the ordered count/matrix sequences. No cached
state can replace a physical premise of the independent checker.

Observed session77745 exited0 on an actual B16 root state from the freshly
replayed45-node cover. All3,072 rows matched exactly, including coefficients,
right-hand sides, names and order. A repeated call matched, and changing the
returned outer list did not change the cached result. Four invalid callers
were rejected: a missing pair, a matrix iterator, a different subset-size
sequence, and a changed lower-bound function. The report SHA256 is
`e24f62174bf0f1da13dc1157e8f92341b7a9f0fbd76d14f93a4092a1f97d66d6`.
The measured5.20s versus0.965s concerns only this generator; no whole-search
speedup is claimed. No LP solve was performed by the parity gate.

## B16 readiness

The preserved complete45-node cover retains the merged closed I21/I22 domain
of original `negative-16a2fc93c8d133f0`. It has two excluded leaves,28 OPEN
leaves, seven complete proxy unions and eight complete angle unions. Fresh
ordinary accepted-center replay session86994 exited0 after21 rounds,2,324
deductions and7,865 checked rows. The exact report SHA256 is
`6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa`.
The later uncommitted105/107-node suffix is unavailable and is not reused.

Observed preparation session29887 exited0 and preserved every45-node payload,
parent and cover byte-for-byte. The prepared manifest only adds the newly
frozen discovery sources. Numerical launch is held because a separate B16
search is active; this readiness packet does not authorize a duplicate.

## B462 alternative readiness

The new attachment of the unchanged published two-round B462 record freshly
replayed in session83098, exit0. It preserves the complete registered original
`negative-462e78d2e2d8be05`, with one OPEN node,214 deductions,490 rows and82
accepted center-row occurrences. Its report SHA256 is
`6bbedffa6c286313e4f904cd9a8c134969cb7b22284585a3fd61b627dc2d53ba`.
The new attachment does not reconstruct the missing historical capture program
or the old run directory. Its separate hand attachment states that limitation.

Observed preparation session17902 exited0 and preserved the complete raw node,
parent and state bytes. B462 is a held alternative for a future free numerical
slot; no new search was started by this preparation.

Both proposed commands use two rounds for newly searched ordinary states,
one round for already-searched retained leaves, zero initial proxy rounds,
depth24 and at most64 new nodes. The frozen driver keeps its existing rules
for unsearched zero-round siblings and its before-SAT propagation. Every new
proxy/SAT/angle split still installs all4/8/2 closed alternatives before any
child search. The independent row, bound, terminal, original-domain and complete
cover checkers are unchanged. No original-cell or mask count changes here.

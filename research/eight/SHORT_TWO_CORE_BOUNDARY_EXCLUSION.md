# Global exclusion of the short two-core word

**Proved.** The seven-state radial word `COCOOOO` cannot occur in an adjacent-pair feasible boundary representative at squared radius \(Q=9789/2500\), with core radius \(1/12\).

The exact verifier data are `two_core_short_pair_data.json`. The completed manifest is `two_core_short_pair_logs_checked/manifest.json`. It records all 28 required ordered-role/sign branches, comprising 1,792 initial closed affine-piece rectangles. The computation visited 9,535,240 nodes and 4,768,516 leaves, with maximum depth 29, and all undefined-behavior sanitizer logs were clean. The exact input data are preserved byte-for-byte from the completed run; their historical candidate status field is superseded by `two_core_short_certificate_status.json` and the completed manifest.

## Ordered role potentials

Suppose the word occurs. Number its seven centers counterclockwise so the physical boundary types are

\[
(C_0,O_1,C_2,O_3,O_4,O_5,O_6).
\]

For each role \(i\), write \(t_i=\tan\alpha_i\in[-1,1]\), with the frame angle relative to that center's ray. Define \(\psi_i\) by linear interpolation on the signed knots \(t=k/8\), \(k=-8,\ldots,8\), using the exact numerator arrays in the data JSON and denominator \(10^8\). The positive and negative arrays contain the actual function values on the two signed halves. They need not be odd. A single consistently chosen chart value \(t_i\) is used for both incident edges of each role.

The exact checker proves

\[
\delta_i+\psi_{i+1}(t_{i+1})-\psi_i(t_i)
\ge\Gamma_i
\]

for every feasible ordered edge \(i\to i+1\), with indices taken modulo seven. The constants are:

| Ordered edge | Boundary types | Numerator of \(\Gamma_i\), denominator \(100000\) |
|---|---|---:|
| \(0\to1\) | C--O | 98722 |
| \(1\to2\) | O--C | 83635 |
| \(2\to3\) | C--O | 98566 |
| \(3\to4\) | O--O | 79316 |
| \(4\to5\) | O--O | 90441 |
| \(5\to6\) | O--O | 79315 |
| \(6\to0\) | O--C | 98550 |

Every ordered edge was verified directly for all four sign combinations of its two tangents. No reflection symmetry, equality between reverse-edge constants, or oddness of a role potential is assumed. The geometric part of the verifier uses the same independently audited true SAT projections and exact disk/core boundary formulas as the earlier pair certificate. The width coefficient is zero.

## The contradiction

Summing the seven inequalities telescopes all seven role potentials, irrespective of their differences from one role to another:

\[
\sum_{i=0}^6\delta_i
\ge\sum_{i=0}^6\Gamma_i
=\frac{125709}{20000}.
\]

The physical center-ray cycle has angle sum \(2\pi\). However,

\[
\frac{125709}{20000}-2\pi
>\frac{125709}{20000}-\frac{710}{113}
=\frac{5117}{2260000}>0.
\]

This contradiction proves the word exclusion.

## Exhaustive remaining radial words

The radial boundary theorem preserves the physical angle sum and the seven adjacent true SAT constraints. The no-adjacent-core theorem and the separate three-core exclusion leave at most two C labels, and no two C labels can be neighbors. When there are exactly two C labels on a seven-cycle, their cyclic distances are either \(2,5\) or \(3,4\). The first case is exactly the word excluded here. Hence every hypothetical unrestricted eight-square counterexample has a seven-square exterior boundary representative with one of exactly three radial necklaces:

\[
\boxed{\mathrm{OOOOOOO},\qquad\mathrm{COOOOOO},\qquad\mathrm{COOCOOO}.}
\]

This is a global adjacent-pair reduction. It does not require an orientation-majority assumption and permits nonneighbor overlaps created by the radial deformation. The three remaining words still require an exhaustive capture argument into the uniform local candidate family; they are not themselves excluded by this theorem.

## Reproduction and audits

From `research/eight`:

```sh
g++ -O3 -std=c++17 -fsanitize=undefined -fno-sanitize-recover=all -DPAIR_DATA_FILE='"two_core_short_pair_data.hpp"' verify_boundary_pair_costs.cpp -o /tmp/n8-short-two-core
python3 run_boundary_pair_costs.py /tmp/n8-short-two-core two_core_short_pair_data.json two_core_short_pair_data.hpp /tmp/n8-short-two-core-logs 3
```

The signed data header enables the separate positive/negative role tables.
All seven directed edges are required explicitly. The exact source, header,
data, executable, and 28 branch-log hashes are bound in the manifest;
`short_two_core_binding_audit.json` records an independent full coverage
and binding check. The [arithmetic range audit](DYADIC_PAIR_ARITHMETIC_RANGE_AUDIT.md)
proves that all 64-bit narrowing and 128-bit products remain in range for
these data, beyond the successful sanitizer execution.

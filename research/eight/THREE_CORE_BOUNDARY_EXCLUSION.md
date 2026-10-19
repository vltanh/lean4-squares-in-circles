# Global exclusion of three core-boundary states

**Proved by exact continuous pair verification and a hand telescoping argument.** The exact rational data used by the validator are `three_core_pair_data_v2.json`; the completed verification manifest is `three_core_pair_logs_checked_v2/manifest.json`. All eight required closed sign branches passed, with all 64 affine-piece rectangles covered in each branch. The run used the exact dyadic arithmetic engine and completed without undefined-behavior sanitizer errors. Earlier discovery candidates are not proof inputs.

## Pair theorem

Use radial boundary types `C` (core) and `O` (outer) at squared radius \(Q=9789/2500\), with core radius \(1/12\). Let \(t=\tan\alpha\in[-1,1]\), where \(\alpha\) is a square frame relative to its center ray. The boundary radius formulas are those in `CYCLIC_RADIAL_BOUNDARY_REDUCTION.md`.

Define odd potentials by linearly interpolating these values at \(t=k/8\), \(k=0,\ldots,8\):

| Type | Numerators with denominator \(10^8\) |
|---|---|
| C | \(0,1142853,2408492,3743201,5006713,6018038,7587799,0,0\) |
| O | \(0,799677,4163365,6444301,7593139,6626810,4538691,2271550,0\) |

For every feasible ordered boundary pair with positive center-angle gap \(\delta\in(3/5,\pi)\), the exact verifier establishes

\[
\begin{aligned}
\delta+\psi_O(t_b)-\psi_C(t_a)&\ge\frac{4698}{5000}
&&\text{for C--O},\\
\delta+\psi_O(t_b)-\psi_O(t_a)&\ge\frac{3244}{5000}
&&\text{for O--O}.
\end{aligned}
\]

These inequalities use true square SAT nonoverlap and exact disk/core boundary formulas. They impose no alignment assumption. The width-excess coefficient is zero. The verifier handles all four tangent-sign choices on every closed piece rectangle. Reflection followed by source/target reversal supplies O--C from C--O: the transformation sends \((t_a,t_b)\) to \((-t_b,-t_a)\), preserves the geometric gap and boundary types after reversal, and oddness preserves the potential difference.

The generic checker has the same geometric coefficient formulas as the separately audited four-type checker; the cost contraction becomes simpler when \(\beta=0\). All operations used for acceptance are exact outward dyadic enclosures. The manifest hashes the data, arithmetic source, generated header, verifier source, executable, and branch logs. The JSON data are deliberately left byte-for-byte unchanged from the verified run, even though their historical status field says candidate.

## Global finite implication

Start with any seven unit squares avoiding the open core disk of radius \(1/12\), lying in the radius-\(\sqrt Q\) disk, and with pairwise disjoint interiors. The radial boundary reduction produces an adjacent-pair feasible seven-center cycle, with every square of type C or O and physical angle sum

\[
\sum_{i=0}^6\delta_i=2\pi.
\]

The independently proved no-adjacent-core theorem excludes neighboring C labels in this representative. A seven-cycle with three C labels and no neighboring C labels has, up to cyclic rotation, the single word

\[
\mathrm{COCOCOO}.
\]

It has six cross edges and one O--O edge. Summing the seven pair inequalities telescopes the potentials and yields

\[
2\pi=\sum_{i=0}^6\delta_i
\ge6\frac{4698}{5000}+\frac{3244}{5000}
=\frac{3929}{625}.
\]

But the classical bound \(\pi<355/113\) gives the strict rational contradiction

\[
\frac{3929}{625}-2\pi
>\frac{3929}{625}-\frac{710}{113}
=\frac{227}{70625}>0.
\]

Therefore **at most two squares in the global radial boundary representative touch the core boundary**. The remaining radial necklaces are exactly

\[
\mathrm{OOOOOOO},\qquad
\mathrm{COOOOOO},\qquad
\mathrm{COCOOOO},\qquad
\mathrm{COOCOOO}.
\]

This reduction is independent of the M5/M6 orientation classification. It applies to the adjacent-pair relaxation produced by the boundary deformation; nonneighbor overlaps created during that deformation are permitted. It does not yet exclude the four remaining words or prove unrestricted optimality.

## Reproduction

From `research/eight`, build the generic validator against the exact retained header and run all declared branches:

```sh
g++ -O3 -std=c++17 -fsanitize=undefined -fno-sanitize-recover=all -DPAIR_DATA_FILE='"three_core_pair_data_v2.hpp"' verify_boundary_pair_costs.cpp -o /tmp/n8-three-core
python3 run_boundary_pair_costs.py /tmp/n8-three-core three_core_pair_data_v2.json three_core_pair_data_v2.hpp /tmp/n8-three-core-logs 3
```

The completed run has 754,058 tangent nodes, 377,285 terminal rectangles, and maximum depth 22; `754058 = 2*377285 - 512`. The data/header/source/log hashes are retained in the manifest. The historical candidate wording inside the unchanged input JSON is superseded by `three_core_certificate_status.json`, which binds the verified data and manifest by SHA-256.

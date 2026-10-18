# Gate 3B.2 / HIGH: independently replayed exact 4+4 two-frame exclusion

**2026-10-13. Complete finite, computer-assisted rational certificate, not a short analytic or Lean proof.** This closes the small Jensen-defect *odd-cut* M5-HIGH child. The unrestricted eight-square theorem and M5-DIFFUSE remain OPEN.

## Fixed-frame theorem

Four axis-parallel unit squares and four unit squares rotated by 45 degrees, arbitrary centers, pairwise disjoint interiors (tangencies permitted), cannot lie in a closed radius-`198869/100000` disk. The entire proof data, independent checker, generator, and SHA256 manifest were produced and **all 66 roots independently replayed** in the associated conversation archive `n8_m5_high_fourfour_exact_certificate.zip`. **The archive has not been added to this GitHub branch**; this file records the statement and verification dependencies but *does not by itself constitute the full finite certificate*. The mathematical theorem depends on the supplied proof data.

### Exact reduction

Let the four standard centers be sorted by `s=x+y`, with relative rank permutation `pi` for `t=x-y`. If `pi_i<pi_j`, genuine axis-parallel SAT separation and weak s/t order force `x_j-x_i>=1`; otherwise `y_j-y_i>=1`. Thus a monotone increasing or decreasing four-permutation forces span >=3, impossible because each center lies within radius `198869/100000-1/2<3/2`. There are 22 permissible standard permutations.

Order the four 45-degree centers by x; record the relative y-order `sigma`. True same-diagonal-frame SAT is `|dx|+|dy|>=sqrt(2)`. With the signs from sigma, each diagonal pair forces `dx+dy>=sqrt(2)` or `dx-dy>=sqrt(2)`. A monotone permutation spans >=3 along a diagonal unit coordinate, also impossible. There are 22 such diagonal permutations.

Each physical D4 rotation/reflection acts on both groups **together**, preserving the disk and both frame types. Exact permutation enumeration shows 484 paired orders split into 66 D4 orbits. Weak center-order ties are allowed: the source order can choose any compatible weak ranking; the forced inequalities remain genuine.

Use 128 exact rational unit tangent directions: `((1024-k*k)/(1024+k*k),64*k/(1024+k*k))`, `0<=k<=32`, and their four quarter-turns, removing duplicates. Each actual square satisfies `n·p_i+H_i(n)<=Rbar`; for standard squares `H=(|nx|+|ny|)/2`, for diagonal squares `H=sqrt(2)*max(|nx|,|ny|)/2`. The exact model lowers sqrt(2) to `707106781/500000000`, making disk and support rows a **necessary outward relaxation**, never a stronger condition than actual geometry.

All six standard-standard and six diagonal-diagonal pair constraints of each order are retained. Every one of the 16 mixed pairs has **all eight signed true SAT alternatives**. Canonical maximum-projection owners exist because all candidate owner axes have the same support sum; signed coordinate axes require `n·d>=(1+sqrt(2))/2`; signed raw diagonal axes require `n·d>=1+sqrt(2)/2`. Each selected bundle also carries two necessary comparison/cone rows. A matching upper rational bound `1414213562373096/10**15` for sqrt(2) is used only where widening the cone requires an upper bound. No mixed owner or contact pattern is presumed in advance, and every tie is retained.

## Certificate format, exact inference

Every active row has form `A_r·p<=b_r`, `p` containing sixteen center coordinates. At a branch node choose a mixed pair and branch over ALL EIGHT signed true axes, preserving every ancestor row. A leaf supplies positive integer multipliers `alpha_r` over rows already active on that branch. Put `v=sum alpha_r*A_r`, `B=sum alpha_r*b_r`; the independent verifier accepts only if

```
B + (3/2)*sum(abs(v[k]) for k in range(16)) < 0.
```

This is an exact Fraction comparison. For any actual packing each center coordinate has absolute value <3/2, so `v·p>=-(3/2)*sum|v[k]|`, contradicting weighted rows `v·p<=B`. The residual force is charged exactly; approximately balanced LP multipliers are **not** treated as exact balances. Unselected SAT rows, missing alternatives, repeated branch pairs, and invalid weights are rejected.

The numerical generator was used for **discovery only**, not by the verifier. The independent replay imports only its rational geometry model and Python's standard library (Fraction, gzip, JSON), not SciPy/NumPy/the generator.

| Complete independent replay | Count |
|---|---:|
| D4 symmetry roots | 66/66 |
| Original admissible paired orders covered | 484/484 |
| Verified proof nodes | 73,210 |
| Verified terminal rational contradictions | 64,067 |
| Verified eight-way branches | 9,143 |
| Maximum branch depth | 9 |

Five deliberate corruptions (wrong root, omitted signed SAT child, zero weight, unselected row, out-of-range pair) were rejected. A second complete replay produced the same totals. A separate **positive** rational-center 4+4 packing, with squared enclosing radius <81/20 and all 28 true SAT pair gaps >=1/1000, maps by one genuine D4 transformation to root 58 and satisfies its relaxed rows at radius 2013/1000; it is NOT an excluded-radius packing.

**Reproduction:** Obtain the complete referenced conversation ZIP and run, from its root:

```sh
python research/eight/verify_m5_fourfour_certificate.py --directory proofs
python research/eight/verify_m5_fourfour_mutations.py
python research/eight/verify_m5_fourfour_positive.py
```

A successful exit requires a complete 66/66 replay. Individual root results are not the entire proof. A 23-root separate 3+5 certificate is already in this PR as `GATE3B_M5_LOW_EXACT_CERTIFICATE.md`.

## Entire M5 small-J exclusion, including HIGH

Use the prior `GATE3B_M5_HIGH_JENSEN_EVEN_EXCLUSION.md` quantitative theorem. For folded coordinates x and barycentric weights lambda, define `c=(sqrt(2)-1)/2`, `W0=28+15c`, `E=W-W0` and

```
J = E - c*(lambda_1+lambda_3+lambda_5+lambda_7).
```

When `J<=3/1000`, all eight frames lie within 1/200 radians of a **single** exact 3+5 (even-index) or 4+4 (odd-index) two-frame cut. Inscribe reference-oriented squares of side `200/201` in the genuine squares and rescale; this produces a *real packing*, with **all 28 pair nonoverlap conditions**, at squared radius at most

```
(9789/2500)*(201/200)^2 = 395485389/100000000 = 3.95485389.
```

The complete earlier 3+5 certificate excludes every even cut. The current verified 4+4 certificate excludes every odd cut, because

```
(198869/100000)^2 - 395485389/100000000
     = 340261/10000000000 > 0.
```

**Corollary:** Every hypothetical M5 eight-square packing under the research ceiling has `J>3/1000`. This includes previous LOW, HIGH-J-EVEN, and HIGH-J-ODD in their now-excluded regions; threshold equality is excluded.

For `h=pi/4`, `V=sum_{i<j}(x_j-x_i)(h-x_j+x_i)`, pair-width second derivatives lie between `-sqrt(2)/2` and `-1/2`, so `V/4<=J<=sqrt(2)*V/4`. Therefore an additional necessary strict orientation inequality is `V>3sqrt(2)/500`. **This inequality is necessary but not equivalent to `J>3/1000`; do not reverse the implication.**

## Unproved exit / strict stop rule

**Remaining M5-DIFFUSE:** `J>3/1000`, with both folded words I/II, arbitrary frames, all actual disk vertex constraints and all 28 genuine true SAT pair disjunctions. No complete structural classification or radius bound for this domain exists. M5, M6--M8, unrestricted `R_8>=R_*`, and equality remain open. Do not label the global PR complete or merged. No production Lean, Lean compilation, or CI involved.

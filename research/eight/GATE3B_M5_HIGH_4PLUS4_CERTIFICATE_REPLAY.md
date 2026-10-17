# Gate 3B.2: exact 4+4 two-frame exclusion and closure of all small-J M5

Date: 2026-10-13. **Computer-assisted exact finite proof**, independently replayed using integer and Fraction arithmetic. This is not an unrestricted eight-square theorem, not a short analytic case proof, and not a Lean formalization.

## Theorem

No packing of four horizontal/vertical unit squares and four squares rotated exactly 45 degrees, with arbitrary centers and disjoint open interiors, fits in a disk of radius

    Rbar = 198869/100000.

The same proof retains contacts/tangencies and all true-SAT owner choices. It does not assume a central square, contact graph, or center-order symmetry.

### Complete geometric case cover

Use common physical D4 (four rotations and four reflections) only: **do not** independently transform the two frame classes. Every center obeys |p_i|<=Rbar-1/2<3/2 because its square contains a radius-1/2 disk.

Label standard centers 0..3 in weak increasing order of s_i=x_i+y_i; record their weak t_i=x_i-y_i order by a permutation pi. True standard-square nonoverlap forces, for i<j in the s-order:

* If t_i<=t_j then x_j-x_i>=1.
* If t_i>=t_j then y_j-y_i>=1.

Consequently completely increasing/decreasing pi would force a horizontal/vertical center span at least 3, impossible. Both weak choices are retained at ties. Exactly 22 of 24 pi orders survive.

Label diagonal centers 4..7 in weak increasing x-order and record their weak y-order by sigma. True diagonal-square separation gives x_j-x_i+(y_j-y_i)>=sqrt(2) when sigma increases and x_j-x_i-(y_j-y_i)>=sqrt(2) when it decreases. The completely monotone sigma orders would force center projection span at least 3 in a diagonal unit direction, impossible. Exactly 22 sigma orders survive.

There are 22^2=484 joint pairs of permutations. Modulo **common** D4 there are exactly 66 root classes. A finite exhaustive rational permutation check constructs their representatives and verifies all 484 belong to their common-action orbits; there is no assumption of independent reflection of one frame class.

### Safe rational relaxation

For each actual square center and each of 128 Pythagorean unit directions n, disk containment gives

    n dot p_i + H_i(n) <= Rbar.

The directions are ((1024-k^2)/(1024+k^2),64k/(1024+k^2)), k=0..32, and their quarter-turns. For standard squares H_i(n)=(|nx|+|ny|)/2; for diagonal squares H_i(n)=sqrt(2)*max(|nx|,|ny|)/2. Replace sqrt(2) by the strict rational lower bound 707106781/500000000. This produces an **outer** relaxation. The 12 within-class pairs inherit the forced separator directions from the two orders.

For every one of 16 mixed pairs, retain ALL EIGHT genuine signed separating-axis choices (four coordinate and four diagonal axes), including canonical-maximizer ties. Each branch carries the true-support lower bound (relaxed by rounding sqrt(2) downward) and two necessary canonical-cone comparisons (also relaxed outward, using 1414213562373096/10^15 as an upper bound for sqrt(2)). Thus no actual square packing can escape the 66 roots and the branch alternatives.

### Exact rational leaf condition

Every necessary row is expressed as A_r dot p<=b_r with all 16 center coordinates in [-3/2,3/2]. At a leaf nonzero positive integer weights alpha_r produce v=sum alpha_r A_r and B=sum alpha_r b_r. The independent verifier accepts only if

    B+(3/2)*sum_{j=1}^{16}|v_j| < 0

using exact fractions. This charges all residual force to the center box; merely approximate numerical force balance never passes. Every branch node must contain all eight alternatives. Leaves may use only globally applicable or inherited selected rows. The code reconstructs rows from geometry rather than trusting stored numerical matrices.

### Entire replay and negative controls

The independent verifier was rerun to completion on all **66** gzip-compressed proof roots:

| Item | Exact replay |
| --- | ---: |
| D4 representatives / original order pairs | 66 / 484 |
| Nodes | 73,210 |
| Branches | 9,143 |
| Rational contradiction leaves | 64,067 |
| Maximum branch depth | 9 |

All five deliberate corruptions were rejected: invalid root, missing branch child, zero multiplier, unselected mixed row, and invalid mixed-pair index. A separately constructed true 4+4 packing of radius above Rbar passed all 32 actual vertex conditions, all 28 SAT pairs, and the corresponding relaxed certificate-root model, guarding against accidentally proving an impossibility at *all* radii.

The complete 66-root proof archive, solver-independent verifier, rational model, optional discovery generator, exact replay logs, and SHA256SUMS accompany the research delivery as the archive `n8_m5_high_fourfour_exact_certificate.zip`, SHA256:

    84ee630f0a2830380db93745f95b10d23e55b3bbed01bb9143cbff9b95d5481b

**Reproducibility caveat:** The binary proof-root data are not contained in this text-only GitHub commit. This note documents a replay that was actually performed against the referenced archive; a reader must obtain the accompanying archive to reproduce the full theorem. Do not treat the prose or the generator alone as a certificate. The full replay uses Python standard library only and no LP/SLSQP/interval solver as an acceptance premise.

## New unconditional reduction inside M5

For either M5 folded word let h=pi/4 and let lambda_1,...,lambda_8 be its ordered-simplex barycentric weights. With c=(sqrt(2)-1)/2, W0=28+15c, and actual pair widths w_ij, set

    E=sum_{i<j}w_ij-W0,
    J=E-c*(lambda_1+lambda_3+lambda_5+lambda_7).

The previously proved two-sided Jensen inequality gives, for V=sum_{i<j}(x_j-x_i)(h-x_j+x_i),

    V/4 <= J <= (sqrt(2)/4)*V.

Whenever J<=3/1000, strong Jensen forces one unique lambda_k>99/100 and ALL original true frames within 1/200 radians of that cut's two exact reference orientations. If k is even it is 3+5; if odd it is 4+4. Insert reference squares of side b=200/201 into the actual whole squares, preserving all 28 nonoverlap constraints and disk containment. Upon scaling by 1/b, the reference packing would have

    q_ref <= (9789/2500)*(201/200)^2 =395485389/100000000
          < (198869/100000)^2.

The preexisting exact 3+5 certificate excludes the even cuts; the present exact 4+4 theorem excludes the odd cuts. **Therefore every hypothetical M5 packing below the research ceiling must satisfy**

    J > 3/1000, hence V > 3sqrt(2)/500.

The equality J=3/1000 is excluded. The V-condition is necessary, not equivalent to the J-condition.

## Unresolved mathematical frontier

**M5-DIFFUSE** (J>3/1000), retaining all eight continuously varying true frames, 32 actual disk vertices and 28 actual SAT disjunctions, remains OPEN. The larger M5 gate remains OPEN. M6, M7, M8, the unrestricted R_8>=R_* theorem and global equality classification are NOT proved. The true seven-outer equality ring and slider freedoms must remain admitted.

No Lean compilation, CI, or PR merge is requested or claimed.

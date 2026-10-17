# Gate 3B.2 / M5-DIFFUSE: the full Jensen defect cannot be charged to the exterior ring

2026-10-13. **Exact orientation counterexample, not a packing counterexample.** This strengthens the earlier HIGH total-support no-go in `GATE3B_M5_HIGH_RING_BUDGET_AND_NO_GO.md`: even after subtracting the four-plus-four cut baseline and replacing total surplus E by the corrected Jensen defect J, there is no uniform positive ring correction depending only on J. The actual disk and central-square geometry remain decisive.

## Statement

Let `h=pi/4`, and use the exact folded M5-I word

    L H L H L H L L.

For ordered folded positions x, define the true pair widths w_ij, W=sum w_ij, `c=(sqrt(2)-1)/2`, `W0=28+15c`, barycentric cut weights `lambda_k=(x_k-x_(k-1))/h` for k=1..7, `lambda_8=(h-x_7)/h`, and

    J=W-W0-c*(lambda_1+lambda_3+lambda_5+lambda_7).

Prior strong concavity proves J>=0 and the complete reference certificate excludes `J<=3/1000` under the target disk ceiling.

**Theorem (no whole-J ring charge).** For every beta>0 there exist **actual strict M5 frame data** (maximum closed 45-degree window count exactly five), a distinguished removed frame indexed 4, and a seven-label cyclic order on the remaining frames for which

    J > 1/5

yet

    sum_(cyclic exterior pairs)(w_ij-1)
       < (sqrt(2)-1) + beta*J.

Consequently `J>3/1000` does NOT by itself imply a quantitative improvement over the sharp exterior ring bound for an arbitrary removed square and arbitrary cyclic order. This does not refute any theorem that ALSO uses the physical square centers or actual disk geometry.

## Explicit continuum, including M5 validity

For `0<epsilon<h/12`, take

    x=(0,epsilon,2epsilon,3epsilon,h/2,h-3epsilon,h-2epsilon,h-epsilon).

All folded positions are strictly increasing. Under the exhaustive bounded occupancy walk `LHLHLHLL`, these produce eight genuine maximum-five orientations `theta_i=x_i+h*1_(word_i=H)` modulo pi/2. In particular the M5 condition holds for every such positive epsilon; the argument is purely orientation-combinatorial and does not presume an eight-square packing.

Remove label 4, and take the cyclic order

    (0,2,5,1,3,6,7).

As epsilon tends to zero, the seven retained frames converge to three at phase zero (labels 0,2,5) and four at phase h (labels 1,3,6,7). Only two consecutive edges of the displayed cycle cross the two phases, so, by continuity of the exact true support widths,

    sum_ring(w_ij-1) -> 2*((sqrt(2)-1)/2)=sqrt(2)-1.   (R)

Meanwhile label 4 stays at `theta_4=h/2`, at a fixed positive angular distance from either group.

## The full Jensen defect stays large

The existing rigorous strong-concavity formula gives

    J >= (1/4)*sum_(i<j) (x_j-x_i)*(h-x_j+x_i).

For the seven pairs incident to label 4, every folded distance tends to h/2, and hence every corresponding summand tends to h²/4. Thus

    liminf_(epsilon->0) J >= (7/4)*(h²/4)
                             =7h²/16
                             > 63/256
                             > 1/5,

where `h=pi/4>3/4`. (The conservative bound 63/256 follows from 7*(3/4)^2/16=63/256.) Thus J>1/5 for all sufficiently small positive epsilon, whereas the ring correction beyond sqrt(2)-1 tends to zero by (R). Given any beta>0, choose epsilon small enough that the correction is <beta/5<beta*J. QED.

## Consequence: the precise physical split required

This counterexample demonstrates that the **single omitted square can carry an arbitrarily large proportion of the Jensen dispersion while the remaining seven frames approach a two-phase exterior ring**. It is not sound to try to prove M5-DIFFUSE impossible from a universal inequality of the form

    exterior marker sum >= 7*(7/8)+C*J

with any C>0 that depends only on M5 frame information. The physical relation between the omitted square and the outer seven must enter. The existing global central-square and exterior-marker theorems provide potential inputs but no completed such inequality.

One can make an **exact, exhaustive but not yet excludable split** for every fixed central label c by decomposing J into its 21 nonnegative exterior-exterior pair Jensen gaps plus seven nonnegative central-exterior pair gaps:

    J = J_exterior + J_center,
    J_exterior>=0, J_center>=0.

Thus `J>3/1000` implies `J_exterior>3/2000` OR `J_center>3/2000`. This dichotomy does not itself restrict the actual centers or prove a radius bound; the present example shows why `J_center` cannot be ignored when the exterior geometry is nearly two-frame.

**Gate status:** entire M5-DIFFUSE, M5, M6--M8, and unrestricted optimality remain OPEN. The conclusion is a falsification of a proposed shortcut, not an additional eliminated radius class. No Lean or CI.

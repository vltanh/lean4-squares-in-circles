# Seven rational projection orders: global owner pruning for M5-DIFFUSE

**2026-10-13. Complete hand theorem, not an exclusion of all M5-DIFFUSE.** This is a global-in-frames refinement of the four broad projected-center order graphs. Every packing under the research radius ceiling has seven simultaneously realized rational projection graphs, each with **no directed path of four edges**. It retains every actual square and every SAT-owner tie.

## 1. Exact rational directional fan

Define seven rational unit rays on the upper semicircle:

```
v0=(1,0)
v1=(77/85,36/85)
v2=(481/769,600/769)
v3=(9/41,40/41)
v4=(-9/41,40/41)
v5=(-481/769,600/769)
v6=(-77/85,36/85)
```

Complete the 14 rays by `v_(k+7)=-v_k` for `0<=k<=6`, indexed counterclockwise modulo 14. Their unit norms follow from the three Pythagorean identities `77²+36²=85²`, `481²+600²=769²` and `9²+40²=41²`.

Consecutive cross products, on either half-circle, are exactly

```
36/85, 28884/65365, 13840/31529, 720/1681,
13840/31529, 28884/65365, 36/85.
```

Every consecutive dot product is positive. Therefore the rays are in strict angular order, all consecutive gaps `φ` lie in `(0,π/2)`, and `0<sin φ<=28884/65365<9/20`. These are rational inequalities, not floating-point angle tests.

## 2. Every actual pair has a nearest rational owner ray

Let eight actual unit squares with pairwise disjoint open interiors lie in a disk of radius `R` with

```
R² <= Q=9789/2500 < (99/50)².
```

For each unordered pair `i<j` choose a **canonical** signed actual SAT axis `n` maximizing `n·d`, where `d=p_j-p_i`. The true nonoverlap SAT disjunction and the common pair-support width give

```
a=n·d >= w_ij >= 1,
b=(Jn)·d,     |b|<=a.
```

The perpendicular signed axes `±Jn` occur in the same real square frame, proving the last inequality even at owner ties.

Choose the nearest one of the 14 rational rays `v_k`, by **maximizing the rational dot product** `v_k·n`. Its angular deviation from `n` is `δ`, bounded by half an adjacent gap `φ`; hence `sin(2δ)<=sin φ<9/20`. Since `0<=δ<π/4`,

```
v_k·d >= (cos δ-sin δ)*a
      = sqrt(1-sin(2δ))*a
      > sqrt(11/20)*a
      > (37/50)*w_ij >= 37/50.                    (1)
```

The strict elementary root comparison is `11/20>1369/2500=(37/50)²`. All sign and nearest-ray ties may be retained.

For each `k=0,...,6`, put edge `i->j` in directed graph `G_k` if the nearest ray is `v_k`, and reverse it to `j->i` in `G_k` if the nearest ray is `v_(k+7)=-v_k`. Every one of the 28 unordered pairs appears exactly once across the seven graphs. Every resulting edge `a->b` satisfies

```
v_k·(p_b-p_a)>37/50.
```

All seven graphs are realized by the SAME eight centers, not independent sets of arbitrary inequalities.

## 3. No four-edge directed path

For any unit direction `v`, true whole-square containment gives

```
v·p_i<=R-H_i(v),   -v·p_i<=R-H_i(v),
H_i(v)=(|v·e_i|+|v·f_i|)/2>=1/2.
```

Thus every projected center span is bounded by

```
v·(p_b-p_a) <= 2R-1 < 2*(99/50)-1=74/25.
```

A four-edge path in some `G_k` would telescope (1) to a projected span strictly greater than `4*(37/50)=74/25`, contradiction. Therefore **every G_k is acyclic and has longest directed path at most THREE edges**. No frame alignment, central square, contact graph, or candidate pose is assumed.

## 4. A stronger center-free path-capacity inequality

For ANY directed canonical-owner path `i_0->...->i_m` and ANY unit reference direction `v` whose angular deviation `δ_r` from every directed owner normal is less than `π/4`, the same canonical argument and the TRUE endpoint support functions give

```
sum_(r=1)^m (cos δ_r-|sin δ_r|) w_(i_(r-1),i_r)
  + H_(i_0)(v)+H_(i_m)(v) <= 2R.                 (2)
```

This retains each actual pair width and both actual endpoint frames. It can reject three-edge paths that pass the uniform seven-order screen.

For example, if three successive directed canonical normals are all within `1/100` radian of the same `v`, then `cos δ-|sin δ|>=1-1/100-1/20000=19799/20000`. Using `w>=1` and `H>=1/2`, (2) would force

```
2R >= 1+3*(19799/20000) = 79397/20000 > 99/25,
```

contradicting `2R<99/25`. Thus **no three-edge owner path with all three normals in one 1/100-radian cone is possible** at the research radius ceiling.

## 5. Why this is a strict owner-graph refinement

Consider eight axis-parallel symbolic unit squares and a complete 28-pair selection of TRUE signed candidate SAT axes. For pairs `0<=i<j<=4`, choose positive horizontal; for all other pairs `i<j`, choose positive vertical. This center-unrestricted separator system is feasible at arbitrarily large disk radius, e.g. centers `p_i=(i,i)`; it has no center-free balanced-force contradiction.

The earlier four broad order graphs are acyclic, with longest path lengths respectively four and three, so they pass the old no-SIX-edge screen. The new `G_0` contains the four-edge path `0->1->2->3->4`, impossible under the disk ceiling. This proves a **genuine new whole-owner-word rejection**, not merely a different way of writing the earlier DAG statement. It is not claimed that this word escaped every other existing disk-specific test.

## 6. Regression and remaining gate

[verify_seven_rational_projection_orders.py](verify_seven_rational_projection_orders.py) uses only `Fraction` and checks all fourteen exact adjacent ray bounds; the symbolic strict-pruning example; all 32 true vertices, all 28 canonical signed SAT owners, and every seven-order path length for the previous genuine rational eight-square packing. The continuous theorem is the hand proof above, not the finite regression.

This reduction applies to ALL eight-square packings and thus directly to the still-open M5-DIFFUSE child `J>3/1000`. Its seven graphs, the previous four graphs, the strict Jensen defect, all 32 vertices and all true SAT inequalities must remain jointly imposed. It **does not exclude all M5-DIFFUSE**, pass M5 or M6--M8, or establish the unrestricted `R_8>=R_*`. Preserve the known equality ring and sliders.

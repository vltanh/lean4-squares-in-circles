# The sharp-row guard covers the aligned D821 boundary family with B and H free

November 4, 2026. This is a complete proof for the explicitly specified aligned
boundary family and its shared sharp-row guard. It earns **zero original-cell
closures and zero mask closures**. The current fixed register remains
**208 CLOSED / 23 OPEN**, and the mask ledger remains **8 CLOSED / 24 OPEN**.
No whole-original classification, caller-ancestry replay or equality
classification is inferred from this family theorem.

The root repeated the compact independent exact replay from a relocated
packet: all 15 frozen inputs, 150 rational criterion checks, every original
pair separator and all 36 corner implications passed. The continuous
necessity and sufficiency argument and a separate independent hand review
are included. No human or proof-kernel verification is claimed; no Lean,
Lake or CI was run.

[Source-bound packet and root replay](computer_assisted/a2_00100_two_free_boundary_manifest.json) ·
[Accepted shared sharp-boundary theorem](A2_00100_SHARED_SHARP_BOUNDARY_TERMINALS.md) ·
[Current complete original-cell proof](A2_00100_B61_FIXED_CENTER_BOUND_PSD_CLOSURE.md)

This is a theorem about a specified family of physical boundary controls. It is not a proof that every configuration in the unchanged D821 original cell belongs to that family. It gives no original-cell or mask closure credit.

Write `Q = 1105/256`. All nine squares in this section are axis-aligned unit squares with disjoint interiors, contained in the closed disk of squared radius Q. Keep these seven centers fixed:

| Original | Center |
| --- | --- |
| A | (-3/2, -1/16) |
| C | (1/2, -17/16) |
| D | (3/2, -1/16) |
| E | (-1, 15/16) |
| F | (0, 15/16) |
| G | (1, 15/16) |
| I | (1/2, -1/16) |

Allow B and H to move. Retain the original actual AB and BC horizontal gaps and their center cones. In aligned coordinates these give

`x_B - x_A >= 1`, `x_C - x_B >= 1`, and
`|y_B-y_A| <= x_B-x_A`, `|y_C-y_B| <= x_C-x_B`.

Also retain `x_H <= x_I` and `y_H <= y_B`. These two inequalities hold in the independently replayed D821 ancestor; the later whole-original bound pilot only strengthens them.

## Exact description of the family

Every such configuration has the form

`B = (-1/2, -1/16-t)`,

`H = (-1/2-u, -17/16-s)`,

where

`u >= 0`, `0 <= t <= s`, and

`R(u,s) := u^2 + 2u + s^2 + (25/8)s - 7/8 <= 0`.

Conversely, every triple with these properties gives disjoint aligned squares in the closed Q disk and satisfies the listed center cones and gaps. The fixed C–D gap is exactly 1, so every member is on the boundary where the original strictly weak C–D predicate fails.

### Proof of necessity, including equality cases

The two actual horizontal gaps force `x_B=-1/2`. The BC center cone then gives `y_B <= -1/16`.

First suppose `x_H > -1/2`. Because `x_H <= x_I=1/2`, the horizontal center distance from H to C is strictly less than 1. Aligned nonoverlap with C forces either `y_H <= -33/16` or `y_H >= -1/16`. The first alternative is impossible: H has a corner with vertical coordinate at most `-41/16`, whose squared norm is already at least `1681/256 > Q`. In the second alternative, `y_H <= y_B <= -1/16` forces both heights to equal `-1/16`. Nonoverlap with B then forces `x_H=1/2`, making H coincide with I, also impossible. Thus `x_H <= -1/2`.

Next suppose `x_H <= -3/2`. Since `y_H <= -1/16`, H's lower left corner has squared norm at least

`2^2 + (9/16)^2 = Q`.

Containment in the closed disk forces equality in both coordinates, hence H coincides with A. Therefore `x_H > -3/2`.

We now have `-3/2 < x_H <= -1/2 = x_B`, so the horizontal B–H distance is strictly less than 1. Their nonoverlap and the retained height order give `y_H <= y_B-1`. Define `t=-1/16-y_B`, `u=-1/2-x_H`, and `s=-17/16-y_H`. These satisfy `u>=0` and `0<=t<=s`.

The lower left H corner is `(-1-u,-25/16-s)`. Its circle constraint is exactly

`(1+u)^2 + (25/16+s)^2 <= Q`,

which expands to `R(u,s)<=0`.

### Proof of sufficiency

The exact inequality below implies `0<=t<=s<53/200<1`. Hence AB and BC have horizontal gap 1 and their height differences, respectively `-t` and `-1+t`, satisfy both original center cones. EF and FG remain actual with horizontal gap 1 and height difference zero.

H is vertically separated from A by `1+s`, from B by `1+s-t`, and from E, F, G by `2+s`. It is horizontally separated from C and I by `1+u`, and from D by `2+u`. B is horizontally separated from A, C, D, G, I and vertically separated from E, F by at least 1. The remaining pairs are the fixed seven-square controls.

The lower left H corner is its farthest corner, and its squared norm is `Q+R(u,s)<=Q`. B's farthest corner has squared norm `1+(9/16+t)^2`, which is at most `1+(25/16+s)^2`, and therefore at most H's farthest squared norm. Every fixed square's corners already lie in the Q disk. This proves sufficiency without sampling.

## Uniform inclusion in the accepted sharp-row guard

Set `r=53/200`. The following is an exact polynomial identity:

`R(u,s) = u^2 + 2u + (s-r)(s+r+25/8) + 467/20000`.

If `u>=0` and `s>=r`, its right side is strictly positive. Therefore `R<=0` implies `s<53/200` and consequently

`U_ABID = |y_B-y_A| + |y_I-y_B| + |y_D-y_I| = 2t < 53/100`.

The ABID horizontal gaps are all 1, the shoulder heights `y_E-y_A` and `y_G-y_D` are both 1, and every selected frame has beta equal to zero. Thus every member lies strictly within the variation bound of the previously accepted sharp-row terminal with `b=1/200`, `U=53/100`. That terminal also applies to a neighborhood in which these inequalities and the small-frame bounds continue to hold. Its exact criterion and equality argument are recorded in `SHARED_ABID_STRICT_BOUNDARY_TERMINAL.md` and `SHARED_ABID_STRICT_TERMINAL_CHECK.json`.

The familiar downward slider is the subfamily `u=0`, `t=s`, with

`0 <= t <= (sqrt(849)-25)/16`.

The original base control is `u=s=t=0`. The proof above additionally allows H to move left and to move down independently of B. In particular, coverage does not rely on the two moving centers having the same vertical displacement.

## D821 caller audit and limits

`verify_cd_whole_open_bounds.py` independently replayed the unchanged v3 ancestor, its zero-round diagonal identity wrapper, and all three additional whole-original bound rounds: 458 new deductions and 1,034 printed rows. The result is an OPEN certified whole-original state, not a closure.

`check_cd_aligned_slider_family.py` checks the entire known downward-slider interval using exact arithmetic in Q(sqrt(849)): original and propagated coordinate bounds, inherited Cartesian and diagonal bounds, the original affine rows, every corner, and all 36 pair separations. Affine expressions are checked at both endpoints; corner squared norms are convex quadratics. The exact report also records the whole-state sharp-guard failures, so a successful audit of the controls cannot be confused with implication of the guard on the whole original cell.

The B/H-swapped base control has `y_H-y_B=1` and violates D821's certified nonpositive upper bound for that difference. More generally, any label-swapped member of the displayed family has `y_H-y_B=1+s-t>=1` and fails the same bound. The unswapped base and full slider are the known Q controls that survive this D821 predicate, and both are covered by the ABID guard. No exhaustive classification of all Q configurations in D821 is claimed.


## Reconstruct the compact exact packet

From `research/nine/computer_assisted`, verify the archive hash recorded in
the manifest, then run:

```sh
tar -xzf a2_00100_two_free_boundary_checkpoint.tar.gz
cd two_free_boundary_package
python -B -S verify_all.py
```

The immutable hand proofs, both independent arithmetic scripts, all original
source bindings and the fresh report are included. The replay checks this
explicit family and the conditional guard. It does not infer a whole-original
premise from numerical controls.

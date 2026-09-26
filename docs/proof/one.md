# One square

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 1.** Let $R_1 = \frac{\sqrt2}2$.

1. The square $Q(0, 0)$ lies in the closed disk of radius $R_1$ about the
   origin.
2. A unit square in a closed disk of radius $R$ forces $R \ge R_1$.
3. The packings of one unit square in a closed disk of radius $R_1$ are
   exactly the configurations with the normal form of $(0, 0)$: the square is
   centred at the disk centre.

![One unit square centred at the disk centre o, its four vertices on the dashed circle of radius root 2 over 2](figures/one.svg)

*One square. Its vertices lie on the circle of radius $R_1$ about its centre.*

*Sketch.* Some vertex of the square is at least half a diagonal from the disk
centre, with equality only when the square is centred there. So in the disk of
radius $R_1$ the square is centred at the disk centre. In a smaller disk it
would be centred there too, and its vertices would lie outside.

*Lean: [`One.model_packing`](../../SquaresInCircles/One/Construction.lean#L25),
[`One.uniqueness`](../../SquaresInCircles/One/Uniqueness.lean#L23),
[`One.optimum`](../../SquaresInCircles/One/Uniqueness.lean#L38), in
[`SquaresInCircles/One/`](../../SquaresInCircles/One).*

## Construction

### Proposition 1.1 (attainment)

$\overline{Q(0, 0)}$ lies in the closed disk of radius $\frac{\sqrt2}2$ about
the origin.

*Proof.* The square lies in $[-\frac12, \frac12]^2$, and
$\frac14 + \frac14 = \frac12$; apply
[Lemma 17](common.md#lemma-17-axis-parallel-squares). $\square$

*Lean: [`One.model_packing`](../../SquaresInCircles/One/Construction.lean#L25),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## Uniqueness

### Proposition 1.2 (uniqueness)

If a unit square $S$ lies in the closed disk of radius $\frac{\sqrt2}2$ about
$o$, then $c_S = o$, and the packing has the normal form of $(0, 0)$.

*Proof.* By [Lemma 1](common.md#lemma-1-farthest-vertex), and since
$a_S, b_S \ge 0$,

```math
\tfrac12 = R_1^2 \ge \varphi(a_S, b_S) = \tfrac12 + a_S + b_S + a_S^2 + b_S^2 \ge \tfrac12 + a_S + b_S \ge \tfrac12 ,
```

so $a_S = b_S = 0$, and by Lemma 1 $|c_S - o|^2 = a_S^2 + b_S^2 = 0$. Take a
chart of $S$ ([Lemma 10](common.md#lemma-10-charts)). By
[Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart), $S$ sits at
$(a_S, \varepsilon_S b_S) = (0, 0)$ in the frame $\theta_S$, and
[Lemma 19](common.md#lemma-19-from-slots-to-a-normal-form) gives the normal
form. $\square$

*Lean: [`One.uniqueness`](../../SquaresInCircles/One/Uniqueness.lean#L23),
[`One.half_add_le_phi`](../../SquaresInCircles/One/Uniqueness.lean#L18),
[`square_chart`](../../SquaresInCircles/Common/Charts.lean#L133),
[`chart_phi`](../../SquaresInCircles/Common/Charts.lean#L76),
[`chart_represents`](../../SquaresInCircles/Common/NormalForm.lean#L148),
[`normal_form_of_slots`](../../SquaresInCircles/Common/NormalForm.lean#L96).*

Proposition 1.1 and [Lemma 21](common.md#lemma-21-normal-forms-of-a-packing)
give the converse: every configuration with this normal form is a packing in
the closed disk of radius $R_1$.

## Lower bound

*Proof of Theorem 1 (2).* The vertex $(\frac12, \frac12)$ of
$\overline{Q(0, 0)}$ lies on the circle of radius $R_1$ about the origin, since
$\frac14 + \frac14 = \frac12$. By Proposition 1.2 every packing in the closed
disk of radius $R_1$ has the normal form of $(0, 0)$, so
[Lemma 22](common.md#lemma-22-the-lower-bound) gives
$R \ge R_1$. $\square$

*Lean: [`One.optimum`](../../SquaresInCircles/One/Uniqueness.lean#L38),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48).*
# Two squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 2.** Let $R_2 = \frac{\sqrt5}2$.

1. The squares $Q(-\frac12, 0)$ and $Q(\frac12, 0)$ form a packing in the
   closed disk of radius $R_2$ about the origin.
2. A packing of two unit squares in a closed disk of radius $R$ forces
   $R \ge R_2$.
3. The packings of two unit squares in a closed disk of radius $R_2$ are
   exactly the configurations with the normal form of
   $(-\frac12, 0), (\frac12, 0)$: the squares form a $2 \times 1$ rectangle
   centred at the disk centre.

![Two unit squares side by side forming a 2 by 1 rectangle centred at o, with its four corners on the dashed circle of radius root 5 over 2](figures/two.svg)

*Two squares. The corners of the $2 \times 1$ rectangle lie on the circle of
radius $R_2$.*

*Sketch.* In the disk of radius $R_2$, the farthest-vertex bound keeps both
centres within $\frac12$ of the disk centre, while centres of disjoint unit
squares are at least 1 apart. So both centres are exactly $\frac12$ from the
disk centre, and each square is centred $\frac12$ from it along one of its
axes. Then each square holds a half of a small circle about the disk centre,
the two halves are opposite, and the squares form the rectangle. A packing in
a smaller disk would be the rectangle too, whose corners reach the circle of
radius $R_2$.

*Lean: [`Two.model_packing`](../../SquaresInCircles/Two/Construction.lean#L26),
[`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L47),
[`Two.optimum`](../../SquaresInCircles/Two/Uniqueness.lean#L76), in
[`SquaresInCircles/Two/`](../../SquaresInCircles/Two).*

## Construction

### Proposition 2.1 (attainment)

$Q(-\frac12, 0)$ and $Q(\frac12, 0)$ are disjoint and lie in the closed disk
of radius $\frac{\sqrt5}2$ about the origin.

*Proof.* The centres differ by 1 in the first coordinate, and both squares lie
in $[-1, 1] \times [-\frac12, \frac12]$, with $1 + \frac14 = \frac54$. Apply
[Lemma 17](common.md#lemma-17-axis-parallel-squares). $\square$

*Lean: [`Two.model_packing`](../../SquaresInCircles/Two/Construction.lean#L26),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## Uniqueness

### Lemma 2.2 (centres near the disk centre)

If $a, b \ge 0$ and $\varphi(a, b) \le \frac54$, then $a^2 + b^2 \le \frac14$.

*Proof.* Expanding,

```math
\varphi(a, b) = (a^2 + b^2) + (a + b) + \tfrac12 .
```

If $a^2 + b^2 > \frac14$, then $(a + b)^2 \ge a^2 + b^2 > \frac14$, so
$a + b > \frac12$ and $\varphi(a, b) > \frac14 + \frac12 + \frac12 = \frac54$.
$\square$

*Lean: [`Two.center_near`](../../SquaresInCircles/Two/Uniqueness.lean#L22).*

### Lemma 2.3 (both centres at distance one half)

Let $S$ and $T$ be disjoint unit squares with $\varphi(a_S, b_S) \le \frac54$
and $\varphi(a_T, b_T) \le \frac54$. Then
$a_S^2 + b_S^2 = a_T^2 + b_T^2 = \frac14$: both centres are exactly $\frac12$
from $o$.

![Two centres c_S and c_T inside the dashed disk of radius one half about o, the parallelogram with vertices o, c_S, c_S plus c_T minus o, and c_T, and its two diagonals](figures/parallelogram.svg)

*The parallelogram spanned by $c_S - o$ and $c_T - o$. Its squared diagonals add
up to twice the squared sides from $o$, so if both centres are within $\frac12$
of $o$, the diagonal from $c_S$ to $c_T$ is at most 1.*

*Proof.* By [Lemma 1](common.md#lemma-1-farthest-vertex) and Lemma 2.2,
$|c_S - o|^2 = a_S^2 + b_S^2 \le \frac14$, and the same for $T$. The
parallelogram law gives

```math
|c_S - c_T|^2 + |c_S + c_T - 2o|^2 = 2|c_S - o|^2 + 2|c_T - o|^2 \le 1 ,
```

while $|c_S - c_T| \ge 1$ by
[Lemma 4](common.md#lemma-4-centres-at-least-1-apart). So equality holds
throughout, and $|c_S - o|^2 = |c_T - o|^2 = \frac14$. $\square$

*Lean: [`Two.centers_at_half`](../../SquaresInCircles/Two/Uniqueness.lean#L36),
[`Two.normSq_parallelogram`](../../SquaresInCircles/Two/Uniqueness.lean#L28),
[`local_center_norm`](../../SquaresInCircles/Common/Basic.lean#L95),
[`centers_distance_sq_ge_one`](../../SquaresInCircles/Common/Contacts.lean#L74).*

### Proposition 2.4 (uniqueness)

If two disjoint unit squares lie in the closed disk of radius
$\frac{\sqrt5}2$ about $o$, the packing has the normal form of
$(-\frac12, 0), (\frac12, 0)$.

*Proof.* Call the squares $S$ and $T$, and take a chart of each
([Lemma 10](common.md#lemma-10-charts)).

1. *Each square is centred at $(\frac12, 0)$ in its chart.* By Lemma 1,
   $\varphi(a_S, b_S)$ and $\varphi(a_T, b_T)$ are at most $\frac54$, so by
   Lemma 2.3 $a_S^2 + b_S^2 = \frac14$. Then
   $\varphi(a_S, b_S) = \frac34 + a_S + b_S \le \frac54$ gives
   $a_S + b_S \le \frac12$, while $(a_S + b_S)^2 \ge a_S^2 + b_S^2 = \frac14$
   gives $a_S + b_S \ge \frac12$. So $a_S b_S = 0$, and since $a_S \ge b_S$,
   $(a_S, b_S) = (\frac12, 0)$. The same holds for $T$.
2. *Each square holds a half circle.* By
   [Lemma 12](common.md#lemma-12-arcs-of-an-exterior-square) (3) with
   $r = \frac12$, $S$ holds the half of $\Gamma_{1/2}$ centred at its phase
   $\theta_S$, and $T$ the half centred at $\theta_T$.
3. *The half circles are opposite.* They are disjoint, so
   $\theta_T = \theta_S + \pi$
   ([Lemma 8](common.md#lemma-8-disjoint-arcs-have-separated-centres)).
4. *The rectangle.* By
   [Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart), $S$ sits at
   $(\frac12, 0)$ in the frame $\theta_S$, and $T$ at $(\frac12, 0)$ in the
   frame $\theta_S + \pi$. Two quarter turns
   ([Lemma 18](common.md#lemma-18-sitting-at-a-centre) (2)) put $T$ at
   $(-\frac12, 0)$ in the frame $\theta_S$.
   [Lemma 19](common.md#lemma-19-from-slots-to-a-normal-form) gives the normal
   form. $\square$

*Lean: [`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L47),
[`sorted_square_chart`](../../SquaresInCircles/Common/Charts.lean#L146),
[`chart_phi`](../../SquaresInCircles/Common/Charts.lean#L76),
[`SquareChart.half_arc`](../../SquaresInCircles/Common/Charts.lean#L193),
[`OpenArc.opposite`](../../SquaresInCircles/Common/Angles.lean#L31),
[`chart_represents`](../../SquaresInCircles/Common/NormalForm.lean#L148),
[`represents_quarter`](../../SquaresInCircles/Common/Angles.lean#L78),
[`normal_form_of_slots`](../../SquaresInCircles/Common/NormalForm.lean#L96).*

Proposition 2.1 and [Lemma 21](common.md#lemma-21-normal-forms-of-a-packing)
give the converse: every configuration with this normal form is a packing in
the closed disk of radius $R_2$.

## Lower bound

*Proof of Theorem 2 (2).* The corner $(1, \frac12)$ of
$\overline{Q(\frac12, 0)}$ lies on the circle of radius $R_2$ about the origin,
since $1 + \frac14 = \frac54$. By Proposition 2.4 every packing in the closed
disk of radius $R_2$ has the normal form of $(-\frac12, 0), (\frac12, 0)$, so
[Lemma 22](common.md#lemma-22-the-lower-bound) gives
$R \ge R_2$. $\square$

*Lean: [`Two.optimum`](../../SquaresInCircles/Two/Uniqueness.lean#L76),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48).*
# Exact seven-row contradiction for two unchanged original parents

**Independently verified:** the terminal rows of `positive-033850931bb6d4ef` and `positive-3cd9c2a7981effa2` are the same seven physical inequalities, with the row-index shifts listed below. Their previously verified original-parent bound inductions remain premises of this short final table. The final combination itself requires no residual estimate.

Use these exact constants:

\[
\begin{aligned}
p&=\frac{108567}{1048576},&
q&=\frac{30302249}{15728640},&
s&=\frac{3837595}{14680064},\\
b&=\frac{15744129381223}{8246337208320},&
u&=\frac{641539}{1048576},&
v&=\frac{3123169}{1048576},\\
w&=\frac{1026017}{1048576},&
r&=\frac{35179895843}{17179869184},&
\delta&=\frac{11}{30}.
\end{aligned}
\]

Define the positive rational multipliers

\[
\alpha=1-s=\frac{10842469}{14680064}>0,
\qquad
\beta=\frac qp-2+s
=\frac{403275382060771}{23906557624320}>0.
\]

All other multipliers are `1` or `1/p`; hence all seven are strictly positive.

## Coefficient table

Each row means the displayed linear combination of the eight coordinates is at most the displayed right side. The physical A–H–I strip row contains only endpoint coordinates after applying its already proved guard; original **H remains essential to that physical theorem**.

| Row | \(x_A\) | \(y_A\) | \(x_C\) | \(y_C\) | \(x_D\) | \(y_D\) | \(x_I\) | \(y_I\) | Right side | Multiplier |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| C–D cone | 0 | 0 | 1 | −1 | −1 | 1 | 0 | 0 | 0 | 1 |
| C–I center-distance secant | 0 | 0 | \(-p\) | \(q\) | 0 | 0 | \(p\) | \(-q\) | \(-b\) | \(1/p\) |
| Inward predecessor | 0 | −1 | 0 | 0 | 0 | −1 | 0 | 2 | \(\delta\) | 1 |
| Proved A–C vertical bound | 0 | 1 | 0 | −1 | 0 | 0 | 0 | 0 | \(u\) | \(\alpha\) |
| Proved A–D horizontal bound | −1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | \(v\) | 1 |
| Proved C–I vertical bound | 0 | 0 | 0 | −1 | 0 | 0 | 0 | 1 | \(w\) | \(\beta\) |
| Physical A–H–I strip | 1 | \(s\) | 0 | 0 | 0 | 0 | −1 | \(-s\) | \(-r\) | 1 |
| **Weighted sum** | **0** | **0** | **0** | **0** | **0** | **0** | **0** | **0** | **\(-K\)** | |

The coordinate cancellations are explicit:

\[
\begin{array}{c|l}
x_A&-1+1=0\\
y_A&-1+\alpha+s=0\\
x_C&1-p/p=0\\
y_C&-1+q/p-\alpha-\beta=0\\
x_D&-1+1=0\\
y_D&1-1=0\\
x_I&p/p-1=0\\
y_I&-q/p+2+\beta-s=0.
\end{array}
\]

The exact weighted right side is

\[
-\frac bp+\delta+\alpha u+v+\beta w-r
=-\frac{2315620317940810579}{12533921283739484160}
=-K<0.
\]

Thus the seven necessary inequalities imply

\[
\boxed{0\le-K<0,}
\]

which is impossible. The positive reserve `K` is approximately `0.1847482735466763`.

## Binding to the two certificates

| Physical row | Index in positive-033850931bb6d4ef | Index in positive-3cd9c2a7981effa2 |
| --- | ---: | ---: |
| C–D cone | 1698 | 1698 |
| C–I center-distance secant | 2256 | 2256 |
| Inward predecessor | 7784 | 7784 |
| A–C vertical bound | 9603 | 9604 |
| A–D horizontal bound | 9604 | 9605 |
| C–I vertical bound | 9678 | 9679 |
| A–H–I strip | 13135 | 13136 |

The independent check compares names, all rational coefficients, and right sides across the two certificates. It regenerates the second parent's seven rows from the accepted physical V14 collector and independently reconstructed new strip formulas after a fresh complete replay of its 76 inherited and 580 new deductions. Every coefficient sum is exactly zero over the rationals.

`computer_assisted/shared_capacity_seven_row_independent.json` contains the fully expanded eight-coordinate table and source hashes. Reproduce the check with:

```sh
python computer_assisted/check_shared_capacity_hand_tables.py <portable-archive.tar.gz>
```

## Reusable algebraic form

For any physically justified seven rows of the table's form, it suffices to prove

\[
p>0,\qquad 0\le s\le1,\qquad q/p\ge2-s,
\]

and

\[
-b/p+\delta+(1-s)u+v+(q/p-2+s)w-r<0.
\]

The same nonnegative combination then gives a contradiction. This separates the reusable eight-coordinate cancellation from the original-parent interval work needed to supply its constants.

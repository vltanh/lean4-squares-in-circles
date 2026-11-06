# An interval terminal for an already selected separator

Retain two original, independently oriented physical unit squares P,T,
their proved center boxes, and a selected physical separating side axis
owned by O, where O is P or T. Write
u_O=(alpha_O,beta_O), v_O=(-beta_O,alpha_O), with alpha_O>0.
Let R^->=1 be a proved common lower support threshold for this original
pair, and let alpha_O<=a^+ and beta_O/alpha_O lie in [s^-,s^+].
The rational endpoint formulas for these bounds are given in
[the frame-coupled pair chapter](FRAME_COUPLED_PAIR_ROWS.md) and
Section 3 of [the finite-table row chapter](CB882_WHOLE_DOMAIN.md).

For the selected sign sigma in {-1,1}, let X and Y be proved closed
intervals containing sigma(x_T-x_P) and sigma(y_T-y_P), respectively.
For any two closed intervals J,K, put

\[
 M(J,K)=\max\{jk:j\text{ is an endpoint of }J,
                         \ k\text{ is an endpoint of }K\}.
\]

A bilinear product on a rectangle attains its maximum at a corner.
For an interval X=[l,u], its negative is -X=[-u,-l].
Thus the following are necessary inequalities for the two selected axes:

\[
\begin{array}{c|c}
\text{Selected axis}&\text{Necessary interval inequality}\\ \hline
\sigma u_O& \max X+M([s^-,s^+],Y)\ \ge R^-/a^+\\
\sigma v_O& \max Y+M([s^-,s^+],-X)\ \ge R^-/a^+.
\end{array}                                                   \tag{1}
\]

Indeed, divide the actual selected separator inequality by alpha_O.
Its right side is at least R^-/alpha_O>=R^-/a^+, while its left side
is bounded above by the corresponding expression in (1). This proof
retains the original owner, signed side axis, and original frame.

There is an analogous direct rule for a selected coordinate separator
of the original contained insets. If their halfwidth lower bounds are
g_P^-,g_T^-, the maximum of the selected signed center-coordinate gap
must be at least g_P^-+g_T^-.

Consequently a cell is empty whenever one of these rational upper
bounds is strictly smaller than its rational threshold. A table using
this rule records the selected separator, the upper bound, and the
threshold; threshold minus upper bound is a strictly positive reserve. An endpoint
equality does not close a cell. All boxes used here must already have
been proved for the entire cell.

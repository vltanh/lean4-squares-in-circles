# The two left main frames have tangent magnitude below 7/40

This is a hand lemma for the original fixed mask `001/00`, at every
`R^2 <= Q = 1105/256`. It does not use a transverse-gap assumption, an
unselected square, or an equality classification. It strengthens the
computer-assisted bulk search without replacing any original square.

Use the canonical original frame
`u_i=(alpha_i,beta_i)`, with `alpha_i>=|beta_i|`, and write

\[
h_i=\frac{\alpha_i+|\beta_i|}{2},\qquad
g_i=\frac1{4h_i},\qquad t_i=\frac{\beta_i}{\alpha_i}.
\]

The actual A,B and B,C links and the original C,D cone inset give

\[
x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D.
\]

Original corner containment gives `x_D+h_D<=R` and `x_A-h_A>=-R`.
Consequently

\[
2R\ge 2h_A+2h_B+(h_C+g_C)+(h_D+g_D)
     \ge 2h_A+2h_B+2.
\]

Here `h+g>=1` follows from `h>=1/2` and
`h+1/(4h)-1=(2h-1)^2/(4h)>=0`. Therefore

\[
h_A+h_B\le R-1,\qquad
h_A,h_B\le R-\frac32<\frac{37}{64},
\]

because `(133/64)^2-Q=9/4096>0` and `R<133/64`.

For `0<=t<=1`, the folded half-width

\[
h(t)=\frac{1+t}{2\sqrt{1+t^2}}
\]

is increasing, since its derivative is
`(1-t)/(2(1+t^2)^(3/2))>=0`. At the proposed cutoff,

\[
h(7/40)=\frac{47}{2\sqrt{1649}}>\frac{37}{64},
\]

as both sides are positive and the squared comparison is

\[
1504^2-37^2\,1649=4535>0.
\]

Thus both original frames satisfy

\[
\boxed{|t_A|<7/40,\qquad |t_B|<7/40.}
\]

The simultaneous reversal maps this statement to the corresponding two
actual-link main frames for `100/00`.

## Use in an exact table

Every search node still records its full original split path. For leaves
marked `context_version: left_angles_7_40_v1`, the producer and independent
verifier intersect the A and B tangent intervals with `[-7/40,7/40]`
before constructing their necessary inequalities. An empty intersection
is an explicit terminal by the lemma above. Leaves without that version
retain their earlier interval reconstruction; their weights are not
silently applied to changed McCormick coefficients.

This interval restriction is an accepted necessary consequence, not a
claim that the remaining full-nine bulk has been excluded. The scalar
arithmetic is reproduced by
`computer_assisted/weak_outer_numeric_left_angle_arithmetic.py`.

# Independent review: mixed-01 gap monotonicities

Date: October 26, 2026.

**Verdict: PASS for all three whole-domain monotonicity lemmas.** This
review covers the saved source `SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md`
and its join to the original necessary conditions in
`SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md`. The source correctly leaves
the directional tradeoff-boundary inequality open. This review does
not infer that remaining sign or close the complete contact orbit.

## 1. Original normalization and pointwise Cauchy elimination

The numerator in (2) has the correct two outgoing shared supports and
the correct nonshared bit-zero norm, with coefficient 2 on \(q^2\).
The force normalization is by the original positive \(\mu_0\),
and all actual means, masks, and physical units remain those of the
accepted closure source.

The tangent support bound, the triangle inequality for the two
displayed planar vectors, and Cauchy with \((w,v)\) of norm
\(2K\) produce (4) pointwise for every original \(q>0\).
No optimum in \(q\) or replacement force triangle is introduced.
The range of \(w\) makes \(v>0\) on the entire closed angular
enlargement.

## 2. Necessary angular consequences

The accepted closure source supplies \(p>1+1/\sqrt2\),
\(c_0+c_1\le1\), and \(h_1>L(c_0)\). The derivation of
\(c_0>3/10\) moves positive terms before squaring, and its squared
reserve is exactly \(182r-128>3461/5000>0\).

For fixed \(\alpha_0+\alpha_1\), the sine-sum minimum is
indeed attained at one angle equal to \(\pi/4\). Its endpoint
value is \(r(1+s_2-c_2)\). This proves the necessary upper
bound on \(s_2-c_2\), and the stated radical chain then proves
\(c_2>7/15\). The squared reserve \(7/256\) for
\(\sqrt{11}>53/16\), and the difference \(1/420\), are correct.

## 3. Decrease with the first angle

I differentiated (3) independently. With \(A=s_0-c_0\),
\(w'=A\), \(v'=-wA/v\), and the opposite derivative of
\(\theta_2\), the two differentiated support terms are exactly

\[
 \partial_{\theta_0}U_0
 =\frac{(v-A)(ws_0-vc_0)}{2v},\qquad
 \partial_{\theta_0}U_2
 =-\frac{(v+A)(ws_2-vc_2)}{2v}.
\]

Thus (8) is exact. The positive factor in \(V\) follows from
\(w>v\), \(s_2\ge r\), and \(c_2\le r\).
The two uniform estimates in (9) follow from their stated positive
rational reserves. In the case \(U>0\), the fraction comparison
in (10) has the correct monotonic direction, and the final quadratic
has negative discriminant \(153/4-28\sqrt2<0\). Therefore
\(\partial_{\theta_0}G<0\) for every \(p\ge3/2\), without
needing the additional closure restrictions.

## 4. Increase with the force ratio

The function \(\mathcal U(w,e)\) is concave in either coordinate
when the other is fixed. Applying the two one-dimensional chord
inequalities successively proves the lower bound by its four
rectangle corners; no joint-concavity claim is needed. All rectangle
endpoints lie in the real radical domain. The bounds at \(w=17/5\)
and \(w=23/6\) have the correct strict signs and yield the three
stated rational values, each greater than \(13/10\).

The ratio \((p+c)/\sqrt{p^2+2pc+1}\) increases with \(c\),
and \(p/\sqrt{p^2+1}\) increases with \(p\). These facts and
the reserve \(17/1600\) give the strict \(17/10\) lower bound
on the first differentiated term. Thus \(\partial_pG>0\)
throughout the claimed necessary domain.

## 5. Decrease with the second angle

The bound \(c_0>3/10\) implies the displayed \(w>11/3\)
with rational reserve \(47/99000\), hence \(v<3/2\) and
\(J_2>91/60>3/2\). Independent differentiation gives exactly
(17), including the negative sign from the changing third angle.

On the lower force interval, the strict radical comparison and the
concave quadratic with endpoint values \(1/64\) and \(73/256\)
give the claimed upper bound \(3p/4\). On the upper interval,
the squared reserve \(3/320\) gives the same bound. The two
intervals cover every \(p\ge1+r\), with their common endpoint
included. The resulting strict derivative sign is therefore global.

All displayed rational reserves were independently reconstructed with
exact fractions. The recovered values include
\(211159/3920400\), \(1191/13600\), \(17/400\),
\(1/180\), \(17/1600\), \(47/99000\),
\(2141/158400\), \(1/64\), \(73/256\), and \(3/320\),
exactly as stated.

## 6. Scope of the accepted reduction

The three monotonicities hold on their stated entire domains and
retain every original positive force and shared-mean endpoint allowed
by closure. The manuscript correctly warns that both independent
angles cannot be increased through the necessary tradeoff
\(c_0+c_1\le1\). A boundary derivative or another whole-boundary
inequality remains necessary before these lemmas give a full scalar
exclusion. No such missing inference is assumed here.

No force-ratio mesh, coefficient packet, numerical proof premise,
Lean compilation, CI, or workflow dispatch was used in this review.

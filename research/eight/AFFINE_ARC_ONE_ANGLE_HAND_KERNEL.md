# A one-angle hand kernel for affine boundary-pair inequalities

## Scope

This note generalizes the independently reviewed scalar method used to
exclude the wrong quarter word 0010111. It treats both boundary kinds,
any fixed tangent subarc, all four forward separating axes, and frame
increments on either side of zero or a quarter turn.

The conclusion is a method for proving specified continuous pair
inequalities by fixed one-variable polynomial identities. A particular
candidate exclusion additionally needs its exact labels, its full table
of scalar regimes, a complete closed-domain union and a cyclic reserve.
No such exclusion is asserted merely because this kernel is available.

The companion `verify_affine_arc_hand.js` performs rational coefficient
arithmetic on a supplied fixed table. It does not optimize a multiplier,
search for a state, or subdivide a domain. Numerical discovery programs
are separate from its mathematical premises.

## 1. The two boundary curves and their supports

Let \(u\in[0,1]\) be the unsigned canonical tangent, and write the
center in its canonical frame as \((a,-\sigma b)\), where
\(b=ua\) and \(\sigma\in\{-1,1\}\).

For an outer state at squared radius Q,

\[
 (a+1/2)^2+(b+1/2)^2=Q.
\tag{1}
\]

For a core boundary state, the side is \(a=7/12\),
\(0\le u\le6/7\); the corner is

\[
 (a-1/2)^2+(b-1/2)^2=1/144,
 \qquad 6/7\le u\le1.
\tag{2}
\]

Each fixed arc is split at the core side/corner junction. Its endpoints
are specified by exact rational tangents, and its affine label is

\[
 L(a,b)=c+pa+qb.
\tag{3}
\]

On a circular piece write

\[
 a(b)=v+\sqrt{\rho^2-(b-v)^2},\qquad
 r(b)=\frac{b-v}{a-v}.
\tag{4}
\]

The outer parameters are \((v,\rho)=(-1/2,\sqrt Q)\), and the core
corner parameters are \((1/2,1/12)\). On these arcs,
\(a'=-r\), \(r' >0\), and \(a''<0\).
The side has constant a. The positive quadratic roots in (1)--(2)
give every endpoint directly; thus its coordinates and r are fixed
algebraic constants.

For a linear functional \(Xa+Yb\), the following lower bounds hold
on the whole fixed arc:

* **Side:** its minimum is the smaller endpoint value.
* **Concave endpoint rule:** if \(X\ge0\), its minimum is the smaller
  endpoint value, since \(Xa(b)+Yb\) is concave.
* **Lower endpoint rule:** if \(Y-Xr\ge0\) at both endpoint r values,
  the functional is increasing and its lower endpoint is a minimum.
* **Upper endpoint rule:** if \(Y-Xr\le0\) at both endpoint r values,
  the functional is decreasing and its upper endpoint is a minimum.
* **Circular rule:** on any circular piece, enlargement to the entire
  circle gives the lower bound
  \[
  v(X+Y)-\rho\sqrt{X^2+Y^2}.
  \tag{5}
  \]

The monotonicity rules require no assumed sign of X: the derivative
\(Y-Xr\) is affine in r and hence lies between its endpoint values.
The circular rule is valid even if its minimizing full-circle point is
outside the original arc. It is never applied to a core side.

These rules include zero coefficients, arc endpoints and contacts at
the side/corner junction. Affine labels may be piecewise defined and
need not agree at a junction: choose one containing closed piece once
for each state and retain that same label on its two incident edges.
The pair table covers either choice.

## 2. Separating-axis reduction

For source \((a,-\sigma b)\), target
\(R(\phi)(A,-\tau B)\), and width

\[
 W(\phi)=\frac{1+|\sin\phi|+|\cos\phi|}{2},
\tag{6}
\]

the four retained forward-axis margins are

\[
\begin{array}{c|l}
1&\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
2&A-a\cos\phi+\sigma b\sin\phi-W,\\
3&a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
4&a-A\cos\phi-\tau B\sin\phi-W.
\end{array}
\tag{7}
\]

Suppose one such margin M is nonnegative. For every fixed multiplier
\(\lambda\ge0\), the corrected pair cost satisfies

\[
 \phi+L_s-L_t\ge\phi+L_s-L_t-\lambda M.
\tag{8}
\]

Reflection followed by reversal exchanges the two states and negates
their signs. To preserve the cost, it replaces their labels by the
negatives of the old target and old source labels, respectively.
Direct substitution in (7) shows that axis 2 becomes axis 4 and axis 3
becomes axis 1; \(\phi\) remains unchanged. Thus it suffices to use
source axes 1 and 4, without assuming any symmetry of the role labels.

Let \(c,p,q\) and \(C,P,T\) be the resulting source and target
label coefficients in (3). The right side of (8) is

\[
 \phi+c-C+\lambda W+X_s a+Y_s b+X_t A+Y_t B,
\tag{9}
\]

where

\[
\begin{array}{c|cc|cc}
\text{axis}&X_s&Y_s&X_t&Y_t\\\hline
1&p&q-\lambda\sigma&-P-\lambda\sin\phi&-T+\lambda\tau\cos\phi\\
4&p-\lambda&q&-P+\lambda\cos\phi&-T+\lambda\tau\sin\phi.
\end{array}
\tag{10}
\]

The source coefficients are constant. Section 1 therefore gives a
fixed source lower bound. Applying an appropriate target support rule
leaves only the variable \(\phi\). The squared target norms needed
in the circular rule are exactly

\[
\begin{aligned}
 V_1&=P^2+T^2+\lambda^2
       +2P\lambda\sin\phi-2T\lambda\tau\cos\phi,\\
 V_4&=P^2+T^2+\lambda^2
       -2P\lambda\cos\phi-2T\lambda\tau\sin\phi.
\end{aligned}
\tag{11}
\]

These formulas follow by expansion and \(\sin^2\phi+\cos^2\phi=1\).
They are squared norms, so they are nonnegative on every actual angle.

## 3. Removing the last radical by one global identity

For \(h>0\), define

\[
 T_h(V)=\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16}.
\tag{12}
\]

For every \(V\ge0\),

\[
 T_h(V)-\sqrt V
 =\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0.
\tag{13}
\]

Thus the target circular support in (5) is bounded below by
\(v(X_t+Y_t)-\rho T_h(V)\). The parameter h is a fixed positive
rational in the table. Equation (13) is global; there is no local
remainder estimate or numerical minimizer in this step.

## 4. The fixed one-angle polynomial test

Write

\[
 \phi=k\pi/2+\epsilon u,\qquad
 k\in\{0,1\},\quad \epsilon\in\{-1,1\},\quad 0\le u\le.7.
\tag{14}
\]

Then the width is always \((1+\sin u+\cos u)/2\), while

\[
\begin{array}{c|cc}
 k&\sin\phi&\cos\phi\\\hline
 0&\epsilon\sin u&\cos u\\
 1&\cos u&-\epsilon\sin u.
\end{array}
\tag{15}
\]

On this interval the alternating series give

\[
 S_7(u)\le\sin u\le S_9(u),\qquad
 C_{10}(u)\le\cos u\le C_8(u).
\tag{16}
\]

Represent sine by its degree-7 polynomial and a degree-9 coefficient
in \([0,1/9!]\); represent cosine by its degree-8 polynomial and a
degree-10 coefficient in \([-1/10!,0]\). Interval arithmetic on
coefficients encloses the expression pointwise, even though the unknown
remainder coefficients can depend on u. No derivatives of them are used.

After substitution into the support premises and the lower cost from
(9), take the lower endpoint of each resulting coefficient. This gives
a lower polynomial because \(u\ge0\). The circular rule has degree
at most 30, and the endpoint and monotonicity rules have degree at most
10. A nonnegative frame charge
\(-\beta(|\sin\phi|+|\cos\phi|-1)/2\) may be included by the same
coefficient arithmetic.

For a fixed rational interval \([l,h]\), substitute
\(u=l+(h-l)x\) and express the polynomial in the Bernstein basis
\(\binom njx^j(1-x)^{n-j}\). Every basis function is nonnegative
and the basis sums to one on \([0,1]\). Nonnegative Bernstein
coefficients therefore prove the support premises on the full interval;
strictly positive coefficients prove a strict cost bound there.

When the endpoint rule gives the minimum of two endpoint values, both
cost polynomials must pass. Every radical constant is enclosed by two
rationals whose squares give its respective lower and upper bounds.
The \(\pi\) enclosure is justified by the alternating Machin series.
The checker records every resulting coefficient lower bound.

## 5. Exact domain completeness

The candidate quarter word is \((0,1,0,1,0,1,1)\). For a declared
source/target tangent subarc, let
\([\alpha_s^-,\alpha_s^+]\) and \([\alpha_t^-,\alpha_t^+]\)
be their signed arctangent ranges. The known center-gap bounds imply

\[
 \frac{19}{25}-\alpha_s^++\alpha_t^-
 <\phi<\frac{710}{113}-\frac{114}{25}-\alpha_s^-+\alpha_t^+.
\tag{17}
\]

Intersect these necessary bounds with
\([k\pi/2-.7,k\pi/2+.7]\), and convert each of its two closed
halves to u in (14). The verifier obtains outward rational bounds for
every endpoint by

\[
 \arctan x=2\arctan\frac{x}{1+\sqrt{1+x^2}},\qquad0\le x\le1,
\tag{18}
\]

followed by alternating sums through powers 49 and 51. Their argument
is less than \(\sqrt2-1<1\), so these sums give bounds with the
required directions. These are fixed comparisons at fixed arc
endpoints, not a varying state-domain computation.

For every original ordered pair of subarcs and every one of the four
axes, the declared table intervals must form a closed chain covering
both required u domains. The table may cover a larger domain. The
verifier also checks that the subarcs cover every declared role, radial
kind and sign interval; the core breakpoint is the exact rational 6/7.
Empty necessary angle domains require no pair row. All nonempty
domains, including an isolated endpoint, do.

Finally a valid cyclic exclusion uses one consistent role label for
each chosen physical state, so the seven labels telescope. The sum of
the seven verified lower bounds must exceed \(2\pi\). A full-SAT
owner/mismatch budget instead uses the separate implication in
`CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md`. The scalar verifier does
not infer either cyclic conclusion without those stated hypotheses.

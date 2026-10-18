# The mixed owners follow from total mismatch at most 1/1000

## Statement

Assume the geometric, cyclic-order, frame-lift and signed-tangent hypotheses
(1)–(3) of `HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md`, with

\[
q\le Q=9789/2500,\qquad S\le\varepsilon=1/1000.
\tag{1}
\]

Then every feasible retained canonical separator on G→A is axis 1, and
every such separator on E→H is axis 2. Together with the independently
proved quarter-owner theorem at \(S\le3/200\), the full allowed list is

\[
\boxed{\{1,3\},\{1\},\{1,3\},\{3,4\},
\{1,3\},\{3,4\},\{2\}.}
\tag{2}
\]

This improves the mixed-owner threshold from \(1/10000\) to \(1/1000\).
The improvement uses the same total mismatch in all five aligned edges.
It applies to arbitrary exterior centers satisfying the stated hypotheses,
including every independent choice of the two radial-boundary types.
The separate tilt conclusion is not assumed or proved in this note.

All forbidden-owner contradictions are strict, including separator ties.
Equality in the eventual radius theorem therefore uses only (2).

## 1. Retain the aligned support cusp

Use the same actual projections \(F_j\), nominal projections \(F_i^0\),
and width function \(W\) as (13)–(18) of the cited note. Each center has
norm less than \(3/2\), so

\[
|F_j(\phi+d)-F_j(\phi)|\le\tfrac32|d|.
\tag{3}
\]

For an aligned edge and \(|d|\le1/500\), the elementary inequalities
\(\cos d\ge1-d^2/2\) and
\(|\sin d|\ge|d|-|d|^3/6\) give

\[
\begin{aligned}
W(k\pi/2+d)
&\ge1+\tfrac12|d|-\tfrac14d^2-\tfrac1{12}|d|^3\\
&\ge1+\left(\tfrac12-\tfrac1{2000}
                  -\tfrac1{3000000}\right)|d|.
\end{aligned}
\tag{4}
\]

Subtracting (3) from the necessary separating inequality yields

\[
F_i^0\ge1-a|d_i|,\qquad a=\frac{1001}{1000},\qquad i\in I.
\tag{5}
\]

Indeed,
\(1+1/2000+1/3000000<1001/1000\). The actual bound
\(S\le1/1000\) is stronger than the \(1/500\) used to derive (4).

The two mixed edges still satisfy

\[
F_{GA}^0\ge W_t,\qquad F_{EH}^0\ge W_t-2S,
\qquad W_t=(1+\cos t+|\sin t|)/2.
\tag{6}
\]

For any fixed nonnegative edge weights \(\lambda_i\), (5)–(6) imply

\[
\sum_i\lambda_i F_i^0\ge
\sum_i\lambda_iw_i^0-
\varepsilon\left(a\max_{i\in I}\lambda_i+2\lambda_6\right),
\tag{7}
\]

where \(w_i^0=1\) on \(I\), and \(w_1^0=w_6^0=W_t\).
The key estimate is just

\[
\sum_{i\in I}\lambda_i|d_i|
\le\left(\max_{i\in I}\lambda_i\right)
   \sum_{i\in I}|d_i|
\le\varepsilon\max_{i\in I}\lambda_i.
\tag{8}
\]

There are no unrecorded independent error allowances: (7) preserves the
single total \(S\).

## 2. The circle dual is unchanged

Use the exact 35 necessary linear rows \(K_j\cdot x\ge v_j\) from
Section 2 of the cited note, including
\(7/12\le a_G,a_T\le349/250\). For a nominal owner pattern, set

\[
\begin{aligned}
C(t)&=\sum_i\lambda_i f_i^0(t)+\sum_j\kappa_jK_j,\\
L(t)&=\sum_i\lambda_iw_i^0(t)+\sum_j\kappa_jv_j+
\frac12\sum_rC_r(t)
-\varepsilon\left(a\max_{i\in I}\lambda_i+2\lambda_6\right).
\end{aligned}
\tag{9}
\]

Here \(\lambda_i,\kappa_j\ge0\) and \(\mu_i>0\) are fixed rational
constants. Equation (7), the cone rows, containment, and one completed
square per center give the necessary inequality

\[
L(t)\le Q\sum_i\mu_i+
\sum_i\frac{C_{a_i}(t)^2+C_{b_i}(t)^2}{4\mu_i}.
\tag{10}
\]

Put \(z=\tan(t/2)\), \(D=1+z^2\). As before, the numerator polynomials
\(\widehat C=DC\) and \(\widehat L=DL\) have degree at most two on each
fixed-sign interval. The strict reverse of (10) is exactly the positivity
of the quartic

\[
P(z)=D\widehat L-QD^2\sum_i\mu_i-
\sum_i\frac{\widehat C_{a_i}^2+
                  \widehat C_{b_i}^2}{4\mu_i}.
\tag{11}
\]

Only the constant loss in (9) differs from the earlier circle-dual
calculation. In particular the maximum in (9) is the maximum of five
explicit rational constants in that row, and introduces no varying-state
choice or additional polynomial degree.

## 3. The finite hand table and the complete alternatives

The 15 alternatives are precisely

\[
\mathcal P=\{(1,g,1,3,1,3,h):
g,h\in\{1,2,3,4\},\ (g,h)\ne(1,2)\}.
\tag{12}
\]

For each pattern, `candidate_mixed_owner_shared_mismatch_hand_data.json`
supplies a finite closed cover of \([-3/8,3/8]\). In total it contains
729 quartics with 3,645 positive Bernstein lower bounds. Each row gives
its rational interval, the seven \(\lambda\) numerators, the nonzero
indexed \(\kappa\) numerators, and seven positive \(\mu\) numerators,
all with denominator \(10^8\). The five final positive integers are
Bernstein lower numerators with denominator \(10^{12}\).

For each row, substitute its constants into (9)–(11), and use the exact
Bernstein conversion (24)–(25) of the cited note. Every resulting
coefficient is at least its printed strictly positive lower bound. The
smallest printed bound over the entire table is

\[
\frac{231527}{10^{12}}>0.
\tag{13}
\]

The companion `verify_candidate_shared_mismatch_owner_duals.py` is a
self-contained rational replay of these fixed comparisons. It reconstructs
the loss (9), all force polynomials, all 3,645 Bernstein coefficients and
the inverse coefficient transformation. It then verifies the 15 exact
closed interval unions, with no duplicate or missing interval or pattern.
It also checks the rational comparison in (4)–(5). Its report binds both
the full data and checker hashes. No floating-point computation, optimizer,
search, sampled state, interval subdivision, or imported proof program is
part of this replay.

If a forbidden feasible mixed separator existed, choose it on that edge
and a feasible separator on every other edge. The prior quarter theorem
reduces the nominal pattern to (12). Its table provides \(P>0\) at the
actual \(z\), contradicting (10). This proves the claimed owner sets for
every actual packing satisfying (1) and the stated geometric hypotheses.

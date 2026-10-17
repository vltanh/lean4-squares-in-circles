# Independent audit of the mixed owners at total mismatch 1/1000

**Result: PASS.** The shared-error argument, circle elimination, complete
15-pattern alternative and every fixed rational quartic have been checked
independently. The conclusion remains conditional on the stated candidate
geometry, signed tangent intervals and preceding quarter-owner theorem.
It does not establish the global bound on total mismatch.

The reviewed theorem is
`HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md`. Its only edits during
this review corrected two mathematical typesetting delimiters. The exact
data and author checker were unchanged.

## 1. Continuous geometric argument

Write the roles in order as `(H,G,A,B,T,D,E)` and use own-frame centers
\((a_i,-\sigma_i b_i)\), with
\(\sigma=(+,-,+,-,+,-,-)\). The four forward SAT projections used by the
author are obtained by projecting the center difference onto source
\(+f\), target \(+e\), target \(+f\) and source \(-e\). Their signs
and source/target coefficients agree with those projections. Varying the
relative frame angle in any one of the four formulas rotates only one
center. Every center has norm less than \(3/2\), because its radius-\(1/2\)
incircle lies in a containing disk of radius less than 2. Hence the
projection changes by at most \((3/2)|d|\).

At a multiple of \(\pi/2\), the square support has a cusp. For
\(|d|\le1/500\), its exact expression and the elementary sine/cosine
inequalities give

\[
W(k\pi/2+d)\ge
1+\left(\frac12-\frac{1}{2000}-\frac{1}{3000000}\right)|d|.
\]

Subtracting the projection error from this necessary SAT lower bound
therefore gives

\[
F_i^0\ge1-\frac{1001}{1000}|d_i|,\qquad i\in I=\{0,2,3,4,5\}.
\]

The direction of the inequality is correct, including negative deviations
and zero deviation. The selected actual axis may be either member of a
nominally coincident aligned pair: the projection error applies to that
actual axis before its nominal value is identified with the representative.

The G-to-A relative angle is exactly \(\pi/2-t\). The E-to-H angle differs
from \(\pi/2+t\) by minus the sum of the five signed aligned deviations.
The width is globally \(1/2\)-Lipschitz, so the nominal necessary bounds
on these two edges are \(F_{GA}^0\ge W_t\) and
\(F_{EH}^0\ge W_t-2S\), respectively. No uncharged error occurs on G-to-A.

For fixed nonnegative weights, the total error is at most

\[
\frac{1001}{1000}\sum_{i\in I}\lambda_i|d_i|+2\lambda_6S
\le S\left(\frac{1001}{1000}\max_{i\in I}\lambda_i+2\lambda_6\right).
\]

Replacing \(S\) by \(1/1000\) is consequently valid. The maximum is taken
over five constants fixed in that row; it is not a state-dependent
selection. This verifies the new shared-total-error step independently of
the superseded per-edge error allowance.

## 2. Cone rows and center elimination

The 35 linear necessary rows were checked from containment, core avoidance
and the declared tangent bounds. In particular, for G and T,
\(b\le(4/5)a\) rules out \(a<7/12\): it would give \(b<1/2\) and
distance to the square less than \(1/12\). Their lower ratio bound
\(b\ge a/20\), together with containment, gives \(a<349/250\).
The remaining roles use the weaker valid primary bounds
\(447/800\le a\le283/200\), and every role has \(b\le9/10\).
The independent checker reproduces the relevant squared rational
comparisons.

Adding the nonnegative weighted necessary rows gives \(C\cdot x\) at
least the weighted right-hand side. Adding half the sum of the force
coordinates changes each center to \(y_i=(a_i+1/2,b_i+1/2)\). For each
positive \(\mu_i\),

\[
C_i\cdot y_i\le\mu_i|y_i|^2+\frac{|C_i|^2}{4\mu_i}
\le Q\mu_i+\frac{|C_i|^2}{4\mu_i}.
\]

Thus the author's inequality (10) is necessary for every admitted center.
It requires neither a sign condition on the force coordinates nor a radial
boundary equality. The strict opposite inequality excludes an owner
pattern for all center coordinates at once.

With \(z=\tan(t/2)\), \(D=1+z^2>0\), and a fixed sign of \(z\), the
nominal force and right-hand-side numerators have degree at most two.
Multiplication by \(D^2\) produces precisely the stated quartic. The error
term is a constant times \(D\) in the right-hand-side numerator and hence
a constant times \(D^2\) in the quartic; its sign is negative, as required
for a conservative necessary inequality.

## 3. Independent fixed arithmetic

`audit_candidate_shared_mismatch_owners_independently.py` imports no author
proof program. It reconstructs the nominal rows from an explicit table of
the geometric formulas. For example, the aligned values are

\[
b_H+b_G,\quad b_A+b_B,\quad a_B-b_T,\quad
b_T+b_D,\quad a_D+b_E,
\]

and it separately lists all four G-to-A and E-to-H alternatives. It builds
the cone contributions directly in coordinate order, rather than calling
the author's generic axis routine. It checks every sign and denominator
of the fixed weights.

For each independently constructed quartic, the program evaluates the
polynomial at five rational points and solves the five-by-five Bernstein
basis interpolation system by exact Gauss-Jordan elimination. It then
expands the resulting Bernstein expression back into the global
\(z\)-coordinate and requires identity of all five power coefficients.
This is an exact polynomial identity, not inference from sampled
positivity. It uses neither the author's coefficient-conversion formula
nor floating-point arithmetic.

All **729 quartics and 3,645 printed positive coefficient bounds** pass.
The least printed lower bound is exactly

\[
\frac{231527}{10^{12}}>0.
\]

The author's complete checker was also run in a new temporary flat
directory containing only its source and fixed data. Its report was
byte-identical to the frozen report, with no standard-error output.
All author input hashes remained unchanged during the review.

## 4. Complete alternatives and endpoint coverage

At the claimed mismatch threshold, the already established zero-quarter
and quarter-owner conclusions apply. Their nominal representatives give
exactly

\[
(1,g,1,3,1,3,h),\qquad g,h\in\{1,2,3,4\}.
\]

Excluding the desired mixed choice \((g,h)=(1,2)\) leaves 15 patterns.
The independent program constructs this set directly. For every pattern
it rejects duplicate intervals, sorts the declared closed intervals and
requires every next left endpoint to equal the preceding right endpoint,
starting at \(-3/8\) and ending at \(3/8\). Intervals crossing zero are
rejected; a zero endpoint is covered by its valid fixed-sign formula.

The exact arctangent lower bound
\(3/8-(3/8)^3/3>7/20\) shows that this interval covers every admitted
\(|t|<7/10\). Thus no angle, pattern or endpoint is missing. Choosing a
putative forbidden feasible mixed separator, together with any feasible
separator on the other edges, produces one of the excluded patterns.
Strict quartic positivity also excludes separator ties.

It follows that G-to-A has only axis 1 and E-to-H only axis 2 under the
stated hypotheses and \(S\le1/1000\). This completes the independent audit
of the strengthened mixed-owner gate.

## 5. Binding and replay

The machine-readable binding is
`candidate_shared_mismatch_owners_independent_audit.json`. Its `sha256`
map includes the corrected manuscript, the shared definition note, the
unchanged author checker, the exact fixed data and the author arithmetic
report. It also records the independent checker hash, every pattern's
closed-cell count and least printed coefficient.

Run:

```sh
python audit_candidate_shared_mismatch_owners_independently.py
```

All paths are relative to the script's directory, so the same three audit
files and five author inputs can be replayed in a flat repository layout.

# Independent audit of the complete outer quarter-one scalar hand gate

## Result

**PASS.** The 140-row scalar theorem for the wrong quarter word 0010111
is valid on its stated continuous domains. Together with the independently
audited six contact neighborhoods, it covers all 48 outer/outer quarter-one
axis cases. The complete whole-word assembly has no remaining scalar-audit
dependency.

This review does not use sampled minima, numerical optimization, or adaptive
state subdivisions. The independent checker reconstructs the fixed rational
polynomials from the stated formulas and solves their Bernstein expansions by
triangular basis elimination.

## Continuous derivation checked independently

1. An outer arc satisfies
   \[
   a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\qquad
   a'=-r,\quad r_0\le r\le1,\quad a''<0.
   \]
   Therefore a linear functional with nonnegative coefficient of \(a\)
   is concave and has its minimum at an arc endpoint. If the derivative
   \(Y-Xr\) has one sign at both endpoints of its \(r\)-interval, the
   claimed axial or diagonal minimum follows. Enlarging to the full
   circle gives the stated unrestricted circular lower bound.

2. Reflection followed by reversal changes source/target signs to
   \((-\tau,-\sigma)\), preserves the frame increment, maps axes \(3,2\)
   to axes \(1,4\), and changes the label coefficients to
   \((-P,t,-p,q)\). Direct substitution reproduces both the original cost
   and the original signed separator. No symmetry of the role labels is
   assumed.

3. For every nonnegative multiplier, subtracting the multiplier times
   the nonnegative SAT margin lowers the corrected cost. This gives
   the two source and target coefficient rows in the manuscript.
   The source support bounds and all target support premises have the
   correct signs, including when a coefficient is negative or zero.

4. Independently expanding the homogeneous identity gives
   \[
   (x-h)^4(x^2+4hx+5h^2)
   =x^6-5h^2x^4+15h^4x^2-16h^5x+5h^6.
   \]
   Thus the cubic polynomial \(T_h(v)\) is an upper bound for \(\sqrt v\)
   for every \(v\ge0,h>0\). The exact squared norms in the two SAT cases
   reduce to the displayed constant and first harmonics by
   \(\sin^2u+\cos^2u=1\). The resulting lower cost contains no unbounded
   variable radical.

5. On \(0\le u\le .7\), the alternating series encloses sine between its
   degree-7 and degree-9 sums and cosine between its degree-10 and
   degree-8 sums. Their unknown remainder coefficients may depend on
   \(u\); coefficient interval arithmetic still encloses each value
   pointwise. After expansion, choosing the lower endpoint of every
   coefficient gives a lower polynomial because all powers \(u^j\)
   are nonnegative. No remainder derivative is used.

6. All fixed radical and Machin-series enclosures are in the correct
   direction. The Bernstein basis is nonnegative and sums to one.
   Nonnegative premise coefficients therefore prove the support-rule
   hypotheses, and strictly positive cost coefficients prove the
   claimed strict cost lower bounds.

## Independent arithmetic reconstruction

The independent Python checker imports none of the author's arithmetic or
polynomial routines. It uses Fraction arithmetic, integer square roots,
interval coefficient addition and multiplication, and Horner substitution
for the affine interval change. It then removes Bernstein basis polynomials
successively from the lowest power, an independent conversion from the
author's direct binomial formula.

The reconstruction verified:

- all **140** declared source support bounds;
- all **310** premise and cost polynomials;
- all **4,475** printed coefficient lower bounds;
- every literal manuscript row, including its signs, interval, multiplier,
  source bound, target rule, radical parameter, and printed cost reserve;
- every source label and reflected/reversed target label against the
  immutable rational role data;
- all **96** closed angle chains for the **48** original axis cases.

The smallest exact cost coefficient is
\[
\frac{945228276818927}{10^{19}}
=0.0000945228276818927>0.000094.
\]
All premise coefficients are nonnegative. Every cost coefficient is strictly
positive. The independently calculated coefficients dominate every printed
decimal lower bound.

## Coverage and whole-word interface

The fixed label roles force role 0 positive and role 2 negative. This follows
from the two zero edges, whose center gaps sum to more than \(1.52\), whereas
the total lifted frame increment is less than \(.7\). Thus their relative
center/frame angles differ by more than \(.82>\pi/4\). A negative-to-positive
zero edge is impossible for the same center-gap reason.

This leaves 19 signed role entries, of which 12 are quarter-one entries.
Each retained SAT axis and each radial kind are included, for 304 total
possibilities. On the outer quarter-one component, the six contact
neighborhoods begin at zero; every complementary scalar chain begins
exactly at that contact theorem's closed endpoint. The other chains begin
at zero. All chains terminate at \(.7\), without gaps.

The scalar table proves \(.8975\) on edge 2 and \(.89765\) on the other
quarter-one edges. The previously audited components give at least those
bounds on their cases. The exact cyclic total is
\[
6(.89765)+.8975=\frac{31417}{5000}
=\frac{710}{113}+\frac{121}{565000}>2\pi.
\]
The labels telescope, contradicting center holonomy \(2\pi\).
The separately replayed whole-word assembly confirms the exact finite
coverage and component bindings. It is an assembly check, rather than a
replacement for any component's continuous proof.

## Replay and binding

The author's checker was copied with its label and table inputs to an
isolated temporary directory. Its output is byte-identical to the frozen
arithmetic JSON, with exit status zero and no diagnostics.

The exact hashes, reconstructed per-row polynomial minima, replay location,
and assembly output are recorded in
short_quarter_scalar_independent_audit.json.

Independent reproduction: run
python3 audit_short_quarter_scalar_independently.py.

The independent checker's SHA256 is
073d7d61782042e14b7afd8d53ecb6321057165d55f6aebc040afefd56ef8112.

No mathematical correction to the author's scalar manuscript, table,
checker, or assembly was required.


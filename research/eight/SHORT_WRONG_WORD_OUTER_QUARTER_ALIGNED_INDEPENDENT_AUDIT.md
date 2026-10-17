# Independent audit: six 0010111 outer quarter contact strips

**Result: PASS for the six stated near-aligned regimes.**
This audit covers the continuous proof and exact input binding of
`SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md`.
It does not certify the separately stated tail regimes.

The source checker freshly passed all 80 comparisons, and its output was
byte-identical to the stored arithmetic JSON. A separate Fraction-based
checker, `verify_short_outer_quarter_aligned_independently.py\), reconstructs
the six normalized coefficient rows directly from `short_hand_labels.json`
and passes 45 additional fixed comparisons using a different rational
implementation.

## Continuous review

1. **Reflection and exact labels.** The original affine marker is
   \(c+pa+\sigma qb\). Applying reflected reversal to the two negative
   original rows negates the swapped constant and primary coefficients,
   and interchanges the transverse coefficients. This reproduces all
   three displayed \(+f\) rows and all three paired \(-e\) rows exactly.
   In particular the constants are not multiplied by the tangent sign.

2. **Aligned minimum.** I independently differentiated (5):
   \(H'=t-p-q(1.5-B)/(b+.5)+Pr_B\), and
   \(H''=qQ/(b+.5)^3+PQ/(A+.5)^3\).
   The negative second term in row 1 uses the correct lower denominator
   \(1.885\), while the positive term uses the upper denominator \(1.4\).
   The one-point strong-convexity lower bound is valid on the entire
   interval. The monotone rows and all three small-\(B\) allowance
   comparisons also have the stated directions.

3. **Source \(+f\), negative half.** The source label is strictly
   increasing and the target contribution strictly decreases with \(B\).
   The stated contact endpoint signs give a complete interval with
   boundaries \(b=0\) and \(B=d\); a source diagonal is not omitted.
   I rederived both formulas in (10). At a stationary target coordinate,
   the same derivative formula as on the moving axial boundary applies.
   The positive linear functional \(tU-PV\) is concave as a function of
   \(V\), so its minimum is at an endpoint; the exact endpoint comparison
   selects the diagonal. The twelve fixed diagonal speed products and
   the interior speed estimate are valid. Thus the compact-minimum
   argument excludes every minimum with \(u>0\), including \(u=.3\).

4. **Source \(+f\), positive half.** Here
   \(D=V\cos x-U\sin x>0\).
   Differentiating the contact gives
   \(b_x=-D+\cos x-\sin x\), which yields (13).
   The proof treats the sign of its parenthesis correctly.
   The target and source endpoint inequalities cover both boundaries.
   All three costs increase in the required direction at every potential
   minimum, so this whole half reduces to alignment.

5. **Source \(-e\), negative half.** Reducing \(a\), and then \(B\)
   if necessary, reaches contact while reducing cost. The claimed
   infeasibility of \(a=d,B=0\) follows already from
   \(.9+1.415(.06)<1\), which the independent checker makes explicit.
   I rederived the diagonal implicit derivative (16); its numerator is
   \(tU+PV\), and the negative \(P\) term uses the upper bound \(V<.66\).
   The continuation stays inside the permitted target arc and reaches
   alignment.

6. **Source \(-e\), positive half.** On contact,
   \(a_x=-h\), \(h'=a-.5\), and
   \((L_a h)'=-qQh^2/v^3+L_a(a-.5)<0\).
   Every sign and denominator in (17) is correct.
   At \(x=0\), both positive factors in (18) decrease with \(B\), so
   \(C_x(0,B)\) increases. The split at \(B=1/80\), loss at most
   \(.02(.06)=.0012\), and aligned monotonicity yield the claimed strict
   bound. If continuation reaches \(a=d\), replacing the formal
   continuation by the actual clamped source gives derivative 1; this
   correctly preserves the lower estimate.

No numerical stationary-point enumeration, hidden sign assumption,
or unproved contact-curve completeness premise is used.

## Bound files

| File | SHA-256 |
|---|---|
| Manuscript | `61eb49ece16e137f8c1e08aef122226359ffd88af70accd4d2037095d7df7992` |
| Source JavaScript checker | `5a54c483efd0c335fd57ec5d7ff14c60d421587286178bed3252e34f966aa45d` |
| Stored source arithmetic JSON | `69fbc4ba12f906a8498597d52e0432d5f97ecc4f8ea642ea3947d6f69a6c5363` |
| Exact role labels | `2113900b72530b6cb660e2a2b9f52d4fd3a54d793426978caa2167cd954a5051` |

The separate independent arithmetic JSON records the same hashes,
coefficient reconstruction, all 45 rational reserves, and the source
replay result.


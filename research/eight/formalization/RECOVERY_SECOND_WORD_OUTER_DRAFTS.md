# Recovery record: second-word outer-pair drafts

## Scope and verification state

This record preserves the global-owner/G2 agent's state after the
executor disconnected and returned an older workspace snapshot. It is
a recovery document, not a claim that the formalization is complete.

The recovered Lean files are **uncompiled source drafts**. No Lean, lake,
typechecker, tests, CI, or proof-source audit was run. Several imports and
pre-outage geometric modules are absent from the returned snapshot.
Consequently the recovered owner join cannot currently be used as a
checked theorem.

Root owns staging, commits, and publication. On root's instruction, new
proof drafting was paused after retained source was materialized.

## Source successfully recovered

Exactly sixteen complete retained patches were applied to the returned
workspace. The earlier approximate count of nineteen was incorrect.

- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoAxialCalculus.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoAxial.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoUpperTargetPrimary.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoTargetRatio.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoPrimaryInverse.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoPrimaryAxis.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoUpperSourcePrimary.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerSourceSecondary.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerSupportPolynomial.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerSupportCurvature.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerSupport.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerStripScalars.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerStripContact.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerStrip.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwoLowerTargetSecondary.lean`
- `SquaresInCircles/Eight/TableFree/SecondOuterOppositeTwo.lean`

The saved owner join is
SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.original_scalar.
Its intended inputs are actual outer states, a quarter offset in
[-7/10,7/10], an original axis j : Fin 4, and its weak forwardMargin
inequality. Its conclusion is

\[
 .89778<\pi/2+x-P(b)-V(B).
\]

It has explicit bodies for all four axes in both angle halves, retaining
ties. Convenience forms original_scalar_abs, original_at_angle, and
original_some_axis are also saved.

The physical SecondWord.cost adapter, reflection adapter, and
BoundaryCycle wrapper were not written after the outage: their existing
source interfaces were unavailable. Do not infer them from the scalar
join alone.

### Recovered module responsibilities

| Module suffix | Content |
|---|---|
| AxialCalculus | Early inverse-boundary decrease and late curvature greater than .11 |
| Axial | Actual rational reference .56615 and the complete zero-source bound |
| UpperTargetPrimary | Original weak upper target-primary axis by finite circle displacement |
| TargetRatio | Whole-circle diagonal target inverse ratio with strict derivative reserve |
| PrimaryInverse | Explicit inverse rotation over all physical primary shifts |
| PrimaryAxis | Zero-target boundary decreases to the aligned endpoint |
| UpperSourcePrimary | Original upper source-primary axis, including its inactive regime |
| LowerSourceSecondary | Original lower source-secondary axis and an IVT-produced zero source |
| LowerSupportPolynomial | One full-interval polynomial certificate for the lower support |
| LowerSupportCurvature | Exact support derivatives and concavity on [0,.7] |
| LowerSupport | Original lower target-secondary axis on [.01,.7] |
| LowerStripScalars | Actual .415/.775 references and zero-target inverse boundary |
| LowerStripContact | Source-contact curvature greater than .1 and endpoint derivative |
| LowerStrip | Actual weak lower target-secondary short interval [0,.01] |
| LowerTargetSecondary | Full-angle join of strip and support tail |
| no suffix | All eight original axis/angle halves |

AxialCalculus had an uncertain pending write during disconnection.
The returned snapshot contained no file at that path, so its complete
retained reconstruction was materialized. No competing copy was
overwritten.

## Missing pre-outage dependencies and reported interfaces

The following nine SecondOuterOppositeTwo files had been drafted on disk
before the outage but were absent on return. Their full source was not
retained in the agent's functions.store.

1. **Data**: value b B φ = φ - P b - V B, original cost identity,
   lower/upper secondary and primary contact formulas.
2. **SourceRatio**: P_first_zero, P_first_affine, source_ratio_paid,
   source_ratio; the last two pay the lower source-primary contact.
3. **Labels**: exact bOne = arc 1 and radical cage, V_first_upper,
   V_second_upper, V_second_antitone, V_first_two, V_second_two,
   P_second_monotone, P_second_small, P_second_bOne,
   and both aligned axial values.
4. **Aligned**: full left/right aligned costs, including
   aligned_left_original and aligned_right_original.
5. **LowerPrimary**: lower_width and original_lower_source_primary.
6. **UpperSecondary**: upper_width, original_upper_source_secondary,
   original_upper_target_secondary.
7. **TargetPrimaryLabel**: actual VPrimaryLabel, its first/second
   derivative bounds, and positive contact product.
8. **LowerTargetPrimary**: original_lower_target_primary with the
   stronger scalar reserve .901.
9. **InverseBounds**: full-interval rational bounds for the actual
   inverse contact, including factor_upper, K0_bounds, and
   actual_height_derivative.

These interfaces were preserved in the working summary and used by the
recovered drafts. Their source, exact namespaces, and elaboration must
be recovered or reconstructed before an ordinary implementation audit.

The earlier complete negative edge-two chain was also absent.
Its final reported files were SecondOuterNegativeTwo.lean and
SecondOuterNegativeTwoCycle.lean. The final cap sequence was:

- SecondOuterNegativeTwoCapGeometry.lean;
- SecondOuterNegativeTwoCapFourth.lean;
- SecondOuterNegativeTwoCapCages.lean;
- SecondOuterNegativeTwoCapReferenceCalculus.lean;
- SecondOuterNegativeTwoCapReferences.lean;
- SecondOuterNegativeTwoCapValues.lean;
- SecondOuterNegativeTwoCap.lean.

This is not an exhaustive manifest of that earlier chain.
Retained mathematical interfaces included NegativeTwo.ContactInverse,
NegativeTwo.TargetContact, NegativeTwo.Inverse, and the original
all-axis/cycle/reflection joins. Those are dependencies of the recovered
opposite edge-two proof.

Shared missing sources included SecondWordData.lean and the outer-label
calculus/bounds/reference modules. Other agents own their recovery
records for mixed-pair and physical bridge modules.

## Mathematical record of the recovered opposite edge-two argument

Every decimal below is an exact terminating rational. Set

\[
 Q=9789/2500,\quad a(b)=\sqrt{Q-(b+.5)^2}-.5,\quad
 U=a+.5,\quad W=b+.5,\quad r=W/U,
\]
\[
 d=\sqrt{Q/2}-.5,\qquad b_1=a(1).
\]

The labels are

\[
 P(b)=.02478+.93015b+.02363b^2-.11055a(b)b,
\]
\[
 V(b)=-.01025a(b)+.16031b+.63457a(b)b.
\]

### Axial bound

The zero-source inverse boundary is
\(H(b)=\pi/2-x_0(b)-P(0)-V(b)\), with the exact original contact angle.
It decreases on [0,.2] and has \(H''>.11\) on [.2,d].
At the single source b=.56615, the retained proof bounds

\[
 x_0\le .150171,\quad H>.897784,\quad |H'|<10^{-5}.
\]

A square completion yields \(H>.89778\) everywhere. The angle comparison
uses the original contact equation and an intermediate-value root.

| Reference quantity | Lower | Upper |
|---|---:|---:|
| U | 1.6670105511 | 1.6670105512 |
| q=Q+1-2U | 1.5815788976 | 1.5815788978 |
| r | .6395580395 | .6395580396 |
| inverse speed | 1.1539405953 | 1.1539405955 |
| inverse factor | .85286630 | .85286632 |
| inverse correction | .17521675 | .17521678 |
| V' | .67764657 | .67764659 |

### Upper target-primary owner

The original separator gives
\(b+1-A\le\{U-1+.35W\}x\).
The circle support \(U+.51W<2.23\) and
\(P'<.6625+.223W\) yield
\(P'(U-1+.35W)<.981\).

For A≥1, compare with aligned source b0=A-1. For A<1, the primary
target-label tangent bounds its loss by .44(1-A), while P'>.773.
Both regimes therefore end at established aligned costs.

### Upper source-primary owner

The inverse rotation extends to all physical primary shifts
z in [d-.5,a0-.5], contained in [0,.915], since q≥1.0856.
The target derivative is

\[
 F(z,B)=\frac{Q-U}{Uq}+\frac{zr}{q\sqrt{q-z^2}}.
\]

It increases with the primary shift. At the diagonal shift,
F-V' is positive at zero and has derivative greater than .012.
Thus the full target contact cost increases.

For source primary height at least one, move to the aligned target.
Below one, move to target zero. That primary boundary decreases to
height one because its source-primary derivative times the actual speed
is less than one. No minimizer premise is used.

### Lower source-secondary owner

For the fixed original target, let c(x) be the maximal allowed source.
Its contact cost derivative is \(-1+P'(c)v<0\).
The actual circle gives \(v^2\le Q-(c+1.5)^2\).
The product \(P'(c)\sqrt{Q-(c+1.5)^2}\) decreases on [0,.415]:
P''<.197, P'>.773, and

\[
 .197(Q-2.25)-.773(1.5)<0.
\]

At zero the product is below one. An IVT argument continues the
original contact to a zero source, where the axial theorem applies.

### Lower target-secondary owner: tail

For x in [.01,.7], use the actual source chord
\(P(b)\le P(0)+.83829b\) for b≤b1 and target line
\(V(B)\le V(0)+1.061B\).
The circle support gives

\[
 F(x)=\pi/2-x-P(0)-V(0)-\sqrt Q\,N(x)
       +1.061\cos x+\frac{.83829+1.061}{2},
\]
\[
 N(x)^2=.83829^2+1.061^2-2(.83829)(1.061)\sin x.
\]

One polynomial identity proves F''<0 on all [0,.7].
The endpoints F(.01)>.8982 and F(.7)>.986 cover the full tail.

### Lower target-secondary owner: short strip

For x in [0,.01], put

\[
 C_x(b)=(a(b)-.5)\cos x-(b+.5)\sin x-.5.
\]

The weak separator gives 0≤B≤C_x(b), hence b≤b1 and C_x(b)≤.415.
An IVT endpoint β in [b,b1] satisfies C_x(β)=0.
The actual .775 reference gives C_x(.775)>0, so β≥.775.

For \(J_x(b)=\pi/2-x-P(b)-V(C_x(b))\),

\[
 J_x''=-P''-V''k^2+V'r'\cos x>.1,\qquad
 k=r\cos x+\sin x.
\]

The constants are P''<.345, V'>.82, r'>.557, cos x≥.99995.
At the actual zero-target endpoint,

\[
 J_x'(\beta)<-.9269+1.061(.871)<0.
\]

Thus the entire feasible source interval decreases to β.
Its zero-target inverse boundary decreases on [.775,b1], because

\[
 \frac{Q-U}{Uq}<.963,\qquad
 \frac{r}{2q\sqrt{q-.25}}>.13,\qquad P'>.9269.
\]

It reaches the aligned axial value above .89778. The endpoint and
its location are proved, not assumed.

## Remaining second-word work at the pause

Before the outage, the agent reported complete drafts for the first
wrong word and second-word outer representatives edge0 opposite,
edge4 opposite, edge3 positive-negative, edge4 same-sign, edge0 same-sign,
and edge2 negative-negative. Their newer source was not recovered in
the returned snapshot. The sixteen files above preserve the newly
finished edge2 negative-positive argument as a dependency-incomplete
draft only.

The opposite edge3 family (-,+) had not yet been translated.
Positive edge3 (+,+) was pending too. Another agent owns negative
edge3 (-,-) and its recovery state.
Do not state that G2, complete owner entry, or the user theorem is done.

## New opposite-edge-three simplification, not yet formalized

For

\[
 T(b)=.01670+2.42322b-.91744b^2-.95769a(b)b,
\]
\[
 L(B)=.03965+3.85510B-1.49748B^2-1.89442a(B)B,
\]

both upper-secondary owners admit a finite comparison avoiding the
hand note's zero-exit curve.

The upper contact gives

\[
 \text{transverse}+1-\text{primary}\le .4x
\]

from d<.9, cos x≤1, sin x≤x. At primary height at least one, compare
with its aligned transverse coordinate; T'<1.069 and L'<1.176 pay
the displacement.

Below primary height one, compare with the aligned axial endpoint.
On [b1,d], the circle slope is greater than .86. Thus the label cost
per unit lost primary height is at most 1.176/.86<1.4; the other
transverse label derivative is also below 1.4.
The total loss is less than \(1.4(.4x)=.56x\), paid by the angular gain.
This reduces both original weak upper-secondary owners, including ties,
to the two aligned costs. Those aligned-cost theorems were not drafted
in this continuation.

## New rational inverse polynomial, not yet formalized

An independent gate for the opposite-edge-three critical curve was
derived exactly in rational arithmetic before the pause.

Put q(u)=Q+1-2u. For positive u and q(u),

\[
 \frac{Q-u}{u q(u)}>.84.
\]

The positive numerator after clearing the denominator is
\(1.68u^2-5.129104u+Q\).
Its completed-square reserve is positive:
\(Q-5.129104^2/6.72>.0007625\).

Define

\[
 X(u)=\frac Q{Q+1}\left(\frac Q{u^5}
              +\frac{2(Q-u^2)}{u^5}\right)
 -\frac{2(Q-1)}{Q+1}\left(\frac Q{u^3q^2}
              -\frac{4(Q-u^2)}{u^2q^3}\right).
\]

Let \(P(u)=(.55-X(u))u^5q(u)^3\) and s=u-1.644.
The exact coefficients of P(1.644+s), from degree zero to eight, are:

| Degree | Exact coefficient |
|---:|---:|
| 0 | 476159311146441826602549/305175781250000000000000 |
| 1 | 26101615378177364354307/244140625000000000000 |
| 2 | -79955973126184850181/488281250000000000 |
| 3 | 454962014464731219/1953125000000000 |
| 4 | 2000561895379869/15625000000000 |
| 5 | 5418602309299/312500000000 |
| 6 | -2460112413/62500000 |
| 7 | -317823/12500 |
| 8 | -22/5 |

They give a single whole-interval bound

\[
 P(1.644+s)\ge
 1.56+s(106.91-163.75s-39.362s^5-25.426s^6-4.4s^7)>0
\]

for 0≤s≤.271. The parenthesis is greater than 62.
Hence X<.55 on [1.644,1.915].
This is mathematical recovery data: no Lean declaration for it was saved.


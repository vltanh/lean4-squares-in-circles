module

public import SquaresInCircles.Eight.Arithmetic.PreparedArc

/-!
# Eight squares: lower bounds of a linear function on an arc

For a valid prepared arc and real coefficients `X` and `Y`, the bounds of `AffineArc.lean`, on the
support domain of `PreparedArc.lean`, bound `X x + Y y` below at every state `(x, y)` of the arc:
by the smaller of the two endpoint values on the core side or when `X ≥ 0` (`endpoints_lower`);
by the value at the lower endpoint when the slope `Y - X r` is nonnegative at the ratios `r` of
both endpoints (`lower_endpoint`); by the value at the upper endpoint when it is nonpositive at
both (`upper_endpoint`). On a circular arc the ratio expressions are the values of `circleRatio`
at the endpoints (`ratioLo_value`, `ratioHi_value`).

The bounds hold for each pair `(X, Y)`. `RowCheck.lean` applies them to the source arc of a row,
where the coefficients are constant, and at each angle to the target arc, where they depend on
the angle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Arithmetic.PreparedArc

/-- On a circular arc the ratio at the lower endpoint is the value of `circleRatio` there. -/
theorem ratioLo_value {a : PreparedArc} {x y : ℝ}
    (hf : a.CircleFacts x y) (hs : a.data.side=false) :
    a.ratioLo.value = circleRatio a.data.shift a.radiusExpr.value a.bLo.value := by
  have he := circle_branch hf.lower_shift hf.lower_circle
  simp only [ratioLo,hs]
  change (a.bLo.value-(a.data.shift : ℝ))/(a.aLo.value-(a.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

theorem ratioHi_value {a : PreparedArc} {x y : ℝ}
    (hf : a.CircleFacts x y) (hs : a.data.side=false) :
    a.ratioHi.value = circleRatio a.data.shift a.radiusExpr.value a.bHi.value := by
  have he := circle_branch hf.upper_shift hf.upper_circle
  simp only [ratioHi,hs]
  change (a.bHi.value-(a.data.shift : ℝ))/(a.aHi.value-(a.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

/-- On the core side or for `X ≥ 0`, a lower bound of `X x + Y y` at the two endpoints holds at
every state of the arc. -/
theorem endpoints_lower {a : PreparedArc} (ha : a.NumericValid)
    {x y X Y m : ℝ} (hxy : a.data.Contains a.radius x y)
    (hmode : a.data.side=true ∨ 0 ≤ X)
    (hl : m ≤ X*a.aLo.value+Y*a.bLo.value)
    (hu : m ≤ X*a.aHi.value+Y*a.bHi.value) : m ≤ X*x+Y*y := by
  have hd := a.supportDomain ha hxy
  cases hs : a.data.side with
  | true =>
      have hx : x=7/12 := by simpa [SupportDomain,hs] using hd.2.2
      have hL : a.aLo.value=7/12 := by
        simp [aLo,endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      have hU : a.aHi.value=7/12 := by
        simp [aHi,endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      apply side_endpoint_lower ⟨hd.1,hd.2.1⟩
      · simpa [hL,hx] using hl
      · simpa [hU,hx] using hu
  | false =>
      have hX := hmode.resolve_left (by simp [hs])
      have hf := a.circleFacts ha hs hxy
      have hc : x=circleX a.data.shift a.radiusExpr.value y ∧
          (∀ z ∈ Icc a.bLo.value a.bHi.value,
            0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2) := by
        simpa [SupportDomain,hs] using hd.2.2
      have hL := circle_branch hf.lower_shift hf.lower_circle
      have hU := circle_branch hf.upper_shift hf.upper_circle
      rw [hc.1]
      exact circle_endpoints_lower hX hc.2 ⟨hd.1,hd.2.1⟩
        (by simpa [← hL] using hl) (by simpa [← hU] using hu)

/-- If `Y - X r ≥ 0` at the ratios of both endpoints, `X x + Y y` is at least its value at the
lower endpoint at every state of the arc. -/
theorem lower_endpoint {a : PreparedArc} (ha : a.NumericValid)
    {x y X Y : ℝ} (hxy : a.data.Contains a.radius x y)
    (hl : 0 ≤ Y-X*a.ratioLo.value) (hu : 0 ≤ Y-X*a.ratioHi.value) :
    X*a.aLo.value+Y*a.bLo.value ≤ X*x+Y*y := by
  have hd := a.supportDomain ha hxy
  cases hs : a.data.side with
  | true =>
      have hx : x=7/12 := by simpa [SupportDomain,hs] using hd.2.2
      have hL : a.aLo.value=7/12 := by
        simp [aLo,endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      have hY : 0 ≤ Y := by
        simpa [ratioLo,hs,ScalarExpr.value,ScalarExpr.eval] using hl
      have hm := mul_le_mul_of_nonneg_left hd.1 hY
      rw [hx,hL]
      linarith
  | false =>
      have hf := a.circleFacts ha hs hxy
      have hc : x=circleX a.data.shift a.radiusExpr.value y ∧
          (∀ z ∈ Icc a.bLo.value a.bHi.value,
            0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2) := by
        simpa [SupportDomain,hs] using hd.2.2
      have hL := circle_branch hf.lower_shift hf.lower_circle
      have hh := circle_lower_endpoint hc.2 ⟨hd.1,hd.2.1⟩
        (by rwa [ratioLo_value hf hs] at hl)
        (by rwa [ratioHi_value hf hs] at hu)
      rw [← hL,← hc.1] at hh
      exact hh

/-- If `Y - X r ≤ 0` at the ratios of both endpoints, `X x + Y y` is at least its value at the
upper endpoint at every state of the arc. -/
theorem upper_endpoint {a : PreparedArc} (ha : a.NumericValid)
    {x y X Y : ℝ} (hxy : a.data.Contains a.radius x y)
    (hl : Y-X*a.ratioLo.value ≤ 0) (hu : Y-X*a.ratioHi.value ≤ 0) :
    X*a.aHi.value+Y*a.bHi.value ≤ X*x+Y*y := by
  have hd := a.supportDomain ha hxy
  cases hs : a.data.side with
  | true =>
      have hx : x=7/12 := by simpa [SupportDomain,hs] using hd.2.2
      have hU : a.aHi.value=7/12 := by
        simp [aHi,endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      have hY : Y ≤ 0 := by
        simpa [ratioHi,hs,ScalarExpr.value,ScalarExpr.eval] using hu
      have hm := mul_le_mul_of_nonpos_left hd.2.1 hY
      rw [hx,hU]
      linarith
  | false =>
      have hf := a.circleFacts ha hs hxy
      have hc : x=circleX a.data.shift a.radiusExpr.value y ∧
          (∀ z ∈ Icc a.bLo.value a.bHi.value,
            0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2) := by
        simpa [SupportDomain,hs] using hd.2.2
      have hU := circle_branch hf.upper_shift hf.upper_circle
      have hh := circle_upper_endpoint hc.2 ⟨hd.1,hd.2.1⟩
        (by rwa [ratioLo_value hf hs] at hl)
        (by rwa [ratioHi_value hf hs] at hu)
      rw [← hU,← hc.1] at hh
      exact hh

end SquaresInCircles.Eight.Arithmetic.PreparedArc

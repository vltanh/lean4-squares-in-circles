module

public import SquaresInCircles.Eight.Arithmetic.SourceSupport

/-!
# Target-state support on the complete closed tangent arc

The coefficients may depend on the angle.  These lemmas are pointwise in the
coefficients and therefore also apply to the Taylor parameter expressions.
-/

@[expose] public section
open Set

namespace SquaresInCircles.Eight.Arithmetic.PreparedArc

theorem ratioLo_value {a : PreparedArc} {x y : ℝ}
    (hf : a.CircleFacts x y) (hs : a.data.side=false) :
    a.ratioLo.value = circleRatio a.data.shift a.radiusExpr.value a.bLo.value := by
  have he := circle_branch hf.lower_shift hf.lower_circle
  simp only [ratioLo,hs,if_false]
  change (a.bLo.value-(a.data.shift : ℝ))/(a.aLo.value-(a.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

theorem ratioHi_value {a : PreparedArc} {x y : ℝ}
    (hf : a.CircleFacts x y) (hs : a.data.side=false) :
    a.ratioHi.value = circleRatio a.data.shift a.radiusExpr.value a.bHi.value := by
  have he := circle_branch hf.upper_shift hf.upper_circle
  simp only [ratioHi,hs,if_false]
  change (a.bHi.value-(a.data.shift : ℝ))/(a.aHi.value-(a.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

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
      nlinarith only [hm,hx,hL]
  | false =>
      have hf := a.circleFacts ha hs hxy
      have hc : x=circleX a.data.shift a.radiusExpr.value y ∧
          (∀ z ∈ Icc a.bLo.value a.bHi.value,
            0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2) := by
        simpa [SupportDomain,hs] using hd.2.2
      have hL := circle_branch hf.lower_shift hf.lower_circle
      have hh := circle_lower_endpoint hc.2 ⟨hd.1,hd.2.1⟩
        (by simpa [ratioLo_value hf hs] using hl)
        (by simpa [ratioHi_value hf hs] using hu)
      simpa [← hL,← hc.1] using hh

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
      nlinarith only [hm,hx,hU]
  | false =>
      have hf := a.circleFacts ha hs hxy
      have hc : x=circleX a.data.shift a.radiusExpr.value y ∧
          (∀ z ∈ Icc a.bLo.value a.bHi.value,
            0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2) := by
        simpa [SupportDomain,hs] using hd.2.2
      have hU := circle_branch hf.upper_shift hf.upper_circle
      have hh := circle_upper_endpoint hc.2 ⟨hd.1,hd.2.1⟩
        (by simpa [ratioLo_value hf hs] using hl)
        (by simpa [ratioHi_value hf hs] using hu)
      simpa [← hU,← hc.1] using hh

theorem circle_majorant_lower {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=false) {x y X Y h : ℝ}
    (hxy : a.data.Contains a.radius x y) (hh : 0 < h) :
    (a.data.shift : ℝ)*(X+Y)-a.radiusExpr.value*radicalMajorant h (X^2+Y^2) ≤
      X*x+Y*y := by
  have hf := a.circleFacts ha hs hxy
  have hρ : 0 ≤ a.radiusExpr.value := by
    rw [radiusExpr_value]
    split_ifs <;> positivity
  exact full_circle_majorant_lower hρ hh hf.point_circle

end SquaresInCircles.Eight.Arithmetic.PreparedArc

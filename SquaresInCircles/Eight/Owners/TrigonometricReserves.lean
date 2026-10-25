module

public import SquaresInCircles.Eight.Frames.Signed.Coordinates

/-!
# Eight squares: trigonometric reserves of the local transports

Each rational reserve comes from a Taylor bound at an endpoint of the interval and monotonicity on
the whole interval (`transport_trig`, `short_transport_trig`, `cos_add_reciprocal_ge_two`,
`flat_core_corner_reserve`, `primary_cap_endpoint_reserve`), with the closed forms of the edge
width (`edgeWidth_positive_formula`, `edgeWidth_negative_formula`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

theorem transport_trig {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    7648/10000 < Real.cos x ∧ Real.cos x ≤ 1 ∧
    0 ≤ Real.sin x ∧ Real.sin x < 6443/10000 ∧
    Real.sin x < Real.cos x := by
  have hb := trig_bracket (l := 0) (u := (7/10 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hcos : (7648/10000 : ℝ) <
      1-(7/10 : ℝ)^2/2+(7/10 : ℝ)^4/24-(7/10 : ℝ)^6/720 := by norm_num
  have hsin : (7/10 : ℝ)-(7/10 : ℝ)^3/6+(7/10 : ℝ)^5/120 <
      (6443/10000 : ℝ) := by norm_num
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2, Real.pi_gt_three])
  exact ⟨hcos.trans_le hb.2.2.1, Real.cos_le_one _, hs0,
    hb.2.1.trans_lt hsin, by linarith [hb.2.1,hb.2.2.1]⟩

theorem transport_trig_coarse {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    3/4 < Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x < 13/20 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
  exact ⟨by linarith,hs0,by linarith⟩

theorem transport_cos_pos {x : ℝ} (hx : |x| ≤ (7/10 : ℝ)) :
    0 < Real.cos x := by
  obtain ⟨hc,hs⟩ := small_angle hx
  norm_num at hc
  linarith

theorem short_transport_trig {x : ℝ} (hx : x ∈ Icc 0 (9/20 : ℝ)) :
    0 < Real.cos x ∧ 0 ≤ Real.sin x ∧ 0 ≤ Real.tan x ∧ Real.tan x < 1/2 := by
  have hb := trig_bracket (l := 0) (u := (9/20 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hc : 0 < Real.cos x := transport_cos_pos (by
    rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hs : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2, Real.pi_gt_three])
  have hr : (9/20 : ℝ)-(9/20 : ℝ)^3/6+(9/20 : ℝ)^5/120 <
      (1-(9/20 : ℝ)^2/2+(9/20 : ℝ)^4/24-(9/20 : ℝ)^6/720)/2 := by
    norm_num
  refine ⟨hc,hs,?_,?_⟩
  · rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hs hc.le
  · rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
    linarith [hb.2.1,hb.2.2.1]

theorem cos_add_reciprocal_ge_two {x : ℝ} (hx : 0 < Real.cos x) :
    2 ≤ Real.cos x + 1/Real.cos x := by
  have he : Real.cos x + 1/Real.cos x - 2 = (Real.cos x-1)^2/Real.cos x := by
    field_simp
    ring
  have hp : 0 ≤ (Real.cos x-1)^2/Real.cos x := div_nonneg (sq_nonneg _) hx.le
  linarith

theorem edgeWidth_positive_formula {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    edgeWidth x=(1+Real.cos x+Real.sin x)/2 := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hx
  simp only [edgeWidth,pairWidth,abs_of_nonneg (show 0 ≤ Real.cos x by linarith),
    abs_of_nonneg hs0]
  ring

theorem edgeWidth_negative_formula {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    edgeWidth (-x)=(1+Real.cos x+Real.sin x)/2 := by
  rw [edgeWidth_neg,edgeWidth_positive_formula hx]

theorem flat_core_corner_reserve :
    (13/12 : ℝ)^2+(183/200 : ℝ)^2 < 5/2 := by norm_num

theorem primary_cap_endpoint_reserve :
    (183/200 : ℝ) <
      (1-(9/20 : ℝ)^2/2)/2+(13/12 : ℝ)*((9/20 : ℝ)-(9/20 : ℝ)^3/6) := by
  norm_num

end SquaresInCircles.Eight
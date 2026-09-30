module
public import SquaresInCircles.Six.Analytic.EndpointReduction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Vertex minorant for the fixed-central-weight pair

The fixed-pair line has coefficients 18/25 and 13/50, not 73/100 and 13/50.
After the diamond change of coordinates the new coefficients are 46/100 and
98/100. The old vertex minorant cannot simply be reused: its coarse constants
lose the middle endpoint reserve after this change.

Use the analytic candidate bounds R <= 8443/5000 and rho >= 1391/1250.
The resulting minorant has coefficients 9/25 and 77/100. Concavity in the
angle and minimization on the two actual diamond boundary segments reduce it
to two explicit quartics. Their common middle endpoint is
6588879/8575000000 > 0. No subdivision or numerical truth premise is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def fixedVertexMinorant (x y t : ℝ) : ℝ :=
  (9/25)*max x y+(77/100)*y+
    (3/2+y/2)*Real.cos t+(1/2+y/2)*Real.sin t-
    (8443/5000)*(1+y)+1391/1250-1

private def fixedPenalty (t : ℝ) : ℝ := 4593/5000-(Real.cos t+Real.sin t)/2
private def fixedBase (t : ℝ) : ℝ := (3/2)*Real.cos t+(1/2)*Real.sin t-7879/5000

private lemma fixed_minorant_decomposition (x y t : ℝ) :
    fixedVertexMinorant x y t=fixedBase t+(9/25)*max x y-fixedPenalty t*y := by
  dsimp [fixedVertexMinorant,fixedBase,fixedPenalty]
  ring

private lemma fixed_penalty_bounds {t : ℝ} (ht : 2/7≤t ∧ t≤3/4) :
    0≤fixedPenalty t ∧ fixedPenalty t≤9/25 := by
  have ht0 : 0≤t := by linarith [ht.1]
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2)
    (show 0≤3/4+t by linarith [ht.1])
  have hcoef : 0≤1/2-t/2-t^2/6 := by nlinarith [ht.2]
  have hp := mul_nonneg ht0 hcoef
  have hs := Real.sin_ge_sub_cube ht0
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hlow : 1+t/2≤Real.cos t+Real.sin t := by nlinarith only [hp,hs,hc]
  have hhigh : Real.cos t+Real.sin t≤3/2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.cos t-Real.sin t)]
  dsimp [fixedPenalty]
  constructor <;> linarith [hlow,hhigh,ht.1]

private lemma fixed_base_left_positive : 0<fixedBase (29/100) := by
  have hs := Real.sin_ge_sub_cube (x := (29:ℝ)/100) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (29:ℝ)/100)
  dsimp [fixedBase]
  nlinarith only [hs,hc]

private def fixedSmallBoundary (x : ℝ) : ℝ :=
  (3/2+x/2)*(1-(2/7+x)^2/2)+
    (1/2+x/2)*((2/7+x)-(2/7+x)^3/6)-7879/5000-(2793/5000)*x

private def fixedLargeBoundary (x : ℝ) : ℝ :=
  (43/25-x/2)*(1-(2/7+x)^2/2)+
    (18/25-x/2)*((2/7+x)-(2/7+x)^3/6)-
    7879/5000+(9/25)*x-(4593/5000)*(11/25-x)

private lemma fixed_small_boundary_positive {x : ℝ} (hx : 0≤x ∧ x≤11/50) :
    0<fixedSmallBoundary x := by
  have hid : fixedSmallBoundary x=
      quartic (-2067/35000) (10449/35000) (-5/28) (-13/42) (-1/12) (2/7+x) := by
    dsimp [fixedSmallBoundary,quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (2:ℝ)/7) (u := (177:ℝ)/350)
  · norm_num
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT : 0≤2/7+x := by linarith [hx.1]
    nlinarith [sq_nonneg (2/7+x)]

private lemma fixed_large_boundary_positive {x : ℝ} (hx : 11/50≤x ∧ x≤11/25) :
    0<fixedLargeBoundary x := by
  have hid : fixedLargeBoundary x=
      quartic (-52767/109375) (57451/35000) (-501/350)
        (223/2100) (1/12) (2/7+x) := by
    dsimp [fixedLargeBoundary,quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (177:ℝ)/350) (u := (127:ℝ)/175)
  · norm_num
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT0 : 0≤2/7+x := by linarith [hx.1]
    have hT1 : 2/7+x≤3/4 := by linarith [hx.2]
    have hsq := mul_nonneg (sub_nonneg.mpr hT1)
      (show 0≤3/4+(2/7+x) by linarith)
    nlinarith

private lemma fixed_minorant_left {x y : ℝ} (hy : 0≤y) :
    0<fixedVertexMinorant x y (29/100) := by
  have hp := fixed_penalty_bounds (t := (29:ℝ)/100) (by constructor <;> norm_num)
  have hM := mul_nonneg (show (0:ℝ)≤9/25 by norm_num)
    (sub_nonneg.mpr (le_max_right x y))
  have hY := mul_nonneg (sub_nonneg.mpr hp.2) hy
  rw [fixed_minorant_decomposition]
  nlinarith only [fixed_base_left_positive,hM,hY]

private lemma fixed_minorant_right {x y : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hdiamond : x+y≤11/25) :
    0<fixedVertexMinorant x y (2/7+x) := by
  let t := 2/7+x
  have hxb : x≤11/25 := by linarith
  have ht : 2/7≤t ∧ t≤3/4 := by dsimp [t]; constructor <;> linarith
  have hp := fixed_penalty_bounds ht
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube (show 0≤t by linarith [ht.1])
  rw [fixed_minorant_decomposition]
  change 0<fixedBase t+(9/25)*max x y-fixedPenalty t*y
  by_cases hsmall : x≤11/50
  · have hM1 := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr (le_max_left x y))
    have hM2 := mul_nonneg hp.1 (sub_nonneg.mpr (le_max_right x y))
    have hC := mul_le_mul_of_nonneg_left hc (show 0≤3/2+x/2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs (show 0≤1/2+x/2 by linarith)
    have hpositive := fixed_small_boundary_positive ⟨hx,hsmall⟩
    have hid : fixedSmallBoundary x=(3/2+x/2)*(1-t^2/2)+
        (1/2+x/2)*(t-t^3/6)-7879/5000-(2793/5000)*x := rfl
    rw [hid] at hpositive
    dsimp [fixedBase,fixedPenalty] at *
    nlinarith only [hM1,hM2,hC,hS,hpositive]
  · have hM := mul_nonneg (show (0:ℝ)≤9/25 by norm_num)
      (sub_nonneg.mpr (le_max_left x y))
    have hY := mul_nonneg hp.1 (show 0≤11/25-x-y by linarith)
    have hC := mul_le_mul_of_nonneg_left hc (show 0≤43/25-x/2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs (show 0≤18/25-x/2 by linarith)
    have hpositive := fixed_large_boundary_positive ⟨(lt_of_not_ge hsmall).le,hxb⟩
    have hid : fixedLargeBoundary x=(43/25-x/2)*(1-t^2/2)+
        (18/25-x/2)*(t-t^3/6)-7879/5000+(9/25)*x-(4593/5000)*(11/25-x) := rfl
    rw [hid] at hpositive
    dsimp [fixedBase,fixedPenalty] at *
    nlinarith only [hM,hY,hC,hS,hpositive]

/-- Positivity on the entire diamond and its full angle interval. -/
theorem fixedVertexMinorant_positive {x y t : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hdiamond : x+y≤11/25)
    (ht : 29/100≤t ∧ t≤2/7+x) : 0<fixedVertexMinorant x y t := by
  have hleft := fixed_minorant_left (x := x) hy
  have hright := fixed_minorant_right hx hy hdiamond
  have hh := trig_lower_of_endpoints
    (A := 3/2+y/2) (B := 1/2+y/2)
    (C := (8443/5000)*(1+y)-1391/1250+1-(9/25)*max x y-(77/100)*y)
    (l := (29:ℝ)/100) (u := 2/7+x)
    (by linarith) (by linarith) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ht
    (by dsimp [fixedVertexMinorant] at hleft; linarith)
    (by dsimp [fixedVertexMinorant] at hright; linarith)
  dsimp [fixedVertexMinorant]
  linarith

end SquaresInCircles.Six.Analytic

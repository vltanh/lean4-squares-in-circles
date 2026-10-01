import SquaresInCircles.Six.Analytic.LowDiagonalStress

/-!
# The low diagonal: the corners

`lowFrozen` is positive at the four corners `(v, d) = (0, 0)`, `(0, 1/2)`,
`(2/3, 0)` and `(2/3, 1/2)` of the angle rectangle, for all centres in their
charts and in the central box. At the first three corners both forces take the
far-vertex bound, with rational bounds for their lengths checked by squaring.
At `(2/3, 1/2)` the force whose direction depends on the angles satisfies the
slope condition of the cap bound and takes that bound. Taylor polynomials
bracket `cos` and `sin` at `1/2`, `2/3` and `7/6`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def lowNormFixed (ds : Bool) : ℝ := if ds then 4696/10000 else 5061/10000
def lowNormZero (ds : Bool) : ℝ := if ds then 4255/10000 else 3983/10000
def lowNormHalf (ds : Bool) : ℝ := if ds then 5056/10000 else 4827/10000
def lowNormFar (ds : Bool) : ℝ := if ds then 5265/10000 else 5046/10000

lemma low_half_bracket :
    (8775:ℝ)/10000≤Real.cos (1/2) ∧ Real.cos (1/2)≤878/1000 ∧
    (4794:ℝ)/10000≤Real.sin (1/2) ∧ Real.sin (1/2)≤4795/10000 := by
  have hcl := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hcu := Seven.cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hsl := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)
  norm_num at hcl hcu hsl hsu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma low_mixed_bracket :
    (3931:ℝ)/10000≤Real.cos (7/6) ∧ Real.cos (7/6)≤2/5 ∧
    (9194:ℝ)/10000≤Real.sin (7/6) ∧ Real.sin (7/6)≤9201/10000 := by
  have hcl := Seven.cos_lower_six (x := (7:ℝ)/6) (by norm_num)
  have hcu := Seven.cos_upper_four (x := (7:ℝ)/6) (by norm_num)
  have hsl := Seven.sin_lower_seven (x := (7:ℝ)/6) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (7:ℝ)/6) (by norm_num)
  norm_num at hcl hcu hsl hsu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma low_fixed_norm_bound (ds : Bool) :
    0≤lowNormFixed ds ∧ (lowFixed ds)^2+(lowMu ds)^2≤(lowNormFixed ds)^2 := by
  cases ds <;> norm_num [lowNormFixed,lowFixed,lowAlpha,lowBeta,lowMu]

lemma low_secondary_corner_zero (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds 0 0 aw bw ad bd cx cy := by
  have h := low_vertex_endpoint_lower ds (v := 0) (d := 0)
    (L0 := lowNormFixed ds) (L := lowNormZero ds)
    (X := lowBeta ds+lowAlpha ds) (Y := 0)
    hW hD hc (by norm_num)
    (low_fixed_norm_bound ds).1
    (by cases ds <;> norm_num [lowNormZero]) (low_fixed_norm_bound ds).2
    (by cases ds <;> norm_num [lowVariable,lowAlpha,lowBeta,lowMu,lowNormZero])
    (by cases ds <;> norm_num [lowAlpha,lowBeta]) (by norm_num)
    (by norm_num) (by norm_num)
  cases ds <;> norm_num [lowAlpha,lowBeta,lowMu,lowNormFixed,lowNormZero] at h <;> linarith

lemma low_secondary_corner_half (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds 0 (1/2) aw bw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := low_half_bracket
  have h := low_vertex_endpoint_lower ds (v := 0) (d := (1:ℝ)/2)
    (L0 := lowNormFixed ds) (L := lowNormHalf ds)
    (X := lowBeta ds+lowAlpha ds*Real.cos (1/2))
    (Y := lowAlpha ds*Real.sin (1/2))
    hW hD hc (by simp only [zero_add]; linarith)
    (low_fixed_norm_bound ds).1
    (by cases ds <;> norm_num [lowNormHalf]) (low_fixed_norm_bound ds).2
    (by cases ds <;> norm_num [lowVariable,lowAlpha,lowBeta,lowMu,lowNormHalf] <;> nlinarith)
    (by cases ds <;> dsimp [lowAlpha,lowBeta] <;> nlinarith)
    (by cases ds <;> dsimp [lowAlpha] <;> nlinarith)
    (by norm_num) (by norm_num)
  cases ds <;> norm_num [lowAlpha,lowBeta,lowMu,lowNormFixed,lowNormHalf] at h <;> linarith

lemma low_secondary_corner_far (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds (2/3) 0 aw bw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := two_thirds_endpoint_bracket
  have h := low_vertex_endpoint_lower ds (v := (2:ℝ)/3) (d := 0)
    (L0 := lowNormFixed ds) (L := lowNormFar ds)
    (X := lowBeta ds*Real.cos (2/3)+lowAlpha ds) (Y := 0)
    hW hD hc (by simp only [add_zero]; linarith)
    (low_fixed_norm_bound ds).1
    (by cases ds <;> norm_num [lowNormFar]) (low_fixed_norm_bound ds).2
    (by cases ds <;> norm_num [lowVariable,lowAlpha,lowBeta,lowMu,lowNormFar] <;> nlinarith)
    (by cases ds <;> dsimp [lowAlpha,lowBeta] <;> nlinarith) (by norm_num)
    (by norm_num)
    (by cases ds <;> norm_num [lowAlpha,lowBeta] <;> linarith)
  cases ds <;> norm_num [lowAlpha,lowBeta,lowMu,lowNormFixed,lowNormFar] at h <;> linarith

lemma low_secondary_corner_mixed (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds (2/3) (1/2) aw bw ad bd cx cy := by
  obtain ⟨hvcl,hvcu,hvsl,hvsu⟩ := two_thirds_endpoint_bracket
  obtain ⟨hdcl,hdcu,hdsl,hdsu⟩ := low_half_bracket
  obtain ⟨hqcl,hqcu,hqsl,hqsu⟩ := low_mixed_bracket
  have hq : (2:ℝ)/3+1/2=7/6 := by norm_num
  have hroot := mul_le_mul
    (show rho0+1/2≤1613/1000 by linarith [rho0_upper]) hqcu
    (show 0≤Real.cos (7/6) by linarith) (by norm_num : (0:ℝ)≤1613/1000)
  have hslope : (rho0+1/2)*(lowMu ds*Real.cos (2/3+1/2))≤
      (lowVariable ds+lowMu ds*Real.sin (2/3+1/2))/2 := by
    rw [hq]
    cases ds <;> dsimp [lowMu,lowVariable,lowAlpha,lowBeta] <;> nlinarith
  have h := low_cap_endpoint_lower ds (v := (2:ℝ)/3) (d := (1:ℝ)/2)
    (L0 := lowNormFixed ds)
    (X := lowBeta ds*Real.cos (2/3)+lowAlpha ds*Real.cos (1/2)) (Y := 0)
    hW hD hc (by rw [hq]; linarith) (by rw [hq]; linarith)
    (low_fixed_norm_bound ds).1 (low_fixed_norm_bound ds).2 hslope
    (by cases ds <;> dsimp [lowAlpha,lowBeta] <;> nlinarith) (by norm_num)
    le_rfl
    (by cases ds <;> dsimp [lowAlpha,lowBeta] <;> nlinarith)
  rw [hq] at h
  cases ds <;> norm_num [lowAlpha,lowBeta,lowMu,lowVariable,lowFixed,lowNormFixed] at h <;> linarith

/-- `lowFrozen` is positive at the four corners of `[0, 2/3] × [0, 1/2]`. -/
theorem low_secondary_corners (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds 0 0 aw bw ad bd cx cy ∧
    0<lowFrozen ds 0 (1/2) aw bw ad bd cx cy ∧
    0<lowFrozen ds (2/3) 0 aw bw ad bd cx cy ∧
    0<lowFrozen ds (2/3) (1/2) aw bw ad bd cx cy :=
  ⟨low_secondary_corner_zero ds hW hD hc,low_secondary_corner_half ds hW hD hc,
    low_secondary_corner_far ds hW hD hc,low_secondary_corner_mixed ds hW hD hc⟩

end SquaresInCircles.Six.Analytic

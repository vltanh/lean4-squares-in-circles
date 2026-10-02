import research.seven.lean.Basic

/-! A and the algebraic part of K: no Bernstein coefficients or angle grid. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def markerA (x : ℝ) : ℝ := 1-x^2
def markerH (x : ℝ) : ℝ := 9-8*x-4*x^2
def markerP (x : ℝ) : ℝ := 676*(1-x^2)^3-9*x^2*(9-8*x-4*x^2)^3

def markerPeak (x : ℝ) : ℝ := 9*x^2*(9-6*x)^3
def markerPeakD (x : ℝ) : ℝ := 54*x*(9-6*x)^2*(3-5*x)

def reservedPeak (x : ℝ) : ℝ := 9*(x+1/8)^2*(9-7*x)^3
def reservedPeakD (x : ℝ) : ℝ := 9*(x+1/8)*(9-7*x)^2*(123/8-35*x)

lemma marker_domains {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < markerA x ∧ markerA x ≤ 1 ∧ 0 < markerH x := by
  dsimp [markerA,markerH]
  have hx2 : x^2 ≤ (3/4 : ℝ)^2 := by nlinarith
  exact ⟨by nlinarith,by nlinarith [sq_nonneg x],by nlinarith⟩

lemma marker_ratio {x : ℝ} (hx : 0 ≤ x) :
    markerH x ≤ (9-6*x)*markerA x := by
  have hid : (9-6*x)*markerA x-markerH x =
      x*(6*(x-5/12)^2+23/24) := by dsimp [markerA,markerH]; ring
  have hm : 0 ≤ x*(6*(x-5/12)^2+23/24) := by positivity
  linarith

lemma reserved_ratio {x : ℝ} (hx : 0 ≤ x) :
    markerH x ≤ (9-7*x)*markerA x := by
  have hid : (9-7*x)*markerA x-markerH x =
      x*(7*(x-5/14)^2+3/28) := by dsimp [markerA,markerH]; ring
  have hm : 0 ≤ x*(7*(x-5/14)^2+3/28) := by positivity
  linarith

lemma markerPeak_hasDeriv (x : ℝ) : HasDerivAt markerPeak (markerPeakD x) x := by
  have hd : DifferentiableAt ℝ markerPeak x := by unfold markerPeak; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [markerPeak,markerPeakD] <;> ring

lemma reservedPeak_hasDeriv (x : ℝ) : HasDerivAt reservedPeak (reservedPeakD x) x := by
  have hd : DifferentiableAt ℝ reservedPeak x := by unfold reservedPeak; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [reservedPeak,reservedPeakD] <;> ring

lemma markerPeak_lt {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) : markerPeak x < 676 := by
  have hm : markerPeak x ≤ markerPeak (3/5) := by
    apply le_at_peak (d := markerPeakD)
      (show (0 : ℝ) ≤ 3/5 ∧ (3/5 : ℝ) ≤ 3/4 by constructor <;> norm_num) hx
    · unfold markerPeak; fun_prop
    · exact markerPeak_hasDeriv
    · intro y hy
      have hsign : 0 ≤ 3-5*y := by linarith [hy.2]
      dsimp [markerPeakD]
      positivity
    · intro y hy
      have hsign : 3-5*y ≤ 0 := by linarith [hy.1]
      have hpos : 0 ≤ 54*y*(9-6*y)^2 := by
        have hy0 : 0 ≤ y := by linarith [hy.1]
        positivity
      exact mul_nonpos_of_nonneg_of_nonpos hpos hsign
  have hc : markerPeak (3/5) < (676 : ℝ) := by norm_num [markerPeak]
  exact hm.trans_lt hc

lemma reservedPeak_lt {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) : reservedPeak x < 676 := by
  have hm : reservedPeak x ≤ reservedPeak (123/280) := by
    apply le_at_peak (d := reservedPeakD)
      (show (0 : ℝ) ≤ 123/280 ∧ (123/280 : ℝ) ≤ 3/4 by constructor <;> norm_num) hx
    · unfold reservedPeak; fun_prop
    · exact reservedPeak_hasDeriv
    · intro y hy
      have hsign : 0 ≤ 123/8-35*y := by linarith [hy.2]
      have hy0 : 0 ≤ y+1/8 := by linarith [hy.1]
      dsimp [reservedPeakD]
      positivity
    · intro y hy
      have hsign : 123/8-35*y ≤ 0 := by linarith [hy.1]
      have hpos : 0 ≤ 9*(y+1/8)*(9-7*y)^2 := by
        have hy0 : 0 ≤ y+1/8 := by linarith [hy.1]
        positivity
      exact mul_nonpos_of_nonneg_of_nonpos hpos hsign
  have hc : reservedPeak (123/280) < (676 : ℝ) := by norm_num [reservedPeak]
  exact hm.trans_lt hc

lemma marker_polynomial_pos {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < markerP x := by
  have hd := marker_domains hx
  have hc := pow_le_pow_left₀ hd.2.2.le (marker_ratio hx.1) 3
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 9*x^2 by positivity)
  have hp := mul_lt_mul_of_pos_left (markerPeak_lt hx) (pow_pos hd.1 3)
  dsimp [markerPeak,markerP,markerA,markerH] at *
  nlinarith

/-- The quantitative form used by K before taking any square roots. -/
lemma reserved_curvature_squared {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    9*(x+1/8)^2*(markerH x)^3 < 676*(markerA x)^3 := by
  have hd := marker_domains hx
  have hc := pow_le_pow_left₀ hd.2.2.le (reserved_ratio hx.1) 3
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 9*(x+1/8)^2 by positivity)
  have hp := mul_lt_mul_of_pos_left (reservedPeak_lt hx) (pow_pos hd.1 3)
  dsimp [reservedPeak] at hp
  nlinarith

end SquaresInCircles.Seven.Human

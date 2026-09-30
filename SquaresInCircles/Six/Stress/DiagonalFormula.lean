import SquaresInCircles.Six.Stress.PairLowerBound

/-!
# Exact reduction of the remaining diagonal contribution

The force direction and length are derived algebraically. The cap branch is
selected by 2 R |sin delta| <= 1, not by coordinate dominance. Dominance is
proved separately only to identify the larger coordinate in the support.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

def diagonalBeta (w s : ℝ) : ℝ := (w-s)/2
def diagonalDelta (w s d : ℝ) : ℝ := d-Real.pi/4-(w+s)/2
def diagonalK : ℝ := 2*Six.hStar*mStar

def diagonalCap (w s d : ℝ) : ℝ :=
  diagonalK*((1-rhoStar)*Real.cos (diagonalBeta w s)+rhoStar*Real.sin (diagonalBeta w s))*
    Real.cos (diagonalDelta w s d)

def diagonalVertex (w s d : ℝ) : ℝ :=
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  diagonalK*((3*Real.cos b-Real.sin b)*Real.cos z/2+
    (Real.cos b-Real.sin b)*|Real.sin z|/2-Six.radius*(Real.cos b-Real.sin b))

def DiagonalDomain (w s d : ℝ) : Prop :=
  (-11/25≤w ∧ w≤2/5) ∧ (-2/5≤s ∧ s≤11/25) ∧ (1/2≤d ∧ d≤Real.pi/4)

lemma diagonalK_pos : 0<diagonalK := by
  dsimp [diagonalK]
  positivity

lemma diagonal_parameters {w s d : ℝ} (h : DiagonalDomain w s d) :
    (-11/25≤diagonalBeta w s ∧ diagonalBeta w s≤2/5) ∧
    |diagonalDelta w s d|≤71/100 ∧
    (0≤d-w ∧ d-w≤Real.pi/2) ∧ (0≤d-s ∧ d-s≤Real.pi/2) := by
  rcases h with ⟨hw,hs,hd⟩
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [diagonalBeta]
    constructor <;> linarith [hw.1,hw.2,hs.1,hs.2]
  · apply abs_le.mpr
    dsimp [diagonalDelta]
    constructor <;> linarith [hw.1,hw.2,hs.1,hs.2,hd.1,hd.2,Real.pi_lt_d4]
  · constructor <;> linarith [hw.1,hw.2,hd.1,hd.2,Real.pi_gt_d2]
  · constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2]

lemma abs_sin_le_abs_value (x : ℝ) : |Real.sin x|≤|x| := by
  simpa using Real.abs_sin_sub_sin_le x 0

lemma cos_lower_from_abs {x a : ℝ} (ha : 0≤a) (hx : |x|≤a) : 1-a^2/2≤Real.cos x := by
  have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [sq_abs] at hsq
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

lemma diagonal_trig_signs {w s d : ℝ} (h : DiagonalDomain w s d) :
    0<Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s) ∧
    0<Real.cos (diagonalDelta w s d) ∧
    |Real.sin (diagonalDelta w s d)|≤Real.cos (diagonalDelta w s d) := by
  have hp := diagonal_parameters h
  have hb : |diagonalBeta w s|≤11/25 := abs_le.mpr ⟨hp.1.1,by linarith [hp.1.2]⟩
  have hcb := cos_lower_from_abs (by norm_num : (0:ℝ)≤11/25) hb
  have hsb := (abs_sin_le_abs_value (diagonalBeta w s)).trans hb
  have hcd := cos_lower_from_abs (by norm_num : (0:ℝ)≤71/100) hp.2.1
  have hsd := (abs_sin_le_abs_value (diagonalDelta w s d)).trans hp.2.1
  have hsb' := (abs_le.mp hsb).2
  exact ⟨by linarith,by linarith,by linarith⟩

lemma halfWidth_first_quadrant {x : ℝ} (hx : 0≤x ∧ x≤Real.pi/2) :
    angularWidth x=(Real.cos x+Real.sin x)/2 := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
  simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]

lemma diagonal_force_formula (w s d : ℝ) :
    diagonalLocalForce w s d=
      (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*Real.cos (diagonalDelta w s d),
       -diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*Real.sin (diagonalDelta w s d)) := by
  have hw : d-w=Real.pi/4+diagonalDelta w s d-diagonalBeta w s := by
    dsimp [diagonalDelta,diagonalBeta]
    ring
  have hs : d-s=Real.pi/4+diagonalDelta w s d+diagonalBeta w s := by
    dsimp [diagonalDelta,diagonalBeta]
    ring
  have hsin : Real.sin (Real.pi/4)=Six.hStar := by simp [Six.hStar,halfDiagonal]
  have hcos : Real.cos (Real.pi/4)=Six.hStar := by simp [Six.hStar,halfDiagonal]
  apply Prod.ext <;>
    simp only [diagonalLocalForce,hw,hs,Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,
      hsin,hcos,diagonalK] <;> ring

lemma diagonal_threshold_formula {w s d : ℝ} (h : DiagonalDomain w s d) :
    mStar*(angularWidth (d-w)+angularWidth (d-s))=
      diagonalK*Real.cos (diagonalBeta w s)*Real.cos (diagonalDelta w s d) := by
  have hp := diagonal_parameters h
  rw [halfWidth_first_quadrant hp.2.2.1,halfWidth_first_quadrant hp.2.2.2]
  have hw : d-w=Real.pi/4+diagonalDelta w s d-diagonalBeta w s := by
    dsimp [diagonalDelta,diagonalBeta]
    ring
  have hs : d-s=Real.pi/4+diagonalDelta w s d+diagonalBeta w s := by
    dsimp [diagonalDelta,diagonalBeta]
    ring
  have hsin : Real.sin (Real.pi/4)=Six.hStar := by simp [Six.hStar,halfDiagonal]
  have hcos : Real.cos (Real.pi/4)=Six.hStar := by simp [Six.hStar,halfDiagonal]
  rw [hw,hs]
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,hsin,hcos,diagonalK]
  ring

lemma diagonal_force_length {w s d : ℝ} (h : DiagonalDomain w s d) :
    Real.sqrt ((diagonalLocalForce w s d).1^2+(diagonalLocalForce w s d).2^2)=
      diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)) := by
  have hscale := mul_pos diagonalK_pos (diagonal_trig_signs h).1
  rw [diagonal_force_formula]
  have hsq :
      (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*Real.cos (diagonalDelta w s d))^2+
      (-diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*Real.sin (diagonalDelta w s d))^2=
      (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)))^2 := by
    linear_combination
      (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)))^2*
        (Real.sin_sq_add_cos_sq (diagonalDelta w s d))
  rw [hsq,Real.sqrt_sq hscale.le]

/-- Exact two-branch expression. The switch is the actual constrained-disk
support switch after the force length has been proved. -/
theorem diagonal_value_formula {w s d : ℝ} (h : DiagonalDomain w s d) :
    diagonalValue w s d=
      if 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
      then diagonalCap w s d else diagonalVertex w s d := by
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let L := diagonalK*(Real.cos b-Real.sin b)
  have hsign := diagonal_trig_signs h
  have hL : 0<L := mul_pos diagonalK_pos hsign.1
  have hx : |(diagonalLocalForce w s d).1|=L*Real.cos z := by
    rw [diagonal_force_formula]
    exact abs_of_pos (mul_pos hL hsign.2.1)
  have hy : |(diagonalLocalForce w s d).2|=L*|Real.sin z| := by
    rw [diagonal_force_formula]
    change |-(L*Real.sin z)|=L*|Real.sin z|
    rw [abs_neg,abs_mul,abs_of_pos hL]
  have horder : |(diagonalLocalForce w s d).2|≤|(diagonalLocalForce w s d).1| := by
    rw [hx,hy]
    exact mul_le_mul_of_nonneg_left hsign.2.2 hL.le
  have hswitch : 2*Six.radius*(L*|Real.sin z|)≤L ↔ 2*Six.radius*|Real.sin z|≤1 := by
    calc
      (2*Six.radius*(L*|Real.sin z|)≤L) ↔ (L*(2*Six.radius*|Real.sin z|)≤L*1) := by ring_nf
      _ ↔ 2*Six.radius*|Real.sin z|≤1 := mul_le_mul_left hL
  rw [diagonalValue,diagonal_threshold_formula h,scalarSupport_max_min,
    min_eq_right horder,max_eq_left horder,diagonal_force_length h,hx,hy]
  change diagonalK*Real.cos b*Real.cos z-
    (if 2*Six.radius*(L*|Real.sin z|)≤L then rhoAt Six.radius*(L*Real.cos z)
     else Six.radius*L-(L*Real.cos z+L*|Real.sin z|)/2)=_
  rw [hswitch]
  by_cases hb : 2*Six.radius*|Real.sin z|≤1
  · rw [if_pos hb,if_pos hb]
    dsimp [diagonalCap,L,b,z,rhoStar]
    ring
  · rw [if_neg hb,if_neg hb]
    dsimp [diagonalVertex,L,b,z]
    ring

end SquaresInCircles.Six.Stress

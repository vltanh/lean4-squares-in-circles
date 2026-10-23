import research.seven.lean.CoarseBoundary
import research.seven.lean.TurnProfiles

/-! E1/E2: the full axial-target support theorem, with switch at pi/6. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def axialLambda (z : ℝ) : ℝ := (3/40)*(1-2*Real.sin z)
def axialU (z : ℝ) : ℝ := Real.cos z-9*axialLambda z
def axialV (z : ℝ) : ℝ := 1-Real.sin z-11*axialLambda z

def axialDefect (A v z : ℝ) : ℝ :=
  1+2*Real.pi/15-(4/5)*z+Real.cos z-
    (A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z)

def axialM (z : ℝ) : ℝ :=
  1091/1600-Real.pi/60-(5/8)*Real.cos z+
    (3*Real.pi/10-131/800)*Real.sin z-(4/5)*z

def axialMD (z : ℝ) : ℝ :=
  (5/8)*Real.sin z+(3*Real.pi/10-131/800)*Real.cos z-4/5

def axialMDD (z : ℝ) : ℝ :=
  (5/8)*Real.cos z-(3*Real.pi/10-131/800)*Real.sin z

lemma small_turn_trig {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    0 ≤ Real.sin z ∧ Real.sin z ≤ 1/2 ∧ (5 : ℝ)/6 < Real.cos z := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,Real.pi_pos])
  have hs1 : Real.sin z ≤ 1/2 := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hz.1,Real.pi_pos]) (by linarith [Real.pi_pos]) hz.2
    simpa only [Real.sin_pi_div_six] using hh
  have hc : Real.sqrt 3/2 ≤ Real.cos z := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
      (by linarith [Real.pi_pos]) hz.2
    simpa only [Real.cos_pi_div_six] using hh
  exact ⟨hs0,hs1,by linarith [sqrt_three_coarse.1]⟩

lemma residual_cone {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    0 < axialU z ∧ axialU z/2 ≤ axialV z ∧ axialV z ≤ (3/5)*axialU z := by
  have hs := small_turn_trig hz
  have hc := Real.cos_le_one z
  have hforce : (29 : ℝ) < 8*Real.sin z+30*Real.cos z := by
    apply Seven.trig_concave_gt (α := (0 : ℝ)) (A := (8 : ℝ))
      (B := (30 : ℝ)) (m := (29 : ℝ)) (l := (0 : ℝ)) (u := Real.pi/6)
      (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_pos]) hz
    · norm_num
    · rw [Real.sin_pi_div_six,Real.cos_pi_div_six]
      linarith [sqrt_three_coarse.1]
  dsimp [axialU,axialV,axialLambda]
  exact ⟨by linarith [hs.1,hs.2.2],by linarith [hs.2.1],by linarith⟩

lemma cone_disk_support {X Y U V : ℝ}
    (hdisk : X^2+Y^2 ≤ (13 : ℝ)/4) (hU : 0 < U)
    (hlo : U/2 ≤ V) (hhi : V ≤ (3/5)*U) :
    U*X+V*Y ≤ (13/8)*U+(4/5)*V := by
  have hV : 0 ≤ V := by linarith
  have hc : 0 ≤ (13/8 : ℝ)*U+(4/5)*V := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hq := mul_nonneg hU.le (sub_nonneg.mpr hhi)
  have hid : ((13/8)*U+(4/5)*V)^2-(13/4)*(U^2+V^2) =
      (261/100)*(V-U/2)*((3/5)*U-V)+
      (271/1000)*U*((3/5)*U-V)+(441/40000)*U^2 := by ring
  have hnorm : (13/4 : ℝ)*(U^2+V^2) ≤ ((13/8)*U+(4/5)*V)^2 := by
    nlinarith [sq_nonneg U]
  exact disk_dot_upper hdisk hc hnorm

lemma axialM_hasDeriv (z : ℝ) : HasDerivAt axialM (axialMD z) z := by
  have hd : DifferentiableAt ℝ axialM z := by unfold axialM; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [axialM,axialMD] <;> ring

lemma axialMD_hasDeriv (z : ℝ) : HasDerivAt axialMD (axialMDD z) z := by
  have hd : DifferentiableAt ℝ axialMD z := by unfold axialMD; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [axialMD,axialMDD] <;> ring

lemma axialM_curvature {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    (1 : ℝ)/8 ≤ axialMDD z := by
  have hs := small_turn_trig hz
  have hb : 0 ≤ 3*Real.pi/10-131/800 := by linarith [pi_lower]
  have hm := mul_le_mul_of_nonneg_left hs.2.1 hb
  dsimp [axialMDD]
  nlinarith [hs.2.2,pi_upper]

lemma axial_small_margin {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    (3 : ℝ)/2000 ≤ axialM z := by
  have ht := Seven.curvature_tangent (f := axialM) (d := axialMD)
    (dd := axialMDD) (κ := (1 : ℝ)/8) (l := (0 : ℝ)) (u := Real.pi/6)
    (t := (0 : ℝ)) hz (by constructor <;> linarith [Real.pi_pos])
    (fun y _ => axialM_hasDeriv y) (fun y _ => axialMD_hasDeriv y)
    (fun y hy => axialM_curvature hy)
  have hv : (1 : ℝ)/250 < axialM 0 := by
    simp only [axialM,Real.cos_zero,Real.sin_zero,mul_zero,mul_one,sub_zero]
    linarith [pi_upper]
  have hd : -(1/40 : ℝ) < axialMD 0 := by
    simp only [axialMD,Real.cos_zero,Real.sin_zero,mul_zero,mul_one,zero_add]
    linarith [pi_lower]
  have hm := mul_le_mul_of_nonneg_right hd.le hz.1
  have hsq := sq_nonneg (z-1/5)
  nlinarith

lemma axial_small_support {A v z : ℝ} (h : Admissible A v)
    (hA : label A v=axial v) (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    axialM z ≤ axialDefect A v z := by
  have hcone := residual_cone hz
  have hdisk := cone_disk_support (state_disk h) hcone.1 hcone.2.1 hcone.2.2
  have hl : 9*(A+1/2)+11*(v+1/2) ≤ 2*Real.pi+17 := by
    linarith [axial_line h hA]
  have hn : 0 ≤ axialLambda z := by
    have hs := small_turn_trig hz
    dsimp [axialLambda]
    linarith [hs.2.1]
  have hm := mul_le_mul_of_nonneg_left hl hn
  dsimp [axialM,axialDefect,axialU,axialV,axialLambda] at *
  nlinarith

def axialG (z : ℝ) : ℝ :=
  1+2*Real.pi/15-(4/5)*z+Real.cos z-
    (51/20)*(Real.cos (z/2)-Real.sin (z/2))

def axialGD (z : ℝ) : ℝ :=
  -4/5-Real.sin z+(51/40)*(Real.sin (z/2)+Real.cos (z/2))

def axialGDD (z : ℝ) : ℝ :=
  -Real.cos z+(51/80)*(Real.cos (z/2)-Real.sin (z/2))

lemma axialG_hasDeriv (z : ℝ) : HasDerivAt axialG (axialGD z) z := by
  have hd : DifferentiableAt ℝ axialG z := by unfold axialG; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [axialG,axialGD] <;> ring

lemma axialGD_hasDeriv (z : ℝ) : HasDerivAt axialGD (axialGDD z) z := by
  have hd : DifferentiableAt ℝ axialGD z := by unfold axialGD; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [axialGD,axialGDD] <;> ring

lemma half_angle_nonneg {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 ≤ Real.cos (z/2)-Real.sin (z/2) := by
  have hh := Seven.sin_le_cos_of_small
    (show 0 ≤ z/2 ∧ z/2 ≤ Real.pi/4 by constructor <;> linarith [hz.1,hz.2])
  linarith

lemma half_angle_norm (z : ℝ) :
    Real.cos z^2+(1-Real.sin z)^2 =
      2*(Real.cos (z/2)-Real.sin (z/2))^2 := by
  have hs : Real.sin z=2*Real.sin (z/2)*Real.cos (z/2) := by
    rw [← Real.sin_two_mul]
    congr 1 <;> ring
  nlinarith [Real.sin_sq_add_cos_sq z,Real.sin_sq_add_cos_sq (z/2)]

lemma axialGDD_factor (z : ℝ) : axialGDD z =
    (Real.cos (z/2)-Real.sin (z/2))*
      (51/80-Real.cos (z/2)-Real.sin (z/2)) := by
  have hc : Real.cos z=Real.cos (z/2)^2-Real.sin (z/2)^2 := by
    have hh := Real.cos_two_mul (z/2)
    rw [show 2*(z/2)=z by ring] at hh
    nlinarith [Real.sin_sq_add_cos_sq (z/2)]
  dsimp [axialGDD]
  rw [hc]
  ring

lemma axialGDD_nonpos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) : axialGDD z ≤ 0 := by
  rw [axialGDD_factor]
  have hh := half_angle_nonneg hz
  have hsum := first_quadrant_sum
    (show 0 ≤ z/2 ∧ z/2 ≤ Real.pi/2 by
      constructor <;> linarith [hz.1,hz.2,Real.pi_pos])
  exact mul_nonpos_of_nonneg_of_nonpos hh (by linarith)

lemma twelfth_half_difference :
    Real.cos (Real.pi/12)-Real.sin (Real.pi/12)=Real.sqrt 2/2 := by
  rw [show Real.pi/12=Real.pi/3-Real.pi/4 by ring,Real.cos_sub,Real.sin_sub,
    Real.cos_pi_div_three,Real.sin_pi_div_three,
    Real.cos_pi_div_four,Real.sin_pi_div_four]
  ring

lemma axialG_endpoints : 0 < axialG (Real.pi/6) ∧ 0 < axialG (Real.pi/2) := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr2 : Real.sqrt 2 < (10 : ℝ)/7 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hleft : axialG (Real.pi/6) = 1+Real.sqrt 3/2-51*Real.sqrt 2/40 := by
    dsimp [axialG]
    rw [show Real.pi/6/2=Real.pi/12 by ring,twelfth_half_difference,Real.cos_pi_div_six]
    ring
  have hright : axialG (Real.pi/2) = 1-4*Real.pi/15 := by
    dsimp [axialG]
    rw [show Real.pi/2/2=Real.pi/4 by ring,
      Real.cos_pi_div_two,Real.cos_pi_div_four,Real.sin_pi_div_four]
    ring
  rw [hleft,hright]
  constructor <;> linarith [sqrt_three_coarse.1,pi_upper]

lemma axial_large_margin {z : ℝ} (hz : Real.pi/6 ≤ z ∧ z ≤ Real.pi/2) :
    0 < axialG z := by
  apply Seven.positive_of_second_nonpos (f := axialG) (d := axialGD) (dd := axialGDD) hz
  · unfold axialG; fun_prop
  · unfold axialGD; fun_prop
  · intro y _; exact axialG_hasDeriv y
  · intro y _; exact axialGD_hasDeriv y
  · intro y hy
    exact axialGDD_nonpos ⟨by linarith [hy.1,Real.pi_pos],hy.2⟩
  · exact axialG_endpoints.1
  · exact axialG_endpoints.2

lemma axial_large_support {A v z : ℝ} (h : Admissible A v)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/2) : axialG z ≤ axialDefect A v z := by
  have hh := half_angle_nonneg hz
  have hid := half_angle_norm z
  have hnorm : (13/4 : ℝ)*(Real.cos z^2+(1-Real.sin z)^2) ≤
      ((51/20)*(Real.cos (z/2)-Real.sin (z/2)))^2 := by
    nlinarith [sq_nonneg (Real.cos (z/2)-Real.sin (z/2))]
  have hb := disk_dot_upper (p := Real.cos z) (q := 1-Real.sin z)
    (state_disk h) (show 0 ≤ (51/20 : ℝ)*(Real.cos (z/2)-Real.sin (z/2)) by positivity) hnorm
  dsimp [axialG,axialDefect]
  linarith

/-- Exact replacement for the full production axial_target_support theorem. -/
theorem axial_target_support {A v z : ℝ} (h : Admissible A v)
    (hA : label A v=axial v) (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-
      (A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  change 0 < axialDefect A v z
  by_cases hsmall : z ≤ Real.pi/6
  · have hm := axial_small_margin ⟨hz.1,hsmall⟩
    have hs := axial_small_support h hA ⟨hz.1,hsmall⟩
    linarith
  · exact (axial_large_margin ⟨(lt_of_not_ge hsmall).le,hz.2⟩).trans_le
      (axial_large_support h hz)

end SquaresInCircles.Seven.Human

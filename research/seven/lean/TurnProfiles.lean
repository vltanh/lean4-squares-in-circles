import research.seven.lean.Basic

/-! C and D: trigonometric statements proved without the old polynomials. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def inwardF (z : ℝ) : ℝ :=
  Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z)-z/50

def inwardQ (z : ℝ) : ℝ :=
  9/50-3*z/8+7*z^2/30+z^3/32-z^4/30-z^5/960

lemma inwardQ_identity (z : ℝ) : inwardQ z =
    (9/40)*(z-5/6)^2+19/800+
      (z^2/960)*(5+(1-z)*(z^2+33*z+3)) := by
  unfold inwardQ
  ring

lemma inward_small_lower {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    z*((9/40)*(z-5/6)^2+19/800) ≤ inwardF z := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := mul_le_mul_of_nonneg_left (Seven.cos_upper_four hz.1)
    (show 0 ≤ (4/5 : ℝ)*z by positivity)
  have hl := Seven.cos_lower_six hz.1
  have htaylor : z*inwardQ z ≤ inwardF z := by
    dsimp [inwardQ,inwardF]
    nlinarith
  have hrem : 0 ≤ (z^2/960)*(5+(1-z)*(z^2+33*z+3)) := by
    have hz1 : 0 ≤ 1-z := by linarith
    positivity
  have hcore : (9/40)*(z-5/6)^2+19/800 ≤ inwardQ z := by
    rw [inwardQ_identity]
    linarith
  exact (mul_le_mul_of_nonneg_left hcore hz.1).trans htaylor

lemma inwardF_hasDeriv (z : ℝ) : HasDerivAt inwardF
    ((1/5)*Real.cos z+((4/5)*z-3/4)*Real.sin z-1/50) z := by
  have hd := (((Real.hasDerivAt_sin z).sub
    (((hasDerivAt_id z).mul (Real.hasDerivAt_cos z)).const_mul (4/5))).sub
    (((hasDerivAt_const z 1).sub (Real.hasDerivAt_cos z)).const_mul (3/4))).sub
    ((hasDerivAt_id z).div_const 50)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [inwardF]; ring) | (dsimp; ring)

lemma first_quadrant_sum {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    1 ≤ Real.cos z+Real.sin z := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show z ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hz.1,hz.2,Real.pi_pos])
  nlinarith [Real.sin_sq_add_cos_sq z,mul_nonneg hs hc]

lemma inward_tail_lower {z : ℝ} (hz : 1 ≤ z ∧ z ≤ Real.pi/2) :
    (3/100 : ℝ)*z ≤ inwardF z := by
  have hmono : MonotoneOn (fun y : ℝ => inwardF y-(3/100)*y)
      (Icc 1 (Real.pi/2)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (d := fun y =>
      (1/5)*Real.cos y+((4/5)*y-3/4)*Real.sin y-1/50-3/100)
    · dsimp [inwardF]; fun_prop
    · intro y _
      exact (inwardF_hasDeriv y).sub ((hasDerivAt_id y).const_mul (3/100))
    · intro y hy
      have hy0 : 0 ≤ y := by linarith [hy.1]
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hy0
        (by linarith [hy.2,Real.pi_pos])
      have hc := Real.cos_nonneg_of_mem_Icc
        (show y ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [hy.1,hy.2,Real.pi_pos])
      have hm := mul_nonneg
        (show 0 ≤ (4/5 : ℝ)*y-3/4-1/20 by linarith [hy.1]) hs
      have hsum := first_quadrant_sum ⟨hy0,hy.2.le⟩
      nlinarith
  have hOne := inward_small_lower (z := (1 : ℝ)) (by constructor <;> norm_num)
  norm_num at hOne
  have hh := hmono ⟨le_rfl,hz.1.trans hz.2⟩ hz hz.1
  linarith

/-- Exact replacement for Seven.inward_turn_profile. -/
theorem inward_turn_profile {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    z/50 ≤ Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) := by
  have hf : 0 ≤ inwardF z := by
    by_cases hsmall : z ≤ 1
    · have hh := inward_small_lower ⟨hz.1,hsmall⟩
      have hp : 0 ≤ z*((9/40)*(z-5/6)^2+19/800) := by positivity
      linarith
    · have hh := inward_tail_lower ⟨(lt_of_not_ge hsmall).le,hz.2⟩
      linarith
  dsimp [inwardF] at hf
  linarith

def oppositeF (z : ℝ) : ℝ :=
  1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z-
    (1/2)*(1-Real.cos z)

lemma oppositeF_hasDeriv (z : ℝ) : HasDerivAt oppositeF
    (4/5-(Real.sqrt 3-1)*Real.cos z-(1/2)*Real.sin z) z := by
  have hd := (((hasDerivAt_const z (1-4*Real.pi/15)).add
    ((hasDerivAt_id z).const_mul (4/5))).sub
    ((Real.hasDerivAt_sin z).const_mul (Real.sqrt 3-1))).sub
    (((hasDerivAt_const z 1).sub (Real.hasDerivAt_cos z)).const_mul (1/2))
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [oppositeF]; ring) | (dsimp; ring)

/-- One fixed vector, with its orthogonal square explicitly accounted for. -/
lemma opposite_derivative_vector (z : ℝ) :
    (Real.sqrt 3-1)*Real.cos z+(1/2)*Real.sin z < (9 : ℝ)/10 := by
  let r := Real.sqrt 3-1
  have hr := sqrt_three_coarse
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hid : (r*Real.cos z+(1/2)*Real.sin z)^2+
      (r*Real.sin z-(1/2)*Real.cos z)^2 = r^2+1/4 := by
    calc
      _ = (r^2+1/4)*(Real.cos z^2+Real.sin z^2) := by ring
      _ = r^2+1/4 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hnorm : r^2+1/4 < (9/10 : ℝ)^2 := by dsimp [r]; nlinarith [hr.1]
  have hsq := sq_nonneg (r*Real.sin z-(1/2)*Real.cos z)
  change r*Real.cos z+(1/2)*Real.sin z < (9 : ℝ)/10
  nlinarith [sq_nonneg (r*Real.cos z+(1/2)*Real.sin z+9/10)]

lemma opposite_scalar_reserve {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    (2 : ℝ)/35 < oppositeF z := by
  have hm : MonotoneOn (fun y : ℝ => oppositeF y+(1/10)*y)
      (Icc 0 (Real.pi/3)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (d := fun y =>
      4/5-(Real.sqrt 3-1)*Real.cos y-(1/2)*Real.sin y+1/10)
    · dsimp [oppositeF]; fun_prop
    · intro y _
      exact (oppositeF_hasDeriv y).add ((hasDerivAt_id y).const_mul (1/10))
    · intro y _; linarith [opposite_derivative_vector y]
  have hh := hm (show (0 : ℝ) ∈ Icc 0 (Real.pi/3) by
    constructor <;> linarith [Real.pi_pos]) hz hz.1
  have hzero : oppositeF 0 = 1-4*Real.pi/15 := by simp [oppositeF]
  rw [hzero] at hh
  linarith [pi_upper]

/-- Exact replacement for Seven.opposite_axial_scalar. -/
theorem opposite_axial_scalar {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    0 < 1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z-
      (1/2)*(1-Real.cos z) := by
  have hh := opposite_scalar_reserve hz
  dsimp [oppositeF] at hh
  linarith

end SquaresInCircles.Seven.Human

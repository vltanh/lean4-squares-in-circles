module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonData

/-!
# Eight squares: the two rational inverse-power bounds used by the common gain

Multiplication by the positive odd power of `sqrt (1-v)` removes the
inverse power. The first resulting derivative has one explicitly known
sign change; the second is nonpositive. Thus the displayed binomial
majorant and minorant hold on their complete stated intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain

def inverseRoot (v : ℝ) : ℝ := Real.sqrt (1-v)
def scaledUpper (v : ℝ) : ℝ := L v*(inverseRoot v)^5
def scaledLower (v : ℝ) : ℝ := L2 v*(inverseRoot v)^3

theorem inverseRoot_positive {v : ℝ} (hv : v<1) : 0< inverseRoot v :=
  Real.sqrt_pos.mpr (by linarith)
theorem inverseRoot_square {v : ℝ} (hv : v<1) : (inverseRoot v)^2=1-v :=
  Real.sq_sqrt (by linarith)
theorem inverseRoot_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt inverseRoot (-1/(2*inverseRoot v)) v := by
  have h := ((hasDerivAt_id' v).const_sub 1).sqrt (by linarith : (1:ℝ)-v≠0)
  exact h

theorem L_derivative (v : ℝ) :
    HasDerivAt L (5/2+(35/4)*v+24*v^2) v := by
  have h := ((((hasDerivAt_id' v).const_mul (5/2:ℝ)).const_add 1).add
    ((hasDerivAt_pow 2 v).const_mul (35/8:ℝ))).add ((hasDerivAt_pow 3 v).const_mul (8:ℝ))
  convert h using 1
  · funext x; simp only [L,Pi.add_apply]
  · norm_num; ring
theorem L2_derivative (v : ℝ) :
    HasDerivAt L2 (3/2+(15/4)*v+(105/16)*v^2) v := by
  have h := ((((hasDerivAt_id' v).const_mul (3/2:ℝ)).const_add 1).add
    ((hasDerivAt_pow 2 v).const_mul (15/8:ℝ))).add ((hasDerivAt_pow 3 v).const_mul (35/16:ℝ))
  convert h using 1
  · funext x; simp only [L2,Pi.add_apply]
  · norm_num; ring

theorem scaledUpper_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt scaledUpper ((inverseRoot v)^3*v^2*(69/16-44*v)) v := by
  have hp := inverseRoot_positive hv
  have hh := (L_derivative v).mul ((inverseRoot_derivative hv).pow 5)
  convert hh using 1
  · rfl
  · calc
      (inverseRoot v)^3*v^2*(69/16-44*v)=
          (inverseRoot v)^3*((1-v)*(5/2+(35/4)*v+24*v^2)-(5/2)*L v) := by
        dsimp [L]; ring
      _=(5/2+(35/4)*v+24*v^2)*(inverseRoot v)^5+
          L v*(5*(inverseRoot v)^4*(-1/(2*inverseRoot v))) := by
        rw [←inverseRoot_square hv]
        field_simp [hp.ne']
        ring

theorem scaledLower_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt scaledLower (-(315/32)*v^3*inverseRoot v) v := by
  have hp := inverseRoot_positive hv
  have hh := (L2_derivative v).mul ((inverseRoot_derivative hv).pow 3)
  convert hh using 1
  · rfl
  · calc
      -(315/32)*v^3*inverseRoot v=
          inverseRoot v*((1-v)*(3/2+(15/4)*v+(105/16)*v^2)-(3/2)*L2 v) := by
        dsimp [L2]; ring
      _=(3/2+(15/4)*v+(105/16)*v^2)*(inverseRoot v)^3+
          L2 v*(3*(inverseRoot v)^2*(-1/(2*inverseRoot v))) := by
        rw [←inverseRoot_square hv]
        field_simp [hp.ne']
        ring

theorem scaledUpper_right : (1:ℝ)<scaledUpper (31/250) := by
  have hp := inverseRoot_positive (v:=(31/250:ℝ)) (by norm_num)
  have hs := inverseRoot_square (v:=(31/250:ℝ)) (by norm_num)
  have hL : 0<L (31/250) := by norm_num [L]
  have h0 : 0<scaledUpper (31/250) := mul_pos hL (pow_pos hp 5)
  have hsq : (scaledUpper (31/250))^2=(L (31/250))^2*(219/250:ℝ)^5 := by
    dsimp [scaledUpper]
    rw [mul_pow,←pow_mul,show 5*2=2*5 by norm_num,pow_mul,hs]
    norm_num
  have hh : (1:ℝ)<(L (31/250))^2*(219/250:ℝ)^5 := by norm_num [L]
  nlinarith

theorem inverse_five_upper {v : ℝ} (hv : v∈Icc (0:ℝ) (31/250)) :
    1/(inverseRoot v)^5≤L v := by
  have hinc : MonotoneOn scaledUpper (Icc (0:ℝ) (69/704)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (scaledUpper_derivative (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledUpper_derivative (by linarith [hx.2])
    · intro x hx
      exact mul_nonneg (mul_nonneg (pow_nonneg (inverseRoot_positive (by linarith [hx.2])).le 3)
        (sq_nonneg x)) (by linarith [hx.2])
  have hdec : AntitoneOn scaledUpper (Icc (69/704:ℝ) (31/250)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro x hx
      exact (scaledUpper_derivative (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledUpper_derivative (by linarith [hx.2])
    · intro x hx
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg (inverseRoot_positive (by linarith [hx.2])).le 3) (sq_nonneg x))
        (by linarith [hx.1])
  have hscale : 1≤ scaledUpper v := by
    by_cases hh : v≤69/704
    · have ht := hinc ⟨le_rfl,by norm_num⟩ ⟨hv.1,hh⟩ hv.1
      simpa [scaledUpper,L,inverseRoot] using ht
    · exact scaledUpper_right.le.trans (hdec ⟨le_of_not_ge hh,hv.2⟩
        ⟨by norm_num,le_rfl⟩ hv.2)
  exact (div_le_iff₀ (pow_pos (inverseRoot_positive (by linarith [hv.2])) 5)).2 hscale

theorem inverse_three_lower {v : ℝ} (hv : 0≤v) (hv1 : v<1) :
    L2 v≤1/(inverseRoot v)^3 := by
  have hm : AntitoneOn scaledLower (Icc 0 v) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro x hx
      exact (scaledLower_derivative (hx.2.trans_lt hv1)).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledLower_derivative (hx.2.le.trans_lt hv1)
    · intro x hx
      have hroot := inverseRoot_positive (hx.2.le.trans_lt hv1)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hx.1.le 3)) hroot.le
  have hh := hm ⟨le_rfl,hv⟩ ⟨hv,le_rfl⟩ hv
  have hs : scaledLower v≤1 := by simpa [scaledLower,L2,inverseRoot] using hh
  exact (le_div_iff₀ (pow_pos (inverseRoot_positive hv1) 3)).2 hs

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain

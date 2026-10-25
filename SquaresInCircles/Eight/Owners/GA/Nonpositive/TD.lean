module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Radicals

/-!
# Eight squares: the nonpositive-TD2 extension of the four-circle obstruction

TD is set to zero only in an algebraic reference expression (`tdIncrement`). The TD2 inequality of
the cycle is kept, and its point T gives the compensating gain (`nonpositive_td_gain`). No aligned
TD0 witness and no moved cycle enter.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.Secondary
open Candidate SignedStress

def tdOwners (hg : Fin 4) : Vertex → Fin 4 := ![hg,2,0,2,2,2,0]

def tdIncrement (z : ℝ) (P : SignedPoint) : ℝ :=
  2*(edgeWidth z-1)-2*(P.a*Real.sin z+P.y*(Real.cos z-1))+charge*z

theorem nonpositive_td_gain {z : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hcore : P.AvoidsCore)
    (hz : z≤0) (hsmall : |z|≤frameCap) : 0≤tdIncrement z P := by
  let s := -z
  have hsint : s∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hz,(neg_le_abs z).trans hsmall⟩
  have hzs : z = -s := by dsimp [s]; ring
  obtain ⟨hc,hc1,hs0,hs1,hsc⟩ := transport_trig hsint
  have hphi : 0≤Real.sin s+Real.cos s-1 := by
    have h := one_le_abs_cos_add_abs_sin s
    simpa [abs_of_nonneg hs0,abs_of_pos (show 0<Real.cos s by linarith),add_comm] using sub_nonneg.mpr h
  have hhalf := SignedPoint.primary_gt_half hs hcore
  have hy := (abs_le.mp hs.2).1
  have hycos := mul_le_mul_of_nonpos_right hy
    (show Real.cos s-1≤0 by linarith)
  have hprimary := mul_nonneg (show 0≤P.a-1/2 by linarith) hphi
  have hsin := Real.sin_ge_sub_cube hsint.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hs2 : s^2≤(7/10)*s := by
    have := mul_le_mul_of_nonneg_right hsint.2 hsint.1
    norm_num [frameCap] at this
    nlinarith
  have hs2' : s^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hsint.1 (by simpa [frameCap] using hsint.2) 2
  have hs3 := mul_le_mul_of_nonneg_right hs2' hsint.1
  have hcharge : charge*s≤2*(Real.sin s+Real.cos s-1) := by
    dsimp [charge]
    nlinarith [hsint.1]
  rw [tdIncrement,hzs,edgeWidth_negative_formula hsint]
  simp only [Real.sin_neg,Real.cos_neg]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.Secondary

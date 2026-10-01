import research.seven.lean.CoarseBoundary
import research.seven.lean.PolynomialBounds
import SquaresInCircles.Seven.TargetBoundaryMonotonicity

/-!
B/N, including the complete circular-target monotonicity statement. Definitions
from production are shared; the old ratio bounds and their narrow numerical
premises are not used in these replacement proofs.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human
open Boundary

lemma axial_circle_bounds_geometric {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    (8 : ℝ)/5 < axialX s ∧ axialX s < 7/4 ∧
    (1 : ℝ)/2 ≤ axialY s ∧ axialY s ≤ Y0 ∧
    (axialX s)^2+(axialY s)^2=(13 : ℝ)/4 := by
  have hY : (1 : ℝ)/2 ≤ axialY s ∧ axialY s ≤ Y0 := by
    dsimp [axialY,s0,u0] at *
    constructor <;> linarith [hs.1,hs.2]
  have hb := transition_xy_bounds
  have hr : 0 ≤ targetSq-(axialY s)^2 := by
    dsimp [targetSq]
    nlinarith [hY.1,hY.2,hb.2.2.2]
  have hsq : (axialX s)^2+(axialY s)^2=(13 : ℝ)/4 := by
    have hh := Real.sq_sqrt hr
    change (axialX s)^2 = targetSq-(axialY s)^2 at hh
    dsimp [targetSq] at hh
    linarith
  have hx0 : 0 ≤ axialX s := Real.sqrt_nonneg _
  exact ⟨by nlinarith [hb.2.2.2],by nlinarith [hY.1],hY.1,hY.2,hsq⟩

lemma axialX_hasDeriv_geometric {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    HasDerivAt axialX (-(4/5)*axialY s/axialX s) s := by
  have hb := axial_circle_bounds_geometric hs
  have hp : 0 < targetSq-(axialY s)^2 := by
    dsimp [targetSq]
    nlinarith [hb.1,hb.2.2.2.2]
  have hd := ((hasDerivAt_const s targetSq).sub
    ((Boundary.hasDerivAt_axialY s).pow 2)).sqrt (ne_of_gt hp)
  convert hd using 1
  · rfl
  · dsimp [axialX,axialY]
    field_simp
    ring

lemma ratio_hasDeriv_geometric {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    HasDerivAt ratio (ratioD s) s := by
  have hb := axial_circle_bounds_geometric hs
  have hx : axialX s ≠ 0 := by linarith [hb.1]
  have hy : axialY s ≠ 0 := by linarith [hb.2.2.1]
  have hden : axialY s*(axialX s-4/5) ≠ 0 :=
    mul_ne_zero hy (by linarith [hb.1])
  have hd := ((axialX_hasDeriv_geometric hs).mul
    ((axialX_hasDeriv_geometric hs).const_sub (9/5))).div
    ((Boundary.hasDerivAt_axialY s).mul
      ((axialX_hasDeriv_geometric hs).sub_const (4/5))) hden
  convert hd using 1
  · rfl
  · dsimp [ratioD]
    field_simp [hx,hy,show axialX s-4/5 ≠ 0 by linarith [hb.1],
      show 5*axialX s-4 ≠ 0 by linarith [hb.1]]
    ring

lemma ratio_derivative_lt_one {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) : ratioD s < 1 := by
  have hb := axial_circle_bounds_geometric hs
  have hx : axialX s ≠ 0 := by linarith [hb.1]
  have hy2 : (axialY s)^2=13/4-(axialX s)^2 := by linarith [hb.2.2.2.2]
  have hrad : 0 < 13-4*(axialX s)^2 := by nlinarith [hb.2.2.1,hy2]
  have hpoly := ratio_numerator_pos ⟨hb.1.le,hb.2.1.le⟩
  have hden : 0 < 5*axialX s*(5*axialX s-4)^2*(13-4*(axialX s)^2) := by
    have hx0 : 0 < axialX s := by linarith [hb.1]
    have hlin : 0 < 5*axialX s-4 := by linarith [hb.1]
    positivity
  have hid : 1-ratioD s = ratioN (axialX s)/
      (5*axialX s*(5*axialX s-4)^2*(13-4*(axialX s)^2)) := by
    dsimp [ratioD,ratioN]
    rw [hy2]
    field_simp [hx,show axialX s*5-4 ≠ 0 by linarith [hb.1],
      ne_of_gt hrad,show 13/4-(axialX s)^2 ≠ 0 by linarith]
    ring
  have hp := div_pos hpoly hden
  rw [← hid] at hp
  linarith

lemma ratio_nonneg_geometric {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) : 0 ≤ ratio s := by
  have hb := axial_circle_bounds_geometric hs
  dsimp [ratio]
  exact div_nonneg (mul_nonneg (by linarith [hb.1]) (by linarith [hb.2.1]))
    (mul_nonneg (by linarith [hb.2.2.1]) (by linarith [hb.1]))

lemma ratio_zero_lt_twelfth_tangent : ratio 0 < 2-Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlow : (4 : ℝ)/5 < Real.sqrt 3 := by nlinarith
  have hhigh : 4*Real.sqrt 3 < (7 : ℝ) := by nlinarith
  have hx : axialX 0=Real.sqrt 3 := by norm_num [axialX,targetSq]
  have hy : axialY 0=(1 : ℝ)/2 := by norm_num [axialY]
  dsimp [ratio]
  rw [hx,hy]
  apply (div_lt_iff₀ (show 0 < (1/2 : ℝ)*(Real.sqrt 3-4/5) by linarith)).mpr
  nlinarith

/-- Optional unchanged internal helper; no decimal enclosure of sqrt(3). -/
lemma ratio_zero_lt : ratio 0 < (51 : ℝ)/200 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlow : (4 : ℝ)/5 < Real.sqrt 3 := by nlinarith
  have hhigh : 1115*Real.sqrt 3 < (1932 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 3-1932/1115)]
  have hx : axialX 0=Real.sqrt 3 := by norm_num [axialX,targetSq]
  have hy : axialY 0=(1 : ℝ)/2 := by norm_num [axialY]
  dsimp [ratio]
  rw [hx,hy]
  apply (div_lt_iff₀ (show 0 < (1/2 : ℝ)*(Real.sqrt 3-4/5) by linarith)).mpr
  nlinarith

lemma twelfth_sine_identity : Real.sin (Real.pi/12) =
    (2-Real.sqrt 3)*Real.cos (Real.pi/12) := by
  rw [show Real.pi/12=Real.pi/3-Real.pi/4 by ring,
    Real.sin_sub,Real.cos_sub,Real.sin_pi_div_three,Real.cos_pi_div_three,
    Real.sin_pi_div_four,Real.cos_pi_div_four]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination (Real.sqrt 2/4)*hs

lemma ratio_initial_sign {θ : ℝ} (hθ : Real.pi/12 ≤ θ ∧ θ < Real.pi/2) :
    0 < Real.sin θ-ratio 0*Real.cos θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hca : 0 < Real.cos (Real.pi/12) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ θ-Real.pi/12 by linarith [hθ.1])
    (show θ-Real.pi/12 ≤ Real.pi by linarith [hθ.2,Real.pi_pos])
  have hid : Real.cos (Real.pi/12)*
      (Real.sin θ-(2-Real.sqrt 3)*Real.cos θ)=Real.sin (θ-Real.pi/12) := by
    rw [Real.sin_sub,twelfth_sine_identity]
    ring
  have hprod : 0 ≤ Real.cos (Real.pi/12)*
      (Real.sin θ-(2-Real.sqrt 3)*Real.cos θ) := by rw [hid]; exact hs
  have hnon : 0 ≤ Real.sin θ-(2-Real.sqrt 3)*Real.cos θ := by
    by_contra hn
    have hmneg := mul_neg_of_pos_of_neg hca (lt_of_not_ge hn)
    linarith
  have hstrict := mul_pos (sub_pos.mpr ratio_zero_lt_twelfth_tangent) hc
  nlinarith

/-- Full replacement using B and N rather than either old numerical helper. -/
theorem circleTarget_decreases {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) :
    AntitoneOn (circleTarget t) (Icc 0 s0) := by
  let E : ℝ → ℝ := fun s => Real.sin (gap-t+s)-ratio s*Real.cos (gap-t+s)
  have hangle (s : ℝ) (hs : s ∈ Icc 0 s0) :
      Real.pi/12 ≤ gap-t+s ∧ gap-t+s < Real.pi/2 := by
    have hb := transition_coarse_geometric
    dsimp [gap]
    constructor <;> linarith [ht.1,ht.2,hs.1,hs.2,Real.pi_pos]
  have hEder (s : ℝ) (hs : s ∈ Icc 0 s0) :
      HasDerivAt E ((1-ratioD s)*Real.cos (gap-t+s)+
        ratio s*Real.sin (gap-t+s)) s := by
    have hd : HasDerivAt (fun x : ℝ => gap-t+x) 1 s :=
      (hasDerivAt_id s).const_add (gap-t)
    convert hd.sin.sub ((ratio_hasDeriv_geometric hs).mul hd.cos) using 1 <;>
      first | rfl | (funext y; dsimp [E]; ring) | ring
  have hEmono : MonotoneOn E (Icc 0 s0) := by
    apply Seven.monoOn_of_hasDeriv_nonneg
      (d := fun s => (1-ratioD s)*Real.cos (gap-t+s)+ratio s*Real.sin (gap-t+s))
    · exact fun s hs => (hEder s hs).continuousAt.continuousWithinAt
    · intro s hs; exact hEder s ⟨hs.1.le,hs.2.le⟩
    · intro s hs
      have hp := ratio_derivative_lt_one ⟨hs.1.le,hs.2.le⟩
      have hn := ratio_nonneg_geometric ⟨hs.1.le,hs.2.le⟩
      have ha := hangle s ⟨hs.1.le,hs.2.le⟩
      have hc := Real.cos_nonneg_of_mem_Icc
        (show gap-t+s ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [ha.1,ha.2,Real.pi_pos])
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
        (show 0 ≤ gap-t+s by linarith [ha.1,Real.pi_pos])
        (show gap-t+s ≤ Real.pi by linarith [ha.2,Real.pi_pos])
      exact add_nonneg (mul_nonneg (by linarith) hc) (mul_nonneg hn hsin)
  have hs0 : 0 ≤ s0 := by linarith [transition_coarse_geometric.2.2.2.2.1]
  have hE0 : 0 < E 0 := by
    have hh := ratio_initial_sign (hangle 0 ⟨le_rfl,hs0⟩)
    simpa only [E,add_zero] using hh
  have hEpos (s : ℝ) (hs : s ∈ Icc 0 s0) : 0 < E s :=
    hE0.trans_le (hEmono ⟨le_rfl,hs0⟩ hs hs.1)
  have hder (s : ℝ) (hs : s ∈ Icc 0 s0) :
      HasDerivAt (circleTarget t)
        (-(axialY s*(axialX s-4/5)/axialX s)*E s) s := by
    have hd : HasDerivAt (fun x : ℝ => gap-t+x) 1 s :=
      (hasDerivAt_id s).const_add (gap-t)
    have hx := axialX_hasDeriv_geometric hs
    have hy := Boundary.hasDerivAt_axialY s
    have hb := axial_circle_bounds_geometric hs
    convert (((hx.sub_const 1).neg.mul hd.sin).add (hy.mul hd.cos)) using 1
    · rfl
    · dsimp [E,ratio]
      field_simp [show axialX s ≠ 0 by linarith [hb.1],
        show axialY s ≠ 0 by linarith [hb.2.2.1],
        show axialX s*5-4 ≠ 0 by linarith [hb.1]]
      ring
  apply Seven.antiOn_of_hasDeriv_nonpos
    (d := fun s => -(axialY s*(axialX s-4/5)/axialX s)*E s)
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => hder s ⟨hs.1.le,hs.2.le⟩)
  intro s hs
  have hb := axial_circle_bounds_geometric ⟨hs.1.le,hs.2.le⟩
  have hp := hEpos s ⟨hs.1.le,hs.2.le⟩
  have hcoef : 0 ≤ axialY s*(axialX s-4/5)/axialX s :=
    div_nonneg (mul_nonneg (by linarith [hb.2.2.1]) (by linarith [hb.1]))
      (by linarith [hb.1])
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoef) hp.le

end SquaresInCircles.Seven.Human

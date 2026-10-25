module

public import SquaresInCircles.Eight.Frames.Diagonal.Transport

/-!
# Eight squares: the enlarged high arc and the complete quarter-turn strip

The enlargement to transverse coordinate `.8` is used only for a lower
support.  It is still the same exact circle.  All trigonometric bounds
and one-sided widths hold on the complete closed strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighContactArc
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport

def extended : Set ℝ := Icc 0 (4/5)
def strip : Set ℝ := Icc (-(1/50:ℝ)) (1/50)
def side (before : Bool) : Set ℝ :=
  if before then Icc (-(1/50:ℝ)) 0 else Icc 0 (1/50)
def C (e : ℝ) : ℝ := Real.cos e-Real.sin e
def D (e : ℝ) : ℝ := Real.cos e+Real.sin e
def W (before : Bool) (e : ℝ) : ℝ := if before then 1+C e else 1+D e
def Wd (before : Bool) (e : ℝ) : ℝ := if before then -D e else C e
def angular (before : Bool) (e : ℝ) : ℝ :=
  Real.pi/2+e-(9/100)*(W before e-2)

theorem side_subset {before : Bool} {e : ℝ} (he : e∈side before) : e∈strip := by
  cases before <;> dsimp [side,strip] at * <;> constructor <;> linarith [he.1,he.2]

theorem zero_side (before : Bool) : (0:ℝ)∈side before := by cases before <;> norm_num [side]

theorem extended_subset {B : ℝ} (hB : B∈extended) : B∈Icc 0 b2 :=
  ⟨hB.1,by linarith [hB.2,b2_bounds.1]⟩

theorem high_extended {B : ℝ} (hB : B∈Icc 0 b1) : B∈extended :=
  ⟨hB.1,by linarith [hB.2,b1_bounds.2]⟩

theorem extended_radial {B : ℝ} (hB : B∈extended) :
    (67/25:ℝ)<A B+1 ∧ A B≤FrameDiagonalArc.a0 := by
  have hc := A_circle (extended_subset hB)
  have hp := A_shift_pos (extended_subset hB)
  have hsq := pow_le_pow_left₀ hB.1 hB.2 2
  have hu := (A_bounds (extended_subset hB)).2
  norm_num [Q0] at hc
  exact ⟨by nlinarith,hu⟩

theorem extended_slope {B : ℝ} (hB : B∈extended) : 0≤ slope B ∧ slope B<3/10 := by
  have hp := (extended_radial hB).1
  constructor
  · exact div_nonneg hB.1 (by linarith)
  · apply (div_lt_iff₀ (show 0<A B+1 by linarith)).2
    linarith [hB.2]

theorem H_deriv_extended {B : ℝ} (hB : B∈extended) : HasDerivAt H (Hd B) B := by
  have hh := (((A_hasDerivAt (extended_subset hB)).sub_const FrameDiagonalArc.a0).const_mul
    u).fun_add ((hasDerivAt_id B).const_mul v)
  rw [show H=fun y => u*(A y-FrameDiagonalArc.a0)+v*id y from rfl]
  exact hh.congr_deriv (by simp only [Hd,Ad,FrameDiagonalArc.slope]; ring)

theorem Hd_extended {B : ℝ} (hB : B∈extended) :
    v-(3/10)*u<Hd B ∧ Hd B≤v := by
  have hr := extended_slope hB
  dsimp [Hd,u,v]
  constructor <;> linarith

theorem H_monotone_extended : MonotoneOn H extended := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun B hB => (H_deriv_extended hB).continuousAt.continuousWithinAt
  · exact fun B hB => H_deriv_extended (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (Hd_extended (Ioo_subset_Icc_self hB)).1
    dsimp [u,v] at hh
    linarith

theorem C_deriv (e : ℝ) : HasDerivAt C (-D e) e := by
  have h := (Real.hasDerivAt_cos e).fun_sub (Real.hasDerivAt_sin e)
  rw [show C=fun x => Real.cos x-Real.sin x from rfl]
  exact h.congr_deriv (by simp only [D]; ring)

theorem D_deriv (e : ℝ) : HasDerivAt D (C e) e := by
  have h := (Real.hasDerivAt_cos e).fun_add (Real.hasDerivAt_sin e)
  rw [show D=fun x => Real.cos x+Real.sin x from rfl]
  exact h.congr_deriv (by simp only [C]; ring)

theorem W_deriv (before : Bool) (e : ℝ) : HasDerivAt (W before) (Wd before e) e := by
  cases before
  · exact (D_deriv e).const_add 1
  · exact (C_deriv e).const_add 1

theorem angular_deriv (before : Bool) (e : ℝ) :
    HasDerivAt (angular before) (1-(9/100)*Wd before e) e := by
  have h := ((hasDerivAt_id e).const_add (Real.pi/2)).fun_sub
    (((W_deriv before e).sub_const 2).const_mul (9/100:ℝ))
  rw [show angular before=fun y => Real.pi/2+id y-9/100*(W before y-2) from rfl]
  exact h.congr_deriv (by ring)

theorem unit (e : ℝ) : (C e)^2+(D e)^2=2 := by
  dsimp [C,D]
  nlinarith [Real.sin_sq_add_cos_sq e]

theorem strip_trig {e : ℝ} (he : e∈strip) :
    -(1/50:ℝ)≤Real.sin e ∧ Real.sin e≤1/50 ∧
      (4999/5000:ℝ)≤Real.cos e ∧ Real.cos e≤1 := by
  have hab : |e|≤(1/50:ℝ) := abs_le.mpr he
  have hs := (Real.abs_sin_le_abs (x := e)).trans hab
  have hsq := pow_le_pow_left₀ (abs_nonneg e) hab 2
  rw [sq_abs] at hsq
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  exact ⟨(abs_le.mp hs).1,(abs_le.mp hs).2,by nlinarith,Real.cos_le_one e⟩

theorem CD_bounds {e : ℝ} (he : e∈strip) :
    C e∈Icc (4899/5000:ℝ) (51/50) ∧ D e∈Icc (4899/5000:ℝ) (51/50) := by
  have ht := strip_trig he
  dsimp [C,D]
  constructor <;> constructor <;> linarith

theorem side_signs {before : Bool} {e : ℝ} (he : e∈side before) :
    (if before then Real.sin e≤0 ∧ 1≤C e ∧ D e≤1
      else 0≤Real.sin e ∧ C e≤1 ∧ 1≤D e) := by
  have ht := strip_trig (side_subset he)
  have hp := one_le_abs_cos_add_abs_sin e
  cases before with
  | false =>
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi he.1
        (by linarith [he.2,Arithmetic.pi_hand_enclosure.1])
      simp only [abs_of_nonneg hs,
        abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)] at hp
      simp only [Bool.false_eq_true,↓reduceIte]
      dsimp [C,D]
      exact ⟨hs,by linarith,by linarith⟩
  | true =>
      have hs : Real.sin e≤0 := by
        have hh := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0≤-e by linarith [he.2])
          (show -e≤Real.pi by linarith [he.1,Arithmetic.pi_hand_enclosure.1])
        simpa only [Real.sin_neg,neg_nonneg] using hh
      simp only [abs_of_nonpos hs,
        abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)] at hp
      simp only [↓reduceIte]
      dsimp [C,D]
      exact ⟨hs,by linarith,by linarith⟩

theorem W_bounds {before : Bool} {e : ℝ} (he : e∈side before) :
    (2:ℝ)≤W before e ∧ W before e≤101/50 := by
  have ht := CD_bounds (side_subset he)
  have hs := side_signs he
  cases before <;> dsimp [W] at * <;> constructor <;>
    linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2,hs.1,hs.2.1,hs.2.2]

theorem angular_derivative_bounds {before : Bool} {e : ℝ} (he : e∈side before) :
    (if before then 1-(9/100)*Wd before e≤109/100
      else (91/100:ℝ)≤1-(9/100)*Wd before e) := by
  have hs := side_signs he
  cases before <;> dsimp [Wd] at * <;> linarith

theorem angle_trig (e : ℝ) :
    Real.sin (Real.pi/2+e)=Real.cos e ∧ Real.cos (Real.pi/2+e)= -Real.sin e := by
  simp [Real.sin_add,Real.cos_add]

theorem W_actual {before : Bool} {e : ℝ} (he : e∈side before) :
    W before e=2*pairWidth (Real.pi/2+e) := by
  have ht := strip_trig (side_subset he)
  have hs := side_signs he
  rw [pairWidth,(angle_trig e).1,(angle_trig e).2,abs_neg,
    abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)]
  cases before
  · rw [abs_of_nonneg hs.1]
    dsimp [W,D]
    ring
  · rw [abs_of_nonpos hs.1]
    dsimp [W,C]
    ring

theorem angular_actual {before : Bool} {e : ℝ} (he : e∈side before) :
    angular before e=Real.pi/2+e-(9/50)*periodicFrameCost (Real.pi/2+e) := by
  rw [angular,W_actual he]
  dsimp [pairWidth,periodicFrameCost]
  ring

@[simp] theorem C_zero : C 0=1 := by norm_num [C]
@[simp] theorem D_zero : D 0=1 := by norm_num [D]
@[simp] theorem W_zero (before : Bool) : W before 0=2 := by cases before <;> norm_num [W]
@[simp] theorem angular_zero (before : Bool) : angular before 0=Real.pi/2 := by simp [angular]

theorem middle_sum_lower {b : ℝ} (hb : b∈Icc b1 b2) :
    (1199/500:ℝ)<A b+b := by
  have hh := plus_monotone ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩ (mid_subset hb) hb.1
  simp only [A_b1] at hh
  rw [b1_eq] at hh
  linarith [a1_precise.1]

end SquaresInCircles.Eight.FrameMidHighContactArc

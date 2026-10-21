module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoInverseBounds

/-!
# Whole-circle calculus for the opposite-quarter axial boundary

The early part decreases.  The remaining part has second derivative
greater than .11, using the exact inverse-contact derivative and the
single full-interval polynomial bounds.  These statements retain the
actual circle radical and both closed coordinate endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.Axial

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

abbrev inverseAngle := NegativeTwo.ContactInverse.angle
abbrev speed := NegativeTwo.ContactInverse.speed
def angle (b : ℝ) : ℝ := inverseAngle (-(1/2)) b
def value (b : ℝ) : ℝ := Real.pi/2-angle b-P 0-V b
def first (b : ℝ) : ℝ := -NegativeTwo.ContactInverse.first (-(1/2)) b-VLabel.d1 b
def second (b : ℝ) : ℝ :=
  PJCritical.inverseTarget (U b) (ratio b) (-(1/2)) (speed (-(1/2)) b)-VLabel.d2 b

lemma inverse_shift_mem : (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) := by norm_num

lemma value_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt value (first b) b := by
  convert ((((NegativeTwo.ContactInverse.angle_hasDerivAt hb inverse_shift_mem).const_sub
    (Real.pi/2)).sub_const (P 0)).sub
    (VLabel.outer_hasDerivAt (outer_domain hb))) using 1 <;>
    dsimp [value,angle,first,V,inverseAngle] <;> ring

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b := by
  convert ((NegativeTwo.ContactInverse.first_hasDerivAt hb inverse_shift_mem).neg.sub
    (VLabel.d1_hasDerivAt (outer_domain hb))) using 1 <;>
    dsimp [first,second,NegativeTwo.ContactInverse.second,speed] <;> ring

lemma first_formula (b : ℝ) :
    first b=Inverse.factor (U b)-
      ratio b/(2*Inverse.q (U b)*speed (-(1/2)) b)-VLabel.d1 b := by
  dsimp [first,NegativeTwo.ContactInverse.first,speed]
  ring

lemma circle_ratio {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (U b)^2+(ratio b)^2*(U b)^2=Q0 := by
  have hp := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hr : ratio b*U b=W b := by
    change (W b/U b)*U b=W b
    field_simp [hp.ne']
  nlinarith

lemma speed_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (457/500:ℝ)<speed (-(1/2)) b := by
  have hd := NegativeTwo.ContactInverse.data hb inverse_shift_mem
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  nlinarith [hd.2.2.2.2.1,hd.2.2.2.2.2]

lemma weight_bound {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<1/(2*Inverse.q (U b)*speed (-(1/2)) b) ∧
      1/(2*Inverse.q (U b)*speed (-(1/2)) b)<101/200 := by
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  have hv := speed_lower hb
  have hq0 : 0<Inverse.q (U b) := by linarith
  have hv0 : 0<speed (-(1/2)) b := by linarith
  have hp : 0<2*Inverse.q (U b)*speed (-(1/2)) b := by positivity
  refine ⟨one_div_pos.mpr hp,?_⟩
  apply (div_lt_iff₀ hp).2
  have hm := mul_le_mul hq hv.le (by norm_num : (0:ℝ)≤457/500) hq0.le
  nlinarith

lemma brace_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    NegativeTwo.Inverse.brace (U b) (ratio b) (speed (-(1/2)) b)<371/1000 := by
  have hd := NegativeTwo.ContactInverse.data hb inverse_shift_mem
  have hI : U b∈Inverse.interval := ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩
  have hq0 : 0<Inverse.q (U b) := by linarith [(Inverse.range_data hI).2]
  have hv := hd.2.2.2.2.1
  have he := NegativeTwo.Inverse.brace_identity hd.1.ne' hq0.ne' hv.ne'
    (circle_ratio hb) hd.2.2.2.2.2
  have hcor : 0≤(ratio b)^2*(-(1/2:ℝ))^2/
      (Inverse.q (U b)*(speed (-(1/2)) b)^2) := by positivity
  have hK := (Inverse.K0_bounds hI).2
  dsimp [Inverse.mass] at hK
  linarith

lemma target_first_antitone : AntitoneOn VLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [V_second_upper (Ioo_subset_Icc_self hb)])

lemma first_early_negative {b : ℝ} (hb : b∈Icc 0 (1/5)) : first b<0 := by
  have hB : b∈Icc 0 outerDiagonal :=
    ⟨hb.1,hb.2.trans NegativeTwo.TargetContact.Cap.two_mem.2⟩
  have hf := Inverse.factor_upper
    (show U b∈Inverse.interval from ⟨(UW_bounds hB).1.le,(UW_bounds hB).2.1.le⟩)
  have hV := target_first_antitone hB NegativeTwo.TargetContact.Cap.two_mem hb.2
  have hw := weight_bound hB
  have hr : 0≤ratio b := by linarith [(outer_ratio_bounds hB).1]
  have hcor : 0≤ratio b/(2*Inverse.q (U b)*speed (-(1/2)) b) := by
    have hh := mul_nonneg hr hw.1.le
    simpa only [mul_one_div] using hh
  rw [first_formula]
  linarith [V_first_two]

lemma second_late_lower {b : ℝ} (hb : b∈Icc (1/5) outerDiagonal) :
    (11/100:ℝ)<second b := by
  have hB : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  have hh := Inverse.actual_height_derivative hB
  have hw := weight_bound hB
  have hk := brace_upper hB
  have hV := V_second_antitone NegativeTwo.TargetContact.Cap.two_mem hB hb.1
  have hprod := mul_le_mul_of_nonneg_left hk.le hw.1.le
  have hcap := mul_le_mul_of_nonneg_right hw.2.le (by norm_num : (0:ℝ)≤371/1000)
  have he : second b=
      -ratio b*PJCritical.heightFactorD (U b)-
      (1/(2*Inverse.q (U b)*speed (-(1/2)) b))*
        NegativeTwo.Inverse.brace (U b) (ratio b) (speed (-(1/2)) b)-VLabel.d2 b := by
    dsimp [second,PJCritical.inverseTarget]
    ring
  rw [he]
  nlinarith [V_second_two]

lemma early_antitone : AntitoneOn value (Icc 0 (1/5)) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (value_hasDerivAt
      ⟨hb.1,hb.2.trans NegativeTwo.TargetContact.Cap.two_mem.2⟩).continuousAt.continuousWithinAt)
    (fun b hb => value_hasDerivAt
      ⟨hb.1.le,hb.2.le.trans NegativeTwo.TargetContact.Cap.two_mem.2⟩)
    (fun b hb => (first_early_negative (Ioo_subset_Icc_self hb)).le)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.Axial


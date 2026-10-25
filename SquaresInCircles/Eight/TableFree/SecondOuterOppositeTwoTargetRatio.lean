module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoAxialCalculus

/-!
# The strict target ratio on the complete actual outer circle

The diagonal-contact inverse speed exceeds the target label derivative
at zero, and their difference has derivative greater than .012 on the
whole circle.  The inverse-polynomial bounds retain the exact circle
and every boundary point.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.TargetRatio

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

def z : ℝ := outerDiagonal-1/2
def speed (b : ℝ) : ℝ := NegativeTwo.ContactInverse.speed z b
def F (b : ℝ) : ℝ := -NegativeTwo.ContactInverse.first z b
def first (b : ℝ) : ℝ := PJCritical.inverseTarget (U b) (ratio b) z (speed b)
def difference (b : ℝ) : ℝ := F b-VLabel.d1 b
def differenceD (b : ℝ) : ℝ := first b-VLabel.d2 b

lemma z_bounds : (399/1000:ℝ)<z ∧ z<2/5 := by
  dsimp [z]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma z_mem : z∈Icc (-(1/2:ℝ)) (2/5) :=
  ⟨by linarith [z_bounds.1],z_bounds.2.le⟩

lemma F_formula (b : ℝ) :
    F b=Inverse.factor (U b)+z*ratio b/(Inverse.q (U b)*speed b) := by
  dsimp [F,NegativeTwo.ContactInverse.first,speed]
  ring

lemma F_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt F (first b) b := by
  exact (NegativeTwo.ContactInverse.first_hasDerivAt hb z_mem).neg.congr_deriv
    (by dsimp only [first,speed,NegativeTwo.ContactInverse.second]; ring)

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (differenceD b) b := by
  exact (F_hasDerivAt hb).sub (VLabel.d1_hasDerivAt (outer_domain hb))

lemma speed_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (481/500:ℝ)<speed b := by
  have hd := NegativeTwo.ContactInverse.data hb z_mem
  have hq := Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)
  have hz2 : z^2<(2/5:ℝ)^2 := by nlinarith [z_bounds.1,z_bounds.2]
  have hv0 : 0<speed b := hd.2.2.2.2.1
  have hn : z^2+(speed b)^2=Inverse.q (U b) := hd.2.2.2.2.2
  nlinarith [hq.2]

lemma weight_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<z/(Inverse.q (U b)*speed b) ∧ z/(Inverse.q (U b)*speed b)<48/125 := by
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  have hv := speed_lower hb
  have hp : 0<Inverse.q (U b)*speed b := by positivity
  refine ⟨div_pos (by linarith [z_bounds.1]) hp,?_⟩
  apply (div_lt_iff₀ hp).2
  have hm := mul_le_mul hq hv.le (by norm_num : (0:ℝ)≤481/500)
    (by linarith : 0≤Inverse.q (U b))
  nlinarith [z_bounds.2]

lemma brace_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    -(81/500:ℝ)<NegativeTwo.Inverse.brace (U b) (ratio b) (speed b) := by
  have hd := NegativeTwo.ContactInverse.data hb z_mem
  have hI : U b∈Inverse.interval := ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩
  have hq := (Inverse.range_data hI).2
  have hq0 : 0<Inverse.q (U b) := by linarith
  have hv : 0<speed b := by linarith [speed_lower hb]
  have hz2 : z^2≤4/25 := by nlinarith [z_bounds.1,z_bounds.2]
  have hr := outer_ratio_bounds hb
  have hr2 : (ratio b)^2≤1 := by nlinarith [hr.1,hr.2.1]
  have hv2 : (1157/1250:ℝ)≤(speed b)^2 := by
    have hn := hd.2.2.2.2.2
    change z^2+(speed b)^2=Inverse.q (U b) at hn
    linarith
  have hden := mul_le_mul hq hv2 (by norm_num : (0:ℝ)≤1157/1250) hq0.le
  have hnum := mul_le_mul hr2 hz2 (sq_nonneg z) (by norm_num : (0:ℝ)≤1)
  have hcor : (ratio b)^2*z^2/(Inverse.q (U b)*(speed b)^2)<4/25 := by
    apply (div_lt_iff₀ (mul_pos hq0 (sq_pos_of_pos hv))).2
    nlinarith
  have he := NegativeTwo.Inverse.brace_identity hd.1.ne' hq0.ne' hv.ne'
    (Axial.circle_ratio hb) hd.2.2.2.2.2
  have hK := (Inverse.K0_bounds hI).1
  dsimp [Inverse.mass] at hK
  linarith

theorem derivative_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (3/250:ℝ)<differenceD b := by
  have hh := Inverse.actual_height_derivative hb
  have hw := weight_bounds hb
  have hk := brace_lower hb
  have hfirst := mul_le_mul_of_nonneg_left hk.le hw.1.le
  have hsecond := mul_lt_mul_of_pos_right hw.2 (by norm_num : (0:ℝ)<81/500)
  have hV := V_second_upper hb
  change (3/250:ℝ)< -ratio b*PJCritical.heightFactorD (U b)+
    z/(Inverse.q (U b)*speed b)*NegativeTwo.Inverse.brace (U b) (ratio b) (speed b)-VLabel.d2 b
  nlinarith

lemma zero_q :
    (67903041/62500000:ℝ)<Inverse.q (U 0) ∧
      Inverse.q (U 0)<543224329/500000000 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0]
  constructor <;> linarith

lemma zero_ratio : (5223/20000:ℝ)<ratio 0 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source.2
  have hp := U_positive (outer_domain outer_zero_mem)
  rw [show ratio 0=(1/2)/U 0 by simp only [ratio,U,zero_add]]
  apply (lt_div_iff₀ hp).2
  linarith

lemma zero_factor : (48099/50000:ℝ)<Inverse.factor (U 0) := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source
  have hq := zero_q
  have hp : 0<U 0*Inverse.q (U 0) := mul_pos (by linarith [hu.1]) (by linarith [hq.1])
  have hh := mul_le_mul hu.2.le hq.2.le
    (by linarith [hq.1] : 0≤Inverse.q (U 0)) (by norm_num)
  change (48099/50000:ℝ)<(Q0-U 0)/(U 0*Inverse.q (U 0))
  apply (lt_div_iff₀ hp).2
  norm_num [Q0]
  nlinarith

lemma zero_speed : speed 0<(963/1000:ℝ) := by
  have hd := NegativeTwo.ContactInverse.data outer_zero_mem z_mem
  have hq := zero_q.2
  have hz := z_bounds
  have hv0 : 0<speed 0 := hd.2.2.2.2.1
  have hn : z^2+(speed 0)^2=Inverse.q (U 0) := hd.2.2.2.2.2
  have hz2 : (399/1000:ℝ)^2<z^2 := by nlinarith [hz.1]
  nlinarith

lemma zero_correction :
    (9959/100000:ℝ)<z*ratio 0/(Inverse.q (U 0)*speed 0) := by
  have hq := zero_q
  have hv := zero_speed
  have hv0 : 0<speed 0 := by linarith [speed_lower outer_zero_mem]
  have hp : 0<Inverse.q (U 0)*speed 0 := mul_pos (by linarith [hq.1]) hv0
  have hden := mul_le_mul hq.2.le hv.le hv0.le (by norm_num)
  have hnum := mul_le_mul z_bounds.1.le zero_ratio.le (by norm_num)
    (by linarith [z_bounds.1] : 0≤z)
  apply (lt_div_iff₀ hp).2
  nlinarith

lemma zero_positive : (1/2000:ℝ)<difference 0 := by
  have hf := zero_factor
  have hc := zero_correction
  have hV := V_first_upper outer_zero_mem
  dsimp [difference]
  rw [F_formula]
  linarith

lemma difference_monotone : MonotoneOn difference (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (difference_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => difference_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => by linarith [derivative_positive (Ioo_subset_Icc_self hb)])

theorem paid {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : VLabel.d1 b<F b := by
  have hm := difference_monotone outer_zero_mem hb hb.1
  have h0 := zero_positive
  dsimp [difference] at *
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.TargetRatio

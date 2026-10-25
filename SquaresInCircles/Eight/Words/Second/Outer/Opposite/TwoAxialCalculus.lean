module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactCap
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoInverseBounds

/-!
# Eight squares: whole-circle calculus for the opposite-quarter axial boundary

The early part decreases.  The remaining part has second derivative
greater than .11, using the exact inverse-contact derivative and the
single full-interval polynomial bounds.  These statements retain the
actual circle radical and both closed coordinate endpoints.
-/

section
/-!
## The fixed circle references used by opposite edge two

The coordinate with primary height one is an actual circle point.
All reference derivative bounds and both axial aligned costs are
obtained from integer-square bounds and the literal labels.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def bOne : ℝ := arc 1

lemma bOne_mem : bOne∈Icc 0 outerDiagonal := primary_secondary_mem primary_one_mem

lemma bOne_arc : arc bOne=1 :=
  (ShortOuterOne.SameContact.actual_arc (primary_state primary_one_mem)).1

lemma bOne_bounds :
    (79058126439213/100000000000000:ℝ)<bOne ∧
      bOne<39529063219607/50000000000000 := by
  have hc := UW_circle (primary_domain primary_one_mem)
  have hp : 0<bOne+1/2 := by linarith [bOne_mem.1]
  norm_num [U,W,Q0] at hc
  change (bOne+1/2)^2+9/4=9789/2500 at hc
  constructor <;> nlinarith

lemma two_radical : (185083/100000:ℝ)<U (1/5) ∧
    U (1/5)<46271/25000 :=
  Asymmetric.shifted_reference NegativeTwo.TargetContact.Cap.two_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma two_ratio : (1891/5000:ℝ)<ratio (1/5) ∧ ratio (1/5)<3783/10000 := by
  have hu := U_positive (outer_domain NegativeTwo.TargetContact.Cap.two_mem)
  change (1891/5000:ℝ)<W (1/5)/U (1/5) ∧
    W (1/5)/U (1/5)<3783/10000
  constructor
  · apply (lt_div_iff₀ hu).2
    norm_num [W]
    linarith [two_radical.2]
  · apply (div_lt_iff₀ hu).2
    norm_num [W]
    linarith [two_radical.1]

lemma two_ratioD : (247/400:ℝ)<ratioD (1/5) := by
  have hu := U_positive (outer_domain NegativeTwo.TargetContact.Cap.two_mem)
  have hcube := pow_le_pow_left₀ hu.le two_radical.2.le 3
  change (247/400:ℝ)<Q0/(U (1/5))^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma V_first_two : (973/1000:ℝ)<VLabel.d1 (1/5) := by
  have hu := two_radical.1
  have hr := two_ratio.2
  have he : VLabel.d1 (1/5)=16031/100000+
      (63457/100000)*(U (1/5)-1/2)-(14583/125000)*ratio (1/5) := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  rw [he]
  linarith

lemma V_second_two : VLabel.d2 (1/5)< -(69/125:ℝ) := by
  have hr := two_ratio.1
  have hd := two_ratioD
  norm_num [RoleLabel.d2,VLabel]
  linarith

lemma P_second_reference : PLabel.d2 (83/200)<197/1000 := by
  have hb : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := Asymmetric.shifted_reference (l := (3509/2000:ℝ))
    (u := (8773/5000:ℝ)) hb (by norm_num) (by norm_num)
    (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hp := U_positive (outer_domain hb)
  have hr : ratio (83/200)<261/500 := by
    change W (83/200)/U (83/200)<261/500
    apply (div_lt_iff₀ hp).2
    norm_num [W]
    linarith
  have hd : ratioD (83/200)<363/500 := by
    have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3509/2000) hu.1.le 3
    change Q0/(U (83/200))^3<363/500
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0]
    nlinarith
  norm_num [RoleLabel.d2,PLabel]
  linarith

lemma P_second_small {b : ℝ} (hb : b∈Icc 0 (83/200)) :
    PLabel.d2 b<197/1000 := by
  have hr : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (P_second_monotone ⟨hb.1,hb.2.trans hr.2⟩ hr hb.2).trans_lt P_second_reference

lemma P_second_bOne : PLabel.d2 bOne<69/200 := by
  have hr : ratio bOne<861/1000 := by
    norm_num [ratio,bOne_arc]
    linarith [bOne_bounds.2]
  have hd : ratioD bOne=9789/2500/(3/2:ℝ)^3 := by
    norm_num [ratioD,bOne_arc,Q0]
  have hmul := mul_le_mul_of_nonneg_right bOne_bounds.2.le
    (show 0≤ratioD bOne by rw [hd]; norm_num)
  norm_num [RoleLabel.d2,PLabel,hd]
  norm_num [hd] at hmul
  nlinarith

lemma aligned_axial_value :
    (44889/50000:ℝ)<Real.pi/2-P bOne-V 0 := by
  have hb := bOne_bounds
  have hb2 := pow_le_pow_left₀ bOne_mem.1 hb.2.le 2
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hpi := pi_hand_enclosure.1
  norm_num [P,V,RoleLabel.outer,RoleLabel.eval,PLabel,VLabel,bOne_arc,
    ShortOuterOne.SameContact.arc_zero]
  nlinarith

lemma reverse_aligned_axial_value :
    (4639/5000:ℝ)<Real.pi/2-P 0-V bOne := by
  have hb := bOne_bounds.2
  have hpi := pi_hand_enclosure.1
  norm_num [P,V,RoleLabel.outer,RoleLabel.eval,PLabel,VLabel,bOne_arc]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.Axial

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
    HasDerivAt value (first b) b :=
  (((NegativeTwo.ContactInverse.angle_hasDerivAt hb inverse_shift_mem).const_sub
    (Real.pi/2)).sub_const (P 0)).fun_sub (VLabel.outer_hasDerivAt (outer_domain hb))

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b :=
  ((NegativeTwo.ContactInverse.first_hasDerivAt hb inverse_shift_mem).neg.fun_sub
    (VLabel.d1_hasDerivAt (outer_domain hb))).congr_deriv
      (by dsimp [second,NegativeTwo.ContactInverse.second]; ring)

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
  linear_combination hc+(ratio b*U b+W b)*hr

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
    (fun _ hb => (value_hasDerivAt
      ⟨hb.1,hb.2.trans NegativeTwo.TargetContact.Cap.two_mem.2⟩).continuousAt.continuousWithinAt)
    (fun _ hb => value_hasDerivAt
      ⟨hb.1.le,hb.2.le.trans NegativeTwo.TargetContact.Cap.two_mem.2⟩)
    (fun _ hb => (first_early_negative (Ioo_subset_Icc_self hb)).le)

end SquaresInCircles.Eight.SecondWord.OppositeTwo.Axial
end
end
end

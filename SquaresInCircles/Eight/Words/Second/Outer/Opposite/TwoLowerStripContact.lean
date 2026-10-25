module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoAxialCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoInverseBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoTargetPrimaryLabel

/-!
# Eight squares: source concentration on the actual short lower contact

For fixed physical angle at most .01, the original target-secondary
contact has positive second derivative in the source coordinate.
Its derivative at the actual zero-target endpoint is negative.
Thus the full feasible source interval decreases to that endpoint.
All contact and derivative formulas use the original outer circle.
-/

section
/-!
## A single exact reference and the full opposite-quarter axial bound

The reference is the rational transverse coordinate .56615.  Its
inverse angle is bounded by a zero of the original contact equation,
using alternating Taylor bounds at .150171.  Actual circle squares
give its value and derivative.  Uniform curvature then covers the
whole circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.Axial

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def reference : ℝ := 11323/20000
def referenceAngle : ℝ := 150171/1000000

lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])

lemma reference_late : reference∈Icc (1/5) outerDiagonal :=
  ⟨by norm_num [reference],reference_mem.2⟩

lemma reference_radical :
    (16670105511/10000000000:ℝ)<U reference ∧
      U reference<2083763189/1250000000 :=
  Asymmetric.shifted_reference reference_mem
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0])
    (by norm_num [reference,W,Q0])

lemma reference_q :
    (988486811/625000000:ℝ)<Inverse.q (U reference) ∧
      Inverse.q (U reference)<7907894489/5000000000 := by
  have hh := reference_radical
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0]
  constructor <;> linarith

lemma reference_ratio :
    (1279116079/2000000000:ℝ)<ratio reference ∧
      ratio reference<7994475495/12500000000 := by
  have hh := reference_radical
  have hp := U_positive (outer_domain reference_mem)
  have hw : W reference=21323/20000 := by norm_num [W,reference]
  change (1279116079/2000000000:ℝ)<W reference/U reference ∧
    W reference/U reference<7994475495/12500000000
  rw [hw]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [hh.2]
  · apply (div_lt_iff₀ hp).2
    linarith [hh.1]

lemma reference_speed :
    (11539405953/10000000000:ℝ)<speed (-(1/2)) reference ∧
      speed (-(1/2)) reference<2307881191/2000000000 := by
  have hd := NegativeTwo.ContactInverse.data reference_mem
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := reference_q
  constructor <;> nlinarith [hd.2.2.2.2.1,hd.2.2.2.2.2]

lemma reference_factor :
    (8528663/10000000:ℝ)<Inverse.factor (U reference) ∧
      Inverse.factor (U reference)<10660829/12500000 := by
  have hu := reference_radical
  have hq := reference_q
  have hp : 0<U reference*Inverse.q (U reference) :=
    mul_pos (by linarith [hu.1]) (by linarith [hq.1])
  have hl := mul_le_mul hu.1.le hq.1.le (by norm_num)
    (by linarith [hu.1] : 0≤U reference)
  have hh := mul_le_mul hu.2.le hq.2.le
    (by linarith [hq.1] : 0≤Inverse.q (U reference)) (by norm_num)
  change (8528663/10000000:ℝ)<(Q0-U reference)/(U reference*Inverse.q (U reference)) ∧
    (Q0-U reference)/(U reference*Inverse.q (U reference))<10660829/12500000
  constructor
  · apply (lt_div_iff₀ hp).2
    norm_num [Q0]
    linarith
  · apply (div_lt_iff₀ hp).2
    norm_num [Q0]
    linarith

lemma reference_correction :
    (700867/4000000:ℝ)<ratio reference/
      (2*Inverse.q (U reference)*speed (-(1/2)) reference) ∧
    ratio reference/(2*Inverse.q (U reference)*speed (-(1/2)) reference)<8760839/50000000 := by
  have hq := reference_q
  have hv := reference_speed
  have hr := reference_ratio
  have hp : 0<2*Inverse.q (U reference)*speed (-(1/2)) reference :=
    mul_pos (by linarith [hq.1]) (by linarith [hv.1])
  have hl := mul_le_mul hq.1.le hv.1.le (by norm_num)
    (by linarith [hq.1] : 0≤Inverse.q (U reference))
  have hh := mul_le_mul hq.2.le hv.2.le
    (by linarith [hv.1] : 0 ≤ speed (-(1/2)) reference) (by norm_num)
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith
  · apply (div_lt_iff₀ hp).2
    linarith

lemma reference_label_first :
    (67764657/100000000:ℝ)<VLabel.d1 reference ∧
      VLabel.d1 reference<67764659/100000000 := by
  have hu := reference_radical
  have hr := reference_ratio
  have he : VLabel.d1 reference=16031/100000+(63457/100000)*(U reference-1/2)-
      (-(41/4000)+(63457/100000)*reference)*ratio reference := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  have hc : (-(41/4000)+(63457/100000)*reference:ℝ)=
      698023611/2000000000 := by
    norm_num [reference]
  rw [he,hc]
  constructor <;> linarith

lemma reference_first : |first reference|<1/100000 := by
  rw [first_formula,abs_lt]
  have hf := reference_factor
  have hc := reference_correction
  have hv := reference_label_first
  constructor <;> linarith

lemma reference_trig :
    (7480360507/50000000000:ℝ)<Real.sin referenceAngle ∧
      Real.cos referenceAngle<24718637739/25000000000 := by
  have hs := sin_lower_seven (show 0≤referenceAngle by norm_num [referenceAngle])
  have hc := cos_le_cos8 (show 0≤referenceAngle by norm_num [referenceAngle])
  unfold referenceAngle at hs hc ⊢
  norm_num [cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma reference_contact_positive :
    0<NegativeTwo.TargetContact.B reference referenceAngle := by
  have hu := reference_radical
  have ht := reference_trig
  have hp := positive_trig (show referenceAngle∈Icc 0 (7/10) by norm_num [referenceAngle])
  have hprod := mul_le_mul
    (show U reference-1≤(833763189/1250000000:ℝ) by linarith [hu.2])
    ht.2.le (by linarith [hp.1] : 0≤Real.cos referenceAngle)
    (by norm_num : (0:ℝ)≤833763189/1250000000)
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤reference+1/2 by norm_num [reference])
  have he : NegativeTwo.TargetContact.B reference referenceAngle=
      1/2-(U reference-1)*Real.cos referenceAngle+
        (reference+1/2)*Real.sin referenceAngle := by
    simp only [NegativeTwo.TargetContact.B,U]
    ring
  have hr : reference+1/2=(21323/20000:ℝ) := by norm_num [reference]
  rw [he,hr]
  rw [hr] at hsin
  linarith

lemma reference_angle_upper : angle reference≤referenceAngle := by
  have hzero : NegativeTwo.TargetContact.B reference 0<0 := by
    rw [NegativeTwo.TargetContact.B_zero]
    have hh := reference_radical.1
    dsimp [U] at hh
    linarith
  have hc : Continuous (NegativeTwo.TargetContact.B reference) :=
    continuous_iff_continuousAt.2 fun x =>
      (NegativeTwo.TargetContact.B_angle_hasDerivAt reference x).continuousAt
  obtain ⟨x,hx,hcontact⟩ := intermediate_value_Icc
    (show (0:ℝ)≤referenceAngle by norm_num [referenceAngle]) hc.continuousOn
      (show (0:ℝ)∈Icc (NegativeTwo.TargetContact.B reference 0)
        (NegativeTwo.TargetContact.B reference referenceAngle) from
        ⟨hzero.le,reference_contact_positive.le⟩)
  have hD : NegativeTwo.TargetContact.Domain reference x :=
    ⟨reference_mem,⟨hx.1,by linarith [hx.2,show referenceAngle≤(7/10:ℝ) by norm_num [referenceAngle]]⟩,
      by rw [hcontact]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hD
  rw [hcontact,show (0:ℝ)-1/2=-(1/2) by norm_num] at he
  exact he.trans_le hx.2

lemma reference_label_value : V reference<24903/50000 := by
  have hu := reference_radical.2
  have he : V reference=-(41/4000)*(U reference-1/2)+(16031/100000)*(11323/20000)+
      (63457/100000)*(U reference-1/2)*(11323/20000) := by
    simp only [V,RoleLabel.outer,RoleLabel.eval,VLabel,U,reference]
    ring
  rw [he]
  linarith

lemma reference_value : (112223/125000:ℝ)<value reference := by
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have ha := reference_angle_upper
  have hv := reference_label_value
  norm_num [referenceAngle,value,P,RoleLabel.outer,RoleLabel.eval,PLabel] at *
  linarith

lemma late_value {b : ℝ} (hb : b∈Icc (1/5) outerDiagonal) :
    (44889/50000:ℝ)<value b := by
  have ht := curvature_tangent (f := value) (d := first) (dd := second) (κ := (11/100:ℝ))
    hb reference_late
    (fun y hy => value_hasDerivAt ⟨by linarith [hy.1],hy.2⟩)
    (fun y hy => first_hasDerivAt ⟨by linarith [hy.1],hy.2⟩)
    (fun y hy => (second_late_lower hy).le)
  have hsmall := abs_lt.mp reference_first
  have hsquare : (first reference)^2<(1/100000:ℝ)^2 := by nlinarith
  have hcomplete := sq_nonneg ((11/100)*(b-reference)+first reference)
  nlinarith [reference_value]

theorem value_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (44889/50000:ℝ)<value b := by
  by_cases hlate : (1/5:ℝ)≤b
  · exact late_value ⟨hlate,hb.2⟩
  · have hm : value (1/5)≤value b := early_antitone ⟨hb.1,by linarith⟩
      (show (1/5:ℝ)∈Icc 0 (1/5) by norm_num) (by linarith)
    exact (late_value ⟨le_rfl,NegativeTwo.TargetContact.Cap.two_mem.2⟩).trans_le hm

/-- Every original zero contact uses the same exact inverse angle. -/
theorem original {a b x : ℝ} (hs : OuterState a b) (hx : x∈Icc 0 (7/10))
    (hcontact : lowerCut a b x=0) :
    (44889/50000:ℝ)<Real.pi/2-x-P 0-V b := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hz : NegativeTwo.TargetContact.B b x=0 := by
    dsimp [NegativeTwo.TargetContact.B,lowerCut] at *
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hz]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hz,show (0:ℝ)-1/2=-(1/2) by norm_num] at he
  have ha : angle b=x := he
  have hv := value_lower hb
  dsimp only [value] at hv
  rw [ha] at hv
  exact hv

end SquaresInCircles.Eight.SecondWord.OppositeTwo.Axial
end
end
end

section
/-!
## A finite circle comparison for the original upper target-primary axis

The weak original separator bounds the transverse displacement from
alignment.  A single circle support pays that displacement by the
angular gain.  If the target primary height is below one, the primary
label tangent pays its simultaneous loss.  No contact minimum or
endpoint selection is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def displacement (b : ℝ) : ℝ := U b-1+(7/20)*W b

lemma P_first_lower_actual {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (773/1000:ℝ)<PLabel.d1 b := by
  have ha := (outer_bounds (ShortOuterOne.SameContact.arc_state hb)).2.1
  have hr := outer_ratio_bounds hb
  have hm := mul_nonneg hb.1 (show 0≤ratio b by linarith [hr.1])
  dsimp [RoleLabel.d1,PLabel]
  nlinarith [outer_endpoint_bounds.2.1]

lemma P_first_increasing : MonotoneOn PLabel.d1 (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun _ hb => (PLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt
  · exact fun _ hb => PLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb))
  · intro b hb
    have hB := Ioo_subset_Icc_self hb
    have hr := outer_ratio_bounds hB
    have hm := mul_nonneg hB.1 hr.2.2.1.le
    dsimp [RoleLabel.d2,PLabel]
    nlinarith [hr.1]

lemma P_increasing : MonotoneOn P (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (PLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => by linarith [P_first_lower_actual (Ioo_subset_Icc_self hb)])

lemma P_affine_difference_hasDerivAt (c : ℝ) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (fun t => c*t-P t) (c-PLabel.d1 b) b := by
  exact (((hasDerivAt_id b).const_mul c).sub
    (PLabel.outer_hasDerivAt (outer_domain hb))).congr_deriv (by ring)

lemma P_chord_at {l b : ℝ} (hl : l∈Icc 0 outerDiagonal) (hb : b∈Icc 0 outerDiagonal)
    (hlb : l≤b) : P b-P l≤PLabel.d1 b*(b-l) := by
  have hdom {t : ℝ} (ht : t∈Icc l b) : t∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans ht.1,ht.2.trans hb.2⟩
  have hm : MonotoneOn (fun t => PLabel.d1 b*t-P t) (Icc l b) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun _ ht => (P_affine_difference_hasDerivAt (PLabel.d1 b) (hdom ht)).continuousAt.continuousWithinAt
    · exact fun _ ht => P_affine_difference_hasDerivAt (PLabel.d1 b) (hdom (Ioo_subset_Icc_self ht))
    · intro t ht
      linarith [P_first_increasing (hdom (Ioo_subset_Icc_self ht)) hb ht.2.le]
  have hh := hm ⟨le_rfl,hlb⟩ ⟨hlb,le_rfl⟩ hlb
  nlinarith

lemma target_primary_loss_below_one {A : ℝ} (hA : A∈Icc outerDiagonal 1) :
    VPrimaryLabel.outer 1-VPrimaryLabel.outer A≤(11/25)*(1-A) := by
  have hdom {t : ℝ} (ht : t∈Icc A 1) : t∈Icc outerDiagonal outerAxial :=
    ⟨hA.1.trans ht.1,ht.2.trans primary_one_mem.2⟩
  have hd {t : ℝ} (ht : t∈Icc A 1) :
      HasDerivAt (fun s => (11/25)*s-VPrimaryLabel.outer s)
        (11/25-VPrimaryLabel.d1 t) t := by
    exact (((hasDerivAt_id t).const_mul (11/25)).sub
      (VPrimaryLabel.outer_hasDerivAt (primary_domain (hdom ht)))).congr_deriv (by ring)
  have hm : MonotoneOn (fun s => (11/25)*s-VPrimaryLabel.outer s) (Icc A 1) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun _ ht => (hd ht).continuousAt.continuousWithinAt
    · exact fun _ ht => hd (Ioo_subset_Icc_self ht)
    · intro t ht
      have hh := V_primary_first_monotone (hdom (Ioo_subset_Icc_self ht))
        primary_one_mem ht.2.le
      linarith [V_primary_one_first.2]
  have hh := hm ⟨le_rfl,hA.2⟩ ⟨hA.2,le_rfl⟩ hA.2
  nlinarith

lemma displacement_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<displacement b := by
  dsimp [displacement]
  linarith [(UW_bounds hb).1,(UW_bounds hb).2.2.1]

lemma weighted_displacement {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b*displacement b<981/1000 := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hs := sq_nonneg ((51/100)*U b-W b)
  have hsupport : U b+(51/100)*W b<223/100 := by
    norm_num [Q0] at hc
    nlinarith
  have hA : PLabel.d1 b<53/80+(223/1000)*W b := by
    dsimp [W]
    linarith [P_first_affine hb]
  have hApos : 0<53/80+(223/1000)*W b := by linarith [hu.2.2.1]
  have hD : displacement b<123/100-(4/25)*W b := by
    dsimp [displacement]
    linarith
  have hfirst := mul_lt_mul_of_pos_right hA (displacement_positive hb)
  have hsecond := mul_lt_mul_of_pos_left hD hApos
  have hpoly := mul_nonneg
    (show 0≤7/5-W b by linarith [hu.2.2.2])
    (show 0≤16829/100000-(223/6250)*(7/5+W b) by linarith [hu.2.2.2])
  nlinarith

lemma upper_primary_displacement {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    b+1-A≤displacement b*x := by
  have hw := upper_width hx
  have hcut : upperPrimary a b x≤A := by
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperPrimary]
    linarith
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hu : 0≤U b-1 := by linarith [(UW_bounds hb).1]
  have hW : 0≤W b := by linarith [(UW_bounds hb).2.2.1]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := mul_le_mul_of_nonneg_left (positive_trig hx).2.2.2.2.1 hu
  have hquadratic := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hcircle := mul_nonneg hW (show 0≤(7/20)*x-(1-Real.cos x) by nlinarith)
  dsimp [upperPrimary] at hcut
  rw [←(ShortOuterOne.SameContact.actual_arc hs).1] at hcut
  have hcut' : 1/2+W b*Real.cos x-(U b-1)*Real.sin x≤A := by
    have he : 1/2+W b*Real.cos x-(U b-1)*Real.sin x=
        1/2+(b+1/2)*Real.cos x-(arc b-1/2)*Real.sin x := by
      simp only [W,U]
      ring
    rw [he]
    exact hcut
  dsimp [displacement,W] at *
  nlinarith

/-- The original weak upper target-primary owner is closed by a finite
circle displacement comparison, including both primary-height regimes. -/
theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hdisp := upper_primary_displacement hs hx hm
  have hp : 0≤PLabel.d1 b := by linarith [P_first_lower_actual hb]
  have hpaid := mul_le_mul_of_nonneg_right (weighted_displacement hb).le hx.1
  have hstep := mul_le_mul_of_nonneg_left hdisp hp
  by_cases hA : 1≤A
  · have hbase : A-1∈Icc 0 outerDiagonal := by
      refine ⟨by linarith,?_⟩
      linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have halign := aligned_left_original (ShortOuterOne.SameContact.arc_state hbase) ht
      (show 1+(A-1)≤A by linarith)
    by_cases hsource : b≤A-1
    · have hP := P_increasing hb hbase hsource
      dsimp [value] at *
      linarith [hx.1]
    · have hP := P_chord_at hbase hb (by linarith)
      dsimp [value] at *
      nlinarith
  · have hApr : A∈Icc outerDiagonal 1 := ⟨(outer_bounds ht).1,by linarith⟩
    have htarget := target_primary_loss_below_one hApr
    have hactual : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
    have hone : VPrimaryLabel.outer 1= -V bOne :=
      VLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at htarget
    have hsource := P_chord_at outer_zero_mem hb hb.1
    have hgap := mul_le_mul_of_nonneg_right
      (show (11/25:ℝ)≤PLabel.d1 b by linarith [P_first_lower_actual hb])
      (show 0≤1-A by linarith)
    have halign := reverse_aligned_axial_value
    dsimp [value] at *
    linarith [hx.1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## The original lower source-secondary owner

The original target remains fixed while the source follows its
maximal allowed transverse contact.  Its paid angular derivative is
negative on the entire physical interval.  An intermediate-value
argument reaches the actual zero source, where the completed axial
bound applies.  No endpoint witness is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSecondary

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def sourceInterval : Set ℝ := Icc 0 (83/200)
def envelope (b : ℝ) : ℝ := Real.sqrt (Q0-(b+3/2)^2)
def product (b : ℝ) : ℝ := PLabel.d1 b*envelope b
def productD (b : ℝ) : ℝ :=
  PLabel.d2 b*envelope b-PLabel.d1 b*(b+3/2)/envelope b
def cost (A B x : ℝ) : ℝ := Real.pi/2-x-P (lowerCut A B x)-V B

lemma source_mem {b : ℝ} (hb : b∈sourceInterval) : b∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨hb.1,by linarith [hb.2]⟩

lemma envelope_data {b : ℝ} (hb : b∈sourceInterval) :
    0<envelope b ∧ (envelope b)^2+(b+3/2)^2=Q0 := by
  have hrad : 0<Q0-(b+3/2)^2 := by
    have hs := pow_le_pow_left₀ (show 0≤b+3/2 by linarith [hb.1])
      (show b+3/2≤(383/200:ℝ) by linarith [hb.2]) 2
    norm_num [Q0]
    nlinarith
  refine ⟨Real.sqrt_pos.mpr hrad,?_⟩
  have hh := Real.sq_sqrt hrad.le
  dsimp [envelope]
  linarith

lemma envelope_hasDerivAt {b : ℝ} (hb : b∈sourceInterval) :
    HasDerivAt envelope (-(b+3/2)/envelope b) b := by
  have hd := envelope_data hb
  have hrad : Q0-(b+3/2)^2≠0 := by nlinarith [sq_pos_of_pos hd.1]
  have hq := ((((hasDerivAt_id' b).add_const (3/2)).fun_pow 2).const_sub Q0).sqrt hrad
  refine hq.congr_deriv ?_
  have he : Real.sqrt (Q0-(b+3/2)^2)=envelope b := rfl
  rw [he]
  field_simp
  norm_num
  ring

lemma product_hasDerivAt {b : ℝ} (hb : b∈sourceInterval) :
    HasDerivAt product (productD b) b :=
  ((PLabel.d1_hasDerivAt (outer_domain (source_mem hb))).fun_mul
    (envelope_hasDerivAt hb)).congr_deriv (by dsimp [productD]; ring)

lemma productD_negative {b : ℝ} (hb : b∈sourceInterval) : productD b<0 := by
  have hd := envelope_data hb
  have h2 := P_second_small hb
  have h1 := P_first_lower_actual (source_mem hb)
  have hmain := mul_lt_mul_of_pos_right h2 (sq_pos_of_pos hd.1)
  have hlast := mul_le_mul h1.le
    (show (3/2:ℝ)≤b+3/2 by linarith [hb.1]) (by norm_num : (0:ℝ)≤3/2)
    (by linarith : 0≤PLabel.d1 b)
  have henv : (envelope b)^2≤Q0-9/4 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2)
      (show (3/2:ℝ)≤b+3/2 by linarith [hb.1]) 2
    nlinarith [hd.2]
  have he : productD b*envelope b=
      PLabel.d2 b*(envelope b)^2-PLabel.d1 b*(b+3/2) := by
    dsimp [productD]
    field_simp [hd.1.ne']
  norm_num [Q0] at henv
  nlinarith

lemma product_antitone : AntitoneOn product sourceInterval :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (product_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => product_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => (productD_negative (Ioo_subset_Icc_self hb)).le)

lemma product_zero : product 0<1 := by
  have hP := P_first_zero
  have he : envelope 0=bOne+1/2 := by
    norm_num [envelope,bOne,arc]
  have hp := (envelope_data (show (0:ℝ)∈sourceInterval by norm_num [sourceInterval])).1
  have hm := mul_lt_mul_of_pos_right hP hp
  dsimp [product]
  rw [he] at *
  nlinarith [bOne_bounds.2]

lemma product_paid {b : ℝ} (hb : b∈sourceInterval) : product b<1 :=
  (product_antitone (by norm_num [sourceInterval]) hb hb.1).trans_lt product_zero

lemma cut_eq {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    lowerCut A B x= -NegativeTwo.TargetContact.B B x := by
  dsimp [lowerCut,NegativeTwo.TargetContact.B]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  ring

lemma cut_zero (A B : ℝ) : lowerCut A B 0=A-1 := by norm_num [lowerCut]; ring

lemma cut_antitone {A B : ℝ} (ht : OuterState A B) :
    AntitoneOn (lowerCut A B) (Icc 0 (7/10)) := by
  intro s hs t ht' hst
  rw [cut_eq ht s,cut_eq ht t]
  exact neg_le_neg (NegativeTwo.TargetContact.B_angle_monotone
    ⟨ht.1,(outer_bounds ht).2.2⟩ hs ht' hst)

lemma cut_upper {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    lowerCut A B x≤A-1 := by
  have hh := cut_antitone ht (by norm_num) hx hx.1
  simpa [cut_zero] using hh

lemma cut_mem {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) : lowerCut A B x∈sourceInterval := by
  refine ⟨hcut,?_⟩
  linarith [cut_upper ht hx,(outer_bounds ht).2.1,outer_endpoint_bounds.2.1]

lemma cut_hasDerivAt {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    HasDerivAt (lowerCut A B) (-NegativeTwo.TargetContact.v B x) x := by
  have hf : lowerCut A B=fun t => -NegativeTwo.TargetContact.B B t := funext (cut_eq ht)
  rw [hf]
  exact (NegativeTwo.TargetContact.B_angle_hasDerivAt B x).neg

lemma speed_paid {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) :
    PLabel.d1 (lowerCut A B x)*NegativeTwo.TargetContact.v B x<1 := by
  have hb : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hc := cut_mem ht hx hcut
  have henv := envelope_data hc
  have hv := NegativeTwo.TargetContact.v_positive hb hx
  have hn := NegativeTwo.TargetContact.norm_identity hb x
  have hcutupper := cut_upper ht hx
  have he : NegativeTwo.TargetContact.B B x= -lowerCut A B x := by
    linarith [cut_eq ht x]
  rw [he] at hn
  have hU : U B=A+1/2 := by
    dsimp [U]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  rw [hU] at hn
  dsimp [NegativeTwo.Inverse.q] at hn
  have hspeed : NegativeTwo.TargetContact.v B x≤envelope (lowerCut A B x) := by
    nlinarith [henv.2]
  have hm := mul_le_mul_of_nonneg_left hspeed
    (show 0≤PLabel.d1 (lowerCut A B x) by linarith [P_first_lower_actual (source_mem hc)])
  exact hm.trans_lt (product_paid hc)

lemma cost_hasDerivAt {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) :
    HasDerivAt (cost A B)
      (-1+PLabel.d1 (lowerCut A B x)*NegativeTwo.TargetContact.v B x) x := by
  have hP := (PLabel.outer_hasDerivAt
    (outer_domain (source_mem (cut_mem ht hx hcut)))).comp x (cut_hasDerivAt ht x)
  exact ((((hasDerivAt_id' x).const_sub (Real.pi/2)).fun_sub hP).sub_const (V B)).congr_deriv
    (by ring)

lemma cap_positive {B : ℝ} (hb : B∈Icc 0 outerDiagonal) :
    0<NegativeTwo.TargetContact.B B (7/10) := by
  have hm := NegativeTwo.TargetContact.B_source_monotone (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
    outer_zero_mem hb hb.1
  have hzero := NegativeTwo.TargetContact.Cap.zero_target.1
  change (613013931/5000000000:ℝ)<NegativeTwo.TargetContact.B 0 (7/10) at hzero
  linarith

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : b≤lowerCut A B x := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerCut]
    linarith
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hstart : NegativeTwo.TargetContact.B B x≤0 := by
    linarith [cut_eq ht x,hs.1]
  have hcontinuous : Continuous (NegativeTwo.TargetContact.B B) :=
    continuous_iff_continuousAt.2 fun y =>
      (NegativeTwo.TargetContact.B_angle_hasDerivAt B y).continuousAt
  obtain ⟨t,htime,hzero⟩ := intermediate_value_Icc hx.2 hcontinuous.continuousOn
    (show (0:ℝ)∈Icc (NegativeTwo.TargetContact.B B x)
      (NegativeTwo.TargetContact.B B (7/10)) from ⟨hstart,(cap_positive hB).le⟩)
  have ht' : t∈Icc 0 (7/10) := ⟨hx.1.trans htime.1,htime.2⟩
  have hcutzero : lowerCut A B t=0 := by rw [cut_eq ht t,hzero]; ring
  have hdom {s : ℝ} (hs' : s∈Icc x t) : s∈Icc 0 (7/10) :=
    ⟨hx.1.trans hs'.1,hs'.2.trans ht'.2⟩
  have hnonneg {s : ℝ} (hs' : s∈Icc x t) : 0≤lowerCut A B s := by
    have hh := cut_antitone ht (hdom hs') ht' hs'.2
    rw [hcutzero] at hh
    exact hh
  have hcost : AntitoneOn (cost A B) (Icc x t) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun s hs' => (cost_hasDerivAt ht (hdom hs') (hnonneg hs')).continuousAt.continuousWithinAt
    · exact fun s hs' => cost_hasDerivAt ht (hdom (Ioo_subset_Icc_self hs'))
        (hnonneg (Ioo_subset_Icc_self hs'))
    · intro s hs'
      linarith [speed_paid ht (hdom (Ioo_subset_Icc_self hs')) (hnonneg (Ioo_subset_Icc_self hs'))]
  have hstep := hcost ⟨le_rfl,htime.1⟩ ⟨htime.1,le_rfl⟩ htime.1
  have hP := P_increasing ⟨hs.1,(outer_bounds hs).2.2⟩
    (source_mem (cut_mem ht hx (by linarith [hs.1]))) hcut
  have haxis := Axial.original ht ht' hcutzero
  dsimp [cost,value] at *
  rw [hcutzero] at hstep
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSecondary
end
end
end

section
/-!
## Scalar bounds for the original lower target-secondary short strip

The two rational source references are .415 and .775.  Actual
circle squares give the required first-derivative bounds.  On the
zero-target boundary the inverse angular derivative is paid with
a strict reserve, so that boundary decreases to the aligned state.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def earlyTarget : Set ℝ := Icc 0 (83/200)
def sourceBand : Set ℝ := Icc (31/40) bOne
def axisValue (b : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle (-(1/2)) b-P b-V 0
def axisFirst (b : ℝ) : ℝ :=
  Inverse.factor (U b)-ratio b/
    (2*Inverse.q (U b)*NegativeTwo.ContactInverse.speed (-(1/2)) b)-PLabel.d1 b

lemma early_mem {b : ℝ} (hb : b∈earlyTarget) : b∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨hb.1,by linarith [hb.2]⟩

lemma band_mem {b : ℝ} (hb : b∈sourceBand) : b∈Icc 0 outerDiagonal :=
  ⟨by linarith [hb.1],hb.2.trans bOne_mem.2⟩

lemma target_reference_mem : (83/200:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma source_reference_mem : (31/40:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma source_reference_radical :
    (75663/50000:ℝ)<U (31/40) ∧ U (31/40)<151327/100000 :=
  Asymmetric.shifted_reference source_reference_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma source_reference_ratio : (42127/50000:ℝ)<ratio (31/40) := by
  have hp := U_positive (outer_domain source_reference_mem)
  change (42127/50000:ℝ)<W (31/40)/U (31/40)
  apply (lt_div_iff₀ hp).2
  norm_num [W]
  nlinarith [source_reference_radical.2]

lemma source_reference_first : (9269/10000:ℝ)<PLabel.d1 (31/40) := by
  have hu := source_reference_radical
  have hr := source_reference_ratio
  have he : PLabel.d1 (31/40)=93015/100000+(2363/50000)*(31/40)-
      (2211/20000)*(U (31/40)-1/2)+(2211/20000)*(31/40)*ratio (31/40) := by
    simp only [RoleLabel.d1,PLabel,U]
    ring
  rw [he]
  linarith

lemma source_first_lower {b : ℝ} (hb : b∈sourceBand) :
    (9269/10000:ℝ)<PLabel.d1 b := by
  have hm := P_first_increasing source_reference_mem (band_mem hb) hb.1
  linarith [source_reference_first]

lemma target_reference_radical :
    (3509/2000:ℝ)<U (83/200) ∧ U (83/200)<8773/5000 :=
  Asymmetric.shifted_reference target_reference_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma target_reference_ratio : ratio (83/200)<261/500 := by
  have hp := U_positive (outer_domain target_reference_mem)
  change W (83/200)/U (83/200)<261/500
  apply (div_lt_iff₀ hp).2
  norm_num [W]
  nlinarith [target_reference_radical.1]

lemma target_reference_first : (41/50:ℝ)<VLabel.d1 (83/200) := by
  have hu := target_reference_radical
  have hr := target_reference_ratio
  have he : VLabel.d1 (83/200)=16031/100000+(63457/100000)*(U (83/200)-1/2)-
      (-(41/4000)+(63457/100000)*(83/200))*ratio (83/200) := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  rw [he]
  linarith

lemma target_first_antitone : AntitoneOn VLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [V_second_upper (Ioo_subset_Icc_self hb)])

lemma target_first_lower {b : ℝ} (hb : b∈earlyTarget) :
    (41/50:ℝ)<VLabel.d1 b := by
  have hm := target_first_antitone (early_mem hb) target_reference_mem hb.2
  linarith [target_reference_first]

lemma target_monotone : MonotoneOn V earlyTarget :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (VLabel.outer_hasDerivAt (outer_domain (early_mem hb))).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain (early_mem (Ioo_subset_Icc_self hb))))
    (fun b hb => by linarith [target_first_lower (Ioo_subset_Icc_self hb)])

lemma source_second_upper {b : ℝ} (hb : b∈Icc 0 bOne) :
    PLabel.d2 b<69/200 := by
  have hm := P_second_monotone ⟨hb.1,hb.2.trans bOne_mem.2⟩ bOne_mem hb.2
  exact hm.trans_lt P_second_bOne

lemma source_ratioD_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD b := by
  have hp := U_positive (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hcube := pow_le_pow_left₀ hp.le hU.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0]
  nlinarith

lemma source_ratio_upper {b : ℝ} (hb : b∈Icc 0 bOne) :
    ratio b<861/1000 := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hp := U_positive (outer_domain hB)
  have ha := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hB) (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at ha
  change W b/U b<861/1000
  apply (div_lt_iff₀ hp).2
  dsimp [W,U]
  linarith [bOne_bounds.2,hb.2]

lemma band_ratio_lower {b : ℝ} (hb : b∈sourceBand) :
    (133/200:ℝ)<ratio b := by
  have hp := U_positive (outer_domain (band_mem hb))
  have hU := (UW_bounds (band_mem hb)).2.1
  change (133/200:ℝ)<W b/U b
  apply (lt_div_iff₀ hp).2
  dsimp [W]
  nlinarith [hb.1]

lemma band_q_upper {b : ℝ} (hb : b∈sourceBand) :
    Inverse.q (U b)≤4789/2500 := by
  have ha := ShortOuterOne.SameContact.arc_antitone
    (outer_domain (band_mem hb)) (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at ha
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0,U]
  linarith

lemma band_speed_upper {b : ℝ} (hb : b∈sourceBand) :
    NegativeTwo.ContactInverse.speed (-(1/2)) b<1291/1000 := by
  have hd := NegativeTwo.ContactInverse.data (band_mem hb)
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := band_q_upper hb
  nlinarith [hd.2.2.2.2.1,hd.2.2.2.2.2]

lemma band_correction_lower {b : ℝ} (hb : b∈sourceBand) :
    (13/100:ℝ)<ratio b/
      (2*Inverse.q (U b)*NegativeTwo.ContactInverse.speed (-(1/2)) b) := by
  have hB := band_mem hb
  have hd := NegativeTwo.ContactInverse.data hB
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hI : U b∈Inverse.interval := ⟨(UW_bounds hB).1.le,(UW_bounds hB).2.1.le⟩
  have hq0 : 0<Inverse.q (U b) := by linarith [(Inverse.range_data hI).2]
  have hv := hd.2.2.2.2.1
  have hden := mul_le_mul (band_q_upper hb) (band_speed_upper hb).le
    hv.le (by norm_num : (0:ℝ)≤4789/2500)
  apply (lt_div_iff₀ (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hq0) hv)).2
  nlinarith [band_ratio_lower hb]

lemma axis_hasDerivAt {b : ℝ} (hb : b∈sourceBand) :
    HasDerivAt axisValue (axisFirst b) b := by
  have hangle := NegativeTwo.ContactInverse.angle_hasDerivAt (band_mem hb)
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  exact (((hangle.const_sub (Real.pi/2)).sub
    (PLabel.outer_hasDerivAt (outer_domain (band_mem hb)))).sub_const (V 0)).congr_deriv
    (by dsimp only [axisFirst,NegativeTwo.ContactInverse.first]; ring)

lemma axis_first_negative {b : ℝ} (hb : b∈sourceBand) : axisFirst b<0 := by
  have hB := band_mem hb
  have hf := Inverse.factor_upper
    (show U b∈Inverse.interval from ⟨(UW_bounds hB).1.le,(UW_bounds hB).2.1.le⟩)
  have hc := band_correction_lower hb
  have hP := source_first_lower hb
  dsimp [axisFirst]
  linarith

lemma axis_antitone : AntitoneOn axisValue sourceBand :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (axis_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => axis_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => (axis_first_negative (Ioo_subset_Icc_self hb)).le)

lemma axis_aligned :
    axisValue bOne=Real.pi/2-P bOne-V 0 := by
  have hzero : NegativeTwo.TargetContact.B bOne 0=0 := by
    rw [NegativeTwo.TargetContact.B_zero,bOne_arc]
    norm_num
  have hd : NegativeTwo.TargetContact.Domain bOne 0 :=
    ⟨bOne_mem,by norm_num,by rw [hzero]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hzero] at he
  norm_num at he
  unfold axisValue
  rw [he,sub_zero]

theorem axis_lower {b : ℝ} (hb : b∈sourceBand) :
    (44889/50000:ℝ)<axisValue b := by
  have hb1 : bOne∈sourceBand := ⟨by linarith [bOne_bounds.1],le_rfl⟩
  have hm := axis_antitone hb hb1 hb.2
  rw [axis_aligned] at hm
  linarith [aligned_axial_value]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip
end
end
end

section
/-!
## Both original upper secondary owners by finite circle comparison

Each original weak secondary separator allows at most `.4*x` of
coordinate displacement from alignment.  Uniform derivative bounds
pay this displacement directly.  If the original primary coordinate
is below one, the primary-label tangent pays its simultaneous loss.
No zero-exit curve or contact minimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma upper_secondary_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : upperCut a b x+1-a≤(2/5)*x := by
  have ht := positive_trig hx
  have hprimary : 0≤a-1/2 := by linarith [(outer_bounds hs).1,fine_outer_endpoint_bounds.2]
  have hcos := mul_nonneg hprimary (sub_nonneg.mpr ht.2.1)
  have hsin := mul_nonneg
    (show 0≤2/5-(b-1/2) by linarith [(outer_bounds hs).2.2,outer_endpoint_bounds.2.2.2])
    ht.2.2.1
  have hangle := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤2/5)
  dsimp [upperCut]
  nlinarith

lemma P_upper_increment {l b : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hb : b∈Icc 0 outerDiagonal) (hlb : l≤b) :
    P b-P l≤(973/1000)*(b-l) := by
  have hh := P_chord_at hl hb hlb
  have hm := mul_le_mul_of_nonneg_right (P_first_bounds hb).2.le (sub_nonneg.mpr hlb)
  linarith

lemma V_upper_increment {l B : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hlB : l≤B) :
    V B-V l≤(1061/1000)*(B-l) := by
  have hm : MonotoneOn (fun t => (1061/1000)*t-V t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (VLabel.affine_difference_hasDerivAt (1061/1000)
        (outer_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => VLabel.affine_difference_hasDerivAt (1061/1000)
        (outer_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [V_first_upper (Ioo_subset_Icc_self ht)])
  have hh := hm hl hB hlB
  linarith

lemma source_primary_loss_below_one {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    PPrimaryLabel.outer 1-PPrimaryLabel.outer a≤(271/250)*(1-a) := by
  have hdom {t : ℝ} (ht : t∈Icc a 1) : t∈Icc outerDiagonal outerAxial :=
    ⟨ha.1.trans ht.1,ht.2.trans primary_one_mem.2⟩
  have hm : MonotoneOn (fun t => (271/250)*t-PPrimaryLabel.outer t) (Icc a 1) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (PPrimaryLabel.affine_difference_hasDerivAt (271/250)
        (primary_domain (hdom ht))).continuousAt.continuousWithinAt)
      (fun t ht => PPrimaryLabel.affine_difference_hasDerivAt (271/250)
        (primary_domain (hdom (Ioo_subset_Icc_self ht))))
      (fun t ht => by
        have hh := M_first_monotone (hdom (Ioo_subset_Icc_self ht)) primary_one_mem ht.2.le
        linarith [M_one_first.2])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨ha.2,le_rfl⟩ ha.2
  linarith

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut : b≤upperCut A B x := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperCut]
    linarith
  have hdisp : b+1-A≤(2/5)*x := by
    linarith [upper_secondary_displacement ht hx]
  have hb := source_mem hs
  by_cases hA : 1≤A
  · have hl : A-1∈Icc 0 outerDiagonal := by
      constructor
      · linarith
      · linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have hbase := aligned_left_original (ShortOuterOne.SameContact.arc_state hl) ht
      (show 1+(A-1)≤A by linarith)
    by_cases hbl : b≤A-1
    · have hP := P_monotone hb hl hbl
      dsimp [value] at *
      linarith [hx.1]
    · have hP := P_upper_increment hl hb (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]
  · have ha : A∈Icc outerDiagonal 1 := ⟨(outer_bounds ht).1,by linarith⟩
    have htarget := target_primary_loss_below_one ha
    have hactual : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
    have hone : VPrimaryLabel.outer 1= -V bOne := VLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at htarget
    have hsource := P_upper_increment outer_zero_mem hb hb.1
    have hgap := mul_nonneg (show 0≤1-A by linarith)
      (show (0:ℝ)≤973/1000-11/25 by norm_num)
    have hbase := reverse_aligned_axial_value
    dsimp [value]
    nlinarith [hx.1]

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut : B≤upperCut a b x := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperCut]
    linarith
  have hdisp : B+1-a≤(2/5)*x := by
    linarith [upper_secondary_displacement hs hx]
  have hB := source_mem ht
  by_cases ha : 1≤a
  · have hl : a-1∈Icc 0 outerDiagonal := by
      constructor
      · linarith
      · linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have hbase := aligned_right_original hs (ShortOuterOne.SameContact.arc_state hl)
      (show 1+(a-1)≤a by linarith)
    by_cases hBl : B≤a-1
    · have hV := V_monotone hB hl hBl
      dsimp [value] at *
      linarith [hx.1]
    · have hV := V_upper_increment hl hB (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]
  · have hA : a∈Icc outerDiagonal 1 := ⟨(outer_bounds hs).1,by linarith⟩
    have hsource := source_primary_loss_below_one hA
    have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    have hone : PPrimaryLabel.outer 1= -P bOne := PLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at hsource
    have htarget := V_upper_increment outer_zero_mem hB hB.1
    have hgap := mul_nonneg hB.1 (show (0:ℝ)≤271/250-1061/1000 by norm_num)
    have hbase := aligned_axial_value
    dsimp [value]
    nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def contact (x b : ℝ) : ℝ := lowerCut (arc b) b x
def sourceSpeed (x b : ℝ) : ℝ := ratio b*Real.cos x+Real.sin x
def contactValue (x b : ℝ) : ℝ := Real.pi/2-x-P b-V (contact x b)
def contactFirst (x b : ℝ) : ℝ :=
  -PLabel.d1 b+VLabel.d1 (contact x b)*sourceSpeed x b
def contactSecond (x b : ℝ) : ℝ :=
  -PLabel.d2 b-VLabel.d2 (contact x b)*(sourceSpeed x b)^2+
    VLabel.d1 (contact x b)*ratioD b*Real.cos x

lemma angle_mem {x : ℝ} (hx : x∈Icc 0 (1/100)) : x∈Icc 0 (7/10) :=
  ⟨hx.1,by linarith [hx.2]⟩

lemma short_cos_lower {x : ℝ} (hx : x∈Icc 0 (1/100)) :
    (19999/20000:ℝ)≤Real.cos x := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  linarith

lemma arc_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt arc (-ratio b) b := by
  exact ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)

lemma ratio_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt ratio (ratioD b) b := by
  exact ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)

lemma contact_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (contact x) (-sourceSpeed x b) b := by
  exact (((((arc_derivative hb).sub_const (1/2)).mul_const (Real.cos x)).sub
    (((hasDerivAt_id b).add_const (1/2)).mul_const (Real.sin x))).sub_const (1/2)).congr_deriv
    (by dsimp only [sourceSpeed]; ring)

lemma speed_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (sourceSpeed x) (ratioD b*Real.cos x) b := by
  exact ((ratio_derivative hb).mul_const (Real.cos x)).add_const (Real.sin x)

lemma speed_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<sourceSpeed x b := by
  have hr : 0<ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hm := mul_pos hr hc
  dsimp [sourceSpeed]
  linarith [(positive_trig hx).2.2.1]

lemma contact_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (contact x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (contact_derivative hb x).continuousAt.continuousWithinAt)
    (fun b hb => contact_derivative (Ioo_subset_Icc_self hb) x)
    (fun b hb => by linarith [speed_positive (Ioo_subset_Icc_self hb) hx])

lemma contact_upper {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : contact x b≤arc b-1 := by
  exact LowerSecondary.cut_upper (ShortOuterOne.SameContact.arc_state hb) hx

lemma contact_early {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : 0≤contact x b) :
    contact x b∈earlyTarget :=
  LowerSecondary.cut_mem (ShortOuterOne.SameContact.arc_state hb) hx hc

lemma contact_bOne {x : ℝ} (hx : x∈Icc 0 (7/10)) : contact x bOne≤0 := by
  have hh := contact_upper bOne_mem hx
  rw [bOne_arc] at hh
  linarith

lemma contactValue_hasDerivAt {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hc : contact x b∈earlyTarget) :
    HasDerivAt (contactValue x) (contactFirst x b) b := by
  have hV := (VLabel.outer_hasDerivAt (outer_domain (early_mem hc))).comp b
    (contact_derivative hb x)
  exact (((PLabel.outer_hasDerivAt (outer_domain hb)).const_sub (Real.pi/2-x)).sub hV).congr_deriv
    (by dsimp only [contactFirst]; ring)

lemma contactFirst_hasDerivAt {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hc : contact x b∈earlyTarget) :
    HasDerivAt (contactFirst x) (contactSecond x b) b := by
  have hV := (VLabel.d1_hasDerivAt (outer_domain (early_mem hc))).comp b
    (contact_derivative hb x)
  exact ((PLabel.d1_hasDerivAt (outer_domain hb)).neg.add
    (hV.mul (speed_derivative hb x))).congr_deriv (by dsimp only [contactSecond,Function.comp_apply]; ring)

lemma contactSecond_lower {b x : ℝ} (hb : b∈Icc 0 bOne)
    (hx : x∈Icc 0 (1/100)) (hc : contact x b∈earlyTarget) :
    (1/10:ℝ)<contactSecond x b := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hP := source_second_upper hb
  have hV := target_first_lower hc
  have hD := source_ratioD_lower hB
  have hcos := short_cos_lower hx
  have hbad := mul_nonneg
    (show 0≤ -VLabel.d2 (contact x b) by linarith [V_second_upper (early_mem hc)])
    (sq_nonneg (sourceSpeed x b))
  have hprod := mul_le_mul hV.le hD.le (by norm_num : (0:ℝ)≤557/1000)
    (by linarith : 0≤VLabel.d1 (contact x b))
  have hprod0 : 0≤VLabel.d1 (contact x b)*ratioD b :=
    mul_nonneg (by linarith) (by linarith)
  have hprod' := mul_le_mul hprod hcos (by norm_num : (0:ℝ)≤19999/20000) hprod0
  dsimp [contactSecond]
  nlinarith

lemma short_speed_upper {b x : ℝ} (hb : b∈Icc 0 bOne)
    (hx : x∈Icc 0 (1/100)) : sourceSpeed x b<871/1000 := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hp := positive_trig (angle_mem hx)
  have hr := source_ratio_upper hb
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hB).1]
  have hm := mul_le_mul_of_nonneg_left hp.2.1 hr0
  dsimp [sourceSpeed]
  nlinarith [hp.2.2.2.2.1,hx.2]

lemma first_zero_negative {b x : ℝ} (hb : b∈sourceBand)
    (hx : x∈Icc 0 (1/100)) (hzero : contact x b=0) :
    contactFirst x b<0 := by
  have hB : b∈Icc 0 bOne := ⟨by linarith [hb.1],hb.2⟩
  have hp := speed_positive (band_mem hb) (angle_mem hx)
  have hs := short_speed_upper hB hx
  have hV := V_first_upper outer_zero_mem
  have hm := mul_le_mul hV.le hs.le hp.le (by norm_num : (0:ℝ)≤1061/1000)
  dsimp [contactFirst]
  rw [hzero]
  linarith [source_first_lower hb]

lemma reference_contact_positive {x : ℝ} (hx : x∈Icc 0 (1/100)) :
    0<contact x (31/40) := by
  have hu := source_reference_radical.1
  have hc := short_cos_lower hx
  have hs : Real.sin x≤1/100 :=
    (positive_trig (angle_mem hx)).2.2.2.2.1.trans hx.2
  have hmul := mul_le_mul
    (show (25663/50000:ℝ)≤U (31/40)-1 by linarith)
    hc (by norm_num : (0:ℝ)≤19999/20000)
    (by linarith : 0≤U (31/40)-1)
  have hsin := mul_le_mul_of_nonneg_left hs
    (by norm_num : (0:ℝ)≤51/40)
  have he : contact x (31/40)=(U (31/40)-1)*Real.cos x-(51/40)*Real.sin x-1/2 := by
    simp only [contact,lowerCut,U]
    ring
  rw [he]
  linarith

lemma zero_endpoint_band {x β : ℝ} (hx : x∈Icc 0 (1/100))
    (hβ : β∈Icc 0 bOne) (hz : contact x β=0) : β∈sourceBand := by
  refine ⟨?_,hβ.2⟩
  by_contra h
  have horder : β≤31/40 := by linarith
  have hm := contact_antitone (angle_mem hx)
    ⟨hβ.1,hβ.2.trans bOne_mem.2⟩ source_reference_mem horder
  rw [hz] at hm
  linarith [reference_contact_positive hx]

lemma zero_contact_value {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hz : contact x b=0) :
    contactValue x b=axisValue b := by
  have hzero : NegativeTwo.TargetContact.B b x=0 := by
    change 1/2-(arc b-1/2)*Real.cos x+(b+1/2)*Real.sin x=0
    dsimp [contact,lowerCut] at hz
    linarith
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hzero]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hzero] at he
  norm_num at he
  unfold contactValue axisValue
  rw [hz,he]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip
end
end
end

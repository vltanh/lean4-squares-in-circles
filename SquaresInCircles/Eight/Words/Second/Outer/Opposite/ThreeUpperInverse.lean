module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeCapRatio
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreePrimaryMotion
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoPrimaryInverse

/-!
# Eight squares: the physical upper-primary inverse motion

The inverse rotation is the same explicit circle function as for edge
two.  Here the literal edge-three target label is paid by the whole-arc
cap-ratio inequality.  The proof identifies every inverse point with
its original primary contact before applying that inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperInverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

abbrev X := OppositeTwo.PrimaryInverse.X
abbrev F := OppositeTwo.PrimaryInverse.F
abbrev shifts := OppositeTwo.PrimaryInverse.shifts
abbrev speed := OppositeTwo.PrimaryInverse.speed
abbrev radius := OppositeTwo.PrimaryInverse.radius
def quotient (B x : ℝ) : ℝ :=
  (Real.cos x+ratio B*Real.sin x)/upperPrimarySpeed B x

lemma primary_shift {a b : ℝ} (hs : OuterState a b) : a-1/2∈shifts := by
  have ha := NegativeTwo.primary_mem hs
  constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]

lemma quotient_hasDerivAt {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (quotient B) (-ratio B/(upperPrimarySpeed B x)^2) x := by
  have hv := upperPrimarySpeed_positive hB hx
  have hu : arc B+1/2≠0 := (U_positive (outer_domain hB)).ne'
  have hspeed : HasDerivAt (upperPrimarySpeed B)
      (-(arc B-1/2)*Real.sin x+(B+1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (B+1/2))).congr_deriv (by ring)
  have hd := ((Real.hasDerivAt_cos x).fun_add
    ((Real.hasDerivAt_sin x).const_mul (ratio B))).fun_div hspeed hv.ne'
  refine hd.congr_deriv ?_
  congr 1
  have hr : ratio B*(arc B+1/2)=B+1/2 := div_mul_cancel₀ (B+1/2) hu
  have ht := Real.sin_sq_add_cos_sq x
  simp only [upperPrimarySpeed]
  linear_combination (ratio B*(arc B-1/2)-(B+1/2))*ht+hr

lemma quotient_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (quotient B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (quotient_hasDerivAt hB ht).continuousAt.continuousWithinAt)
    (fun t ht => quotient_hasDerivAt hB (Ioo_subset_Icc_self ht))
    (fun t ht => by
      exact div_nonpos_of_nonpos_of_nonneg
        (by linarith [(outer_ratio_bounds hB).1]) (sq_nonneg _))

lemma quotient_paid {B x : ℝ} (hB : B∈Icc (1/5) outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : LLabel.d1 B<quotient B x := by
  have hb := CapRatio.domain hB
  have hcap := CapRatio.positive hB
  have hv := upperPrimarySpeed_positive hb (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hV : CapRatio.V B=upperPrimarySpeed B (7/10) := by
    dsimp [CapRatio.V,CapRatio.c,CapRatio.s,upperPrimarySpeed,U,W]
    ring
  have hp : LLabel.d1 B<quotient B (7/10) := by
    apply (lt_div_iff₀ hv).2
    dsimp [CapRatio.F,CapRatio.c,CapRatio.s] at hcap
    rw [hV] at hcap
    linarith
  exact hp.trans_le (quotient_antitone hb hx (by norm_num) hx.2)

lemma X_monotone {z : ℝ} (hz : z∈shifts) :
    MonotoneOn (X z) (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t ht => (OppositeTwo.PrimaryInverse.X_source_hasDerivAt ht hz).continuousAt.continuousWithinAt)
    (fun t ht => OppositeTwo.PrimaryInverse.X_source_hasDerivAt (Ioo_subset_Icc_self ht) hz)
  intro t ht
  have hb := Ioo_subset_Icc_self ht
  have hd := OppositeTwo.PrimaryInverse.data hb hz
  have hu := U_positive (outer_domain hb)
  have hq := NegativeTwo.Inverse.actual_q_positive hb
  have hfactor := NegativeTwo.Inverse.factor_lower hu (by linarith : 0<NegativeTwo.Inverse.q (U t))
  have hratio := outer_ratio_bounds hb
  have hn : 0≤z*ratio t/(NegativeTwo.Inverse.q (U t)*speed z t) := by
    apply div_nonneg (mul_nonneg hz.1 (by linarith [hratio.1]))
    exact mul_nonneg (by linarith) hd.2.2.1.le
  dsimp [F,OppositeTwo.PrimaryInverse.F]
  linarith

lemma X_nonnegative {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z≤W B) : 0≤X z B := by
  have hr := (OppositeTwo.PrimaryInverse.data hB
    (show (0:ℝ)∈shifts by norm_num [shifts,OppositeTwo.PrimaryInverse.shifts])).1
  have hquot := div_le_div_of_nonneg_right hz (show 0≤radius B by linarith)
  have hh := Real.arcsin_le_arcsin hquot
  have ha := OppositeTwo.PrimaryInverse.aligned hB (z := W B) rfl
  dsimp [X,OppositeTwo.PrimaryInverse.X,OppositeTwo.PrimaryInverse.inverseAngle,
    NegativeTwo.ContactInverse.angle] at ha ⊢
  linarith

lemma X_contact {B z : ℝ} (hB : B∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    upperPrimary B (X z B)=z+1/2 := by
  have hd := OppositeTwo.PrimaryInverse.data hB hz
  have hr : 0<radius B := by linarith [hd.1]
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hB hz
  have htr := NegativeTwo.ContactInverse.base_trig hB
  have hs := Real.sin_arcsin ha.1.le ha.2.le
  dsimp [upperPrimary,X,OppositeTwo.PrimaryInverse.X,
    OppositeTwo.PrimaryInverse.inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,Real.sin_add,Real.cos_add,
    htr.1,htr.2,hs]
  dsimp [U,W]
  field_simp [hr.ne']
  have hc := UW_circle (outer_domain hB)
  have hq := hd.2.1
  dsimp [OppositeTwo.Inverse.q,NegativeTwo.Inverse.q,U,W] at hc hq
  have hc' := congrArg (fun v : ℝ => z*v) hc
  have hq' := congrArg (fun v : ℝ => z*v) hq
  nlinarith [hc',hq']

lemma physical_speed {B z x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈shifts) (hx : x∈Icc 0 (7/10))
    (hc : upperPrimary B x=z+1/2) : speed z B=upperPrimarySpeed B x := by
  have hd := OppositeTwo.PrimaryInverse.data hB hz
  have hp := upperPrimarySpeed_positive hB hx
  have hn := upperPrimary_norm hB x
  rw [hc] at hn
  have hq := hd.2.2.2
  dsimp [OppositeTwo.Inverse.q,NegativeTwo.Inverse.q,U] at hq
  nlinarith [hd.2.2.1]

lemma physical_F {B z x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈shifts) (hx : x∈Icc 0 (7/10))
    (hc : upperPrimary B x=z+1/2) : F z B=quotient B x := by
  have he := physical_speed hB hz hx hc
  have hu := U_positive (outer_domain hB)
  have hv := upperPrimarySpeed_positive hB hx
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hzform : z=W B*Real.cos x-(U B-1)*Real.sin x := by
    dsimp [upperPrimary,U,W] at hc ⊢
    linarith
  have hvform : upperPrimarySpeed B x=(U B-1)*Real.cos x+W B*Real.sin x := by
    dsimp [upperPrimarySpeed,U,W]
    ring
  change (Q0-U B)/(U B*NegativeTwo.Inverse.q (U B))+
      z*(W B/U B)/(NegativeTwo.Inverse.q (U B)*speed z B)=
        (Real.cos x+(W B/U B)*Real.sin x)/upperPrimarySpeed B x
  rw [he,hzform]
  field_simp [hu.ne',hq.ne',hv.ne']
  rw [hvform]
  dsimp [NegativeTwo.Inverse.q]
  linear_combination Real.cos x*(UW_circle (outer_domain hB))

lemma inverse_paid {B z : ℝ} (hB : B∈Icc (1/5) outerDiagonal)
    (hz : z∈shifts) (hx : X z B∈Icc 0 (7/10)) : LLabel.d1 B<F z B := by
  rw [physical_F (CapRatio.domain hB) hz hx (X_contact (CapRatio.domain hB) hz)]
  exact quotient_paid hB hx

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperInverse

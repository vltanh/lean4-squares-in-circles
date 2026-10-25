module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJHessian
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactInverse

/-!
# Eight squares: the actual inverse-contact curve for the P/J Hessian argument

The angle is the explicit physical inverse
of the same-sign contact.  Differentiation along (1,-.7) realizes the
negative Hessian direction on an actual curve of original contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open NegativeTwo.Inverse (q factor factorD)

def inverseAngle (s B : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle (s-1/2) B
def inverseValue (s B : ℝ) : ℝ := inverseAngle s B+PLabel.outer s-JLabel.outer B
def inverseDirection (s B : ℝ) : ℝ :=
  -1/NegativeTwo.ContactInverse.speed (s-1/2) B-
    (7/10)*(factor (U B)+(s-1/2)*ratio B/
      (q (U B)*NegativeTwo.ContactInverse.speed (s-1/2) B))
def inverseDirectionSecond (s B : ℝ) : ℝ :=
  -((s-1/2)+(7/5)*ratio B)/(NegativeTwo.ContactInverse.speed (s-1/2) B)^3+
    (49/100)*PJCritical.inverseTarget (U B) (ratio B) (s-1/2)
      (NegativeTwo.ContactInverse.speed (s-1/2) B)
def lineValue (s B t : ℝ) : ℝ := inverseValue (s+t) (B-(7/10)*t)
def lineFirst (s B t : ℝ) : ℝ :=
  inverseDirection (s+t) (B-(7/10)*t)+PLabel.d1 (s+t)+(7/10)*JLabel.d1 (B-(7/10)*t)
def lineSecond (s B t : ℝ) : ℝ :=
  inverseDirectionSecond (s+t) (B-(7/10)*t)+PLabel.d2 (s+t)-
    (49/100)*JLabel.d2 (B-(7/10)*t)

lemma inverse_data {s B : ℝ} (hs : s∈Icc 0 outerDiagonal)
    (_hB : B∈Icc 0 outerDiagonal) :
    s-1/2∈Icc (-(1/2):ℝ) (2/5) := by
  constructor <;> linarith [hs.1,hs.2,outer_endpoint_bounds.2.2.2]

lemma inverse_contact {s B : ℝ} (hs : s∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) : b B (inverseAngle s B)=s := by
  have hh := NegativeTwo.ContactInverse.contact hB (inverse_data hs hB)
  dsimp [inverseAngle,b]
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  dsimp [NegativeTwo.TargetContact.B] at hh
  linarith [hh.1]

lemma inverse_original {B x : ℝ} (hd : Domain B x) :
    inverseAngle (b B x) B=x := by
  have hz := inverse_data hd.2.2 hd.1
  have hd' := NegativeTwo.ContactInverse.data hd.1 hz
  have hr : 0<NegativeTwo.ContactInverse.radius B := by linarith [hd'.2.2.1]
  have ht := NegativeTwo.ContactInverse.base_trig hd.1
  have ha := NegativeTwo.ContactInverse.base_bounds hd.1
  have hy : -(Real.pi/2)≤Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B ∧
      Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B≤Real.pi/2 := by
    constructor <;> linarith [hd.2.1.1,hd.2.1.2,ha.1,ha.2,Real.pi_gt_three]
  have he : (b B x-1/2)/NegativeTwo.ContactInverse.radius B=
      Real.sin (Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B) := by
    rw [Real.sin_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,ht.1,ht.2]
    dsimp [b,U,W]
    field_simp [hr.ne']
    ring
  dsimp [inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [he,Real.arcsin_sin hy.1 hy.2]
  ring

lemma inverse_speed_original {B x : ℝ} (hd : Domain B x) :
    NegativeTwo.ContactInverse.speed (b B x-1/2) B=v B x := by
  have h := NegativeTwo.ContactInverse.data hd.1 (inverse_data hd.2.2 hd.1)
  have hn := norm_identity hd.1 x
  have hv := v_positive hd.1 hd.2.1
  nlinarith [h.2.2.2.2.1,h.2.2.2.2.2]

lemma inverse_line_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => inverseAngle (s+y) (B-(7/10)*y))
      (inverseDirection (s+t) (B-(7/10)*t)) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hr : 0<NegativeTwo.ContactInverse.radius (B-(7/10)*t) := by linarith [hd.2.2.1]
  have hw := hd.2.2.2.2.1
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hsource : HasDerivAt (fun y : ℝ => s+y-1/2) 1 t :=
    (((hasDerivAt_id' t).const_add s).sub_const (1/2))
  have hrad := (NegativeTwo.ContactInverse.radius_hasDerivAt hB).comp t htarget
  have harg := hsource.fun_div hrad hr.ne'
  have ha := NegativeTwo.ContactInverse.argument_bounds hB hz
  have hasin := (Real.hasDerivAt_arcsin
    (by linarith : (s+t-1/2)/NegativeTwo.ContactInverse.radius (B-(7/10)*t)≠-1)
    (by linarith : (s+t-1/2)/NegativeTwo.ContactInverse.radius (B-(7/10)*t)≠1)).comp t harg
  have hbase := (NegativeTwo.ContactInverse.base_hasDerivAt hB).comp t htarget
  have hder := (hbase.fun_add hasin).const_sub (Real.pi/2)
  refine hder.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [NegativeTwo.ContactInverse.inverse_root hB hz]
  dsimp only [inverseDirection]
  rw [←hd.2.2.2.1]
  generalize NegativeTwo.ContactInverse.radius (B-(7/10)*t)=r at hr ⊢
  generalize NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)=v at hw ⊢
  have hr0 := hr.ne'
  have hw0 := hw.ne'
  field_simp
  ring

lemma inverse_direction_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => inverseDirection (s+y) (B-(7/10)*y))
      (inverseDirectionSecond (s+t) (B-(7/10)*t)) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hu := hd.1
  have hw := hd.2.2.2.2.1
  have hq : 0<q (U (B-(7/10)*t)) := by linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hsource : HasDerivAt (fun y : ℝ => s+y-1/2) 1 t :=
    (((hasDerivAt_id' t).const_add s).sub_const (1/2))
  have hU0 := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
      (1/2)).comp t htarget
  have hU : HasDerivAt (fun y => U (B-(7/10)*y)) (-ratio (B-(7/10)*t)*(-(7/10))) t := hU0
  have hQ := (NegativeTwo.Inverse.q_hasDerivAt (U (B-(7/10)*t))).comp t hU
  have hR := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).comp t htarget
  have hF := (NegativeTwo.Inverse.factor_hasDerivAt hu.ne' hq.ne').comp t hU
  have hrad : q (U (B-(7/10)*t))-(s+t-1/2)^2≠0 := by
    nlinarith [hd.2.2.2.2.2,sq_pos_of_pos hw]
  have hspeed := (hQ.fun_sub (hsource.fun_pow 2)).sqrt hrad
  have hden := hQ.fun_mul hspeed
  have hweight := (hsource.fun_mul hR).fun_div hden (mul_ne_zero hq.ne' hw.ne')
  have hrecip := (hasDerivAt_const t (-(1:ℝ))).fun_div hspeed hw.ne'
  have hder := hrecip.fun_sub ((hF.fun_add hweight).const_mul (7/10))
  refine hder.congr_deriv ?_
  have hsp : Real.sqrt (q (U (B-(7/10)*t))-(s+t-1/2)^2)=
      NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t) := rfl
  have hrD : ratioD (B-(7/10)*t)=Q0/(U (B-(7/10)*t))^3 := rfl
  simp only [Function.comp_apply,inverseDirectionSecond,PJCritical.inverseTarget,
    PJCritical.heightFactorD,NegativeTwo.Inverse.brace,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  rw [hsp,hrD]
  have hn := hd.2.2.2.2.2
  generalize NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)=v at hw hn ⊢
  generalize q (U (B-(7/10)*t))=Q at hq hn ⊢
  generalize factorD (U (B-(7/10)*t))=F
  generalize U (B-(7/10)*t)=u at hu ⊢
  generalize ratio (B-(7/10)*t)=ρ
  generalize s+t-1/2=z at hn ⊢
  have hu0 := hu.ne'
  have hq0 := hq.ne'
  have hw0 := hw.ne'
  field_simp
  linear_combination (-35000*Q*ρ*u^3)*hn

lemma lineValue_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (lineValue s B) (lineFirst s B t) t := by
  have hsource : HasDerivAt (fun y : ℝ => s+y) 1 t := (hasDerivAt_id' t).const_add s
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hP0 := (PLabel.outer_hasDerivAt (outer_domain hs)).comp t hsource
  have hP : HasDerivAt (fun y => PLabel.outer (s+y)) (PLabel.d1 (s+t)*1) t := hP0
  have hJ0 := (JLabel.outer_hasDerivAt (outer_domain hB)).comp t htarget
  have hJ : HasDerivAt (fun y => JLabel.outer (B-(7/10)*y))
      (JLabel.d1 (B-(7/10)*t)*(-(7/10))) t := hJ0
  exact (((inverse_line_hasDerivAt hs hB).fun_add hP).fun_sub hJ).congr_deriv
    (by dsimp only [lineFirst]; ring)

lemma lineFirst_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (lineFirst s B) (lineSecond s B t) t := by
  have hsource : HasDerivAt (fun y : ℝ => s+y) 1 t := (hasDerivAt_id' t).const_add s
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hP0 := (PLabel.d1_hasDerivAt (outer_domain hs)).comp t hsource
  have hP : HasDerivAt (fun y => PLabel.d1 (s+y)) (PLabel.d2 (s+t)*1) t := hP0
  have hJ0 := (JLabel.d1_hasDerivAt (outer_domain hB)).comp t htarget
  have hJ : HasDerivAt (fun y => JLabel.d1 (B-(7/10)*y))
      (JLabel.d2 (B-(7/10)*t)*(-(7/10))) t := hJ0
  exact (((inverse_direction_hasDerivAt hs hB).fun_add hP).fun_add
    (hJ.const_mul (7/10))).congr_deriv (by dsimp only [lineSecond]; ring)

lemma stationary_line_negative {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : lineSecond (b B x) B 0< -(1/200:ℝ) := by
  have hneg := hessian_direction_negative hd hstat
  have hv := v_positive hd.1 hd.2.1
  have hp := p_positive hd.2.2
  have hprod : p (b B x)*v B x=1 := by dsimp [p,angleFirst] at *; linarith
  have hcube : 1/(v B x)^3=(p (b B x))^3 := by
    field_simp
    rw [← mul_pow,mul_comm,hprod]
    norm_num
  have heq : lineSecond (b B x) B 0=E (b B x)-(7/5)*ratio B*(p (b B x))^3+
      (49/100)*(PJCritical.inverseTarget (U B) (ratio B) (b B x-1/2) (v B x)-JLabel.d2 B) := by
    simp only [lineSecond,inverseDirectionSecond,add_zero,mul_zero,sub_zero,
      inverse_speed_original hd,E]
    rw [div_eq_mul_one_div _ ((v B x)^3),hcube]
    ring
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ

module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperContact

/-!
# Uniform curvature of the six actual primary contacts

Uncompiled transcription of (9)--(12), (18) of the complementary
upper-primary note and (6)--(8), (25) of the three-family note.
The source and target radicals are bounded on the actual coupled
contact. The quadratic remainder is retained for the two owners whose
minimum can be in the interior of that contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

def curvatureFloor : Row→ℝ := ![86/100,1,44/100,6/10,52/100,67/100]
def targetDenom (r : Row) : ℝ := if P r<0 then 1399/1000 else 383/200

theorem source_root_bounds {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<arc a+1/2 ∧ arc a+1/2<(7/5:ℝ) := by
  have hb := SameContact.primary_secondary_mem ha
  exact ⟨SameContact.shifted_positive (Same.primary_domain ha),
    by linarith [hb.2,ShortMixedZero.fine_diagonal_bounds.2]⟩

theorem target_root_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1399/1000:ℝ)<arc B+1/2 ∧ arc B+1/2<(383/200:ℝ) := by
  have hb := outer_bounds (SameContact.arc_state hB)
  exact ⟨by linarith [hb.1,ShortMixedZero.fine_diagonal_bounds.1],
    by linarith [hb.2.1,ShortOuterZero.fine_axial_bounds.2]⟩

theorem source_ratioD_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    Q0/(7/5:ℝ)^3≤ratioD a := by
  have hr := source_root_bounds ha
  have hp := pow_le_pow_left₀ hr.1.le hr.2.le 3
  dsimp [ratioD]
  apply (le_div_iff₀ (pow_pos hr.1 3)).2
  norm_num [Q0] at *
  nlinarith

theorem target_ratioD_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    Q0/(383/200:ℝ)^3≤ratioD B ∧ ratioD B≤Q0/(1399/1000:ℝ)^3 := by
  have hr := target_root_bounds hB
  have hp0 : 0<arc B+1/2 := by linarith
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hr.1.le 3
  have hhi := pow_le_pow_left₀ hp0.le hr.2.le 3
  constructor
  · dsimp [ratioD]
    apply (le_div_iff₀ (pow_pos hp0 3)).2
    norm_num [Q0] at *
    nlinarith
  · dsimp [ratioD]
    apply (div_le_iff₀ (pow_pos hp0 3)).2
    norm_num [Q0] at *
    nlinarith

theorem signed_target_curvature (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    P r*Q0/(targetDenom r)^3≤P r*ratioD B := by
  have hr := target_ratioD_bounds hB
  by_cases hP : P r<0
  · have hh := mul_le_mul_of_nonpos_left hr.2 hP.le
    simpa [targetDenom,hP,mul_div_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hr.1 (le_of_not_gt hP)
    simpa [targetDenom,hP,mul_div_assoc] using hh

theorem curvature_of_cos (r : Row) {B x k : ℝ} (hd : Domain B x)
    (hk : 0<k) (hcos : k<Real.cos x) :
    q r*Q0*k^2/(7/5:ℝ)^3+P r*Q0/(targetDenom r)^3<second r B x := by
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hL : 0<sourceD r (contact B x) := by
    linarith [sourceD_lower r hd.2.2,(coefficients r).2.2.1]
  have hk' : k<stateSpeed B x := hcos.trans_le (stateSpeed_lower hd.1 hd.2.1)
  have hsquare : k^2<(stateSpeed B x)^2 := by nlinarith
  have hr := source_ratioD_lower hd.2.2
  have hfirst := mul_lt_mul_of_pos_left hsquare
    (mul_pos hq (show 0<Q0/(7/5:ℝ)^3 by norm_num [Q0]))
  have hfirst' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr hq.le) (sq_nonneg (stateSpeed B x))
  have hsecond := signed_target_curvature r hd.1
  have hdrop := mul_nonneg
    (SameContact.ratioD_pos (SameContact.outer_domain hd.1)).le
    (mul_nonneg hL.le (positive_trig hd.2.1).2.2.1)
  have e1 : second r B x=q r*ratioD (contact B x)*(stateSpeed B x)^2+
      ratioD B*(sourceD r (contact B x)*Real.sin x)+P r*ratioD B := by
    dsimp only [second,sourceDD]
    ring
  have e2 : q r*Q0*k^2/(7/5:ℝ)^3=q r*(Q0/(7/5:ℝ)^3)*k^2 := by ring
  rw [e1,e2]
  linarith

theorem curvature_positive (r : Row) : 0<curvatureFloor r := by
  fin_cases r <;> norm_num [curvatureFloor]

theorem curvature (r : Row) {B x : ℝ} (hd : Domain B x) :
    curvatureFloor r<second r B x := by
  have hh := curvature_of_cos r hd (by norm_num : (0:ℝ)<191/250)
    (lt_trans (by norm_num) (positive_trig hd.2.1).1)
  fin_cases r <;> norm_num [curvatureFloor,targetDenom,p,q,P,Q0] at * <;> linarith

theorem early_cos {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (99417/100000:ℝ)<Real.cos x := by
  have hnum : (99417/100000:ℝ)<HighOrderTaylor.C14 (27/250) := by
    norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]
  have ht := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤27/250 by norm_num)
  have hm := cos_anti (before_domain he hx).2.1
    (by norm_num : (27/250:ℝ)∈Icc 0 (7/10))
    (show x≤27/250 by linarith [(event_bounds he).2.1,hx.2])
  exact hnum.trans_le (ht.trans hm)

theorem early_curvature_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x≤e) : (39/25:ℝ)<second 0 B x := by
  have hh := curvature_of_cos 0 hd (by norm_num : (0:ℝ)<99417/100000)
    (early_cos he ⟨hd.2.1.1,hx⟩)
  norm_num [targetDenom,q,P,Q0] at hh
  linarith

theorem early_curvature_one {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x≤e) : (38/25:ℝ)<second 1 B x := by
  have hh := curvature_of_cos 1 hd (by norm_num : (0:ℝ)<99417/100000)
    (early_cos he ⟨hd.2.1.1,hx⟩)
  norm_num [targetDenom,q,P,Q0] at hh
  linarith

theorem contact_tangent (r : Row) {D B x κ : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B)
    (hκ : ∀E∈Icc D B,κ≤ second r E x) :
    value r D x+first r D x*(B-D)+κ/2*(B-D)^2≤value r B x := by
  exact CenteredMonomialBounds.second_derivative_tangent_lower
    (fun E hE => value_target_hasDerivAt r (between_domain hD hB hE))
    (fun E hE => first_target_hasDerivAt r (between_domain hD hB hE)) hκ
    (show D∈Icc D B from ⟨le_rfl,hDB⟩)
    (show B∈Icc D B from ⟨hDB,le_rfl⟩)

theorem endpoint_minimum (r : Row) {D B x : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B) (hfirst : 0≤first r D x) :
    value r D x≤value r B x := by
  have hh := contact_tangent r hD hB hDB
    (fun E hE => (curvature r (between_domain hD hB hE)).le)
  have hp := mul_nonneg hfirst (sub_nonneg.mpr hDB)
  have hq := mul_nonneg (div_nonneg (curvature_positive r).le (by norm_num : (0:ℝ)≤2))
    (sq_nonneg (B-D))
  linarith

theorem contact_remainder (r : Row) {D B x κ h : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B)
    (hκ0 : 0<κ) (hh0 : 0≤h) (hfirst : -h≤first r D x)
    (hκ : ∀E∈Icc D B,κ≤ second r E x) :
    value r D x-h^2/(2*κ)≤value r B x := by
  have ht := contact_tangent r hD hB hDB hκ
  have hp := mul_le_mul_of_nonneg_right hfirst (sub_nonneg.mpr hDB)
  have hs := sq_nonneg (κ*(B-D)-h)
  have hdiv : h^2/(2*κ)*(2*κ)=h^2 := by
    field_simp [ne_of_gt hκ0]
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper

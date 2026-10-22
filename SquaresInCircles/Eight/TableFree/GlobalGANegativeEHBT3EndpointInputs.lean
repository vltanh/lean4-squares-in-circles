module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2EndpointData

/-!
# Exact original-angle inputs for all thirty-four EH1/BT3 endpoints

Uncompiled Section 8. The native polynomial coordinate is x=theta-b.
All angle domains, coefficient signs, and the q-star replacement are
proved before the radical transfer. The small-high A-support allowance
follows from the already proved sixth-order bound, since
(151/500)*(8/15)^2 < 43/500. No additional A-support hypothesis is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointInputs
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate
open WholeIntervalPolynomial
open PositiveTD.Certificate (taylor_bounds)

abbrev thetaAt (r : Row) (x : ℝ) : ℝ := x+(left r:ℝ)
def aAt : Split→ℝ→ℝ | .atA,t=>t | .atT,_=>0
def zAt : Split→ℝ→ℝ | .atA,_=>0 | .atT,t=>t
abbrev Kactual (r : Row) (x : ℝ) := Explicit.k (family r) (thetaAt r x)
abbrev Lactual (r : Row) (x : ℝ) := Explicit.l (family r) (thetaAt r x)
abbrev Mactual (r : Row) (x : ℝ) := Explicit.m (family r) (thetaAt r x)
def Cactual (r : Row) (ep : Split) (x : ℝ) :=
  Explicit.c (family r) (thetaAt r x) (zAt ep (thetaAt r x))
def argument (r : Row) (x : ℝ) : ℝ :=
  if positive r then gainArgument r (thetaAt r x)-thetaAt r x
  else thetaAt r x-gainArgument r (thetaAt r x)

@[simp] theorem theta_eval (r : Row) (x : ℝ) : aeval x (theta r)=thetaAt r x := by
  simp [theta,thetaAt]
@[simp] theorem d_eval (r : Row) (x : ℝ) : aeval x (d r)=argument r x := by
  simp only [d,argument]
  split <;> simp_all only [map_sub,s_eval,theta_eval]

lemma original_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    thetaAt r x∈Icc (left r:ℝ) (right r:ℝ) := by
  dsimp [thetaAt,width] at *
  push_cast at *
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma frame_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    thetaAt r x∈Icc 0 frameCap := total_domain r (original_domain r hx)

lemma split_domains (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) :
    aAt ep (thetaAt r x)∈Icc 0 frameCap ∧
      zAt ep (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases ep <;> simp [aAt,zAt,ht,show (0:ℝ)≤frameCap by norm_num [frameCap]]

lemma gain_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    gainArgument r (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases r <;> simp [gainArgument,equal,u,v,ht,frameCap]
  split <;> norm_num [u,v,frameCap]

lemma argument_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    argument r x∈Icc 0 frameCap := by
  have ht := original_domain r hx
  cases r <;>
    norm_num [argument,positive,equal,gainArgument,left,right,u,v,frameCap] at ht ⊢
  all_goals first
    | exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
    | split <;> norm_num [u,v] <;>
        exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩

/-- Five elementary coefficient margins, each on its full native interval. -/
def coefficientMargin (r : Row) : Fin 5→ℚ[X] :=
  ![k r-C (1/2),l r-C (1/2),m r-C (1/2),1-k r,l r-k r]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_certificate : ∀r : Row,∀i : Fin 5,
    centered 0 (width r) (coefficientMargin r i)=
      expansion 3 (centered 0 (width r) (coefficientMargin r i)) ∧
    (0:ℚ)<lowerOn 3 0 (width r) (coefficientMargin r i) := by decide

lemma coefficient_margin_positive (r : Row) (i : Fin 5) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (coefficientMargin r i) := by
  have hh := coefficient_certificate r i
  exact positive_on_interval (interval_positive r) hh.1 hh.2 hx

lemma coefficient_bounds (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    0<Kactual r x ∧ 0<Lactual r x ∧ 0<Mactual r x ∧
      Kactual r x≤1 ∧ Kactual r x≤Lactual r x := by
  have hk := coefficient_margin_positive r 0 hx
  have hl := coefficient_margin_positive r 1 hx
  have hm := coefficient_margin_positive r 2 hx
  have hk1 := coefficient_margin_positive r 3 hx
  have hkl := coefficient_margin_positive r 4 hx
  simp only [coefficientMargin,Matrix.cons_val_zero,Matrix.cons_val_succ,
    map_sub,map_one,aeval_C,k_eval,l_eval,m_eval] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma c_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<Cactual r ep x := by
  have hm := (coefficient_bounds r hx).2.2.1
  have hz := (split_domains r ep hx).2
  have hf := PositiveTD.Explicit.factor_lower hz
  change 0<Mactual r x*(Real.cos (zAt ep (thetaAt r x))+
    PositiveTD.eta*Real.sin (zAt ep (thetaAt r x)))
  exact mul_pos hm (by linarith)

lemma c_upper (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : Cactual r ep x≤aeval x (cUpper r ep) := by
  have hp := coefficient_bounds r hx
  have ht := taylor_bounds (frame_domain r hx)
  cases ep
  · simp [Cactual,Explicit.c,zAt,PositiveBT3.tilted,cUpper]
  · have hh := mul_le_mul_of_nonneg_left
      (show Real.cos (thetaAt r x)+PositiveTD.eta*Real.sin (thetaAt r x)≤
        aeval (thetaAt r x) PositiveTD.Certificate.C12+
          PositiveTD.eta*aeval (thetaAt r x) PositiveTD.Certificate.S9 by
            dsimp [PositiveTD.eta]; linarith [ht.2.2.2.2.2,ht.2.2.1]) hp.2.2.1.le
    simpa [Cactual,Explicit.c,zAt,PositiveBT3.tilted,cUpper,aeval_comp,
      Certificate.eta,PositiveTD.eta] using hh

/-- A q-star comparison is needed only for the high-family B-negative rows. -/
def needs_qstar : Row→Bool
  | .smallHigh i => decide (i=2)
  | .farHigh i _ => decide (i=2)
  | _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem qstar_certificate : ∀r : Row,needs_qstar r=true →
    centered 0 (width r) (qStar r-m r)=
      expansion 3 (centered 0 (width r) (qStar r-m r)) ∧
    (0:ℚ)<lowerOn 3 0 (width r) (qStar r-m r) := by decide

lemma qstar_bound (r : Row) (hr : needs_qstar r=true) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) :
    max (Lactual r x) (Mactual r x)≤aeval x (qStar r) := by
  have hc := qstar_certificate r hr
  have hm := positive_on_interval (interval_positive r) hc.1 hc.2 hx
  simp only [map_sub,m_eval] at hm
  have ht := frame_domain r hx
  refine max_le ?_ (by linarith)
  simp only [qStar,map_add,map_mul,map_sub,aeval_C,l_eval,theta_eval]
  norm_num [Certificate.h,frameCap] at ht ⊢
  linarith [ht.2]

/-- The quartic small-high allowance is weaker than the existing sixth-order
support bound on the whole native interval. -/
lemma small_high_charge {t : ℝ} (ht : t∈Icc (1/6:ℝ) (7/10)) :
    aeval t (JBase .smallHigh)≤TwoPositive.ASupport.charge t := by
  have hh := NegativeDEPositiveTD.AEnvelope.high_polynomial_charge ht
  have hx : t-1/6∈Icc (0:ℝ) (8/15) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hmul := mul_le_mul_of_nonneg_left hx2 (pow_nonneg hx.1 4)
  have hcompare : (151/500:ℝ)*(t-1/6)^6≤(43/500)*(t-1/6)^4 := by
    nlinarith [pow_nonneg hx.1 4]
  have hJ : aeval t J0=aeval t NegativeDEPositiveTD.Certificate.J0 := by
    simp [J0,abar,NegativeDEPositiveTD.Certificate.J0]
  simp only [JBase,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  rw [hJ]
  simp only [NegativeDEPositiveTD.Certificate.J1,map_sub,map_mul,map_pow,
    aeval_C,aeval_X] at hh
  norm_num only [PositiveTD.Certificate.L] at hh
  linarith only [hh,hcompare]

lemma charge_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    aeval x (J r)≤TwoPositive.ASupport.charge (thetaAt r x) := by
  have ht := original_domain r hx
  simp only [J,aeval_comp,theta_eval]
  cases r
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (show thetaAt .lowEqual x∈Icc (0:ℝ) (1/4) from
          ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (show thetaAt .lowNegative x∈Icc (0:ℝ) (1/4) from
          ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  · exact small_high_charge ht
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (show thetaAt (.farPositive _) x∈Icc (0:ℝ) (1/4) from
          ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter ht
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter ht
  · have ht' : thetaAt (.farHigh _ _) x∈Icc (1/6:ℝ) (7/10) :=
      ⟨by linarith [ht.1],ht.2⟩
    simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J1,
      NegativeDEPositiveTD.Certificate.J0,PositiveTD.Certificate.L] using
      NegativeDEPositiveTD.AEnvelope.high_polynomial_charge ht'

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointInputs

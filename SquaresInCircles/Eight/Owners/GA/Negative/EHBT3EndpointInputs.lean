module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData

/-!
# Eight squares: the angle inputs of the thirty-four EH1/BT3 endpoints

The native polynomial coordinate is `x = θ - b`. All angle domains, coefficient signs and the
q-star comparison (`qstar_bound`) are proved before the radical transfer. The small-high A-support
allowance follows from the sixth-order bound, since `(151/500) (8/15)^2 < 43/500`
(`small_high_charge`). No further A-support hypothesis is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointInputs
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

lemma original_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    thetaAt r x∈Icc (left r:ℝ) (right r:ℝ) := by
  dsimp [thetaAt,GlobalGA.NegativeEHBT3.Certificate.width] at *
  push_cast at *
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma frame_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    thetaAt r x∈Icc 0 frameCap := total_domain r (original_domain r hx)

lemma split_domains (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aAt ep (thetaAt r x)∈Icc 0 frameCap ∧
      zAt ep (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases ep <;> simp [aAt,zAt,ht,show (0:ℝ)≤frameCap by norm_num [frameCap]]

lemma gain_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    gainArgument r (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases r with
  | farHigh i b => cases b <;> norm_num [gainArgument,equal,u,v,frameCap]
  | _ => simp [gainArgument,equal,v,ht] <;> norm_num [frameCap]

lemma argument_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    argument r x∈Icc 0 frameCap := by
  have ht := original_domain r hx
  cases r <;>
    norm_num [argument,positive,equal,gainArgument,left,right,u,v,frameCap] at ht ⊢
  all_goals first
    | exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
    | split <;> norm_num [u,v] <;>
        exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩

/-- Five elementary coefficient margins, each on its whole native interval. -/
def coefficientMargin (r : Row) : Fin 5→ℚ[X] :=
  ![k r-C (1/2),l r-C (1/2),m r-C (1/2),1-k r,l r-k r]

/-! ### The margins on the family intervals

The margins are the family margins composed with `theta r = X + left r`. Each family margin has
degree at most three and positive Bernstein coefficients of degree three on the interval of its
family, so it is a positive combination of the products `(θ - a)^i (b - θ)^(3-i)`, which
`linarith` finds. -/

private def r75_bm (f : Family) : Fin 5→ℚ[X] :=
  ![kBase f-C (1/2),lBase f-C (1/2),mBase f-C (1/2),1-kBase f,lBase f-kBase f]

private theorem r75_margin_comp (r : Row) (i : Fin 5) :
    coefficientMargin r i=(r75_bm (family r) i).comp (theta r) := by
  fin_cases i <;> simp [coefficientMargin,r75_bm,Certificate.k,Certificate.l,Certificate.m,
    sub_comp,one_comp]

/-- The interval of a family: the union of the intervals of its rows. -/
private def r75_lo : Family→ℚ | .smallLow => 0 | .smallHigh => 1/6 | .farLow => 0 | .farHigh => 1/4
private def r75_hi : Family→ℚ
  | .smallLow => 1/6 | .smallHigh => 7/10 | .farLow => 1/4 | .farHigh => 7/10

private theorem r75_family_domain (r : Row) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    thetaAt r x∈Icc (r75_lo (family r):ℝ) (r75_hi (family r)) := by
  have h := original_domain r hx
  cases r <;> norm_num [left,right,family,r75_lo,r75_hi] at h ⊢ <;>
    exact ⟨by linarith [h.1],by linarith [h.2]⟩

/-- Bernstein hints of degree three on `[a, b]`. -/
local macro "r75_cubic" a:term:max b:term:max : tactic => `(tactic| (
  intro i θ hθ
  have h0 : 0≤θ-$a := sub_nonneg.2 hθ.1
  have h1 : 0≤$b-θ := sub_nonneg.2 hθ.2
  have b0 := pow_nonneg h0 3
  have b1 := mul_nonneg (pow_nonneg h0 2) h1
  have b2 := mul_nonneg h0 (pow_nonneg h1 2)
  have b3 := pow_nonneg h1 3
  fin_cases i <;>
    simp only [r75_bm,kBase,lBase,mBase,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,map_add,map_sub,map_mul,map_pow,
      map_one,aeval_C,aeval_X,eq_ratCast] <;>
    push_cast <;> linarith))

private theorem r75_smallLow :
    ∀ (i : Fin 5) {θ : ℝ},θ∈Icc (0:ℝ) (1/6) → 0<aeval θ (r75_bm .smallLow i) := by r75_cubic 0 (1/6)
private theorem r75_smallHigh :
    ∀ (i : Fin 5) {θ : ℝ},θ∈Icc (1/6:ℝ) (7/10) → 0<aeval θ (r75_bm .smallHigh i) := by r75_cubic (1/6) (7/10)
private theorem r75_farLow :
    ∀ (i : Fin 5) {θ : ℝ},θ∈Icc (0:ℝ) (1/4) → 0<aeval θ (r75_bm .farLow i) := by r75_cubic 0 (1/4)
private theorem r75_farHigh :
    ∀ (i : Fin 5) {θ : ℝ},θ∈Icc (1/4:ℝ) (7/10) → 0<aeval θ (r75_bm .farHigh i) := by r75_cubic (1/4) (7/10)

lemma coefficient_margin_positive (r : Row) (i : Fin 5) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<aeval x (coefficientMargin r i) := by
  have hθ := r75_family_domain r hx
  rw [r75_margin_comp,aeval_comp,theta_eval]
  generalize thetaAt r x=θ at hθ
  generalize family r=f at hθ ⊢
  cases f <;> norm_num [r75_lo,r75_hi] at hθ
  · exact r75_smallLow i hθ
  · exact r75_smallHigh i hθ
  · exact r75_farLow i hθ
  · exact r75_farHigh i hθ

lemma coefficient_bounds (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    0<Kactual r x ∧ 0<Lactual r x ∧ 0<Mactual r x ∧
      Kactual r x≤1 ∧ Kactual r x≤Lactual r x := by
  have hk : 0<aeval x (k r-C (1/2)) := coefficient_margin_positive r 0 hx
  have hl : 0<aeval x (l r-C (1/2)) := coefficient_margin_positive r 1 hx
  have hm : 0<aeval x (m r-C (1/2)) := coefficient_margin_positive r 2 hx
  have hk1 : 0<aeval x (1-k r) := coefficient_margin_positive r 3 hx
  have hkl : 0<aeval x (l r-k r) := coefficient_margin_positive r 4 hx
  simp only [map_sub,map_one,aeval_C,k_eval,l_eval,m_eval,eq_ratCast] at hk hl hm hk1 hkl
  push_cast at hk hl hm
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma c_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<Cactual r ep x := by
  have hm := (coefficient_bounds r hx).2.2.1
  have hz := (split_domains r ep hx).2
  have hf := PositiveTD.Explicit.factor_lower hz
  change 0<Mactual r x*(Real.cos (zAt ep (thetaAt r x))+
    PositiveTD.eta*Real.sin (zAt ep (thetaAt r x)))
  exact mul_pos hm (lt_trans (by norm_num) hf)

lemma c_upper (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : Cactual r ep x≤aeval x (cUpper r ep) := by
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

lemma qstar_bound (r : Row) (hr : needs_qstar r=true) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    max (Lactual r x) (Mactual r x)≤aeval x (qStar r) := by
  have hcomp : qStar r-m r=(lBase (family r)+C (3/20)*(C Certificate.h-X)-mBase (family r)).comp
      (theta r) := by
    simp [qStar,Certificate.l,Certificate.m,sub_comp,add_comp,mul_comp,C_comp,X_comp]
  have hθ := original_domain r hx
  have hm : 0<aeval x (qStar r-m r) := by
    rw [hcomp,aeval_comp,theta_eval]
    generalize thetaAt r x=θ at hθ
    cases r <;> simp [needs_qstar] at hr <;>
      norm_num [left,right,family] at hθ <;>
      (have h0 := sub_nonneg.2 hθ.1; have h1 := sub_nonneg.2 hθ.2
       simp only [family,lBase,mBase,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
         eq_ratCast,Certificate.h]
       push_cast
       linarith [pow_nonneg h0 3,mul_nonneg (pow_nonneg h0 2) h1,mul_nonneg h0 (pow_nonneg h1 2),
         pow_nonneg h1 3])
  simp only [map_sub,m_eval] at hm
  have ht := frame_domain r hx
  refine max_le ?_ (by linarith)
  simp only [qStar,map_add,map_mul,map_sub,aeval_C,l_eval,theta_eval,eq_ratCast]
  norm_num [Certificate.h,frameCap] at ht ⊢
  linarith [ht.2]

/-- The quartic small-high allowance is weaker than the sixth-order support bound on the whole
native interval. -/
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
  simp only [JBase,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  rw [hJ]
  simp only [NegativeDEPositiveTD.Certificate.J1,map_sub,map_mul,map_pow,
    aeval_C,aeval_X,eq_ratCast] at hh
  push_cast [PositiveTD.Certificate.L] at hh ⊢
  linarith only [hh,hcompare]

lemma charge_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aeval x (J r)≤TwoPositive.ASupport.charge (thetaAt r x) := by
  have ht := original_domain r hx
  simp only [J,aeval_comp,theta_eval]
  have hq (h0 : ((left r:ℚ):ℝ)=0 ∨ ((left r:ℚ):ℝ)=1/10) (h1 : ((right r:ℚ):ℝ)≤1/4) :
      thetaAt r x∈Icc (0:ℝ) (1/4) := by
    constructor
    · rcases h0 with h0|h0 <;> linarith [ht.1]
    · linarith [ht.2]
  cases r
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inl (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · exact small_high_charge (by simpa [left,right] using ht)
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inl (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · rename_i j b
    have ht' : thetaAt (.farHigh j b) x∈Icc (1/6:ℝ) (7/10) := by
      norm_num [left,right] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
    simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J1,
      NegativeDEPositiveTD.Certificate.J0,PositiveTD.Certificate.L] using
      NegativeDEPositiveTD.AEnvelope.high_polynomial_charge ht'

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointInputs

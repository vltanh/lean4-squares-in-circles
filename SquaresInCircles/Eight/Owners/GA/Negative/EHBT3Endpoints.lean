module

public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData

/-!
# Eight squares: all thirty-four actual EH1/BT3 endpoint inequalities

The existing finite
polynomial certificates are applied on their original closed intervals;
all mass, norm, support, sign and angle inputs are derived internally.
The conclusion is the actual trigonometric/circle scalar, not a
polynomial surrogate. Continuous concentration and the original-source
stress must still supply the full-domain argument using these endpoints.
-/

section
/-!
## The angle inputs of the thirty-four EH1/BT3 endpoints

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
end
end
end

section
/-!
## Actual nonradical and circle inputs for the EH1/BT3 endpoints

Half-circle shifts are collected before Taylor
bounds. The sorted small-low D support is used only in that family;
all other endpoint expressions retain the fourth full-circle norm.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointSupport
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate EndpointInputs
open PositiveTD.Certificate (taylor_bounds)

abbrev small (r : Row) : Prop := family r=.smallLow

def actualBase (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  let t := thetaAt r x
  let k := Kactual r x
  let l := Lactual r x
  let m := Mactual r x
  if small r then
    match ep with
    | .atA => 2*k+3*l+5/2-GlobalGA.Secondary.diagonal+(5/2-GlobalGA.Secondary.diagonal)*m+l*TwoPositive.ASupport.charge t
    | .atT => 2*k+3*l+5/2-GlobalGA.Secondary.diagonal+m*(1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos t+
        (1/2+PositiveTD.eta*(1-GlobalGA.Secondary.diagonal)-PositiveTD.sigma)*Real.sin t)
  else
    match ep with
    | .atA => 2*k+3*l+3+3*m+l*TwoPositive.ASupport.charge t
    | .atT => 2*k+3*l+3+m*(1+2*Real.cos t+
        (1/2+(3/2)*PositiveTD.eta-PositiveTD.sigma)*Real.sin t)

def pairA (r : Row) (x : ℝ) : Fin 4→ℝ :=
  ![Kactual r x,Kactual r x,Lactual r x,1]
def pairB (r : Row) (ep : Split) (x : ℝ) : Fin 4→ℝ :=
  ![1,Lactual r x,Mactual r x,Cactual r ep x]

def zeroNorm (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) : ℝ :=
  if active r i then pairNorm (pairA r x i) (pairB r ep x i) 0 else 0

lemma pair_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    0<pairA r x i ∧ 0<pairB r ep x i := by
  have hp := coefficient_bounds r hx
  have hc := c_positive r ep hx
  fin_cases i <;> simp [pairA,pairB,hp.1,hp.2.1,hp.2.2.1,hc]

lemma sigma_upper : PositiveTD.sigma≤(Certificate.sigmabar:ℝ) := by
  have h := NonnegativeTotals.Charges.sigma_upper
  norm_num [Certificate.sigmabar,NonnegativeTotals.Certificate.sigmabar] at h ⊢
  exact h

lemma diagonal_upper : GlobalGA.Secondary.diagonal≤(Certificate.cbar:ℝ) := by
  have h := PositiveTD.Certificate.diagonal_le_cbar
  norm_num [Certificate.cbar,PositiveTD.Certificate.cbar] at h ⊢
  exact h

lemma base_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : aeval x (base r ep)≤actualBase r ep x := by
  have hp := coefficient_bounds r hx
  have ht := taylor_bounds (frame_domain r hx)
  have hs := (transport_trig (frame_domain r hx)).2.2.1
  have hc := (NegativeESecant.cos_pos (frame_domain r hx)).le
  have hJ := mul_le_mul_of_nonneg_left (charge_lower r hx) hp.2.1.le
  have hσ := mul_le_mul_of_nonneg_right sigma_upper hs
  have hdC := mul_le_mul_of_nonneg_right diagonal_upper hc
  have hdS := mul_le_mul_of_nonneg_right diagonal_upper hs
  have hcb : ((Certificate.cbar:ℚ):ℝ)=449607033/500000000 := by norm_num [Certificate.cbar]
  have hsb : ((Certificate.sigmabar:ℚ):ℝ)=1415477291/1000000000 := by
    norm_num [Certificate.sigmabar]
  have het : ((Certificate.eta:ℚ):ℝ)=293/1000 := by norm_num [Certificate.eta]
  have hpe : PositiveTD.eta=293/1000 := rfl
  have hdu : GlobalGA.Secondary.diagonal≤449607033/500000000 := hcb ▸ diagonal_upper
  rw [hcb] at hdC hdS
  rw [hsb] at hσ
  by_cases hsmall : family r=.smallLow
  · cases ep
    · have hdm := mul_le_mul_of_nonneg_right
        (sub_le_sub_left diagonal_upper (5/2)) hp.2.2.1.le
      rw [hcb] at hdm
      simp only [base,ite_eq_left hsmall,map_add,map_mul,map_sub,aeval_C,eq_ratCast,k_eval,l_eval,m_eval]
      simp only [actualBase,small,ite_eq_left hsmall]
      push_cast
      linarith only [hJ,hdu,hdm]
    · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
        (show (0:ℝ)≤3/2-449607033/500000000 by norm_num)
      have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
        (show (1/2:ℝ)+293/1000*(1-449607033/500000000)-1415477291/1000000000≤0 by norm_num)
      have hinner :
          1+(3/2-449607033/500000000)*aeval (thetaAt r x) PositiveTD.Certificate.C10+
            (1/2+293/1000*(1-449607033/500000000)-1415477291/1000000000)*
              aeval (thetaAt r x) PositiveTD.Certificate.S9≤
          1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos (thetaAt r x)+
            (1/2+PositiveTD.eta*(1-GlobalGA.Secondary.diagonal)-PositiveTD.sigma)*
              Real.sin (thetaAt r x) := by
        rw [hpe]
        linarith only [hcos,hsin,hdC,hdS,hσ]
      have hh := mul_le_mul_of_nonneg_left hinner hp.2.2.1.le
      simp only [base,ite_eq_left hsmall,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast,
        k_eval,l_eval,m_eval,aeval_comp,theta_eval]
      simp only [actualBase,small,ite_eq_left hsmall]
      push_cast
      linarith only [hh,hdu]
  · cases ep
    · simp only [base,ite_eq_right hsmall,map_add,map_mul,aeval_C,eq_ratCast,k_eval,l_eval,m_eval]
      simp only [actualBase,small,ite_eq_right hsmall]
      push_cast
      linarith only [hJ]
    · have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
        (show (1/2:ℝ)+(3/2)*(293/1000)-1415477291/1000000000≤0 by norm_num)
      have hinner :
          1+2*aeval (thetaAt r x) PositiveTD.Certificate.C10+
            (1/2+(3/2)*(293/1000)-1415477291/1000000000)*
              aeval (thetaAt r x) PositiveTD.Certificate.S9≤
          1+2*Real.cos (thetaAt r x)+
            (1/2+(3/2)*PositiveTD.eta-PositiveTD.sigma)*Real.sin (thetaAt r x) := by
        rw [hpe]
        linarith only [hsin,hσ,ht.2.2.2.2.1]
      have hh := mul_le_mul_of_nonneg_left hinner hp.2.2.1.le
      simp only [base,ite_eq_right hsmall,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast,
        k_eval,l_eval,m_eval,aeval_comp,theta_eval]
      simp only [actualBase,small,ite_eq_right hsmall]
      push_cast
      linarith only [hh]

lemma gain_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aeval x (gainLower r)≤charge (family r) (gainArgument r (thetaAt r x)) := by
  have ht := taylor_bounds (gain_domain r hx)
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (show (0:ℝ)≤82/125 by norm_num)
  have hg : aeval x (g r)≤gain (gainArgument r (thetaAt r x)) := by
    simp only [g,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast,aeval_comp,s_eval]
    dsimp [gain]
    push_cast
    linarith only [hsin,hcos]
  simp only [gainLower,charge]
  split
  · have hh := mul_le_mul_of_nonneg_left hg (show (0:ℝ)≤201/200 by norm_num)
    simp only [map_sub,map_mul,aeval_C,eq_ratCast]
    push_cast
    linarith only [hh]
  · exact hg

lemma baseline_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    baseline (family r) (thetaAt r x) (aAt ep (thetaAt r x)) (zAt ep (thetaAt r x))=
      actualBase r ep x-R*∑i,zeroNorm r ep x i := by
  have ht := frame_domain r hx
  have hw := edgeWidth_positive_formula ht
  rw [Fin.sum_univ_four]
  have h0 : zeroNorm r ep x 0=pairNorm (Kactual r x) 1 0 := by
    simp [zeroNorm,active,pairA,pairB]
  have h1 : zeroNorm r ep x 1=pairNorm (Kactual r x) (Lactual r x) 0 := by
    simp [zeroNorm,active,pairA,pairB]
  have h2 : zeroNorm r ep x 2=pairNorm (Lactual r x) (Mactual r x) 0 := by
    simp [zeroNorm,active,pairA,pairB]
  rw [h0,h1,h2]
  by_cases hsmall : family r=.smallLow
  · have hl : Lactual r x=1 := by simp only [Lactual,hsmall,Explicit.l]
    have hl' : Explicit.l (family r) (thetaAt r x)=1 := hl
    have h3 : zeroNorm r ep x 3=0 := by
      simp [zeroNorm,active,hsmall]
    rw [h3,hl]
    cases ep
    · simp only [baseline,actualBase,aAt,zAt]
      rw [ite_eq_left hsmall,ite_eq_left hsmall,hl']
      simp only [PositiveBT3.Analytic.lowBaseline,PositiveBT3.tilted,fullSupport_pair,hl,
        edgeWidth_zero,Real.cos_zero,Real.sin_zero,pairNorm_symm 1 (Kactual r x) 0,
        pairNorm_symm (Mactual r x) 1 0]
      ring
    · simp only [baseline,actualBase,aAt,zAt]
      rw [ite_eq_left hsmall,ite_eq_left hsmall,hl']
      simp only [PositiveBT3.Analytic.lowBaseline,PositiveBT3.tilted,fullSupport_pair,hl,
        hw,TwoPositive.ASupport.charge_zero,pairNorm_symm 1 (Kactual r x) 0,
        pairNorm_symm (Mactual r x) 1 0]
      ring
  · have h3 : zeroNorm r ep x 3=pairNorm 1 (Cactual r ep x) 0 := by
      simp [zeroNorm,active,hsmall,pairA,pairB]
    rw [h3]
    cases ep
    · simp only [baseline,actualBase,aAt,zAt]
      rw [ite_eq_right hsmall,ite_eq_right hsmall]
      simp only [Cactual,Explicit.c,zAt,PositiveBT3.Analytic.fullBaseline,PositiveBT3.tilted,
        fullSupport_pair,edgeWidth_zero,Real.cos_zero,Real.sin_zero]
      rw [pairNorm_symm (Mactual r x*(1+PositiveTD.eta*0)) 1 0]
      ring
    · simp only [baseline,actualBase,aAt,zAt]
      rw [ite_eq_right hsmall,ite_eq_right hsmall]
      simp only [Cactual,Explicit.c,zAt,PositiveBT3.Analytic.fullBaseline,PositiveBT3.tilted,
        fullSupport_pair,hw,TwoPositive.ASupport.charge_zero]
      rw [pairNorm_symm (Mactual r x*(Real.cos (thetaAt r x)+
        PositiveTD.eta*Real.sin (thetaAt r x))) 1 0]
      ring

lemma negative_coefficient_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (he : equal r=false)
    (hn : positive r=false) :
    max (pairA r x (index r)) (pairB r ep x (index r))≤
      aeval x (larger r (index r)) := by
  have hp := coefficient_bounds r hx
  cases r with
  | lowEqual => simp [equal] at he
  | lowNegative => simp [index,pairA,pairB,larger,max_eq_right hp.2.2.2.1]
  | smallHigh i =>
      fin_cases i
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.1
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.2
      · simpa [index,pairA,pairB,larger] using
          qstar_bound (.smallHigh 2) rfl hx
  | farPositive i => simp [positive] at hn
  | farNegative i =>
      fin_cases i
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.1
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.2
  | farEqual => simp [equal] at he
  | farHigh i upper =>
      fin_cases i
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.1
      · simp [index,pairA,pairB,larger]; exact hp.2.2.2.2
      · simpa [index,pairA,pairB,larger] using
          qstar_bound (.farHigh 2 upper) rfl hx

lemma positive_coefficient_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (hr : positive r=true) :
    min (pairA r x (index r)) (pairB r ep x (index r))=
      aeval x (smaller r (index r)) := by
  have hp := coefficient_bounds r hx
  cases r <;> simp only [positive,Bool.false_eq_true] at hr
  rename_i i
  have ht := original_domain (.farPositive i) hx
  have hm1 : 1≤Mactual (.farPositive i) x := by
    dsimp [Mactual,Explicit.m,family]
    norm_num only [left,right] at ht
    linarith [ht.2]
  have hlm : Lactual (.farPositive i) x≤Mactual (.farPositive i) x := by
    dsimp [Lactual,Mactual,Explicit.l,Explicit.m,family]
    norm_num only [left,right] at ht
    linarith [ht.2]
  have hz : zAt ep (thetaAt (.farPositive i) x)∈Icc (0:ℝ) (1/6) := by
    cases ep <;> simp only [zAt]
    · norm_num
    · norm_num only [left,right] at ht
      exact ⟨ht.1,by linarith [ht.2]⟩
  have hf := PositiveTD.Explicit.low_factor hz
  have hc : Mactual (.farPositive i) x≤Cactual (.farPositive i) ep x := by
    have hh := mul_le_mul_of_nonneg_left hf.1 hp.2.2.1.le
    simpa [Cactual,Explicit.c,PositiveBT3.tilted] using hh
  fin_cases i
  · simp [index,pairA,pairB,smaller]; exact hp.2.2.2.1
  · simp [index,pairA,pairB,smaller]; exact hlm
  · simp [index,pairA,pairB,smaller]; exact hm1.trans hc

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointSupport
end
end
end

section
/-!
## The thirty-four EH1/BT3 norm comparisons

A negative endpoint modifies one of H, G, B; a positive endpoint modifies H, B or the two-angle D
norm. Only the positive D norm uses the upper bound of the tilted coefficient. The sorted small-low
D term is absent from both sides of the same three-norm identity (`norm_sum_identity`); no full
norm stands in for it.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointNorms
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate EndpointInputs EndpointSupport
open PositiveTD.Certificate (taylor_bounds)

abbrev pAt (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  min (pairA r x (index r)) (pairB r ep x (index r))
abbrev qAt (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  max (pairA r x (index r)) (pairB r ep x (index r))

def signedAngle (r : Row) (x : ℝ) (i : Fin 4) : ℝ :=
  if equal r ∨ i≠index r then 0 else if positive r then argument r x else -argument r x

def normAt (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) : ℝ :=
  if active r i then pairNorm (pairA r x i) (pairB r ep x i) (signedAngle r x i) else 0

def actualExtra (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  if equal r then 0
  else if positive r then pAt r ep x*(PositiveAngularEnvelope.phi (argument r x)-1)-(1/200)*argument r x
  else qAt r ep x*(Real.cos (argument r x)-1)

def actualA (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  actualBase r ep x+charge (family r) (gainArgument r (thetaAt r x))+actualExtra r ep x

def increment (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  if equal r then 0
  else if positive r then U R (pAt r ep x) (qAt r ep x) (argument r x)-(1/200)*argument r x
  else V R (pAt r ep x) (qAt r ep x) (argument r x)

def value (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  baseline (family r) (thetaAt r x) (aAt ep (thetaAt r x)) (zAt ep (thetaAt r x))+
    charge (family r) (gainArgument r (thetaAt r x))+increment r ep x

lemma norm_nonnegative (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) :
    0≤normAt r ep x i := by
  unfold normAt
  split <;> first | exact Real.sqrt_nonneg _ | exact le_rfl

lemma sorted_norm (a b t : ℝ) : pairNorm (min a b) (max a b) t=pairNorm a b t := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,pairNorm_symm]

lemma active_index (r : Row) : active r (index r) := by
  cases r <;> simp [active,family,index]

lemma negative_index (r : Row) (he : equal r=false) (hn : positive r=false) :
    index r≠(3:Fin 4) := by
  cases r with
  | lowEqual => simp [equal] at he
  | lowNegative => decide
  | smallHigh i => fin_cases i <;> decide
  | farPositive i => simp [positive] at hn
  | farNegative i => fin_cases i <;> decide
  | farEqual => simp [equal] at he
  | farHigh i upper => fin_cases i <;> simp [index]

lemma zero_square_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    (pairA r x i)^2+(pairB r ep x i)^2≤aeval x (normZero r ep i) := by
  have hc := c_upper r ep hx
  have hc0 := (c_positive r ep hx).le
  have hsq := pow_le_pow_left₀ hc0 hc 2
  fin_cases i <;> simp [pairA,pairB,normZero]
  · linarith
  · linarith

lemma product_nonnegative (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) : 0≤aeval x (product r ep i) := by
  have hp := coefficient_bounds r hx
  have hc := (c_positive r ep hx).le.trans (c_upper r ep hx)
  fin_cases i <;> simp [product]
  · exact hp.1.le
  · exact mul_nonneg hp.1.le hp.2.1.le
  · exact mul_nonneg hp.2.1.le hp.2.2.1.le
  · exact hc

lemma product_upper (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    pairA r x i*pairB r ep x i≤aeval x (product r ep i) := by
  fin_cases i <;> simp [pairA,pairB,product]
  exact c_upper r ep hx

lemma product_exact (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) (hi : i≠3) :
    aeval x (product r ep i)=pairA r x i*pairB r ep x i := by
  fin_cases i <;> simp_all [pairA,pairB,product]

lemma norm_square_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    (normAt r ep x i)^2≤aeval x (P r ep i) := by
  by_cases hi : active r i
  · have hp := pair_positive r ep hx i
    have hz := zero_square_bound r ep hx i
    have hd := argument_domain r hx
    have ht := taylor_bounds hd
    by_cases he : equal r ∨ i≠index r
    · have hn := NonnegativeTotals.Analytic.norm_zero_square (pairA r x i) (pairB r ep x i)
      simpa only [normAt,ite_eq_left hi,signedAngle,ite_eq_left he,P,map_add,map_zero,add_zero,hn] using hz
    · have heq : equal r=false := by cases h : equal r <;> simp_all
      have hii : i=index r := by tauto
      by_cases hr : positive r
      · have hprod := mul_le_mul (product_upper r ep hx i) ht.2.2.1
          (transport_trig hd).2.2.1 (product_nonnegative r ep hx i)
        have hn := PairNormCalculus.pairNorm_sq hp.1 hp.2
          (show |argument r x|≤frameCap by rw [abs_of_nonneg hd.1]; exact hd.2)
        simp only [PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct] at hn
        simp only [normAt,ite_eq_left hi,signedAngle,ite_eq_right he,ite_eq_left hr,P,
          map_add,map_mul,aeval_C,eq_ratCast,aeval_comp,d_eval]
        push_cast
        nlinarith only [hz,hprod,hn]
      · have hfalse : positive r=false := by cases h : positive r <;> simp_all
        have hin : i≠3 := by simpa only [hii] using negative_index r heq hfalse
        have hprod := mul_le_mul_of_nonneg_left ht.2.1 (mul_nonneg hp.1.le hp.2.le)
        have hn := PairNormCalculus.pairNorm_sq hp.1 hp.2
          (show |-argument r x|≤frameCap by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
        simp only [PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct,Real.sin_neg] at hn
        simp only [normAt,ite_eq_left hi,signedAngle,ite_eq_right he,ite_eq_right hr,P,
          map_add,map_neg,map_mul,aeval_C,eq_ratCast,aeval_comp,d_eval,product_exact r ep x i hin]
        push_cast
        nlinarith only [hz,hprod,hn]
  · simp [normAt,P,hi]

lemma extra_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aeval x (if equal r then 0 else if positive r then positiveExtra r else negativeExtra r)≤
      actualExtra r ep x := by
  have hd := argument_domain r hx
  have ht := taylor_bounds hd
  by_cases he : equal r
  · simp [actualExtra,he]
  · by_cases hp : positive r
    · have hcoeff := positive_coefficient_identity r ep hx (by simpa using hp)
      have hpos := pair_positive r ep hx (index r)
      have hm : 0≤pAt r ep x := le_min hpos.1.le hpos.2.le
      have hphi : aeval (argument r x) PositiveTD.Certificate.C10+
          aeval (argument r x) PositiveTD.Certificate.S11-1≤
            PositiveAngularEnvelope.phi (argument r x)-1 := by
        dsimp [PositiveAngularEnvelope.phi]
        linarith [ht.2.2.2.2.1,ht.2.1]
      have hh := mul_le_mul_of_nonneg_left hphi hm
      simp only [ite_eq_right he,ite_eq_left hp,actualExtra,positiveExtra,
        map_sub,map_mul,map_add,map_one,aeval_C,eq_ratCast,aeval_comp,d_eval]
      rw [←hcoeff]
      push_cast
      linarith only [hh]
    · have heq : equal r=false := by cases h : equal r <;> simp_all
      have hpq : positive r=false := by cases h : positive r <;> simp_all
      have hcoeff := negative_coefficient_bound r ep hx heq hpq
      have hpos := pair_positive r ep hx (index r)
      have hq : 0≤aeval x (larger r (index r)) :=
        (hpos.1.le.trans (le_max_left _ _)).trans hcoeff
      have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq
      have h₂ := mul_le_mul_of_nonpos_right hcoeff
        (sub_nonpos.mpr (Real.cos_le_one (argument r x)))
      simp only [ite_eq_right he,ite_eq_right hp,actualExtra,negativeExtra,
        map_mul,map_sub,map_one,aeval_comp,d_eval]
      linarith only [h₁,h₂]

lemma nonradical_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : aeval x (A r ep)≤actualA r ep x := by
  have hb := base_lower r ep hx
  have hg := gain_lower r hx
  have he := extra_lower r ep hx
  simpa only [Certificate.A,map_add,actualA] using add_le_add (add_le_add hb hg) he

lemma norm_sum_identity (r : Row) (ep : Split) (x : ℝ) (he : equal r=false) :
    (∑i,normAt r ep x i)=(∑i,zeroNorm r ep x i)-
      pairNorm (pairA r x (index r)) (pairB r ep x (index r)) 0+
      pairNorm (pairA r x (index r)) (pairB r ep x (index r))
        (if positive r then argument r x else -argument r x) := by
  let b := pairNorm (pairA r x (index r)) (pairB r ep x (index r))
      (if positive r then argument r x else -argument r x)-
    pairNorm (pairA r x (index r)) (pairB r ep x (index r)) 0
  have hi : ∀i,normAt r ep x i=zeroNorm r ep x i+if i=index r then b else 0 := by
    intro i
    by_cases hii : i=index r
    · subst i
      simp only [normAt,zeroNorm,active_index,ite_true,signedAngle,he,
        Bool.false_eq_true,ne_eq,not_true_eq_false,or_self,ite_false]
      dsimp [b]
      ring
    · simp [normAt,zeroNorm,signedAngle,he,hii]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  dsimp [b]
  ring

lemma scalar_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : value r ep x=actualA r ep x-R*∑i,normAt r ep x i := by
  rw [value,baseline_identity r ep hx]
  by_cases he : equal r
  · simp only [actualA,actualExtra,increment,ite_eq_left he]
    have hn : ∀i,normAt r ep x i=zeroNorm r ep x i := by
      intro i
      simp [normAt,zeroNorm,signedAngle,he]
    simp_rw [hn]
    ring
  · have heq : equal r=false := by cases h : equal r <;> simp_all
    rw [norm_sum_identity r ep x heq]
    by_cases hp : positive r
    · simp only [actualA,actualExtra,increment,ite_eq_right he,ite_eq_left hp,U,
        pAt,qAt,sorted_norm]
      ring
    · simp only [actualA,actualExtra,increment,ite_eq_right he,ite_eq_right hp,V,
        pAt,qAt,sorted_norm]
      ring

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.EndpointNorms
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Endpoints
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate EndpointInputs EndpointSupport EndpointNorms

lemma radius_upper : R≤(Certificate.Rbar:ℝ) := by
  have hh : R^2=qCap := radius_sq
  have hr := Real.sqrt_nonneg qCap
  norm_num [qCap,Certificate.Rbar] at hh ⊢
  nlinarith

lemma numerator_identity (r : Row) (ep : Split) (x : ℝ) :
    aeval x (numerator r ep)=
      2*aeval x (A r ep)*(∏i,aeval x (mass r ep i))-(Certificate.Rbar:ℝ)*
        ∑i,if active r i then (aeval x (P r ep i)+(aeval x (mass r ep i))^2)*
          ∏j∈Finset.univ.erase i,aeval x (mass r ep j) else 0 := by
  simp only [numerator,map_sub,map_mul,map_prod,map_sum,aeval_C,eq_ratCast]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp [map_prod]

/-- Every row and both split endpoints, with no analytic positivity premise. -/
theorem value_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<value r ep x := by
  have hnum := numerator_positive r ep hx
  rw [numerator_identity] at hnum
  have hh := FiniteActiveRadicalTransfer.positive (active r)
    (fun i => aeval x (mass r ep i)) (normAt r ep x)
    (fun i => aeval x (P r ep i))
    (fun i => mass_positive r ep i hx)
    (norm_nonnegative r ep x)
    (fun i => norm_square_bound r ep hx i)
    (fun i hi => by simp [normAt,hi]) radius_upper
    (by norm_num [Certificate.Rbar] : (0:ℝ)≤(Certificate.Rbar:ℝ))
    (nonradical_lower r ep hx) hnum
  rw [scalar_identity r ep hx]
  exact hh

lemma native_coordinate (r : Row) {t : ℝ}
    (ht : t∈Icc (left r:ℝ) (right r:ℝ)) :
    t-(left r:ℝ)∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ) := by
  dsimp [GlobalGA.NegativeEHBT3.Certificate.width]
  push_cast
  exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

/-- Public endpoint form in the original total angle rather than x=theta-b. -/
theorem original_endpoint_positive (r : Row) (ep : Split) {t : ℝ}
    (ht : t∈Icc (left r:ℝ) (right r:ℝ)) :
    0<value r ep (t-(left r:ℝ)) := value_positive r ep (native_coordinate r ht)

/-- The two small-low equal-angle endpoints. -/
theorem small_low_equal (ep : Split) {t : ℝ} (ht : t∈Icc (0:ℝ) (1/10)) :
    0<baseline .smallLow t (aAt ep t) (zAt ep t)+gain t := by
  have ht' : t∈Icc (left .lowEqual:ℝ) (right .lowEqual:ℝ) := by
    norm_num [left,right]; exact ht
  simpa [value,increment,charge,far,Certificate.family,Certificate.equal,
    Certificate.gainArgument,thetaAt,Certificate.left] using
    original_endpoint_positive .lowEqual ep ht'

/-- The two small-low shifted-negative endpoints retain their actual H norm. -/
theorem small_low_negative (ep : Split) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (1/6)) :
    0<baseline .smallLow t (aAt ep t) (zAt ep t)+gain (1/10)+
      V R (Explicit.k .smallLow t) 1 (t-1/10) := by
  have ht' : t∈Icc (left .lowNegative:ℝ) (right .lowNegative:ℝ) := by
    norm_num [left,right]; exact ht
  have hx := native_coordinate .lowNegative ht'
  have hk := (coefficient_bounds .lowNegative hx).2.2.2.1
  have hkn : Explicit.k .smallLow t≤1 := by
    simpa [Kactual,thetaAt,Certificate.family] using hk
  simpa [value,increment,charge,far,Certificate.family,Certificate.equal,
    Certificate.positive,Certificate.gainArgument,thetaAt,Certificate.left,
    argument,pAt,qAt,pairA,pairB,Certificate.index,Kactual,Lactual,Mactual,
    min_eq_left hkn,max_eq_right hkn,v] using original_endpoint_positive .lowNegative ep ht'

/-- The two far-low equal-angle endpoints include the original EH charge. -/
theorem far_low_equal (ep : Split) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (1/4)) :
    0<baseline .farLow t (aAt ep t) (zAt ep t)+charge .farLow t := by
  have ht' : t∈Icc (left .farEqual:ℝ) (right .farEqual:ℝ) := by
    norm_num [left,right]; exact ht
  simpa [value,increment,Certificate.family,Certificate.equal,
    Certificate.gainArgument,thetaAt,Certificate.left] using
    original_endpoint_positive .farEqual ep ht'

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Endpoints
end
end
end

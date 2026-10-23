module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3EndpointInputs

/-!
# Actual nonradical and circle inputs for the EH1/BT3 endpoints

Uncompiled Section 8. Half-circle shifts are collected before Taylor
bounds. The sorted small-low D support is used only in that family;
all other endpoint expressions retain the fourth full-circle norm.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointSupport
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
    | .atA => 2*k+3*l+5/2-diagonal+(5/2-diagonal)*m+l*TwoPositive.ASupport.charge t
    | .atT => 2*k+3*l+5/2-diagonal+m*(1+(3/2-diagonal)*Real.cos t+
        (1/2+PositiveTD.eta*(1-diagonal)-PositiveTD.sigma)*Real.sin t)
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
    (hx : x∈Icc 0 (width r:ℝ)) (i : Fin 4) :
    0<pairA r x i ∧ 0<pairB r ep x i := by
  have hp := coefficient_bounds r hx
  have hc := c_positive r ep hx
  fin_cases i <;> simp [pairA,pairB,hp.1,hp.2.1,hp.2.2.1,hc]

lemma sigma_upper : PositiveTD.sigma≤(Certificate.sigmabar:ℝ) := by
  simpa [Certificate.sigmabar,PositiveTD.Certificate.sigmabar] using
    NonnegativeTotals.Charges.sigma_upper

lemma diagonal_upper : diagonal≤(Certificate.cbar:ℝ) := by
  simpa [Certificate.cbar,PositiveTD.Certificate.cbar] using
    PositiveTD.Certificate.diagonal_le_cbar

lemma base_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : aeval x (base r ep)≤actualBase r ep x := by
  have hp := coefficient_bounds r hx
  have ht := taylor_bounds (frame_domain r hx)
  have hs := (transport_trig (frame_domain r hx)).2.2.1
  have hc := (NegativeESecant.cos_pos (frame_domain r hx)).le
  have hJ := mul_le_mul_of_nonneg_left (charge_lower r hx) hp.2.1.le
  have hσ := mul_le_mul_of_nonneg_right sigma_upper hs
  have hdC := mul_le_mul_of_nonneg_right diagonal_upper hc
  have hdS := mul_le_mul_of_nonneg_right diagonal_upper hs
  by_cases hsmall : family r=.smallLow
  · cases ep
    · have hdm := mul_le_mul_of_nonneg_right
        (sub_le_sub_left diagonal_upper (5/2)) hp.2.2.1.le
      simp only [base,if_pos hsmall,map_add,map_mul,map_sub,aeval_C,k_eval,l_eval,m_eval]
      push_cast
      simp only [actualBase,small,if_pos hsmall]
      nlinarith only [hJ,diagonal_upper,hdm]
    · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
        (show (0:ℝ)≤3/2-(Certificate.cbar:ℝ) by norm_num [Certificate.cbar])
      have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
        (show (1/2:ℝ)+(Certificate.eta:ℝ)*(1-(Certificate.cbar:ℝ))-
          (Certificate.sigmabar:ℝ)≤0 by norm_num [Certificate.eta,Certificate.cbar,Certificate.sigmabar])
      have hinner :
          1+(3/2-(Certificate.cbar:ℝ))*aeval (thetaAt r x) PositiveTD.Certificate.C10+
            (1/2+(Certificate.eta:ℝ)*(1-(Certificate.cbar:ℝ))-(Certificate.sigmabar:ℝ))*
              aeval (thetaAt r x) PositiveTD.Certificate.S9≤
          1+(3/2-diagonal)*Real.cos (thetaAt r x)+
            (1/2+PositiveTD.eta*(1-diagonal)-PositiveTD.sigma)*Real.sin (thetaAt r x) := by
        dsimp [Certificate.eta,PositiveTD.eta] at *
        nlinarith only [hcos,hsin,hdC,hdS,hσ]
      have hh := mul_le_mul_of_nonneg_left hinner hp.2.2.1.le
      simp only [base,if_pos hsmall,map_add,map_mul,map_sub,map_one,aeval_C,
        k_eval,l_eval,m_eval,aeval_comp,theta_eval]
      push_cast
      simp only [actualBase,small,if_pos hsmall]
      nlinarith only [hh,diagonal_upper]
  · cases ep
    · simp only [base,if_neg hsmall,map_add,map_mul,aeval_C,k_eval,l_eval,m_eval]
      simp only [actualBase,small,if_neg hsmall]
      linarith only [hJ]
    · have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
        (show (1/2:ℝ)+(3/2)*(Certificate.eta:ℝ)-(Certificate.sigmabar:ℝ)≤0 by
          norm_num [Certificate.eta,Certificate.sigmabar])
      have hinner :
          1+2*aeval (thetaAt r x) PositiveTD.Certificate.C10+
            (1/2+(3/2)*(Certificate.eta:ℝ)-(Certificate.sigmabar:ℝ))*
              aeval (thetaAt r x) PositiveTD.Certificate.S9≤
          1+2*Real.cos (thetaAt r x)+
            (1/2+(3/2)*PositiveTD.eta-PositiveTD.sigma)*Real.sin (thetaAt r x) := by
        dsimp [Certificate.eta,PositiveTD.eta] at *
        nlinarith only [hsin,hσ,ht.2.2.2.2.1]
      have hh := mul_le_mul_of_nonneg_left hinner hp.2.2.1.le
      simp only [base,if_neg hsmall,map_add,map_mul,map_sub,map_one,aeval_C,
        k_eval,l_eval,m_eval,aeval_comp,theta_eval]
      push_cast
      simp only [actualBase,small,if_neg hsmall]
      linarith only [hh]

lemma gain_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (width r:ℝ)) :
    aeval x (gainLower r)≤charge (family r) (gainArgument r (thetaAt r x)) := by
  have ht := taylor_bounds (gain_domain r hx)
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (show (0:ℝ)≤82/125 by norm_num)
  have hg : aeval x (g r)≤gain (gainArgument r (thetaAt r x)) := by
    simp only [g,map_add,map_mul,map_sub,map_one,aeval_C,aeval_comp,s_eval]
    dsimp [gain]
    linarith only [hsin,hcos]
  simp only [gainLower,charge]
  split
  · have hh := mul_le_mul_of_nonneg_left hg (show (0:ℝ)≤201/200 by norm_num)
    simp only [map_sub,map_mul,aeval_C]
    linarith only [hh]
  · exact hg

lemma baseline_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) :
    baseline (family r) (thetaAt r x) (aAt ep (thetaAt r x)) (zAt ep (thetaAt r x))=
      actualBase r ep x-R*∑i,zeroNorm r ep x i := by
  have ht := frame_domain r hx
  have hw := edgeWidth_positive_formula ht
  cases r <;> cases ep <;>
    simp only [baseline,actualBase,small,family,aAt,zAt,zeroNorm,active,pairA,pairB,
      Cactual,Explicit.c,Explicit.l,PositiveBT3.Analytic.lowBaseline,
      PositiveBT3.Analytic.fullBaseline,PositiveBT3.tilted,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,
      TwoPositive.ASupport.charge_zero,edgeWidth_zero,hw,
      Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      reduceCtorEq,if_true,if_false,true_or,false_or,or_self,not_true_eq_false,
      fullSupport_pair]
  all_goals
    simp only [pairNorm_symm (1:ℝ),pairNorm_symm (Lactual _ _),
      pairNorm_symm (Mactual _ _)]
    dsimp [Kactual,Lactual,Mactual]
    ring

lemma negative_coefficient_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) (he : equal r=false) (hn : positive r=false) :
    max (pairA r x (index r)) (pairB r ep x (index r))≤
      aeval x (larger r (index r)) := by
  have hp := coefficient_bounds r hx
  cases r with
  | lowEqual => simp [equal] at he
  | lowNegative => simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.1]
  | smallHigh i =>
      fin_cases i
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.1]
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.2]
      · simpa [index,pairA,pairB,larger] using
          qstar_bound (.smallHigh 2) (by decide) hx
  | farPositive i => simp [positive] at hn
  | farNegative i =>
      fin_cases i
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.1]
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.2]
  | farEqual => simp [equal] at he
  | farHigh i upper =>
      fin_cases i
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.1]
      · simpa [index,pairA,pairB,larger,max_eq_right hp.2.2.2.2]
      · simpa [index,pairA,pairB,larger] using
          qstar_bound (.farHigh 2 upper) (by decide) hx

lemma positive_coefficient_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) (hr : positive r=true) :
    min (pairA r x (index r)) (pairB r ep x (index r))=
      aeval x (smaller r (index r)) := by
  have hp := coefficient_bounds r hx
  cases r <;> simp only [positive,reduceCtorEq,Bool.false_eq_true] at hr
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
  · simp [index,pairA,pairB,smaller,min_eq_left hp.2.2.2.1]
  · simp [index,pairA,pairB,smaller,min_eq_left hlm]
  · simp [index,pairA,pairB,smaller,min_eq_left (hm1.trans hc)]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointSupport

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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointSupport

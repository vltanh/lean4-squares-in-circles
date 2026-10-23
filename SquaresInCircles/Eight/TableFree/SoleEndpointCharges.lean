module

public import SquaresInCircles.Eight.TableFree.SoleScalarEndpointAlgebra

/-!
# The endpoint scalar charges dominate the original ordinary minima

Uncompiled source. H, A, B, D retain their actual single-angle or
two-angle status. The only deliberately stronger scalar coefficient is
the high sole-DE H coefficient 1.06; its direction follows from the
nonpositive factor cos(t)-1. All min/max comparisons are proved here
from the coefficient families on their complete domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleEndpointCharges
open SoleECoefficients SoleOrdinaryData SoleBalancedCoefficients SoleScalarData
open SoleScalarEndpointAlgebra PositiveAngularEnvelope SingleAngleConcavity
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

def Gcase (b : Band) (de : Bool) (i : Fin 4) : ScalarCase :=
  match b with
  | .low => .lowG
  | .middle => .middleG i
  | .high => if de=true ∧ i=0 then .highDEH else .highG i

def Ecase (b : Band) (de : Bool) (i : Fin 4) : ScalarCase :=
  match b with
  | .low => if de then .lowDE else .lowE
  | .middle => if de then .middleDE i else .middleE i
  | .high => .highE i

theorem Gcase_band (b : Band) (de : Bool) (i : Fin 4) : band (Gcase b de i)=b := by
  cases b <;> simp [Gcase,band] <;> split_ifs <;> rfl
theorem Ecase_band (b : Band) (de : Bool) (i : Fin 4) : band (Ecase b de i)=b := by
  cases b <;> cases de <;> rfl
theorem Gcase_atG (b : Band) (de : Bool) (i : Fin 4) : atG (Gcase b de i)=true := by
  cases b <;> simp [Gcase,atG] <;> split_ifs <;> rfl
theorem Ecase_atG (b : Band) (de : Bool) (i : Fin 4) : atG (Ecase b de i)=false := by
  cases b <;> cases de <;> rfl

theorem Gcase_index {b : Band} (de : Bool) {i : Fin 4} (hi : b=.low → i=2) :
    negativeIndex (Gcase b de i)=i := by
  cases b
  · simpa [Gcase,negativeIndex] using (hi rfl).symm
  · rfl
  · by_cases hh : de=true ∧ i=0
    · simp [Gcase,hh,negativeIndex,hh.2]
    · simp [Gcase,hh,negativeIndex]

theorem Ecase_index {b : Band} (de : Bool) {i : Fin 4} (hi : b=.low → i=2) :
    negativeIndex (Ecase b de i)=i := by
  cases b <;> cases de <;> simp_all [Ecase,negativeIndex]

theorem norm_min_max (a b u : ℝ) : pairNorm (min a b) (max a b) u=pairNorm a b u := by
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,pairNorm_symm]

theorem non_single_nu {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b)
    (i : Fin 4) (hi : single de i=false) : nu b de t x e i=large b de t x e i := by
  have hc := (ell_le_k_c ht).2
  fin_cases i <;> cases de <;>
    simp_all [single,nu,large,alpha,beta,max_eq_right hc]

theorem pure_eq {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) (R u : ℝ) (i : Fin 4) :
    pure (single de i) R (small b de t x e i) (large b de t x e i) (nu b de t x e i) u=
      Vnu R (alpha b de t x e i) (beta b t x i) (nu b de t x e i) u := by
  have hnorm (v : ℝ) := norm_min_max (alpha b de t x e i) (beta b t x i) v
  by_cases hi : single de i=true
  · simp only [pure,hi,if_true,Vnu,small,large,hnorm]
  · have hi' : single de i=false := Bool.eq_false_of_not_eq_true hi
    rw [pure,hi',if_false,← Vnu_larger,← non_single_nu ht i hi']
    simp only [Vnu,small,large,hnorm]

theorem middle_G_n_ge_one {t : ℝ} (ht : t∈domain .middle) : 1≤n .middle t t := by
  have hleft : (103/100:ℝ)<(31/100)*Real.sin (1/5)+Real.cos (1/5) := by
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/5 by norm_num)
    have hc := Real.one_sub_sq_div_two_le_cos (x := (1/5:ℝ))
    norm_num at hs hc
    linarith
  have hright : (103/100:ℝ)<(31/100)*Real.sin (7/20)+Real.cos (7/20) := by
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤7/20 by norm_num)
    have hc := Real.one_sub_sq_div_two_le_cos (x := (7/20:ℝ))
    norm_num at hs hc
    linarith
  have htilt := trig_concave_gt (α := (0:ℝ)) (A := (31/100:ℝ)) (B := (1:ℝ))
    (m := (103/100:ℝ)) (l := (1/5:ℝ)) (u := (7/20:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]) ht
    (by simpa using hleft) (by simpa using hright)
  have hk := (middle_bounds ht).1
  have hk0 := (positive ht).1
  have hh := mul_lt_mul_of_pos_left htilt hk0
  dsimp [n,g,SecondaryEStress.tiltedWeight]
  simp only [zero_mul,zero_add,one_mul] at hh
  nlinarith

theorem G_norm {b : Band} (de : Bool) {t : ℝ} {i : Fin 4}
    (hi : b=.low → i=2) (u : ℝ) :
    pairNorm (firstData (Gcase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Gcase b de i)))
      (secondData (Gcase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Gcase b de i))) u=
      pairNorm (alpha b de t t 0 i) (beta b t t i) u := by
  rw [Gcase_index de hi]
  cases b <;> cases de <;> fin_cases i <;>
    simp_all [Gcase,firstData,secondData,band,atG,isDE,nData,n,
      SecondaryEStress.tiltedWeight,alpha,beta,r,pairNorm_symm]

theorem E_norm {b : Band} (de : Bool) {t : ℝ} {i : Fin 4}
    (hi : b=.low → i=2) (u : ℝ) :
    pairNorm (firstData (Ecase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Ecase b de i)))
      (secondData (Ecase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Ecase b de i))) u=
      pairNorm (alpha b de t 0 t i) (beta b t 0 i) u := by
  rw [Ecase_index de hi]
  cases b <;> cases de <;> fin_cases i <;>
    simp_all [Ecase,firstData,secondData,band,atG,isDE,nData,pData,rData,n,
      SecondaryEStress.tiltedWeight,alpha,beta,p,r,pairNorm_symm]

theorem G_nu_le {b : Band} (de : Bool) {t : ℝ} (ht : t∈domain b)
    {i : Fin 4} (hi : b=.low → i=2) :
    nu b de t t 0 i≤nuData (Gcase b de i) t (Real.sin t) (Real.cos t) := by
  cases b
  · have hii := hi rfl
    subst i
    cases de <;> simp [Gcase,nu,nuData,band,atG,isDE,negativeIndex]
  · have hn := middle_G_n_ge_one ht
    have hc : (1:ℝ)≤c .middle t := by linarith [(middle_bounds ht).2.2.1]
    cases de <;> fin_cases i <;>
      simp [Gcase,nu,nuData,band,atG,isDE,negativeIndex,large,alpha,beta,r,p,
        nData,show k .middle t*(Real.cos t+g .middle t*Real.sin t)=n .middle t t by rfl,
        max_eq_right hn,max_eq_right hc]
  · have hn := (high_n ht ⟨(angle ht).1,le_rfl⟩).2.le
    have hmax : max (1:ℝ) (n .high t t)≤53/50 := max_le (by norm_num) hn
    have hc : (1:ℝ)≤c .high t := by norm_num [c]
    cases de <;> fin_cases i <;>
      simp [Gcase,nu,nuData,band,atG,isDE,negativeIndex,large,alpha,beta,r,p,
        nData,show k .high t*(Real.cos t+g .high t*Real.sin t)=n .high t t by rfl,
        max_eq_right hc,hmax]

theorem E_nu_le {b : Band} (de : Bool) {t : ℝ} (ht : t∈domain b)
    {i : Fin 4} (hi : b=.low → i=2) :
    nu b de t 0 t i≤nuData (Ecase b de i) t (Real.sin t) (Real.cos t) := by
  cases b
  · have hii := hi rfl
    subst i
    cases de <;> simp [Ecase,nu,nuData,band,atG,isDE,negativeIndex]
  · have hk : k .middle t≤1 := (middle_bounds ht).2.1.le
    have hc : (1:ℝ)≤c .middle t := by linarith [(middle_bounds ht).2.2.1]
    have hr : (1:ℝ)≤r .middle t :=
      (middle_split ht ⟨(angle ht).1,le_rfl⟩ ⟨(angle ht).1,le_rfl⟩).2.2.2.2.1
    have hkr : k .middle t≤r .middle t := hk.trans hr
    have hpc := SoleBalancedPolynomials.middle_p_lt_c ht
    cases de <;> fin_cases i <;>
      simp [Ecase,nu,nuData,band,atG,isDE,negativeIndex,large,alpha,beta,
        n,SecondaryEStress.tiltedWeight,nData,rData,
        max_eq_left hkr,max_eq_right hc,max_eq_right hpc.le]
  · have hk : (1:ℝ)≤k .high t := by linarith [(high_bounds ht).1]
    have hc : (1:ℝ)≤c .high t := by norm_num [c]
    cases de <;> fin_cases i <;>
      simp [Ecase,nu,nuData,band,atG,isDE,negativeIndex,large,alpha,beta,
        n,SecondaryEStress.tiltedWeight,nData,p,r,max_eq_right hk,max_eq_right hc]

theorem G_charge_le {b : Band} (de : Bool) {t : ℝ} (ht : t∈domain b)
    (R : ℝ) {i : Fin 4} (hi : b=.low → i=2) :
    charge (Gcase b de i) R t≤
      pure (single de i) R (small b de t t 0 i) (large b de t t 0 i) (nu b de t t 0 i) t := by
  rw [pure_eq ht]
  have hm := mul_le_mul_of_nonpos_right (G_nu_le de ht hi)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [charge,Vnu]
  rw [G_norm de hi (-t),G_norm de hi 0]
  linarith

theorem E_charge_le {b : Band} (de : Bool) {t : ℝ} (ht : t∈domain b)
    (R : ℝ) {i : Fin 4} (hi : b=.low → i=2) :
    charge (Ecase b de i) R t≤
      pure (single de i) R (small b de t 0 t i) (large b de t 0 t i) (nu b de t 0 t i) t := by
  rw [pure_eq ht]
  have hm := mul_le_mul_of_nonpos_right (E_nu_le de ht hi)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [charge,Vnu]
  rw [E_norm de hi (-t),E_norm de hi 0]
  linarith

end SquaresInCircles.Eight.TableFree.SoleEndpointCharges

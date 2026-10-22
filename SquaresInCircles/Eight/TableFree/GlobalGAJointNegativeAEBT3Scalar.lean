module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Taylor

/-!
# Both actual radical endpoints for the joint-negative BT3 family

Uncompiled conclusion of the BT3 scalar companion. The exact factor f
clears the reciprocal coefficient m = c/f. The variable tilt support
is the fourth radical; it is not replaced by a constant tilt reserve.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
open Candidate Secondary Polynomial Certificate (Row Endpoint)
open PositiveAngularEnvelope OrdinaryAngleConcavity

theorem constant_bounds : R<(Certificate.Rplus:ℝ) ∧
    1/Real.sqrt 2<(Certificate.dPlus:ℝ) :=
  ⟨JointNegativeAETD2.Analytic.constant_bounds.1,JointNegativeAETD2.Analytic.constant_bounds.2.2⟩

def rationalSum (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  ∑i,weightData r e c eta s t i*(vData r e k c eta s t i+(alphaData r e k c eta s t i)^2)/
    (2*alphaData r e k c eta s t i)
def radicalSum (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  ∑i,weightData r e c eta s t i*Real.sqrt (vData r e k c eta s t i)

theorem five_mass_identity (a v w : Fin 5→ℝ) (ha : ∀i,a i≠0) :
    (∑i,w i*(v i+(a i)^2)*∏j∈Finset.univ.erase i,a j)=
      2*(∏i,a i)*(∑i,w i*(v i+(a i)^2)/(2*a i)) := by
  have h0 : (Finset.univ.erase (0:Fin 5))={1,2,3,4} := by decide
  have h1 : (Finset.univ.erase (1:Fin 5))={0,2,3,4} := by decide
  have h2 : (Finset.univ.erase (2:Fin 5))={0,1,3,4} := by decide
  have h3 : (Finset.univ.erase (3:Fin 5))={0,1,2,4} := by decide
  have h4 : (Finset.univ.erase (4:Fin 5))={0,1,2,3} := by decide
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ,h0,h1,h2,h3,h4]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]
  ring

theorem factorization (r : Row) (e : Endpoint) (k c eta s t : ℝ)
    (ha : ∀i,0<alphaData r e k c eta s t i) :
    numeratorData r e k c eta s t=2*(∏i,alphaData r e k c eta s t i)*
      (AData r e k c eta s t-(Certificate.Rplus:ℝ)*rationalSum r e k c eta s t) := by
  have hh := five_mass_identity (alphaData r e k c eta s t) (vData r e k c eta s t)
    (weightData r e c eta s t) (fun i => (ha i).ne')
  dsimp [numeratorData,rationalSum]
  rw [hh]
  ring

theorem actual_data (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (∀i,0<alphaData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) i) ∧
      (∀i,0≤vData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) i) ∧
      (∀i,0≤weightData r e (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) i) := by
  have hr := Explicit.ranges r hz
  have hi := JointNegativeAETD2.Analytic.input_bounds (Explicit.frame_domain r hz)
  have hb := data_bounds r e hr.k_domain hr.c_domain hr.eta_domain hi.1 hi.2.1
  refine ⟨fun i => by linarith [(hb.1 i).1],?_,fun i => (hb.2.2.1 i).1⟩
  intro i
  cases r <;> cases e <;> fin_cases i <;>
    simp only [vData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first
    | positivity
    | nlinarith [sq_nonneg (Explicit.k .low z-Real.sin z),Real.sin_sq_add_cos_sq z]
    | nlinarith [sq_nonneg (Explicit.k .middle z-Real.sin z),Real.sin_sq_add_cos_sq z]
    | nlinarith [sq_nonneg (Explicit.k .high z-Real.sin z),Real.sin_sq_add_cos_sq z]

theorem rational_model_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<AData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z)-
      (Certificate.Rplus:ℝ)*rationalSum r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) := by
  have hp := actual_numerator_positive r e hz
  have hd := actual_data r e hz
  rw [factorization r e _ _ _ _ _ hd.1] at hp
  have hm : 0<∏i,alphaData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) i :=
    Finset.prod_pos (fun i _ => hd.1 i)
  exact (mul_pos_iff_of_pos_left (by positivity : 0<2*(∏i,
    alphaData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) i))).mp hp

theorem radical_model_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<AData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z)-
      (Certificate.Rplus:ℝ)*radicalSum r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) := by
  have hd := actual_data r e hz
  have hsum : radicalSum r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z)≤
      rationalSum r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (ScalarRadicalTransfer.sqrt_le_mass_majorant (hd.2.1 i) (hd.1 i)) (hd.2.2 i)
    simpa [mul_div_assoc] using hh
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show (0:ℝ)≤(Certificate.Rplus:ℝ) by norm_num [Certificate.Rplus])
  linarith [rational_model_positive r e hz]

def actualA (r : Row) (e : Endpoint) (k c eta z : ℝ) : ℝ :=
  (if e=.V then tilt eta z*(2*k+5+Real.cos z)+c*TData eta (Real.sin z) (Real.cos z)
   else (tilt eta z*(2*k+5)+c*TData eta (Real.sin z) (Real.cos z))*Real.cos z+
     tilt eta z*(1+(13/12)*Real.sin z))-
    if Certificate.diagonalD r then
      (R/Real.sqrt 2)*(1+c)*tilt eta z*(if e=.V then 1 else Real.cos z) else 0
def endpoint (e : Endpoint) (k c eta z : ℝ) : ℝ :=
  if e=.V then tilt eta z*(baseline k c eta z+V R k 1 z)
  else tilt eta z*Real.cos z*(baseline k c eta z+F k z)

theorem cleared_B_norm {f c : ℝ} (hf : 0<f) :
    f*Real.sqrt (1+(c/f)^2)=Real.sqrt (f^2+c^2) := by
  have hleft := Real.sq_sqrt (show 0≤1+(c/f)^2 by positivity)
  have hright := Real.sq_sqrt (show 0≤f^2+c^2 by positivity)
  have hid : f^2*(1+(c/f)^2)=f^2+c^2 := by field_simp [hf.ne']; ring
  have hpos := mul_nonneg hf.le (Real.sqrt_nonneg (1+(c/f)^2))
  nlinarith [Real.sqrt_nonneg (f^2+c^2)]

theorem endpoint_identity (r : Row) (e : Endpoint) {k c eta z : ℝ}
    (hz : z∈Icc 0 frameCap) (hf : 0<tilt eta z)
    (hD : (Certificate.diagonalD r=true → 1≤c) ∧ (Certificate.diagonalD r=false → c≤1)) :
    endpoint e k c eta z=actualA r e k c eta z-
      R*radicalSum r e k c eta (Real.sin z) (Real.cos z) := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hB := cleared_B_norm (c:=c) hf
  have hnorm := NegativeAPositiveTD.SecantBaseline.support_norm_identity (r:=k) hcos
  have hroot : Real.sqrt (k^2+1)=Real.sqrt (1+k^2) := by congr 1; ring
  have hpair : pairNorm k 1 (-z)=Real.sqrt (1+k^2-2*k*Real.sin z) := by
    dsimp [pairNorm,PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct]
    rw [Real.sin_neg]
    congr 1
    ring
  have hzroot : pairNorm k 1 0=Real.sqrt (1+k^2) := by
    simp [pairNorm,PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct]
    congr 1
    ring
  have hD' : dNorm c=if Certificate.diagonalD r then (1+c)/Real.sqrt 2 else Real.sqrt (1+c^2) := by
    cases r
    · exact JointNegativeAETD2.Analytic.dNorm_diagonal (hD.1 rfl)
    · exact JointNegativeAETD2.Analytic.dNorm_diagonal (hD.1 rfl)
    · exact JointNegativeAETD2.Analytic.dNorm_full (hD.2 rfl)
  cases e <;> cases r <;>
    simp only [endpoint,baseline,actualA,radicalSum,vData,weightData,Certificate.diagonalD,
      if_true,if_false,reduceCtorEq,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.sqrt_zero,zero_mul,mul_zero,mul_one,one_mul,add_zero,sub_zero,V,hpair,hzroot,
      F,JointNegativeAETD2.F,SecantNormCurvature.normalized,SecantNormCurvature.secant,
      hnorm,hroot,hD',NegativeAPositiveTD.SecantBaseline.denominator,
      fData,TData,sigma,fullSupport,one_pow]
  all_goals
    have hB' : tilt eta z*Real.sqrt (1+(c/tilt eta z)^2)=
        Real.sqrt ((Real.cos z+eta*Real.sin z)^2+c^2) := by simpa [tilt] using hB
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hf.ne',hcos.ne']
    nlinarith only [hB']

theorem A_lower (r : Row) (e : Endpoint) {k c eta z : ℝ}
    (hz : z∈Icc 0 frameCap) (hc : 0≤c) (hf : 0≤tilt eta z) :
    AData r e k c eta (Real.sin z) (Real.cos z)≤actualA r e k c eta z := by
  have hcos : 0≤Real.cos z := by linarith [(transport_trig hz).1]
  have hd : R/Real.sqrt 2≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ) := by
    have hh := mul_le_mul constant_bounds.1.le constant_bounds.2.le
      (by positivity : 0≤1/Real.sqrt 2)
      (by norm_num [Certificate.Rplus] : 0≤(Certificate.Rplus:ℝ))
    simpa only [div_eq_mul_inv,one_mul] using hh
  have h1 := mul_le_mul_of_nonneg_right hd (show 0≤1+c by linarith)
  have h2 := mul_le_mul_of_nonneg_right h1 hf
  have h3 := mul_le_mul_of_nonneg_right h2 hcos
  cases r <;> cases e <;>
    simp only [AData,actualA,fData,tilt,Certificate.diagonalD,if_true,if_false,
      reduceCtorEq,mul_one,sub_zero] at ⊢ h2 h3 <;> linarith

theorem endpoint_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<endpoint e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) z := by
  have hr := Explicit.ranges r hz
  have hd := actual_data r e hz
  have hf : 0<tilt (Explicit.eta r z) z := by
    change 0<Explicit.f r z
    linarith [hr.f_domain.1]
  have hsum : 0≤radicalSum r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hd.2.2 i) (Real.sqrt_nonneg _))
  have hR := mul_le_mul_of_nonneg_right constant_bounds.1.le hsum
  have hA := A_lower r e (k:=Explicit.k r z) (Explicit.frame_domain r hz)
    (show 0≤Explicit.c r z by linarith [hr.c_domain.1]) hf.le
  rw [endpoint_identity r e (Explicit.frame_domain r hz) hf (Explicit.D_branch r hz)]
  linarith [radical_model_positive r e hz]

end Analytic

theorem scalar_endpoints (r : Certificate.Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<baseline (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) z+
      OrdinaryAngleConcavity.V Secondary.R (Explicit.k r z) 1 z ∧
    0<baseline (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) z+F (Explicit.k r z) z := by
  have hf : 0<tilt (Explicit.eta r z) z := by
    change 0<Explicit.f r z
    linarith [(Explicit.ranges r hz).f_domain.1]
  have hcos : 0<Real.cos z := by linarith [(transport_trig (Explicit.frame_domain r hz)).1]
  have hV := Analytic.endpoint_positive r .V hz
  have hF := Analytic.endpoint_positive r .F hz
  simp only [Analytic.endpoint,if_true,if_false,reduceCtorEq] at hV hF
  exact ⟨(mul_pos_iff_of_pos_left hf).mp hV,
    (mul_pos_iff_of_pos_left (mul_pos hf hcos)).mp hF⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3

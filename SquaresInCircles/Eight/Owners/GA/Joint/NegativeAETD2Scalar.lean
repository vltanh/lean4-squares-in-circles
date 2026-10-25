module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Taylor
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SecantBaseline
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer

/-!
# Eight squares: both actual radical endpoints for the joint-negative TD2 family

Positive auxiliary
masses majorize the original radicals by a completed square; the six
polynomial reserves survive the explicit Taylor allowance. The two
final inequalities involve the actual trigonometric coefficient family.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Analytic
open Candidate Secondary Polynomial
open Certificate (Row Endpoint)
open PositiveAngularEnvelope OrdinaryAngleConcavity

theorem constant_bounds : R<(Certificate.Rplus:ℝ) ∧ sigma<(Certificate.sigmaPlus:ℝ) ∧
    1/Real.sqrt 2<(Certificate.dPlus:ℝ) := by
  have hR0 := Real.sqrt_nonneg qCap
  have hR2 := Real.sq_sqrt (show (0:ℝ)≤qCap by norm_num [qCap])
  have hN0 := Real.sqrt_nonneg (1+eta^2)
  have hN2 := Real.sq_sqrt (show (0:ℝ)≤1+eta^2 by positivity)
  have hRN : (R*Real.sqrt (1+eta^2))^2=qCap*(1+eta^2) := by
    rw [mul_pow,hR2,hN2]
  have hRN0 : 0≤R*Real.sqrt (1+eta^2) := mul_nonneg hR0 hN0
  have hd0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hd2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  refine ⟨?_,?_,?_⟩
  · norm_num [Certificate.Rplus,qCap] at hR2 ⊢
    nlinarith
  · dsimp [sigma,fullSupport]
    norm_num [Certificate.sigmaPlus,eta,qCap] at hRN ⊢
    nlinarith
  · apply (div_lt_iff₀ hd0).2
    norm_num [Certificate.dPlus]
    nlinarith

def rationalSum (r : Row) (e : Endpoint) (k c s t : ℝ) : ℝ :=
  ∑i,weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)/
    (2*alphaData r e k c s t i)
def radicalSum (r : Row) (e : Endpoint) (k c s t : ℝ) : ℝ :=
  ∑i,weightData r e s t i*Real.sqrt (vData r e k c s t i)

theorem four_mass_identity (a v w : Fin 4→ℝ) (ha : ∀i,a i≠0) :
    (∑i,w i*(v i+(a i)^2)*∏j∈Finset.univ.erase i,a j)=
      2*(∏i,a i)*(∑i,w i*(v i+(a i)^2)/(2*a i)) := by
  have h0 : (Finset.univ.erase (0:Fin 4))={1,2,3} := by decide
  have h1 : (Finset.univ.erase (1:Fin 4))={0,2,3} := by decide
  have h2 : (Finset.univ.erase (2:Fin 4))={0,1,3} := by decide
  have h3 : (Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ,h0,h1,h2,h3]
  field_simp [ha 0,ha 1,ha 2,ha 3]

theorem factorization (r : Row) (e : Endpoint) (k c s t : ℝ)
    (ha : ∀i,0<alphaData r e k c s t i) :
    numeratorData r e k c s t=2*(∏i,alphaData r e k c s t i)*
      (hData r e k c s t-(Certificate.Rplus:ℝ)*rationalSum r e k c s t) := by
  have hh := four_mass_identity (alphaData r e k c s t) (vData r e k c s t)
    (weightData r e s t) (fun i=>(ha i).ne')
  dsimp [numeratorData,rationalSum]
  rw [hh]
  ring

theorem actual_data (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (∀i,0<alphaData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) i) ∧
      (∀i,0≤vData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) i) ∧
      (∀i,0≤weightData r e (Real.sin z) (Real.cos z) i) := by
  have hr := Explicit.ranges r hz
  have hi := input_bounds (Explicit.frame_domain r hz)
  have hm : mData (Explicit.c r z) (Real.sin z) (Real.cos z)∈Icc (0:ℝ) (7/5) := by
    change Explicit.m r z∈Icc (0:ℝ) (7/5)
    exact ⟨by linarith [hr.1.1,hr.2.2.2.1],by linarith [hr.2.2.2.2.1,hr.2.2.2.2.2.1]⟩
  have hb := data_bounds r e hr.1 ⟨hr.2.1,hr.2.2.1.le⟩ hi.1 hi.2.1 hm
  refine ⟨fun i=>by linarith [(hb.1 i).1],?_,fun i=>(hb.2.2.1 i).1⟩
  intro i
  rcases i with ⟨_|_|_|_|n,hi⟩
  · show 0≤1+(Explicit.k r z)^2; positivity
  · show 0≤1+(mData (Explicit.c r z) (Real.sin z) (Real.cos z))^2; positivity
  · show 0≤(if e=.V then 1+(Explicit.k r z)^2-2*(Explicit.k r z)*Real.sin z
      else 1+(Explicit.k r z)^2*(Real.cos z)^2)
    split_ifs
    · nlinarith [sq_nonneg (Explicit.k r z-Real.sin z),Real.sin_sq_add_cos_sq z]
    · positivity
  · show 0≤(if Certificate.diagonalD r then 0 else 1+(Explicit.c r z)^2)
    split_ifs
    · exact le_rfl
    · positivity
  · omega

theorem rational_model_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<hData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z)-
      (Certificate.Rplus:ℝ)*rationalSum r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) := by
  have hp := actual_numerator_positive r e hz
  have hd := actual_data r e hz
  rw [factorization r e _ _ _ _ hd.1] at hp
  have hm : 0<∏i,alphaData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) i :=
    Finset.prod_pos (fun i _=>hd.1 i)
  exact (mul_pos_iff_of_pos_left (by positivity : 0<2*(∏i,
    alphaData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) i))).mp hp

theorem radical_model_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<hData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z)-
      (Certificate.Rplus:ℝ)*radicalSum r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) := by
  have hd := actual_data r e hz
  have hsum : radicalSum r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z)≤
      rationalSum r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (ScalarRadicalTransfer.sqrt_le_mass_majorant (hd.2.1 i) (hd.1 i)) (hd.2.2 i)
    simpa [mul_div_assoc] using hh
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show (0:ℝ)≤(Certificate.Rplus:ℝ) by norm_num [Certificate.Rplus])
  linarith [rational_model_positive r e hz]

def actualH (r : Row) (e : Endpoint) (k c z : ℝ) : ℝ :=
  (if e=.V then 2*k+5+Real.cos z+c*(1+2*Real.cos z+(1/2+(3/2)*eta-sigma)*Real.sin z)
   else (2*k+5+c*(1+2*Real.cos z+(1/2+(3/2)*eta-sigma)*Real.sin z))*Real.cos z+
     1+(13/12)*Real.sin z)-
    if Certificate.diagonalD r then R/Real.sqrt 2*(1+c)*(if e=.V then 1 else Real.cos z) else 0
def endpoint (e : Endpoint) (k c z : ℝ) : ℝ :=
  if e=.V then baseline k c z+V R k 1 z else Real.cos z*(baseline k c z+F k z)

theorem dNorm_diagonal {c : ℝ} (hc : 1≤c) : dNorm c=(1+c)/Real.sqrt 2 := by
  simp [dNorm,hc]
theorem dNorm_full {c : ℝ} (hc : c≤1) : dNorm c=Real.sqrt (1+c^2) := by
  by_cases hh : 1≤c
  · have he : c=1 := le_antisymm hc hh
    subst c
    have hs0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
    have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    simp only [dNorm,le_refl,ite_true,one_pow]
    norm_num
  · simp [dNorm,hh]

theorem endpoint_identity (r : Row) (e : Endpoint) {k c z : ℝ}
    (hz : z∈Icc 0 frameCap)
    (hD : (Certificate.diagonalD r=true → 1≤c) ∧ (Certificate.diagonalD r=false → c≤1)) :
    endpoint e k c z=actualH r e k c z-R*radicalSum r e k c (Real.sin z) (Real.cos z) := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hnorm := NegativeAPositiveTD.SecantBaseline.support_norm_identity (r:=k) hcos
  have hroot : Real.sqrt (k^2+1)=Real.sqrt (1+k^2) := by congr 1; ring
  have hpair : pairNorm k 1 (-z)=Real.sqrt (1+k^2-2*k*Real.sin z) := by
    dsimp [pairNorm,PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct]
    rw [Real.sin_neg]
    congr 1
    ring
  have hzroot : pairNorm k 1 0=Real.sqrt (1+k^2) := by
    simp [pairNorm]
    congr 1
  have hD' : dNorm c=if Certificate.diagonalD r then (1+c)/Real.sqrt 2 else Real.sqrt (1+c^2) := by
    cases r
    · exact dNorm_diagonal (hD.1 rfl)
    · exact dNorm_diagonal (hD.1 rfl)
    · exact dNorm_full (hD.2 rfl)
  cases e <;> cases r <;>
    simp only [endpoint,baseline,actualH,radicalSum,vData,weightData,Certificate.diagonalD,
      ite_true,ite_false,reduceCtorEq,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.sqrt_zero,mul_zero,mul_one,one_mul,sub_zero,V,hpair,hzroot,
      F,SecantNormCurvature.normalized,SecantNormCurvature.secant,hnorm,hroot,hD',
      mData,tilted,NegativeAPositiveTD.SecantBaseline.denominator]
  all_goals try rw [Real.tan_eq_sin_div_cos]
  all_goals field_simp [hcos.ne']
  all_goals ring

theorem H_lower (r : Row) (e : Endpoint) {k c z : ℝ}
    (hz : z∈Icc 0 frameCap) (hc : 0≤c) :
    hData r e k c (Real.sin z) (Real.cos z)≤actualH r e k c z := by
  have ht := transport_trig hz
  have hcos : 0≤Real.cos z := by linarith [ht.1]
  have hσ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right constant_bounds.2.1.le ht.2.2.1) hc
  have hd : R/Real.sqrt 2≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ) := by
    have hh := mul_le_mul constant_bounds.1.le constant_bounds.2.2.le
      (by positivity : 0≤1/Real.sqrt 2)
      (by norm_num [Certificate.Rplus] : 0≤(Certificate.Rplus:ℝ))
    simpa only [div_eq_mul_inv,one_mul] using hh
  have hd' := mul_le_mul_of_nonneg_right hd (show 0≤1+c by linarith)
  have hd'' := mul_le_mul_of_nonneg_right hd' hcos
  have hσ' := mul_le_mul_of_nonneg_right hσ hcos
  cases r <;> cases e <;>
    simp only [hData,actualH,jData,Certificate.diagonalD,ite_true,ite_false,reduceCtorEq,mul_one,sub_zero]
  all_goals
    simp only [eta,Certificate.sigmaPlus,Certificate.Rplus,Certificate.dPlus] at *
    linarith

theorem endpoint_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<endpoint e (Explicit.k r z) (Explicit.c r z) z := by
  have hr := Explicit.ranges r hz
  have hd := actual_data r e hz
  have hsum : 0≤radicalSum r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) :=
    Finset.sum_nonneg (fun i _=>mul_nonneg (hd.2.2 i) (Real.sqrt_nonneg _))
  have hR := mul_le_mul_of_nonneg_right constant_bounds.1.le hsum
  have hH := H_lower r e (k:=Explicit.k r z) (Explicit.frame_domain r hz)
    (show 0≤Explicit.c r z by linarith [hr.1.1,hr.2.1])
  rw [endpoint_identity r e (Explicit.frame_domain r hz) (Explicit.D_branch r hz)]
  linarith [radical_model_positive r e hz]

end Analytic

/-- The two exact endpoint inequalities, including both branch endpoints. -/
theorem scalar_endpoints (r : Certificate.Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<baseline (Explicit.k r z) (Explicit.c r z) z+OrdinaryAngleConcavity.V
      Secondary.R (Explicit.k r z) 1 z ∧
      0<baseline (Explicit.k r z) (Explicit.c r z) z+F (Explicit.k r z) z := by
  have hV := Analytic.endpoint_positive r .V hz
  have hF := Analytic.endpoint_positive r .F hz
  have hcos : 0<Real.cos z := by linarith [(transport_trig (Explicit.frame_domain r hz)).1]
  refine ⟨by simpa [Analytic.endpoint] using hV,?_⟩
  simp only [Analytic.endpoint,ite_false,reduceCtorEq] at hF
  exact (mul_pos_iff_of_pos_left hcos).mp hF

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2

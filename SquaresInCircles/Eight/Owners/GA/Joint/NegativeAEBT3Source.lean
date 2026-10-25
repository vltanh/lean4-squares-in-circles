module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3BlockBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonCertificates
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Taylor
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonEndpoints
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2GainComparison
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Taylor
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleAngle
public import SquaresInCircles.Eight.Owners.GA.Sorted.DSevenFifthsActual
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer

/-!
# Eight squares: negative A and core E with positive BT3 and TD0

The seven separator inequalities of the cycle give a nonpositive stress
(`concentrated_nonpositive`). Their signed angle budgets force one of the concentrated
alternatives, which are all positive. The TD0 error is independent, and T keeps its radial state.
-/

section
/-!
## The three unit-pair chord reserves for the BT3 penalty endpoints

The two short-left-endpoint chords are established at k = .65 and
extended to the whole k interval by monotonicity of the exact angle
derivative in k. The cost at zero is then compared with the relevant
chord; no derivative of the weight family is used here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Chords
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus
open JointNegativeAETD2.BlockBounds

theorem right_chord {f : ℝ→ℝ} {a z b : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f) (ha : a∈Ico 0 frameCap)
    (hz : z∈Icc 0 a) (hgap : b*(frameCap-a)≤f frameCap-f a) :
    b*(frameCap-z)≤f frameCap-f z := by
  have hT0 : (0:ℝ)≤frameCap := by norm_num [frameCap]
  generalize frameCap=T at *
  have hden : 0<T-z := by linarith [hz.2,ha.2]
  have hpos : 0<T-a := by linarith [ha.2]
  set u : ℝ := (T-a)/(T-z) with hu_def
  set v : ℝ := (a-z)/(T-z) with hv_def
  have hu : 0≤u := div_nonneg hpos.le hden.le
  have hv : 0≤v := div_nonneg (by linarith [hz.2]) hden.le
  have huv : u+v=1 := by rw [hu_def,hv_def]; field_simp; ring
  have hp : u*z+v*T=a := by rw [hu_def,hv_def]; field_simp; ring
  have hh := hc.2 (show z∈Icc 0 T from ⟨hz.1,hz.2.trans ha.2.le⟩)
    (show T∈Icc 0 T from ⟨hT0,le_rfl⟩) hu hv huv
  simp only [smul_eq_mul,hp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hden.le
  have he : (T-z)*(u*f z+v*f T)=(T-a)*f z+(a-z)*f T := by
    rw [hu_def,hv_def]
    field_simp
  rw [he] at hm
  have hg := mul_le_mul_of_nonneg_left hgap hden.le
  have hfinal : 0≤(T-a)*(f T-f z-b*(T-z)) := by linarith
  have hh' := (mul_nonneg_iff_of_pos_left hpos).mp hfinal
  linarith

theorem chord_k_monotone {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc 0 frameCap) :
    V R (13/20) 1 frameCap-V R (13/20) 1 z≤V R k 1 frameCap-V R k 1 z := by
  have hk0 : 0<k := by linarith [hk.1]
  have hh := derivative_reserve
    (f:=fun t => V R k 1 t-V R (13/20) 1 t)
    (df:=fun t => Vd R k 1 t-Vd R (13/20) 1 t) (k:=0)
    (fun t ht => ((V_hasDerivAt hk0 (by norm_num) ht).sub
      (V_hasDerivAt (by norm_num : (0:ℝ)<13/20) (by norm_num) ht)).continuousAt.continuousWithinAt)
    (fun t ht => (V_hasDerivAt hk0 (by norm_num) (Ioo_subset_Icc_self ht)).sub
      (V_hasDerivAt (by norm_num : (0:ℝ)<13/20) (by norm_num) (Ioo_subset_Icc_self ht)))
    (fun t ht => sub_nonneg.mpr (NegativeAPositiveTD.NegativeSlope.normalized_slope_mono
      (by norm_num) hk.1 (by linarith [hk.2]) (Ioo_subset_Icc_self ht)))
    hz (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz.2
  linarith

theorem low_chord {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc (0:ℝ) (3/20)) :
    (4/5)*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩
  exact (low_unit_chord hz).le.trans (chord_k_monotone hk hz')

theorem V_three_tenths : V R (13/20) 1 (3/10)<3/10 := by
  have ht : |-(3/10:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=-(3/10)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=-(3/10)) (by norm_num) (by norm_num) ht
  have hz := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=0) (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hz2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=0) (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hn2 hz2
  have hs : Real.sin (3/10:ℝ)<739/2500 := by
    have hh := sin_upper_five (x:=(3/10:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  have hc : Real.cos (3/10:ℝ)<4777/5000 := by
    have hh := cos_upper_four (x:=(3/10:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  have hzhi : pairNorm (13/20) 1 0<11927/10000 := by nlinarith
  have hnlo : (10189/10000:ℝ)<pairNorm (13/20) 1 (-(3/10)) := by nlinarith
  have hgap : pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-(3/10))<869/5000 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hgap.le (Real.sqrt_nonneg qCap)
  have hR := mul_le_mul_of_nonneg_right
    (show R≤4947/2500 by linarith [Secondary.radius_bounds.2]) (by norm_num : (0:ℝ)≤869/5000)
  dsimp [V]
  nlinarith

theorem middle_chord {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc (0:ℝ) (3/10)) :
    (3/4)*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hc := V_concave (R:=R) (p:=(13/20:ℝ)) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) (by norm_num) (by norm_num)
  have hfc : frameCap=7/10 := rfl
  have hgap : (3/4)*(frameCap-3/10)≤V R (13/20) 1 frameCap-V R (13/20) 1 (3/10) := by
    linarith [low_V_cap,V_three_tenths]
  have hh := right_chord hc (show (3/10:ℝ)∈Ico 0 frameCap by norm_num [frameCap]) hz hgap
  exact hh.trans (chord_k_monotone hk ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)

theorem cost_zero_chord {k c z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hc : c≤7/5) (hz : z∈Icc 0 frameCap)
    (hdiag : 1≤c → z≤3/10) (hlater : 3/20≤z → c≤6/5) :
    Penalty.cost c 0*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hP : 0≤frameCap-z := sub_nonneg.mpr hz.2
  by_cases hc1 : c<1
  · have hh := unit_negative_growth hk hz
      (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz.2
    simp only [Penalty.cost,ite_eq_left hc1,SecantNormCurvature.secant,Real.cos_zero,div_one]
    simp only [frameCap] at hh hP ⊢
    linarith
  · have hc1' : 1≤c := le_of_not_gt hc1
    by_cases hzlow : z≤3/20
    · have hh := low_chord hk ⟨hz.1,hzlow⟩
      have hcost := (Penalty.cost_bounds hc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).2
      have hp := mul_le_mul_of_nonneg_right hcost hP
      simp only [frameCap] at hh hP hp ⊢
      linarith
    · have hh := middle_chord hk ⟨hz.1,hdiag hc1'⟩
      have hcsmall := hlater (le_of_lt (lt_of_not_ge hzlow))
      have hcost : Penalty.cost c 0≤327/500 := by
        simp only [Penalty.cost,ite_eq_right hc1,SecantNormCurvature.secant,Real.cos_zero,div_one]
        exact max_le (by norm_num) (max_le (by linarith) (by norm_num))
      have hp := mul_le_mul_of_nonneg_right hcost hP
      simp only [frameCap] at hh hP hp ⊢
      linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Chords
end
end
end

section
/-!
## Both actual radical endpoints for the joint-negative TD2 family

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
end
end

section
/-!
## The two radical endpoints of the joint-negative BT3 family

Both endpoint values of each row are positive (`scalar_endpoints`). The tilt factor `f` clears the
reciprocal coefficient `m = c/f` (`cleared_B_norm`). The support of the variable tilt is the fourth
radical, not a constant tilt reserve.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Analytic
open Candidate Secondary Polynomial
open Certificate (Row Endpoint)
open PositiveAngularEnvelope OrdinaryAngleConcavity

theorem constant_bounds : R<(Certificate.Rplus:ℝ) ∧
    1/Real.sqrt 2<(Certificate.dPlus:ℝ) :=
  ⟨JointNegativeAETD2.Analytic.constant_bounds.1,JointNegativeAETD2.Analytic.constant_bounds.2.2⟩

def rationalSum (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  ∑i,weightData r e c eta s t i*(vData r e k c eta s t i+(alphaData r e k c eta s t i)^2)/
    (2*alphaData r e k c eta s t i)
def radicalSum (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  ∑i,weightData r e c eta s t i*Real.sqrt (vData r e k c eta s t i)

private theorem r66_fin5 {P : Fin 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) : ∀ i,P i := by
  intro i
  fin_cases i
  exacts [h0,h1,h2,h3,h4]

theorem five_mass_identity (a v w : Fin 5→ℝ) (ha : ∀i,a i≠0) :
    (∑i,w i*(v i+(a i)^2)*∏j∈Finset.univ.erase i,a j)=
      2*(∏i,a i)*(∑i,w i*(v i+(a i)^2)/(2*a i)) := by
  have h0 : (Finset.univ.erase (0:Fin 5))={1,2,3,4} := by decide
  have h1 : (Finset.univ.erase (1:Fin 5))={0,2,3,4} := by decide
  have h2 : (Finset.univ.erase (2:Fin 5))={0,1,3,4} := by decide
  have h3 : (Finset.univ.erase (3:Fin 5))={0,1,2,4} := by decide
  have h4 : (Finset.univ.erase (4:Fin 5))={0,1,2,3} := by decide
  simp [Fin.sum_univ_five,Fin.prod_univ_five,h0,h1,h2,h3,h4]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

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
  have hsc := Real.sin_sq_add_cos_sq z
  apply r66_fin5
  · simp only [vData,Matrix.cons_val]; positivity
  · simp only [vData,Matrix.cons_val]; positivity
  · simp only [vData,Matrix.cons_val]
    split_ifs
    · nlinarith [sq_nonneg (Explicit.k r z-Real.sin z),sq_nonneg (Real.cos z)]
    · positivity
  · simp only [vData,Matrix.cons_val]; positivity
  · simp only [vData,Matrix.cons_val]
    split_ifs
    · exact le_rfl
    · positivity

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
  have h1 : 0≤f*Real.sqrt (1+(c/f)^2) := mul_nonneg hf.le (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq h1,mul_pow,Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

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
    simp only [pairNorm,Real.sin_neg]
    congr 1
    ring
  have hzroot : pairNorm k 1 0=Real.sqrt (1+k^2) := by
    simp only [pairNorm,Real.sin_zero]
    congr 1
    ring
  have hD' : dNorm c=if Certificate.diagonalD r then (1+c)/Real.sqrt 2 else Real.sqrt (1+c^2) := by
    cases r
    · exact JointNegativeAETD2.Analytic.dNorm_diagonal (hD.1 rfl)
    · exact JointNegativeAETD2.Analytic.dNorm_diagonal (hD.1 rfl)
    · exact JointNegativeAETD2.Analytic.dNorm_full (hD.2 rfl)
  have hc' : tilt eta z*(c/tilt eta z)=c := by field_simp
  have hcc : Real.cos z*(Real.cos z)⁻¹=1 := mul_inv_cancel₀ hcos.ne'
  simp only [tilt] at hB hc'
  cases e
  · cases r <;>
      simp only [endpoint,baseline,actualA,radicalSum,Fin.sum_univ_five,vData,weightData,
        Matrix.cons_val,Certificate.diagonalD,↓reduceIte,reduceCtorEq,
        V,hpair,hzroot,fData,TData,sigma,fullSupport,one_pow,Real.sqrt_zero,hD',tilt] <;>
      linear_combination (1+2*Real.cos z+(1/2+3/2*eta-(R*Real.sqrt (1+eta^2)-(1+eta)/2))*
        Real.sin z)*hc'-R*hB
  · cases r <;>
      simp only [endpoint,baseline,actualA,radicalSum,Fin.sum_univ_five,vData,weightData,
        Matrix.cons_val,Certificate.diagonalD,↓reduceIte,reduceCtorEq,
        F,JointNegativeAETD2.F,SecantNormCurvature.normalized,
        SecantNormCurvature.secant,hnorm,hroot,NegativeAPositiveTD.SecantBaseline.denominator,
        fData,TData,sigma,fullSupport,one_pow,Real.tan_eq_sin_div_cos,Real.sqrt_zero,hD',tilt] <;>
      linear_combination (Real.cos z*(1+2*Real.cos z+(1/2+3/2*eta-(R*Real.sqrt (1+eta^2)-
        (1+eta)/2))*Real.sin z))*hc'-(R*Real.cos z)*hB+
        ((Real.cos z+eta*Real.sin z)+13/12*(Real.cos z+eta*Real.sin z)*Real.sin z-
          R*(Real.cos z+eta*Real.sin z)*Real.sqrt (1+k^2*Real.cos z^2))*hcc

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
    simp only [AData,actualA,fData,tilt,Certificate.diagonalD,ite_true,ite_false,
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
  simp only [Analytic.endpoint,ite_true,ite_false,reduceCtorEq] at hV hF
  exact ⟨(mul_pos_iff_of_pos_left hf).mp hV,
    (mul_pos_iff_of_pos_left (mul_pos hf hcos)).mp hF⟩

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3
end
end

section
/-!
## Every concentrated joint-negative TD2 alternative is positive

The two negative magnitudes are merged while charging the
selected secant. The same endpoint principle is used at z for pure
terms and at h for separated saturated terms.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Concentrated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Source
open Certificate (Row)

def p (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 4→ℝ :=
  pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s
def q (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 4→ℝ :=
  qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s
def base (f : Row) (r s z : ℝ) : ℝ :=
  baseline (Explicit.k f z) (Explicit.c f z) z+F (Explicit.k f z) r+F (Explicit.k f z) s
def positive (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p f atG atH r s z) (q f atG atH r s z) 3 i d
def negative (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 4) : ℝ :=
  V R (p f atG atH r s z i) (q f atG atH r s z i) d
def mixed (f : Row) (atG atH : Bool) (r s z P N : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2) (p f atG atH r s z) (q f atG atH r s z) 3 i P N
def pure (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  NegativeAPositiveTD.Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
    (p f atG atH r s z) (q f atG atH r s z) 3 i j (r+s) z
def saturated (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  NegativeAPositiveTD.Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2)
    (p f atG atH r s z) (q f atG atH r s z) 3 i j (r+s) z
def scalar (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  base f r s z+min (pure f atG atH r s z i j) (saturated f atG atH r s z i j)

theorem canonical_merge {k r s t : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (j : Fin 3) :
    min (V R k 1 t) (F k t)≤
      F k r+F k s+V R k (BlockBounds.canonicalQ r s j) (t-(r+s)) := by
  have he := CommonGain.endpoint hk ht ⟨add_nonneg hr hs,hS⟩
  have hd : 0≤t-(r+s) := by linarith
  have hcap : r+s+(t-(r+s))≤frameCap := by linarith [ht.2]
  fin_cases j
  · have hm := CommonGain.merge hk hr hs (hS.trans ht.2)
    have hmin := min_le_left (V R k 1 (t-(r+s)))
      (V R k (SecantNormCurvature.secant (r+s)) (t-(r+s)))
    simp only [BlockBounds.canonicalQ,Fin.zero_eta,Matrix.cons_val_zero]
    linarith
  · have hm := CommonGain.merge_charged hk hr hs hd hcap
    simpa [BlockBounds.canonicalQ] using he.trans hm
  · have hm := CommonGain.merge_charged_right hk hr hs hd hcap
    simpa [BlockBounds.canonicalQ] using he.trans hm

theorem negative_merge (f : Row) (atG atH : Bool) {r s z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (i : Fin 4) :
    min (V R (Explicit.k f z) 1 t) (F (Explicit.k f z) t)≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+negative f atG atH r s z (t-(r+s)) i := by
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH
    (show t-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [ht.2,hr.1,hs.1]⟩) i
  have hh := canonical_merge (Explicit.ranges f hz).1 hr.1 hs.1 ht hS j
  change _≤negative f atG atH r s z (t-(r+s)) i at hj
  linarith

theorem pure_negative_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 4) :
    0<base f r s z+negative f atG atH r s z (z-(r+s)) i := by
  have hh := negative_merge f atG atH hz hr hs hH (Explicit.frame_domain f hz) hS i
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) z+
      min (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) := by
    rcases le_total (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) with h|h
    · rw [min_eq_left h]; exact he.1
    · rw [min_eq_right h]; exact he.2
  dsimp [base]
  linarith

theorem pure_positive_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 4) :
    0<base f r s z+positive f atG atH r s z (r+s-z) i := by
  have hk := (Explicit.ranges f hz).1
  have hz' := Explicit.frame_domain f hz
  have hd : r+s-z∈Icc 0 frameCap := ⟨by linarith [hS.1],by linarith [hS.2,hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hd i
  change -BlockBounds.charge f z*(r+s-z)≤positive f atG atH r s z (r+s-z) i at hu
  have hm := CommonGain.merge hk hr.1 hs.1 hS.2
  have hg := CommonGain.growth hk.1 hz' ⟨add_nonneg hr.1 hs.1,hS.2⟩ hS.1
  have hc := mul_le_mul_of_nonneg_right
    (show BlockBounds.charge f z≤9/10 by linarith [(BlockBounds.charge_bounds f hz).2.1]) hd.1
  have he := (scalar_endpoints f hz).2
  dsimp [base]
  linarith

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 4) :
    0<base f r s z+mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i := by
  by_cases horder : r+s≤z
  · have hl := BlockBounds.same_negative f atG atH hz hr hs hH horder i
    have hp := pure_negative_positive f atG atH hz hr hs hH horder i
    change negative f atG atH r s z (z-(r+s)) i≤
      mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
    linarith
  · have horder' : z≤r+s := le_of_lt (lt_of_not_ge horder)
    have hl := BlockBounds.same_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
    have hp := pure_positive_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
    change positive f atG atH r s z (r+s-z) i≤
      mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
    linarith

theorem separated_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 4) :
    0<base f r s z+positive f atG atH r s z (frameCap-z) i+
      negative f atG atH r s z (frameCap-(r+s)) j := by
  have hz' := Explicit.frame_domain f hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz'.2],by linarith [hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hP i
  change -BlockBounds.charge f z*(frameCap-z)≤positive f atG atH r s z (frameCap-z) i at hu
  have hn := negative_merge f atG atH hz hr hs hH hcap hS j
  have hV := BlockBounds.separated_V_charge f hz
  have hF := CommonGain.growth (Explicit.ranges f hz).1.1 hz' hcap hz'.2
  have hcharge := mul_le_mul_of_nonneg_right
    (show BlockBounds.charge f z≤9/10 by linarith [(BlockBounds.charge_bounds f hz).2.1]) hP.1
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) z-
      BlockBounds.charge f z*(frameCap-z)+
      min (V R (Explicit.k f z) 1 frameCap) (F (Explicit.k f z) frameCap) := by
    rcases le_total (V R (Explicit.k f z) 1 frameCap) (F (Explicit.k f z) frameCap) with h|h
    · rw [min_eq_left h]; linarith [he.1]
    · rw [min_eq_right h]
      have he2 := he.2
      simp only [frameCap] at hF hcharge he2 ⊢
      linarith
  dsimp [base]
  linarith

theorem all_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 4) :
    0<scalar f atG atH r s z i j := by
  have hp : 0<base f r s z+pure f atG atH r s z i j := by
    by_cases hh : r+s≤z
    · simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,negative] using
        pure_negative_positive f atG atH hz hr hs hH hh j
    · have hh' : z≤r+s := le_of_lt (lt_of_not_ge hh)
      simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,positive] using
        pure_positive_positive f atG atH hz hr hs hH ⟨hh',hS⟩ i
  have hsaturated : 0<base f r s z+saturated f atG atH r s z i j := by
    by_cases hij : i=j
    · simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,mixed] using
        same_positive f atG atH hz hr hs hH hS j
    · have hh := separated_positive f atG atH hz hr hs hH hS i j
      simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,positive,negative,add_assoc] using hh
  unfold scalar
  rcases le_total (pure f atG atH r s z i j) (saturated f atG atH r s z i j) with h|h
  · rw [min_eq_left h]; exact hp
  · rw [min_eq_right h]; exact hsaturated

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Concentrated
end
end
end

section
/-!
## Positivity of every concentrated joint-negative BT3 alternative

The selected secant is charged before the penalty endpoint principle. The distinguished D
same-block alternative is itself a separated term and uses that argument directly. Ordinary
same-block terms reduce to their pure surplus (`same_positive`), and `all_positive` collects every
alternative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Concentrated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Source
open Certificate (Row)
open JointNegativeAETD2

def p (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 5→ℝ :=
  pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s
def q (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 5→ℝ :=
  qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s
def cost (f : Row) (r s z : ℝ) : ℝ := Penalty.cost (Explicit.c f z) (r+s)
def selected (f : Row) (atH : Bool) (z : ℝ) : Fin 5 := distinguished atH (Explicit.c f z)
def base (f : Row) (r s z : ℝ) : ℝ :=
  baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
    F (Explicit.k f z) r+F (Explicit.k f z) s
def positive (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 5) : ℝ :=
  PositiveTD.Hybrid.positive R (cost f r s z) (p f atG atH r s z) (q f atG atH r s z)
    (selected f atH z) i d
def negative (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 5) : ℝ :=
  V R (p f atG atH r s z i) (q f atG atH r s z i) d
def mixed (f : Row) (atG atH : Bool) (r s z P N : ℝ) (i : Fin 5) : ℝ :=
  PositiveTD.Hybrid.block R (cost f r s z) (p f atG atH r s z) (q f atG atH r s z)
    (selected f atH z) i P N
def pure (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  NegativeAPositiveTD.Concentration.pure R (cost f r s z)
    (p f atG atH r s z) (q f atG atH r s z) (selected f atH z) i j (r+s) z
def saturated (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  NegativeAPositiveTD.Concentration.saturated R (cost f r s z)
    (p f atG atH r s z) (q f atG atH r s z) (selected f atH z) i j (r+s) z
def scalar (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  base f r s z+min (pure f atG atH r s z i j) (saturated f atG atH r s z i j)

theorem canonical_allocation {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (hd : 0≤d) (hcap : r+s+d≤frameCap) (j : Fin 3) :
    F k (r+s)+min (V R k 1 d) (V R k (sec (r+s)) d)≤
      F k r+F k s+V R k (BlockBounds.canonicalQ r s j) d := by
  fin_cases j
  · have hm : F k (r+s)≤F k r+F k s := CommonGain.merge hk hr hs (by linarith)
    have hmin := min_le_left (V R k 1 d) (V R k (sec (r+s)) d)
    simp only [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
      Fin.zero_eta,Fin.isValue,Matrix.cons_val_zero]
    linarith
  · simpa [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ] using
      CommonGain.merge_charged hk hr hs hd hcap
  · simpa [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ] using
      CommonGain.merge_charged_right hk hr hs hd hcap

theorem negative_merge (f : Row) (atG atH : Bool) {r s z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (i : Fin 5) :
    min (V R (Explicit.k f z) 1 t) (F (Explicit.k f z) t)≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+negative f atG atH r s z (t-(r+s)) i := by
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH
    (show t-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [ht.2,hr.1,hs.1]⟩) i
  have hh := JointNegativeAETD2.Concentrated.canonical_merge
    (Explicit.ranges f hz).k_domain hr.1 hs.1 ht hS j
  change _≤negative f atG atH r s z (t-(r+s)) i at hj
  linarith

theorem pure_negative_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 5) :
    0<base f r s z+negative f atG atH r s z (z-(r+s)) i := by
  have hh := negative_merge f atG atH hz hr hs hH (Explicit.frame_domain f hz) hS i
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
      min (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) := by
    rcases le_total (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) with h|h
    · rw [min_eq_left h]; exact he.1
    · rw [min_eq_right h]; exact he.2
  dsimp [base]
  linarith

theorem pure_positive_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 5) :
    0<base f r s z+positive f atG atH r s z (r+s-z) i := by
  have hc := Explicit.ranges f hz
  have hz' := Explicit.frame_domain f hz
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS.2⟩
  have hd : r+s-z∈Icc 0 frameCap := ⟨by linarith [hS.1],by linarith [hS.2,hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hS.2 hd i
  change -cost f r s z*(r+s-z)≤positive f atG atH r s z (r+s-z) i at hu
  have hm := CommonGain.merge hc.k_domain hr.1 hs.1 hS.2
  have hg := CommonGain.growth hc.k_domain.1 hz' htotal hS.1
  have hcost : cost f r s z≤9/10 := by
    dsimp [cost]; linarith [(Penalty.cost_bounds hc.c_domain.2 htotal).2]
  have hcharge := mul_le_mul_of_nonneg_right hcost hd.1
  have he := (scalar_endpoints f hz).2
  dsimp [base]
  linarith

theorem negative_allocation (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 5) :
    F (Explicit.k f z) (r+s)+
      min (V R (Explicit.k f z) 1 (frameCap-(r+s)))
        (V R (Explicit.k f z) (sec (r+s)) (frameCap-(r+s)))≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+
        negative f atG atH r s z (frameCap-(r+s)) i := by
  have hd : frameCap-(r+s)∈Icc 0 frameCap :=
    ⟨by linarith,by linarith [hr.1,hs.1]⟩
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH hd i
  have hh := canonical_allocation (Explicit.ranges f hz).k_domain hr.1 hs.1 hd.1
    (show r+s+(frameCap-(r+s))≤frameCap by linarith) j
  change _≤negative f atG atH r s z (frameCap-(r+s)) i at hj
  linarith

theorem separated_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 5) :
    0<base f r s z+positive f atG atH r s z (frameCap-z) i+
      negative f atG atH r s z (frameCap-(r+s)) j := by
  have hc := Explicit.ranges f hz
  have hz' := Explicit.frame_domain f hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz'.2],by linarith [hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hS hP i
  change -cost f r s z*(frameCap-z)≤positive f atG atH r s z (frameCap-z) i at hu
  have hn := negative_allocation f atG atH hz hr hs hH hS j
  have hp : min (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
        (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap)≤
      F (Explicit.k f z) (r+s)+min (V R (Explicit.k f z) 1 (frameCap-(r+s)))
        (V R (Explicit.k f z) (sec (r+s)) (frameCap-(r+s)))-
        (frameCap-z)*Penalty.cost (Explicit.c f z) (r+s) :=
    Penalty.endpoint (c:=Explicit.c f z) hc.k_domain hP.1 htotal
  have hV := Chords.cost_zero_chord hc.k_domain hc.c_domain.2 hz'
    (fun h => (hc.diagonal_cut h).1) hc.later_c
  have hF : 9/10*(frameCap-z)≤F (Explicit.k f z) frameCap-F (Explicit.k f z) z :=
    CommonGain.growth hc.k_domain.1 hz' hcap hz'.2
  have hch : Penalty.cost (Explicit.c f z) frameCap≤9/10 := by
    linarith [(Penalty.cost_bounds hc.c_domain.2 hcap).2]
  have hcharge := mul_le_mul_of_nonneg_right hch hP.1
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
      min (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
        (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap) := by
    rcases le_total
      (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
      (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap) with h|h
    · rw [min_eq_left h]
      nlinarith [he.1]
    · rw [min_eq_right h]
      simp only [frameCap] at hF hcharge ⊢
      linarith [he.2]
  dsimp only [base,cost] at hu ⊢
  linarith

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 5) :
    0<base f r s z+mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i := by
  by_cases hi : i=selected f atH z
  · have hh := separated_positive f atG atH hz hr hs hH hS i i
    simpa [mixed,positive,negative,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,hi,add_assoc] using hh
  · by_cases horder : r+s≤z
    · have hl := BlockBounds.same_negative f atG atH hz hr hs hH horder i hi
      have hp := pure_negative_positive f atG atH hz hr hs hH horder i
      change negative f atG atH r s z (z-(r+s)) i≤
        mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
      linarith
    · have horder' : z≤r+s := le_of_lt (lt_of_not_ge horder)
      have hl := BlockBounds.same_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i hi
      have hp := pure_positive_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
      change positive f atG atH r s z (r+s-z) i≤
        mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
      linarith

theorem all_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 5) :
    0<scalar f atG atH r s z i j := by
  have hp : 0<base f r s z+pure f atG atH r s z i j := by
    by_cases hh : r+s≤z
    · simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,negative] using
        pure_negative_positive f atG atH hz hr hs hH hh j
    · have hh' : z≤r+s := le_of_lt (lt_of_not_ge hh)
      simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,positive] using
        pure_positive_positive f atG atH hz hr hs hH ⟨hh',hS⟩ i
  have hsaturated : 0<base f r s z+saturated f atG atH r s z i j := by
    by_cases hij : i=j
    · simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,mixed] using
        same_positive f atG atH hz hr hs hH hS j
    · have hh := separated_positive f atG atH hz hr hs hH hS i j
      simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,positive,negative,add_assoc] using hh
  unfold scalar
  rcases le_total (pure f atG atH r s z i j) (saturated f atG atH r s z i j) with h|h
  · rw [min_eq_left h]; exact hp
  · rw [min_eq_right h]; exact hsaturated

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Concentrated
end
end
end

section
/-!
## The joint-negative BT3 block minorant at the original points

The negative DE3 case uses the exact one-angle secant-D comparison.
The negative EH1 case uses the ordinary D pair below c=1 and the wider
sorted two-angle envelope above it. Both retain the original TD0 error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

theorem family_rotation (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    Explicit.c f z=Explicit.m f z*tilt (Explicit.eta f z) z := by
  have hf : Explicit.f f z≠0 := (show 0<Explicit.f f z by
    linarith [(Explicit.ranges f hz).f_domain.1]).ne'
  simpa [Explicit.m,Explicit.f] using (div_mul_cancel₀ (Explicit.c f z) hf).symm

theorem ordinary_D_identity {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (k m r s : ℝ) {c : ℝ} (hc : c<1) :
    actualD C true c s=
      PositiveTD.actualPairIncrement (blocks C hg atG true k m c r s 3) (C.point D).reflect := by
  simp [actualD,blocks,PositiveTD.actualPairIncrement,lambdaD,
    JointNegativeAETD2.Source.lambdaD,clippedSupport,not_le.mpr hc,SignedPoint.reflect]
  ring

theorem single_D_identity {C : SignedCycle} {c s : ℝ}
    (hs : s∈Icc 0 frameCap) (hc : c∈Icc (7/10:ℝ) (7/5)) :
    actualD C false c s=SecantD.actualIncrement (sec s) c (delta C.theta T) (C.point D) := by
  have hbase := SecantD.baseline_clipped (JointNegativeAETD2.CommonGain.full_secant_domain hs) hc
  simp [actualD,SecantD.actualIncrement,lambdaD,JointNegativeAETD2.Source.lambdaD,
    pairF,pairG,hbase,edgeWidth,pairWidth]

theorem diagonal_D_identity {C : SignedCycle} {c s : ℝ} (hc : 1≤c) :
    actualD C true c s=
      c*(edgeWidth (delta C.theta T)-1)+edgeWidth (delta C.theta D)-1+(1+c)*GlobalGA.Secondary.diagonal-
        (PositiveBT3.forceA c (delta C.theta T) (delta C.theta D)*(C.point D).a+
          PositiveBT3.forceB c (delta C.theta T) (delta C.theta D)*(-(C.point D).y)) := by
  simp [actualD,lambdaD,JointNegativeAETD2.Source.lambdaD,
    pairF,pairG,PositiveBT3.forceA,PositiveBT3.forceB,clippedSupport,hc,diagonalSupport]
  ring

theorem block_family_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (i : Fin 5) :
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f (delta C.theta B)) (r+s))
      (pWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s)
      (qWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s)
      (distinguished atH (Explicit.c f (delta C.theta B))) i
      (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i).P
      (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i).N≤
      actualBlocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i := by
  let k := Explicit.k f (delta C.theta B)
  let m := Explicit.m f (delta C.theta B)
  let c := Explicit.c f (delta C.theta B)
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  have hz0 := Explicit.frame_domain f hz
  have hb := budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz0.1
  have hcoeff := pair_domain f atG atH hz hr hs hH
  have hordinary (j : Fin 5) (hj : j≠distinguished atH c) {P : SignedPoint}
      (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights atG atH k m c r s j) (qWeights atG atH k m c r s j)
        (blocks C hg atG atH k m c r s j).P (blocks C hg atG atH k m c r s j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG atH k m c r s j) P := by
    have hd := ordinary_coefficients (C:=C) (hg:=hg) (m:=m) (c:=c)
      atG atH (show k≤1 by dsimp [k]; linarith [hc.k_domain.2])
      (show k≤lambdaG atG r by dsimp [k]; linarith [hc.k_domain.2,hl.1.1])
      (show k≤lambdaH atH s by dsimp [k]; linarith [hc.k_domain.2,hl.2.2.1.1]) j hj
    have hp : 0≤(blocks C hg atG atH k m c r s j).p := by
      rw [hd.1]; exact (hcoeff j).1.le
    have hbudget := block_budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz0.1 j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hbudget.1 hbudget.2
    rw [hd.1,hd.2] at hh
    exact hh
  have hn0 : (0:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  have hn1 : (1:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  have hn2 : (2:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  fin_cases i <;> try simp only [Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue]
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn0,k,m,c] using hordinary 0 hn0 hHy (hcontained H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn1,k,m,c] using hordinary 1 hn1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn2,k,m,c] using hordinary 2 hn2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · by_cases ho : ordinaryD atH c
    · have htrue : atH=true := ho.1
      subst htrue
      have hn3 : (3:Fin 5)≠distinguished true c := by simp [distinguished,ho]
      have hh := hordinary 3 hn3 (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hcontained D)
      rw [←ordinary_D_identity (C:=C) (hg:=hg) atG k m r s ho.2] at hh
      simpa [PositiveTD.Hybrid.block,actualBlocks,hn3,k,m,c] using hh
    · have hd : distinguished atH c=3 := by simp [distinguished,ho]
      have hk' : k∈Icc (1/2:ℝ) (17/20) := by
        dsimp [k]; constructor <;> linarith [hc.k_domain.1,hc.k_domain.2]
      cases atH
      · have hneg : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
        have hh := SecantD.actual_minorant (hsorted D) hDy (hcontained D) hq
          (JointNegativeAETD2.CommonGain.full_secant_domain hs) hk' hc.c_domain
          (hc.k_le_m.trans hc.m_le_c) (original_error_bound hvar hneg T)
        rw [←single_D_identity (C:=C) hs hc.c_domain] at hh
        have hsec := Penalty.secant_monotone hs hb.total_domain (by linarith [hr.1])
        have hmax := max_le_max hsec (le_rfl : c≤c)
        have hcost := (mul_le_mul_of_nonneg_left hmax (show (0:ℝ)≤109/200 by norm_num)).trans
          (BlockBounds.cost_max_coefficient (c:=c) hb.total_domain)
        have hcharge := mul_le_mul_of_nonneg_right hcost (positivePart_nonneg (delta C.theta T))
        simp only [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,
          pWeights,qWeights,Matrix.cons_val,Fin.isValue,
          Bool.false_eq_true,↓reduceIte,positivePart_zero,negativePart_zero,add_zero]
        dsimp [SecantD.slope] at hh
        change -Penalty.cost c (r+s)*positivePart (delta C.theta T)+
          V R k 1 (negativePart (delta C.theta T))≤actualD C false c s
        linarith
      · have h1c : 1≤c := by
          by_contra hn
          exact ho ⟨rfl,lt_of_not_ge hn⟩
        have hsmall := hc.diagonal_cut h1c
        have hD := block_budgets hg atG true k m c hr.1 hs.1 ha he hvar hz0.1 (3:Fin 5)
        have hdom : PositiveBT3.SignedDomain (delta C.theta T) (delta C.theta D) := by
          simpa [PositiveBT3.SignedDomain,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,
            blocks,Block.P,Block.N] using hD
        have hh := SortedDSevenFifths.actual_minorant_for (hsorted D) hDy (hcontained D) hq
          (show k∈Icc (1/2:ℝ) SortedDSevenFifths.K from ⟨hk'.1,hsmall.2⟩)
          (show c∈Icc 1 SortedDSevenFifths.Cmax from ⟨h1c,hc.c_domain.2⟩) hdom
        rw [←diagonal_D_identity (C:=C) (s:=s) h1c] at hh
        have hcost : (13/20:ℝ)≤Penalty.cost c (r+s) := by
          simp only [Penalty.cost,ite_eq_right (not_lt.mpr h1c)]
          exact le_max_left _ _
        have hcharge := mul_le_mul_of_nonneg_right hcost
          (add_nonneg (positivePart_nonneg (delta C.theta T)) (positivePart_nonneg (delta C.theta D)))
        have hd' : distinguished true (Explicit.c f (delta C.theta B))=3 := hd
        have ho' : ¬ordinaryD true (Explicit.c f (delta C.theta B)) := ho
        simp only [PositiveTD.Hybrid.block,hd',actualBlocks,blocks,Block.P,Block.N,
          pWeights,qWeights,Matrix.cons_val,Fin.isValue,↓reduceIte,ho']
        dsimp [SortedDSevenFifths.slope,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal] at hh
        change -Penalty.cost c (r+s)*(positivePart (delta C.theta T)+positivePart (delta C.theta D))+
          V R k 1 (negativePart (delta C.theta T)+negativePart (delta C.theta D))≤actualD C true c s
        linarith
  · by_cases ho : ordinaryD atH c <;>
      simp [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,
        pWeights,qWeights,distinguished,ho,c]

theorem original_stress_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12) (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    exactBaseline atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
      (Explicit.c f (delta C.theta B)) (Explicit.eta f (delta C.theta B)) r s (delta C.theta B)+
      (∑i,PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f (delta C.theta B)) (r+s))
        (pWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s)
        (qWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s)
        (distinguished atH (Explicit.c f (delta C.theta B))) i
        (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s i).P
        (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s i).N)≤
      actualStress C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    block_family_lower (hg:=hg) f atG atH hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH
      ha he hz i)
  have hc := Explicit.ranges f hz
  have hT := tReserve_nonnegative (hsorted T) (hcontained T) hq
    (show 0≤Explicit.m f (delta C.theta B) by linarith [hc.k_domain.1,hc.k_le_m])
    hc.eta_domain.1 (Explicit.frame_domain f hz)
  rw [decomposition C atG atH _ _ _ hhg
    (show r∈Icc 0 frameCap by exact ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩)
    hs ha he hA hE (family_rotation f hz)]
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
end
end
end

section
/-!
## Negative A and core E with positive TD2

The seven separation inequalities of the cycle give a nonpositive stress
(`concentrated_nonpositive`). Its common baseline and the signed budgets imply a nonpositive
concentrated scalar, against the coefficient family. The concentrated alternatives are bounds on
the scalar, not configurations, and no support point is moved.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

namespace Source

theorem concentrated_nonpositive {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    ∃i j : Fin 4,Concentrated.scalar f atG atH r s (delta C.theta T) i j≤0 := by
  let k := Explicit.k f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hz' := Explicit.frame_domain f hz
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩
  have hb := budgets hg atG atH k c hr.1 hs.1 ha he hvar hz'.1
  have hp := pair_domain f atG atH hz hr hs hH
  obtain ⟨i,j,hendpoint⟩ := NegativeAPositiveTD.Concentration.concentrate
    R (GlobalGA.Secondary.diagonal-1/2)
    (Concentrated.p f atG atH r s (delta C.theta T))
    (Concentrated.q f atG atH r s (delta C.theta T))
    (fun i => (blocks C hg atG atH k c r s i).P)
    (fun i => (blocks C hg atG atH k c r s i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => show _≤2*_ by
      have hh := hp i; dsimp only [Concentrated.p,Concentrated.q]; linarith [hh.1,hh.2.2])
    (fun i => (blocks C hg atG atH k c r s i).P_nonneg)
    (fun i => (blocks C hg atG atH k c r s i).N_nonneg)
    hb.total_domain hz' hb.positive_bound hb.negative_bound hb.balance
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have hbase := common_baseline_lower (k:=k) (c:=c) atG atH
    (show 0<k by dsimp [k]; linarith [hk.1])
    (show k≤1 by dsimp [k]; linarith [hk.2]) hkc hkm hr' hs hz'
  have hlower := original_stress_lower f atG atH hsorted hcontained hq
    hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hz
  have hupper := stress_nonpositive (k:=k) (c:=c) atG atH
    (show 0≤k by dsimp [k]; linarith [hk.1])
    (show 0≤c by dsimp [k,c] at *; linarith [hk.1,hkc]) hr' hs hz'
    hHG hGA hAB hBT hTD hDE hEH
  refine ⟨i,j,?_⟩
  change min (Concentrated.pure f atG atH r s (delta C.theta T) i j)
    (Concentrated.saturated f atG atH r s (delta C.theta T) i j)≤_ at hendpoint
  dsimp only [Concentrated.p,Concentrated.q] at hendpoint
  dsimp only [Concentrated.scalar,Concentrated.base]
  change baseline k c (delta C.theta T)+F k r+F k s+_≤0
  linarith

end Source

theorem row_cover {z : ℝ} (hz : z∈Icc 0 frameCap) :
    ∃f : Row,z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ) := by
  by_cases hl : z≤3/20
  · exact ⟨.low,by simpa [Certificate.left,Certificate.right] using And.intro hz.1 hl⟩
  by_cases hm : z≤19/100
  · exact ⟨.transition,by simp [Certificate.left,Certificate.right]; constructor <;> linarith⟩
  · exact ⟨.full,by simp [Certificate.left,Certificate.right,frameCap] at *; constructor <;> linarith⟩

/-- The four flat-core systems are impossible. Zero endpoints are allowed; the entry theorems give
the strict interior cuts. -/
theorem original {q r s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : Source.aError C atG= -r) (he : Source.eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) : False := by
  have hb := Source.budgets hg atG atH 1 1 hr.1 hs.1 ha he hvar hz
  obtain ⟨f,hf⟩ := row_cover hb.td_domain
  obtain ⟨i,j,hij⟩ := Source.concentrated_nonpositive f atG atH
    hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hf
    hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (Concentrated.all_positive f atG atH hf hr hs hH hb.total_domain.2 i j)) hij

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

namespace Source

theorem concentrated_nonpositive {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    ∃i j : Fin 5,Concentrated.scalar f atG atH r s (delta C.theta B) i j≤0 := by
  let k := Explicit.k f (delta C.theta B)
  let m := Explicit.m f (delta C.theta B)
  let c := Explicit.c f (delta C.theta B)
  let eta := Explicit.eta f (delta C.theta B)
  have hz' := Explicit.frame_domain f hz
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩
  have hb := budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz'.1
  have hp := pair_domain f atG atH hz hr hs hH
  obtain ⟨i,j,hendpoint⟩ := NegativeAPositiveTD.Concentration.concentrate
    R (Penalty.cost c (r+s))
    (Concentrated.p f atG atH r s (delta C.theta B))
    (Concentrated.q f atG atH r s (delta C.theta B))
    (fun i => (blocks C hg atG atH k m c r s i).P)
    (fun i => (blocks C hg atG atH k m c r s i).N) (distinguished atH c)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => by
      have hh := hp i
      dsimp only [Concentrated.p,Concentrated.q]
      linarith [hh.1,hh.2.2])
    (fun i => (blocks C hg atG atH k m c r s i).P_nonneg)
    (fun i => (blocks C hg atG atH k m c r s i).N_nonneg)
    hb.total_domain hz' hb.positive_bound hb.negative_bound hb.balance
  have hc := Explicit.ranges f hz
  have hf : tilt eta (delta C.theta B)≠0 :=
    (show 0<Explicit.f f (delta C.theta B) by linarith [hc.f_domain.1]).ne'
  have hbase := common_baseline_lower (k:=k) (m:=m) (c:=c) (eta:=eta) atG atH
    (show 0<k by dsimp [k]; linarith [hc.k_domain.1])
    (show k≤1 by dsimp [k]; linarith [hc.k_domain.2])
    (hc.k_le_m.trans hc.m_le_c) hc.k_le_m hr' hs hz' hf (family_rotation f hz)
  have hlower := original_stress_lower f atG atH hsorted hcontained hq
    hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hz
  have hupper := stress_nonpositive (k:=k) (m:=m) (c:=c) atG atH
    (show 0≤k by dsimp [k]; linarith [hc.k_domain.1])
    (show 0 ≤ m by dsimp [m]; linarith [hc.k_domain.1,hc.k_le_m])
    (show 0≤c by dsimp [c]; linarith [hc.c_domain.1]) hr' hs
    hHG hGA hAB hBT hTD hDE hEH
  refine ⟨i,j,?_⟩
  change min (Concentrated.pure f atG atH r s (delta C.theta B) i j)
    (Concentrated.saturated f atG atH r s (delta C.theta B) i j)≤_ at hendpoint
  dsimp only [Concentrated.p,Concentrated.q,Concentrated.cost,Concentrated.selected] at hendpoint
  dsimp only [Concentrated.scalar,Concentrated.base]
  change baseline k c eta (delta C.theta B)+F k r+F k s+_≤0
  linarith

end Source

theorem row_cover {z : ℝ} (hz : z∈Icc 0 frameCap) :
    ∃f : Row,z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ) := by
  by_cases hl : z≤3/20
  · exact ⟨.low,by simpa [Certificate.left,Certificate.right] using And.intro hz.1 hl⟩
  by_cases hm : z≤1/4
  · exact ⟨.middle,by simp [Certificate.left,Certificate.right]; constructor <;> linarith⟩
  · exact ⟨.high,by simp [Certificate.left,Certificate.right,frameCap] at *; constructor <;> linarith⟩

/-- The four systems with one negative A primary and one negative E primary are impossible with
positive BT3 and a TD0 error of either sign. -/
theorem original {q r s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : Source.aError C atG= -r) (he : Source.eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hz : 0≤delta C.theta B) (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) : False := by
  have hb := Source.budgets hg atG atH 1 1 1 hr.1 hs.1 ha he hvar hz
  obtain ⟨f,hf⟩ := row_cover hb.bt_domain
  obtain ⟨i,j,hij⟩ := Source.concentrated_nonpositive f atG atH
    hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH ha he hA hE hhg hf
    hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (Concentrated.all_positive f atG atH hf hr hs hH hb.total_domain.2 i j)) hij

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3
end
end
end

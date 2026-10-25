module

public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer
public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport
public import SquaresInCircles.Eight.Owners.Sole.NegativeTGrowth
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope

/-!
# Eight squares: the two sole positive E primaries are impossible

At the common radius, with the points, the weak owner of AB and every signed ordinary angle of the
cycle, concavity of the scalar at fixed coordinates comes before the support estimates of the
anchors (`original_false`). The sole-EH family allows either sign of E (`sole_EH_false`); sole-DE
keeps the nonpositive sign of E needed by its axis-work inequality (`sole_DE_false`).
-/

section
/-!
## Endpoint support bounds for the fixed original anchors

Independent norm supports are applied only after the
fixed-coordinate split model has been defined and its concavity proved.
The exact ordinary increment retains all original angles and AB owners.
The E support bound is an explicit scalar argument, proved separately
for the intrinsic split endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleSplitAnchorBounds
open Candidate SignedStress SoleECoefficients SoleOriginalBlocks SoleSplitModel
open SoleSplitSupport SoleResiduals PositiveAngularEnvelope ActualCoreEBlocks

def anchorSupport (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R t x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab 2 0 (deOwner de) (ehOwner de)
      (n b t x) (k b t) (ell b t) (c b t) (c b t)
      (eMultiplier b de t e) (hMultiplier b de e)-
    SoleEStress.halfShift C ab 2 0 (deOwner de) (ehOwner de)
      (n b t x) (k b t) (ell b t) (c b t) (c b t)
      (eMultiplier b de t e) (hMultiplier b de e)

def baseline (b : Band) (de : Bool) (R t x e Z : ℝ) : ℝ :=
  (3/2)*n b t x+2*ell b t+3*c b t+
    (eMultiplier b de t e+hMultiplier b de e)/2+k b t*(edgeWidth x+1/2)+
    eMultiplier b de t e*edgeWidth (if de then e else 0)+
    hMultiplier b de e*edgeWidth (if de then 0 else e)-
    R*SoleEStress.zeroNorms (n b t x) (k b t) (ell b t) (c b t) (c b t)
      (eMultiplier b de t e) (hMultiplier b de e)-
    k b t*sigma R (g b t)*Real.sin x-Z

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (b : Band) (de : Bool) (R t x e : ℝ)
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) :
    anchorWork C ab b de t x e≤anchorSupport C ab b de R t x e := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (forceData C ab b de t x e H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (forceData C ab b de t x e A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (forceData C ab b de t x e B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (forceData C ab b de t x e D)
  have hsum := SoleEStress.sum_bounds C hab (Or.inl rfl) (Or.inl rfl)
    (deOwner_cases de) (ehOwner_cases de) (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e) R
  simp only [SoleEStress.bound,Fin.sum_univ_succ] at hsum
  dsimp [anchorWork,anchorSupport,forceData] at *
  dsimp [SecondaryEStress.signedSupport] at hsum
  linarith

theorem variable_decomposition {C : SignedCycle} {ab : Fin 4} (b : Band) (de : Bool)
    (R t x e Z : ℝ) (hab : ab=0 ∨ ab=2)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    variableDemand C b de t x e-anchorSupport C ab b de R t x e-
      k b t*sigma R (g b t)*Real.sin x-Z=
        baseline b de R t x e Z+SoleOriginalBlocks.increment C ab b de R t x e := by
  have hzero : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  rcases hab with rfl | rfl <;> cases de <;>
    simp only [variableDemand,anchorSupport,baseline,SoleOriginalBlocks.increment,
      SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
      deOwner,ehOwner,ordinaryDE,ordinaryEH,↓reduceIte,Bool.false_eq_true,
      show (1:Fin 4)≠0 by decide,
      show (3:Fin 4)≠2 by decide,show (2:Fin 4)≠0 by decide,
      width_eq (ha H),width_eq (ha A),width_eq (ha B),width_eq (ha T),
      width_eq (ha D),width_eq (ha E),hzero,phi_zero,psi_zero,
      zero_add,add_zero,mul_zero,mul_one] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {R M t x Z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain b) (hx : x∈Icc 0 t)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hZ : eBound C b de R M t (t-x)≤Z) :
    baseline b de R t x (t-x) Z+SoleOriginalBlocks.increment C ab b de R t x (t-x)≤
      SoleSplitModel.value C ab b de R M t x := by
  have hanchor := anchorWork_le b de R t x (t-x) hab hR hc hn
  have hid := variable_decomposition b de R t x (t-x) Z hab ha
  rw [value_eq_stress de R M hab ht hx hn]
  dsimp [stress]
  linarith

end SquaresInCircles.Eight.SoleSplitAnchorBounds
end
end
end

section
/-!
## Exact decomposition of the sole-E endpoint scalars

Each scalar is its zero-angle anchor baseline plus
one negative ordinary charge. The fifth radical is the explicit primary
support. These identities connect the analytic scalar data to the
fixed-coordinate split; they contain no numerical evaluation premise.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarEndpointAlgebra
open Candidate SoleECoefficients SoleResiduals SoleOriginalBlocks SoleEndpointSupport
open PositiveAngularEnvelope SingleAngleConcavity SoleScalarData
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

def lastRadical (s : ScalarCase) (t : ℝ) : ℝ :=
  weightData s t (Real.sin t) 4*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) 4)

def baseAt (s : ScalarCase) (R M t : ℝ) : ℝ :=
  outsideData s R M t (Real.sin t) (Real.cos t) (Real.sin (t/2))-
    nuData s t (Real.sin t) (Real.cos t)*(Real.cos t-1)-
    R*((∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
      (secondData s t (Real.sin t) (Real.cos t) i) 0)+lastRadical s t)

def charge (s : ScalarCase) (R t : ℝ) : ℝ :=
  Vnu R (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
    (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s))
    (nuData s t (Real.sin t) (Real.cos t)) t

theorem row_decomposition (s : ScalarCase) (t : ℝ) :
    rowSum s t (Real.sin t) (Real.cos t)=
      (∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
        (secondData s t (Real.sin t) (Real.cos t) i) 0)+
      pairNorm (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
        (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s)) (-t)-
      pairNorm (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
        (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s)) 0+lastRadical s t := by
  have key : ∀ j : Fin 4,negativeIndex s=j →
      rowSum s t (Real.sin t) (Real.cos t)=
      (∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
        (secondData s t (Real.sin t) (Real.cos t) i) 0)+
      pairNorm (firstData s t (Real.sin t) (Real.cos t) j)
        (secondData s t (Real.sin t) (Real.cos t) j) (-t)-
      pairNorm (firstData s t (Real.sin t) (Real.cos t) j)
        (secondData s t (Real.sin t) (Real.cos t) j) 0+lastRadical s t := by
    intro j hj
    fin_cases j <;>
      simp [rowSum,lastRadical,Fin.sum_univ_succ,weightData,squareData,squaredData,
        hj,pairNorm,Real.sin_neg,sub_eq_add_neg] <;> ring_nf
  exact key _ rfl

theorem value_decomposition (s : ScalarCase) (R M t : ℝ) :
    valueAt s R M t=baseAt s R M t+charge s R t := by
  rw [valueAt,row_decomposition]
  dsimp [baseAt,charge,Vnu]
  ring

def Gbase (b : Band) (R t : ℝ) : ℝ :=
  3+2*ell b t+3*c b t+k b t*(1+2*Real.cos t+(1+2*g b t)*Real.sin t)-
    R*(pairNorm 1 (n b t t) 0+pairNorm (k b t) (ell b t) 0+
      pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0+
      k b t*Real.sin t*Real.sqrt (1+(g b t)^2))

def Ebase (b : Band) (de : Bool) (R M t : ℝ) : ℝ :=
  if b=.high then
    3+Real.sin t-2*R*Real.sin (t/2)+3*k b t+2*ell b t+3*c b t-
      R*(pairNorm 1 (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0)
  else if de then
    3*k b t+2*ell b t+3*c b t+1+Real.cos t/2+
      (1/2-M)*Real.sin t+(3/2)*r b t-
      R*(pairNorm (r b t) (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0)
  else
    3*k b t+2*ell b t+3*c b t+1+2*Real.cos t+(1+2*eta b t)*Real.sin t-
      R*(pairNorm 1 (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm (p b t t) (c b t) 0+
        Real.sin t*Real.sqrt (1+(eta b t)^2))

theorem base_at_G (s : ScalarCase) (R M t : ℝ) (hs : atG s=true) :
    baseAt s R M t=Gbase (band s) R t := by
  cases s <;>
    simp_all [atG,band,baseAt,Gbase,outsideData,firstData,secondData,lastRadical,
      Fin.sum_univ_succ,weightData,squareData,nData,n,SecondaryEStress.tiltedWeight,
      pairNorm_zero] <;> ring_nf <;> simp

theorem base_at_E (s : ScalarCase) (R M t : ℝ) (hs : atG s=false) :
    baseAt s R M t=Ebase (band s) (isDE s) R M t := by
  cases s <;>
    simp_all [atG,isDE,band,baseAt,Ebase,outsideData,firstData,secondData,lastRadical,
      Fin.sum_univ_succ,weightData,squareData,pData,rData,p,r,pairNorm_zero] <;> ring_nf <;> simp

theorem baseline_at_G {b : Band} (de : Bool) (R t : ℝ) (ht : t∈domain b) :
    SoleSplitAnchorBounds.baseline b de R t t 0 0=Gbase b R t := by
  have hs := (transport_trig (angle ht)).2.2.1
  have hc := (transport_trig (angle ht)).1
  have hc0 : 0≤Real.cos t := by linarith
  cases b <;> cases de <;>
    simp [SoleSplitAnchorBounds.baseline,Gbase,eMultiplier,hMultiplier,
      SoleEStress.zeroNorms,n,SecondaryEStress.tiltedWeight,p,r,sigma,
      edgeWidth,pairWidth,abs_of_nonneg hs,abs_of_nonneg hc0] <;> ring

theorem baseline_at_E {b : Band} (de : Bool) (R M t : ℝ) (ht : t∈domain b) :
    SoleSplitAnchorBounds.baseline b de R t 0 t (endpointWork b de R M t)=Ebase b de R M t := by
  have hs := (transport_trig (angle ht)).2.2.1
  have hc := (transport_trig (angle ht)).1
  have hc0 : 0≤Real.cos t := by linarith
  cases b <;> cases de <;>
    simp [SoleSplitAnchorBounds.baseline,Ebase,endpointWork,highWork,eMultiplier,hMultiplier,
      SoleEStress.zeroNorms,n,SecondaryEStress.tiltedWeight,p,r,sigma,
      edgeWidth,pairWidth,abs_of_nonneg hs,abs_of_nonneg hc0] <;> ring

end SquaresInCircles.Eight.SoleScalarEndpointAlgebra
end
end
end

section
/-!
## The endpoint scalar charges dominate the original ordinary minima

H, A, B, D retain their actual single-angle or
two-angle status. The only deliberately stronger scalar coefficient is
the high sole-DE H coefficient 1.06; its direction follows from the
nonpositive factor cos(t)-1. All min/max comparisons are proved here
from the coefficient families on their complete domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleEndpointCharges
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
  cases b <;> simp [Gcase,band]
  split_ifs <;> rfl
theorem Ecase_band (b : Band) (de : Bool) (i : Fin 4) : band (Ecase b de i)=b := by
  cases b <;> cases de <;> rfl
theorem Gcase_atG (b : Band) (de : Bool) (i : Fin 4) : atG (Gcase b de i)=true := by
  cases b <;> simp [Gcase,atG]
  split_ifs <;> rfl
theorem Ecase_atG (b : Band) (de : Bool) (i : Fin 4) : atG (Ecase b de i)=false := by
  cases b <;> cases de <;> rfl

theorem Gcase_index {b : Band} (de : Bool) {i : Fin 4} (hi : b=.low → i=2) :
    negativeIndex (Gcase b de i)=i := by
  cases b
  · simpa [Gcase,negativeIndex] using (hi rfl).symm
  · rfl
  · by_cases hh : de=true ∧ i=0
    · simp [Gcase,hh,negativeIndex]
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
    simp_all [single,nu,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta]

theorem pure_eq {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) (R u : ℝ) (i : Fin 4) :
    pure (single de i) R (small b de t x e i) (large b de t x e i) (nu b de t x e i) u=
      Vnu R (SoleOrdinaryData.alpha b de t x e i) (SoleOrdinaryData.beta b t x i) (nu b de t x e i) u := by
  have hnorm (v : ℝ) := norm_min_max (SoleOrdinaryData.alpha b de t x e i)
    (SoleOrdinaryData.beta b t x i) v
  by_cases hi : single de i=true
  · simp only [SingleAngleConcavity.pure,hi,↓reduceIte,Vnu,small,large,hnorm]
  · have hi' : single de i=false := Bool.eq_false_of_not_eq_true hi
    rw [non_single_nu ht i hi']
    simp only [SingleAngleConcavity.pure,hi',Bool.false_eq_true,↓reduceIte,←Vnu_larger,Vnu,
      small,large,hnorm]

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
      pairNorm (SoleOrdinaryData.alpha b de t t 0 i) (SoleOrdinaryData.beta b t t i) u := by
  rw [Gcase_index de hi]
  cases b <;> cases de <;> fin_cases i <;>
    simp_all [Gcase,firstData,secondData,band,atG,nData,n,
      SecondaryEStress.tiltedWeight,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,r,p,pairNorm_symm]

theorem E_norm {b : Band} (de : Bool) {t : ℝ} {i : Fin 4}
    (hi : b=.low → i=2) (u : ℝ) :
    pairNorm (firstData (Ecase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Ecase b de i)))
      (secondData (Ecase b de i) t (Real.sin t) (Real.cos t) (negativeIndex (Ecase b de i))) u=
      pairNorm (SoleOrdinaryData.alpha b de t 0 t i) (SoleOrdinaryData.beta b t 0 i) u := by
  rw [Ecase_index de hi]
  cases b <;> cases de <;> fin_cases i <;>
    simp_all [Ecase,firstData,secondData,band,atG,isDE,pData,rData,n,
      SecondaryEStress.tiltedWeight,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,p,r,pairNorm_symm]

theorem G_nu_le {b : Band} (de : Bool) {t : ℝ} (ht : t∈domain b)
    {i : Fin 4} (hi : b=.low → i=2) :
    nu b de t t 0 i≤nuData (Gcase b de i) t (Real.sin t) (Real.cos t) := by
  cases b
  · have hii := hi rfl
    subst i
    cases de <;> simp [Gcase,nu,nuData,band,atG,negativeIndex]
  · have hn := middle_G_n_ge_one ht
    have hc : (1:ℝ)≤c .middle t := by linarith [(middle_bounds ht).2.2.1]
    cases de <;> fin_cases i <;>
      simp [Gcase,nu,nuData,band,atG,negativeIndex,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,r,p,
        nData,show k .middle t*(Real.cos t+g .middle t*Real.sin t)=n .middle t t by rfl,
        max_eq_right hn,max_eq_right hc]
  · have hn := (high_n ht ⟨(angle ht).1,le_rfl⟩).2.le
    have hmax : max (1:ℝ) (n .high t t)≤53/50 := max_le (by norm_num) hn
    have hc : (1:ℝ)≤c .high t := by norm_num [c]
    cases de <;> fin_cases i <;>
      simp [Gcase,nu,nuData,band,atG,negativeIndex,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,r,p,
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
      simp [Ecase,nu,nuData,band,atG,isDE,negativeIndex,large,SoleOrdinaryData.alpha,
        SoleOrdinaryData.beta,n,SecondaryEStress.tiltedWeight,rData,
        max_eq_left hkr,max_eq_right hc,max_eq_right hpc.le]
    simp [r]
  · have hk : (1:ℝ)≤k .high t := by linarith [(high_bounds ht).1]
    have hc : (1:ℝ)≤c .high t := by norm_num [c]
    cases de <;> fin_cases i <;>
      simp [Ecase,nu,nuData,band,atG,isDE,negativeIndex,large,SoleOrdinaryData.alpha,
        SoleOrdinaryData.beta,n,SecondaryEStress.tiltedWeight,p,r,max_eq_right hk,
        max_eq_right hc]

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

end SquaresInCircles.Eight.SoleEndpointCharges
end
end
end

section
/-!
## Positive-mass transfer for the sole-E endpoint polynomials

Each of the five masses is proved positive on the
entire relevant coefficient interval. Multiplying the elementary
square-root majorants by those masses gives exactly the stored
polynomial expression. No fitted approximation or sampled assertion
is a premise of the transfer.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarRadicals
open Polynomial SoleScalarPolynomials SoleECoefficients HighOrderTaylor

def radicalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*Real.sqrt (aeval z (rowSquare s i))

def rationalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*
    (aeval z (rowSquare s i)+(aeval z (massAt s i))^2)/(2*aeval z (massAt s i))

private theorem five_mass_identity (a v w : Fin 5 → ℝ) (ha : ∀i,a i≠0) :
    (∑i : Fin 5,w i*(v i+(a i)^2)*∏j : Fin 5,if j=i then 1 else a j)=
      2*(∏i : Fin 5,a i)*(∑i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    aeval z (certificate s)=
      2*(∏i : Fin 5,aeval z (massAt s i))*
        (aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z) := by
  have ha : ∀i : Fin 5,aeval z (massAt s i)≠0 := by
    intro i
    have hi := (mass_bounds s i hz).1
    linarith
  have hid := five_mass_identity (fun i => aeval z (massAt s i))
    (fun i => aeval z (rowSquare s i)) (fun i => aeval z (rowWeight s i)) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_ofNat,map_sum,map_add,
    map_pow,map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem rational_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    0<aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z := by
  have hp := certificate_positive s hz
  rw [certificate_factorization s hz] at hp
  have hM : 0<∏i : Fin 5,aeval z (massAt s i) := by
    apply Finset.prod_pos
    intro i _
    have hh := (mass_bounds s i hz).1
    linarith
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hM)).mp hp

theorem radical_le_rational (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    radicalSum s z≤rationalSum s z := by
  apply Finset.sum_le_sum
  intro i _
  have hm : 0<aeval z (massAt s i) := by
    have hh := (mass_bounds s i hz).1
    linarith
  have hv : 0≤aeval z (rowSquare s i) := by
    have hh := (square_bounds s i hz).1
    linarith
  have h := mul_le_mul_of_nonneg_left
    (ScalarRadicalTransfer.sqrt_le_mass_majorant hv hm) (hw i)
  simpa only [mul_div_assoc] using h

theorem radical_reserve (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    (margin:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*radicalSum s z := by
  have hp := rational_positive s hz
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational s hz hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem taylor_weights (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    ∀i : Fin 5,0≤aeval (t-(origin (band s):ℝ)) (rowWeight s i) := by
  have hd := angle ht
  have hs : S15 t∈Set.Icc 0 1 :=
    ⟨S15_nonneg hd,(S15_le_sin hd.1).trans (Real.sin_le_one t)⟩
  intro i
  rw [(SoleScalarData.polynomial_rows s i t).2]
  exact (SoleScalarData.weight_bounds s ht hs i).1

theorem polynomial_radicalSum (s : ScalarCase) (t : ℝ) :
    radicalSum s (t-(origin (band s):ℝ))=SoleScalarData.taylorSum s t := by
  unfold radicalSum SoleScalarData.taylorSum SoleScalarData.rowSum
  apply Finset.sum_congr rfl
  intro i _
  rw [(SoleScalarData.polynomial_rows s i t).1,
    (SoleScalarData.polynomial_rows s i t).2]

theorem taylor_reserve (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    (margin:ℝ)<SoleScalarData.taylorOutside s t-
      (radiusUpper:ℝ)*SoleScalarData.taylorSum s t := by
  have hp := radical_reserve s (local_parameter ht) (taylor_weights s ht)
  simpa only [SoleScalarData.polynomial_outside,polynomial_radicalSum] using hp

end SquaresInCircles.Eight.SoleScalarRadicals
end
end
end

section
/-!
## Strict trigonometric sole-E endpoint inequalities

The five radical rows lose at most 2500 Taylor
remainders, and the outside term loses at most 100. The rational
radius is below two, so the total error is below the explicit 10^-8
allowance in the polynomial certificates. The resulting inequalities
also hold at every smaller actual radius and its actual axis coordinate.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarTransfer
open SoleECoefficients SoleScalarData SoleScalarTaylor HighOrderTaylor
open BoundedRadicalPerturbation
open SoleScalarPolynomials (ScalarCase band radiusUpper axisUpper margin)

theorem outside_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    taylorOutside s t-100*remainder≤
      outsideData s (radiusUpper:ℝ) (axisUpper:ℝ) t
        (Real.sin t) (Real.cos t) (Real.sin (t/2)) := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,heta,heta1⟩
  rcases input_bounds (angle ht) with ⟨hs,hco,hs',hco'⟩
  rcases input_errors (angle ht) with ⟨hse,hce,hhe⟩
  have he0 : 0≤remainder := by norm_num [remainder]
  have hnu := nu_bounds s ht hs hco
  have hN := product_difference
    (show |nuData s t (Real.sin t) (Real.cos t)|≤2 by
      rw [abs_of_nonneg hnu.1]; exact hnu.2)
    (show |C16 t-1|≤1 by apply abs_le.mpr; constructor <;> linarith [hco'.1,hco'.2])
    (nu_error s ht)
    (show |(Real.cos t-1)-(C16 t-1)|≤remainder by simpa using hce)
  have hN' := abs_le.mp hN
  have hkg0 : 0≤k (band s) t*(1+2*g (band s) t) := mul_nonneg hk.le (by linarith)
  have hkg : k (band s) t*(1+2*g (band s) t)≤2 := by
    have hm := mul_le_mul_of_nonneg_left
      (show 1+2*g (band s) t≤17/10 by linarith) hk.le
    linarith
  have hG := linear_difference
    (show |2*k (band s) t|≤3 by rw [abs_of_nonneg (by linarith)]; linarith)
    (show |k (band s) t*(1+2*g (band s) t)|≤2 by
      rw [abs_of_nonneg hkg0]; exact hkg) hce hse
  have hG' := abs_le.mp hG
  have hE := linear_difference (by norm_num : |(2:ℝ)|≤2)
    (show |1+2*eta (band s) t|≤2 by
      rw [abs_of_nonneg (by linarith)]; linarith) hce hse
  have hE' := abs_le.mp hE
  have hD := linear_difference (by norm_num : |(1/2:ℝ)|≤1/2)
    (by norm_num [axisUpper] : |(1/2:ℝ)-(axisUpper:ℝ)|≤1) hce hse
  have hD' := abs_le.mp hD
  have hr := tilted_error (angle ht) (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  simp only [one_mul] at hr
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  have hDr := constant_product_difference (by norm_num : |(3/2:ℝ)|≤3/2) hr
  have hDr' := abs_le.mp hDr
  have hH := linear_difference (by norm_num : |(1:ℝ)|≤1)
    (by norm_num [radiusUpper] : |(-2:ℝ)*(radiusUpper:ℝ)|≤4) hse hhe
  have hH' := abs_le.mp hH
  dsimp only [taylorOutside,outsideData]
  split_ifs
  · linarith only [hN'.1,hG'.1,he0]
  · linarith only [hN'.1,hD'.1,hDr'.1,he0]
  · linarith only [hN'.1,hH'.1,he0]
  · linarith only [hN'.1,hE'.1,he0]

theorem conservative_positive (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0<valueAt s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  have hp := SoleScalarRadicals.taylor_reserve s ht
  have hd := outside_error s ht
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2
    (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<(margin:ℝ) := by norm_num [remainder,margin]
  unfold valueAt
  nlinarith

theorem rowSum_nonneg (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0≤rowSum s t (Real.sin t) (Real.cos t) := by
  have hs := (input_bounds (angle ht)).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds s ht hs i).1 (Real.sqrt_nonneg _)

theorem outside_antitone_parameters (s : ScalarCase) {R R' M M' t : ℝ}
    (ht : t∈domain (band s)) (hR : R≤R') (hM : M≤M') :
    outsideData s R' M' t (Real.sin t) (Real.cos t) (Real.sin (t/2))≤
      outsideData s R M t (Real.sin t) (Real.cos t) (Real.sin (t/2)) := by
  have hd := angle ht
  have hs := (input_bounds hd).1.1
  have h1 := hd.1
  have h2 := hd.2
  norm_num [frameCap] at h2
  have hh : t/2∈Set.Icc 0 frameCap :=
    ⟨by linarith,by norm_num [frameCap]; linarith⟩
  have hsh := (input_bounds hh).1.1
  have hRp := mul_nonneg (sub_nonneg.mpr hR) hsh
  have hMp := mul_nonneg (sub_nonneg.mpr hM) hs
  dsimp only [outsideData]
  split_ifs <;> linarith

theorem valueAt_positive (s : ScalarCase) {R M t : ℝ}
    (ht : t∈domain (band s))
    (hR : R≤(radiusUpper:ℝ)) (hM : M≤(axisUpper:ℝ)) :
    0<valueAt s R M t := by
  have hp := conservative_positive s ht
  have ho := outside_antitone_parameters s ht hR hM
  have hs := mul_le_mul_of_nonneg_right hR (rowSum_nonneg s ht)
  unfold valueAt at *
  linarith

/-- The estimates use the actual common radius and its actual axis
coordinate. Only the scalar support comparison uses the rational ceiling. -/
theorem actual_radius_positive (s : ScalarCase) {q t : ℝ}
    (ht : t∈domain (band s)) (hq : q≤qTrial) :
    0<valueAt s (Real.sqrt q) (axisCoordinate q) t := by
  apply valueAt_positive s ht
  · exact (Real.sqrt_le_sqrt hq).trans SoleScalarPolynomials.radius_upper.le
  · have hm := Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))
    have hu := SoleScalarPolynomials.axis_upper
    dsimp [axisCoordinate] at *
    linarith

end SquaresInCircles.Eight.SoleScalarTransfer
end
end
end

section
/-!
## Strict positivity at both intrinsic sole-E endpoints

The concrete scalar estimates are combined with the
original ordinary signed-angle budgets. The low interval uses B alone;
the middle and high intervals use the minimum of the four actual pure
charges. Every scalar is evaluated at the actual common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleEndpointPositive
open Candidate SoleECoefficients SoleOrdinaryData SoleOriginalBlocks
open SoleEndpointSupport SoleScalarEndpointAlgebra SoleEndpointCharges
open SingleAngleConcavity SoleBalancedEnvelope
open SoleScalarPolynomials (band atG isDE)

theorem G_pure_positive {b : Band} (de : Bool) {q t : ℝ}
    (ht : t∈domain b) (hq : q≤qTrial) {i : Fin 4} (hi : b=.low → i=2) :
    0<Gbase b (Real.sqrt q) t+
      pure (single de i) (Real.sqrt q) (small b de t t 0 i)
        (large b de t t 0 i) (nu b de t t 0 i) t := by
  have hp := SoleScalarTransfer.actual_radius_positive (Gcase b de i)
    (by simpa only [Gcase_band] using ht) hq
  rw [value_decomposition,base_at_G _ _ _ _ (Gcase_atG b de i),Gcase_band] at hp
  exact lt_of_lt_of_le hp (by linarith [G_charge_le de ht (Real.sqrt q) hi])

theorem E_pure_positive {b : Band} (de : Bool) {q t : ℝ}
    (ht : t∈domain b) (hq : q≤qTrial) {i : Fin 4} (hi : b=.low → i=2) :
    0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+
      pure (single de i) (Real.sqrt q) (small b de t 0 t i)
        (large b de t 0 t i) (nu b de t 0 t i) t := by
  have hp := SoleScalarTransfer.actual_radius_positive (Ecase b de i)
    (by simpa only [Ecase_band] using ht) hq
  have hb : Ebase b (isDE (Ecase b de i)) (Real.sqrt q) (axisCoordinate q) t=
      Ebase b de (Real.sqrt q) (axisCoordinate q) t := by
    cases b <;> cases de <;> simp [Ecase,isDE,Ebase]
  rw [value_decomposition,base_at_E _ _ _ _ (Ecase_atG b de i),Ecase_band,hb] at hp
  exact lt_of_lt_of_le hp (by linarith [E_charge_le de ht (Real.sqrt q) hi])

theorem B_pure {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) (R : ℝ) :
    pure (single de 2) R (small b de t x e 2) (large b de t x e 2)
      (nu b de t x e 2) t=OrdinaryAngleConcavity.V R (ell b t) (c b t) t := by
  rcases B_data (de := de) (x := x) (e := e) ht with ⟨hp,hq,-⟩
  simp [single,SingleAngleConcavity.pure,hp,hq]

theorem G_original_positive {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<Gbase b (Real.sqrt q) t+increment C ab b de (Real.sqrt q) t t 0 := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hxt : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  have he0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  by_cases hb : b=.low
  · subst b
    have hinc := low_original_increment hab hR (by simpa only [hR2] using hQL)
      (by simpa only [hR2] using hcap) ht hxt he0 ha hvar hG hE htotal
    have hp := G_pure_positive de ht hQU (i := 2) (by intro _; rfl)
    rw [B_pure ht] at hp
    linarith
  · let f : Fin 4 → ℝ := fun i => pure (single de i) (Real.sqrt q)
      (small b de t t 0 i) (large b de t t 0 i) (nu b de t t 0 i) t
    have hinc := balanced_original_increment hb hab hR
      (by simpa only [hR2] using hQL) (by simpa only [hR2] using hcap)
      ht hxt he0 ha hvar hG hE htotal (minimumFour_le f)
    have hp : 0<Gbase b (Real.sqrt q) t+minimumFour f :=
      minimumFour_positive (fun i => G_pure_positive de ht hQU (i := i)
        (fun hh => (hb hh).elim))
    linarith

theorem E_original_positive {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+
      increment C ab b de (Real.sqrt q) t 0 t := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hx0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  have het : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  by_cases hb : b=.low
  · subst b
    have hinc := low_original_increment hab hR (by simpa only [hR2] using hQL)
      (by simpa only [hR2] using hcap) ht hx0 het ha hvar hG hE htotal
    have hp := E_pure_positive de ht hQU (i := 2) (by intro _; rfl)
    rw [B_pure ht] at hp
    linarith
  · let f : Fin 4 → ℝ := fun i => pure (single de i) (Real.sqrt q)
      (small b de t 0 t i) (large b de t 0 t i) (nu b de t 0 t i) t
    have hinc := balanced_original_increment hb hab hR
      (by simpa only [hR2] using hQL) (by simpa only [hR2] using hcap)
      ht hx0 het ha hvar hG hE htotal (minimumFour_le f)
    have hp : 0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+minimumFour f :=
      minimumFour_positive (fun i => E_pure_positive de ht hQU (i := i)
        (fun hh => (hb hh).elim))
    linarith

theorem fixed_endpoints {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<SoleSplitModel.value C ab b de (Real.sqrt q) (axisCoordinate q) t 0 ∧
      0<SoleSplitModel.value C ab b de (Real.sqrt q) (axisCoordinate q) t t := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by
    simpa only [hR2] using hC.contained
  have hx0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  have hxt : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  have hEbound := SoleSplitAnchorBounds.value_lower de hab (Real.sqrt_nonneg q) ht hx0 hc hn ha
    (Z := endpointWork b de (Real.sqrt q) (axisCoordinate q) t)
    (by simpa only [sub_zero] using at_E de hQL ht (hC.sorted E) (hC.contained E))
  have hGbound := SoleSplitAnchorBounds.value_lower de hab (Real.sqrt_nonneg q) ht hxt hc hn ha
    (M := axisCoordinate q) (Z := 0)
    (by simp only [sub_self,at_G,le_refl])
  simp only [sub_zero,baseline_at_E de _ _ _ ht] at hEbound
  simp only [sub_self,baseline_at_G de _ _ ht] at hGbound
  exact ⟨(E_original_positive de hab hQL hQU ht ha hvar hG hE htotal).trans_le hEbound,
    (G_original_positive de hab hQL hQU ht ha hvar hG hE htotal).trans_le hGbound⟩

end SquaresInCircles.Eight.SoleEndpointPositive
end
end
end

section
/-!
## The ordinary minorants after a negative T primary

H and A keep their pair charges. A BT3 row changes only the positive B pair, and its negative
charge is bounded by the unchanged B charge. In the EH rows the D block has the clipped support as
positive branch and the smaller of the unchanged D and A charges as negative one. In a sole-DE row
D has no ordinary angle; its zero block uses the functions of A only to keep one finite index
type. These blocks form concave block data (`data`) with their minorants (`positive_lower`,
`negative_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTOrdinaryData
open SoleTScalarModel SoleNegativeTCoefficients PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryAngleConcentration SingleAngleConcavity
open ActualOrdinaryBlocks SoleNegativeTGrowth

def shortDomain (td : Bool) : Set ℝ := if td then Icc 0 (3/10) else Icc 0 (9/100)
def dCoefficient (f : Family) (td : Bool) (t s : ℝ) : ℝ :=
  SoleNegativeTSplit.tdWeight f td t s
def Used (f : Family) (i : Fin 4) : Prop := isDE f=false ∨ i≠3

def positive (f : Family) (atG td : Bool) (R t s v : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then
    if isDE f then U R (small f atG t 1) (large f atG t 1) v
    else if p (face f atG) t 0≤dCoefficient f td t s then
      -(2/5)*p (face f atG) t 0*v
    else U R (dCoefficient f td t s) (p (face f atG) t 0) v
  else if i=2 ∧ td=false then U R (ell f t 0) (c f t 0/Real.cos s) v
  else U R (small f atG t i) (large f atG t i) v

def negative (f : Family) (atG : Bool) (R t v : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then
    if isDE f then oldV f atG R t v 1
    else min (oldV f atG R t v 3) (oldV f atG R t v 1)
  else oldV f atG R t v i

def block (f : Family) (atG td : Bool) (R t s P N : ℝ) (i : Fin 4) : ℝ :=
  if single f td i then positive f atG td R t s P i+negative f atG R t N i
  else mixedBlock R (small f atG t i) (large f atG t i) P N

theorem short_small {td : Bool} {s : ℝ} (hs : s∈shortDomain td) : s∈Icc 0 frameCap := by
  cases td <;> norm_num [shortDomain,frameCap] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩

theorem d_coefficient_ge {f : Family} (td : Bool) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈shortDomain td) : c f t 0≤dCoefficient f td t s := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hsec := SoleNegativeTSplit.secant_nonneg (short_small hs)
  cases td
  · exact le_rfl
  · have hh := mul_nonneg hc.le hsec.2
    have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
    dsimp [dCoefficient,SoleNegativeTSplit.tdWeight]
    rw [he]
    linarith

theorem mixed_indices {f : Family} {td : Bool} {i : Fin 4} (hi : single f td i=false) :
    (i=0 ∧ isDE f=true) ∨ (i=2 ∧ td=true) := by
  fin_cases i <;> cases hf : isDE f <;> cases ht : td <;>
    simp_all [single]

theorem mixed_nu {f : Family} (atG : Bool) {td : Bool} {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) (hi : single f td i=false) :
    nu f atG t i=large f atG t i := by
  have hpr := pairs f atG t
  rcases mixed_indices hi with ⟨rfl,hf⟩ | ⟨rfl,htd⟩
  · have hh := old_cap atG ht 0
    have hlam : lambda f=5/4 := by simp [lambda,hf]
    have hcap : (SolePositiveTCoefficients.cap f:ℝ)=5/4 := by
      cases f <;> simp_all [isDE,SolePositiveTCoefficients.cap]
    have hlarge : large f atG t 0=max (lambda f) (n (face f atG) t 0) := by
      simp only [large,hpr.1,hpr.2]
      rfl
    have hnu : SoleNegativeTCoefficients.nu f atG t 0=lambda f := by
      simp [SoleNegativeTCoefficients.nu,hf]
    rw [hlarge] at hh ⊢
    rw [hnu]
    rw [hcap,← hlam] at hh
    exact (le_antisymm hh (le_max_left _ _)).symm
  · have he := c_ge_ell atG ht
    have hlarge : large f atG t 2=max (ell f t 0) (c f t 0) := by
      simp only [large,hpr.1,hpr.2]
      rfl
    rw [hlarge,max_eq_right he]
    rfl

theorem positive_mixed {f : Family} (atG : Bool) {td : Bool} (R t s v : ℝ)
    (i : Fin 4) (hi : single f td i=false) :
    positive f atG td R t s v i=U R (small f atG t i) (large f atG t i) v := by
  rcases mixed_indices hi with ⟨rfl,hf⟩ | ⟨rfl,rfl⟩ <;> simp [positive]

theorem negative_mixed {f : Family} (atG : Bool) {td : Bool} (R : ℝ) {t : ℝ}
    (ht : t∈domain f) (v : ℝ) (i : Fin 4) (hi : single f td i=false) :
    negative f atG R t v i=V R (small f atG t i) (large f atG t i) v := by
  have hne : i≠3 := by rcases mixed_indices hi with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  rw [negative,ite_eq_right hne,oldV,mixed_nu atG ht i hi,Vnu_larger]

@[simp] theorem positive_zero (f : Family) (atG td : Bool) (R t s : ℝ) (i : Fin 4) :
    positive f atG td R t s 0 i=0 := by
  unfold positive
  split_ifs <;> simp

@[simp] theorem negative_zero (f : Family) (atG : Bool) (R t : ℝ) (i : Fin 4) :
    negative f atG R t 0 i=0 := by
  unfold negative
  split_ifs <;> simp [SoleNegativeTGrowth.zero]

theorem block_left {f : Family} (atG td : Bool) (R : ℝ) {t : ℝ}
    (ht : t∈domain f) (s N : ℝ) (i : Fin 4) :
    block f atG td R t s 0 N i=negative f atG R t N i := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    rw [mixedBlock_zero_left,negative_mixed atG R ht N i hi]
  · simp [block,hi]

theorem block_right {f : Family} (atG td : Bool) (R t s P : ℝ) (i : Fin 4) :
    block f atG td R t s P 0 i=positive f atG td R t s P i := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    rw [mixedBlock_zero_right,positive_mixed atG R t s P i hi]
  · simp [block,hi]

theorem affine_concave (a : ℝ) : ConcaveOn ℝ (Icc 0 frameCap) (fun x : ℝ => a*x) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  ring_nf
  rfl

private lemma r63_concave_add_const {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc 0 frameCap) g) (C : ℝ) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => g x+C) := by
  refine ⟨hg.1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 hx hy ha hb hab
  have h2 : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul] at h ⊢
  linarith

private lemma r63_concave_const_add {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc 0 frameCap) g) (C : ℝ) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => C+g x) := by
  refine ⟨hg.1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 hx hy ha hb hab
  have h2 : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul] at h ⊢
  linarith

theorem minimum_concave {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 frameCap) f) (hg : ConcaveOn ℝ (Icc 0 frameCap) g) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => min (f x) (g x)) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hfx := mul_le_mul_of_nonneg_left (min_le_left (f x) (g x)) hu
  have hfy := mul_le_mul_of_nonneg_left (min_le_left (f y) (g y)) hv
  have hgx := mul_le_mul_of_nonneg_left (min_le_right (f x) (g x)) hu
  have hgy := mul_le_mul_of_nonneg_left (min_le_right (f y) (g y)) hv
  have hf' := hf.2 hx hy hu hv huv
  have hg' := hg.2 hx hy hu hv huv
  simp only [smul_eq_mul] at hf' hg' ⊢
  exact le_min (by linarith) (by linarith)

theorem positive_concave {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => positive f atG td R t s v i) := by
  have hbase (j : Fin 4) : ConcaveOn ℝ (Icc 0 frameCap)
      (U R (small f atG t j) (large f atG t j)) :=
    U_concave hR hQ (SoleNegativeTCoefficients.positive atG ht j).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht j)
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simpa [positive,hde] using hbase 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      by_cases hdiag : p (face f atG) t 0≤dCoefficient f td t s
      · simpa [positive,hde',hdiag,mul_assoc] using
          affine_concave (-(2/5)*p (face f atG) t 0)
      · have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
        have hcg := d_coefficient_ge td ht hs
        have hp2 := p_half_c atG ht
        have hg : 0<dCoefficient f td t s := hc.trans_le hcg
        simpa [positive,hde',hdiag] using
          U_concave hR hQ hg (lt_of_not_ge hdiag).le (by linarith : p (face f atG) t 0≤2*dCoefficient f td t s)
  · by_cases hB : i=2 ∧ td=false
    · have hsBT : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain,hB.2] using hs
      have hb := changed_B_domain atG ht hsBT
      simpa [positive,hD,hB] using U_concave hR hQ hb.1 hb.2.1 hb.2.2
    · simpa [positive,hD,hB] using hbase i

theorem negative_concave {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => negative f atG R t v i) := by
  by_cases hD : i=3
  · by_cases hde : isDE f=true
    · simpa [negative,hD,hde] using old_concave atG hR hQ ht 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simpa [negative,hD,hde'] using minimum_concave
        (old_concave atG hR hQ ht 3) (old_concave atG hR hQ ht 1)
  · simpa [negative,hD] using old_concave atG hR hQ ht i

theorem block_concave_P {f : Family} (atG td : Bool) {R t s N : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hN : N∈Icc 0 frameCap) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => block f atG td R t s P N i) := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    exact mixedBlock_concave_positive hR hQ
      (SoleNegativeTCoefficients.positive atG ht i).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht i) hN
  · simp only [block,hi,↓reduceIte]
    exact r63_concave_add_const (positive_concave atG td hR hQ ht hs i)
      (negative f atG R t N i)

theorem block_concave_N {f : Family} (atG td : Bool) {R t s P : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (_hs : s∈shortDomain td)
    (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun N => block f atG td R t s P N i) := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    exact mixedBlock_concave_negative hR hQ
      (SoleNegativeTCoefficients.positive atG ht i).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht i) hP
  · simp only [block,hi,↓reduceIte]
    exact r63_concave_const_add (negative_concave atG hR hQ ht i)
      (positive f atG td R t s P i)

def data {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td) :
    OccupiedSignedConcentration.Data (Fin 4) where
  U i v := positive f atG td R t s v i
  V i v := negative f atG R t v i
  F i P N := block f atG td R t s P N i
  single := single f td
  U_zero := positive_zero f atG td R t s
  V_zero := negative_zero f atG R t
  F_left := fun i N => block_left atG td R ht s N i
  F_right := fun i P => block_right atG td R t s P i
  U_concave := positive_concave atG td hR hQ ht hs
  V_concave := negative_concave atG hR hQ ht
  F_concave_P := fun i _ hN => block_concave_P atG td hR hQ ht hs hN i
  F_concave_N := fun i _ hP => block_concave_N atG td hR hQ ht hs hP i

theorem positive_lower {f : Family} (atG td : Bool) {R t s v : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    -gamma f*v≤positive f atG td R t s v i := by
  have hbase (j : Fin 4) : -gamma f*v≤U R (small f atG t j) (large f atG t j) v := by
    have hU : -(109/200)*large f atG t j*v≤U R (small f atG t j) (large f atG t j) v :=
      OrdinaryPositiveEnvelope.U_lower hR hQ
        (SoleNegativeTCoefficients.positive atG ht j).2.2 min_le_max
        (SoleNegativeTCoefficients.half_ratio atG ht j) hv
    have hc := mul_le_mul_of_nonneg_right (old_cost atG ht j) hv.1
    linarith
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simpa [positive,hde] using hbase 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      by_cases hdiag : p (face f atG) t 0≤dCoefficient f td t s
      · have hm := mul_le_mul_of_nonneg_right (D_linear_cost atG ht) hv.1
        simp only [positive,↓reduceIte,hde',Bool.false_eq_true,hdiag]
        linarith
      · have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
        have hcg := d_coefficient_ge td ht hs
        have hp2 := p_half_c atG ht
        have hU : -(109/200)*p (face f atG) t 0*v≤
            U R (dCoefficient f td t s) (p (face f atG) t 0) v :=
          OrdinaryPositiveEnvelope.U_lower hR hQ (hc.trans_le hcg)
            (lt_of_not_ge hdiag).le (by linarith : p (face f atG) t 0≤2*dCoefficient f td t s) hv
        have hm := mul_le_mul_of_nonneg_right (D_full_cost atG ht) hv.1
        simp only [positive,↓reduceIte,hde',Bool.false_eq_true,hdiag]
        linarith
  · by_cases hB : i=2 ∧ td=false
    · have hsBT : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain,hB.2] using hs
      have hb := changed_B_domain atG ht hsBT
      have hU : -(109/200)*(c f t 0/Real.cos s)*v≤
          U R (ell f t 0) (c f t 0/Real.cos s) v :=
        OrdinaryPositiveEnvelope.U_lower hR hQ hb.1 hb.2.1 hb.2.2 hv
      have hm := mul_le_mul_of_nonneg_right (changed_B_cost ht hsBT) hv.1
      obtain ⟨rfl,rfl⟩ := hB
      have hpos : positive f atG false R t s v 2=U R (ell f t 0) (c f t 0/Real.cos s) v := by
        simp [positive]
      rw [hpos]
      linarith
    · simpa [positive,hD,hB] using hbase i

theorem negative_lower {f : Family} (atG : Bool) {R t v L : ℝ}
    (hV : ∀ i,Used f i → L≤oldV f atG R t v i) (i : Fin 4) :
    L≤negative f atG R t v i := by
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simp only [negative,↓reduceIte,hde]
      exact hV 1 (Or.inr (by decide))
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simp only [negative,↓reduceIte,hde',Bool.false_eq_true]
      exact le_min (hV 3 (Or.inl hde')) (hV 1 (Or.inr (by decide)))
  · simp only [negative,hD,↓reduceIte]
    exact hV i (Or.inr hD)

theorem negative_linear {f : Family} (atG : Bool) {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    gamma f*v≤negative f atG R t v i :=
  negative_lower atG (fun j _ => linear_lower atG hR hQL hQU ht hv j) i

end SquaresInCircles.Eight.SoleNegativeTOrdinaryData
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveExclusion
open Candidate SoleECoefficients SoleOriginalBlocks

theorem original_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 (deOwner de) (ehOwner de) i)) : False := by
  let t := delta C.theta G+primary C de
  let b := choose t
  have htotal : delta C.theta G+primary C de=t := rfl
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab b de t (delta C.theta G) (primary C de)
    hvar hG hE htotal
  have hP0 : 0≤∑i,(blocks C ab b de t (delta C.theta G) (primary C de) i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C ab b de t (delta C.theta G) (primary C de) i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain b := choose_mem htcap
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by dsimp [t]; linarith⟩
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by
    simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hMtrial : axisCoordinate q≤axisCoordinate qTrial := by
    exact sub_le_sub_right (Real.sqrt_le_sqrt (sub_le_sub_right hQU (1/4))) (1/2)
  have hM : axisCoordinate q≤283/200 := by
    have hu := SoleScalarPolynomials.axis_upper
    norm_num [SoleScalarPolynomials.axisUpper] at hu
    linarith
  have hconc := SoleSplitModel.concave ab de hR hRsq hM ht hC.sorted hcCap ha
  obtain ⟨h0,h1⟩ := SoleEndpointPositive.fixed_endpoints de hab hQL hQU ht hC hn
    hvar hG hE htotal
  have hpos := SoleSplitModel.positive_of_endpoints hconc hx h0 h1
  have hnec := SoleSplitSupport.necessary de hab hR ht hG hE htotal hC.sorted hc hn
    (SoleEndpointSupport.primary_le_axis hQL (hC.sorted E) (hC.contained E)) hsign hf
  exact (not_lt_of_ge hnec) hpos

theorem sole_EH_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hE : 0≤delta C.theta E)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 2 1 i)) : False := by
  exact original_false false hQL hQU hC hn hvar hab hG hE
    (by intro h; cases h) hf

theorem sole_DE_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hEy : (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  exact original_false true hQL hQU hC hn hvar hab hG hD (fun _ => hEy) hf

end SquaresInCircles.Eight.SolePositiveExclusion
end
end
end

module

public import SquaresInCircles.Eight.TableFree.SolePositiveTOriginalBlocks
public import SquaresInCircles.Eight.TableFree.SoleEndpointSupport

/-!
# Positive-T endpoint support at the unchanged original radius

Uncompiled source. The concave G/E split has already been defined with
the original anchor coordinates fixed. Only here are its two endpoint
values bounded by the four circle supports. The T support permits both
signed tangents, and the E support retains the actual same-radius axis.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTEndpoint
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open SoleTScalarModel SolePositiveTSplitModel SolePositiveTSplitSupport
open SolePositiveTOrdinaryData PositiveAngularEnvelope

def faceForces (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

theorem face_forces_eq (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) :
    forceData C ab s.family s.td t z (x s t z) (e s t z)=faceForces C ab s t z := rfl

def anchorSupport (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
      (n s t z) (k s.family t z) (ell s.family t z)
      (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)-
    SoleEStress.halfShift C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
      (n s t z) (k s.family t z) (ell s.family t z)
      (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

def eWork (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  if tiltedE s.family then sigma R (epsilon s.family t)*Real.sin (e s t z)
  else if isDE s.family then M*Real.sin (e s t z)
  else SoleEndpointSupport.highWork R (e s t z)

theorem T_support {C : SignedCycle} (ab : Fin 4) (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (hsource : z=tPrimary C s.td) :
    circleSupport R (faceForces C ab s t z T)=primarySupport R (c s.family t z) (eta t) z := by
  have hc := (coefficient_positive ht hz).2.2.1.le
  have hη := (coefficient_positive ht hz).2.2.2.2.2
  have hs := (transport_trig (split_angles s ht hz).1).2.2.1
  have hκ : 0≤c s.family t z*Real.sin z := mul_nonneg hc hs
  unfold faceForces
  rw [SoleEStress.force_T]
  cases htd : s.td
  · have hδ : delta C.theta B=z := by simpa [tPrimary,htd] using hsource.symm
    simp only [htd,btOwner,tdOwner,btWeight,tdWeight,if_false]
    rw [SecondaryEStress.force_T_bt_primary,hδ]
    have he : (c s.family t z*Real.sin z,mWeight s.family t z-c s.family t z*Real.cos z)=
        (c s.family t z*Real.sin z,(c s.family t z*Real.sin z)*eta t) := by
      ext <;> dsimp [mWeight] <;> ring
    rw [he]
    exact (scaled_primary_support (R:=R) hκ hη).2
  · have hδ : delta C.theta T=z := by simpa [tPrimary,htd] using hsource.symm
    simp only [htd,btOwner,tdOwner,btWeight,tdWeight,if_true]
    rw [SecondaryEStress.force_T_td_primary,hδ]
    have he : (c s.family t z*Real.sin z,c s.family t z*Real.cos z-mWeight s.family t z)=
        (c s.family t z*Real.sin z,-(c s.family t z*Real.sin z)*eta t) := by
      ext <;> dsimp [mWeight] <;> ring
    rw [he]
    exact (scaled_primary_support (R:=R) hκ hη).1

theorem fixedWork_le {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (hs : (C.point T).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors) :
    fixedWork C ab s.family s.td t z (x s t z) (e s t z)≤
      anchorSupport C ab s R t z+primarySupport R (c s.family t z) (eta t) z := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (faceForces C ab s t z H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (faceForces C ab s t z A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (faceForces C ab s t z B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (faceForces C ab s t z D)
  have hT := work_le_circleSupport hR hs (hc T) (faceForces C ab s t z T)
  rw [T_support ab s ht hz hsource] at hT
  have hsum := SoleEStress.sum_bounds C hab
    (SolePositiveTOriginalBlocks.btOwner_cases s.td) (SolePositiveTOriginalBlocks.tdOwner_cases s.td)
    (deOwner_cases s.family) (ehOwner_cases s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family) R
  simp only [SoleEStress.bound,Fin.sum_univ_succ] at hsum
  simp only [fixedWork,face_forces_eq]
  dsimp [faceForces,anchorSupport] at *
  linarith

theorem E_support {C : SignedCycle} (s : ScalarCase) {R M t z : ℝ}
    (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2)) :
    eBound C s.family R M t (e s t z)≤eWork s R M t z := by
  have he := (split_angles s ht hz).2.2
  by_cases htilt : tiltedE s.family=true
  · simp [eBound,eWork,htilt]
  · have htilt' := Bool.eq_false_of_not_eq_true htilt
    by_cases hde : isDE s.family=true
    · simp [eBound,eWork,htilt',hde]
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simp only [eBound,eWork,htilt',hde',if_false]
      exact SoleEndpointSupport.folded_work_le hR hs hc he

theorem decomposition {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) (R M : ℝ) {t z : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (ha : ∀ i,|delta C.theta i|≤frameCap) :
    variableDemand C s.family s.td t z (x s t z) (e s t z)-anchorSupport C ab s R t z-
      primarySupport R (c s.family t z) (eta t) z-
      k s.family t z*sigma R (g s.family t)*Real.sin (x s t z)-eWork s R M t z=
    baseline s R (M+1/2) t z+SolePositiveTOriginalBlocks.increment C ab s R t z := by
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hWx := edgeWidth_positive_formula hx
  have hWe := edgeWidth_positive_formula he
  have hWz := edgeWidth_positive_formula hz'
  have hψz := psi_positive hz'
  have hW0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  cases htd : s.td
  · have hδ : delta C.theta B=z := by simpa [tPrimary,htd] using hsource.symm
    rcases hab with rfl | rfl <;> cases hf : s.family <;>
      simp [variableDemand,anchorSupport,baseline,SolePositiveTOriginalBlocks.increment,
        SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
        eWork,eTerm,primaryCoefficient,primarySupport,sigma,SoleEndpointSupport.highWork,
        first,second,Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,btWeight,tdWeight,
        ordinaryDE,ordinaryEH,nWeight,n,mWeight,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,hf,htd,
        hδ,hWx,hWe,hWz,hW0,hψz,width_eq (ha H),width_eq (ha A),width_eq (ha T),
        width_eq (ha D),width_eq (ha E),phi,psi_zero] <;> ring
  · have hδ : delta C.theta T=z := by simpa [tPrimary,htd] using hsource.symm
    rcases hab with rfl | rfl <;> cases hf : s.family <;>
      simp [variableDemand,anchorSupport,baseline,SolePositiveTOriginalBlocks.increment,
        SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
        eWork,eTerm,primaryCoefficient,primarySupport,sigma,SoleEndpointSupport.highWork,
        first,second,Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,btWeight,tdWeight,
        ordinaryDE,ordinaryEH,nWeight,n,mWeight,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,hf,htd,
        hδ,hWx,hWe,hWz,hW0,hψz,width_eq (ha H),width_eq (ha A),width_eq (ha B),
        width_eq (ha D),width_eq (ha E),phi,psi_zero] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R M t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    baseline s R (M+1/2) t z+SolePositiveTOriginalBlocks.increment C ab s R t z≤
      SolePositiveTSplitModel.value C ab s.family s.td R M t z (x s t z) := by
  have hx : x s t z∈Icc 0 (t-z) := by
    cases s.atG <;> simp [x] <;> linarith [hz.2]
  have he : t-z-x s t z=e s t z := by cases s.atG <;> simp [x,e]
  have hfixed := fixedWork_le s hab hR ht hz hsource (hs T) hc hn
  have hE := E_support s hR ht hz (hs E) (hc E)
  have hid := decomposition s R M hab ht hz hsource ha
  rw [value_eq_stress s.td R M hab ht hz hx hn,he]
  dsimp [stress]
  change _≤variableDemand C s.family s.td t z (x s t z) (e s t z)-
    fixedWork C ab s.family s.td t z (x s t z) (e s t z)-
    k s.family t z*sigma R (g s.family t)*Real.sin (x s t z)-eBound C s.family R M t (e s t z)
  linarith

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {q t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (hsource : z=tPrimary C s.td)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t) :
    0<SolePositiveTSplitModel.value C ab s.family s.td (Real.sqrt q) (axisCoordinate q) t z (x s t z) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have hR := Real.sqrt_nonneg q
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hQL
  have hRU : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hpure (i : Fin 4) : 1/10000-baseline s (Real.sqrt q) (Real.sqrt (q-1/4)) t z≤
      SingleAngleConcavity.pure (single s i) (Real.sqrt q) (small s t z i) (large s t z i)
        (actualNu s t z i) t := by
    have hs := SolePositiveTScalar.actual_radius_positive {s with negative:=i} hQU ht hz
    have hl := pure_scalar_lower s (R:=Real.sqrt q) (M:=Real.sqrt (q-1/4)) ht hz i
    linarith
  have hi := SolePositiveTOriginalBlocks.original_increment s hab hR hRL hRU ht hz
    ha hvar hG hE hT htotal hpure
  have hl := value_lower s hab hR ht hz hsource hC.sorted hc hn ha
    (M:=axisCoordinate q)
  have haxis : axisCoordinate q+1/2=Real.sqrt (q-1/4) := by simp [axisCoordinate]
  rw [haxis] at hl
  linarith

end SquaresInCircles.Eight.TableFree.SolePositiveTEndpoint

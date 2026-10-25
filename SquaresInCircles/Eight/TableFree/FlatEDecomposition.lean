module

public import SquaresInCircles.Eight.TableFree.FlatEStress

/-!
# Exact E-secant accounting at the original anchors

Uncompiled source. Each E gain is measured from the actual current H or
D zero-angle norm. Consequently a negative T gain and a negative E gain
at D add exactly, including when both multipliers are secants.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatEDecomposition
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks FlatEStress FlatTStress

def oldDefect (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : ℝ :=
  if flatT then CoreENegativeStress.flatDefect C ab bt td de eh n k l b t R
  else CoreEStress.defect C ab bt td de eh n k l b t R

theorem old_as_anchors {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (flatT : Bool) (n k l b t R : ℝ) :
    oldDefect C ab bt td de eh flatT n k l b t R=
      demand C (SecondaryEStress.weights n k l b t)+CoreEStress.halfShift C ab bt td de eh n k l b t-
      R*CoreEStress.anchorNorms C ab bt td de eh n k l b t-
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t G)-
      (if flatT then work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t T))-
      work (CoreEStress.forces C ab bt td de eh n k l b t E) (C.point E) := by
  cases flatT
  · simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
    rw [CoreEStress.defect,CoreEStress.sum_bounds C hab hbt htd hde heh]
    ring
  · exact CoreENegativeStress.flatDefect_as_anchors hab hbt htd hde heh n k l b t R

theorem DE_balance {C : SignedCycle} {de : Fin 4}
    (hde : de=2 ∨ de=3) (hsmall : |delta C.theta D|≤frameCap)
    (hd : primaryDE C de≤0) :
    deWeight C de*edgeWidth (delta C.theta D)+deWeight C de*PositiveAngularEnvelope.phi (ordinaryDE C de)/2-
      deWeight C de*psi (ordinaryDE C de)+(7/12)*Real.tan (deAngle C de)=
      edgeWidth (delta C.theta D)-edgeWidth (primaryDE C de)+1+
      PositiveAngularEnvelope.phi (ordinaryDE C de)/2-psi (ordinaryDE C de)+
      (1/Real.cos (deAngle C de)-1+(13/12)*Real.tan (deAngle C de)) := by
  rcases hde with rfl | rfl
  · simp [deWeight,deAngle,primaryDE,ordinaryDE,edgeWidth,pairWidth]
  · have hneg : delta C.theta D≤0 := by simpa [primaryDE] using hd
    have ha : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hneg,(neg_le_abs _).trans hsmall⟩
    have hw := edgeWidth_negative_formula ha
    have hc := transport_cos_pos hsmall
    simp only [neg_neg] at hw
    simp [deWeight,deAngle,primaryDE,ordinaryDE,hw,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring

theorem EH_balance {C : SignedCycle} {eh : Fin 4}
    (heh : eh=0 ∨ eh=1) (hsmall : |delta C.theta E|≤frameCap)
    (he : primaryEH C eh≤0) :
    ehWeight C eh*edgeWidth (delta C.theta E)+ehWeight C eh*PositiveAngularEnvelope.phi (ordinaryEH C eh)/2-
      ehWeight C eh*psi (ordinaryEH C eh)+(7/12)*Real.tan (ehAngle C eh)=
      edgeWidth (delta C.theta E)-edgeWidth (primaryEH C eh)+1+
      PositiveAngularEnvelope.phi (ordinaryEH C eh)/2-psi (ordinaryEH C eh)+
      (1/Real.cos (ehAngle C eh)-1+(13/12)*Real.tan (ehAngle C eh)) := by
  rcases heh with rfl | rfl
  · simp [ehWeight,ehAngle,primaryEH,ordinaryEH,edgeWidth,pairWidth]
  · have hneg : delta C.theta E≤0 := by simpa [primaryEH] using he
    have ha : -delta C.theta E∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hneg,(neg_le_abs _).trans hsmall⟩
    have hw := edgeWidth_negative_formula ha
    have hc := transport_cos_pos hsmall
    simp only [neg_neg] at hw
    simp [ehWeight,ehAngle,primaryEH,ordinaryEH,hw,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring

theorem E_work_charge {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    work (CoreEStress.forces C ab bt td de eh n k l b t E) (C.point E)+charge C de eh=
      edgeWidth (primaryDE C de)+edgeWidth (primaryEH C eh)-2 := by
  rw [CoreEStress.force_E hde heh]
  dsimp [work,ActualCoreEBlocks.charge,CoreECharge.pairDeficit]
  ring

theorem accounting {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (flatT : Bool) (n k l b t R : ℝ) :
    FlatEStress.defect C ab bt td de eh flatT n k l b t R=
      oldDefect C ab bt td de eh flatT n k l b t R-charge C de eh+
      secantCharge R 1 n (ehAngle C eh)+secantCharge R 1 t (deAngle C de)+
      FlatEStress.increment C ab bt td de eh n k l b t R-
      CoreEStress.increment C ab bt td de eh n k l b t R := by
  have hD := DE_balance hde (hsmall D) hd
  have hE := EH_balance heh (hsmall E) he
  have hw := E_work_charge (C := C) hde heh ab bt td n k l b t
  have hDemand : demand C (FlatEStress.weights C de eh n k l b t)-
      demand C (SecondaryEStress.weights n k l b t)=
      (deWeight C de-1)*edgeWidth (delta C.theta D)+
        (ehWeight C eh-1)*edgeWidth (delta C.theta E) := by
    simp [demand,FlatEStress.weights,SecondaryEStress.weights,Fin.sum_univ_succ,D,E]
    ring
  rw [FlatEStress.defect_as_anchors hab hbt htd hde heh,
    old_as_anchors hab hbt htd hde heh,
    FlatEStress.E_work hde heh hsmall hflat,
    FlatEStress.increment_eq hab hbt htd]
  dsimp [CoreEStress.increment,FlatEStress.halfShift,CoreEStress.halfShift,
    FlatEStress.zeroNorms,PositivePrimaryBaselines.zeroNorms,secantCharge]
  simp only [one_mul,pairNorm_symm 1 n,pairNorm_symm 1 t]
  dsimp only [deWeight,ehWeight] at *
  rw [pairNorm_symm (1/Real.cos (deAngle C de)) t]
  linarith [hDemand,hD,hE,hw]

theorem positive_TD {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 2 de eh false (tiltedWeight k η (delta C.theta G)) k l
      (tiltedWeight k η (delta C.theta T)) k R=
      tdBaseline R k l η (delta C.theta G) (delta C.theta T)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 k (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l
        (tiltedWeight k η (delta C.theta T)) k R := by
  rw [accounting hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.td_decomposition hab hde heh hk hη hsmall hx hz]
  ring

theorem positive_BT {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta B∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 3 0 de eh false (tiltedWeight k η (delta C.theta G)) k l k
      (tiltedWeight k η (delta C.theta B)) R=
      btBaseline R k l η (delta C.theta G) (delta C.theta B)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta B)) (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l k
        (tiltedWeight k η (delta C.theta B)) R := by
  rw [accounting hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.bt_decomposition hab hde heh hk hη hsmall hx hz]
  ring

theorem secondary_T {C : SignedCycle} {ab de eh : Fin 4} {R k l c η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 0 de eh false (tiltedWeight k η (delta C.theta G)) k l c c R=
      secondaryBaseline R k l c η (delta C.theta G)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 c (deAngle C de)+
      FlatEStress.increment C ab 2 0 de eh (tiltedWeight k η (delta C.theta G)) k l c c R := by
  rw [accounting hab (Or.inl rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.secondary_decomposition hab hde heh hk hη hsmall hx]
  ring

theorem negative_TD {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hTflat : (C.point T).a=7/12)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 2 de eh true (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c 1 s+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 (c/Real.cos s) (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R := by
  rw [accounting hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,↓reduceIte]
  rw [CoreENegativeStress.negative_TD_decomposition hab hde heh hk hη hsmall hx hs hT hTflat]
  ring

theorem negative_BT {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hTflat : (C.point T).a=7/12)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 3 0 de eh true (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c l s+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 c (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R := by
  rw [accounting hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,↓reduceIte]
  rw [CoreENegativeStress.negative_BT_decomposition hab hde heh hk hη hsmall hx hs hB hTflat]
  ring

end SquaresInCircles.Eight.TableFree.FlatEDecomposition

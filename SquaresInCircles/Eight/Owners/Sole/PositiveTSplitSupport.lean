module

public import SquaresInCircles.Eight.Owners.Sole.PositiveTSplitModel

/-!
# Eight squares: the original weak witnesses imply the positive-T split inequality

G and E are bounded in their original signed
coordinates. H/A/B/D/T retain their actual work. In particular the
concave split is necessary before independent anchor supports are used.
The two physical T rows and the two weak AB owners stay explicit.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTSplitSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open SoleTScalarModel SolePositiveTSplitModel

def forceData (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x e : ℝ) :
    Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (nWeight f t z x) (k f t z) (ell f t z) (btWeight f td t z) (tdWeight f td t z)
    (deWeight f t e) (ehWeight f)

def variableDemand (C : SignedCycle) (f : Family) (td : Bool) (t z x e : ℝ) : ℝ :=
  nWeight f t z x*edgeWidth (delta C.theta H)+k f t z*edgeWidth x+
    ell f t z*edgeWidth (delta C.theta A)+btWeight f td t z*edgeWidth (delta C.theta B)+
    tdWeight f td t z*edgeWidth (delta C.theta T)+
    deWeight f t e*edgeWidth (if isDE f then e else delta C.theta D)+
    ehWeight f*edgeWidth (if isDE f then delta C.theta E else e)

def fixedWork (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x e : ℝ) : ℝ :=
  work (forceData C ab f td t z x e H) (C.point H)+
    work (forceData C ab f td t z x e A) (C.point A)+
    work (forceData C ab f td t z x e B) (C.point B)+
    work (forceData C ab f td t z x e T) (C.point T)+
    work (forceData C ab f td t z x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool)
    (R M t z x e : ℝ) : ℝ :=
  variableDemand C f td t z x e-fixedWork C ab f td t z x e-
    k f t z*sigma R (g f t)*Real.sin x-eBound C f R M t e

theorem deOwner_cases (f : Family) : deOwner f=2 ∨ deOwner f=3 := by
  cases f <;> simp [deOwner,isDE]
theorem ehOwner_cases (f : Family) : ehOwner f=0 ∨ ehOwner f=1 := by
  cases f <;> simp [ehOwner,isDE]

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool)
    (R M : ℝ) {t z x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f)
    (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z)) (hn : C.NormalAnchors) :
    SolePositiveTSplitModel.value C ab f td R M t z x=
      stress C ab f td R M t z x (t-z-x) := by
  have hH : |(C.point H).y|=(C.point H).y := abs_of_nonneg hn.H_nonneg
  have hD : |(C.point D).y|=-(C.point D).y := abs_of_nonpos hn.D_nonpos
  rw [SolePositiveTSplitModel.formula ab td R M ht hz hx]
  simp only [stress,variableDemand,fixedWork,constant,transverse,SoleSplitModel.transverse,
    radialD,radialH,hH,hD,forceData,SoleEStress.forces,force,work]
  rcases hab with rfl | rfl <;> cases f <;> cases td <;>
    simp [SoleEStress.weights,CoreEStress.owners,previous,source,target,word,add,scale,
      SignedCycle.edge,zeroProjection,quarterProjection,H,A,B,T,D,E,next,btOwner,tdOwner,
      deOwner,ehOwner,deWeight,ehWeight,lambda,tiltedE,isDE] <;> ring

theorem original_demand (C : SignedCycle) (f : Family) (td : Bool) (t z : ℝ) :
    variableDemand C f td t z (delta C.theta G) (ePrimary C f)=
      demand C (SoleEStress.weights (nWeight f t z (delta C.theta G)) (k f t z)
        (ell f t z) (btWeight f td t z) (tdWeight f td t z)
        (deWeight f t (ePrimary C f)) (ehWeight f)) := by
  rw [SoleEStress.demand_eq]
  cases f <;> simp [variableDemand,ePrimary,isDE]

theorem E_force (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x : ℝ) :
    forceData C ab f td t z x (ePrimary C f) E=
      if isDE f then (Real.sin (ePrimary C f),lambda f-Real.cos (ePrimary C f))
      else (Real.sin (ePrimary C f),Real.cos (ePrimary C f)-deWeight f t (ePrimary C f)) := by
  unfold forceData
  rw [SoleEStress.force_E (deOwner_cases f) (ehOwner_cases f)]
  cases f <;> simp [deOwner,ehOwner,primaryDE,primaryEH,ePrimary,
    deWeight,ehWeight,lambda,isDE,tiltedE]

theorem E_work_le {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R M t z x : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (he : ePrimary C f∈Icc 0 (t-z))
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2))
    (ha : (C.point E).a≤M) (hsign : isDE f=true → (C.point E).y≤0) :
    work (forceData C ab f td t z x (ePrimary C f) E) (C.point E)≤
      eBound C f R M t (ePrimary C f) := by
  have he' : ePrimary C f∈Icc 0 frameCap :=
    ⟨he.1,by linarith [he.2,hz.1,(angle ht).2]⟩
  have hsin := (transport_trig he').2.2.1
  have hcos := Real.cos_le_one (ePrimary C f)
  rw [E_force]
  by_cases hd : isDE f=true
  · have hy := hsign hd
    have htilt : tiltedE f=false := by cases f <;> simp_all [isDE,tiltedE]
    have hlam : lambda f=5/4 := by simp [lambda,hd]
    have hv : 0≤lambda f-Real.cos (ePrimary C f) := by rw [hlam]; linarith
    have hm := mul_nonpos_of_nonneg_of_nonpos hv hy
    have ha' := mul_le_mul_of_nonneg_right ha hsin
    simp [eBound,hd,htilt,work]
    nlinarith
  · have hd' : isDE f=false := Bool.eq_false_of_not_eq_true hd
    simp only [hd',Bool.false_eq_true,↓reduceIte]
    by_cases htilt : tiltedE f=true
    · have hε := (coefficient_positive ht hz).2.2.2.2.1
      have hw := work_le_circleSupport hR hs hc
        (Real.sin (ePrimary C f),-Real.sin (ePrimary C f)*epsilon f t)
      have hsupp := (scaled_primary_support (R := R) hsin hε).1
      rw [hsupp] at hw
      simp only [eBound,deWeight,htilt,↓reduceIte,work,sigma] at *
      linarith
    · have htilt' : tiltedE f=false := Bool.eq_false_of_not_eq_true htilt
      have hy := mul_le_mul_of_nonpos_left (neg_abs_le (C.point E).y)
        (show Real.cos (ePrimary C f)-1≤0 by linarith)
      simp only [eBound,deWeight,htilt',hd',Bool.false_eq_true,↓reduceIte,work]
      linarith

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R t z e : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (hx : delta C.theta G∈Icc 0 (t-z))
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forceData C ab f td t z (delta C.theta G) e G) (C.point G)≤
      k f t z*sigma R (g f t)*Real.sin (delta C.theta G) := by
  obtain ⟨hk,hl,hc0,hg,hε,hη⟩ := coefficient_positive ht hz
  have hx' : delta C.theta G∈Icc 0 frameCap :=
    ⟨hx.1,by linarith [hx.2,hz.1,(angle ht).2]⟩
  have hw := work_le_circleSupport hR hs hc (forceData C ab f td t z (delta C.theta G) e G)
  have hfd : forceData C ab f td t z (delta C.theta G) e G=
      SecondaryEStress.forces C ab (btOwner td) (tdOwner td)
        (tiltedWeight (k f t z) (g f t) (delta C.theta G)) (k f t z) (ell f t z)
        (btWeight f td t z) (tdWeight f td t z) G := by
    unfold forceData
    rw [SoleEStress.force_G]
    rfl
  have hsupp := positive_G_support (R := R) (ab := ab) (bt := btOwner td) (td := tdOwner td)
    (l := ell f t z) (b := btWeight f td t z) (t := tdWeight f td t z) hk.le hg hx'
  rw [hfd,hsupp] at hw
  rw [hfd]
  have hp : primarySupport R (k f t z) (g f t) (delta C.theta G)=
      k f t z*sigma R (g f t)*Real.sin (delta C.theta G) := by
    simp only [primarySupport,sigma]
    ring
  linarith

theorem positive_weights {f : Family} (td : Bool) {t z x e : ℝ}
    (ht : t∈domain f) (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z)) (he : e∈Icc 0 (t-z)) :
    0<nWeight f t z x ∧ 0<k f t z ∧ 0<ell f t z ∧
      0<btWeight f td t z ∧ 0<tdWeight f td t z ∧ 0<deWeight f t e ∧ 0<ehWeight f := by
  obtain ⟨hk,hl,hc,hg,hε,hη⟩ := coefficient_positive ht hz
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,(angle ht).2]⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,by linarith [he.2,hz.1,(angle ht).2]⟩
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans (angle ht).2⟩
  have hn : 0<nWeight f t z x := by
    dsimp [nWeight]
    exact mul_pos hk (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hx').1]) (mul_nonneg hg (transport_trig hx').2.2.1))
  have hm : 0< mWeight f t z := by
    dsimp [mWeight]
    exact mul_pos hc (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hz').1]) (mul_nonneg hη (transport_trig hz').2.2.1))
  have hd : 0<deWeight f t e := by
    dsimp [deWeight]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (by linarith [(transport_trig he').1])
        (mul_nonneg hε (transport_trig he').2.2.1)
    · norm_num
  refine ⟨hn,hk,hl,?_,?_,hd,?_⟩
  · dsimp [btWeight]; split_ifs <;> assumption
  · dsimp [tdWeight]; split_ifs <;> assumption
  · dsimp [ehWeight,lambda]; split_ifs <;> norm_num

/-- Necessity has no lower-radius assumption. The original seven weak
contacts and original signed points are the complete geometric input. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool) {R M t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f)
    (htotal : delta C.theta G+ePrimary C f+z=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : (C.point E).a≤M)
    (hsign : isDE f=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i
      (CoreEStress.owners ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f) i)) :
    SolePositiveTSplitModel.value C ab f td R M t z (delta C.theta G)≤0 := by
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by linarith⟩
  have he : ePrimary C f∈Icc 0 (t-z) := ⟨hE,by linarith⟩
  have hxe : t-z-delta C.theta G=ePrimary C f := by linarith
  obtain ⟨hn0,hk,hl,hbt,htd,hde,heh⟩ := positive_weights td ht hz hx he
  have hw : ∀ i,0≤SoleEStress.weights (nWeight f t z (delta C.theta G)) (k f t z) (ell f t z)
      (btWeight f td t z) (tdWeight f td t z) (deWeight f t (ePrimary C f)) (ehWeight f) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0.le,hk.le,hl.le,hbt.le,htd.le,hde.le,heh.le]
  have hbound : ∀ i,work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) i) (C.point i)≤
      (![work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) H) (C.point H),
        k f t z*sigma R (g f t)*Real.sin (delta C.theta G),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) A) (C.point A),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) B) (C.point B),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) T) (C.point T),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) D) (C.point D),
        eBound C f R M t (ePrimary C f)] : Vertex → ℝ) i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab td hR ht hz hx (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact E_work_le ab td hR ht hz he (hs E) (hc E) ha hsign
  have hsep := weighted_separation_le hw hf hbound
  rw [value_eq_stress td R M hab ht hz hx hn,hxe]
  have hd := original_demand C f td t z
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    add_zero] at hsep
  simp only [stress,fixedWork,hd]
  linarith

end SquaresInCircles.Eight.SolePositiveTSplitSupport

module

public import SquaresInCircles.Eight.TableFree.SoleSplitModel

/-!
# The fixed-coordinate split is necessary for the original weak owners

Uncompiled source. At the original primary split, the weighted seven
weak separators give a nonpositive relaxed stress. Only the G and E
works are bounded here: the H/A/B/D coordinates remain original.
Sole-EH allows either E sign; sole-DE retains E.y<=0 explicitly.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleSplitSupport
open Candidate SignedStress SoleECoefficients SoleOriginalBlocks SoleSplitModel
open SoleResiduals SecondaryEStress ActualCoreEBlocks

def forceData (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab 2 0 (deOwner de) (ehOwner de)
    (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e)

def variableDemand (C : SignedCycle) (b : Band) (de : Bool) (t x e : ℝ) : ℝ :=
  n b t x*edgeWidth (delta C.theta H)+k b t*edgeWidth x+
    ell b t*edgeWidth (delta C.theta A)+c b t*edgeWidth (delta C.theta B)+
    c b t*edgeWidth (delta C.theta T)+
    eMultiplier b de t e*edgeWidth (if de then e else delta C.theta D)+
    hMultiplier b de e*edgeWidth (if de then delta C.theta E else e)

def anchorWork (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) : ℝ :=
  work (forceData C ab b de t x e H) (C.point H)+
    work (forceData C ab b de t x e A) (C.point A)+
    work (forceData C ab b de t x e B) (C.point B)+
    work (forceData C ab b de t x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R M t x e : ℝ) : ℝ :=
  variableDemand C b de t x e-anchorWork C ab b de t x e-
    k b t*sigma R (g b t)*Real.sin x-eBound C b de R M t e

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool)
    (R M : ℝ) {t x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain b) (hx : x∈Icc 0 t)
    (hn : C.NormalAnchors) :
    SoleSplitModel.value C ab b de R M t x=stress C ab b de R M t x (t-x) := by
  rw [SoleSplitModel.formula ab de R M ht hx]
  rcases hab with rfl | rfl <;> cases de <;>
    simp [stress,variableDemand,anchorWork,constant,transverse,radial,forceData,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,
      source,target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,G,A,B,T,D,E,next,deOwner,ehOwner,eMultiplier,hMultiplier,
      abs_of_nonneg hn.H_nonneg,abs_of_nonpos hn.D_nonpos] <;> ring

theorem original_demand (C : SignedCycle) (b : Band) (de : Bool) (t : ℝ) :
    variableDemand C b de t (delta C.theta G) (primary C de)=
      demand C (SoleEStress.weights (n b t (delta C.theta G)) (k b t) (ell b t)
        (c b t) (c b t) (eMultiplier b de t (primary C de)) (hMultiplier b de (primary C de))) := by
  rw [SoleEStress.demand_eq]
  cases de <;> simp [variableDemand,primary]

theorem E_force (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x : ℝ) :
    forceData C ab b de t x (primary C de) E=
      if de then (Real.sin (primary C de),hMultiplier b de (primary C de)-Real.cos (primary C de))
      else (Real.sin (primary C de),Real.cos (primary C de)-eMultiplier b de t (primary C de)) := by
  unfold forceData
  rw [SoleEStress.force_E (deOwner_cases de) (ehOwner_cases de)]
  cases de <;> simp [deOwner,ehOwner,primaryDE,primaryEH,primary,eMultiplier,hMultiplier]

theorem E_work_le {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R M t x : ℝ}
    (hR : 0≤R) (ht : t∈domain b) (he : primary C de∈Icc 0 t)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2))
    (ha : (C.point E).a≤M) (hsign : de=true → (C.point E).y≤0) :
    work (forceData C ab b de t x (primary C de) E) (C.point E)≤
      eBound C b de R M t (primary C de) := by
  have he' : primary C de∈Icc 0 frameCap := ⟨he.1,he.2.trans (angle ht).2⟩
  have hsin := (transport_trig he').2.2.1
  have hcos := Real.cos_le_one (primary C de)
  rw [E_force]
  cases de
  · simp only [Bool.false_eq_true,if_false]
    by_cases hb : b=.high
    · subst b
      have hy := mul_le_mul_of_nonpos_left (neg_abs_le (C.point E).y)
        (show Real.cos (primary C false)-1≤0 by linarith)
      simp only [eBound,if_true,Bool.false_eq_true,if_false,eMultiplier,p,work]
      nlinarith
    · have heta := (SoleECoefficients.positive ht).2.2.2.2
      have hh := work_le_circleSupport hR hs hc
        (Real.sin (primary C false),-Real.sin (primary C false)*eta b t)
      have hcirc := (scaled_primary_support (R := R) hsin heta).1
      rw [hcirc] at hh
      simp only [eBound,hb,if_false,Bool.false_eq_true,eMultiplier,p,work,sigma] at *
      nlinarith
  · simp only [if_true]
    have hy := hsign rfl
    have hvertical : 0≤hMultiplier b true (primary C true)-Real.cos (primary C true) := by
      cases b <;> simp only [hMultiplier,r,if_true,if_false] <;> nlinarith
    have hm := mul_nonpos_of_nonneg_of_nonpos hvertical hy
    have ha' := mul_le_mul_of_nonneg_right ha hsin
    simp [eBound,work] at *
    nlinarith

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R t e : ℝ}
    (hR : 0≤R) (ht : t∈domain b) (hx : delta C.theta G∈Icc 0 t)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forceData C ab b de t (delta C.theta G) e G) (C.point G)≤
      k b t*sigma R (g b t)*Real.sin (delta C.theta G) := by
  have hp := SoleECoefficients.positive ht
  have hx' : delta C.theta G∈Icc 0 frameCap := ⟨hx.1,hx.2.trans (angle ht).2⟩
  have hh := work_le_circleSupport hR hs hc (forceData C ab b de t (delta C.theta G) e G)
  unfold forceData at hh
  rw [SoleEStress.force_G] at hh
  have hsup := positive_G_support (R := R) (ab := ab) (bt := 2) (td := 0)
    (l := ell b t) (b := c b t) (t := c b t) hp.1.le hp.2.2.2.1 hx'
  simpa only [n,hsup,primarySupport,sigma,mul_comm,mul_left_comm,mul_assoc] using hh

theorem T_force (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) :
    forceData C ab b de t x e T=(0,0) := by
  unfold forceData
  rw [SoleEStress.force_T,force_T_secondary]
  simp

/-- This uses only the original seven weak witnesses. The lower-radius
bound needed for positivity is deliberately absent from necessity. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {R M t : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain b)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : (C.point E).a≤M)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 (deOwner de) (ehOwner de) i)) :
    SoleSplitModel.value C ab b de R M t (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := primary C de
  have hx : x∈Icc 0 t := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 t := ⟨hE,by dsimp [x,e] at *; linarith⟩
  have hxe : t-x=e := by dsimp [x,e]; linarith
  obtain ⟨hk,hl,hc0,hg,heta⟩ := SoleECoefficients.positive ht
  obtain ⟨hn0,hp0,hr0⟩ := weights_positive ht hx he
  have hw : ∀ i,0≤SoleEStress.weights (n b t x) (k b t) (ell b t) (c b t) (c b t)
      (eMultiplier b de t e) (hMultiplier b de e) i := by
    intro i
    fin_cases i <;> cases de <;>
      simp [SoleEStress.weights,eMultiplier,hMultiplier,hn0.le,hk.le,hl.le,hc0.le,hp0.le,hr0.le]
  let Bnd : Vertex → ℝ := ![
    work (forceData C ab b de t x e H) (C.point H),
    k b t*sigma R (g b t)*Real.sin x,
    work (forceData C ab b de t x e A) (C.point A),
    work (forceData C ab b de t x e B) (C.point B),0,
    work (forceData C ab b de t x e D) (C.point D),eBound C b de R M t e]
  have hbound : ∀ i,work (forceData C ab b de t x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab de hR ht hx (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · simp [Bnd,T_force,work,T]
    · exact le_rfl
    · exact E_work_le ab de hR ht he (hs E) (hc E) ha hsign
  have hsep := weighted_separation_le hw hf hbound
  rw [value_eq_stress de R M hab ht hx hn,hxe]
  change stress C ab b de R M t x e≤0
  have hd := original_demand C b de t
  change variableDemand C b de t x e=_ at hd
  dsimp [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_succ] at hsep
  dsimp [anchorWork]
  linarith

end SquaresInCircles.Eight.TableFree.SoleSplitSupport

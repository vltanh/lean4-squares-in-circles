module

public import SquaresInCircles.Eight.Owners.Sole.SplitSupport

/-!
# Eight squares: endpoint support bounds for the fixed original anchors

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

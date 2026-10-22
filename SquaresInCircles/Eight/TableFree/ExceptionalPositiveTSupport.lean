module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTStress

/-!
# Positive-T endpoint supports after the actual-coordinate split

Uncompiled source. The four original anchors are bounded by their
signed circle supports only after x+e is split with z fixed. All
ordinary angles, including the two H angles, remain in the increment.
The baseline is exactly the one in the two positive-T hand proofs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress ExceptionalPositiveTStress

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (td : Bool)
    (R k l c eta z x e : ℝ) (hab : ab=0 ∨ ab=2) (hR : 0≤R)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors) :
    ExceptionalPositiveTStress.anchorWork C ab td k l c eta z x e≤
      anchorSupport C ab td R k l c eta z x e := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (forces C ab td k l c eta z x e H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (forces C ab td k l c eta z x e A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (forces C ab td k l c eta z x e B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (forces C ab td k l c eta z x e D)
  have hsum := SoleEStress.sum_bounds C hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l
    (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) R
  simp only [SoleEStress.bound,Fin.sum_univ_succ] at hsum
  dsimp [ExceptionalPositiveTStress.anchorWork,anchorSupport,forces] at *
  dsimp [signedSupport] at hsum
  linarith

theorem decomposition {C : SignedCycle} {ab : Fin 4} (td : Bool)
    (R k l c eta : ℝ) {z x e : ℝ}
    (hab : ab=0 ∨ ab=2) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 frameCap) (he : e∈Icc 0 frameCap)
    (hsource : primary C td=z) :
    variableDemand C td k l c eta z x e-anchorSupport C ab td R k l c eta z x e-
      k*sigma R eta*Real.sin x-c*sigma R eta*Real.sin z-sigma R eta*Real.sin e=
      baseline td R k l c eta z x e+increment C ab td R k l c eta z x e := by
  rcases hab with rfl | rfl <;> cases td <;>
    simp [primary] at hsource <;>
    simp [variableDemand,anchorSupport,baseline,increment,SoleEStress.increment,
      SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
      ExceptionalContactSupport.contactScalar,btOwner,tdOwner,bWeight,tWeight,
      ordinaryDE,ordinaryEH,hsource,width_eq (ha H),width_eq (ha A),
      width_eq (ha B),width_eq (ha T),width_eq (ha E),
      edgeWidth_positive_formula hz,edgeWidth_positive_formula hx,
      edgeWidth_positive_formula he,phi,psi,tilt,sigma] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R k l c eta t z x : ℝ} (hab : ab=0 ∨ ab=2) (hR : 0≤R) (heta : 0≤eta)
    (ht : t∈Icc 0 frameCap) (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z))
    (hsource : primary C td=z) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C) :
    baseline td R k l c eta z x (t-z-x)+
      increment C ab td R k l c eta z x (t-z-x)≤
        value C ab td R k l c eta t z x := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,ht.2]⟩
  have he : t-z-x∈Icc 0 frameCap :=
    ⟨by linarith [hx.2],by linarith [hx.1,hz.1,ht.2]⟩
  have hw := anchorWork_le td R k l c eta z x (t-z-x) hab hR hc hn
  have hE := ExceptionalContactSupport.eWork_le hR heta he (hs E) (hc E)
  have hid := decomposition td R k l c eta hab ha hz' hx' he hsource
  rw [value_eq_stress td R k l c eta hab ht hz hx hsource hn hcontact]
  dsimp [stress]
  linarith

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTSupport

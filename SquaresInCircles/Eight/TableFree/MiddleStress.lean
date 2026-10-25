module

public import SquaresInCircles.Eight.TableFree.MiddlePhysicalStress
public import SquaresInCircles.Eight.TableFree.MiddleAngularStress

/-!
# The common middle stress from either original AB owner

Uncompiled source draft.  The conclusion uses the actual signed T
tangent, an arbitrary proved lower bound for the original A primary,
and the original T--A frame difference.  The arbitrary B frame has been
eliminated by whole-interval width and norm comparisons.  No endpoint,
alignment, G/T sign, core, or changed point is an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace MiddleStress
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open CorrelatedSameBlock MiddlePhysicalStress MiddleAngularPenalty

theorem B_eq_width (l s : ℝ) :
    MiddleAngularStress.B l s=endpointWidth l s-
      Real.sqrt qCap*(pairNorm l 1 s-pairNorm l 1 0) := by
  by_cases hs : 0≤ s
  · simp [MiddleAngularStress.B,endpointWidth,hs,U]
  · simp [MiddleAngularStress.B,endpointWidth,hs,V]

theorem single_increment_lower {l w s : ℝ} (hlw : l≤w) (hw : w≤1)
    (hs : |s|≤frameCap) :
    MiddleAngularStress.B l s≤w*psi s-
      Real.sqrt qCap*(pairNorm l 1 s-pairNorm l 1 0) := by
  rw [B_eq_width]
  by_cases hs0 : 0≤ s
  · have hs' : s∈Icc 0 frameCap := ⟨hs0,(le_abs_self s).trans hs⟩
    have hp := mul_nonneg (sub_nonneg.mpr hlw)
      (sub_nonneg.mpr (one_le_phi hs'))
    simp only [endpointWidth,hs0,↓reduceIte]
    rw [psi_positive hs']
    nlinarith
  · have hn : -s∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs s).trans hs⟩
    have hψ : psi s=Real.cos s-1 := by
      simpa only [neg_neg,Real.cos_neg] using psi_negative hn
    have hp := mul_nonneg (sub_nonneg.mpr hw)
      (show 0≤1-Real.cos s by linarith [Real.cos_le_one s])
    simp only [endpointWidth,hs0,↓reduceIte]
    rw [hψ]
    nlinarith

/-- Both actual weak AB owners give the same scalar bound, without
placing B between A and T and without assigning any sign to T. -/
theorem actual_middle {A B T : SignedPoint} {l f d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0) (hf : f≤A.a)
    (hl : l∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : quarterFeasible B T v 2) :
    f+2+2*l-2*Real.sqrt qCap*Real.sqrt (1+l^2)+
      MiddleAngularStress.B l (d+v)+T.y≤0 := by
  have hR := Real.sqrt_nonneg qCap
  have hq : (Real.sqrt qCap)^2=qCap :=
    Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hcA : A.Contained ((Real.sqrt qCap)^2) := by
    rw [hq]
    exact hA
  have hcB : B.Contained ((Real.sqrt qCap)^2) := by
    rw [hq]
    exact hB
  have hl0 : 0≤l := by linarith [hl.1]
  have hl1 : l≤1 := by linarith [hl.2]
  have hN0 : pairNorm l 1 0=Real.sqrt (1+l^2) := by
    simp [pairNorm_zero,add_comm]
  rcases hAB with hAB | hAB
  · have hraw := raw_zero hR hcA hcB hyA hyB hl0 hf hd hv hAB hBT
    have hwidth := signed_width ⟨hl.1,hl1⟩ hd hv hs
    rw [B_eq_width]
    rw [hN0] at hraw ⊢
    linarith
  · have hraw := raw_two hR hcA hcB hyA hyB hl0 hf hd hv hAB hBT
    have hd' := single_increment_lower (le_refl l) hl1 hd
    have hv' := single_increment_lower hl1 (le_refl (1:ℝ)) hv
    have hsum := MiddleAngularStress.subadditive hl hd hv hs
    rw [hN0] at hraw hd' hv'
    linarith

end MiddleStress

namespace SignedCycle
open Candidate

/-- Original-cycle form of the common middle stress.  It uses only the
retained actual AB owner and BT2; a GA1 entry cycle is therefore in scope. -/
theorem middle_stress {q l f : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (w : C.Witnesses) (hBT : C.Feasible B 2) (hf : f≤(C.point A).a)
    (hl : l∈Icc (13/20 : ℝ) (23/25)) :
    f+2+2*l-2*Real.sqrt qCap*Real.sqrt (1+l^2)+
      MiddleAngularStress.B l (C.theta T-C.theta A)+(C.point T).y≤0 := by
  have howner : w.owner A=0 ∨ w.owner A=2 := by
    simpa [normalOwners,A] using w.allowed A
  simp only [A] at howner
  have hab : zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 0 ∨
      zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 2 := by
    have hw := w.feasible A
    rcases howner with ho | ho
    · left
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
    · right
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
  have hbt : quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 2 := by
    simpa [Feasible,slack,edge,delta,next,word,B,T,quarterFeasible] using hBT
  have hs : |(C.theta B-C.theta A)+(C.theta T-C.theta B)|≤frameCap := by
    rw [show (C.theta B-C.theta A)+(C.theta T-C.theta B)=C.theta T-C.theta A by ring]
    exact hC.spread T A
  have h := MiddleStress.actual_middle ((hC.contained A).trans hq)
    ((hC.contained B).trans hq) hn.A_nonneg hn.B_nonpos hf hl
    (hC.spread B A) (hC.spread T B) hs hab hbt
  simpa only [show (C.theta B-C.theta A)+(C.theta T-C.theta B)=
    C.theta T-C.theta A by ring] using h

end SignedCycle
end SquaresInCircles.Eight.TableFree

module

public import SquaresInCircles.Eight.TableFree.SoleEndpointPositive

/-!
# Original weak-owner exclusions for the two sole positive E primaries

Uncompiled source. The common radius, original points, original AB
owner, and every ordinary signed angle are retained. Concavity of the
fixed-coordinate scalar precedes the anchor support estimates. The
sole-EH theorem allows either sign of E; sole-DE explicitly keeps the
nonpositive E sign needed by its axis-work inequality.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveExclusion
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

end SquaresInCircles.Eight.TableFree.SolePositiveExclusion

module

public import SquaresInCircles.Eight.TableFree.SolePositiveTEndpoint

/-!
# Actual sole-E exclusions for both nonnegative T primary owners

Uncompiled source. This is the original-source join of the complete
scalar, ordinary-angle, and fixed-coordinate arguments. The selected
AB and T owners remain weak, including every zero-error tie. No G or T
tangent sign and no radial-kind premise is used. Sole EH permits either
E sign; sole DE retains exactly the nonpositive E sign its axis bound uses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTExclusion
open Candidate SoleTScalarModel SolePositiveTSplitModel

def choose (de : Bool) (t : ℝ) : Family :=
  if de then if t≤7/20 then .deLow else .deHigh
  else if t≤1/5 then .ehLow else if t≤7/20 then .ehMiddle else .ehHigh

theorem choose_isDE (de : Bool) (t : ℝ) : isDE (choose de t)=de := by
  cases de <;> simp [choose] <;> split_ifs <;> rfl

theorem choose_mem (de : Bool) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    t∈domain (choose de t) := by
  have h1 : 0 ≤ t := ht.1
  have h2 : t ≤ 7/10 := ht.2
  cases de <;> simp only [choose,Bool.false_eq_true,↓reduceIte] <;>
    split_ifs <;> norm_num [domain,left,right] <;> constructor <;> linarith

theorem original_false {C : SignedCycle} {ab : Fin 4} (de td : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hT : 0≤tPrimary C td) (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td)
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  obtain ⟨z,hzd⟩ : ∃ z : ℝ,z=tPrimary C td := ⟨_,rfl⟩
  obtain ⟨t,htd⟩ : ∃ t : ℝ,t=delta C.theta G+(if de then delta C.theta D else delta C.theta E)+z :=
    ⟨_,rfl⟩
  obtain ⟨f,hfd⟩ : ∃ f : Family,f=choose de t := ⟨_,rfl⟩
  have hde : isDE f=de := by rw [hfd]; exact choose_isDE de t
  have hE' : 0 ≤ ePrimary C f := by simp only [ePrimary,hde]; exact hE
  have htotal : delta C.theta G+ePrimary C f+tPrimary C td=t := by
    rw [htd,hzd]
    simp only [ePrimary,hde]
  obtain ⟨ht0,hP,hN⟩ := SolePositiveTOriginalBlocks.original_budgets (s := ⟨f,td,false,0⟩)
    hab t z hvar hG hE' hT htotal
  have hP0 : 0 ≤ ∑i,(SolePositiveTOriginalBlocks.blocks C ab ⟨f,td,false,0⟩ t z i).P :=
    Finset.sum_nonneg (fun i _ =>
      (SolePositiveTOriginalBlocks.blocks C ab ⟨f,td,false,0⟩ t z i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain f := hfd ▸ choose_mem de htcap
  have hEnn : 0 ≤ (if de then delta C.theta D else delta C.theta E) := hE
  have hz : z∈Icc 0 t := ⟨hzd ▸ hT,by rw [htd]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by rw [htd]; linarith⟩
  have hq0 : 0 ≤ q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q ≤ qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2 ≤ qCap := by rw [hR2]; exact hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by rw [hR2]; exact hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i| ≤ frameCap := fun i => hC.spread (next i) i
  have hM : axisCoordinate q ≤ 283/200 := by
    have hm := Real.sqrt_le_sqrt (sub_le_sub_right hQU (1/4))
    have hu := SoleTScalarModel.axis_upper
    have hv : ((SoleTScalarModel.axisUpper:ℚ):ℝ)=1914558470771/1000000000000 := by
      norm_num [SoleTScalarModel.axisUpper]
    unfold axisCoordinate
    linarith
  have hconc := SolePositiveTSplitModel.concave ab td hR hRsq hM ht hz hC.sorted hcCap ha
  have h0 : 0 < SolePositiveTSplitModel.value C ab f td (Real.sqrt q) (axisCoordinate q) t z 0 := by
    have hh := SolePositiveTEndpoint.endpoint_positive (C:=C) (ab:=ab) ⟨f,td,false,0⟩
      hab hQL hQU ht hz hzd hC hn hvar hG hE' hT htotal
    simpa only [x,Bool.false_eq_true,↓reduceIte] using hh
  have h1 : 0 < SolePositiveTSplitModel.value C ab f td (Real.sqrt q) (axisCoordinate q) t z
      (t-z) := by
    have hh := SolePositiveTEndpoint.endpoint_positive (C:=C) (ab:=ab) ⟨f,td,true,0⟩
      hab hQL hQU ht hz hzd hC hn hvar hG hE' hT htotal
    simpa only [x,↓reduceIte] using hh
  have hpos := SolePositiveTSplitModel.positive_of_endpoints hconc hx h0 h1
  have hnec := SolePositiveTSplitSupport.necessary td hab hR ht hz hG hE'
    (by rw [hzd]; exact htotal) hC.sorted hc hn
    (SoleEndpointSupport.primary_le_axis hQL (hC.sorted E) (hC.contained E))
    (by intro h; apply hsign; rw [← hde]; exact h)
    (by simpa only [deOwner,ehOwner,hde] using hf)
  exact (not_lt_of_ge hnec) hpos

theorem sole_EH_TD2_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hE : 0≤delta C.theta E) (hT : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 2 1 i)) : False := by
  exact original_false false true hQL hQU hC hn hvar hab hG hE hT (by intro h; cases h) hf

theorem sole_EH_BT3_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hE : 0≤delta C.theta E) (hB : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 2 1 i)) : False := by
  exact original_false false false hQL hQU hC hn hvar hab hG hE hB (by intro h; cases h) hf

theorem sole_DE_TD2_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤delta C.theta T)
    (hEy : (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : False := by
  exact original_false true true hQL hQU hC hn hvar hab hG hD hT (fun _ => hEy) hf

theorem sole_DE_BT3_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hB : 0≤delta C.theta B)
    (hEy : (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : False := by
  exact original_false true false hQL hQU hC hn hvar hab hG hD hB (fun _ => hEy) hf

end SquaresInCircles.Eight.TableFree.SolePositiveTExclusion

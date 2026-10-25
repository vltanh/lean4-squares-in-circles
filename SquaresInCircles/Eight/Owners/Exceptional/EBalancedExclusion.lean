module

public import SquaresInCircles.Eight.Owners.Exceptional.EBalanced

/-!
# Eight squares: original exceptional-contact exclusion for total angle at least .18

The strict scalar bounds are applied to the actual
four-block budget only at the intrinsic endpoints. Concavity then
returns to the original split, where the seven original weak owners
give the opposite inequality. All frames and all points stay original.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalEBalancedExclusion
open Candidate ExceptionalECoefficients ExceptionalContactStress ExceptionalEBalanced

theorem fixed_endpoints {C : SignedCycle} {ab : Fin 4} {b : Band} {R t : ℝ}
    (hb : b≠.low) (hab : ab=0 ∨ ab=2) (hR : 0≤R)
    (hQL : qLow≤R^2) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) (hcontact : Contact C) :
    0<value C ab R (k b t) (ell b t) (c b t) (eta b t) t 0 ∧
      0<value C ab R (k b t) (ell b t) (c b t) (eta b t) t t := by
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have heta := (ranges ht).2.2.2.2.2
  have heta0 : 0≤eta b t := by linarith [heta.1]
  have hd := angle ht
  have hL0 := original_endpoint_lower false hb hab hR hQL hcap ht ha hvar hG hD htotal
  have hL1 := original_endpoint_lower true hb hab hR hQL hcap ht ha hvar hG hD htotal
  simp only [endpointX,endpointE,Bool.false_eq_true,↓reduceIte] at hL0 hL1
  have hv0 := ExceptionalContactSupport.value_lower (k := k b t) (l := ell b t) (c := c b t)
    hab hR heta0 hd
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,hd.1⟩) hs hc hn ha hcontact
  have hv1 := ExceptionalContactSupport.value_lower (k := k b t) (l := ell b t) (c := c b t)
    hab hR heta0 hd
    (show t∈Icc 0 t from ⟨hd.1,le_rfl⟩) hs hc hn ha hcontact
  rw [sub_zero,ExceptionalContactSupport.baseline_at_E hd] at hv0
  rw [sub_self,ExceptionalContactSupport.baseline_at_G hd] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hb ht hR hQU
  constructor <;> linarith

theorem original_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hlarge : 9/50≤delta C.theta G+delta C.theta D)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  let t := delta C.theta G+delta C.theta D
  let b : Band := if t≤7/20 then .middle else .high
  have htotal : delta C.theta G+delta C.theta D=t := rfl
  have hb : b≠.low := by dsimp [b]; split_ifs <;> decide
  obtain ⟨ht0,hP,hN⟩ := ExceptionalContactBlocks.original_budgets hab
    (k b t) (ell b t) (c b t) (eta b t) t (delta C.theta G) (delta C.theta D)
    hvar hG hD htotal
  have hP0 : 0≤∑i,(ExceptionalContactBlocks.blocks C ab (k b t) (ell b t) (c b t)
      (eta b t) (delta C.theta G) (delta C.theta D) i).P :=
    Finset.sum_nonneg (fun i _ => (ExceptionalContactBlocks.blocks C ab (k b t) (ell b t) (c b t)
      (eta b t) (delta C.theta G) (delta C.theta D) i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain b := by
    dsimp [b]
    split_ifs with hh
    · exact ⟨hlarge,hh⟩
    · exact ⟨(lt_of_not_ge hh).le,htcap.2⟩
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by dsimp [t]; linarith⟩
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  rcases ranges ht with ⟨hk,hl,hl1,hc0,hc1,heta⟩
  have hconc := ExceptionalContactStress.concave ab (l := ell b t) (c := c b t) hR hRsq hk heta
    htcap hC.sorted hcCap ha hEy
  obtain ⟨h0,h1⟩ := fixed_endpoints hb hab hR (by simpa only [hR2] using hQL)
    (by simpa only [hR2] using hQU) ht hC.sorted hc hn ha hvar hG hD htotal hcontact
  have hpos : 0<value C ab (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t (delta C.theta G) :=
    (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
      (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) hx)
  have hnec := ExceptionalContactStress.necessary (k := k b t) (eta := eta b t) hab hR
    (by linarith [hk.1]) hl.le hc0.le
    (by linarith [heta.1]) htcap hG hD htotal hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.ExceptionalEBalancedExclusion

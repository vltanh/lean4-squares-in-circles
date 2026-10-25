module

public import SquaresInCircles.Eight.Owners.Exceptional.EBalanced
public import SquaresInCircles.Eight.Owners.Exceptional.ELowEnvelope

/-!
# Eight squares: the two low intervals of the exceptional contact exclusion

The ordinary envelope of the low family covers `[0, 0.18]`; only its endpoint scalar has the
critical gap. On the two strict intervals `[0, 1/10]` and `[4/25, 9/50]` (`intervals`) the endpoint
scalars are positive (`scalar_endpoints`), which excludes the exceptional contact there
(`ExceptionalELowExclusion.original_false`). With the middle and high bands this excludes it
outside the critical strip (`ExceptionalEOutside.original_false`), for the points, radius, signed
angles and weak owners of the cycle.
-/

section
/-!
## Original exceptional-contact exclusion for total angle at least .18

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalELowExclusion
open Candidate ExceptionalECoefficients ExceptionalContactStress ExceptionalELowEnvelope
open OrdinaryAngleConcavity

def intervals : Set ℝ := Icc 0 (1/10) ∪ Icc (4/25) (9/50)

theorem family_domain {t : ℝ} (ht : t∈intervals) : t∈domain .low := by
  rcases ht with ht | ht <;> exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

theorem scalar_endpoints {R t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qTrial)
    (ht : t∈intervals) :
    0<ExceptionalContactSupport.atE R (k .low t) (ell .low t) (c .low t) (eta .low t) t+
      V R (ell .low t) (c .low t) t ∧
    0<ExceptionalContactSupport.atG R (k .low t) (ell .low t) (c .low t) (eta .low t) t+
      V R (ell .low t) (c .low t) t := by
  have hf := family_domain ht
  have hE : 0<ExceptionalContactSupport.atE R (k .low t) (ell .low t) (c .low t) (eta .low t) t+
      V R (ell .low t) (c .low t) t := by
    rcases ht with ht | ht
    · have hh := ExceptionalETaylor.endpoint_positive .lowZero (t := t)
        (by
          norm_num [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
            ExceptionalEPolynomials.length] at ht ⊢
          exact ht) hR hQU
      simpa [ExceptionalEPolynomials.band,ExceptionalEPolynomials.negativeIndex,
        ExceptionalEScalarData.charge,ExceptionalEScalarData.firstData,ExceptionalEScalarData.secondData,
        ExceptionalEScalarData.nuData,SingleAngleConcavity.Vnu,V] using hh
    · have hh := ExceptionalETaylor.endpoint_positive .lowReturn (t := t)
        (by
          norm_num [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
            ExceptionalEPolynomials.length] at ht ⊢
          exact ht) hR hQU
      simpa [ExceptionalEPolynomials.band,ExceptionalEPolynomials.negativeIndex,
        ExceptionalEScalarData.charge,ExceptionalEScalarData.firstData,ExceptionalEScalarData.secondData,
        ExceptionalEScalarData.nuData,SingleAngleConcavity.Vnu,V] using hh
  rcases ranges hf with ⟨hk,hl,hl1,hc,hc1,heta⟩
  have hcompare := ExceptionalContactSupport.E_le_G (l := ell .low t) (c := c .low t) hR
    ⟨by linarith [hk.1],hk.2⟩
    (low_tilt hf (show t∈Icc 0 t from ⟨hf.1,le_rfl⟩)).1
    (contactScalar_le_three hR hQL heta.2 (angle hf))
  exact ⟨hE,by linarith⟩

theorem fixed_endpoints {C : SignedCycle} {ab : Fin 4} {R t : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qTrial)
    (ht : t∈intervals) (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) (hcontact : Contact C) :
    0<value C ab R (k .low t) (ell .low t) (c .low t) (eta .low t) t 0 ∧
      0<value C ab R (k .low t) (ell .low t) (c .low t) (eta .low t) t t := by
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hf := family_domain ht
  have hd := angle hf
  have heta := (ranges hf).2.2.2.2.2
  have he0 : 0≤eta .low t := by linarith [heta.1]
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,hf.1⟩
  have hright : t∈Icc 0 t := ⟨hf.1,le_rfl⟩
  have hL0 := original_increment hab hR hQL hcap hf hz hright ha hvar hG hD htotal
  have hL1 := original_increment hab hR hQL hcap hf hright hz ha hvar hG hD htotal
  have hv0 := ExceptionalContactSupport.value_lower (k := k .low t) (l := ell .low t)
    (c := c .low t) hab hR he0 hd hz hs hc hn ha hcontact
  have hv1 := ExceptionalContactSupport.value_lower (k := k .low t) (l := ell .low t)
    (c := c .low t) hab hR he0 hd hright hs hc hn ha hcontact
  rw [sub_zero,ExceptionalContactSupport.baseline_at_E hd] at hv0
  rw [sub_self,ExceptionalContactSupport.baseline_at_G hd] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hR hQL hQU ht
  constructor <;> linarith

theorem original_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈intervals)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  let t := delta C.theta G+delta C.theta D
  have htotal : delta C.theta G+delta C.theta D=t := rfl
  have ht' : t∈intervals := ht
  have hd := angle (family_domain ht')
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by dsimp [t]; linarith⟩
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  rcases ranges (family_domain ht') with ⟨hk,hl,hl1,hc0,hc1,heta⟩
  have hconc := ExceptionalContactStress.concave ab (l := ell .low t) (c := c .low t) hR hRsq hk heta hd hC.sorted hcCap ha hEy
  obtain ⟨h0,h1⟩ := fixed_endpoints hab hR (by simpa only [hR2] using hQL)
    (by simpa only [hR2] using hQU) ht' hC.sorted hc hn ha hvar hG hD htotal hcontact
  have hpos := (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr hd.1) (right_mem_Icc.mpr hd.1) hx)
  have hnec := ExceptionalContactStress.necessary (k := k .low t) (eta := eta .low t) hab hR (by linarith [hk.1]) hl.le hc0.le
    (by linarith [heta.1]) hd hG hD htotal hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.ExceptionalELowExclusion

namespace SquaresInCircles.Eight.ExceptionalEOutside
open Candidate ExceptionalContactStress

/-- The exceptional contact is impossible outside the critical strip, weak ties and `x = 0`
included; the critical strip is handled by the sharp family. -/
theorem original_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (houtside : delta C.theta G+delta C.theta D≤1/10 ∨
      4/25≤delta C.theta G+delta C.theta D)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  rcases houtside with hsmall | hlarge
  · exact ExceptionalELowExclusion.original_false hQL hQU hC hn hvar hab hG hD
      (Or.inl ⟨by linarith,hsmall⟩) hEy hcontact hf
  · by_cases hh : delta C.theta G+delta C.theta D≤9/50
    · exact ExceptionalELowExclusion.original_false hQL hQU hC hn hvar hab hG hD
        (Or.inr ⟨hlarge,hh⟩) hEy hcontact hf
    · exact ExceptionalEBalancedExclusion.original_false hQL hQU hC hn hvar hab hG hD
        (lt_of_not_ge hh).le hEy hcontact hf

end SquaresInCircles.Eight.ExceptionalEOutside
end
end
end

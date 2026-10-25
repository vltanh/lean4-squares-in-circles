module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTEnvelope

/-!
# Actual positive-T exceptional-contact exclusion outside the sharp strip

Uncompiled source. Both complete fixed-z faces use the same original
coordinates and the same arbitrary EH contact. Their strict scalar
reserve and the concave G/E split contradict the original seven weak
witnesses at the actual common ceiling. No radial assumption is used.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOutside
open Candidate ExceptionalPositiveTScalarModel ExceptionalPositiveTOrdinaryData
open ExceptionalContactStress PositiveAngularEnvelope

theorem baseline_eq (s : ScalarCase) (R t z : ℝ) :
    baseline s R t z=ExceptionalPositiveTStress.baseline s.td R
      (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
      z (x s t z) (ExceptionalPositiveTScalarModel.e s t z) := by
  simp [baseline,ExceptionalPositiveTStress.baseline,SoleEStress.zeroNorms,
    first,second,n,m,p,ExceptionalPositiveTStress.bWeight,ExceptionalPositiveTStress.tWeight,
    Fin.sum_univ_succ,add_assoc]

theorem increment_eq (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) :
    ExceptionalPositiveTBlocks.increment C ab s.td (weights s t z) R=
      ExceptionalPositiveTStress.increment C ab s.td R
        (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
        z (x s t z) (ExceptionalPositiveTScalarModel.e s t z) := rfl

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {q t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : ExceptionalPositiveTStress.primary C s.td=z)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hT : 0≤ExceptionalPositiveTStress.primary C s.td)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C s.td=t)
    (hcontact : Contact C) :
    0<ExceptionalPositiveTStress.value C ab s.td (Real.sqrt q)
      (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
      t z (x s t z) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have hR := Real.sqrt_nonneg q
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hQL
  have hRU : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hpure (i : Fin 4) : 77/1000000-baseline s (Real.sqrt q) t z≤
      SingleAngleConcavity.pure (single s i) (Real.sqrt q) (small s t z i) (large s t z i)
        (actualNu s t z i) t := by
    have hs := ExceptionalPositiveTScalar.actual_radius_positive (charged s t z i) hQU ht hz
    have hl := pure_scalar_lower s (R:=Real.sqrt q) ht hz i
    linarith
  have hi := ExceptionalPositiveTEnvelope.original_increment s hab hR hRL hRU ht hz
    ha hvar hG hD hT htotal hpure
  have hx : x s t z∈Icc 0 (t-z) := by
    cases h : s.atG <;> simp [x,h] <;> linarith [hz.2]
  have he : t-z-x s t z=ExceptionalPositiveTScalarModel.e s t z := by
    cases h : s.atG <;> simp [x,ExceptionalPositiveTScalarModel.e,h]
  have hl := ExceptionalPositiveTSupport.value_lower s.td hab hR
    (coefficient_positive ht hz).2.2.2 (angle ht) hz hx hsource hC.sorted hc hn ha hcontact
    (k:=k s.family t z) (l:=ell s.family t z) (c:=c s.family t z)
  rw [he,← baseline_eq,← increment_eq] at hl
  linarith

def choose (t : ℝ) : Family :=
  if t≤1/10 then .lowZero else if t≤9/50 then .lowAfter else if t≤7/20 then .middle else .high
theorem choose_mem {t : ℝ} (ht : t∈Icc 0 frameCap) (houtside : t≤1/10 ∨ 4/25≤t) :
    t∈domain (choose t) := by
  have h2 : t≤7/10 := ht.2
  dsimp [choose]
  split_ifs <;> norm_num [domain,left,right] <;> constructor <;>
    rcases houtside with h | h <;> linarith [ht.1,h2]

theorem original_false {C : SignedCycle} {ab : Fin 4} (td : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hT : 0≤ExceptionalPositiveTStress.primary C td) (hEy : 0≤(C.point E).y)
    (hcontact : Contact C)
    (houtside : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td≤1/10 ∨
      4/25≤delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab
      (ExceptionalPositiveTStress.btOwner td) (ExceptionalPositiveTStress.tdOwner td) 3 0 i)) : False := by
  let z := ExceptionalPositiveTStress.primary C td
  let t := delta C.theta G+delta C.theta D+z
  let f := choose t
  have htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t := rfl
  have htcap := (ExceptionalPositiveTBlocks.original_budgets hab td
    ⟨0,0,0,0,0,0⟩ hvar hG hD hT htotal).1
  have ht : t∈domain f := choose_mem htcap houtside
  have hz : z∈Icc 0 t := ⟨hT,by dsimp [t]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by dsimp [t]; linarith⟩
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hweights := coefficient_positive ht hz
  have hsplit := split_bounds ht hz
  have hconc := ExceptionalPositiveTStress.concave ab td hR hRsq hsplit.1 hsplit.2 htcap hz
    hC.sorted hcCap ha hEy (l:=ell f t z) (c:=c f t z)
  have h0 : 0<ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (k f t z) (ell f t z) (c f t z) (eta f t) t z 0 := by
    have hh := endpoint_positive (C:=C) (ab:=ab) ⟨f,td,false,0,false⟩ hab hQL hQU ht hz rfl
      hC hn hvar hG hD hT htotal hcontact
    simpa only [x,Bool.false_eq_true,if_false] using hh
  have h1 : 0<ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (k f t z) (ell f t z) (c f t z) (eta f t) t z (t-z) := by
    have hh := endpoint_positive (C:=C) (ab:=ab) ⟨f,td,true,0,false⟩ hab hQL hQU ht hz rfl
      hC hn hvar hG hD hT htotal hcontact
    simpa only [x,if_true] using hh
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (t-z) from ⟨le_rfl,by linarith [hz.2]⟩)
    (show t-z∈Icc 0 (t-z) from ⟨by linarith [hz.2],le_rfl⟩) hx
  have hpos := (lt_min h0 h1).trans_le hmin
  have hnec := ExceptionalPositiveTStress.necessary td hab hR hweights.1.le
    hweights.2.1.le hweights.2.2.1.le hweights.2.2.2 htcap hz rfl hG hD
    (by simpa only [z] using htotal) hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOutside

module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTEndpoints
public import SquaresInCircles.Eight.TableFree.CriticalNegativeTExclusion

/-!
# Original-contact exclusion of negative T outside the critical strip

Uncompiled source. The original three signed blocks feed the continuous
envelope, and the original D feeds the sorted support. Concavity is
applied to the literal fixed-source split stress. The final entry cases
reselect an available secondary owner at the same state or use the
actual short flat-T contact. No source point or frame is replaced.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTExclusion
open Candidate ExceptionalECoefficients ExceptionalContactStress ExceptionalNegativeTStress
open ExceptionalEBalanced (endpointX endpointE endpoints_mem)
open ExceptionalNegativeTOrdinaryData ExceptionalNegativeTEnvelope ExceptionalNegativeTEndpoints
open CriticalNegativeTOrdinaryData (shortDomain short_small)
open NegativeSecondaryEExclusion

theorem original_lower (face : Bool) {C : SignedCycle} {ab : Fin 4} {td : Bool}
    {R t s : ℝ} {b : Band} (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (ht : t∈domain b)
    (hs : s∈shortDomain td) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (halign : td=false → delta C.theta T=0) :
    lowerEnvelope b R t face s≤ increment C ab td R (k b t) (ell b t) (c b t) (eta b t) s
      (endpointX face t) (endpointE face t) := by
  let blocks := CriticalNegativeTBlocks.blocks C ab td (k b t) (ell b t) (c b t) (eta b t) s
    (endpointX face t) (endpointE face t)
  have hs0 := (short_small hs).1
  obtain ⟨hP,hN⟩ := CriticalNegativeTBlocks.original_budgets hab td (k b t) (ell b t) (c b t)
    (eta b t) (endpointX face t) (endpointE face t) hvar hG hD hs0 hsource htotal halign
  have hlow := ordinary_lower face (fun i => (blocks i).P) (fun i => (blocks i).N)
    hR hQL hQU ht hs (fun i => (blocks i).P_nonneg) (fun i => (blocks i).N_nonneg) hP hN
    (CriticalNegativeTBlocks.single_parts C ab td (k b t) (ell b t) (c b t) (eta b t) s
      (endpointX face t) (endpointE face t))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    CriticalNegativeTBlocks.block_minorant (R := R) (angle ht).1 hs0
      (fun i => (actual_conditions face ht hs i).1.le) ha hP hN i)
  rw [CriticalNegativeTBlocks.increment_eq td R (k b t) (ell b t) (c b t) (eta b t) s
    (endpointX face t) (endpointE face t) hab halign]
  exact hlow.trans hsum

theorem fixed_endpoint (face td : Bool) {C : SignedCycle} {ab : Fin 4} {q t s : ℝ} {b : Band}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain b) (hout : t≤1/10 ∨ 4/25≤t) (hs : s∈shortDomain td)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (hflat : (C.point T).a=7/12) (halign : td=false → delta C.theta T=0)
    (hcontact : Contact C) :
    0<value C ab td (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t s (endpointX face t) := by
  have hq : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsq := Real.sq_sqrt hq
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hRQL : qLow≤(Real.sqrt q)^2 := by simpa [hsq] using hQL
  have hRQU : (Real.sqrt q)^2≤qTrial := by simpa [hsq] using hQU
  have hRcap : (Real.sqrt q)^2≤qCap := by simpa [hsq] using hcap
  have hx := (endpoints_mem face (angle ht).1).1
  have he : t-endpointX face t=endpointE face t := by cases face <;> simp [endpointX,endpointE]
  have hi := original_lower face hab (Real.sqrt_nonneg q) hRQL hRcap ht hs ha hvar hG hD hsource htotal halign
  have hv := ExceptionalNegativeTSortedStress.source_lower td hab hQL hcap ht hx hs hC.sorted hC.contained
    hn ha hcontact hsource hflat halign
  rw [he] at hv
  have hb : ExceptionalContactSupport.baseline (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t)
      (endpointX face t) (endpointE face t)=base b (Real.sqrt q) t face := by
    cases face <;> simp [endpointX,endpointE,base,
      ExceptionalContactSupport.baseline_at_E (angle ht),ExceptionalContactSupport.baseline_at_G (angle ht)]
  rw [hb] at hv
  have hp := total_positive face td (Real.sqrt_nonneg q) hRQL hRQU ht hout hs
  linarith

theorem flat_false {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool) {t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hout : t≤1/10 ∨ 4/25≤t) (htotal : delta C.theta G+delta C.theta D=t)
    (hs : s∈shortDomain td) (hsource : primary C td= -s)
    (hflat : (C.point T).a=7/12) (halign : td=false → delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) : False := by
  let b : Band := if t≤9/50 then .low else if t≤7/20 then .middle else .high
  have ht0 : 0≤t := by linarith
  obtain ⟨hP,hN⟩ := CriticalNegativeTBlocks.original_budgets hab td (k b t) (ell b t) (c b t)
    (eta b t) 0 t hvar hG hD (short_small hs).1 hsource htotal halign
  have hP0 : 0≤∑i,(CriticalNegativeTBlocks.blocks C ab td (k b t) (ell b t) (c b t) (eta b t) s 0 t i).P :=
    Finset.sum_nonneg (fun i _ => (CriticalNegativeTBlocks.blocks C ab td (k b t) (ell b t) (c b t)
      (eta b t) s 0 t i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain b := by
    dsimp [b]
    split_ifs <;> constructor <;> first | exact ht0 | exact htcap.2 | linarith
  have hq : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsq := Real.sq_sqrt hq
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hRcap : (Real.sqrt q)^2≤qCap := by simpa [hsq] using hcap
  have hc : ∀i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa [hsq] using hC.contained
  have hcCap : ∀i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have h0 := fixed_endpoint false td hab hQL hQU ht hout hs hC hn ha hvar hG hD
    hsource htotal hflat halign hcontact
  have h1 := fixed_endpoint true td hab hQL hQU ht hout hs hC hn ha hvar hG hD
    hsource htotal hflat halign hcontact
  simp only [endpointX,Bool.false_eq_true,if_false,if_true] at h0 h1
  rcases ranges ht with ⟨hk,hl,hl1,hc0,hc1,heta⟩
  have hconc := ExceptionalNegativeTStress.concave (l:=ell b t) (c:=c b t) (s:=s) ab td (Real.sqrt_nonneg q) hRcap hk heta htcap
    hC.sorted hcCap ha hEy
  have hpos := (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) hx)
  have hnec := ExceptionalNegativeTStress.necessary (k:=k b t) (l:=ell b t) (c:=c b t) (eta:=eta b t) (s:=s) td hab (Real.sqrt_nonneg q)
    (by linarith [hk.1]) hl.le hc0.le (by linarith [heta.1]) htcap (short_small hs)
    hG hD htotal hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : False := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hsource : delta C.theta T= -s := by dsimp [s]; ring
  have hBT := (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hsource]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  obtain hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_TD_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core T) (hC.core D) hcap hn.D_nonpos hs hBT hTD
  · have hsame : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hsource] using hsecondary)
    exact ExceptionalEOutside.original_false hQL hQU hC hn hvar hab hG hD hout hEy hcontact
      (SoleNegativeTExclusion.reselect_TD hf hsame)
  · exact flat_false true hQL hQU hC hn hvar hab hG hD hout rfl
      (show s∈shortDomain true from ⟨hs.1.le,hshort.le⟩) hsource hflat
      (by intro h; cases h) hEy hcontact hf

theorem negative_BT_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact ExceptionalEOutside.original_false hQL hQU hC hn hvar hab hG hD hout hEy hcontact
      (SoleNegativeTExclusion.reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hsource : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hsource]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hsource] using hh))
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hcap hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact flat_false false hQL hQU hC hn hvar hab hG hD hout rfl
    (show s∈shortDomain false from ⟨hs.1.le,hshort.le⟩) hsource hflat
    (fun _ => halign) hEy hcontact hf

theorem negative_TD_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : delta C.theta G=0 := by
  by_cases hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D
  · exact (negative_TD_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD hout hTb hT hEy hcontact hf).elim
  · push_neg at hout
    exact CriticalNegativeTExclusion.negative_TD_G_zero hd hsharp hq hC hn hvar hab hG hD
      ⟨hout.1.le,hout.2.le⟩ hTb hT hEy hcontact hf

theorem negative_BT_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : delta C.theta G=0 := by
  by_cases hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D
  · exact (negative_BT_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD hout hTb hB halign hEy hcontact hf).elim
  · push_neg at hout
    exact CriticalNegativeTExclusion.negative_BT_G_zero hd hsharp hq hC hn hvar hab hG hD
      ⟨hout.1.le,hout.2.le⟩ hTb hB halign hEy hcontact hf

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTExclusion

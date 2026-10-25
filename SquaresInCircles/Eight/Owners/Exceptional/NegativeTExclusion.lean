module

public import SquaresInCircles.Eight.Owners.Critical.PositiveTExclusion
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTEndpoints
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTSortedGain

/-!
# Eight squares: negative T at the exceptional contact outside the critical strip

The three signed blocks of the cycle feed the continuous envelope, and D feeds the sorted support;
concavity is applied to the split stress at the fixed points of the cycle (`fixed_endpoint`).
Outside the critical strip a negative T primary is then impossible (`flat_false`,
`negative_TD_false`, `negative_BT_false`): the entry selects an available secondary owner again at
the same state, or uses the short contact of T on the flat core, and no point or frame moves. With
the critical strip, a negative T primary forces the G error to vanish (`negative_TD_G_zero`,
`negative_BT_G_zero`).
-/

section
/-!
## Sorted-D improvement of the literal original contact stress

D's actual force has no ordinary rotation in either
negative-primary row. Its sorted support is substituted only after the
fixed-source G/E split expression has been formed. Every source point,
the original EH0 contact and the original q remain unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTSortedStress
open Candidate SignedStress ActualSortedSupport PositiveAngularEnvelope ActualCoreEBlocks
open ExceptionalContactStress ExceptionalNegativeTStress ExceptionalECoefficients
open CriticalNegativeTOrdinaryData (bWeight tWeight shortDomain short_small)
open ExceptionalNegativeTSortedGain

theorem D_force {C : SignedCycle} (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (halign : td=false → delta C.theta T=0) :
    forces C ab td k l c eta s x e D=(1,-tWeight td c s) := by
  rw [ExceptionalNegativeTStress.forces,SoleEStress.force_D (td_cases td) (Or.inr rfl)]
  cases td <;> simp [tdOwner,ordinaryDE,rotatedPair,halign]

theorem anchorWork_sorted {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q c s : ℝ} (k l eta x e : ℝ) (hab : ab=0 ∨ ab=2)
    (hq : 0≤q) (hc0 : 0<c) (hs : s∈Icc 0 frameCap)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained q)
    (hn : C.NormalAnchors) (halign : td=false → delta C.theta T=0) :
    anchorWork C ab td k l c eta s x e+
      full q 1 (tWeight td c s)-ActualSortedSupport.support q 1 (tWeight td c s)≤
        anchorSupport C ab td (Real.sqrt q) k l c eta s x e := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have ht0 : 0<tWeight td c s := by cases td <;> simp [tWeight] <;> positivity
  have hD := actual_negative_support hq (hpoints D) hn.D_nonpos (hcircle D)
    (show 0≤1+tWeight td c s by positivity)
  have hFD := D_force ab td k l c eta s x e halign
  have hDwork : work (forces C ab td k l c eta s x e D) (C.point D)≤
      ActualSortedSupport.support q 1 (tWeight td c s) := by
    rw [hFD]
    dsimp [work] at *
    linarith
  have hDfull : SecondaryEStress.signedSupport (Real.sqrt q) (-1)
      (ExceptionalNegativeTStress.forces C ab td k l c eta s x e D)=
      full q 1 (tWeight td c s) := by
    rw [hFD]
    simp only [SecondaryEStress.signedSupport,full,neg_sq,one_pow]
    ring
  have hH := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point H).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle H)
    (Or.inl rfl) (by simp [abs_of_nonneg hn.H_nonneg]) (forces C ab td k l c eta s x e H)
  have hA := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point A).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle A)
    (Or.inl rfl) (by simp [abs_of_nonneg hn.A_nonneg]) (forces C ab td k l c eta s x e A)
  have hB := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point B).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle B)
    (Or.inr rfl) (by simp [abs_of_nonpos hn.B_nonpos]) (forces C ab td k l c eta s x e B)
  have hsum := SoleEStress.sum_bounds C hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e) (Real.sqrt q)
  simp only [SoleEStress.bound,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at hsum
  dsimp only [ExceptionalNegativeTStress.anchorWork,ExceptionalNegativeTStress.anchorSupport,
    ExceptionalNegativeTStress.forces,SecondaryEStress.signedSupport] at *
  linarith

theorem improved_value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q k l c eta t s x : ℝ} (hab : ab=0 ∨ ab=2) (hq : 0≤q)
    (hc0 : 0<c) (heta : 0≤eta) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hs : s∈Icc 0 frameCap) (hpoints : ∀ i,(C.point i).Sorted)
    (hcircle : ∀ i,(C.point i).Contained q) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C)
    (hsource : primary C td= -s) (hflat : (C.point T).a=7/12)
    (halign : td=false → delta C.theta T=0) :
    ExceptionalContactSupport.baseline (Real.sqrt q) k l c eta x (t-x)+
      gain td (Real.sqrt q) l c s+increment C ab td (Real.sqrt q) k l c eta s x (t-x)+
        full q 1 (tWeight td c s)-ActualSortedSupport.support q 1 (tWeight td c s)≤
          value C ab td (Real.sqrt q) k l c eta t s x := by
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hw := anchorWork_sorted td k l eta x (t-x) hab hq hc0 hs hpoints hcircle hn halign
  have hT := T_work ab td k l c eta x (t-x) hs hsource hflat
  have hE := ExceptionalContactSupport.eWork_le (Real.sqrt_nonneg q) heta he
    (hpoints E) (show (C.point E).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle E)
  have hid := decomposition td (Real.sqrt q) k l c eta x (t-x) hab ha hs hsource halign
  rw [value_eq_stress td (Real.sqrt q) k l c eta s hab ht hx hn hcontact]
  dsimp only [ExceptionalNegativeTStress.stress]
  linarith

theorem coefficient_ratio {b : Band} {t : ℝ} (ht : t∈domain b) :
    117/200≤ell b t/c b t := by
  have hc := (ranges ht).2.2.2.1
  apply (le_div_iff₀ hc).2
  by_cases hb : b=.low
  · subst b
    have hh := (low_correlations ht).1
    nlinarith [mul_nonneg ht.1 hc.le]
  · have hh := (balanced_bounds hb ht).2.2.2.2.2.1
    nlinarith

theorem source_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q t s x : ℝ} {b : Band} (hab : ab=0 ∨ ab=2)
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain b) (hx : x∈Icc 0 t)
    (hs : s∈shortDomain td) (hpoints : ∀ i,(C.point i).Sorted)
    (hcircle : ∀ i,(C.point i).Contained q) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C)
    (hsource : primary C td= -s) (hflat : (C.point T).a=7/12)
    (halign : td=false → delta C.theta T=0) :
    ExceptionalContactSupport.baseline (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) x (t-x)+
      correction b td t+lowerGain b td t s+
        increment C ab td (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) s x (t-x)≤
          value C ab td (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t s x := by
  have hq : 0≤q := by norm_num [qLow] at hQL; linarith
  have hc := (ranges ht).2.2.2.1
  have he : 0≤eta b t := by linarith [(ranges ht).2.2.2.2.2.1]
  cases td
  · have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hh := ExceptionalNegativeTStress.value_lower (k := k b t) (l := ell b t) (c := c b t)
      false hab (Real.sqrt_nonneg q) he (angle ht) hx
      (short_small hs) hpoints (fun i => by simpa [Real.sq_sqrt hq] using hcircle i)
      hn ha hcontact hsource hflat halign
    have hg : (21/20)*c b t*s≤gain false (Real.sqrt q) (ell b t) (c b t) s := by
      by_cases hz : s=0
      · simp [hz,gain,FlatTStress.secantCharge]
      · have hs0 : 0<s := lt_of_le_of_ne hs'.1 (Ne.symm hz)
        have hgain := mul_lt_mul_of_pos_left
          (SoleNegativeTGain.BT_strict hq hQU (coefficient_ratio ht) ⟨hs0,hs'.2⟩) hc
        simp only [gain,Bool.false_eq_true,↓reduceIte]
        rw [CriticalNegativeTCurvature.charge_eq_gain hc (short_small hs)]
        linarith
    simpa only [correction,Bool.false_and,Bool.false_eq_true,↓reduceIte,lowerGain] using
      (by linarith :
      ExceptionalContactSupport.baseline (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) x (t-x)+
        0+(21/20)*c b t*s+increment C ab false (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) s x (t-x)≤
          value C ab false (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t s x)
  · have hs' : s∈Icc 0 (3/10:ℝ) := by simpa [shortDomain] using hs
    have hh := improved_value_lower (k := k b t) (l := ell b t) true hab hq hc he (angle ht) hx
      (short_small hs)
      hpoints hcircle hn ha hcontact hsource hflat halign
    have hg := corrected_gain hQL hQU ht hs'
    simp only [tWeight,↓reduceIte] at hh
    simp only [lowerGain,↓reduceIte]
    linarith

end SquaresInCircles.Eight.ExceptionalNegativeTSortedStress
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTExclusion
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
  simp only [endpointX,Bool.false_eq_true,ite_false,ite_true] at h0 h1
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

theorem negative_TD_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : delta C.theta G=0 := by
  by_cases hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D
  · exact (negative_TD_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD hout hTb hT hEy hcontact hf).elim
  · push Not at hout
    exact CriticalNegativeTExclusion.negative_TD_G_zero hd hsharp hq hC hn hvar hab hG hD
      ⟨hout.1.le,hout.2.le⟩ hTb hT hEy hcontact hf

theorem negative_BT_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : delta C.theta G=0 := by
  by_cases hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D
  · exact (negative_BT_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD hout hTb hB halign hEy hcontact hf).elim
  · push Not at hout
    exact CriticalNegativeTExclusion.negative_BT_G_zero hd hsharp hq hC hn hvar hab hG hD
      ⟨hout.1.le,hout.2.le⟩ hTb hB halign hEy hcontact hf

end SquaresInCircles.Eight.ExceptionalNegativeTExclusion
end
end
end

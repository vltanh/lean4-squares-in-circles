module

public import SquaresInCircles.Eight.TableFree.CriticalNegativeTBlocks
public import SquaresInCircles.Eight.TableFree.SoleNegativeTExclusion

/-!
# Sharp original-contact exclusion of genuine negative T

Uncompiled source. Local entry is performed at the original radius q.
An available secondary owner is reselected at the same points and
frames. Otherwise the actual flat T work gives strict endpoint gain at
the stationary sharp support radius. The result includes both AB weak
owners, arbitrary G sign, arbitrary original EH error, and every signed
ordinary allocation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTExclusion
open Candidate CriticalEExclusion CriticalECoefficients ExceptionalContactStress
open CriticalNegativeTOrdinaryData CriticalNegativeTContinuation ExceptionalNegativeTStress
open NegativeSecondaryEExclusion PositiveAngularEnvelope

theorem flat_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool) {t s : ℝ}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (htotal : delta C.theta G+delta C.theta D=t)
    (hs : s∈shortDomain td) (hs0 : 0<s) (hsource : primary C td= -s)
    (hflat : (C.point T).a=7/12) (halign : td=false → delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) : False := by
  have h := coefficient_bounds hsharp ht
  have hr := radius_bounds hsharp
  have hq0 : 0≤d.q := by norm_num [qLow] at hsharp; linarith [hsharp.1]
  have hsq := Real.sq_sqrt hq0
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by
    intro i
    rw [hsq]
    exact (hC.contained i).trans hq
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => ((hC.contained i).trans hq).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,h.angle.1⟩
  have ht' : t∈Icc 0 t := ⟨h.angle.1,le_rfl⟩
  have hgain : OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t<
      gain td (Real.sqrt d.q) (L d.q t) (Cc d.q t) s+
        lowerEnvelope (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) t s := by
    cases td
    · simpa [gain,CriticalNegativeTPolynomials.shortAngle] using
        BT_gain hsharp ht (show s∈Ioc 0 CriticalNegativeTPolynomials.shortAngle from
          ⟨hs0,by simpa [shortDomain,CriticalNegativeTPolynomials.shortAngle] using hs.2⟩)
    · simpa [gain] using TD_gain hsharp ht
        (show s∈Ioc 0 (3/10:ℝ) from ⟨hs0,by simpa [shortDomain] using hs.2⟩)
  have hinc0 := CriticalNegativeTBlocks.original_lower hab hr.1 hr.2.1 hr.2.2.1 h hz ht'
    hs ha hvar hG hD hsource htotal halign
  have hinc1 := CriticalNegativeTBlocks.original_lower hab hr.1 hr.2.1 hr.2.2.1 h ht' hz
    hs ha hvar hG hD hsource htotal halign
  have hv0 := ExceptionalNegativeTStress.value_lower (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) td hab hr.1
    (show 0≤Eta d.q t by linarith [h.eta_lower]) h.angle hz (short_small hs)
    hC.sorted hc hn ha hcontact hsource hflat halign
  have hv1 := ExceptionalNegativeTStress.value_lower (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) td hab hr.1
    (show 0≤Eta d.q t by linarith [h.eta_lower]) h.angle ht' (short_small hs)
    hC.sorted hc hn ha hcontact hsource hflat halign
  rw [sub_zero,ExceptionalContactSupport.baseline_at_E h.angle] at hv0
  rw [sub_self,ExceptionalContactSupport.baseline_at_G h.angle] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hd hsharp ht
  have h0 : 0<ExceptionalNegativeTStress.value C ab td (Real.sqrt d.q)
      (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t s 0 := by linarith
  have h1 : 0<ExceptionalNegativeTStress.value C ab td (Real.sqrt d.q)
      (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t s t := by linarith
  have hconc := ExceptionalNegativeTStress.concave (l:=L d.q t) (c:=Cc d.q t) (s:=s) ab td hr.1 hr.2.2.1
    (show K d.q t∈Icc (431/500:ℝ) 1 by constructor <;> linarith [h.k_lower,h.k_upper])
    (show Eta d.q t∈Icc (1/4:ℝ) (327/1000) by constructor <;> linarith [h.eta_lower,h.eta_upper])
    h.angle hC.sorted hcCap ha hEy
  have hpos := (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc hz ht' hx)
  have hnec := ExceptionalNegativeTStress.necessary (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) (eta:=Eta d.q t) (s:=s) td hab hr.1
    h.order.1.le h.ell_pos.le (by linarith [h.c_lower]) (by linarith [h.eta_lower])
    h.angle (short_small hs) hG hD htotal hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

theorem negative_TD_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : delta C.theta G=0 := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hsource : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hsource]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hcap : q≤qCap := hq.trans (hsharp.2.trans uniform_radius_order.2.2.1.le)
  obtain hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_TD_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core T) (hC.core D) hcap hn.D_nonpos hs hBT hTD
  · have hsame : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hsource] using hsecondary)
    exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact
      (SoleNegativeTExclusion.reselect_TD hf hsame)
  · exact (flat_false hd hsharp true hq hC hn hvar hab hG hD ht rfl
      (show s∈shortDomain true from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
      (by intro h; cases h) hEy hcontact hf).elim

theorem negative_BT_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : delta C.theta G=0 := by
  by_cases hsecondary : C.Feasible B 2
  · exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact
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
  have hcap : q≤qCap := hq.trans (hsharp.2.trans uniform_radius_order.2.2.1.le)
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hcap hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact (flat_false hd hsharp false hq hC hn hvar hab hG hD ht rfl
    (show s∈shortDomain false from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
    (fun _ => halign) hEy hcontact hf).elim

end SquaresInCircles.Eight.TableFree.CriticalNegativeTExclusion

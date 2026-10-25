module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNonnegative
public import SquaresInCircles.Eight.Owners.GA.High.BT2NegativeANonnegativeESource

/-!
# Eight squares: a core E, negative A and nonnegative E, with positive TD2

E, on the core curve, is normalized on a source domain before A moves. On the cycle with A moved,
the selected DE and EH axes of E, its selected total and the signed T error are those before the
move of A.

A negative flat GA3 or AB2 normal form of A either has the secondary GA2 or AB0 feasible at the
same state, and then the reselection gives the stress of nonnegative totals
`reduced_nonnegative_AE_false`, or satisfies the entry cut of A (`NegativeA.GA_entry`). In the
second case the short/long-E contradiction `negative_A_nonnegative_E_positive_TD2_raw_false`
applies to every radial kind and owner flag of E (`negative_A_nonnegative_E_positive_TD2_false`).
The cycle with A moved is used only as a signed cycle, not as a packing, and weak ties are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

private theorem core_E_nonnegative_as_charge
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E)) :
    0≤GlobalGA.PairedE.cycleTotal R.A.cycle
      (deFlag R.E.source) (ehFlag R.E.source) := by
  simpa [GlobalGA.PairedE.cycleTotal, GlobalGA.NonnegativeTotals.Source.eTotal,
    GlobalGA.PairedE.total, GlobalGA.PairedE.selected,
    ActualCoreEBlocks.eTotal,
    ActualCoreEBlocks.primaryDE,
    ActualCoreEBlocks.primaryEH,
    de_owner R.E.source,eh_owner R.E.source] using he

/-- The stress `negative_A_nonnegative_E_positive_TD2_raw_false` makes no assumption on the radial
kind of E. -/
private theorem core_negative_A_positive_TD2_with_entry_false
    (hqU : q≤qCap)
    (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (atG : Bool)
    (hGA : R.A.cycle.Feasible G (if atG then 3 else 2))
    (hAB : R.A.cycle.Feasible A (if atG then 0 else 2))
    (hflat : (R.A.cycle.point A).a=7/12)
    (hy : 0≤(R.A.cycle.point A).y)
    (hcut : (R.A.cycle.point A).y≤ if atG then 39/250 else 1/2)
    (s : ℝ)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError R.A.cycle atG= -s) :
    False := by
  have hH : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]; exact R.E.source.H_positive.le
  have hG : (R.A.cycle.point G).y≤0 := by
    rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
  have hB : (R.A.cycle.point B).y≤0 := by
    rw [ATransport.B_point R.A]; exact R.E.source.B_negative.le
  have hD : (R.A.cycle.point D).y≤0 := by
    rw [ATransport.D_point R.A]; exact R.E.source.D_negative.le
  have hDE : R.A.cycle.Feasible D
      (if deFlag R.E.source then 3 else 2) := by
    rw [←de_owner R.E.source]; exact R.DE
  have hEH : R.A.cycle.Feasible E
      (if ehFlag R.E.source then 1 else 0) := by
    rw [←eh_owner R.E.source]; exact R.EH
  have hHG : R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
    (original_HG R.E.source).imp
      (ATransport.HG R.A 0) (ATransport.HG R.A 2)
  exact negative_A_nonnegative_E_positive_TD2_raw_false
    atG (deFlag R.E.source) (ehFlag R.E.source)
    R.A.necessary.sorted R.A.necessary.contained hqU
    hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le)
    hs ha hflat hy hcut (core_E_nonnegative_as_charge R he)
    hz hHG hGA hAB (R.BT2 hBT) (R.TD 2 hTD)
    hDE hEH

/-- A weak secondary GA2 witness at the same state reduces to nonnegative A and E totals, with
neither E nor T moved or reselected. -/
private theorem secondary_GA_core_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hab : R.A.ab=false)
    (hsecondary : R.A.cycle.Feasible G 2) : False := by
  let P : CycleResult q R.E.cycle :=
    { R.A with
      ga := false
      GA := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,
          GlobalGA.PairedE.selected,hab] }
  let S : CoreEFirstResult I := ⟨R.E,P⟩
  have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      P.cycle (deFlag R.E.source) (ehFlag R.E.source) := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected,
      ActualCoreEBlocks.eTotal,
      ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,
      de_owner R.E.source,eh_owner R.E.source] using he
  exact reduced_nonnegative_AE_false S hqU hBT
    (by simp [GlobalGA.NegativeANormalForm.total,
      GlobalGA.PairedE.selected,hab,P,S])
    he'

/-- Likewise a weak secondary AB0 witness at the same state gives a zero A primary total, without
moving A, E, T or any anchor on the circle. -/
private theorem secondary_AB_core_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hga : R.A.ga=false)
    (hsecondary : R.A.cycle.Feasible A 0) : False := by
  let P : CycleResult q R.E.cycle :=
    { R.A with
      ab := false
      AB := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,
          GlobalGA.PairedE.selected,hga] }
  let S : CoreEFirstResult I := ⟨R.E,P⟩
  have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      P.cycle (deFlag R.E.source) (ehFlag R.E.source) := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected,
      ActualCoreEBlocks.eTotal,
      ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,
      de_owner R.E.source,eh_owner R.E.source] using he
  exact reduced_nonnegative_AE_false S hqU hBT
    (by simp [GlobalGA.NegativeANormalForm.total,
      GlobalGA.PairedE.selected,hga,P,S])
    he'

/-- A negative normal form of A with a nonnegative selected E total is impossible on the cycle
with E then A moved, for positive TD2; both negative branches of the flat-A normal form are
covered. -/
theorem negative_A_nonnegative_E_positive_TD2_false
    (hqU : q≤qCap)
    (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hnegative : ¬0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab
      (delta R.A.cycle.theta G) (delta R.A.cycle.theta A)) :
    False := by
  rcases R.A.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
  · exact hnegative hnonneg
  · by_cases hsec : R.A.cycle.Feasible G 2
    · exact secondary_GA_core_false R hqU hBT he ha hsec
    have hG : (R.A.cycle.point G).y≤0 := by
      rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
    have hquarter : quarterFeasible (R.A.cycle.point G) (R.A.cycle.point A)
        (delta R.A.cycle.theta G) 3 := by
      have hh : R.A.cycle.Feasible G 3 := by simpa [hg] using R.A.GA
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,G,A,quarterFeasible,sub_nonneg] using hh
    let s := -(delta R.A.cycle.theta G)
    have hs : s∈Ioc 0 frameCap := by
      dsimp [s]
      constructor
      · linarith [hu.2]
      · simp only [frameCap]
        linarith [hu.1]
    have houterA : (R.A.cycle.point A).y≤0→
        (R.A.cycle.point A).Outer q := by
      intro hh
      linarith [hy.1]
    rcases GlobalGA.NegativeA.GA_entry (R.A.necessary.sorted G)
        (R.A.necessary.contained G) (R.A.necessary.sorted A)
        (R.A.radial A) hqU hG houterA hs
        (by simpa [s,neg_neg] using hquarter) with hsecondary|⟨_,_,hcut,_⟩
    · apply hsec
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,G,A,quarterFeasible,sub_nonneg,s] using hsecondary
    have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut true) := by
      simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta G)∈Icc 0 (1/4:ℝ) by
          constructor <;> linarith [hu.1,hu.2])
    exact core_negative_A_positive_TD2_with_entry_false R hqU
      hBT hTD hz he true (by simpa [hg] using R.A.GA)
      (by simpa [ha] using R.A.AB) hflat hy.1.le hcut.le
      s hs' (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
  · by_cases hsec : R.A.cycle.Feasible A 0
    · exact secondary_AB_core_false R hqU hBT he hg hsec
    let s := -(delta R.A.cycle.theta A)
    have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut false) := by
      simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta A)∈Icc 0 (19/50:ℝ) by
          constructor <;> linarith [hv.1,hv.2])
    exact core_negative_A_positive_TD2_with_entry_false R hqU
      hBT hTD hz he false (by simpa [hg] using R.A.GA)
      (by simpa [ha] using R.A.AB) hflat hy.1.le hy.2.le
      s hs' (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])

end SquaresInCircles.Eight.HighGABT2

module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2ReducedANegativeOuterEPositiveT
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAEntry

/-!
# Complete outer-E terminal for negative A normalization

A is a necessary-system motion, not an original packing. The sole
negative primary either has its *actual same-state* secondary projection
feasible (hence its selected primary total becomes zero), or the exact
local entry estimate supplies the positive flat-core and angle/tangent
cut used by the already proved short/long-E stress. This handles
arbitrary signs of the unchanged TD error and weak owner ties.

The new sources retain all unchanged original E and T witnesses.
This is an uncompiled transcription; no CI or kernel claims.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Negative reduced GA3 with actual GA2 as a weak secondary: selecting
GA2 on the same moved state gives the nonnegative-A terminal. -/
theorem reduced_GA_secondary_outer_E_false
    (hqU : q≤qCap) (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hab : O.ab=false) (hsecondary : O.cycle.Feasible G 2) : False := by
  let P : CycleResult q C :=
    { O with
      ga := false
      GA := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hab] }
  exact reduced_nonnegative_A_outer_E_false I P hqU hBT houter
    (by simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hab,P])

include I in
/-- Negative reduced AB2 with actual AB0 as a weak secondary: likewise
no change of the moved A state, its radius or any non-A witness. -/
theorem reduced_AB_secondary_outer_E_false
    (hqU : q≤qCap) (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hga : O.ga=false) (hsecondary : O.cycle.Feasible A 0) : False := by
  let P : CycleResult q C :=
    { O with
      ab := false
      AB := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hga] }
  exact reduced_nonnegative_A_outer_E_false I P hqU hBT houter
    (by simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hga,P])

include I in
/-- All negative-A transported normal forms with the *unchanged original
outer E* are impossible under BT2, for either physical TD owner and
every signed T error. Only the necessary cycle O is used after A moves. -/
theorem negative_A_outer_E_all_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hnegative : ¬0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
      (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  by_cases hpositive : tdFlag I=true ∧ 0<delta C.theta T
  · have hTD : C.Feasible T 2 := by
      have ho : I.owner T=2 := tdFlag_true I hpositive.1
      simpa [ho] using I.feasible T
    rcases O.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
    · exact hnegative hnonneg
    · by_cases hsec : O.cycle.Feasible G 2
      · exact reduced_GA_secondary_outer_E_false I O hqU houter hBT ha hsec
      have hG : (O.cycle.point G).y≤0 := by
        rw [ATransport.G_point O]; exact I.G_negative.le
      have hquarter : quarterFeasible (O.cycle.point G) (O.cycle.point A)
          (delta O.cycle.theta G) 3 := by
        have hh : O.cycle.Feasible G 3 := by simpa [hg] using O.GA
        simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
          word,delta,next,G,A,quarterFeasible,sub_nonneg] using hh
      let s := -(delta O.cycle.theta G)
      have hs : s∈Ioc 0 frameCap := by
        dsimp [s]
        constructor
        · linarith [hu.2]
        · simp only [frameCap]
          linarith [hu.1]
      have houterA : (O.cycle.point A).y≤0→(O.cycle.point A).Outer q := by
        intro hh
        linarith [hy.1]
      rcases GlobalGA.NegativeA.GA_entry (O.necessary.sorted G)
          (O.necessary.contained G) (O.necessary.sorted A) (O.radial A)
          hqU hG houterA hs
          (by simpa [s,neg_neg] using hquarter) with hsecondary|⟨_,_,hcut,_⟩
      · apply hsec
        simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
          word,delta,next,G,A,quarterFeasible,sub_nonneg,s] using hsecondary
      have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut true) := by
        simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
          using (show -(delta O.cycle.theta G)∈Icc 0 (1/4:ℝ) by
            constructor <;> linarith [hu.1,hu.2])
      exact reduced_negative_A_outer_E_positive_TD2_false I O hqU houter
        hBT hTD hpositive.2.le true
        (by simpa [hg] using O.GA) (by simpa [ha] using O.AB)
        hflat hy.1.le hcut.le s hs'
        (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
    · by_cases hsec : O.cycle.Feasible A 0
      · exact reduced_AB_secondary_outer_E_false I O hqU houter hBT hg hsec
      let s := -(delta O.cycle.theta A)
      have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut false) := by
        simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
          using (show -(delta O.cycle.theta A)∈Icc 0 (19/50:ℝ) by
            constructor <;> linarith [hv.1,hv.2])
      exact reduced_negative_A_outer_E_positive_TD2_false I O hqU houter
        hBT hTD hpositive.2.le false
        (by simpa [hg] using O.GA) (by simpa [ha] using O.AB)
        hflat hy.1.le (by simpa using hy.2.le) s hs'
        (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
  · have htd : tdFlag I=true→delta C.theta T≤0 := by
      intro ht
      by_contra hn
      exact hpositive ⟨ht,lt_of_not_ge hn⟩
    exact negative_reduced_A_nonpositive_T_false I O hqL hqU hBT htd hnegative

end SquaresInCircles.Eight.TableFree.HighGABT2
